use super::*;

/// Whole-block preprocessing for `#[vcheck]` and `#[vcheck_provide]`. Returns true
/// if it rewrote `items`.
pub fn vcheck_provide_preprocess(items: &mut Vec<Item>) -> bool {
    // The folded block expands through `verus_spec_check_unverified!` in
    // the `verus_spec_check` crate, whose harnesses need `alloc` and
    // `std`. Builds that don't have those features
    // (e.g. `--is-core` / `--no-std` / `--no-alloc`) can't resolve the
    // path, so any synthesis we do would emit references that fail to
    // link. Detect those modes via `vstd_kind()` and treat all vcheck
    // markers as no-ops there: strip the markers so they don't surface
    // as unknown attributes, then bail without folding anything.
    let kind = crate::vstd_kind::vstd_kind();
    let is_no_alloc_std_build = matches!(
        kind,
        crate::vstd_kind::VstdKind::NoVstd
            | crate::vstd_kind::VstdKind::IsCore
            | crate::vstd_kind::VstdKind::ImportedViaCore
    );
    if is_no_alloc_std_build {
        let mut any = false;
        for item in items.iter_mut() {
            if item_has_attr(item, "vcheck_provide") || item_has_attr(item, "vcheck") {
                strip_attr_item(item, "vcheck_provide");
                strip_attr_item(item, "vcheck");
                any = true;
            }
            if item_has_attr(item, "vcheck_axiom") {
                strip_attr_item(item, "vcheck_axiom");
                any = true;
            }
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        if impl_fn_has_attr(f, "vcheck") || impl_fn_has_attr(f, "vcheck_provide") {
                            strip_attr_impl_fn(f, "vcheck");
                            strip_attr_impl_fn(f, "vcheck_provide");
                            any = true;
                        }
                    }
                }
            }
        }
        return any;
    }

    // Detect any markers up front.
    let mut any_marker = false;
    for item in items.iter() {
        if item_has_attr(item, "vcheck_provide")
            || item_has_attr(item, "vcheck")
            || item_has_attr(item, "vcheck_axiom")
        {
            any_marker = true;
        }
        if external_provide_names(item).is_some() {
            any_marker = true;
        }
        if let Item::Impl(im) = item {
            for ii in &im.items {
                if let ImplItem::Fn(f) = ii {
                    if impl_fn_has_attr(f, "vcheck") || impl_fn_has_attr(f, "vcheck_provide") {
                        any_marker = true;
                    }
                    // Inline `#[vcheck] assert(...)` inside a method body
                    // also counts: the engine block needs to fold the
                    // enclosing method so the inline-assert harness
                    // emitter can drive it.
                    if crate::vcheck_assert::block_has_vcheck_inline_assert(&f.block) {
                        any_marker = true;
                    }
                }
            }
        }
        // Inline `#[vcheck] assert(...)` inside a free fn body. Same
        // rationale as the impl-method case above.
        if let Item::Fn(f) = item {
            if crate::vcheck_assert::block_has_vcheck_inline_assert(&f.block) {
                any_marker = true;
            }
        }
    }
    if !any_marker {
        return false;
    }

    // Pre-pass: rewrite each `assume_specification` item that carries a
    // `#[vcheck]` or `#[vcheck_provide]` marker into a synthesized exec wrapper fn
    // bearing the same marker. The wrapper has `#[verifier::external_body]`
    // (its body is a trusted call into the specified path) and the same
    // requires/ensures, so the rest of the pipeline can treat it as an
    // ordinary contract-bearing exec fn.
    //
    // The original `assume_specification` is preserved (with its markers
    // stripped) so other code that depends on the contract — including
    // verifier-side reasoning that resolves `<[T]>::is_empty` to its
    // assumed spec — keeps working. Without this, marking an `assume_spec`
    // would change the verifier's view of the surrounding crate.
    let mut synthesized_wrappers: Vec<Item> = Vec::new();
    for item in items.iter_mut() {
        if let Item::AssumeSpecification(asp) = item {
            if asp
                .attrs
                .iter()
                .any(|a| attr_is(a, "vcheck") || attr_is(a, "vcheck_provide"))
            {
                // An assume_specification may carry SEVERAL `#[vcheck(...)]`
                // markers, one per concrete instantiation — e.g. a primary
                // `#[vcheck(T = u32, ...)]` for ordinary behavior plus a
                // `#[vcheck(T = (), ...)]` whose zero-sized element type makes
                // usize::MAX-length containers constructible (the only way
                // to reach combined-length overflow in `append`-style
                // specs). Synthesize one wrapper per marker.
                //
                // Only the FIRST marker's wrapper keeps `#[vcheck_cov_fuzz]`
                // (and other companion markers): coverage measurement wants
                // one canonical instantiation, and duplicate cov targets
                // would double-count arms. Secondary wrappers get a `_vN`
                // ident suffix so their fns (and harness/test names) stay
                // distinct.
                let vcheck_attrs: Vec<verus_syn::Attribute> = asp
                    .attrs
                    .iter()
                    .filter(|a| attr_is(a, "vcheck"))
                    .cloned()
                    .collect();
                let non_vcheck_attrs: Vec<verus_syn::Attribute> = asp
                    .attrs
                    .iter()
                    .filter(|a| !attr_is(a, "vcheck"))
                    .cloned()
                    .collect();
                if vcheck_attrs.len() > 1 {
                    for (i, vcheck_attr) in vcheck_attrs.iter().enumerate() {
                        let mut variant = asp.clone();
                        variant.attrs = if i == 0 {
                            let mut v = non_vcheck_attrs.clone();
                            v.insert(0, vcheck_attr.clone());
                            v
                        } else {
                            let mut v: Vec<verus_syn::Attribute> = non_vcheck_attrs
                                .iter()
                                .filter(|a| !attr_is(a, "vcheck_cov_fuzz"))
                                .cloned()
                                .collect();
                            v.insert(0, vcheck_attr.clone());
                            v
                        };
                        if let Some(mut synthesized) =
                            synthesize_vcheck_wrapper_from_assume_spec(&variant)
                        {
                            if i > 0 {
                                synthesized.sig.ident = quote::format_ident!(
                                    "{}_v{}",
                                    synthesized.sig.ident,
                                    i + 1
                                );
                            }
                            synthesized_wrappers.push(Item::Fn(synthesized));
                        }
                    }
                } else {
                    let asp_copy = asp.clone();
                    if let Some(synthesized) = synthesize_vcheck_wrapper_from_assume_spec(&asp_copy) {
                        synthesized_wrappers.push(Item::Fn(synthesized));
                    }
                }
                // Strip the markers from the original so the verifier
                // doesn't see them as unknown attributes; the synthesized
                // wrappers carry them and drive the harness.
                asp.attrs
                    .retain(|a| !attr_is(a, "vcheck") && !attr_is(a, "vcheck_provide"));
            }
        }
        // `#[vcheck(K = V, ...)]` on a *generic exec fn*: substituting into
        // the item itself would monomorphize it in place and break every
        // generic caller. Instead synthesize a parallel monomorphizing
        // wrapper (same contract, trusted turbofish call into the
        // original) carrying the marker, and strip the marker from the
        // original so it keeps its generics.
        if let Item::Fn(f) = item {
            let has_subst = f.attrs.iter().any(|a| attr_is(a, "vcheck"))
                && item_marker_subst(item, "vcheck").map_or(false, |s| !s.is_empty());
            if has_subst {
                if let Item::Fn(f) = item {
                    if let Some(synthesized) = synthesize_vcheck_wrapper_from_generic_exec_fn(f) {
                        synthesized_wrappers.push(Item::Fn(synthesized));
                        f.attrs.retain(|a| !attr_is(a, "vcheck"));
                    }
                }
            }
        }
        // `#[vcheck_axiom]` on a proof / axiom fn: synthesize a parallel
        // `#[verifier::external_body] #[vcheck]` exec wrapper. The original
        // proof / axiom fn is preserved (with `#[vcheck_axiom]` stripped)
        // so the verifier continues to see it; the wrapper carries the
        // contract into the harness.
        if let Item::Fn(f) = item {
            if f.attrs.iter().any(|a| attr_is(a, "vcheck_axiom")) {
                let f_copy = f.clone();
                if let Some(synthesized) = synthesize_vcheck_wrapper_from_proof_fn(&f_copy) {
                    synthesized_wrappers.push(Item::Fn(synthesized));
                }
                // Strip `#[vcheck_axiom]` from the original so the
                // verifier doesn't see it as an unknown attribute.
                f.attrs.retain(|a| !attr_is(a, "vcheck_axiom"));
            }
        }
    }
    items.extend(synthesized_wrappers);

    // Note: `int` / `nat` quantifier-bound variable types are handled
    // narrowly inside the harness's lifted-clause synthesis, not block-
    // wide. A block-wide rewrite would touch spec-fn bodies in a way that
    // breaks Verus's spec semantics (Seq::index expects `int`, etc.). The
    // engine still rejects `int`-bound quantifiers in spec-fn bodies; users
    // should use runtime-primitive bounds (`usize`, `u32`, ...) there.

    // Pre-pass: rewrite each marked trait impl `impl<T> Trait for X<T>`.
    //   - If the Self type supports an inherent impl (it's a sibling
    //     user-defined struct/enum), mangle method names with the trait
    //     prefix and drop the trait header in place. The rest of the
    //     pipeline then handles the impl as an inherent block.
    //   - If the Self type doesn't support an inherent impl (primitive,
    //     unsized, external-crate type), lift each marked method into a
    //     free fn `<TraitPrefix>_<method>` taking the receiver as a typed
    //     param. The harness drives those as ordinary free fns.
    {
        // Compute per-index marker presence first so we don't have aliasing
        // borrows when we mutate the items in place.
        let marker_at: Vec<bool> = items
            .iter()
            .map(|item| {
                let item_marker = item_has_attr(item, "vcheck_provide") || item_has_attr(item, "vcheck");
                let method_marker = match item {
                    Item::Impl(im) => im.items.iter().any(|ii| match ii {
                        ImplItem::Fn(f) => {
                            impl_fn_has_attr(f, "vcheck") || impl_fn_has_attr(f, "vcheck_provide")
                        }
                        _ => false,
                    }),
                    _ => false,
                };
                item_marker || method_marker
            })
            .collect();
        // Walk indices once, deciding inherent-vs-lift per-impl.
        // We accumulate replacement items separately and splice at the end
        // because vec mutation while iterating is awkward.
        let mut replacements: Vec<(usize, Vec<Item>)> = Vec::new();
        for (i, item) in items.iter().enumerate() {
            if !marker_at[i] {
                continue;
            }
            if let Item::Impl(im) = item {
                if im.trait_.is_some() {
                    if self_ty_supports_inherent_impl(im.self_ty.as_ref()) {
                        // Will rewrite in place below.
                        continue;
                    }
                    // Lift each method to a free fn, AND keep the original
                    // impl block (with markers stripped) so other vstd code
                    // that calls these methods directly still resolves.
                    let trait_prefix = im
                        .trait_
                        .as_ref()
                        .and_then(|(_, path, _)| path.segments.last().map(|s| s.ident.to_string()))
                        .unwrap_or_else(|| "_".to_string());
                    let mut lifted: Vec<Item> = Vec::new();
                    for ii in &im.items {
                        if let ImplItem::Fn(f) = ii {
                            // Only lift methods that carry the marker;
                            // unmarked sibling methods stay where they are.
                            if !impl_fn_has_attr(f, "vcheck") && !impl_fn_has_attr(f, "vcheck_provide") {
                                continue;
                            }
                            if let Some(new_fn) = lift_trait_method_to_free_fn(
                                &im.generics,
                                im.self_ty.as_ref(),
                                &trait_prefix,
                                f,
                            ) {
                                lifted.push(Item::Fn(new_fn));
                            }
                            // Methods that fail to lift get dropped here;
                            // they'll surface as missing-fn errors at the
                            // harness layer if the user marked one.
                        }
                    }
                    replacements.push((i, lifted));
                }
            }
        }
        // Apply in-place inherent rewrites for the cases we kept.
        for (i, item) in items.iter_mut().enumerate() {
            if !marker_at[i] {
                continue;
            }
            // Skip if we already chose to lift this impl.
            if replacements.iter().any(|(j, _)| *j == i) {
                continue;
            }
            if let Item::Impl(im) = item {
                if im.trait_.is_some() {
                    rewrite_trait_impl_to_inherent(im);
                }
            }
        }
        // Splice replacements in (highest index first so positions don't
        // shift under us). For each replacement: keep the ORIGINAL impl
        // (with vcheck markers stripped from its methods so they pass through
        // as ordinary trait impl methods) and INSERT the lifted free fns
        // immediately after.
        replacements.sort_by(|a, b| b.0.cmp(&a.0));
        for (i, lifted) in replacements {
            // Strip vcheck markers from the original impl's methods before
            // it passes through to the verifier — they've been carried to
            // the lifted free fns and shouldn't trigger another harness.
            if let Item::Impl(im) = &mut items[i] {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        strip_attr_impl_fn(f, "vcheck");
                        strip_attr_impl_fn(f, "vcheck_provide");
                    }
                }
            }
            // Insert lifted items right after the original impl. We splice
            // an empty range starting at i+1 so the original is preserved.
            items.splice(i + 1..i + 1, lifted);
        }
    }

    // 0. Reject misplaced markers up front with actionable errors. We do this
    // BEFORE building the index so we can give precise placement guidance
    // ("put `#[vcheck_provide]` on the struct/enum, free fn, or its method").
    let mut placement_errors: Vec<TokenStream2> = Vec::new();
    for item in items.iter() {
        // `#[vcheck_provide]` on an item kind we can't fold.
        if item_has_attr(item, "vcheck_provide") {
            if let Some(kind) = vcheck_provide_unsupported_item_kind(item) {
                let span = item_attr_span(item, "vcheck_provide")
                    .unwrap_or_else(proc_macro2::Span::call_site);
                let msg = format!(
                    "verus_spec_check: `#[vcheck_provide]` was placed on {kind}, but it can only be \
applied to:\n\
\u{20} - a `struct` or `enum` definition (folds the type and its inherent impls into the engine);\n\
\u{20} - a free `spec fn` definition (folds just that spec fn);\n\
\u{20} - a method inside a non-generic inherent `impl Type {{ ... }}` block (folds the surrounding impl).\n\
\n\
Move `#[vcheck_provide]` to the top of the relevant `struct`/`enum`, free `spec fn`, \
or impl method instead.",
                    kind = kind
                );
                placement_errors.push(quote::quote_spanned! { span =>
                    const _: () = { compile_error!(#msg); };
                });
            }
        }
        // `#[vcheck_provide]` / `#[vcheck]` on a method inside an impl: previously
        // we rejected trait impls, but with feature-4 trait-impl folding the
        // pre-pass below pre-rewrites them into inherent-shape impls. Defer
        // the soundness check (associated-type projections, etc.) to the
        // engine, which will produce a precise diagnostic when it can't
        // lower a body. We still reject markers we can't make sense of:
        // none currently — every shape is folded.
        let _ = item;
    }
    if !placement_errors.is_empty() {
        let mut error_items: Vec<Item> = Vec::new();
        for ts in placement_errors {
            if let Ok(item) = verus_syn::parse2::<Item>(ts) {
                error_items.push(item);
            }
        }
        // Stripping markers on the existing items so they don't reach rustc as
        // unknown attributes alongside our diagnostics.
        let mut sanitized = std::mem::take(items);
        for item in &mut sanitized {
            strip_attr_item(item, "vcheck_provide");
            convert_vcheck_to_sentinel_item(item);
            strip_attr_item(item, "vcheck_cov_mutate");
            strip_attr_item(item, "vcheck_cov_fuzz");
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        convert_vcheck_to_sentinel_impl_fn(f);
                        strip_attr_impl_fn(f, "vcheck_cov_mutate");
                        strip_attr_impl_fn(f, "vcheck_cov_fuzz");
                        strip_attr_impl_fn(f, "vcheck_provide");
                    }
                }
            }
        }
        error_items.extend(sanitized);
        *items = error_items;
        return true;
    }

    let index = build_index(items);

    // 1. Seed sets:
    //   - engine_idxs: indices that MUST go into the engine block (markers
    //     and `external_vcheck_provide!` invocations).
    //   - explicit_substs: the subst attached to each marker the user wrote.
    //   - generic_seeds: typed seeds for the generics-aware closure pass.
    //   - seed_idents: simpler ident-only seeds for the legacy closure (the
    //     name-only path is still used to keep diagnostics for free spec-fn
    //     calls cheap and unambiguous).
    let mut engine_idxs: HashSet<usize> = HashSet::new();
    let mut explicit_substs: HashMap<usize, Subst> = HashMap::new();
    // Items folded into engine_idxs solely because their body contains a
    // stmt-level `#[vcheck] assert(...)`. These get a skip-regular-harness
    // sentinel stamped before strip so the downstream classify pass
    // emits only the inline-assert harness, not a regular `vcheck_<fn>`
    // harness for the enclosing fn (which would be a noisy by-product
    // of the fold, not what the user asked for).
    let mut inline_assert_only_idxs: HashSet<usize> = HashSet::new();
    // Same idea for impl methods, addressed by (impl_item_idx, method_idx).
    // The impl block is folded as a whole, but only methods that match
    // the inline-assert-only criterion get the sentinel.
    let mut inline_assert_only_impl_methods: HashSet<(usize, usize)> = HashSet::new();
    // Names referenced by #[vcheck] contracts -> closure seeds (legacy).
    let mut seed_idents: HashSet<String> = HashSet::new();
    // Typed seeds for the generics-aware closure: (name, type-args, subst).
    let mut generic_seeds: Vec<(String, Vec<Type>, Subst)> = Vec::new();
    // Free-function calls in #[vcheck] contracts.
    // These must resolve to a sibling free spec fn; if not, they're external
    // and need one of the resolution tiers.
    let mut vcheck_free_calls: HashSet<String> = HashSet::new();
    // Names provided by `external_vcheck_provide!`: these resolve, so
    // they suppress the diagnostic.
    let mut externally_provided: HashSet<String> = HashSet::new();
    // Explicit #[vcheck_provide] types contribute themselves + their impls.
    let mut explicit_provided_types: HashSet<String> = HashSet::new();

    for (i, item) in items.iter().enumerate() {
        // external_vcheck_provide! { ... } -> fold into the engine block (its
        // `exec_<name>` companions land in the harness module) and register
        // the provided names.
        if let Some(names) = external_provide_names(item) {
            engine_idxs.insert(i);
            for n in names {
                externally_provided.insert(n);
            }
        }
        // #[vcheck_provide] on a type / free fn.
        if item_has_attr(item, "vcheck_provide") {
            engine_idxs.insert(i);
            if let Some(s) = item_marker_subst(item, "vcheck_provide") {
                explicit_substs.insert(i, s);
            }
            if let Some(n) = type_def_name(item) {
                explicit_provided_types.insert(n.to_string());
            }
            // #[vcheck_provide] on a free fn: include it. If it's a free spec fn,
            // also recurse into its body so nested calls are folded too.
            if let Item::Fn(f) = item {
                collect_sig_idents(&f.sig, &mut seed_idents);
                if matches!(f.sig.mode, FnMode::Spec(..)) {
                    collect_block_idents(&f.block, &mut seed_idents);
                }
            }
        }
        // #[vcheck] on a free fn: include the fn, seed closure from its contract.
        if item_has_attr(item, "vcheck") {
            if let Item::Fn(f) = item {
                engine_idxs.insert(i);
                let vcheck_subst = item_marker_subst(item, "vcheck").unwrap_or_default();
                if !vcheck_subst.is_empty() {
                    explicit_substs.insert(i, vcheck_subst.clone());
                }
                collect_contract_idents(&f.sig, &mut seed_idents);
                collect_free_call_names(&f.sig, &mut vcheck_free_calls);
                // Also seed the generics-aware walker.
                let mut typed = Vec::<(String, Vec<Type>)>::new();
                collect_contract_typed_refs(&f.sig, &mut typed);
                for (n, a) in typed {
                    generic_seeds.push((n, a, vcheck_subst.clone()));
                }
            }
        }
        // Inline `#[vcheck] assert(...)` inside a free fn body: same
        // treatment as an item-level `#[vcheck]`. The fn must reach the
        // engine block so the inline-assert harness emitter
        // (`emit_inline_assert_block`) can pair the assert with an
        // enclosing `ContractTarget`. Seed from the contract so any
        // sibling spec fns / user types referenced by `requires` /
        // `ensures` are folded too.
        if let Item::Fn(f) = item {
            if !engine_idxs.contains(&i)
                && !matches!(f.sig.mode, FnMode::Spec(..))
                && crate::vcheck_assert::block_has_vcheck_inline_assert(&f.block)
            {
                engine_idxs.insert(i);
                inline_assert_only_idxs.insert(i);
                collect_contract_idents(&f.sig, &mut seed_idents);
                collect_free_call_names(&f.sig, &mut vcheck_free_calls);
                let mut typed = Vec::<(String, Vec<Type>)>::new();
                collect_contract_typed_refs(&f.sig, &mut typed);
                for (n, a) in typed {
                    generic_seeds.push((n, a, Subst::default()));
                }
            }
        }
        // #[vcheck] / #[vcheck_provide] on a method inside an impl: include the
        // whole impl block and the impl's Self type. 
        if let Item::Impl(im) = item {
            let mut impl_has_marker = false;
            let impl_attr_subst =
                item_marker_subst(item, "vcheck").or_else(|| item_marker_subst(item, "vcheck_provide"));
            let mut method_subst: Option<Subst> = None;
            for (mi, ii) in im.items.iter().enumerate() {
                if let ImplItem::Fn(f) = ii {
                    if impl_fn_has_attr(f, "vcheck") {
                        impl_has_marker = true;
                        if method_subst.is_none() {
                            method_subst = impl_fn_marker_subst(f, "vcheck");
                        }
                        collect_contract_idents(&f.sig, &mut seed_idents);
                        collect_free_call_names(&f.sig, &mut vcheck_free_calls);
                        let mut typed = Vec::<(String, Vec<Type>)>::new();
                        collect_contract_typed_refs(&f.sig, &mut typed);
                        let s_for_seed = impl_fn_marker_subst(f, "vcheck")
                            .or_else(|| impl_attr_subst.clone())
                            .unwrap_or_default();
                        for (n, a) in typed {
                            generic_seeds.push((n, a, s_for_seed.clone()));
                        }
                    }
                    if impl_fn_has_attr(f, "vcheck_provide") {
                        impl_has_marker = true;
                        if method_subst.is_none() {
                            method_subst = impl_fn_marker_subst(f, "vcheck_provide");
                        }
                        // For a spec method, seed from its body so nested
                        // references are folded.
                        collect_sig_idents(&f.sig, &mut seed_idents);
                        if matches!(f.sig.mode, FnMode::Spec(..)) {
                            collect_block_idents(&f.block, &mut seed_idents);
                        }
                        if let Some(self_name) = inherent_impl_self_name(item) {
                            explicit_provided_types.insert(self_name.to_string());
                        }
                    }
                    // Inline `#[vcheck] assert(...)` inside a method body
                    // without any item-level marker on the method
                    if !impl_fn_has_attr(f, "vcheck")
                        && !impl_fn_has_attr(f, "vcheck_provide")
                        && !matches!(f.sig.mode, FnMode::Spec(..))
                        && crate::vcheck_assert::block_has_vcheck_inline_assert(&f.block)
                    {
                        impl_has_marker = true;
                        inline_assert_only_impl_methods.insert((i, mi));
                        collect_contract_idents(&f.sig, &mut seed_idents);
                        collect_free_call_names(&f.sig, &mut vcheck_free_calls);
                        let mut typed = Vec::<(String, Vec<Type>)>::new();
                        collect_contract_typed_refs(&f.sig, &mut typed);
                        let s_for_seed = impl_attr_subst.clone().unwrap_or_default();
                        for (n, a) in typed {
                            generic_seeds.push((n, a, s_for_seed.clone()));
                        }
                    }
                }
            }
            if impl_has_marker {
                engine_idxs.insert(i);
                if let Some(s) = impl_attr_subst.clone().or(method_subst) {
                    explicit_substs.insert(i, s);
                }
                if let Some(self_name) = inherent_impl_self_name(item) {
                    seed_idents.insert(self_name.to_string());
                    // Seed the generics-aware walker with the Self type and
                    // its type-args, picking up the impl's marker subst.
                    let s_for_seed = explicit_substs.get(&i).cloned().unwrap_or_default();
                    let self_args: Vec<Type> = if let Item::Impl(im) = item {
                        if let Type::Path(tp) = im.self_ty.as_ref() {
                            if tp.qself.is_none() && tp.path.segments.len() == 1 {
                                path_seg_type_args(&tp.path.segments[0].arguments)
                            } else {
                                Vec::new()
                            }
                        } else {
                            Vec::new()
                        }
                    } else {
                        Vec::new()
                    };
                    generic_seeds.push((self_name.to_string(), self_args, s_for_seed));
                }
            }
        }
    }

    // 1b. Tier-aware diagnostic: any free spec-fn call in a #[vcheck] contract
    // that does NOT resolve to a sibling free fn is defined outside this block
    // and has no exec companion. Surface an actionable, path-inferred error
    // rather than letting the engine emit a broken `exec_<name>(..)` call.
    let unresolved: Vec<String> = vcheck_free_calls
        .iter()
        .filter(|name| {
            !index.free_fns.contains_key(*name)
                && !is_builtin_free_spec_fn(name)
                && !externally_provided.contains(*name)
                && !is_resource_native_ident(name)
        })
        .cloned()
        .collect();
    if !unresolved.is_empty() {
        let use_index = build_use_index(items);
        let mut names: Vec<String> = unresolved;
        names.sort();
        let mut error_items: Vec<Item> = Vec::new();
        for name in &names {
            let inferred = infer_path_for(name, &use_index);
            let msg = unresolved_spec_fn_message(name, &inferred);
            let err_tokens: TokenStream2 = quote! {
                const _: () = { compile_error!(#msg); };
            };
            if let Ok(item) = verus_syn::parse2::<Item>(err_tokens) {
                error_items.push(item);
            }
        }
        // Replace the block with only the diagnostics. Keeping the user's
        // `#[vcheck]` fn would cause a cascade: its contract calls the undefined
        // `exec_<name>` / spec fn, producing a second (E-coded) resolution
        // error that obscures our actionable message. The compile_error stops
        // the build cleanly with just the tier-aware guidance.
        *items = error_items;
        return true;
    }

    // 2. Pull in inherent impls of explicitly-provided types.
    for ty in &explicit_provided_types {
        if let Some(impl_idxs) = index.type_impls.get(ty) {
            for &ix in impl_idxs {
                engine_idxs.insert(ix);
            }
        }
    }

    // 3. Compute the closure from the seeds and union it in. Names covered by
    // an `external_vcheck_provide!` stub are excluded from sibling folding
    // (option 1): the provided exec companion is used instead, which lets a
    // `#[vcheck]` reach specs whose body depends on cross-module spec fns.
    let closure = compute_closure(seed_idents, &externally_provided, items, &index);
    engine_idxs.extend(closure);

    // 3a. Generics-aware closure: produces per-item substs by walking type-
    // args along the call/reference graph from each `#[vcheck]` callsite.
    let generic_closure =
        compute_closure_with_substs(generic_seeds, &externally_provided, items, &index);
    // Merge: indices from the typed walker join engine_idxs.
    for &idx in generic_closure.chosen.keys() {
        engine_idxs.insert(idx);
    }
    // Build the final per-item subst map. Priority:
    //   1. explicit_substs (a marker on the item itself).
    //   2. generic_closure subst (inherited from a #[vcheck] callsite).
    //   3. empty (item is non-generic).
    // Conflicts between (1) and (2), or among multiple (2)s, are surfaced as
    // diagnostics below.
    let mut item_substs: HashMap<usize, Subst> = HashMap::new();
    let mut item_subst_conflicts: Vec<InstantiationConflict> = generic_closure.conflicts;
    for (idx, generic_subst) in generic_closure.chosen {
        if let Some(explicit) = explicit_substs.get(&idx) {
            if !generic_subst.is_empty() && !explicit.agrees_with(&generic_subst) {
                let name = item_display_name(&items[idx]);
                item_subst_conflicts.push(InstantiationConflict {
                    item_idx: idx,
                    item_name: name,
                    first: explicit.clone(),
                    second: generic_subst,
                });
                item_substs.insert(idx, explicit.clone());
            } else {
                item_substs.insert(idx, explicit.clone());
            }
        } else {
            item_substs.insert(idx, generic_subst);
        }
    }
    // Items in engine_idxs but not in generic_closure.chosen: pick up explicit
    // marker subst if any (else default).
    for &idx in &engine_idxs {
        if !item_substs.contains_key(&idx) {
            if let Some(explicit) = explicit_substs.get(&idx) {
                item_substs.insert(idx, explicit.clone());
            } else {
                item_substs.insert(idx, Subst::default());
            }
        }
    }

    // 3a-conflicts: emit a diagnostic per disagreeing instantiation.
    if !item_subst_conflicts.is_empty() {
        let mut error_items: Vec<Item> = Vec::new();
        for c in &item_subst_conflicts {
            let span = items
                .get(c.item_idx)
                .map(|it| {
                    item_attr_span(it, "vcheck_provide")
                        .or_else(|| item_attr_span(it, "vcheck"))
                        .unwrap_or_else(proc_macro2::Span::call_site)
                })
                .unwrap_or_else(proc_macro2::Span::call_site);
            let msg = format!(
                "verus_spec_check: `{name}` is reached by `#[vcheck]` callsites with conflicting \
instantiations:\n\
\u{20} - first: {{ {first} }}\n\
\u{20} - second: {{ {second} }}\n\
\n\
Property-based testing currently emits one engine block per provider, so a single \
provider can't be folded under two different concrete instantiations. Either:\n\
\u{20} - factor the conflicting `#[vcheck]` callsites into separate Verus blocks/files, or\n\
\u{20} - duplicate the provider with explicit `#[vcheck_provide(...)]` markers that fix \
the instantiation locally.",
                name = c.item_name,
                first = c.first.render(),
                second = c.second.render(),
            );
            error_items.push(
                verus_syn::parse2::<Item>(quote::quote_spanned! { span =>
                    const _: () = { compile_error!(#msg); };
                })
                .expect("conflict diagnostic must parse"),
            );
        }
        // Strip markers and surface diagnostics + sanitized items.
        let mut sanitized = std::mem::take(items);
        for item in &mut sanitized {
            strip_attr_item(item, "vcheck_provide");
            convert_vcheck_to_sentinel_item(item);
            strip_attr_item(item, "vcheck_cov_mutate");
            strip_attr_item(item, "vcheck_cov_fuzz");
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        convert_vcheck_to_sentinel_impl_fn(f);
                        strip_attr_impl_fn(f, "vcheck_cov_mutate");
                        strip_attr_impl_fn(f, "vcheck_cov_fuzz");
                        strip_attr_impl_fn(f, "vcheck_provide");
                    }
                }
            }
        }
        error_items.extend(sanitized);
        *items = error_items;
        return true;
    }

    // 3a-unbound: any folded item with declared type-params and no subst (or
    // a subst that doesn't bind every param) means the user wrote a
    // generic `#[vcheck]` or `#[vcheck_provide]` without supplying enough
    // instantiation. Emit a tailored diagnostic per item.
    let mut unbound_errors: Vec<TokenStream2> = Vec::new();
    for &idx in &engine_idxs {
        let params = match index.type_params_by_idx.get(&idx) {
            Some(p) if !p.is_empty() => p.clone(),
            _ => continue,
        };
        let subst = item_substs.get(&idx).cloned().unwrap_or_default();
        let unbound_types: Vec<&Ident> = params
            .iter()
            .filter(|p| !subst.map.contains_key(&p.to_string()))
            .collect();
        let const_params = item_const_params(&items[idx]);
        let unbound_consts: Vec<&Ident> = const_params
            .iter()
            .filter(|p| !subst.consts.contains_key(&p.to_string()))
            .collect();
        if unbound_types.is_empty() && unbound_consts.is_empty() {
            continue;
        }
        let item = &items[idx];
        let name = item_display_name(item);
        let span = item_attr_span(item, "vcheck_provide")
            .or_else(|| item_attr_span(item, "vcheck"))
            .or_else(|| {
                if let Item::Impl(im) = item {
                    for ii in &im.items {
                        if let ImplItem::Fn(f) = ii {
                            if let Some(s) = impl_fn_attr_span(f, "vcheck") {
                                return Some(s);
                            }
                            if let Some(s) = impl_fn_attr_span(f, "vcheck_provide") {
                                return Some(s);
                            }
                        }
                    }
                }
                None
            })
            .unwrap_or_else(proc_macro2::Span::call_site);
        let unbound_str = unbound_types
            .iter()
            .map(|i| i.to_string())
            .chain(unbound_consts.iter().map(|i| format!("const {}", i)))
            .collect::<Vec<_>>()
            .join(", ");
        let suggestion = unbound_types
            .iter()
            .map(|i| {
                let t = suggest_default_type(i, &[]);
                format!("{} = {}", i, quote!(#t))
            })
            .chain(unbound_consts.iter().map(|i| format!("{} = 4", i)))
            .collect::<Vec<_>>()
            .join(", ");
        let attr_kind = if item_has_attr(item, "vcheck_provide") {
            "vcheck_provide"
        } else if item_has_attr(item, "vcheck") {
            "vcheck"
        } else {
            "vcheck"
        };
        let msg = format!(
            "verus_spec_check: `{name}` is generic in <{unbound}> but no concrete instantiation \
was found.\n\
\n\
Property-based testing needs concrete types to sample. Either:\n\
\u{20} - put `#[{attr_kind}({suggestion})]` on this item to fix an instantiation \
explicitly, or\n\
\u{20} - attach a `#[vcheck]` to a (non-generic, or already-instantiated) function whose \
contract reaches `{name}`, and the instantiation will be inherited automatically.",
            name = name,
            unbound = unbound_str,
            attr_kind = attr_kind,
            suggestion = suggestion,
        );
        unbound_errors.push(quote::quote_spanned! { span =>
            const _: () = { compile_error!(#msg); };
        });
    }
    if !unbound_errors.is_empty() {
        let mut error_items: Vec<Item> = Vec::new();
        for ts in unbound_errors {
            if let Ok(item) = verus_syn::parse2::<Item>(ts) {
                error_items.push(item);
            }
        }
        let mut sanitized = std::mem::take(items);
        for item in &mut sanitized {
            strip_attr_item(item, "vcheck_provide");
            convert_vcheck_to_sentinel_item(item);
            strip_attr_item(item, "vcheck_cov_mutate");
            strip_attr_item(item, "vcheck_cov_fuzz");
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        convert_vcheck_to_sentinel_impl_fn(f);
                        strip_attr_impl_fn(f, "vcheck_cov_mutate");
                        strip_attr_impl_fn(f, "vcheck_cov_fuzz");
                        strip_attr_impl_fn(f, "vcheck_provide");
                    }
                }
            }
        }
        error_items.extend(sanitized);
        *items = error_items;
        return true;
    }

    // 3b. Diagnostic: any uninterp spec fn (or body-less spec fn) folded into
    // the engine block has no body the engine can lower into a runnable
    // companion. Surface a tailored error rather than letting `exec_spec`
    // produce a "missing return expression" or "unsupported statement" error
    // on the empty body.
    let mut uninterp_errors: Vec<TokenStream2> = Vec::new();
    for &idx in &engine_idxs {
        let item = &items[idx];
        match item {
            // `#[vcheck_view]` uninterp views are intentionally body-less: the
            // engine lowers `view(x)` to the developer-supplied `realize` fn
            // rather than compiling a companion, so they're exempt.
            Item::Fn(f)
                if is_uninterp_spec_fn(f) && !f.attrs.iter().any(|a| attr_is(a, "vcheck_view")) =>
            {
                let span = f.sig.ident.span();
                let name = f.sig.ident.to_string();
                let msg = uninterp_spec_message(&name);
                uninterp_errors.push(quote::quote_spanned! { span =>
                    const _: () = { compile_error!(#msg); };
                });
            }
            Item::Impl(im) => {
                // Built-in routed carriers: the exec_spec rewriter routes
                // method calls on these spec types to the runtime exec
                // models (`.exec_count()`, `.exec_index()`, ...), so their
                // uninterp method declarations are NOT dead ends — exempt
                // them from the diagnostic.
                let routed_carrier = inherent_impl_self_name(item)
                    .map(|n| matches!(n.to_string().as_str(), "Multiset" | "Map" | "Set" | "Seq"))
                    .unwrap_or(false);
                if routed_carrier {
                    continue;
                }
                for ii in &im.items {
                    if let ImplItem::Fn(f) = ii {
                        if impl_fn_is_uninterp_spec(f) {
                            let span = f.sig.ident.span();
                            let owner = inherent_impl_self_name(item)
                                .map(|n| n.to_string())
                                .unwrap_or_else(|| "?".to_string());
                            let qualified = format!("{}::{}", owner, f.sig.ident);
                            let msg = uninterp_spec_message(&qualified);
                            uninterp_errors.push(quote::quote_spanned! { span =>
                                const _: () = { compile_error!(#msg); };
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }
    if !uninterp_errors.is_empty() {
        let mut error_items: Vec<Item> = Vec::new();
        for ts in uninterp_errors {
            if let Ok(item) = verus_syn::parse2::<Item>(ts) {
                error_items.push(item);
            }
        }
        // Strip markers from the existing items so they don't reach rustc as
        // unknown attributes alongside our diagnostics, and don't fold into
        // the engine block (which would re-trigger the engine error).
        let mut sanitized = std::mem::take(items);
        for item in &mut sanitized {
            strip_attr_item(item, "vcheck_provide");
            convert_vcheck_to_sentinel_item(item);
            strip_attr_item(item, "vcheck_cov_mutate");
            strip_attr_item(item, "vcheck_cov_fuzz");
            if let Item::Impl(im) = item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        convert_vcheck_to_sentinel_impl_fn(f);
                        strip_attr_impl_fn(f, "vcheck_cov_mutate");
                        strip_attr_impl_fn(f, "vcheck_cov_fuzz");
                        strip_attr_impl_fn(f, "vcheck_provide");
                    }
                }
            }
        }
        error_items.extend(sanitized);
        *items = error_items;
        return true;
    }

    // 4. Partition: chosen indices (marker-stripped, substituted) -> engine
    // block; rest stay. Per-item substitutions come from `item_substs`,
    // computed by combining explicit markers and the generics-aware closure.
    let mut engine_items: Vec<Item> = Vec::new();
    let mut remaining: Vec<Item> = Vec::new();
    // Track which sibling types had their type-params stripped, so we can
    // also strip type-args from in-block references to them. e.g. once
    // `Cell<V>` becomes `Cell`, every `Cell<u64>` in fields/impls becomes
    // `Cell` too.
    let mut stripped_type_names: HashSet<String> = HashSet::new();
    for (i, item) in items.iter().enumerate() {
        if engine_idxs.contains(&i) {
            if let Some(s) = item_substs.get(&i) {
                if !s.is_empty() {
                    if let Some(name) = type_def_name(item) {
                        stripped_type_names.insert(name.to_string());
                    }
                }
            }
        }
    }
    for (i, mut item) in items.drain(..).enumerate() {
        if engine_idxs.contains(&i) {
            // Stamp Miri-mode sentinel BEFORE stripping `#[vcheck]` so the
            // downstream `verus_spec_check_unverified!` macro's classify pass can
            // still recover `miri = "skip"`. The original `#[vcheck(...)]`
            // attribute is stripped here (and only here) to keep it from
            // surfacing to rustc as an unknown attribute.
            stamp_miri_mode_sentinel_item(&mut item);
            // Likewise stamp the backend sentinel before the `#[vcheck]` strip
            // so the downstream pass can recover `backend = "bolero"`.
            stamp_backend_sentinel_item(&mut item);
            // And the bolero-mode sentinel (`fuzz`/`kani`) so the downstream
            // pass and tooling can recover the selected mode.
            stamp_bolero_mode_sentinel_item(&mut item);
            // For free fns folded solely because of a stmt-level `#[vcheck]`
            // assert, stamp the skip-regular-harness sentinel so the
            // downstream classify pass doesn't emit a redundant
            // `vcheck_<fn>` harness.
            if inline_assert_only_idxs.contains(&i) {
                stamp_skip_regular_harness_on_attrs(item_attrs_mut(&mut item));
            }
            strip_attr_item(&mut item, "vcheck_provide");
            // Convert (not just strip) `#[vcheck]` on free fns: the sentinel
            // lets classify hard-error on a marked fn with no contract
            // clauses instead of silently emitting nothing (see
            // `convert_vcheck_to_sentinel_item`).
            convert_vcheck_to_sentinel_item(&mut item);
            if let Item::Impl(im) = &mut item {
                for (mi, ii) in im.items.iter_mut().enumerate() {
                    if let ImplItem::Fn(f) = ii {
                        stamp_miri_mode_sentinel_impl_fn(f);
                        stamp_backend_sentinel_impl_fn(f);
                        stamp_bolero_mode_sentinel_impl_fn(f);
                        // Same skip-regular-harness sentinel for impl
                        // methods folded solely because of a stmt-level
                        // `#[vcheck]` assert.
                        if inline_assert_only_impl_methods.contains(&(i, mi)) {
                            stamp_skip_regular_harness_on_attrs(Some(&mut f.attrs));
                        }
                        convert_vcheck_to_sentinel_impl_fn(f);
                        strip_attr_impl_fn(f, "vcheck_provide");
                        // NOTE: deliberately do NOT strip `vcheck_cov_mutate`
                        // or `vcheck_cov_fuzz` from items going to the engine.
                        // The verus_spec_check classify step inside the engine
                        // block needs the attribute to capture metadata; it
                        // strips after capture.
                    }
                }
            }
            // Apply the resolved substitution before handing the item to the
            // engine. For non-generic items this is a no-op.
            if let Some(s) = item_substs.get(&i) {
                if !s.is_empty() {
                    substitute_item(&mut item, s);
                }
            }
            // Strip type-args from references to monomorphized siblings.
            strip_type_args_for_names(&mut item, &stripped_type_names);
            engine_items.push(item);
        } else {
            // Defensive: a stray `#[vcheck]` / `#[vcheck_provide]` on an item we did
            // not fold (e.g. an unsupported item kind) must still be stripped
            // so it never reaches rustc as an unknown attribute.
            strip_attr_item(&mut item, "vcheck_provide");
            strip_attr_item(&mut item, "vcheck");
            if let Item::Impl(im) = &mut item {
                for ii in &mut im.items {
                    if let ImplItem::Fn(f) = ii {
                        convert_vcheck_to_sentinel_impl_fn(f);
                        strip_attr_impl_fn(f, "vcheck_cov_mutate");
                        strip_attr_impl_fn(f, "vcheck_cov_fuzz");
                        strip_attr_impl_fn(f, "vcheck_provide");
                    }
                }
            }
            remaining.push(item);
        }
    }

    // If no items were folded despite a marker being present, the markers
    // were on unsupported item kinds. We've already stripped them; emitting
    // an empty engine block would be harmless but pointless, so skip it.
    if engine_items.is_empty() {
        *items = remaining;
        return true;
    }
    // 5. Fold the engine group into one verus_spec_check_unverified! invocation.
    // We emit the call through `::verus_spec_check::verus_spec_check_unverified!`
    // rather than a `vstd` path so this works against stock vstd. Users only
    // need `verus_spec_check` as a top-level crate dep.
    let macro_call: TokenStream2 = quote! {
        ::verus_spec_check::verus_spec_check_unverified! {
            #(#engine_items)*
        }
    };
    let macro_item: Item =
        verus_syn::parse2(macro_call).expect("vcheck: synthesized macro item must parse");
    remaining.push(macro_item);

    *items = remaining;
    true
}
