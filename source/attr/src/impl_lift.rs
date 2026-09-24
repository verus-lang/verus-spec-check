use super::*;

/// Rewrite a marked trait impl `impl<T> Trait for X<T> { ... }` into an
/// inherent impl `impl<T> X<T> { ... }`, mangling each method name with the
/// trait's identifier (e.g. `view` becomes `View_view`) so multiple traits
/// implemented for the same Self type don't collide. Removes the trait
/// header in place. Best-effort: if the trait path is qualified, uses the
/// last segment as the prefix.
pub fn rewrite_trait_impl_to_inherent(im: &mut verus_syn::ItemImpl) {
    let trait_prefix = match &im.trait_ {
        Some((_, path, _)) => path
            .segments
            .last()
            .map(|s| s.ident.to_string())
            .unwrap_or_else(|| "_".to_string()),
        None => return,
    };
    // Drop the `Trait for` part.
    im.trait_ = None;
    // Mangle method names.
    for ii in &mut im.items {
        if let ImplItem::Fn(f) = ii {
            let new_name = format_ident!("{}_{}", trait_prefix, f.sig.ident);
            f.sig.ident = new_name;
        }
    }
}

/// Decide whether a Self type can host an inherent impl in the harness's
/// scope. Returns `false` for types where rustc's orphan rule (or
/// primitive-vs-impl rules, or unsized-vs-Sized requirements) would reject
/// `impl <ty> { ... }`.
///
/// Rejects:
///   - Primitive types (`[T; N]`, `[T]`, `str`, `u8`..`u128`, `i8`..`i128`,
///     `usize`, `isize`, `f32`, `f64`, `bool`, `char`).
///   - External-crate paths (anything starting with `core`, `std`, `alloc`).
///   - Tuple, reference, pointer types.
///
/// Accepts: single-segment ident paths whose name isn't reserved. The
/// caller still needs to verify the name is actually in-block; this is a
/// fast structural check.
pub fn self_ty_supports_inherent_impl(ty: &Type) -> bool {
    match ty {
        Type::Path(tp) => {
            if tp.qself.is_some() {
                return false;
            }
            if tp.path.leading_colon.is_some() {
                return false;
            }
            if tp.path.segments.is_empty() {
                return false;
            }
            // Multi-segment paths like `core::ops::Range` are external.
            // Single-segment is what user-defined sibling types look like.
            if tp.path.segments.len() > 1 {
                let head = tp.path.segments[0].ident.to_string();
                if matches!(head.as_str(), "core" | "std" | "alloc") {
                    return false;
                }
                // Other multi-segment paths: conservatively treat as external.
                return false;
            }
            // Single-segment: reject primitive names.
            let name = tp.path.segments[0].ident.to_string();
            !matches!(
                name.as_str(),
                "u8" | "u16"
                    | "u32"
                    | "u64"
                    | "u128"
                    | "usize"
                    | "i8"
                    | "i16"
                    | "i32"
                    | "i64"
                    | "i128"
                    | "isize"
                    | "f32"
                    | "f64"
                    | "bool"
                    | "char"
                    | "str"
                    // Standard external types where adding inherent methods
                    // would violate the orphan rule.
                    | "String"
                    | "Vec"
                    | "Option"
                    | "Result"
                    | "HashMap"
                    | "HashSet"
            )
        }
        // Slices, arrays, references, pointers, tuples, etc. all reject
        // inherent impls.
        _ => false,
    }
}

/// Build a free-fn substitute for a method inside a trait impl. Used when
/// the impl's Self type doesn't permit an inherent rewrite (primitive,
/// unsized, or external). The new fn:
///   - Takes the receiver as a regular `__vcheck_self` parameter typed the
///     same way (`&Self`, `&mut Self`, or `Self` for owned).
///   - Inherits the impl's generics.
///   - Has its body and contract clauses rewritten so every `self` token
///     becomes `__vcheck_self`.
///   - Is named `<TraitPrefix>_<orig_method>` to avoid collisions when the
///     same method name appears in multiple traits.
pub fn lift_trait_method_to_free_fn(
    impl_generics: &verus_syn::Generics,
    self_ty: &Type,
    trait_prefix: &str,
    method: &verus_syn::ImplItemFn,
) -> Option<verus_syn::ItemFn> {
    use verus_syn::token::Paren;
    use verus_syn::{FnArg, FnArgKind, FnMode, ModeExec, Pat, PatType, Token};
    let synth_self_name: Ident = Ident::new("__vcheck_self", proc_macro2::Span::call_site());

    // Step 1: produce a transformed Signature with the receiver replaced by
    // a typed `__vcheck_self: <Self type>` first param. We do this by
    // rebuilding the inputs list.
    let mut new_sig = method.sig.clone();
    new_sig.ident = format_ident!("{}_{}", trait_prefix, new_sig.ident);
    let mut new_inputs: verus_syn::punctuated::Punctuated<FnArg, Token![,]> =
        verus_syn::punctuated::Punctuated::new();
    for arg in new_sig.inputs.iter() {
        match &arg.kind {
            FnArgKind::Receiver(rcv) => {
                let recv_ty: Type = if let Some((_amp, lt)) = &rcv.reference {
                    // `&self` / `&'a self` / `&mut self` / `&'a mut self`.
                    // Preserve any explicit lifetime so the receiver and
                    // return type can share it (e.g. `fn f<'a>(&'a self)
                    // -> &'a str`). Without this, rustc errors with
                    // "explicit lifetime required" when the wrapper is
                    // synthesized for an impl method that ties its
                    // return lifetime to `&'a self`.
                    match (lt, rcv.mutability.is_some()) {
                        (Some(lt), true) => verus_syn::parse_quote! { &#lt mut #self_ty },
                        (Some(lt), false) => verus_syn::parse_quote! { &#lt #self_ty },
                        (None, true) => verus_syn::parse_quote! { &mut #self_ty },
                        (None, false) => verus_syn::parse_quote! { &#self_ty },
                    }
                } else {
                    self_ty.clone()
                };
                let pat: Pat = verus_syn::parse_quote! { #synth_self_name };
                new_inputs.push(FnArg {
                    kind: FnArgKind::Typed(PatType {
                        attrs: Vec::new(),
                        pat: Box::new(pat),
                        colon_token: Token![:](rcv.self_token.span),
                        ty: Box::new(recv_ty),
                    }),
                    tracked: None,
                });
            }
            FnArgKind::Typed(_) => {
                new_inputs.push(arg.clone());
            }
        }
    }
    new_sig.inputs = new_inputs;

    // A lifted method is now a free function, where `Self` is not a legal
    // type. Replace every bare `Self` in typed parameters and the return type
    // with the impl's full self type (including generic arguments), e.g.
    // `other: Self` becomes `other: HashSet<Item>`.
    struct ReplaceSelfType<'a> {
        self_ty: &'a Type,
    }
    impl verus_syn::visit_mut::VisitMut for ReplaceSelfType<'_> {
        fn visit_type_mut(&mut self, ty: &mut Type) {
            let is_bare_self = matches!(
                ty,
                Type::Path(tp)
                    if tp.qself.is_none()
                        && tp.path.leading_colon.is_none()
                        && tp.path.segments.len() == 1
                        && tp.path.segments[0].ident == "Self"
            );
            if is_bare_self {
                *ty = self.self_ty.clone();
                return;
            }
            verus_syn::visit_mut::visit_type_mut(self, ty);
        }
    }
    let mut replace_self_type = ReplaceSelfType { self_ty };
    verus_syn::visit_mut::VisitMut::visit_signature_mut(&mut replace_self_type, &mut new_sig);

    // Step 2: merge impl-level generics into the fn's. Drop conflicts
    // (impl-level params with the same name take precedence for the fn body).
    let mut merged_generics = impl_generics.clone();
    for p in new_sig.generics.params.iter() {
        merged_generics.params.push(p.clone());
    }
    if let Some(wc) = &new_sig.generics.where_clause {
        match &mut merged_generics.where_clause {
            Some(existing) => {
                for pred in wc.predicates.iter() {
                    existing.predicates.push(pred.clone());
                }
            }
            None => {
                merged_generics.where_clause = Some(wc.clone());
            }
        }
    }
    new_sig.generics = merged_generics;

    // Step 3: ensure the fn is `exec` mode.
    new_sig.fn_token = Token![fn](proc_macro2::Span::call_site());
    if !matches!(new_sig.mode, FnMode::Exec(..)) {
        new_sig.mode = FnMode::Exec(ModeExec {
            exec_token: Token![exec](proc_macro2::Span::call_site()),
        });
    }

    // Step 4: rewrite `self` -> `__vcheck_self` in BOTH the signature's spec
    // clauses (requires/ensures/returns/decreases) and the body. We do this
    // token-wise by emitting each, running the rewrite, and re-parsing.
    let block = &method.block;
    let body_tokens = crate::exec_spec::replace_self_tokens(quote! { #block }, &synth_self_name);
    let new_block: verus_syn::Block = match verus_syn::parse2(body_tokens) {
        Ok(b) => b,
        Err(_) => return None,
    };

    // Same treatment for the spec clauses. The clauses live in
    // `new_sig.spec` as `Option<Requires>` / `Option<Ensures>` / etc. We
    // rewrite the inner expressions in-place.
    fn rewrite_specification_self(spec: &mut verus_syn::Specification, replacement: &Ident) {
        for e in spec.exprs.iter_mut() {
            let toks = quote! { #e };
            let rewritten = crate::exec_spec::replace_self_tokens(toks, replacement);
            if let Ok(new_e) = verus_syn::parse2::<Expr>(rewritten) {
                *e = new_e;
            }
        }
    }
    if let Some(req) = &mut new_sig.spec.requires {
        rewrite_specification_self(&mut req.exprs, &synth_self_name);
    }
    if let Some(ens) = &mut new_sig.spec.ensures {
        rewrite_specification_self(&mut ens.exprs, &synth_self_name);
    }
    if let Some(ret) = &mut new_sig.spec.returns {
        rewrite_specification_self(&mut ret.exprs, &synth_self_name);
    }

    // Step 5: copy attrs and ensure `#[verifier::external_body]` is set.
    let mut new_attrs = method.attrs.clone();
    let has_external_body = new_attrs.iter().any(|a| {
        let p = a.path();
        p.segments.len() == 2
            && p.segments[0].ident == "verifier"
            && p.segments[1].ident == "external_body"
    });
    if !has_external_body {
        let ext: Attribute = verus_syn::parse_quote! { #[verifier::external_body] };
        new_attrs.push(ext);
    }
    // The mangled `<Trait>_<method>` ident violates snake-case lint;
    // suppress so the lifted fn doesn't pollute the user's warning output.
    let allow_naming: Attribute = verus_syn::parse_quote! { #[allow(non_snake_case)] };
    new_attrs.push(allow_naming);
    let _ = Paren::default();
    Some(verus_syn::ItemFn {
        attrs: new_attrs,
        vis: method.vis.clone(),
        sig: new_sig,
        block: Box::new(new_block),
        semi_token: None,
    })
}
