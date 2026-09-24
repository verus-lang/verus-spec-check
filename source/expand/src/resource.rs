use super::*;

/// Pair each `ParamShape::Resource` permission param with a
/// `ParamShape::ResourceHandle` (`PPtr<V>`) param of the same `V`, in
/// signature order, filling `handle_ident` in the resource shape. Returns
/// the map from permission ident to its shadow-model ident, used by the
/// clause pre-pass.
///
/// Both halves are mandatory: a permission without its handle can't be
/// coupled to real memory (the harness would have nothing to pass for the
/// pointer), and a bare `PPtr<V>` without a permission has no
/// materialization source.
pub fn pair_resource_params(
    param_idents: &[Ident],
    param_shapes: &mut [ParamShape],
) -> Result<HashMap<String, Ident>, Error> {
    // Collect handle candidates: (index, V-token-string, tier), unconsumed.
    let mut handle_slots: Vec<(usize, String, ResourceTier, bool)> = Vec::new();
    for (i, shape) in param_shapes.iter().enumerate() {
        if let ParamShape::ResourceHandle { value_ty, tier } = shape {
            handle_slots.push((i, quote!(#value_ty).to_string(), *tier, false));
        }
    }

    let mut models: HashMap<String, Ident> = HashMap::new();
    for i in 0..param_shapes.len() {
        let (value_str, perm_ident) = match &param_shapes[i] {
            ParamShape::Resource { value_ty, .. } => {
                (quote!(#value_ty).to_string(), param_idents[i].clone())
            }
            _ => continue,
        };
        let slot = handle_slots
            .iter_mut()
            .find(|(_, v, _, used)| !*used && *v == value_str);
        let Some((handle_idx, _, handle_tier, used)) = slot else {
            return Err(Error::new_spanned(
                &param_idents[i],
                format!(
                    "verus_spec_check: permission parameter `{perm_ident}` has no matching \
handle parameter (`PPtr<{value_str}>`, `*mut {value_str}`, or `*const {value_str}`) to \
couple to. The harness materializes real memory for the sampled model and must pass \
its pointer somewhere; add the handle to the signaturs."
                ),
            ));
        };
        *used = true;
        let tier = *handle_tier;
        let handle_ident = param_idents[*handle_idx].clone();
        if let ParamShape::Resource {
            handle_ident: h,
            tier: t,
            ..
        } = &mut param_shapes[i]
        {
            *h = Some(handle_ident);
            *t = Some(tier);
        }
        models.insert(perm_ident.to_string(), resource_model_ident(&perm_ident));
    }

    // Any handle left unpaired has no materialization source.
    if let Some((i, v, _, _)) = handle_slots.iter().find(|(_, _, _, used)| !used) {
        return Err(Error::new_spanned(
            &param_idents[*i],
            format!(
                "verus_spec_check: pointer/handle parameter has no matching \
`Tracked<&PointsTo<{v}>>` / `Tracked<&mut PointsTo<{v}>>` permission parameter. A bare \
pointer can't be sampled (there is no memory behind it); pair it with a permission so \
the harness can materialize coupled state."
            ),
        ));
    }

    Ok(models)
}

/// Outcome of the resource clause pre-pass.
pub enum ResourceClauseDisposition {
    /// Clause kept (projections rewritten onto shadow models); feed it to
    /// the normal contract rewriter.
    Keep(Expr),
    /// Clause is over handle-identity ghost state (`perm.pptr() == ptr`
    /// etc.) that holds by construction and has no runtime observable —
    /// drop it. Ensures droppage is counted by the caller so a harness
    /// whose EVERY ensures clause is dropped errors out as vacuous.
    Skip,
    /// Clause is a standalone post-state tag (`final(perm).is_init()` /
    /// `is_uninit()` on a `&mut` permission). Consumed as an observation
    /// *directive*: it selects the guard transition and read-back protocol
    /// rather than being asserted (asserting it against the model the tag
    /// itself produced would be circular). Its claim is still exposed:
    /// value assertions read through the tag's protocol, and a wrong tag
    /// surfaces as failing values or Miri-visible leaks/invalid reads.
    Directive,
}

/// Contract-directed post-state tag for a `&mut` permission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourcePostTag {
    Init,
    Uninit,
}

/// Post-state observation plan accumulated across the ensures clauses of a
/// fn with `&mut` permission params.
#[derive(Default)]
pub struct ResourcePostPlan {
    /// perm ident -> post-state tag from standalone `final(perm).is_*()`
    /// directive clauses.
    pub post_tag: HashMap<String, ResourcePostTag>,
    /// perms whose `final(perm).value()` is projected — forces a certified
    /// read-back after the call.
    pub needs_post_value: HashSet<String>,
}

/// Which contract state a permission projection refers to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceStateRef {
    /// Bare `perm` — pre and post coincide for shared borrows; ambiguous
    /// (and rejected) for `&mut`.
    Bare,
    /// `old(perm)` — pre-call state (the sampled model).
    Old,
    /// `final(perm)` — post-call state (read-back / directive).
    Final,
}

/// If `e` (possibly wrapped in `old(..)` / `final(..)` / parens) is a
/// reference to a known permission param, return its name and which state
/// the wrapper refers to.
pub fn resource_receiver(
    e: &Expr,
    models: &HashMap<String, Ident>,
) -> Option<(String, ResourceStateRef)> {
    fn bare_name(e: &Expr, models: &HashMap<String, Ident>) -> Option<String> {
        match e {
            Expr::Paren(p) => bare_name(&p.expr, models),
            _ => ident_of_expr(e).filter(|n| models.contains_key(n)),
        }
    }
    match e {
        Expr::Paren(p) => resource_receiver(&p.expr, models),
        Expr::Final(f) => bare_name(&f.arg, models).map(|n| (n, ResourceStateRef::Final)),
        Expr::Call(c) => {
            if let Expr::Path(p) = c.func.as_ref() {
                if p.path.is_ident("old") && c.args.len() == 1 {
                    return bare_name(&c.args[0], models).map(|n| (n, ResourceStateRef::Old));
                }
            }
            None
        }
        _ => bare_name(e, models).map(|n| (n, ResourceStateRef::Bare)),
    }
}

/// Clause pre-pass for permission params: classify + rewrite each requires/ensures clause BEFORE the
/// generic `ContractRewriter` sees it.
///
///   - pre-state projections (`perm.is_init()` for shared borrows,
///     `old(perm).value()` etc.) -> exec calls on the `__vcheck_model_<perm>`
///     shadow binding;
///   - post-state value projections (`final(perm).value()`, `&mut` only)
///     -> exec calls on the `__vcheck_post_model_<perm>` read-back binding
///     (recorded in `plan.needs_post_value`);
///   - standalone post-state tags (`final(perm).is_init()` /
///     `is_uninit()`) -> `Directive` (recorded in `plan.post_tag`);
///   - handle-identity projections (`pptr()`, `ptr()`, `addr()`) -> the
///     whole clause is dropped (`Skip`): ghost bookkeeping guaranteed by
///     constructor replay, with no runtime observable;
///   - anything else that touches the permission (whole-view `perm@`,
///     `mem_contents()` comparisons, bare `perm` on a `&mut` permission,
///     `final()` in requires) -> targeted diagnostic.
pub fn rewrite_resource_clause(
    clause: &Expr,
    models: &HashMap<String, Ident>,
    modes: &HashMap<String, ResourceMode>,
    is_ensures: bool,
    plan: &mut ResourcePostPlan,
) -> Result<ResourceClauseDisposition, Error> {
    if models.is_empty() {
        return Ok(ResourceClauseDisposition::Keep(clause.clone()));
    }

    // Standalone post-state tag clause? Detected at the top level BEFORE
    // the projection rewriter runs: `final(perm).is_init()` as a WHOLE
    // ensures clause is an observation directive, not an assertion.
    // (Embedded occurrences — `final(perm).is_init() && ...` — are
    // rejected by the rewriter below: mixing a directive into a boolean
    // expression has no evaluable meaning.)
    if is_ensures {
        let mut top = clause;
        while let Expr::Paren(p) = top {
            top = &p.expr;
        }
        if let Expr::MethodCall(mc) = top {
            if mc.args.is_empty() {
                if let Some((name, ResourceStateRef::Final)) =
                    resource_receiver(&mc.receiver, models)
                {
                    if modes.get(&name) == Some(&ResourceMode::MutRef) {
                        let tag = match mc.method.to_string().as_str() {
                            "is_init" => Some(ResourcePostTag::Init),
                            "is_uninit" => Some(ResourcePostTag::Uninit),
                            _ => None,
                        };
                        if let Some(tag) = tag {
                            if let Some(prev) = plan.post_tag.insert(name.clone(), tag) {
                                if prev != tag {
                                    return Err(Error::new_spanned(
                                        clause,
                                        format!(
                                            "verus_spec_check: conflicting post-state tags for \
permission `{name}`: the ensures clauses claim both `is_init()` and `is_uninit()`."
                                        ),
                                    ));
                                }
                            }
                            return Ok(ResourceClauseDisposition::Directive);
                        }
                    }
                }
            }
        }
    }

    struct Rewriter<'a> {
        models: &'a HashMap<String, Ident>,
        modes: &'a HashMap<String, ResourceMode>,
        is_ensures: bool,
        plan: &'a mut ResourcePostPlan,
        skip: bool,
        err: Option<Error>,
    }
    impl Rewriter<'_> {
        fn fail(&mut self, spanned: &dyn quote::ToTokens, msg: String) {
            self.err = Some(Error::new_spanned(spanned, msg));
        }
    }
    impl VisitMut for Rewriter<'_> {
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            if self.skip || self.err.is_some() {
                return;
            }
            // Decompose whole-`MemContents` comparisons BEFORE the
            // projection walk sees the bare `mem_contents()`/`opt_value()`
            // call: `recv.opt_value() == MemContents::Init(v)` is
            // equivalent to `recv.is_init() && recv.value() == v`, and
            // `== MemContents::Uninit` to `recv.is_uninit()`. (Either
            // orientation.) This lets contracts like vstd's
            // `ptr_mut_write` take a direct `#[vcheck]`.
            if let Expr::Binary(bin) = e {
                if matches!(bin.op, verus_syn::BinOp::Eq(_)) {
                    let sides = [(&bin.left, &bin.right), (&bin.right, &bin.left)];
                    let mut rewritten: Option<Expr> = None;
                    for (proj_side, ctor_side) in sides {
                        let recv: Option<Expr> = match proj_side.as_ref() {
                            Expr::MethodCall(mc)
                                if (mc.method == "mem_contents" || mc.method == "opt_value")
                                    && mc.args.is_empty()
                                    && resource_receiver(&mc.receiver, self.models).is_some() =>
                            {
                                Some((*mc.receiver).clone())
                            }
                            _ => None,
                        };
                        let Some(recv) = recv else { continue };
                        match ctor_side.as_ref() {
                            // `MemContents::Init(v)` (any path spelling)
                            Expr::Call(call) => {
                                if let Expr::Path(p) = call.func.as_ref() {
                                    let is_init_ctor = p
                                        .path
                                        .segments
                                        .last()
                                        .map(|s| s.ident == "Init")
                                        .unwrap_or(false);
                                    if is_init_ctor && call.args.len() == 1 {
                                        let v = call.args.first().unwrap().clone();
                                        rewritten = Some(verus_syn::parse_quote! {
                                            ((#recv).is_init() && (#recv).value() == (#v))
                                        });
                                    }
                                }
                            }
                            // `MemContents::Uninit`
                            Expr::Path(p) => {
                                let is_uninit_ctor = p
                                    .path
                                    .segments
                                    .last()
                                    .map(|s| s.ident == "Uninit")
                                    .unwrap_or(false);
                                if is_uninit_ctor {
                                    rewritten = Some(verus_syn::parse_quote! {
                                        ((#recv).is_uninit())
                                    });
                                }
                            }
                            _ => {}
                        }
                        if rewritten.is_some() {
                            break;
                        }
                    }
                    if let Some(new_e) = rewritten {
                        *e = new_e;
                        // Recurse into the decomposed form so the
                        // projections get routed to the shadow model.
                        verus_syn::visit_mut::visit_expr_mut(self, e);
                        return;
                    }
                }
            }
            // Whole-view projections of a permission (`perm@`, `perm.view()`,
            // `perm.deep_view()`) aren't supported: the view is a
            // `PointsToData`-like struct whose exec mirror doesn't exist yet.
            let view_inner: Option<Expr> = match e {
                Expr::View(v) => Some((*v.expr).clone()),
                Expr::MethodCall(mc)
                    if (mc.method == "view" || mc.method == "deep_view") && mc.args.is_empty() =>
                {
                    Some((*mc.receiver).clone())
                }
                _ => None,
            };
            if let Some(inner) = view_inner {
                if resource_receiver(&inner, self.models).is_some() {
                    self.fail(
                        &*e,
                        "verus_spec_check: whole-view projection of a permission (`perm@` / \
`perm.view()`) is not supported yet. Use the method projections instead: `is_init()`, \
`is_uninit()`, `value()`."
                            .to_string(),
                    );
                    return;
                }
            }
            if let Expr::MethodCall(mc) = e {
                if let Some((name, sref)) = resource_receiver(&mc.receiver, self.models) {
                    let mode = *self.modes.get(&name).expect("mode registered per perm");
                    let method = mc.method.to_string();
                    match method.as_str() {
                        // Handle-identity / provenance ghost state: true by
                        // construction (the guard materialized the memory
                        // the permission speaks for), no runtime observable.
                        "pptr" | "ptr" | "addr" | "id" | "provenance" => {
                            self.skip = true;
                            return;
                        }
                        "mem_contents" | "opt_value" => {
                            self.fail(
                                &*e,
                                "verus_spec_check: comparing a permission's whole `mem_contents()` \
is not supported yet. Rewrite the clause with `is_init()` / `is_uninit()` / `value()` \
projections."
                                    .to_string(),
                            );
                            return;
                        }
                        "is_init" | "is_uninit" | "value" if mc.args.is_empty() => {}
                        other => {
                            self.fail(
                                &*e,
                                format!(
                                    "verus_spec_check: unsupported projection `.{other}()` on \
permission `{name}`. Supported: `is_init()`, `is_uninit()`, `value()`; handle-identity \
clauses (`pptr()`, `addr()`) are discharged by construction."
                                ),
                            );
                            return;
                        }
                    }
                    // Which model does the projection read? Shared borrows
                    // are state-constant: old/final/bare all mean the
                    // sampled model. `&mut` permissions distinguish states
                    // and require explicit markers.
                    let model: Ident = match (mode, sref, self.is_ensures) {
                        (ResourceMode::Ref | ResourceMode::Owned, _, _) => {
                            resource_model_ident(&format_ident!("{}", name))
                        }
                        (ResourceMode::MutRef, ResourceStateRef::Old, _) => {
                            resource_model_ident(&format_ident!("{}", name))
                        }
                        (ResourceMode::MutRef, ResourceStateRef::Bare, _) => {
                            self.fail(
                                &*e,
                                format!(
                                    "verus_spec_check: bare `{name}.{method}()` on a `&mut` \
permission is ambiguous between pre- and post-state. Write `old({name}).{method}()` or \
`final({name}).{method}()` explicitly."
                                ),
                            );
                            return;
                        }
                        (ResourceMode::MutRef, ResourceStateRef::Final, false) => {
                            self.fail(
                                &*e,
                                format!(
                                    "verus_spec_check: `final({name})` cannot appear in a \
requires clause (there is no post-state before the call)."
                                ),
                            );
                            return;
                        }
                        (ResourceMode::MutRef, ResourceStateRef::Final, true) => {
                            match method.as_str() {
                                "value" => {
                                    self.plan.needs_post_value.insert(name.clone());
                                    resource_post_model_ident(&format_ident!("{}", name))
                                }
                                // is_init / is_uninit embedded in a larger
                                // expression: directives must be standalone
                                // clauses (see the top-level check).
                                _ => {
                                    self.fail(
                                        &*e,
                                        format!(
                                            "verus_spec_check: `final({name}).{method}()` must be a \
standalone ensures clause — it directs the harness's post-state observation protocol and \
can't be embedded in a larger expression."
                                        ),
                                    );
                                    return;
                                }
                            }
                        }
                    };
                    let exec_method = format_ident!("exec_{}", method);
                    *e = verus_syn::parse_quote! { (&#model).#exec_method() };
                    return;
                }
            }
            verus_syn::visit_mut::visit_expr_mut(self, e);
        }
    }

    // Whole-clause `final(perm).mem_contents() == MemContents::Init(v)` /
    // `== MemContents::Uninit`: decompose at the CLAUSE level, because the
    // is_init/is_uninit half is a post-state observation directive that
    // must stand alone. Init(v) registers the tag and leaves the value
    // comparison as the clause; Uninit is a pure directive.
    let mut working = clause.clone();
    if is_ensures {
        let mut top = clause;
        while let Expr::Paren(p) = top {
            top = &p.expr;
        }
        if let Expr::Binary(bin) = top {
            if matches!(bin.op, verus_syn::BinOp::Eq(_)) {
                let sides = [(&bin.left, &bin.right), (&bin.right, &bin.left)];
                for (proj_side, ctor_side) in sides {
                    let recv_info = match proj_side.as_ref() {
                        Expr::MethodCall(mc)
                            if (mc.method == "mem_contents" || mc.method == "opt_value")
                                && mc.args.is_empty() =>
                        {
                            resource_receiver(&mc.receiver, models)
                                .map(|(n, s)| (n, s, (*mc.receiver).clone()))
                        }
                        _ => None,
                    };
                    let Some((name, sref, recv)) = recv_info else {
                        continue;
                    };
                    if !(sref == ResourceStateRef::Final
                        && modes.get(&name) == Some(&ResourceMode::MutRef))
                    {
                        continue;
                    }
                    let register =
                        |plan: &mut ResourcePostPlan, tag: ResourcePostTag| -> Result<(), Error> {
                            if let Some(prev) = plan.post_tag.insert(name.clone(), tag) {
                                if prev != tag {
                                    return Err(Error::new_spanned(
                                        clause,
                                        format!(
                                            "verus_spec_check: conflicting post-state tags for \
permission `{name}`: the ensures clauses claim both `is_init()` and `is_uninit()`."
                                        ),
                                    ));
                                }
                            }
                            Ok(())
                        };
                    match ctor_side.as_ref() {
                        Expr::Call(call) if call.args.len() == 1 => {
                            if let Expr::Path(p) = call.func.as_ref() {
                                if p.path.segments.last().map(|s| s.ident == "Init") == Some(true) {
                                    register(plan, ResourcePostTag::Init)?;
                                    let v = call.args.first().unwrap().clone();
                                    working = verus_syn::parse_quote! { #recv.value() == (#v) };
                                    break;
                                }
                            }
                        }
                        Expr::Path(p) => {
                            if p.path.segments.last().map(|s| s.ident == "Uninit") == Some(true) {
                                register(plan, ResourcePostTag::Uninit)?;
                                return Ok(ResourceClauseDisposition::Directive);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    let mut rewritten = working;
    let mut rw = Rewriter {
        models,
        modes,
        is_ensures,
        plan,
        skip: false,
        err: None,
    };
    rw.visit_expr_mut(&mut rewritten);
    if let Some(err) = rw.err {
        return Err(err);
    }
    if rw.skip {
        return Ok(ResourceClauseDisposition::Skip);
    }

    // Leftover bare permission idents (positions the projection rewrite
    // didn't consume) would reach the generic rewriter as `Option<V>`
    // sample bindings — a silent type confusion. Reject.
    struct BareScan<'a> {
        models: &'a HashMap<String, Ident>,
        found: Option<String>,
    }
    impl<'ast> verus_syn::visit::Visit<'ast> for BareScan<'_> {
        fn visit_expr_path(&mut self, p: &'ast ExprPath) {
            if self.found.is_none() && p.qself.is_none() && p.path.segments.len() == 1 {
                let name = p.path.segments[0].ident.to_string();
                if self.models.contains_key(&name) {
                    self.found = Some(name);
                }
            }
        }
    }
    let mut scan = BareScan {
        models,
        found: None,
    };
    verus_syn::visit::Visit::visit_expr(&mut scan, &rewritten);
    if let Some(name) = scan.found {
        return Err(Error::new_spanned(
            clause,
            format!(
                "verus_spec_check: permission `{name}` is used in a position the harness can't \
evaluate. Permissions have no runtime value; contracts may only project them via \
`is_init()` / `is_uninit()` / `value()`."
            ),
        ));
    }

    Ok(ResourceClauseDisposition::Keep(rewritten))
}

#[cfg(test)]
mod resource_param_tests {
    use super::*;

    fn expand_text(input: TokenStream2) -> String {
        let out = expand(input.into(), false);
        Into::<TokenStream2>::into(out).to_string()
    }

    fn harness_of(text: &str) -> &str {
        text.split("mod __verus_spec_check_")
            .nth(1)
            .expect("harness module expected")
    }

    /// The ptr_ref-shaped fn: shared permission + handle + value ensures
    fn read_it_input() -> TokenStream2 {
        quote! {
            #[verifier::external_body]
            pub exec fn read_it(ptr: PPtr<u32>, Tracked(perm): Tracked<&PointsTo<u32>>) -> (v: u32)
                requires
                    perm.pptr() == ptr,
                    perm.is_init(),
                ensures
                    v == perm.value(),
            {
                *ptr.borrow(Tracked(perm))
            }
        }
    }

    #[test]
    fn shared_permission_produces_materializing_harness() {
        let text = expand_text(read_it_input());
        assert!(
            !text.contains("compile_error"),
            "expansion should succeed: {text}"
        );
        let h = harness_of(&text);
        // Model binding lowers the sampled Option<u32> into the shadow model.
        assert!(
            h.contains("__vcheck_model_perm"),
            "shadow model binding expected: {h}"
        );
        assert!(
            h.contains("exec_mem_contents_from_option"),
            "model lowering expected: {h}"
        );
        // Materialization via the guard; handle shadowed from it.
        assert!(
            h.contains("VcheckDynResourceGuard"),
            "guard materialization expected: {h}"
        );
        assert!(
            h.contains("__vcheck_guard_perm . handle ()"),
            "handle shadow expected: {h}"
        );
        // The fn under test receives a minted ZST for the permission.
        assert!(
            h.contains("Tracked :: assume_new ()"),
            "minted Tracked arg expected: {h}"
        );
        // requires: `perm.is_init()` filters on the model...
        assert!(h.contains("exec_is_init"), "is_init filter expected: {h}");
        // ...while the handle-identity clause is dropped entirely (no
        // `.pptr()` projection survives; the `simple_pptr::PPtr` guard
        // type path is expected).
        assert!(
            !h.contains(". pptr ("),
            "handle-identity clause must be dropped: {h}"
        );
        // ensures: value projection evaluates against the model.
        assert!(h.contains("exec_value"), "value projection expected: {h}");
    }

    #[test]
    fn owned_permission_rejected_with_roadmap() {
        let text = expand_text(quote! {
            pub exec fn consume_it(ptr: PPtr<u32>, Tracked(perm): Tracked<PointsTo<u32>>)
                requires perm.is_init(),
            {
            }
        });
        assert!(
            text.contains("compile_error"),
            "owned mode must be rejected: {text}"
        );
        assert!(
            text.contains("not supported yet"),
            "roadmap message expected: {text}"
        );
    }

    #[test]
    fn mut_permission_raw_tier_write_shape() {
        let text = expand_text(quote! {
            #[verifier::external_body]
            pub exec fn write_it(ptr: *mut u32, Tracked(perm): Tracked<&mut PointsTo<u32>>, v: u32)
                requires
                    old(perm).ptr() == ptr,
                ensures
                    final(perm).is_init(),
                    final(perm).value() == v,
            {
                ptr_mut_write(ptr, Tracked(perm), v)
            }
        });
        assert!(
            !text.contains("compile_error"),
            "&mut raw shape should expand: {text}"
        );
        let h = harness_of(&text);
        // Raw-tier materializer + teardown.
        assert!(h.contains("allocate"), "raw allocate expected: {h}");
        assert!(h.contains("deallocate"), "raw deallocate expected: {h}");
        assert!(h.contains("ptr_mut_write"), "raw init-write expected: {h}");
        // Directive -> guard transition, not an assertion.
        assert!(
            h.contains("mark_init"),
            "is_init directive -> mark_init: {h}"
        );
        // final(perm).value() -> read-back into the post model.
        assert!(h.contains("read_back"), "read-back expected: {h}");
        assert!(
            h.contains("__vcheck_post_model_perm"),
            "post model expected: {h}"
        );
        assert!(h.contains("ptr_mut_read"), "raw read-back op expected: {h}");
    }

    /// `ptr_mut_read` wrapper shape -- post-state tag `Uninit`
    /// (a directive, no read-back since no `final().value()` clause) and
    /// the returned value asserted against the PRE-state model.
    #[test]
    fn mut_permission_read_shape_uninit_directive() {
        let text = expand_text(quote! {
            #[verifier::external_body]
            pub exec fn read_it(ptr: *mut u32, Tracked(perm): Tracked<&mut PointsTo<u32>>) -> (v: u32)
                requires
                    old(perm).ptr() == ptr,
                    old(perm).is_init(),
                ensures
                    final(perm).is_uninit(),
                    v == old(perm).value(),
            {
                ptr_mut_read(ptr, Tracked(perm))
            }
        });
        assert!(
            !text.contains("compile_error"),
            "read shape should expand: {text}"
        );
        let h = harness_of(&text);
        assert!(
            h.contains("mark_uninit"),
            "is_uninit directive -> mark_uninit: {h}"
        );
        assert!(
            !h.contains("read_back"),
            "no read-back without final().value(): {h}"
        );
        // v == old(perm).value() evaluates on the PRE model.
        assert!(h.contains("__vcheck_model_perm"), "pre model expected: {h}");
        assert!(
            h.contains("exec_value"),
            "pre-state value projection expected: {h}"
        );
    }

    /// Bare `perm.X()` on a `&mut` permission is ambiguous — must error.
    #[test]
    fn mut_permission_bare_projection_rejected() {
        let text = expand_text(quote! {
            pub exec fn f(ptr: *mut u32, Tracked(perm): Tracked<&mut PointsTo<u32>>) -> (b: bool)
                ensures b == perm.is_init(),
            {
                true
            }
        });
        assert!(
            text.contains("compile_error"),
            "bare &mut projection must error: {text}"
        );
        assert!(
            text.contains("ambiguous"),
            "ambiguity message expected: {text}"
        );
    }

    /// `final(perm)` in a requires clause is nonsensical — must error.
    #[test]
    fn final_in_requires_rejected() {
        let text = expand_text(quote! {
            pub exec fn f(ptr: *mut u32, Tracked(perm): Tracked<&mut PointsTo<u32>>) -> (b: bool)
                requires final(perm).is_init(),
                ensures b,
            {
                true
            }
        });
        assert!(
            text.contains("compile_error"),
            "final in requires must error: {text}"
        );
    }

    /// Conflicting post-state tags — must error.
    #[test]
    fn conflicting_post_tags_rejected() {
        let text = expand_text(quote! {
            pub exec fn f(ptr: *mut u32, Tracked(perm): Tracked<&mut PointsTo<u32>>) -> (v: u32)
                ensures
                    final(perm).is_init(),
                    final(perm).is_uninit(),
                    v == old(perm).value(),
            {
                0
            }
        });
        assert!(
            text.contains("compile_error"),
            "conflicting tags must error: {text}"
        );
        assert!(text.contains("conflicting post-state tags"), "{text}");
    }

    /// `final(perm).value()` together with `final(perm).is_uninit()` —
    /// there is no post-value to read from uninitialized memory.
    #[test]
    fn post_value_of_uninit_rejected() {
        let text = expand_text(quote! {
            pub exec fn f(ptr: *mut u32, Tracked(perm): Tracked<&mut PointsTo<u32>>) -> (v: u32)
                ensures
                    final(perm).is_uninit(),
                    final(perm).value() == 0,
            {
                0
            }
        });
        assert!(
            text.contains("compile_error"),
            "value-of-uninit must error: {text}"
        );
        assert!(text.contains("no post-state value"), "{text}");
    }

    /// Owned `Tracked<PointsTo<V>>` stays rejected (consumption tracking
    /// is future work)
    #[test]
    fn owned_permission_still_rejected() {
        let text = expand_text(quote! {
            pub exec fn consume_it(ptr: *mut u32, Tracked(perm): Tracked<PointsTo<u32>>)
                requires old(perm).is_init(),
            {
            }
        });
        assert!(
            text.contains("compile_error"),
            "owned mode must stay rejected: {text}"
        );
    }

    #[test]
    fn permission_without_handle_is_error() {
        let text = expand_text(quote! {
            pub exec fn no_handle(Tracked(perm): Tracked<&PointsTo<u32>>) -> (b: bool)
                ensures b == perm.is_init(),
            {
                true
            }
        });
        assert!(
            text.contains("compile_error"),
            "unpaired permission must error: {text}"
        );
        assert!(
            text.contains("no matching"),
            "pairing message expected: {text}"
        );
    }

    #[test]
    fn handle_without_permission_is_error() {
        let text = expand_text(quote! {
            pub exec fn no_perm(ptr: PPtr<u32>) -> (b: bool)
                ensures b,
            {
                true
            }
        });
        assert!(
            text.contains("compile_error"),
            "unpaired handle must error: {text}"
        );
        assert!(
            text.contains("no matching"),
            "pairing message expected: {text}"
        );
    }

    #[test]
    fn whole_view_projection_rejected() {
        let text = expand_text(quote! {
            pub exec fn viewer(ptr: PPtr<u32>, Tracked(perm): Tracked<&PointsTo<u32>>) -> (b: bool)
                ensures b == (perm@.opt_value is Init),
            {
                true
            }
        });
        assert!(
            text.contains("compile_error"),
            "perm@ must be rejected: {text}"
        );
        assert!(
            text.contains("is_init"),
            "diagnostic should name supported projections: {text}"
        );
    }

    /// Whole-`MemContents` equality decomposes into the supported
    /// projections (`is_init() && value() == v` / `is_uninit()`) instead
    /// of being rejected.
    #[test]
    fn mem_contents_comparison_decomposes_to_projections() {
        let text = expand_text(quote! {
            pub exec fn cmp(ptr: PPtr<u32>, Tracked(perm): Tracked<&PointsTo<u32>>) -> (b: bool)
                ensures b == (perm.mem_contents() == MemContents::Init(1u32)),
            {
                true
            }
        });
        assert!(
            !text.contains("compile_error"),
            "mem_contents cmp against a ctor must decompose, not reject: {text}"
        );
        assert!(
            text.contains("is_init"),
            "decomposed clause must route through is_init: {text}"
        );
    }

    #[test]
    fn old_final_wrappers_normalize_to_model() {
        let text = expand_text(quote! {
            #[verifier::external_body]
            pub exec fn read_it2(ptr: PPtr<u32>, Tracked(perm): Tracked<&PointsTo<u32>>) -> (v: u32)
                requires
                    old(perm).is_init(),
                ensures
                    v == final(perm).value(),
            {
                *ptr.borrow(Tracked(perm))
            }
        });
        assert!(
            !text.contains("compile_error"),
            "old/final should normalize: {text}"
        );
        let h = harness_of(&text);
        assert!(h.contains("exec_is_init"), "{h}");
        assert!(h.contains("exec_value"), "{h}");
        assert!(
            !h.contains("__vcheck_pre_perm"),
            "no snapshot machinery for shared perms: {h}"
        );
    }
}
