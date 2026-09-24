//! Support for lifting inline forall and exists quantifiers

use super::*;

/// Bounded-domain quantifier lowering for higher-order contracts.
///
/// Rewrites the two `contains`-bounded quantifier shapes into linear scans
/// over the (runtime) sequence, so clauses like
///
/// ```text
/// forall|elem: T| s.contains(elem) ==> call_ensures(pred, (&elem,), true)
/// exists|elem: T| s.contains(elem) && call_ensures(pred, (&elem,), true)
/// ```
///
/// become
///
/// ```text
/// (s).iter().cloned().all(|elem: T| call_ensures(pred, (&elem,), true))
/// (s).iter().cloned().any(|elem: T| call_ensures(pred, (&elem,), true))
/// ```
///
/// The bound `s` and the body are left intact for the `ContractRewriter`
/// to lower afterwards (views, `old()` snapshots, `call_ensures` on
/// sampled predicates). `.cloned()` makes the binder an owned `T` at
/// runtime, matching its spec-side type, so `&elem` in the body is `&T`.
///
/// GATED: fires only when the closure body mentions a sampled predicate
/// ident. Everything else keeps the existing behavior (quantifier lifting
/// into a synthetic spec fn compiled by exec_spec).
///
/// `#[trigger]` attributes inside the rewritten quantifier are stripped —
/// they are SMT instrumentation with no runtime meaning (and are not
/// valid Rust in expression position).
pub fn rewrite_pred_bounded_quantifiers(expr: &mut Expr, sampled_pred_idents: &HashSet<String>) {
    use verus_syn::{visit_mut, BinOp};
    struct R<'a> {
        preds: &'a HashSet<String>,
    }
    impl<'a> R<'a> {
        fn mentions_pred(&self, e: &Expr) -> bool {
            let toks = quote! { #e }.to_string();
            self.preds.iter().any(|p| {
                // Cheap ident scan on token text with boundary chars.
                toks.split(|c: char| !c.is_alphanumeric() && c != '_')
                    .any(|w| w == p)
            })
        }
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            // Recurse first so nested quantifiers rewrite inside-out.
            visit_mut::visit_expr_mut(self, e);
            // Closure-method form: `<seq>.all(|x| body)` / `<seq>.any(|x| body)`
            // where the body mentions a sampled pred. Same lowering as the
            // quantifier forms: linear scan with an owned binder.
            if let Expr::MethodCall(mc) = e {
                let m = mc.method.to_string();
                if (m == "all" || m == "any") && mc.args.len() == 1 {
                    if let Expr::Closure(cl) = &mc.args[0] {
                        if cl.inputs.len() == 1 && self.mentions_pred(&cl.body) {
                            let binder = cl.inputs[0].clone();
                            let mut body = (*cl.body).clone();
                            strip_trigger_attrs(&mut body);
                            let mut recv = (*mc.receiver).clone();
                            strip_trigger_attrs(&mut recv);
                            let method: Ident = format_ident!("{}", m);
                            *e = verus_syn::parse_quote! {
                                (#recv).iter().cloned().#method(|#binder| #body)
                            };
                            return;
                        }
                    }
                }
            }
            let Expr::Unary(u) = e else { return };
            let is_forall = matches!(u.op, UnOp::Forall(..));
            let is_exists = matches!(u.op, UnOp::Exists(..));
            if !is_forall && !is_exists {
                return;
            }
            let Expr::Closure(closure) = u.expr.as_ref() else {
                return;
            };
            if closure.inputs.len() != 1 {
                return;
            }
            let binder = closure.inputs[0].clone();
            let binder_ident = match &binder.pat {
                verus_syn::Pat::Type(pt) => match pt.pat.as_ref() {
                    verus_syn::Pat::Ident(pi) => pi.ident.to_string(),
                    _ => return,
                },
                verus_syn::Pat::Ident(pi) => pi.ident.to_string(),
                _ => return,
            };
            if !self.mentions_pred(&closure.body) {
                return;
            }
            // Peel parens/blocks around the body.
            let mut body: &Expr = &closure.body;
            loop {
                match body {
                    Expr::Paren(p) => body = &p.expr,
                    Expr::Group(g) => body = &g.expr,
                    _ => break,
                }
            }
            // Match `<guard> ==> <rest>` (forall) / `<guard> && <rest>` (exists),
            // where <guard> is `<seq>.contains(<binder>)`.
            let Expr::Binary(bin) = body else { return };
            let op_ok = (is_forall && matches!(bin.op, BinOp::Imply(_)))
                || (is_exists && matches!(bin.op, BinOp::And(_)));
            if !op_ok {
                return;
            }
            // Guard may carry a `#[trigger]` attribute; matching ignores attrs.
            let mut guard: &Expr = &bin.left;
            loop {
                match guard {
                    Expr::Paren(p) => guard = &p.expr,
                    Expr::Group(g) => guard = &g.expr,
                    _ => break,
                }
            }
            let Expr::MethodCall(mc) = guard else { return };
            if mc.method != "contains" || mc.args.len() != 1 {
                return;
            }
            let Some(arg_name) = ident_of_expr(&mc.args[0]) else {
                return;
            };
            if arg_name != binder_ident {
                return;
            }
            let seq_expr = (*mc.receiver).clone();
            let mut rest = (*bin.right).clone();
            strip_trigger_attrs(&mut rest);
            let mut seq_expr = seq_expr;
            strip_trigger_attrs(&mut seq_expr);
            let method: Ident = if is_forall {
                format_ident!("all")
            } else {
                format_ident!("any")
            };
            *e = verus_syn::parse_quote! {
                (#seq_expr).iter().cloned().#method(|#binder| #rest)
            };
        }
    }
    let mut r = R {
        preds: sampled_pred_idents,
    };
    r.visit_expr_mut(expr);
}

/// Remove `#[trigger]` / `#[auto]` attributes from every expression in the
/// tree. These are SMT trigger annotations — meaningless (and un-compilable)
/// in the runtime harness.
pub fn strip_trigger_attrs(expr: &mut Expr) {
    use verus_syn::visit_mut;
    struct S;
    impl VisitMut for S {
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            if let Some(attrs) = expr_attrs_mut(e) {
                attrs.retain(|a| {
                    let name = a.path().segments.last().map(|s| s.ident.to_string());
                    !matches!(name.as_deref(), Some("trigger") | Some("auto"))
                });
            }
            visit_mut::visit_expr_mut(self, e);
        }
    }
    S.visit_expr_mut(expr);
}

/// Mutable access to an expression's outer attributes, for the variants
/// that can carry them in contract positions.
pub fn expr_attrs_mut(e: &mut Expr) -> Option<&mut Vec<verus_syn::Attribute>> {
    match e {
        Expr::MethodCall(x) => Some(&mut x.attrs),
        Expr::Call(x) => Some(&mut x.attrs),
        Expr::Binary(x) => Some(&mut x.attrs),
        Expr::Unary(x) => Some(&mut x.attrs),
        Expr::Paren(x) => Some(&mut x.attrs),
        Expr::Path(x) => Some(&mut x.attrs),
        Expr::Field(x) => Some(&mut x.attrs),
        Expr::Index(x) => Some(&mut x.attrs),
        Expr::View(x) => Some(&mut x.attrs),
        _ => None,
    }
}

/// Detects whether an expression contains a `forall` or `exists` quantifier.
/// We walk the AST with verus_syn's read-only visitor.
pub fn contains_quantifier(expr: &Expr) -> bool {
    struct QFinder {
        found: bool,
    }
    impl<'a> Visit<'a> for QFinder {
        fn visit_expr_unary(&mut self, e: &'a ExprUnary) {
            if matches!(e.op, UnOp::Forall(..) | UnOp::Exists(..)) {
                self.found = true;
                return;
            }
            verus_syn::visit::visit_expr_unary(self, e);
        }
    }
    let mut f = QFinder { found: false };
    f.visit_expr(expr);
    f.found
}

/// Free-variable analysis: collect all simple-path identifiers reachable from
/// `expr` that are NOT bound locally by a closure / let / pattern. This is a
/// best-effort pass — when in doubt it returns the ident as a free variable
/// (the worst case is that the synthetic spec fn carries an unused
/// parameter, which is benign).
pub fn collect_free_idents(expr: &Expr, exclude_built_ins: bool) -> Vec<String> {
    struct Collector {
        bound: Vec<String>,
        free: Vec<String>,
        exclude_built_ins: bool,
    }
    impl Collector {
        fn is_built_in(&self, name: &str) -> bool {
            // Don't capture commonly-used type / module names that are not
            // actual local variables. Verus / Rust language keywords aren't
            // visited as ident expressions.
            matches!(name, "true" | "false" | "Some" | "None" | "Ok" | "Err")
        }
    }
    impl<'a> Visit<'a> for Collector {
        fn visit_expr_closure(&mut self, c: &'a verus_syn::ExprClosure) {
            // Closure params: bind each ident pattern in the body scope.
            let snapshot = self.bound.len();
            for input in &c.inputs {
                collect_pat_binders(&input.pat, &mut self.bound);
            }
            verus_syn::visit::visit_expr(self, &c.body);
            self.bound.truncate(snapshot);
        }
        fn visit_expr_path(&mut self, p: &'a ExprPath) {
            if p.qself.is_none()
                && p.path.segments.len() == 1
                && matches!(p.path.segments[0].arguments, PathArguments::None)
            {
                let name = p.path.segments[0].ident.to_string();
                if !self.bound.contains(&name) {
                    if !(self.exclude_built_ins && self.is_built_in(&name)) {
                        if !self.free.contains(&name) {
                            self.free.push(name);
                        }
                    }
                }
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
        fn visit_local(&mut self, l: &'a verus_syn::Local) {
            // Visit the init expression in the OLD scope, then bind.
            if let Some(init) = &l.init {
                verus_syn::visit::visit_expr(self, &init.expr);
            }
            collect_pat_binders(&l.pat, &mut self.bound);
        }
    }

    fn collect_pat_binders(pat: &Pat, bound: &mut Vec<String>) {
        match pat {
            Pat::Ident(pi) => bound.push(pi.ident.to_string()),
            Pat::Type(pt) => collect_pat_binders(&pt.pat, bound),
            Pat::Tuple(t) => {
                for p in &t.elems {
                    collect_pat_binders(p, bound);
                }
            }
            Pat::TupleStruct(ts) => {
                for p in &ts.elems {
                    collect_pat_binders(p, bound);
                }
            }
            Pat::Struct(s) => {
                for f in &s.fields {
                    collect_pat_binders(&f.pat, bound);
                }
            }
            _ => {}
        }
    }

    let mut c = Collector {
        bound: vec![],
        free: vec![],
        exclude_built_ins,
    };
    c.visit_expr(expr);
    c.free
}

/// Walk a contract clause and detect references the macro definitely cannot
/// turn into a runnable form. Returns a descriptive error if found.
///
/// NOTE: method calls on user-typed receivers are not flagged here. They are
/// always lowered to `<T as ToExecModel>::to_exec_model(..)
/// .exec_<m>()`, which resolves across files by trait/path. If the type was
/// never `#[vcheck_provide]`'d, the `on_unimplemented` diagnostics on
/// `ToExecModel` / `VcheckSpecCompanion` fire at the harness call site — a
/// better, localized error than a macro-time guess. This function is retained
/// as a hook for future high-confidence checks; currently it accepts
/// everything.
pub fn check_clause_resolvable(
    _clause: &Expr,
    _spec_fn_names: &HashSet<String>,
    _user_typed_idents: &HashMap<String, Ident>,
    _self_ident: Option<&Ident>,
) -> Result<(), Error> {
    Ok(())
}

#[allow(dead_code)]
pub fn check_clause_resolvable_unused(
    clause: &Expr,
    spec_fn_names: &HashSet<String>,
    user_typed_idents: &HashMap<String, Ident>,
    self_ident: Option<&Ident>,
) -> Result<(), Error> {
    struct Checker<'a> {
        spec_fn_names: &'a HashSet<String>,
        user_typed_idents: &'a HashMap<String, Ident>,
        self_ident: Option<&'a Ident>,
        error: Option<Error>,
    }
    impl<'a> Checker<'a> {
        fn receiver_is_user_typed(&self, recv: &Expr) -> bool {
            if let Some(name) = ident_of_expr(recv) {
                if self.user_typed_idents.contains_key(&name) {
                    return true;
                }
                if let Some(s) = self.self_ident {
                    if name == s.to_string() {
                        return true;
                    }
                }
            }
            false
        }
    }
    impl<'ast, 'a> Visit<'ast> for Checker<'a> {
        fn visit_expr_method_call(&mut self, mc: &'ast verus_syn::ExprMethodCall) {
            let method = mc.method.to_string();
            if self.error.is_none()
                && self.receiver_is_user_typed(&mc.receiver)
                && !self.spec_fn_names.contains(&method)
                && !is_known_runtime_method(&method)
            {
                self.error = Some(Error::new_spanned(
                    &mc.method,
                    format!(
                        "verus_spec_check: the contract calls `.{method}(...)`, but `{method}` is \
                         not a spec fn defined inside this verus_spec_check_unverified! block.\n\n\
                         The harness needs a runnable companion (`exec_{method}`) to evaluate \
                         this clause, and the macro can only generate one for spec fns it can \
                         see between its own braces. If `{method}` is defined in another module \
                         or file, the macro cannot reach it.\n\n\
                         Fix: move the spec fn `{method}` (and any types/spec fns it depends on) \
                         into this same `verus_spec_check_unverified! {{ ... }}` block.",
                        method = method
                    ),
                ));
            }
            verus_syn::visit::visit_expr_method_call(self, mc);
        }
    }
    let mut c = Checker {
        spec_fn_names,
        user_typed_idents,
        self_ident,
        error: None,
    };
    c.visit_expr(clause);
    match c.error {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// Methods the engine / runtime knows how to compile on exec values. These
/// are NOT spec fns the user defined, so they must not be flagged as
/// "unresolved spec method". Mirrors the method list in exec_spec.rs plus
/// the deep_view bridge.
pub fn is_known_runtime_method(name: &str) -> bool {
    matches!(
        name,
        "deep_view"
            | "len"
            | "dom"
            | "index"
            | "drop_first"
            | "drop_last"
            | "add"
            | "push"
            | "update"
            | "subrange"
            | "to_multiset"
            | "take"
            | "skip"
            | "last"
            | "first"
            | "count"
            | "is_prefix_of"
            | "is_suffix_of"
            | "contains"
            | "contains_key"
            | "get"
            | "index_of"
            | "index_of_first"
            | "index_of_last"
            | "insert"
            | "remove"
            | "intersect"
            | "union"
            | "difference"
            | "sub"
            | "unwrap"
            | "as_slice"
            | "clone"
    )
}

/// Rewrite `int` / `nat` types appearing as quantifier-bound variable types
/// (in `forall`/`exists` closure params) to runtime equivalents (`i64`/`u64`).
/// The engine's `exec_spec` rejects spec-only `int`/`nat` for quantified vars,
/// so the lift pass needs to swap them before producing the synthetic spec
/// fn body. The rewrite is conservative — it only touches *closure
/// parameter* types, not arbitrary type positions, so spec-side semantics
/// (like `s.len()` returning `nat`) are preserved.
pub fn rewrite_int_nat_in_quantifiers(expr: &mut Expr) {
    struct R;
    impl VisitMut for R {
        fn visit_expr_closure_mut(&mut self, c: &mut verus_syn::ExprClosure) {
            for input in c.inputs.iter_mut() {
                rewrite_pat_int_nat(&mut input.pat);
            }
            verus_syn::visit_mut::visit_expr_closure_mut(self, c);
        }
    }
    fn rewrite_pat_int_nat(pat: &mut verus_syn::Pat) {
        if let verus_syn::Pat::Type(pt) = pat {
            replace_int_nat_in_type(&mut pt.ty);
        }
    }
    fn replace_int_nat_in_type(ty: &mut Type) {
        if let Type::Path(tp) = ty {
            if tp.qself.is_none() && tp.path.segments.len() == 1 {
                let name = tp.path.segments[0].ident.to_string();
                if name == "int" {
                    *ty = verus_syn::parse_quote! { i64 };
                    return;
                }
                if name == "nat" {
                    *ty = verus_syn::parse_quote! { u64 };
                    return;
                }
            }
        }
    }
    R.visit_expr_mut(expr);
}

/// For a clause that contains an inline quantifier, lift the entire clause
/// into a synthetic `spec fn __vcheck_clause_<n>(...)`. Returns:
///   - the synthetic spec fn (as an `ItemFn` to push into engine_items)
///   - a replacement clause that calls it: `__vcheck_clause_n(arg1, arg2, ...)`
///
/// Free-variable analysis selects which params of the exec fn (and which
/// `result` ident, if any) the clause captures.
pub fn lift_quantified_clause(
    clause: &Expr,
    exec_fn_name: &Ident,
    counter: &mut u64,
    param_specs: &[(Ident, TokenStream2)], // (name, spec_type) for each fn param
    return_ident: Option<&Ident>,
    return_shape: &ReturnShape,
) -> (TokenStream2, TokenStream2) {
    let id = *counter;
    *counter += 1;
    let synth_name = format_ident!("__vcheck_clause_{}_{}", exec_fn_name, id);

    // Engine restriction: quantifier-bound variables must be a runtime
    // primitive int (`u32`, `i64`, etc.); `int` / `nat` are spec-only and
    // rejected. Rewrite the spec types to runtime equivalents (`int -> i64`,
    // `nat -> u64`) before lifting so contracts written in spec arithmetic
    // can still be vcheck'd.
    let mut clause = clause.clone();
    rewrite_int_nat_in_quantifiers(&mut clause);

    // Give the return-value binder a hygienic name inside the synthetic
    // clause spec fn. The `exec_spec` companion generator names its own
    // return value `res`, so a contract whose return binder is literally
    // `res` (the vstd convention, e.g. `-> (res: Vec<T>)`) would produce a
    // synthetic fn with a param `res` colliding with that internal return.
    // Rename it up-front to a reserved alias; the call site still passes the
    // real return value.
    let ret_alias = format_ident!("__vcheck_ret_val");
    if let Some(ri) = return_ident {
        rename_ident_in_expr(&mut clause, &ri.to_string(), &ret_alias);
    }

    // Handle `old(<param>)` inside the clause. A synthetic clause spec fn is a
    // pure function of its arguments, so the `&mut` pre-state can't be
    // recovered inside its body — it must be passed as its own parameter.
    // Rewrite each `old(<p>)` to a fresh `__vcheck_old_<p>` ident here; below we
    // add a matching synthetic param and pass `old(<p>).deep_view()` at the
    // call site, where the ContractRewriter lowers `old(..)` to the snapshot.
    let old_param_names = collect_old_call_params(&clause);
    // (alias_string, original_ident, spec_type) for each `old(<param>)`.
    let mut old_aliases: Vec<(String, Ident, TokenStream2)> = Vec::new();
    for name in &old_param_names {
        if let Some((orig, spec_ty)) = param_specs.iter().find(|(p, _)| &p.to_string() == name) {
            let alias = format_ident!("__vcheck_old_{}", name);
            rewrite_old_call_to_ident(&mut clause, name, &alias);
            old_aliases.push((alias.to_string(), orig.clone(), spec_ty.clone()));
        }
    }

    let free = collect_free_idents(&clause, /*exclude_built_ins=*/ true);

    // Build (param_name, spec_type) pairs for the synthetic spec fn,
    // dropping any free idents that aren't params or the return.
    let mut sig_params: Vec<(Ident, TokenStream2)> = Vec::new();
    let mut call_args: Vec<TokenStream2> = Vec::new();

    for free_name in &free {
        // Match against an `old(<param>)` alias: synthetic param carries the
        // pre-state spec type; the call site passes `old(<orig>).deep_view()`
        // so the ContractRewriter lowers it to the pre-call snapshot.
        if let Some((alias, orig, spec_ty)) = old_aliases.iter().find(|(a, _, _)| a == free_name) {
            let alias_id = format_ident!("{}", alias);
            sig_params.push((alias_id, spec_ty.clone()));
            call_args.push(quote! { old(#orig).deep_view() });
            continue;
        }
        // Match against fn parameters first.
        if let Some((id, spec_ty)) = param_specs.iter().find(|(p, _)| p == free_name) {
            sig_params.push((id.clone(), spec_ty.clone()));
            // The harness call passes `<param>.deep_view()` for the spec
            // type; that's already handled by ContractRewriter when it sees
            // the synthetic spec fn — except the synthetic spec fn ITSELF
            // takes the spec type and the rewriter gets the call form. We
            // want the call site of the lifted clause to read
            // `__vcheck_clause_n(<param>.deep_view(), ...)`, then the existing
            // rewriter strips `.deep_view()` per param shape.
            call_args.push(quote! { #id.deep_view() });
            continue;
        }
        // Match against the return ident (now renamed to `ret_alias` in the
        // clause body above). The synthetic param uses the hygienic alias,
        // but the call site passes the real return value.
        if let Some(ri) = return_ident {
            if free_name == &ret_alias.to_string() {
                let spec_ty = return_shape_to_spec_type(return_shape);
                sig_params.push((ret_alias.clone(), spec_ty));
                call_args.push(quote! { #ri.deep_view() });
                continue;
            }
        }
        // Free vars that don't bind to params: skip silently. They're
        // probably constants or names from the surrounding module.
    }

    let sig_param_decls = sig_params.iter().map(|(n, t)| quote! { #n: #t });

    // Emit the synthetic spec fn.
    let body = clause.clone();
    let synth_fn = quote! {
        spec fn #synth_name(#(#sig_param_decls),*) -> bool {
            #body
        }
    };

    let replacement = quote! { #synth_name(#(#call_args),*) };
    (synth_fn, replacement)
}

pub fn return_shape_to_spec_type(shape: &ReturnShape) -> TokenStream2 {
    match shape {
        ReturnShape::Unit => quote! { () },
        ReturnShape::Primitive => quote! { _ }, // shouldn't happen in practice
        ReturnShape::OwnedVec(e)
        | ReturnShape::RefSlice(e)
        | ReturnShape::MutRefSlice(e)
        | ReturnShape::OwnedVecDeque(e) => {
            let inner = match e {
                ParamElem::Primitive(t) => quote! { #t },
                ParamElem::UserType(n) => quote! { #n },
            };
            quote! { Seq<#inner> }
        }
        ReturnShape::OwnedArray(e, _)
        | ReturnShape::RefArray(e, _)
        | ReturnShape::MutRefArray(e, _) => {
            let inner = match e {
                ParamElem::Primitive(t) => quote! { #t },
                ParamElem::UserType(n) => quote! { #n },
            };
            quote! { Seq<#inner> }
        }
        ReturnShape::OwnedOption(e) => {
            let inner = match e {
                ParamElem::Primitive(t) => quote! { #t },
                ParamElem::UserType(n) => quote! { #n },
            };
            quote! { Option<#inner> }
        }
        ReturnShape::OwnedResult(t, e) => {
            let tt = match t {
                ParamElem::Primitive(t) => quote! { #t },
                ParamElem::UserType(n) => quote! { #n },
            };
            let et = match e {
                ParamElem::Primitive(t) => quote! { #t },
                ParamElem::UserType(n) => quote! { #n },
            };
            quote! { Result<#tt, #et> }
        }
        ReturnShape::OwnedHashMap => quote! { Map<_, _> },
        ReturnShape::OwnedHashSet => quote! { Set<_> },
        ReturnShape::OwnedBTreeMap => quote! { Map<_, _> },
        ReturnShape::OwnedBTreeSet => quote! { Set<_> },
        ReturnShape::OwnedMultiset => quote! { Multiset<_> },
        ReturnShape::OwnedUserType(n) | ReturnShape::RefUserType(n) => quote! { #n },
        ReturnShape::RefPrimitive(t) => quote! { #t },
        ReturnShape::RefStr | ReturnShape::OwnedString => quote! { Seq<char> },
        ReturnShape::OwnedOrdering => quote! { ::core::cmp::Ordering },
        ReturnShape::OwnedOptionOrdering => quote! { Option<::core::cmp::Ordering> },
        ReturnShape::OpaqueConcretize(_) => quote! { int },
        ReturnShape::Tuple2(_, _) => quote! { (_, _) },
    }
}
