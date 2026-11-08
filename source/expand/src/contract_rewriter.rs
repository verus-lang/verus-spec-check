//! Contract type rewriter, which is applied to each `requires` / `ensures`
//! expression. It has two jobs:
//!   1. Strip `.deep_view()` method calls (the receiver becomes the harness
//!      binding directly).
//!   2. Rename calls to known spec fns: `f(x)` -> `exec_f(x)` for free fns,
//!      and `x.f(...)` -> `x.exec_f(...)` for spec methods.
//!
//! The contract rewriter is in a sense a layer over exec_spec. While
//! exec_spec does most of the work in making contracts executable, 
//! the contract rewriter enables the support of particularly nasty types
//! e.g. int, nat, real, and mut with dedicated runtime environments. For example,
//! int requires the num_bigint library at runtime.

use super::*;

/// Whether a harness-level ident holds a `Map`-shaped (`HashMap`) or
/// `Set`-shaped (`HashSet`) value. Used by the contract rewriter to route
/// `Map`/`Set` view operations (`insert`/`remove`/`contains_key`/`index`)
/// to the `ExecMap`/`ExecSet` companions (or the real `HashMap`/`HashSet`
/// method) instead of the `Seq` slice-shape lowering.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MapSetKind {
    Map,
    Set,
}

fn peel_paren_deref(mut cur: &Expr) -> &Expr {
    loop {
        match cur {
            Expr::Paren(p) => cur = p.expr.as_ref(),
            Expr::Unary(u) if matches!(u.op, UnOp::Deref(_)) => cur = u.expr.as_ref(),
            _ => return cur,
        }
    }
}

pub struct ContractRewriter<'a> {
    pub spec_fn_names: &'a HashSet<String>,
    /// Per parameter: how `<param>.deep_view()` translates at the call site.
    /// For `&mut`-shaped params this is the *post-call* view (after the
    /// real fn returns); the pre-call view is in `pre_view_for`.
    pub param_call_form: &'a HashMap<String, TokenStream2>,
    /// Per parameter: how `old(<param>).deep_view()` translates. Only
    /// populated for `&mut` params; for normal params the pre-state and
    /// post-state are the same, so `old(<id>)` is treated as `<id>` at
    /// the rewriter level.
    pub pre_view_for: &'a HashMap<String, TokenStream2>,
    /// Idents whose value is a user-defined type at the harness level (the
    /// user's OWN type, e.g. `User`). Maps ident-name -> user type name. Used
    /// to insert `__vcheck_to_exec_T(&x)` conversions before spec-fn / spec-
    /// method calls that expect the engine `Exec*` form.
    pub user_typed_idents: &'a HashMap<String, Ident>,
    /// Idents whose value is owned at the harness level but whose spec-fn
    /// signature takes a borrow (`&str` for owned `String`, `&[T]` for
    /// owned `Vec<T>`, etc.). When the rewriter sees `f(<id>)` for a
    /// known spec fn `f` and `<id>` is in this map, it inserts `&` (or
    /// `.as_str()` / `.as_slice()` as appropriate). Maps ident-name ->
    /// borrow-form expression.
    pub auto_borrow_idents: &'a HashMap<String, TokenStream2>,
    /// `runtime fn name -> spec fn name` redirect for
    /// `#[verifier::when_used_as_spec(...)]`. When rewriting `f(args)` in a
    /// contract, we redirect to `exec_<spec_name>(args)` instead of
    /// `exec_<f>(args)` if `f` is in this map.
    pub when_used_as_spec_redirect: &'a HashMap<String, String>,
    /// Idents (and their `__vcheck_pre_*` snapshots) that hold a `HashMap`/
    /// `HashSet` value, so `<id>@.<map-op>(..)` routes to the map/set
    /// companions rather than the `Seq` lowering.
    pub map_set_shaped_idents: &'a HashMap<String, MapSetKind>,
    /// Idents holding a sampled `VcheckPred` value (`ParamShape::PredFn`
    /// params). `call_ensures(<id>, (x,), r)` / `<id>.ensures((x,), r)`
    /// lower to `<id>.models(x, r)`; `call_requires` / `.requires` lower
    /// to `true` (the sampled family is total).
    pub sampled_pred_idents: &'a HashSet<String>,
    pub return_ident: Option<Ident>,
    pub return_shape: ReturnShape,
    /// Idents bound (via `let`) to a `__vcheck_int::*` expression during
    /// the contract-rewrite pass. Used by the comparison-lift and
    /// if-arm-unification logic so that subsequent uses of the ident
    /// are treated as `SpecInt`-valued without needing type info.
    /// `visit_local_mut` populates this on the fly.
    pub spec_int_idents: HashSet<String>,
    /// Idents bound (via `let`) to a `__vcheck_real::*` expression — the real
    /// analogue of `spec_int_idents`. Lets a subsequent use of the ident be
    /// treated as `SpecReal`-valued so arithmetic/comparisons route to
    /// `__vcheck_real::*`. `visit_local_mut` populates it.
    pub spec_real_idents: HashSet<String>,
    /// Names of `external_vcheck_provide!` twins whose return type is
    /// `int`/`nat` (their exec companions return `SpecInt`). Calls to them
    /// route casts/comparisons through the `__vcheck_int` domain.
    pub int_returning_provided: HashSet<String>,
}

impl<'a> ContractRewriter<'a> {
    /// The std value kind of a `ret->Some_0` / `ret->Ok_0` / `ret->Err_0` projection.
    fn std_value_return_projection(&self, e: &Expr) -> Option<StdValueKind> {
        let ret_ident = self.return_ident.as_ref()?;
        let Expr::GetField(egf) = peel_paren_deref(e) else {
            return None;
        };
        if !expr_is_ident(peel_paren_deref(&egf.base), ret_ident) {
            return None;
        }
        let member = match &egf.member {
            verus_syn::Member::Named(id) => id.to_string(),
            verus_syn::Member::Unnamed(idx) => idx.index.to_string(),
        };
        let elem = match (member.as_str(), &self.return_shape) {
            ("Some_0", ReturnShape::OwnedOption(elem)) => elem,
            ("Ok_0", ReturnShape::OwnedResult(elem, _)) => elem,
            ("Err_0", ReturnShape::OwnedResult(_, elem)) => elem,
            _ => return None,
        };
        let ParamElem::Primitive(ty) = elem else {
            return None;
        };
        std_value_kind(ty, &HashSet::new())
    }

    /// If `e` (a method-call receiver) resolves to a map/set-shaped ident —
    /// through the already-lowered `@` view (`&<id>`), an `old()` snapshot
    /// (`&__vcheck_pre_<id>`), or a bare ident — return its kind. Peels a
    /// single `&`/`*`.
    fn resolve_mapset(&self, e: &Expr) -> Option<MapSetKind> {
        let inner: &Expr = match e {
            Expr::Reference(r) => r.expr.as_ref(),
            Expr::Unary(u) if matches!(u.op, UnOp::Deref(_)) => u.expr.as_ref(),
            other => other,
        };
        ident_of_expr(inner).and_then(|n| self.map_set_shaped_idents.get(&n).copied())
    }

    /// If `e` is a bare ident that we've registered as SpecInt-typed
    /// (via a `let x = __vcheck_int::...` binding), return `&x` instead
    /// so passing through the comparison/arithmetic helpers doesn't
    /// move the binding. Otherwise return `e` as-is. The `IntoSpecInt`
    /// impl for `&SpecInt` clones internally, so the resulting call
    /// is equivalent in value while leaving the binding intact for
    /// later use in the contract.
    fn borrow_form_for_spec_int_ident(&self, e: &Expr) -> Expr {
        if let Some(name) = ident_of_expr(e) {
            if self.spec_int_idents.contains(&name) {
                let id = format_ident!("{}", name);
                return verus_syn::parse_quote! { &#id };
            }
        }
        e.clone()
    }

    /// Recursive analogue of `is_call_to_vcheck_int_returning_int` that
    /// also considers idents bound via `let` to a SpecInt expression
    /// (registered in `spec_int_idents`), and looks through parens /
    /// blocks / if-else tails. Used to decide whether to lift a
    /// comparison, narrow a cast, or wrap a sibling if-arm.
    pub fn expr_tail_is_vcheck_int(&self, expr: &Expr) -> bool {
        let mut cur = expr;
        loop {
            match cur {
                Expr::Paren(p) => cur = p.expr.as_ref(),
                Expr::Block(b) => match b.block.stmts.last() {
                    Some(verus_syn::Stmt::Expr(e, None)) => cur = e,
                    _ => return false,
                },
                Expr::If(eif) => {
                    let then_has = match eif.then_branch.stmts.last() {
                        Some(verus_syn::Stmt::Expr(e, None)) => self.expr_tail_is_vcheck_int(e),
                        _ => false,
                    };
                    let else_has = match &eif.else_branch {
                        Some((_, e)) => self.expr_tail_is_vcheck_int(e),
                        None => false,
                    };
                    return then_has || else_has;
                }
                Expr::Call(c) => {
                    // `exec_<name>(..)` where <name> is an int/nat-returning
                    // external_vcheck_provide! twin: the companion returns a
                    // SpecInt, so casts/comparisons route through __vcheck_int.
                    if let Expr::Path(ExprPath {
                        path, qself: None, ..
                    }) = c.func.as_ref()
                    {
                        if path.segments.len() == 1 {
                            let n = path.segments[0].ident.to_string();
                            if let Some(base) = n.strip_prefix("exec_") {
                                if self.int_returning_provided.contains(base) {
                                    return true;
                                }
                            }
                            if self.int_returning_provided.contains(&n) {
                                return true;
                            }
                        }
                    }
                    return is_call_to_vcheck_int_returning_int(cur);
                }
                // `<expr>.vcheck_realize()` returns a `SpecInt`, so a comparison
                // with it as an operand should lift into `__vcheck_int::*`.
                Expr::MethodCall(mc) if mc.method == "vcheck_realize" => return true,
                Expr::Path(ExprPath {
                    path, qself: None, ..
                }) => {
                    if path.leading_colon.is_none()
                        && path.segments.len() == 1
                        && matches!(path.segments[0].arguments, PathArguments::None)
                    {
                        let name = path.segments[0].ident.to_string();
                        return self.spec_int_idents.contains(&name);
                    }
                    return false;
                }
                _ => return false,
            }
        }
    }

    /// The `real` analogue of [`Self::expr_tail_is_vcheck_int`]: does `expr`
    /// evaluate to a `SpecReal`? Recognizes `__vcheck_real::*` calls,
    /// `let`-bound real idents (`spec_real_idents`), and looks through
    /// parens / blocks / if-else tails.
    fn expr_tail_is_vcheck_real(&self, expr: &Expr) -> bool {
        let mut cur = expr;
        loop {
            match cur {
                Expr::Paren(p) => cur = p.expr.as_ref(),
                Expr::Block(b) => match b.block.stmts.last() {
                    Some(verus_syn::Stmt::Expr(e, None)) => cur = e,
                    _ => return false,
                },
                Expr::If(eif) => {
                    let then_has = match eif.then_branch.stmts.last() {
                        Some(verus_syn::Stmt::Expr(e, None)) => self.expr_tail_is_vcheck_real(e),
                        _ => false,
                    };
                    let else_has = match &eif.else_branch {
                        Some((_, e)) => self.expr_tail_is_vcheck_real(e),
                        None => false,
                    };
                    return then_has || else_has;
                }
                Expr::Call(_) => return is_call_to_vcheck_real_returning_real(cur),
                Expr::Path(ExprPath {
                    path, qself: None, ..
                }) => {
                    if path.leading_colon.is_none()
                        && path.segments.len() == 1
                        && matches!(path.segments[0].arguments, PathArguments::None)
                    {
                        let name = path.segments[0].ident.to_string();
                        return self.spec_real_idents.contains(&name);
                    }
                    return false;
                }
                _ => return false,
            }
        }
    }

    /// The `real` analogue of [`Self::borrow_form_for_spec_int_ident`]: pass a
    /// `let`-bound real ident by reference (`&x`) so we don't move it
    /// (`BigRational` isn't `Copy`); `IntoSpecReal for &SpecReal` clones.
    fn borrow_form_for_spec_real_ident(&self, e: &Expr) -> Expr {
        if let Some(name) = ident_of_expr(e) {
            if self.spec_real_idents.contains(&name) {
                let id = format_ident!("{}", name);
                return verus_syn::parse_quote! { &#id };
            }
        }
        e.clone()
    }
}

impl<'a> VisitMut for ContractRewriter<'a> {
    fn visit_local_mut(&mut self, local: &mut verus_syn::Local) {
        // Recurse first so the init's RHS is rewritten (any `+`/`/`/etc.
        // in the RHS is lifted into `__vcheck_int::*` calls before we
        // inspect it).
        verus_syn::visit_mut::visit_local_mut(self, local);
        // If the init is `__vcheck_int::*` (or `Expr::Block` whose tail
        // is), mark the bound ident as SpecInt-valued.
        if let Some(init) = &local.init {
            if self.expr_tail_is_vcheck_int(&init.expr) {
                if let verus_syn::Pat::Ident(pi) = &local.pat {
                    self.spec_int_idents.insert(pi.ident.to_string());
                }
                // Also handle `let x: T = ...` (PatType wrapping PatIdent).
                if let verus_syn::Pat::Type(pt) = &local.pat {
                    if let verus_syn::Pat::Ident(pi) = pt.pat.as_ref() {
                        self.spec_int_idents.insert(pi.ident.to_string());
                    }
                }
            }
            // Same, for the real domain: `let r = <__vcheck_real expr>;`.
            if self.expr_tail_is_vcheck_real(&init.expr) {
                if let verus_syn::Pat::Ident(pi) = &local.pat {
                    self.spec_real_idents.insert(pi.ident.to_string());
                }
                if let verus_syn::Pat::Type(pt) = &local.pat {
                    if let verus_syn::Pat::Ident(pi) = pt.pat.as_ref() {
                        self.spec_real_idents.insert(pi.ident.to_string());
                    }
                }
            }
        }
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Verus `real` literals (`100real`, `1.5real`) denote the EXACT decimal
        // value. There's no runtime primitive `real`, so unlike `int`/`nat`
        // (which strip to a bare integer and lift on demand) a `real` literal
        // lowers directly to a `SpecReal` constant via `__vcheck_real::from_str`,
        // which parses the decimal exactly (`0.1real` -> 1/10, not the f64
        // rounding). Handles both `Lit::Int` (`100real`) and `Lit::Float`
        // (`1.5real`) suffixed forms.
        if let Expr::Lit(verus_syn::ExprLit { lit, .. }) = expr {
            let real_digits: Option<String> = match lit {
                verus_syn::Lit::Int(li) if li.suffix() == "real" => {
                    Some(li.base10_digits().to_string())
                }
                verus_syn::Lit::Float(lf) if lf.suffix() == "real" => {
                    Some(lf.base10_digits().to_string())
                }
                _ => None,
            };
            if let Some(digits) = real_digits {
                *expr = verus_syn::parse_quote! {
                    ::verus_spec_check::__vcheck_real::from_str(#digits)
                };
                return;
            }
        }

        // Strip Verus math-integer literal suffixes: `0nat` / `5int` are
        // spec-only literals with no runtime counterpart. Rewrite to the bare
        // integer (`0` / `5`); the per-operator lifting (6a/6b) promotes it to
        // `SpecInt` when a sibling operand demands it. Without this, rustc
        // rejects the `nat`/`int` suffix ("invalid suffix for number literal").
        if let Expr::Lit(verus_syn::ExprLit {
            lit: verus_syn::Lit::Int(li),
            ..
        }) = expr
        {
            let suffix = li.suffix();
            if suffix == "nat" || suffix == "int" {
                let digits = li.base10_digits().to_string();
                let bare = verus_syn::LitInt::new(&digits, li.span());
                *expr = verus_syn::parse_quote! { #bare };
                return;
            }
        }

        // Pre-recurse normalization of two-state markers.
        //
        // `final(<x>)` parses as `Expr::Final(ExprFinal { arg: <x> })` —
        // it represents the post-call value of `x`, which is what bare
        // `<x>` already means in our rewrite scheme. Strip the marker.
        //
        // `old(<x>)` parses as `Expr::Call(old, [<x>])` (no dedicated
        // verus_syn variant; `old` is a regular fn-name). Replace with a
        // synthetic ident `__vcheck_pre_<x>` that the deep_view rewrite will
        // resolve via `pre_view_for`.
        if let Expr::Final(f) = expr {
            let inner = (*f.arg).clone();
            *expr = inner;
        }
        // `ret->Some_0@` over a std-valued element
        if let Expr::View(v) = expr {
            if let Some(kind) = self.std_value_return_projection(&v.expr) {
                *expr = kind.view_form_expr(&v.expr);
            }
        }
        // `(*old(<id>)).remaining().unref()` — vstd 2026-06-14's
        // `IteratorSpec` idiom for the not-yet-yielded elements of a `&mut`
        // iterator parameter (the successor of the older `@.1.skip(@.0)`
        // tuple idiom, which the arms below already lower). For an
        // `IterState` param the pre-view is the `(cursor, order)` tuple, so
        // the whole composite lowers to the remaining slice
        // `&order[cursor..]`. Matched BEFORE the `old(..)` normalization
        // (the composite contains the `old` call). Only `IterState` params
        // have `remaining()` in their contracts, so keying on
        // `pre_view_for` membership is unambiguous.
        if let Expr::MethodCall(unref_mc) = expr {
            if unref_mc.method == "unref" && unref_mc.args.is_empty() {
                if let Expr::MethodCall(rem_mc) = unref_mc.receiver.as_ref() {
                    if rem_mc.method == "remaining" && rem_mc.args.is_empty() {
                        if let Some(name) = old_call_ident_through_wrappers(&rem_mc.receiver) {
                            if let Some(pre) = self.pre_view_for.get(&name) {
                                let p = pre.clone();
                                *expr = verus_syn::parse_quote! {
                                    &((#p).1)[((#p).0) as usize..]
                                };
                                return;
                            }
                        }
                    }
                }
            }
        }
        // `into_iter_keys(*old(s))` / `hash::into_iter_keys(*old(s))` — vstd's
        // spec view of a `Keys` iterator's FULL original key sequence,
        // cursor-independent (the idiom the corrected `remaining()` phrasing
        // replaced; audited-unsound specs are written in it, so lowering it
        // lets the harness demonstrate the counterexample). For an `IterState`
        // param that is exactly the materialized-order component of the
        // pre-view tuple. `into_iter_hash_keys` (the `hash_set::Iter` analogue)
        // has the same shape.
        if let Expr::Call(call) = expr {
            if let Expr::Path(ExprPath {
                path, qself: None, ..
            }) = call.func.as_ref()
            {
                let last = path.segments.last().map(|s| s.ident.to_string());
                if matches!(
                    last.as_deref(),
                    Some("into_iter_keys") | Some("into_iter_hash_keys")
                ) && call.args.len() == 1
                {
                    if let Some(name) = old_call_ident_through_wrappers(&call.args[0]) {
                        if let Some(pre) = self.pre_view_for.get(&name) {
                            let p = pre.clone();
                            *expr = verus_syn::parse_quote! { ((#p).1) };
                            return;
                        }
                    }
                }
            }
        }
        if let Expr::Call(call) = expr {
            if let Expr::Path(ExprPath {
                path, qself: None, ..
            }) = call.func.as_ref()
            {
                if path.leading_colon.is_none()
                    && path.segments.len() == 1
                    && path.segments[0].ident == "old"
                    && call.args.len() == 1
                {
                    if let Some(name) = ident_of_expr(&call.args[0]) {
                        if self.pre_view_for.contains_key(&name) {
                            // Replace `old(<x>)` with the synthetic ident
                            // `__vcheck_pre_<x>`; the deep_view rewriter
                            // below picks this up via the `pre_view_for`
                            // mapping (registered at the same key as
                            // `param_call_form`).
                            let synth: Ident = format_ident!("__vcheck_pre_{}", name);
                            *expr = verus_syn::parse_quote! { #synth };
                        }
                    }
                }
            }
        }

        // 0-bigand. Verus prefix conjunction / disjunction chains
        // (`&&& e1 &&& e2` / `||| e1 ||| e2`). Verus's clause parsing keeps
        // top-level chains as separate `requires`/`ensures` exprs, but a
        // chain nested inside a `match` arm or `if` branch reaches the
        // rewriter as `Expr::BigAnd` / `Expr::BigOr` — token forms with no
        // Rust equivalent. Lower to a parenthesized `&&` / `||` chain
        // BEFORE the recursive descent so each conjunct then gets the
        // usual per-operand rewrites.
        if let Expr::BigAnd(b) = expr {
            let exprs: Vec<Expr> = b.exprs.iter().map(|e| (*e.expr).clone()).collect();
            *expr = verus_syn::parse_quote! { ( #((#exprs))&&* ) };
        }
        if let Expr::BigOr(b) = expr {
            let exprs: Vec<Expr> = b.exprs.iter().map(|e| (*e.expr).clone()).collect();
            *expr = verus_syn::parse_quote! { ( #((#exprs))||* ) };
        }

        // 0-empty-map. `<expr> == Map::<K,V>::empty()` (either side, also
        // `!=`): the view side of the comparison lowers to a `&`-borrowed
        // runtime container whose carrier depends on the operand's shape
        // (`&HashMap` for HashMap/Map-viewed params and returns, `&BTreeMap`
        // for BTree ones). The generic constructor lowering below (section
        // 1b) always produces an OWNED `HashMap::new()`, which fails to
        // typecheck against `&HashMap` and is the wrong carrier for BTree.
        // In comparison position, lower the constructor operand to
        // `&Default::default()` instead: borrowed, and type inference picks
        // the carrier from the other operand. (Non-comparison uses keep the
        // 1b lowering.)
        if let Expr::Binary(b) = expr {
            use verus_syn::BinOp;
            if matches!(b.op, BinOp::Eq(_) | BinOp::Ne(_)) {
                for side in [b.left.as_mut(), b.right.as_mut()] {
                    if is_map_set_empty_call(side) {
                        *side = verus_syn::parse_quote! {
                            &::core::default::Default::default()
                        };
                    }
                }
            }
        }

        // 0. Verus-style chained comparisons: `a <= b <= c` parses in
        // verus_syn as `(a <= b) <= c`. In Verus this is meaningful;
        // in plain Rust it's a type error. Rewrite to `(a <= b) &&
        // (b <= c)` when we detect the shape.
        //
        // This MUST happen BEFORE the recursive descent. Otherwise the
        // inner comparison `(a <= b)` gets lifted by section 6b into a
        // `__vcheck_int::le(a, b)` call, which is no longer an
        // `Expr::Binary`. The chained-compare detector matches on
        // `Expr::Binary` for the inner comparison, so a post-recurse
        // run would miss the chain entirely and leave `bool <= c` —
        // a type error.
        if let Some(rewritten) = rewrite_chained_compare(expr) {
            *expr = rewritten;
            // Recurse into the rewritten form so its sub-expressions
            // (now standard binary comparisons) get the usual
            // arithmetic / comparison lifting from sections 6a/6b.
            verus_syn::visit_mut::visit_expr_mut(self, expr);
            return;
        }

        // A1. Comparisons with an explicit `as int` / `as nat` operand.
        //
        // Section 0a strips `x as int` to a bare primitive, and section 6b
        // only lifts a comparison into `__vcheck_int::*` when an operand is
        // *already* a lifted (SpecInt) expression. That combination fails for
        // a comparison whose two sides are different primitive widths (e.g.
        // `(a as int) <= (u8::MAX as int)` with `a: u16`) or where an operand
        // is an `Option`/`Result` projection (`ret->Some_0 as int`): after the
        // child recursion strips the casts, Rust sees a raw cross-type `==`
        // and rejects it.
        //
        // When the *source* explicitly cast an operand to `int`/`nat`, honor
        // that intent: lower the whole comparison into `__vcheck_int::<cmp>`, so
        // both sides pass through `IntoSpecInt` and compare in the unbounded
        // integer domain regardless of their surface widths. This MUST run
        // before the recurse-first below (otherwise 0a strips the casts during
        // child recursion and the signal is lost). We strip the outer
        // `as int`/`as nat` from each operand and recurse into the rewritten
        // call so nested projections / arithmetic are still lowered.
        if let Expr::Binary(b) = expr {
            use verus_syn::BinOp;
            let cmp_helper: Option<&'static str> = match &b.op {
                BinOp::Lt(_) => Some("lt"),
                BinOp::Le(_) => Some("le"),
                BinOp::Gt(_) => Some("gt"),
                BinOp::Ge(_) => Some("ge"),
                BinOp::Eq(_) => Some("eq"),
                BinOp::Ne(_) => Some("ne"),
                _ => None,
            };
            if let Some(h) = cmp_helper {
                let l_inner = spec_int_cast_inner(&b.left);
                let r_inner = spec_int_cast_inner(&b.right);
                if l_inner.is_some() || r_inner.is_some() {
                    let l = l_inner.unwrap_or_else(|| (*b.left).clone());
                    let r = r_inner.unwrap_or_else(|| (*b.right).clone());
                    let h_id = format_ident!("{}", h);
                    *expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_int::#h_id(#l, #r)
                    };
                    verus_syn::visit_mut::visit_expr_mut(self, expr);
                    return;
                }
            }
        }

        // Recurse first so nested rewrites land before parent rewrites.
        verus_syn::visit_mut::visit_expr_mut(self, expr);

        // 0a-pre. Strip `*<pre-snapshot ident>` produced by the
        // `old(x)` -> `__vcheck_pre_x` normalization. Source like
        // `*old(option) is None` becomes (after pre-recurse) `*__vcheck_pre_option`,
        // which Rust refuses because `Option<T>` doesn't `Deref`.
        // The semantic meaning of `*old(x)` for a `&mut T` param is
        // "the value `x` referenced before the call" — which is
        // exactly what `__vcheck_pre_x` holds directly. Strip the deref.
        //
        // Similarly, `*<harness-ident>` for a `&mut T` param: after
        // the call the binding still holds the (now mutated) owned
        // value. `*x` means "the value x points to" — for our owned-
        // form binding, that's just `x`.
        if let Expr::Unary(u) = expr {
            if matches!(u.op, verus_syn::UnOp::Deref(_)) {
                if let Some(name) = ident_of_expr(&u.expr) {
                    let strip =
                        name.starts_with("__vcheck_pre_") || self.param_call_form.contains_key(&name);
                    if strip {
                        let inner = (*u.expr).clone();
                        *expr = inner;
                    }
                }
            }
        }

        // 0a. Verus spec-integer casts: `x as nat` / `x as int` are
        // spec-only conversions with no direct runtime counterpart.
        // We *strip* them: the source value is already a primitive
        // integer at runtime, and our per-operator lifting in section
        // 6a/6b promotes arithmetic and comparisons into `SpecInt`
        // when the math demands it. Stripping (instead of lifting
        // here) means contracts like `let x = lhs as int; ... if x ==
        // 0 { ... }` keep `x` as a primitive `i8` at the use site,
        // so `x == 0` is a plain primitive comparison that doesn't
        // need lifting.
        //
        // Casts further downstream like `(x + y) as $T` are still
        // narrowed correctly because section 6a will have lifted
        // `x + y` to a `__vcheck_int::*` call, and section 6c then
        // narrows the cast.
        //
        // Type-Group stripping handles the `parse_quote!`-induced
        // `Type::Group(Type::Path(...))` wrapping that proc-macro
        // hygiene introduces around interpolated types.
        if let Expr::Cast(cast) = expr {
            let mut ty_ref: &Type = cast.ty.as_ref();
            while let Type::Group(g) = ty_ref {
                ty_ref = g.elem.as_ref();
            }
            if let Type::Path(tp) = ty_ref {
                if tp.qself.is_none()
                    && tp.path.leading_colon.is_none()
                    && tp.path.segments.len() == 1
                {
                    let target = tp.path.segments[0].ident.to_string();
                    // `<x> as real` -> convert into the real domain. Runs before
                    // the `nat`/`int` strip so it isn't shadowed. `cast(..)`
                    // dispatches on the operand type (int -> exact, float ->
                    // finite/non-finite path) at runtime, so no type info is
                    // needed here.
                    if target == "real" {
                        let inner = (*cast.expr).clone();
                        *expr = verus_syn::parse_quote! {
                            ::verus_spec_check::__vcheck_real::cast(#inner)
                        };
                        return;
                    }
                    // `<real> as int` -> floor (bridges back to the integer
                    // domain; `floor` returns a `SpecInt`). Only when the
                    // operand is real-valued — otherwise fall through to the
                    // ordinary `int` strip below.
                    if target == "int" && self.expr_tail_is_vcheck_real(&cast.expr) {
                        let inner = (*cast.expr).clone();
                        *expr = verus_syn::parse_quote! {
                            ::verus_spec_check::__vcheck_real::floor(#inner)
                        };
                        return;
                    }
                    if target == "nat" || target == "int" {
                        let inner = (*cast.expr).clone();
                        *expr = verus_syn::parse_quote! { (#inner) };
                        return;
                    }
                }
            }
        }

        // `<real>.floor()` (Verus `real::floor()`): the exec form floors into
        // the integer domain. Runs post-recurse so the receiver is already
        // lowered to a `__vcheck_real::*` expression.
        if let Expr::MethodCall(ExprMethodCall {
            receiver,
            method,
            args,
            ..
        }) = expr
        {
            if method == "floor" && args.is_empty() && self.expr_tail_is_vcheck_real(receiver) {
                let recv = (**receiver).clone();
                *expr = verus_syn::parse_quote! {
                    ::verus_spec_check::__vcheck_real::floor(#recv)
                };
                return;
            }
        }

        // 0. (chained-compare moved to before the recursive descent
        // above; section 6b's lifting would otherwise turn the inner
        // comparison into a non-`Expr::Binary` form, defeating the
        // chained-compare detector.)

        // 1. Strip `<expr>.deep_view()` or `<expr>@` (Verus's `View`-postfix
        // shorthand). Both denote the same spec view: in Verus, `s@` parses
        // as `Expr::View { expr: s }` and is semantically equivalent to
        // `s.deep_view()` for the purpose of contract evaluation. Treat them
        // identically in the harness rewriter. Also handle the explicit
        // `<expr>.view()` form (used in vstd as a longhand for `s@`).
        let view_receiver: Option<Expr> = match expr {
            Expr::MethodCall(ExprMethodCall {
                receiver,
                method,
                args,
                ..
            }) if (method == "deep_view" || method == "view") && args.is_empty() => {
                Some((**receiver).clone())
            }
            Expr::View(v) => Some((*v.expr).clone()),
            _ => None,
        };
        if let Some(receiver_clone) = view_receiver {
            // Return-named ident: re-shape per ReturnShape.
            if let Some(ret_ident) = &self.return_ident {
                if expr_is_ident(&receiver_clone, ret_ident) {
                    *expr = self.rewrite_return_deep_view(ret_ident.clone());
                    return;
                }
                // Mutable slice members of tuple returns are rebound to owned
                // Vec snapshots. Preserve the tuple field syntax while
                // presenting a slice to the Seq lowering.
                if let Expr::Field(field) = &receiver_clone {
                    if expr_is_ident(&field.base, ret_ident) {
                        if let ReturnShape::Tuple2(a, b) = &self.return_shape {
                            let elem = match &field.member {
                                verus_syn::Member::Unnamed(index) if index.index == 0 => {
                                    Some(a.as_ref())
                                }
                                verus_syn::Member::Unnamed(index) if index.index == 1 => {
                                    Some(b.as_ref())
                                }
                                _ => None,
                            };
                            if matches!(
                                elem,
                                Some(ReturnShape::MutRefSlice(_) | ReturnShape::MutRefArray(_, _))
                            ) {
                                let projection = receiver_clone.clone();
                                *expr = verus_syn::parse_quote! { #projection.as_slice() };
                                return;
                            }
                        }
                    }
                }
            }

            // Parameter ident: substitute the registered call form.
            if let Some(name) = ident_of_expr(&receiver_clone) {
                // First check the pre-state map for `__vcheck_pre_<id>`
                // synthetic idents (introduced by the `old(...)`
                // normalization step above). The pre-state form is
                // already a deep_view-shaped expression — substitute it
                // directly without going through `param_call_form`.
                if let Some(stripped) = name.strip_prefix("__vcheck_pre_") {
                    if let Some(pre) = self.pre_view_for.get(stripped) {
                        let p = pre.clone();
                        *expr = verus_syn::parse_quote!( #p );
                        return;
                    }
                }
                if let Some(call_form) = self.param_call_form.get(&name) {
                    let cf = call_form.clone();
                    *expr = verus_syn::parse_quote!( #cf );
                    return;
                }
            }

            // String-literal view (`"foo"@`, most commonly `""@` in
            // emptiness contracts): lower to the same `&[char]` shape that
            // `String` / `&str` parameter views take, so comparisons like
            // `s@ == ""@` typecheck. A bare unwrap would leave a `&str`
            // literal facing a `&[char]` view.
            if let Expr::Lit(verus_syn::ExprLit {
                lit: verus_syn::Lit::Str(_),
                ..
            }) = &receiver_clone
            {
                let lit = receiver_clone.clone();
                *expr = verus_syn::parse_quote! {
                    ::verus_spec_check::__vcheck_str_chars(#lit).as_slice()
                };
                return;
            }

            // Otherwise: just unwrap to the receiver (best-effort).
            *expr = receiver_clone;
            return;
        }

        // Current vstd iterator specs expose the yet-to-be-yielded sequence as
        // `(*old(iter)).remaining().unref()`. Iterator parameters are already
        // sampled as `(cursor, iteration_order)` snapshots; lower this accessor
        // chain to the suffix beginning at that cursor.
        if let Expr::MethodCall(unref_call) = expr {
            if unref_call.method == "unref" && unref_call.args.is_empty() {
                if let Expr::MethodCall(remaining_call) = unref_call.receiver.as_ref() {
                    if remaining_call.method == "remaining" && remaining_call.args.is_empty() {
                        let mut state = (*remaining_call.receiver).clone();
                        // Iterator pre-state snapshots are represented directly
                        // by `pre_view_for` (cursor + stable iteration order),
                        // not by a materialized `__vcheck_pre_<id>` local.
                        if let Some(name) = ident_of_expr(&state) {
                            if let Some(param) = name.strip_prefix("__vcheck_pre_") {
                                if let Some(pre) = self.pre_view_for.get(param) {
                                    state = verus_syn::parse2(pre.clone())
                                        .expect("iterator pre-view expression");
                                }
                            }
                        }
                        *expr = verus_syn::parse_quote! {
                            ::verus_spec_check::__vcheck_iter_remaining(#state)
                        };
                        return;
                    }
                }
            }
        }

        // 1a. `<str>.spec_bytes()` — Verus's spec-side `Seq<u8>` view
        // of a string's UTF-8 bytes. The runtime equivalent is
        // `s.as_bytes()`, wrapped through the engine's slice-helper
        // so the result lands in the `Seq<u8>`-shaped slice path.
        //
        // We only rewrite when the receiver is a known `&str` /
        // `String` param (looked up via `param_call_form`). For other
        // receivers (e.g. user-typed values that happen to have a
        // method named `spec_bytes`), fall through and let the normal
        // spec-fn renaming path handle it.
        if let Expr::MethodCall(mc) = expr {
            if mc.method == "spec_bytes" && mc.args.is_empty() {
                // (i) Receiver is a known `&str` / `String` parameter.
                if let Some(name) = ident_of_expr(&mc.receiver) {
                    if self.auto_borrow_idents.contains_key(&name)
                        || self.param_call_form.contains_key(&name)
                    {
                        let id = format_ident!("{}", name);
                        *expr = verus_syn::parse_quote! {
                            ::verus_spec_check::__vcheck_str_bytes(&#id)
                        };
                        return;
                    }
                    // (ii) Receiver is the return ident and the fn returns a
                    // `&str` / `String` (`res.spec_bytes()`). `&res` is
                    // `&&str` / `&String`, both deref-coerce to `&str`.
                    if let Some(ret) = &self.return_ident {
                        if name == ret.to_string()
                            && matches!(
                                self.return_shape,
                                ReturnShape::RefStr | ReturnShape::OwnedString
                            )
                        {
                            let recv = (*mc.receiver).clone();
                            *expr = verus_syn::parse_quote! {
                                ::verus_spec_check::__vcheck_str_bytes(&#recv)
                            };
                            return;
                        }
                    }
                }
                // (iii) Receiver is a tuple projection of the return
                // (`res.0.spec_bytes()` / `res.1.spec_bytes()`) where that
                // member is `&str` / `String` — e.g. `str::split_at`'s
                // `(&str, &str)` return.
                if let Expr::Field(field) = mc.receiver.as_ref() {
                    if let (Some(base), Some(ret)) =
                        (ident_of_expr(&field.base), &self.return_ident)
                    {
                        if base == ret.to_string() {
                            if let ReturnShape::Tuple2(a, b) = &self.return_shape {
                                let elem = match &field.member {
                                    verus_syn::Member::Unnamed(i) if i.index == 0 => {
                                        Some(a.as_ref())
                                    }
                                    verus_syn::Member::Unnamed(i) if i.index == 1 => {
                                        Some(b.as_ref())
                                    }
                                    _ => None,
                                };
                                if matches!(
                                    elem,
                                    Some(ReturnShape::RefStr | ReturnShape::OwnedString)
                                ) {
                                    let recv = (*mc.receiver).clone();
                                    *expr = verus_syn::parse_quote! {
                                        ::verus_spec_check::__vcheck_str_bytes(&#recv)
                                    };
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }

        // 1b. Spec-only constructors that have a runtime equivalent.
        // Patterns like `Seq::<char>::empty()`, `Map::<K,V>::empty()`,
        // `Set::<T>::empty()` appear in contract clauses (e.g. `r@ ==
        // Seq::<char>::empty()` for a fn that returns an empty container).
        // The bare constructor call doesn't get lowered through the
        // spec-fn renaming path because it's not a local spec fn — but the
        // engine has runtime equivalents (`Vec::new`, `HashMap::new`,
        // `HashSet::new`). Lower these here so contracts comparing
        // against them evaluate at runtime.
        if let Expr::Call(call) = expr {
            if call.args.is_empty() {
                if let Expr::Path(ExprPath {
                    path, qself: None, ..
                }) = call.func.as_ref()
                {
                    let n = path.segments.len();
                    if n >= 2 {
                        let container_seg = &path.segments[n - 2];
                        let method_seg = &path.segments[n - 1];
                        if method_seg.ident == "empty"
                            && matches!(method_seg.arguments, PathArguments::None)
                        {
                            let cname = container_seg.ident.to_string();
                            let args_ts = match &container_seg.arguments {
                                PathArguments::AngleBracketed(ab) => {
                                    let args = &ab.args;
                                    Some(quote! { <#args> })
                                }
                                _ => None,
                            };
                            let lowered: Option<Expr> = match cname.as_str() {
                                "Seq" => Some(if let Some(a) = args_ts {
                                    verus_syn::parse_quote! {
                                        ::std::vec::Vec::#a::new().as_slice()
                                    }
                                } else {
                                    verus_syn::parse_quote! {
                                        ::std::vec::Vec::new().as_slice()
                                    }
                                }),
                                "Map" => Some(if let Some(a) = args_ts {
                                    verus_syn::parse_quote! {
                                        ::std::collections::HashMap::#a::new()
                                    }
                                } else {
                                    verus_syn::parse_quote! {
                                        ::std::collections::HashMap::new()
                                    }
                                }),
                                "Set" => Some(if let Some(a) = args_ts {
                                    verus_syn::parse_quote! {
                                        ::std::collections::HashSet::#a::new()
                                    }
                                } else {
                                    verus_syn::parse_quote! {
                                        ::std::collections::HashSet::new()
                                    }
                                }),
                                _ => None,
                            };
                            if let Some(new) = lowered {
                                *expr = new;
                                return;
                            }
                        }
                    }
                }
            }
        }

        // 1c. `<x> is Variant` / `<x> isnt Variant` — verus's matches
        // operator. The exec form is `matches!(<x>, ..::Variant ..)`.
        // Lower here so subsequent stages don't see the verus-only
        // `Expr::Is` node.
        if let Expr::Is(eis) = expr {
            let recv = (*eis.base).clone();
            let recv = match recv {
                Expr::Unary(u) if matches!(u.op, verus_syn::UnOp::Deref(_)) => (*u.expr).clone(),
                other => other,
            };
            let vname = eis.variant_ident.to_string();
            let vid: Ident = format_ident!("{}", vname);
            let new: Expr = match vname.as_str() {
                "Some" => verus_syn::parse_quote! { ::core::matches!(#recv, Some(_)) },
                "None" => verus_syn::parse_quote! { ::core::matches!(#recv, None) },
                "Ok" => verus_syn::parse_quote! { ::core::matches!(#recv, Ok(_)) },
                "Err" => verus_syn::parse_quote! { ::core::matches!(#recv, Err(_)) },
                _ => verus_syn::parse_quote! {
                    ::core::matches!(#recv, #vid { .. } | #vid(..) | #vid)
                },
            };
            *expr = new;
            return;
        }
        if let Expr::IsNot(eis) = expr {
            let recv = (*eis.base).clone();
            let recv = match recv {
                Expr::Unary(u) if matches!(u.op, verus_syn::UnOp::Deref(_)) => (*u.expr).clone(),
                other => other,
            };
            let vname = eis.variant_ident.to_string();
            let vid: Ident = format_ident!("{}", vname);
            let new: Expr = match vname.as_str() {
                "Some" => verus_syn::parse_quote! { !::core::matches!(#recv, Some(_)) },
                "None" => verus_syn::parse_quote! { !::core::matches!(#recv, None) },
                "Ok" => verus_syn::parse_quote! { !::core::matches!(#recv, Ok(_)) },
                "Err" => verus_syn::parse_quote! { !::core::matches!(#recv, Err(_)) },
                _ => verus_syn::parse_quote! {
                    !::core::matches!(#recv, #vid { .. } | #vid(..) | #vid)
                },
            };
            *expr = new;
            return;
        }

        // 1d. `<x>->Variant_<n>` / `<x>->Variant` — verus's variant-field
        // accessor. Lower to a `match` for known std enums (Option /
        // Result); fall back to `<vid>(__v) => __v` for generic enums.
        // The arm projects field `<n>` of the variant; we only support
        // index 0 currently (the common case for `Some`/`Ok`/`Err`).
        if let Expr::GetField(egf) = expr {
            let recv = (*egf.base).clone();
            let recv = match recv {
                Expr::Unary(u) if matches!(u.op, verus_syn::UnOp::Deref(_)) => (*u.expr).clone(),
                other => other,
            };
            let member_str = match &egf.member {
                verus_syn::Member::Named(id) => id.to_string(),
                verus_syn::Member::Unnamed(idx) => idx.index.to_string(),
            };
            let vname: String = if let Some(under) = member_str.rfind('_') {
                let (left, right) = member_str.split_at(under);
                let right = &right[1..];
                if right.parse::<usize>().is_ok() {
                    left.to_string()
                } else {
                    member_str.clone()
                }
            } else {
                member_str.clone()
            };
            let new: Expr = match vname.as_str() {
                "Ok" => verus_syn::parse_quote! {
                    match (#recv).clone() { Ok(__v) => __v, _ => unreachable!() }
                },
                "Err" => verus_syn::parse_quote! {
                    match (#recv).clone() { Err(__v) => __v, _ => unreachable!() }
                },
                "Some" => verus_syn::parse_quote! {
                    match (#recv).clone() { Some(__v) => __v, _ => unreachable!() }
                },
                _ => {
                    if vname.parse::<usize>().is_ok() {
                        // Numeric-only member like `<x>->0`. The variant
                        // is ambiguous from this layer; at the call site
                        // it's typically `Option`. Default to `Some`.
                        verus_syn::parse_quote! {
                            match (#recv).clone() { Some(__v) => __v, _ => unreachable!() }
                        }
                    } else {
                        let vid: Ident = format_ident!("{}", vname);
                        verus_syn::parse_quote! {
                            match (#recv).clone() { #vid(__v) => __v, _ => unreachable!() }
                        }
                    }
                }
            };
            *expr = new;
            return;
        }

        // 1c. `#[vcheck_view]` view-fn call: `view(x)` denotes the abstract view
        // of an opaque `VcheckConcretize` type, realized at runtime by
        // `x.vcheck_realize()`. We recurse into the rewritten node so the arg's
        // param substitution (a sampled `Sample` -> injected opaque value) or
        // the returned opaque value flows into the receiver, then return.
        if let Expr::Call(call) = expr {
            if let Expr::Path(ExprPath {
                path, qself: None, ..
            }) = call.func.as_ref()
            {
                if path.leading_colon.is_none()
                    && path.segments.len() == 1
                    && matches!(path.segments[0].arguments, PathArguments::None)
                    && call.args.len() == 1
                    && is_view_fn(&path.segments[0].ident.to_string())
                {
                    let vname = path.segments[0].ident.to_string();
                    let arg = call.args.iter().next().unwrap().clone();
                    if let Some(realize) = view_realize_expr(&vname) {
                        // Resolve the view arg to a `&Opaque`:
                        //   - a bare opaque param ident -> its call-form
                        //     (`&inject(sample.clone())`), since bare params
                        //     aren't otherwise substituted (only `x@` is);
                        //   - an already-`&`-prefixed arg (`&ret`) -> as-is;
                        //   - otherwise borrow it.
                        let realized_arg: Expr = if let Some(name) = ident_of_expr(&arg) {
                            if let Some(cf) = self.param_call_form.get(&name) {
                                let cf = cf.clone();
                                verus_syn::parse_quote! { #cf }
                            } else {
                                verus_syn::parse_quote! { &(#arg) }
                            }
                        } else if matches!(arg, Expr::Reference(_)) {
                            arg.clone()
                        } else {
                            verus_syn::parse_quote! { &(#arg) }
                        };
                        // Wrap in `__vcheck_int::lift` so the realized value is a
                        // recognized `SpecInt` operand: contract arithmetic and
                        // comparisons then lift uniformly.
                        *expr = verus_syn::parse_quote! {
                            ::verus_spec_check::__vcheck_int::lift(#realize(#realized_arg))
                        };
                        return;
                    }
                }
            }
        }

        // 2. Rename `f(args)` to `exec_f(args)` when `f` is a known spec fn,
        // or to `exec_<spec_X>(args)` when `f` has `when_used_as_spec(spec_X)`.
        // If an argument is a bare user-typed ident, insert the conversion.
        if let Expr::Call(call) = expr {
            // 2a. Special-case verus's `is_variant(<x>, "Variant")` builtin.
            // It has no exec companion (`exec_is_variant`), so the default
            // rename path produces an unresolved-fn error. Lower to a
            // `matches!` expression that handles all three variant shapes
            // (unit, tuple, struct). The receiver `<x>` is whatever the
            // user wrote — typically a `&Option<T>` / `&Result<T, E>` etc.
            // We also handle the `*<x>` form that `verifier::inline` spec
            // bodies sometimes emit.
            if let Expr::Path(ExprPath {
                path, qself: None, ..
            }) = call.func.as_ref()
            {
                if path.segments.len() == 1
                    && path.segments[0].ident == "is_variant"
                    && call.args.len() == 2
                {
                    // Second arg should be a string literal `"Variant"`.
                    let variant_name: Option<String> = match call.args.iter().nth(1) {
                        Some(Expr::Lit(lit)) => {
                            if let verus_syn::Lit::Str(s) = &lit.lit {
                                Some(s.value())
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    if let Some(vname) = variant_name {
                        let recv = call.args.iter().next().unwrap().clone();
                        // Strip a leading deref so `is_variant(*x, ...)`
                        // and `is_variant(x, ...)` produce the same code.
                        let recv = match recv {
                            Expr::Unary(u) if matches!(u.op, verus_syn::UnOp::Deref(_)) => {
                                (*u.expr).clone()
                            }
                            other => other,
                        };
                        let vid: Ident = format_ident!("{}", vname);
                        // Build the variant matcher. For known std enums
                        // (Option / Result) we know the path; for others
                        // we use a glob that handles unit, tuple, and
                        // struct variant shapes.
                        let new: Expr = match vname.as_str() {
                            "Some" => verus_syn::parse_quote! {
                                ::core::matches!(#recv, Some(_))
                            },
                            "None" => verus_syn::parse_quote! {
                                ::core::matches!(#recv, None)
                            },
                            "Ok" => verus_syn::parse_quote! {
                                ::core::matches!(#recv, Ok(_))
                            },
                            "Err" => verus_syn::parse_quote! {
                                ::core::matches!(#recv, Err(_))
                            },
                            _ => {
                                // Generic fallback: try unit, tuple, and
                                // struct variants in one matches! arm. Uses
                                // an unqualified path so the variant
                                // resolves relative to the enum context.
                                verus_syn::parse_quote! {
                                    ::core::matches!(#recv, #vid { .. } | #vid(..) | #vid)
                                }
                            }
                        };
                        *expr = new;
                        return;
                    }
                }
            }
            if let Expr::Path(ExprPath {
                path, qself: None, ..
            }) = call.func.as_mut()
            {
                // Multi-segment paths to vstd's per-width spec-fn modules
                // (e.g. `u8_specs::wrapping_add(x, y)`).
                //
                // Each `<width>_specs::<op>` spec fn has a specific
                // unbounded-arithmetic definition in
                // `vstd/wrapping.rs`. We inline that definition here
                // so the runtime contract evaluation is a *genuine*
                // check against the Rust intrinsic — not a tautology
                // `intrinsic == intrinsic`. The inlined form uses the
                // `__vcheck_int::*` helpers so the math happens in
                // unbounded `SpecInt` and the final narrowing fails
                // loudly if any sampled input violates the spec.
                //
                // Width-keyed constants:
                //   - `MAX`/`MIN` come from `<T>::MAX`/`<T>::MIN`.
                //   - `range` is `2^bits` (u8: 256, u16: 65536, ...).
                //     We compute it as `(<T>::MAX as i128 - <T>::MIN
                //     as i128) + 1` for signed types, or `<T>::MAX as
                //     u128 + 1` for unsigned. To keep the inlining
                //     side-effect-free we precompute literals.
                if path.segments.len() == 2 && call.args.len() <= 3 {
                    let mod_name = path.segments[0].ident.to_string();
                    let fn_name = path.segments[1].ident.to_string();
                    let int_ty: Option<&'static str> = match mod_name.as_str() {
                        "u8_specs" => Some("u8"),
                        "u16_specs" => Some("u16"),
                        "u32_specs" => Some("u32"),
                        "u64_specs" => Some("u64"),
                        "u128_specs" => Some("u128"),
                        "usize_specs" => Some("usize"),
                        "i8_specs" => Some("i8"),
                        "i16_specs" => Some("i16"),
                        "i32_specs" => Some("i32"),
                        "i64_specs" => Some("i64"),
                        "i128_specs" => Some("i128"),
                        "isize_specs" => Some("isize"),
                        _ => None,
                    };
                    if let Some(ty) = int_ty {
                        let is_signed = ty.starts_with('i');
                        let ty_ident = format_ident!("{}", ty);
                        // Range = 2^bits. Computed via __vcheck_int::lift
                        // so it's a `SpecInt` and the spec arithmetic
                        // stays unbounded.
                        let bits: u32 = match ty {
                            "u8" | "i8" => 8,
                            "u16" | "i16" => 16,
                            "u32" | "i32" => 32,
                            "u64" | "i64" => 64,
                            "u128" | "i128" => 128,
                            "usize" | "isize" => {
                                // usize/isize: rely on runtime BITS.
                                // Use 0 as a sentinel; the lowering
                                // below uses `<usize>::BITS` directly.
                                0
                            }
                            _ => unreachable!(),
                        };
                        // For fixed widths produce a literal; for
                        // pointer-sized use the runtime BITS const.
                        let range_expr: Expr = if bits == 0 {
                            verus_syn::parse_quote! {
                                ::verus_spec_check::__vcheck_int::shl(1u32, <#ty_ident>::BITS)
                            }
                        } else {
                            verus_syn::parse_quote! {
                                ::verus_spec_check::__vcheck_int::shl(1u32, #bits)
                            }
                        };
                        let to_ty_fn = format_ident!("to_{}", ty);
                        let args: Vec<Expr> = call.args.iter().cloned().collect();
                        // Three families: `wrapping_<add|sub|mul>`,
                        // `wrapping_add_signed`/`wrapping_add_unsigned`,
                        // `wrapping_shl`/`wrapping_shr`.
                        match fn_name.as_str() {
                            "wrapping_add"
                            | "wrapping_sub"
                            | "wrapping_mul"
                            | "wrapping_add_signed"
                            | "wrapping_add_unsigned" => {
                                if args.len() != 2 {
                                    return;
                                }
                                let a = args[0].clone();
                                let b = args[1].clone();
                                let math_op = match fn_name.as_str() {
                                    "wrapping_add"
                                    | "wrapping_add_signed"
                                    | "wrapping_add_unsigned" => format_ident!("add"),
                                    "wrapping_sub" => format_ident!("sub"),
                                    "wrapping_mul" => format_ident!("mul"),
                                    _ => unreachable!(),
                                };
                                // Compute the math-int result, then
                                // narrow via Euclidean `% range`. The
                                // remainder is always in `[0, range)`.
                                // For unsigned `T`, that's exactly `T`'s
                                // value range. For signed `T`, if the
                                // remainder lies in `[MAX+1, range)`,
                                // subtract `range` to map into
                                // `[MIN, -1]`.
                                if is_signed {
                                    *expr = verus_syn::parse_quote! {
                                        {
                                            let __vcheck_m = ::verus_spec_check::__vcheck_int::#math_op(#a, #b);
                                            let __vcheck_r = #range_expr;
                                            let __vcheck_rem = ::verus_spec_check::__vcheck_int::rem(&__vcheck_m, &__vcheck_r);
                                            ::verus_spec_check::__vcheck_int::#to_ty_fn({
                                                if ::verus_spec_check::__vcheck_int::gt(&__vcheck_rem, <#ty_ident>::MAX) {
                                                    ::verus_spec_check::__vcheck_int::sub(&__vcheck_rem, &__vcheck_r)
                                                } else {
                                                    __vcheck_rem
                                                }
                                            })
                                        }
                                    };
                                } else {
                                    *expr = verus_syn::parse_quote! {
                                        {
                                            let __vcheck_m = ::verus_spec_check::__vcheck_int::#math_op(#a, #b);
                                            let __vcheck_r = #range_expr;
                                            ::verus_spec_check::__vcheck_int::#to_ty_fn(
                                                ::verus_spec_check::__vcheck_int::rem(&__vcheck_m, &__vcheck_r)
                                            )
                                        }
                                    };
                                }
                                return;
                            }
                            "wrapping_shl" | "wrapping_shr" => {
                                // Verus's spec body is `x <op> (shift % bits)`.
                                // In Verus's `int` semantics, `<<` is
                                // multiplication by `2^n` and `>>` is
                                // truncated division by `2^n`. We
                                // perform those in `SpecInt` and
                                // narrow back, using `signed_crop`-
                                // style sign adjustment for signed
                                // types (same as wrapping_<add|sub|mul>
                                // above).
                                if args.len() != 2 {
                                    return;
                                }
                                let a = args[0].clone();
                                let b = args[1].clone();
                                let bits_lit: Expr = if bits == 0 {
                                    verus_syn::parse_quote! {
                                        <#ty_ident>::BITS
                                    }
                                } else {
                                    verus_syn::parse_quote! { #bits }
                                };
                                let shl_or_shr = match fn_name.as_str() {
                                    "wrapping_shl" => format_ident!("shl"),
                                    "wrapping_shr" => format_ident!("shr"),
                                    _ => unreachable!(),
                                };
                                if is_signed {
                                    *expr = verus_syn::parse_quote! {
                                        {
                                            let __vcheck_shift_masked = (#b) % (#bits_lit);
                                            let __vcheck_m = ::verus_spec_check::__vcheck_int::#shl_or_shr(#a, __vcheck_shift_masked);
                                            let __vcheck_r = #range_expr;
                                            let __vcheck_rem = ::verus_spec_check::__vcheck_int::rem(&__vcheck_m, &__vcheck_r);
                                            ::verus_spec_check::__vcheck_int::#to_ty_fn({
                                                if ::verus_spec_check::__vcheck_int::gt(&__vcheck_rem, <#ty_ident>::MAX) {
                                                    ::verus_spec_check::__vcheck_int::sub(&__vcheck_rem, &__vcheck_r)
                                                } else {
                                                    __vcheck_rem
                                                }
                                            })
                                        }
                                    };
                                } else {
                                    *expr = verus_syn::parse_quote! {
                                        {
                                            let __vcheck_shift_masked = (#b) % (#bits_lit);
                                            let __vcheck_m = ::verus_spec_check::__vcheck_int::#shl_or_shr(#a, __vcheck_shift_masked);
                                            let __vcheck_r = #range_expr;
                                            ::verus_spec_check::__vcheck_int::#to_ty_fn(
                                                ::verus_spec_check::__vcheck_int::rem(&__vcheck_m, &__vcheck_r)
                                            )
                                        }
                                    };
                                }
                                return;
                            }
                            _ => {}
                        }
                    }
                }
                if path.segments.len() == 1 {
                    let seg = &mut path.segments[0];
                    let name = seg.ident.to_string();
                    // Special-case Verus's `call_ensures(f, (args...), ret)`:
                    // a spec-side relation meaning "calling f with args
                    // produces ret". At runtime, when f is a concrete
                    // monomorphic path (e.g. `<u32 as From<u8>>::from`
                    // after `#[vcheck(T = u8, U = u32)]` monomorphization),
                    // this is operationally `ret == f(args...)`. We
                    // lower to that direct comparison so the harness
                    // actually invokes the impl.
                    //
                    // Recognized shapes:
                    //   call_ensures(<path>, (a, b, ...), ret)
                    //   call_ensures(<path>, (), ret)        // no args
                    //
                    // The first arg must be a `Path` (we don't try to
                    // resolve closures or generic-typed function values);
                    // if it isn't, fall through and the builtin-check
                    // diagnostic surfaces normally.
                    if name == "call_ensures" && call.args.len() == 3 {
                        let fn_arg = &call.args[0];
                        let tuple_arg = &call.args[1];
                        let ret_arg = &call.args[2];
                        // SAMPLED-PREDICATE branch (must come before the
                        // generic path branch, which would lower to a
                        // closure *invocation* — wrong for stateful preds,
                        // whose call would advance the budget counter).
                        // `call_ensures(<pred>, (x,), r)` lowers to
                        // `<pred>.models(x, r)`: exact contract for pure
                        // kinds, trace membership for stateful kinds.
                        if let Some(pred_name) = ident_of_expr(fn_arg) {
                            if self.sampled_pred_idents.contains(&pred_name) {
                                if let Expr::Tuple(t) = tuple_arg {
                                    if t.elems.len() == 1 {
                                        let x = pred_borrow_form(&t.elems[0]);
                                        let pid = format_ident!("{}", pred_name);
                                        let r = ret_arg.clone();
                                        let mut new_expr: Expr = verus_syn::parse_quote! {
                                            #pid.models(#x, #r)
                                        };
                                        // Recurse into the lowered form so the
                                        // tuple-element and ret sub-exprs get
                                        // their own rewrites (views, old(), …).
                                        self.visit_expr_mut(&mut new_expr);
                                        *expr = new_expr;
                                        return;
                                    }
                                }
                            }
                        }
                        // The function must be a path-like expression.
                        // Acceptable forms: `Path` (ExprPath) and
                        // method-as-fn syntax like `T::default`. Both
                        // parse as `Expr::Path`.
                        if matches!(fn_arg, Expr::Path(_)) {
                            // Extract the tuple's elements; accept `(a, b)`
                            // (tuple) or `()` (unit) as the args.
                            let args_vec: Option<Vec<Expr>> = match tuple_arg {
                                Expr::Tuple(t) => Some(t.elems.iter().cloned().collect()),
                                _ => None,
                            };
                            if let Some(args) = args_vec {
                                let f = fn_arg.clone();
                                let r = ret_arg.clone();
                                *expr = if args.is_empty() {
                                    verus_syn::parse_quote! { (#r) == (#f()) }
                                } else {
                                    verus_syn::parse_quote! {
                                        (#r) == (#f(#(#args),*))
                                    }
                                };
                                return;
                            }
                        }
                    }
                    // `call_requires(<pred>, (x,))` on a sampled predicate:
                    // the VcheckPred family is total, so the precondition holds
                    // for every input.
                    if name == "call_requires" && call.args.len() == 2 {
                        if let Some(pred_name) = ident_of_expr(&call.args[0]) {
                            if self.sampled_pred_idents.contains(&pred_name) {
                                *expr = verus_syn::parse_quote! { true };
                                return;
                            }
                        }
                    }
                    // Special-case verus's arithmetic builtins:
                    // `add(a, b)`, `sub(a, b)`, `mul(a, b)`. These appear
                    // in bit-vector specs (e.g. `sub(8, t)` for shift
                    // arithmetic). They have no exec companion; lower
                    // to plain Rust arithmetic. The contract context
                    // guarantees no overflow (e.g. `sub(8, t)` with
                    // `0 <= t <= 8`); if vcheck ever samples a violating
                    // input, the panic surfaces as a clear axiom-
                    // soundness failure.
                    //
                    // We emit a block that binds the rhs first so the
                    // lhs's type inference picks up the rhs's type
                    // (handles the common `sub(8, t as u8)` shape where
                    // `8` is an int literal and `t` is u8).
                    if call.args.len() == 2 {
                        let op_tokens: Option<TokenStream2> = match name.as_str() {
                            "add" => Some(quote! { + }),
                            "sub" => Some(quote! { - }),
                            "mul" => Some(quote! { * }),
                            _ => None,
                        };
                        if let Some(op) = op_tokens {
                            let lhs = call.args.iter().next().unwrap().clone();
                            let rhs = call.args.iter().nth(1).unwrap().clone();
                            *expr = verus_syn::parse_quote! {
                                { let __vcheck_rhs = (#rhs); let __vcheck_lhs = (#lhs); __vcheck_lhs #op __vcheck_rhs }
                            };
                            return;
                        }
                    }
                    // Verus's `cloned::<T>(a, b)` spec predicate ("b is a
                    // clone of a") means deep-value equality. At runtime the
                    // harness materializes owned values, so lower to `a == b`.
                    // Appears in `Clone::clone` postconditions
                    // (`cloned(opt.unwrap(), res.unwrap())`).
                    if name == "cloned" && call.args.len() == 2 {
                        let a = call.args.iter().next().unwrap().clone();
                        let b = call.args.iter().nth(1).unwrap().clone();
                        *expr = verus_syn::parse_quote! { ((#a) == (#b)) };
                        return;
                    }
                    let target_name: Option<String> =
                        if let Some(redirected) = self.when_used_as_spec_redirect.get(&name) {
                            Some(redirected.clone())
                        } else if self.spec_fn_names.contains(&name) {
                            Some(name.clone())
                        } else {
                            None
                        };
                    if let Some(t) = target_name {
                        seg.ident = format_ident!("exec_{}", t);
                        // Companions are always monomorphic (generated per
                        // closure substitution, or supplied as a concrete
                        // `external_vcheck_provide!` stub), so drop any
                        // turbofish the source call carried:
                        // `obeys_cmp::<u32>()` -> `exec_obeys_cmp()`. Guard
                        // predicates on monomorphized container specs
                        // (`obeys_cmp::<Key>()`, `obeys_key_model::<Key>()`)
                        // are the canonical case.
                        seg.arguments = PathArguments::None;
                        // Convert any bare user-typed argument: `f(u)` where
                        // `u: User` -> `exec_f(&__vcheck_to_exec_User(&u))`.
                        for arg in call.args.iter_mut() {
                            self.convert_user_arg(arg);
                        }
                    }
                }
            }
        }

        // 2a-seq. Verus's `seq![a, b, ...]` / `seq![]` sequence literal.
        // In a contract clause it denotes a `Seq`; the slice-shape lowering
        // represents sequences as `Vec`, so rewrite the macro name `seq` to
        // `vec` (element exprs are simple literals/idents in practice, so the
        // opaque macro tokens don't need further rewriting). Appears in
        // `Option::as_slice` (`res@ == seq![x]` / `seq![]`) and VecDeque
        // front-insertion specs.
        if let Expr::Macro(m) = expr {
            if m.mac.path.segments.len() == 1 && m.mac.path.segments[0].ident == "seq" {
                m.mac.path.segments[0].ident = format_ident!("vec");
                return;
            }
        }

        // 2a-pred. Method-form closure-contract sugar on a sampled
        // predicate: `pred.ensures((x,), r)` ≡ `call_ensures(pred, (x,), r)`
        // and `pred.requires((x,))` ≡ `call_requires(pred, (x,))`. Lowered
        // identically to the free-fn forms (see the `call_ensures` branch):
        // `models` for ensures, `true` for requires.
        if let Expr::MethodCall(mc) = expr {
            if let Some(pred_name) = ident_of_expr(&mc.receiver) {
                if self.sampled_pred_idents.contains(&pred_name) {
                    let method = mc.method.to_string();
                    if method == "ensures" && mc.args.len() == 2 {
                        if let Expr::Tuple(t) = &mc.args[0] {
                            if t.elems.len() == 1 {
                                let x = pred_borrow_form(&t.elems[0]);
                                let pid = format_ident!("{}", pred_name);
                                let r = mc.args[1].clone();
                                let mut new_expr: Expr = verus_syn::parse_quote! {
                                    #pid.models(#x, #r)
                                };
                                self.visit_expr_mut(&mut new_expr);
                                *expr = new_expr;
                                return;
                            }
                        }
                    }
                    if method == "requires" && mc.args.len() == 1 {
                        *expr = verus_syn::parse_quote! { true };
                        return;
                    }
                }
            }
        }

        // 2a-mapset. Route `Map`/`Set` view operations to the real
        // `HashMap`/`HashSet` method (or `ExecMap`/`ExecSet` companion),
        // BEFORE the `Seq` slice-shape arms below — several method names
        // (`insert`/`remove`/`index`/`contains`) collide between `Seq` and
        // `Map`/`Set`. Fires only when the receiver resolves (through the
        // already-lowered `@` view, i.e. `&<id>` / `&__vcheck_pre_<id>`) to a
        // map/set-shaped ident. Keys are passed by reference to the real
        // `HashMap`/`HashSet` methods; the concrete-key harnesses use
        // primitive keys whose `@` view is the identity.
        if let Expr::MethodCall(mc) = expr {
            if let Some(kind) = self.resolve_mapset(&mc.receiver) {
                let recv = (*mc.receiver).clone();
                let method = mc.method.to_string();
                match (kind, method.as_str(), mc.args.len()) {
                    // ---- Map reads ----
                    (MapSetKind::Map, "contains_key", 1) => {
                        let k = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { (#recv).contains_key(&(#k)) };
                        return;
                    }
                    (MapSetKind::Map, "get", 1) => {
                        // `Map::get(k)` -> `exec_get` (owned `Option<V>`).
                        let k = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { (#recv).exec_get(#k) };
                        return;
                    }
                    (MapSetKind::Map, "index", 1) => {
                        // `Map::index(k)` -> `exec_index` (`&V`).
                        let k = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { (#recv).exec_index(#k) };
                        return;
                    }
                    (MapSetKind::Map, "dom", 0) => {
                        *expr = verus_syn::parse_quote! { (#recv).exec_dom() };
                        return;
                    }
                    // ---- Map mutation ----
                    // Functional `Map::insert` / `Map::remove` -> `exec_*`
                    // (owned `HashMap`), wrapped in `&` so a subsequent
                    // `<map>@ == <this>` compares `&HashMap == &HashMap` via
                    // `HashMap`'s (order-independent) `PartialEq`.
                    (MapSetKind::Map, "insert", 2) => {
                        let k = mc.args[0].clone();
                        let v = mc.args[1].clone();
                        *expr = verus_syn::parse_quote! { &((#recv).exec_insert(#k, #v)) };
                        return;
                    }
                    (MapSetKind::Map, "remove", 1) => {
                        let k = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { &((#recv).exec_remove(#k)) };
                        return;
                    }
                    // ---- Set ----
                    (MapSetKind::Set, "contains", 1) => {
                        let k = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { (#recv).contains(&(#k)) };
                        return;
                    }
                    (MapSetKind::Set, "insert", 1) => {
                        let k = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { &((#recv).exec_insert(#k)) };
                        return;
                    }
                    (MapSetKind::Set, "remove", 1) => {
                        let k = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { &((#recv).exec_remove(#k)) };
                        return;
                    }
                    // Binary set algebra (`Set::union`/`intersect`/`difference`).
                    // The operand `s2@` lowers to `&s2` (a `&HashSet`), matching
                    // the `ExecSpecSet*` companions' `s2: Self` parameter; the
                    // owned result is wrapped in `&` for `<set>@ == <op>`.
                    (MapSetKind::Set, "union", 1) => {
                        let a = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { &((#recv).exec_union(#a)) };
                        return;
                    }
                    (MapSetKind::Set, "intersect", 1) => {
                        let a = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { &((#recv).exec_intersect(#a)) };
                        return;
                    }
                    (MapSetKind::Set, "difference", 1) => {
                        let a = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! { &((#recv).exec_difference(#a)) };
                        return;
                    }
                    (MapSetKind::Set, "map", 1) => {
                        // Functional `Set::map(f)`: apply the spec closure to
                        // every element and materialize the resulting finite set.
                        let f = mc.args[0].clone();
                        *expr = verus_syn::parse_quote! {
                            &(::verus_spec_check::__vcheck_set_map(#recv, #f))
                        };
                        return;
                    }
                    // `len` / `is_empty` map to the real `HashMap`/`HashSet`
                    // methods verbatim; leave them alone (no Seq arm claims
                    // them, so they pass through as `(#recv).len()` etc.).
                    (_, "len", 0) | (_, "is_empty", 0) => return,
                    _ => {}
                }
            }
        }

        // 2a-map-index. Bracket indexing on a Map-shaped binding
        // (`old(m)@[k]` — Verus `Map` index syntax). Route to the
        // `exec_index` companion (owned `V`; panics on an absent key,
        // which the contract context precludes via `contains_key`
        // guards). Must run before the generic Seq index arm below so a
        // map subscript never falls into slice indexing.
        if let Expr::Index(ei) = expr {
            if matches!(self.resolve_mapset(&ei.expr), Some(MapSetKind::Map)) {
                let base = (*ei.expr).clone();
                let k = (*ei.index).clone();
                // `vcheck_owned` normalizes the carriers' differing
                // `exec_index` returns (`&V` for HashMap via vstd_ext,
                // owned `V` for BTreeMap via the runtime companion) to an
                // owned `V`.
                *expr = verus_syn::parse_quote! {
                    ::verus_spec_check::VcheckMapIndexOwned::vcheck_owned((#base).exec_index(#k))
                };
                return;
            }
        }

        // 2a-index. Bracket indexing `<seq>[<expr>]` (Verus `Seq` index
        // syntax, which reaches us as `Expr::Index`). Bare `usize` subscripts
        // pass through as ordinary Rust indexing, but a lifted `SpecInt`
        // subscript (e.g. `old@[old@.len() - 1]` in `Vec::pop` /
        // `VecDeque::pop_back`) is a `BigInt` and can't index a slice —
        // route it through `__vcheck_int::to_usize`. Runs post-recurse so the
        // subscript has already been lowered to its `__vcheck_int::*` form.
        if let Expr::Index(ei) = expr {
            if expr_is_spec_int_call(&ei.index) {
                let base = (*ei.expr).clone();
                let idx = (*ei.index).clone();
                *expr = verus_syn::parse_quote! {
                    (#base)[::verus_spec_check::__vcheck_int::to_usize(#idx)]
                };
                return;
            }
        }

        // 2b. Lower `Seq`-style method calls that appear directly in the
        // harness (e.g. inside an `ensures` clause). The engine handles
        // these inside its own block, but contract clauses are rewritten by
        // this visitor and end up in the harness's `prop_assert!` — so we
        // need a slice-shape lowering. Patterns:
        //   <slice>.index(i as int)      -> <slice>[i as usize]
        //   <slice>.subrange(i, j)       -> &<slice>[i as usize..j as usize]
        //   <slice>.update(i, v)         -> { let mut __t = <slice>.to_vec(); __t[i as usize] = v; __t }
        //   <slice>.len()                -> <slice>.len()  (already valid)
        if let Expr::MethodCall(mc) = expr {
            let method = mc.method.to_string();
            let receiver = (*mc.receiver).clone();
            match method.as_str() {
                "index" if mc.args.len() == 1 => {
                    // The index may be a lifted `SpecInt` (e.g. `len() - 1`);
                    // `lower_index_operand` routes it through `to_usize`
                    // instead of an invalid `BigInt as usize`.
                    let idx = lower_index_operand(&mc.args[0]);
                    let new: Expr = verus_syn::parse_quote! {
                        (#receiver)[#idx]
                    };
                    *expr = new;
                    return;
                }
                "subrange" if mc.args.len() == 2 => {
                    let i = lower_index_operand(&mc.args[0]);
                    let j = lower_index_operand(&mc.args[1]);
                    let new: Expr = verus_syn::parse_quote! {
                        &(#receiver)[#i..#j]
                    };
                    *expr = new;
                    return;
                }
                // `Seq::skip(n)` (all but the first n) / `Seq::take(n)`
                // (the first n) — slice-range lowerings. Seq-only method
                // names in contract position (the bounded-quantifier
                // pre-pass rewrites its own scans to `.iter().cloned()`
                // BEFORE this table runs, so no Iterator collision).
                "skip" if mc.args.len() == 1 => {
                    let n = lower_index_operand(&mc.args[0]);
                    let new: Expr = verus_syn::parse_quote! {
                        &(#receiver)[#n..]
                    };
                    *expr = new;
                    return;
                }
                "take" if mc.args.len() == 1 => {
                    let n = lower_index_operand(&mc.args[0]);
                    let new: Expr = verus_syn::parse_quote! {
                        &(#receiver)[..#n]
                    };
                    *expr = new;
                    return;
                }
                "update" if mc.args.len() == 2 => {
                    let i = lower_index_operand(&mc.args[0]);
                    let v = mc.args[1].clone();
                    // Lower to a call into the harness's `__vcheck_seq_update`
                    // helper. Calling a fn keeps the expression flat — block
                    // / closure syntax in prop_assert! tripped its
                    // format-string parser.
                    // The `.as_slice()` suffix on the Vec-returning seq
                    // helpers (`update`/`push`/`drop_last`/`insert`/
                    // `remove`/`reverse`) marks the result as a sequence
                    // operand, so a parent `==`/`!=` lowers through the
                    // ZST-aware `__vcheck_seq_eq` (rule 4b) instead of
                    // walking a possibly usize::MAX-length ZST sequence
                    // element by element.
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_update((#receiver).to_vec(), #i, #v).as_slice()
                    };
                    *expr = new;
                    return;
                }
                "push" if mc.args.len() == 1 => {
                    // `<slice>.push(x)` is Verus's `Seq::push`, which
                    // returns a new sequence with `x` appended. Lower
                    // through `__vcheck_seq_push` to keep the expression
                    // flat (block syntax trips prop_assert!).
                    let v = mc.args[0].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_push((#receiver).to_vec(), #v).as_slice()
                    };
                    *expr = new;
                    return;
                }
                "drop_last" if mc.args.is_empty() => {
                    // `<slice>.drop_last()` is Verus's `Seq::drop_last`
                    // (all-but-last). Lower through `__vcheck_seq_drop_last`.
                    // `last`/`first`/`drop_last` are Seq-only method names
                    // (Set/Map have no such methods), so this syntactic
                    // rewrite can't collide with a collection spec.
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_drop_last((#receiver).to_vec()).as_slice()
                    };
                    *expr = new;
                    return;
                }
                "last" if mc.args.is_empty() => {
                    // `<slice>.last()` is Verus's `Seq::last`, which
                    // returns the ELEMENT (`T`) — unlike the inherent
                    // slice `.last()` (`Option<&T>`). Lower through the
                    // element-returning helper.
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_last((#receiver).to_vec())
                    };
                    *expr = new;
                    return;
                }
                "first" if mc.args.is_empty() => {
                    // `<slice>.first()` is Verus's `Seq::first` (element
                    // `T`). Same rationale as `last`.
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_first((#receiver).to_vec())
                    };
                    *expr = new;
                    return;
                }
                "insert" if mc.args.len() == 2 => {
                    // `<slice>.insert(i, x)` is Verus's `Seq::insert`
                    // (shift-right). Lower through `__vcheck_seq_insert`.
                    // Same syntactic-match caveat as the `index`/`update`
                    // arms (assumes Seq-shaped receiver; Set/Map aren't
                    // harnessed).
                    let i = lower_index_operand(&mc.args[0]);
                    let x = mc.args[1].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_insert((#receiver).to_vec(), #i, #x).as_slice()
                    };
                    *expr = new;
                    return;
                }
                "remove" if mc.args.len() == 1 => {
                    // `<slice>.remove(i)` is Verus's `Seq::remove`
                    // (shift-left). Lower through `__vcheck_seq_remove`.
                    let i = lower_index_operand(&mc.args[0]);
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_remove((#receiver).to_vec(), #i).as_slice()
                    };
                    *expr = new;
                    return;
                }
                "add" if mc.args.len() == 1 => {
                    // `<slice>.add(<other>)` is Verus's `Seq::add` (the
                    // method form of `Seq + Seq`). Lower the same way as
                    // the binary `+` form.
                    let other = mc.args[0].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_concat(#receiver, #other).as_slice()
                    };
                    *expr = new;
                    return;
                }
                "to_set" if mc.args.is_empty() => {
                    // `Seq::to_set()` materializes the sequence's distinct
                    // elements as a finite runtime HashSet.
                    let new: Expr = verus_syn::parse_quote! {
                        &(::verus_spec_check::__vcheck_seq_to_set(#receiver))
                    };
                    *expr = new;
                    return;
                }
                "contains" if mc.args.len() == 1 => {
                    // `<slice>.contains(x)` is Verus's `Seq::contains`,
                    // which takes the element BY VALUE — unlike the
                    // inherent slice `.contains(&T)`. Left unrewritten it
                    // resolves to the std method and fails to typecheck
                    // (`expected &T, found T`). Set-shaped receivers are
                    // handled by the kind-aware Map/Set table before this
                    // one runs; same syntactic-match caveat as the
                    // `insert`/`remove` arms otherwise.
                    let x = mc.args[0].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_contains(#receiver, #x)
                    };
                    *expr = new;
                    return;
                }
                "reverse" if mc.args.is_empty() => {
                    // `<slice>.reverse()` is Verus's `Seq::reverse`, which
                    // RETURNS the reversed sequence — unlike the inherent
                    // in-place `[T]::reverse` returning `()`. Left
                    // unrewritten the harness compares `()` against a
                    // sequence.
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_reverse((#receiver).to_vec()).as_slice()
                    };
                    *expr = new;
                    return;
                }
                "is_prefix_of" if mc.args.len() == 1 => {
                    // `a.is_prefix_of(b)` is Verus's `Seq::is_prefix_of`.
                    // No inherent slice method of that name exists, so
                    // before this arm the harness failed with E0599.
                    let other = mc.args[0].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_is_prefix_of(#receiver, #other)
                    };
                    *expr = new;
                    return;
                }
                "is_suffix_of" if mc.args.len() == 1 => {
                    // Mirror of `is_prefix_of`.
                    let other = mc.args[0].clone();
                    let new: Expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_seq_is_suffix_of(#receiver, #other)
                    };
                    *expr = new;
                    return;
                }
                _ => {}
            }
        }

        // 3. Spec-method call on a user-typed receiver. We route it through
        // the engine companion: `u.f(..)` ->
        // `<U as ToExecModel>::to_exec_model(&u).exec_f(..)`. This works for
        // both in-block spec methods and EXTERNAL ones (defined + provided in
        // another file), since `exec_f` is generated on the `Exec*` type at
        // its `#[vcheck_provide]` site and reached by path.
        if let Expr::MethodCall(mc) = expr {
            let name = mc.method.to_string();
            let recv_user_ty =
                ident_of_expr(&mc.receiver).and_then(|n| self.user_typed_idents.get(&n).cloned());

            if let Some(user_ty) = recv_user_ty {
                // Receiver is a user-typed ident: always treat the call as a
                // spec-companion call (unknown methods on a sampled user value
                // can only be spec companions in this context).
                if !is_known_runtime_method(&name) {
                    let exec_name = self
                        .when_used_as_spec_redirect
                        .get(&name)
                        .cloned()
                        .unwrap_or_else(|| name.clone());
                    mc.method = format_ident!("exec_{}", exec_name);
                    let recv_name = ident_of_expr(&mc.receiver).unwrap();
                    let recv_id = format_ident!("{}", recv_name);
                    let new_recv: Expr = verus_syn::parse_quote! {
                        <#user_ty as ::verus_spec_check::ToExecModel>::to_exec_model(&#recv_id)
                    };
                    *mc.receiver = new_recv;
                }
            } else if let Some(redirected) = self.when_used_as_spec_redirect.get(&name) {
                // Method-style runtime call with a `when_used_as_spec` redirect:
                // call the spec companion directly.
                mc.method = format_ident!("exec_{}", redirected);
            } else if self.spec_fn_names.contains(&name) {
                // Receiver isn't a tracked user-typed ident, but the method is
                // a known in-block spec fn (e.g. chained `x.perm.is_revoked()`
                // where `x.perm` is already an Exec value): just rename.
                mc.method = format_ident!("exec_{}", mc.method);
            }
        }

        // 4. Sequence concat: `<lhs>.as_slice() + <rhs>.as_slice()` arises
        // when contract clauses write `a@ + b@` (Verus's `Seq::add` / `+`).
        // Plain Rust slices don't support `+`, so route through the runtime
        // helper. Detection is post-rewrite: by the time we see the parent
        // `BinOp::Add`, both children have already been lowered to slice
        // form by the deep_view substitution above.
        if let Expr::Binary(b) = expr {
            // Both operands must be sequence-shaped (a `.as_slice()`
            // projection or a `vec![...]` literal from a lowered `seq!`);
            // plain integer `a + b` has neither, so arithmetic is untouched.
            // `__vcheck_seq_concat` accepts `AsRef<[T]>`, so a by-value `Vec`
            // (from `vec![...]`) and a `&[T]` slice mix freely — this is what
            // makes `seq![value] + old@` (VecDeque `push_front`) lower.
            if matches!(b.op, verus_syn::BinOp::Add(..))
                && expr_is_seq_operand(&b.left)
                && expr_is_seq_operand(&b.right)
            {
                let l = (*b.left).clone();
                let r = (*b.right).clone();
                *expr = verus_syn::parse_quote! {
                    ::verus_spec_check::__vcheck_seq_concat(#l, #r).as_slice()
                };
                return;
            }
        }

        // 4b. Sequence equality: `<lhs>.as_slice() == <rhs>.as_slice()`
        // arises when contract clauses write `a@ == b@` (and the `=~=` /
        // `===` extensional forms). Plain slice `PartialEq` walks every
        // element — for zero-sized element types the boundary strategies
        // produce lengths near `usize::MAX` and the walk never terminates
        // in a debug build. Route through the runtime helper, which
        // compares lengths first and one representative pair for ZSTs.
        // Detection mirrors the concat lowering: both operands must be
        // sequence-shaped post-rewrite, so scalar `==` is untouched.
        if let Expr::Binary(b) = expr {
            use verus_syn::BinOp;
            let positive = match &b.op {
                BinOp::Eq(_) | BinOp::BigEq(_) | BinOp::ExtEq(_) | BinOp::ExtDeepEq(_) => {
                    Some(true)
                }
                BinOp::Ne(_) | BinOp::BigNe(_) | BinOp::ExtNe(_) | BinOp::ExtDeepNe(_) => {
                    Some(false)
                }
                _ => None,
            };
            if let Some(positive) = positive {
                if expr_is_seq_operand(&b.left) && expr_is_seq_operand(&b.right) {
                    let l = (*b.left).clone();
                    let r = (*b.right).clone();
                    *expr = if positive {
                        verus_syn::parse_quote! {
                            ::verus_spec_check::__vcheck_seq_eq(#l, #r)
                        }
                    } else {
                        verus_syn::parse_quote! {
                            (!::verus_spec_check::__vcheck_seq_eq(#l, #r))
                        }
                    };
                    return;
                }
            }
        }

        // 5. Verus-only logical operators have no plain-Rust equivalent.
        // Lower them to ordinary boolean expressions:
        //   `a ==> b`  ->  `!(a) || (b)`
        //   `a <== b`  ->  `!(b) || (a)`
        //   `a <==> b` ->  `(a) == (b)`
        //   `a === b`  ->  `(a) == (b)`   (extensional eq lowers like ==)
        //   `a !== b`  ->  `(a) != (b)`
        // Without these the harness emits tokens like `a <==> b` which rustc
        // refuses to parse.
        if let Expr::Binary(b) = expr {
            use verus_syn::BinOp;
            let l = (*b.left).clone();
            let r = (*b.right).clone();
            match &b.op {
                BinOp::Imply(_) => {
                    *expr = verus_syn::parse_quote! { (!(#l) || (#r)) };
                    return;
                }
                BinOp::Exply(_) => {
                    *expr = verus_syn::parse_quote! { (!(#r) || (#l)) };
                    return;
                }
                BinOp::Equiv(_) | BinOp::BigEq(_) | BinOp::ExtEq(_) | BinOp::ExtDeepEq(_) => {
                    *expr = verus_syn::parse_quote! { ((#l) == (#r)) };
                    return;
                }
                BinOp::BigNe(_) | BinOp::ExtNe(_) | BinOp::ExtDeepNe(_) => {
                    *expr = verus_syn::parse_quote! { ((#l) != (#r)) };
                    return;
                }
                // Shift-by-bitwidth: in Verus's spec semantics `x << N`
                // for `N >= type::BITS` is defined as `0` (modular
                // wrap). In Rust runtime it panics in debug. Lower to
                // `wrapping_shl` / `wrapping_shr` so axioms that
                // mention high shifts evaluate sanely.
                //
                // Skipped when one of the operands is itself an
                // engine-injected receiver method call (`.exec_*(...)`)
                // — those are container ops compiled by `exec_spec`,
                // not numeric shifts.
                BinOp::Shl(_) => {
                    // Skip for `Seq`-style operands.
                    if !expr_is_slice_call(&b.left) && !expr_is_slice_call(&b.right) {
                        *expr = verus_syn::parse_quote! {
                            (#l).wrapping_shl((#r) as u32)
                        };
                        return;
                    }
                }
                BinOp::Shr(_) => {
                    if !expr_is_slice_call(&b.left) && !expr_is_slice_call(&b.right) {
                        *expr = verus_syn::parse_quote! {
                            (#l).wrapping_shr((#r) as u32)
                        };
                        return;
                    }
                }
                _ => {}
            }
        }

        // 6. Spec-int lifting.
        //
        // Verus contract expressions evaluate in unbounded `int`/`nat`
        // arithmetic. Narrowing back to a bounded primitive happens at
        // explicit `as $T` casts and at the boundary into the runtime
        // call. To preserve that semantics at runtime, we lift the bare
        // arithmetic and comparison operators that appear in contracts
        // into the `::verus_spec_check::__vcheck_int::*` helpers from the runtime
        // crate, which operate on a `num_bigint::BigInt`-backed
        // `SpecInt`. See `verus_spec_check_runtime/src/spec_int.rs`.
        //
        // Concretely:
        //   `a + b` (non-slice)  ->  `::verus_spec_check::__vcheck_int::add(a, b)`
        //   `a - b`              ->  `::verus_spec_check::__vcheck_int::sub(a, b)`
        //   `a * b`              ->  `::verus_spec_check::__vcheck_int::mul(a, b)`
        //   `a / b`              ->  `::verus_spec_check::__vcheck_int::div(a, b)`
        //   `a % b`              ->  `::verus_spec_check::__vcheck_int::rem(a, b)`
        //
        // Comparisons are lifted *only* when one operand is already a
        // `__vcheck_int::*` call. Otherwise we leave them alone — the bare
        // `<`/`<=`/etc. on primitives is correct and avoids unnecessary
        // BigInt allocation. The lifting forms:
        //   `a < b`   ->  `::verus_spec_check::__vcheck_int::lt(a, b)`
        //   `a <= b`  ->  `::verus_spec_check::__vcheck_int::le(a, b)`
        //   ...
        //
        // `as $T` on a `__vcheck_int::*` expression becomes the matching
        // `__vcheck_int::to_$T(_)` narrowing call. Out-of-range narrowing
        // panics with a clear message — that's the desired property-
        // test signal that the contract claims a narrowed value but
        // the math evaluated out-of-range.
        //
        // Shifts and bitwise ops keep their existing primitive
        // semantics (`wrapping_shl` etc. above). Verus's bit-vector
        // axioms encode width-dependent behavior (`u8 << 8 == 0`) via
        // the operand types; without type info we can't reliably lift
        // those without regressing the axiom case. Leaving shifts on
        // primitives is the conservative choice.

        // Helper: does `e` look like a call to `::verus_spec_check::__vcheck_int::*`
        // OR a reference to a `let`-bound SpecInt ident? Strips
        // `Expr::Paren` wrappers.
        let is_spec_int = |e: &Expr| -> bool { self.expr_tail_is_vcheck_int(e) };

        // 6-real. Real arithmetic + comparison routing. Runs BEFORE the int
        // lifting (6a/6b) because section 6a lifts *every* arithmetic op to
        // `__vcheck_int` unconditionally — so a real operand must be caught first.
        // Fires only when an operand is `SpecReal`-valued. No `%` (real has no
        // remainder); unary neg is handled in the `Expr::Unary` section below.
        if let Expr::Binary(b) = expr {
            use verus_syn::BinOp;
            if self.expr_tail_is_vcheck_real(&b.left) || self.expr_tail_is_vcheck_real(&b.right) {
                let helper: Option<&'static str> = match &b.op {
                    BinOp::Add(_) => Some("add"),
                    BinOp::Sub(_) => Some("sub"),
                    BinOp::Mul(_) => Some("mul"),
                    BinOp::Div(_) => Some("div"),
                    BinOp::Lt(_) => Some("lt"),
                    BinOp::Le(_) => Some("le"),
                    BinOp::Gt(_) => Some("gt"),
                    BinOp::Ge(_) => Some("ge"),
                    BinOp::Eq(_) => Some("eq"),
                    BinOp::Ne(_) => Some("ne"),
                    _ => None,
                };
                if let Some(h) = helper {
                    let h_id = format_ident!("{}", h);
                    let l = (*b.left).clone();
                    let r = (*b.right).clone();
                    let l_form = self.borrow_form_for_spec_real_ident(&l);
                    let r_form = self.borrow_form_for_spec_real_ident(&r);
                    *expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_real::#h_id(#l_form, #r_form)
                    };
                    return;
                }
            }
        }

        // 6-real-neg. Unary negation of a real: route to `__vcheck_real::neg`
        // (which takes `impl IntoSpecReal`, so a `let`-bound `SpecReal` ident —
        // not `Copy` — is passed by reference rather than moved).
        if let Expr::Unary(u) = expr {
            if matches!(u.op, verus_syn::UnOp::Neg(_)) && self.expr_tail_is_vcheck_real(&u.expr) {
                let operand = self.borrow_form_for_spec_real_ident(&u.expr);
                *expr = verus_syn::parse_quote! {
                    ::verus_spec_check::__vcheck_real::neg(#operand)
                };
                return;
            }
        }

        // 6-int-neg. Unary negation of a SpecInt: route to `__vcheck_int::neg`.
        // Without this, `-(lifted arithmetic)` leaves a raw Rust `-` applied
        // to a `SpecInt` operand (e.g. `requires x >= -(i32::MAX / 2)` lowers
        // its division to `__vcheck_int::div` but the negation and comparison
        // stayed raw, producing an `i32 >= BigInt` type error in the harness).
        // Rewriting to the recognized `neg` call also lets the enclosing
        // comparison lift into the `__vcheck_int` domain (children are visited
        // first, so the comparison arm sees the rewritten call).
        if let Expr::Unary(u) = expr {
            if matches!(u.op, verus_syn::UnOp::Neg(_)) && self.expr_tail_is_vcheck_int(&u.expr) {
                let operand = self.borrow_form_for_spec_int_ident(&u.expr);
                *expr = verus_syn::parse_quote! {
                    ::verus_spec_check::__vcheck_int::neg(#operand)
                };
                return;
            }
        }

        // 6a. Arithmetic lifting.
        if let Expr::Binary(b) = expr {
            use verus_syn::BinOp;
            let l = (*b.left).clone();
            let r = (*b.right).clone();
            // Skip if either operand is a slice expression — those
            // belong to the `Seq` path (handled in section 4).
            let slice_arith = expr_is_slice_call(&b.left) || expr_is_slice_call(&b.right);
            if !slice_arith {
                let helper: Option<&'static str> = match &b.op {
                    BinOp::Add(_) => Some("add"),
                    BinOp::Sub(_) => Some("sub"),
                    BinOp::Mul(_) => Some("mul"),
                    BinOp::Div(_) => Some("div"),
                    BinOp::Rem(_) => Some("rem"),
                    _ => None,
                };
                if let Some(h) = helper {
                    let h_id = format_ident!("{}", h);
                    // For SpecInt-typed operands that are bare idents
                    // bound to a `let`, pass by reference so we don't
                    // move them (BigInt isn't Copy). The `IntoSpecInt`
                    // impl for `&SpecInt` clones internally.
                    let l_form = self.borrow_form_for_spec_int_ident(&l);
                    let r_form = self.borrow_form_for_spec_int_ident(&r);
                    *expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_int::#h_id(#l_form, #r_form)
                    };
                    return;
                }
            }
        }

        // 6b. Comparison lifting (only when an operand is a __vcheck_int::*
        // call, i.e. the comparison sits at the boundary between a
        // lifted arithmetic subexpression and the rest of the
        // contract).
        if let Expr::Binary(b) = expr {
            use verus_syn::BinOp;
            let l = (*b.left).clone();
            let r = (*b.right).clone();
            let lifted = is_spec_int(&l) || is_spec_int(&r);
            if lifted {
                let helper: Option<&'static str> = match &b.op {
                    BinOp::Lt(_) => Some("lt"),
                    BinOp::Le(_) => Some("le"),
                    BinOp::Gt(_) => Some("gt"),
                    BinOp::Ge(_) => Some("ge"),
                    BinOp::Eq(_) => Some("eq"),
                    BinOp::Ne(_) => Some("ne"),
                    _ => None,
                };
                if let Some(h) = helper {
                    let h_id = format_ident!("{}", h);
                    let l_form = self.borrow_form_for_spec_int_ident(&l);
                    let r_form = self.borrow_form_for_spec_int_ident(&r);
                    *expr = verus_syn::parse_quote! {
                        ::verus_spec_check::__vcheck_int::#h_id(#l_form, #r_form)
                    };
                    return;
                }
            }
        }

        // 6c. Cast narrowing: `<lifted> as $T` ->
        // `::verus_spec_check::__vcheck_int::to_$T(<lifted>)`. Only fires when
        // the operand is a `__vcheck_int::*` call (otherwise the cast is
        // a normal primitive `as` on a value of known type — let Rust
        // handle it).
        if let Expr::Cast(cast) = expr {
            if is_spec_int(cast.expr.as_ref()) {
                // Strip any `Type::Group` wrappers introduced by macro
                // hygiene (proc-macro `parse_quote!` of an interpolated
                // type yields `Type::Group(Type::Path(...))`).
                let mut ty_ref: &Type = cast.ty.as_ref();
                while let Type::Group(g) = ty_ref {
                    ty_ref = g.elem.as_ref();
                }
                if let Type::Path(tp) = ty_ref {
                    if tp.qself.is_none()
                        && tp.path.leading_colon.is_none()
                        && tp.path.segments.len() == 1
                    {
                        let target = tp.path.segments[0].ident.to_string();
                        let to_fn: Option<&'static str> = match target.as_str() {
                            "u8" => Some("to_u8"),
                            "u16" => Some("to_u16"),
                            "u32" => Some("to_u32"),
                            "u64" => Some("to_u64"),
                            "u128" => Some("to_u128"),
                            "usize" => Some("to_usize"),
                            "i8" => Some("to_i8"),
                            "i16" => Some("to_i16"),
                            "i32" => Some("to_i32"),
                            "i64" => Some("to_i64"),
                            "i128" => Some("to_i128"),
                            "isize" => Some("to_isize"),
                            _ => None,
                        };
                        if let Some(fn_name) = to_fn {
                            let fn_id = format_ident!("{}", fn_name);
                            let inner = (*cast.expr).clone();
                            *expr = verus_syn::parse_quote! {
                                ::verus_spec_check::__vcheck_int::#fn_id(#inner)
                            };
                            return;
                        }
                    }
                }
            }
        }

        // 6d. `if`-arm type unification.
        //
        // After lifting arithmetic into `SpecInt`, an `if-else` chain
        // can end up with some arms producing `SpecInt` and others
        // producing primitive integer literals (e.g. `if x == 0 { 0 }
        // else { x / d }` after `x: SpecInt`). Rust's type checker
        // refuses the mismatch. To unify, walk the chain and: if any
        // tail-position expression is a `__vcheck_int::*` call (or
        // recursively contains one in its own tail), wrap every other
        // tail in `__vcheck_int::lift(_)`. This is a no-op for SpecInts
        // (idempotent via `IntoSpecInt for SpecInt`) and lifts plain
        // integer literals into SpecInt.
        if let Expr::If(_) = expr {
            self.unify_if_arms_into_spec_int(expr);
        }
    }
}

#[cfg(test)]
mod int_nat_lowering_tests {
    //! How the contract rewriter lowers Verus math-integer literals (`0int`,
    //! `5nat`) and `as int` / `as nat` casts.
    //!
    //! Two distinct things happen and it's worth separating them:
    //!
    //! 1. **Suffix stripping (always).** `0int` / `5nat` are spec-only literals
    //!    with no runtime type — rustc rejects the suffix ("invalid suffix for
    //!    number literal"). So the rewriter *always* rewrites them to the bare
    //!    integer (`0` / `5`). This is unconditional and independent of context.
    //!
    //! 2. **SpecInt lifting (contextual).** A comparison is only lowered into
    //!    the unbounded `::verus_spec_check::__vcheck_int::*` (SpecInt / BigInt) domain
    //!    when a sibling operand is *already* SpecInt-valued (a spec-fn/`@`
    //!    result, lifted arithmetic, a `let`-bound spec-int ident, or an
    //!    explicit `as int` / `as nat` cast). A bare stripped literal by itself
    //!    is NOT a lifting trigger — `x == 0int` where `x` is a primitive stays
    //!    a plain primitive `x == 0`. This is deliberate: promoting a primitive
    //!    comparison to BigInt would be wasteful and, for `==`, semantically
    //!    identical anyway.
    //!
    //! Arithmetic (`+ - * / %`) is the exception: it is *always* lifted so
    //! contract math evaluates in the unbounded domain (that's where spec-vs-impl
    //! overflow mismatches live), then narrowed back at an `as $T` cast.

    use super::*;
    use std::collections::{HashMap, HashSet};
    use verus_syn::visit_mut::VisitMut;

    /// Run the `ContractRewriter` over `expr` with an otherwise-empty context.
    /// `spec_int_idents` seeds the set of idents the rewriter treats as
    /// SpecInt-valued (as if bound by an earlier `let x = __vcheck_int::...`),
    /// which is what drives contextual comparison lifting. Returns the
    /// whitespace-normalized token text of the rewritten expression.
    fn rewrite(expr: Expr, spec_int_idents: &[&str]) -> String {
        let spec_fn_names: HashSet<String> = HashSet::new();
        let param_call_form: HashMap<String, TokenStream2> = HashMap::new();
        let pre_view_for: HashMap<String, TokenStream2> = HashMap::new();
        let user_typed_idents: HashMap<String, Ident> = HashMap::new();
        let auto_borrow_idents: HashMap<String, TokenStream2> = HashMap::new();
        let when_used_as_spec_redirect: HashMap<String, String> = HashMap::new();
        let map_set_shaped_idents: HashMap<String, MapSetKind> = HashMap::new();
        let sampled_pred_idents: HashSet<String> = HashSet::new();

        let mut rw = ContractRewriter {
            spec_fn_names: &spec_fn_names,
            param_call_form: &param_call_form,
            pre_view_for: &pre_view_for,
            user_typed_idents: &user_typed_idents,
            auto_borrow_idents: &auto_borrow_idents,
            when_used_as_spec_redirect: &when_used_as_spec_redirect,
            map_set_shaped_idents: &map_set_shaped_idents,
            sampled_pred_idents: &sampled_pred_idents,
            return_ident: None,
            return_shape: ReturnShape::Unit,
            spec_int_idents: spec_int_idents.iter().map(|s| s.to_string()).collect(),
            spec_real_idents: HashSet::new(),
            int_returning_provided: int_returning_provided_registry(),
        };

        let mut e = expr;
        rw.visit_expr_mut(&mut e);
        quote! { #e }
            .to_string()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    // ---- 1. Unconditional suffix stripping ---------------------------------

    #[test]
    fn top_level_int_literal_suffix_is_stripped() {
        // A bare `0int` on its own becomes `0`. Nothing to lift — the point is
        // just that the spec-only suffix never reaches rustc.
        let out = rewrite(verus_syn::parse_quote! { 0int }, &[]);
        assert_eq!(out, "0", "got: {out}");
    }

    #[test]
    fn top_level_nat_literal_suffix_is_stripped() {
        let out = rewrite(verus_syn::parse_quote! { 5nat }, &[]);
        assert_eq!(out, "5", "got: {out}");
    }

    #[test]
    fn multidigit_int_literal_preserves_digits() {
        // Stripping uses base-10 digits, so the value is preserved verbatim.
        let out = rewrite(verus_syn::parse_quote! { 100int }, &[]);
        assert_eq!(out, "100", "got: {out}");
    }

    #[test]
    fn int_literal_compared_with_primitive_stays_primitive() {
        // `x == 0int` where `x` is an ordinary primitive: the suffix is
        // stripped, but the comparison is NOT lifted (neither operand is
        // SpecInt). Answering "should it be lowered?" — the literal must be,
        // the comparison must not.
        let out = rewrite(verus_syn::parse_quote! { x == 0int }, &[]);
        assert_eq!(out, "x == 0", "got: {out}");
        assert!(
            !out.contains("__vcheck_int"),
            "must not lift to SpecInt: {out}"
        );
    }

    #[test]
    fn two_bare_literals_stay_a_primitive_comparison() {
        // `0int == 5nat` -> `0 == 5`. Both suffixes stripped; no SpecInt domain
        // needed because a literal-vs-literal compare is already well-typed.
        let out = rewrite(verus_syn::parse_quote! { 0int == 5nat }, &[]);
        assert_eq!(out, "0 == 5", "got: {out}");
        assert!(!out.contains("__vcheck_int"), "must not lift: {out}");
    }

    // ---- 2. Contextual lifting: a SpecInt sibling forces the compare up -----

    #[test]
    fn int_literal_compared_with_spec_int_ident_lifts_to_eq() {
        // `s == 0int` where `s` is SpecInt-valued (e.g. bound from a spec fn
        // returning `int`/`nat`): the compare lowers to `__vcheck_int::eq`, the
        // literal is stripped, and the SpecInt operand is passed by reference
        // (BigInt isn't `Copy`).
        let out = rewrite(verus_syn::parse_quote! { s == 0int }, &["s"]);
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_int :: eq"),
            "expected SpecInt eq lowering: {out}"
        );
        assert!(
            out.contains("& s"),
            "SpecInt ident should pass by reference: {out}"
        );
        // No leftover spec-only suffix.
        assert!(!out.contains("0int"), "int suffix leaked: {out}");
    }

    #[test]
    fn nat_literal_compared_with_spec_int_ident_lifts_to_lt() {
        let out = rewrite(verus_syn::parse_quote! { s < 5nat }, &["s"]);
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_int :: lt"),
            "expected SpecInt lt lowering: {out}"
        );
        assert!(!out.contains("5nat"), "nat suffix leaked: {out}");
    }

    #[test]
    fn explicit_as_int_cast_comparison_lifts_and_strips_literal() {
        // `(x as int) == 0int`: the explicit cast signals the source wants the
        // unbounded domain, so the whole comparison lowers to `__vcheck_int::eq`
        // (section A1) even though `x` is a plain primitive. The `0int` literal
        // is stripped during the recursive pass over the rewritten call.
        let out = rewrite(verus_syn::parse_quote! { (x as int) == 0int }, &[]);
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_int :: eq"),
            "explicit `as int` cast should force SpecInt lowering: {out}"
        );
        assert!(
            !out.contains("as int"),
            "the `as int` cast should be consumed: {out}"
        );
        assert!(!out.contains("0int"), "int suffix leaked: {out}");
    }

    // ---- 3. Arithmetic is always lifted ------------------------------------

    #[test]
    fn int_literal_in_arithmetic_lifts_to_vcheck_int_add() {
        // Arithmetic always lowers into the unbounded domain, so a literal
        // operand is stripped and folded into a `__vcheck_int::add` call.
        let out = rewrite(verus_syn::parse_quote! { x + 1int }, &[]);
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_int :: add"),
            "arithmetic should lift to SpecInt: {out}"
        );
        assert!(
            out.contains("1") && !out.contains("1int"),
            "literal should be stripped: {out}"
        );
    }

    #[test]
    fn nested_arith_and_compare_with_literals_all_lifted() {
        // `s == x * 2int + 1int`: inner arithmetic lifts (`mul` then `add`),
        // which makes the RHS SpecInt, so the outer `==` lifts to `eq`. Every
        // literal suffix is gone.
        let out = rewrite(verus_syn::parse_quote! { s == x * 2int + 1int }, &["s"]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_int :: eq"), "{out}");
        assert!(out.contains(":: verus_spec_check :: __vcheck_int :: mul"), "{out}");
        assert!(out.contains(":: verus_spec_check :: __vcheck_int :: add"), "{out}");
        // No spec-only literal suffix survives (the substring "int" itself is
        // fine — it appears in `__vcheck_int`; what must be gone is `2int`/`1int`).
        assert!(!out.contains("2int"), "int suffix leaked: {out}");
        assert!(!out.contains("1int"), "int suffix leaked: {out}");
    }

    // ---- 4. End-to-end through `expand` (the assume-spec scenario) ----------

    #[test]
    fn expand_assume_spec_with_int_literal_ensures_strips_suffix() {
        // Mirrors the user's scenario: an `assume_specification`-style trusted
        // exec fn whose ensures compares against an `int` literal.
        //
        // Important design point this test pins down: the engine emits the
        // ORIGINAL spec/exec fn verbatim inside a `vstd::prelude::verus! { .. }`
        // block (only Verus consumes that; rustc never does), so `0int`
        // legitimately survives *there* — it must, since Verus needs the real
        // spec. The stripping + SpecInt lowering happens only in the generated
        // `#[cfg(test)]` harness module, which is the executable code. So we
        // scope the assertions to the harness, not the whole expansion.
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            pub exec fn __vcheck_assume_zero(x: u32) -> (result: u32)
                ensures
                    result as int == 0int,
            {
                0u32
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();

        // The harness module is named `__verus_spec_check_<n>` where `<n>` comes from
        // a process-global counter, so match on the prefix (not a fixed index)
        // to stay robust when other tests expand first.
        let harness = text
            .split("mod __verus_spec_check_")
            .nth(1)
            .expect("expansion should contain the generated harness module");
        assert!(
            harness.contains(":: verus_spec_check :: __vcheck_int :: eq (result , 0)"),
            "harness should lower `result as int == 0int` to a SpecInt eq: {harness}"
        );
        assert!(
            !harness.contains("0int"),
            "no spec-only int suffix should reach the executable harness: {harness}"
        );
    }

    #[test]
    fn negated_lifted_arithmetic_routes_to_neg_and_lifts_comparison() {
        // `x >= -(i32::MAX / 2)`: the division always lifts to
        // `__vcheck_int::div` (SpecInt), so the negation must route to
        // `__vcheck_int::neg` and the comparison must lift to
        // `__vcheck_int::ge`. Regression test for the cov_mutate
        // `signed_double` example, where the raw `-` left an
        // `i32 >= BigInt` type error in the harness.
        let out = rewrite(verus_syn::parse_quote! { x >= -(i32::MAX / 2) }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_int :: neg"), "{out}");
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_int :: ge (x ,"),
            "{out}"
        );
        assert!(
            !out.contains("- ("),
            "raw unary minus must not survive: {out}"
        );
    }

    #[test]
    fn negated_spec_int_ident_routes_to_neg() {
        // A `let`-bound SpecInt ident under unary minus takes the same
        // path (and is passed by reference — BigInt isn't Copy).
        let out = rewrite(verus_syn::parse_quote! { -s + 1 }, &["s"]);
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_int :: neg (& s)"),
            "{out}"
        );
        assert!(out.contains(":: verus_spec_check :: __vcheck_int :: add"), "{out}");
    }
}

#[cfg(test)]
mod real_lowering_tests {
    //! Tests how the contract rewriter lowers Verus `real` expressions
    //!
    //! `real` mirrors `int`/`nat` but with two twists (see `spec_real.rs`):
    //!   - there's no runtime primitive, so a `real` literal lowers *directly*
    //!     to an exact `__vcheck_real::from_str(..)` constant (`0.1real` = 1/10,
    //!     not the f64 rounding), and `x as real` -> `__vcheck_real::cast(x)`;
    //!   - `+ - * /` and comparisons route to `__vcheck_real::*` when an operand
    //!     is real (no `%`), and `as int` / `.floor()` bridge back via
    //!     `__vcheck_real::floor` (returning a `SpecInt`).

    use super::*;
    use std::collections::{HashMap, HashSet};
    use verus_syn::visit_mut::VisitMut;

    /// Run the rewriter over `expr`, seeding `spec_real_idents` (idents treated
    /// as `let`-bound `SpecReal` values). Returns normalized token text.
    fn rewrite_real(expr: Expr, spec_real_idents: &[&str]) -> String {
        let spec_fn_names: HashSet<String> = HashSet::new();
        let param_call_form: HashMap<String, TokenStream2> = HashMap::new();
        let pre_view_for: HashMap<String, TokenStream2> = HashMap::new();
        let user_typed_idents: HashMap<String, Ident> = HashMap::new();
        let auto_borrow_idents: HashMap<String, TokenStream2> = HashMap::new();
        let when_used_as_spec_redirect: HashMap<String, String> = HashMap::new();
        let map_set_shaped_idents: HashMap<String, MapSetKind> = HashMap::new();
        let sampled_pred_idents: HashSet<String> = HashSet::new();

        let mut rw = ContractRewriter {
            spec_fn_names: &spec_fn_names,
            param_call_form: &param_call_form,
            pre_view_for: &pre_view_for,
            user_typed_idents: &user_typed_idents,
            auto_borrow_idents: &auto_borrow_idents,
            when_used_as_spec_redirect: &when_used_as_spec_redirect,
            map_set_shaped_idents: &map_set_shaped_idents,
            sampled_pred_idents: &sampled_pred_idents,
            return_ident: None,
            return_shape: ReturnShape::Unit,
            spec_int_idents: HashSet::new(),
            spec_real_idents: spec_real_idents.iter().map(|s| s.to_string()).collect(),
            int_returning_provided: HashSet::new(),
        };
        let mut e = expr;
        rw.visit_expr_mut(&mut e);
        quote! { #e }
            .to_string()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[test]
    fn int_form_real_literal_lowers_to_exact_from_str() {
        let out = rewrite_real(verus_syn::parse_quote! { 100real }, &[]);
        assert_eq!(
            out, ":: verus_spec_check :: __vcheck_real :: from_str (\"100\")",
            "got: {out}"
        );
    }

    #[test]
    fn float_form_real_literal_lowers_to_exact_from_str() {
        let out = rewrite_real(verus_syn::parse_quote! { 1.5real }, &[]);
        assert_eq!(
            out, ":: verus_spec_check :: __vcheck_real :: from_str (\"1.5\")",
            "got: {out}"
        );
    }

    #[test]
    fn as_real_cast_lowers_to_cast() {
        let out = rewrite_real(verus_syn::parse_quote! { x as real }, &[]);
        assert_eq!(out, ":: verus_spec_check :: __vcheck_real :: cast (x)", "got: {out}");
    }

    #[test]
    fn real_addition_routes_to_vcheck_real_add() {
        let out = rewrite_real(verus_syn::parse_quote! { (x as real) + 1real }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_real :: add"), "{out}");
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_real :: cast (x)"),
            "{out}"
        );
        assert!(out.contains("from_str (\"1\")"), "{out}");
        // Must NOT go through the integer path.
        assert!(!out.contains("__vcheck_int"), "{out}");
    }

    #[test]
    fn real_division_routes_to_vcheck_real_div() {
        let out = rewrite_real(verus_syn::parse_quote! { (x as real) / (y as real) }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_real :: div"), "{out}");
        assert!(!out.contains("__vcheck_int"), "{out}");
    }

    #[test]
    fn real_comparison_routes_to_vcheck_real_le() {
        let out = rewrite_real(verus_syn::parse_quote! { (x as real) <= 1.5real }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_real :: le"), "{out}");
    }

    #[test]
    fn real_as_int_lowers_to_floor() {
        let out = rewrite_real(verus_syn::parse_quote! { (x as real) as int }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_real :: floor"), "{out}");
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_real :: cast (x)"),
            "{out}"
        );
    }

    #[test]
    fn real_floor_method_lowers_to_floor() {
        let out = rewrite_real(verus_syn::parse_quote! { (x as real).floor() }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_real :: floor"), "{out}");
    }

    #[test]
    fn real_negation_routes_to_vcheck_real_neg() {
        let out = rewrite_real(verus_syn::parse_quote! { -(x as real) }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_real :: neg"), "{out}");
    }

    #[test]
    fn let_bound_real_ident_passes_by_reference() {
        // A `let`-bound real ident routes arithmetic to the real path and is
        // passed by reference (BigRational isn't Copy).
        let out = rewrite_real(verus_syn::parse_quote! { r + 1real }, &["r"]);
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_real :: add (& r"),
            "{out}"
        );
    }

    #[test]
    fn pure_int_expression_unaffected_by_real_support() {
        // Regression: an expression with no real operand still lowers through
        // the integer path.
        let out = rewrite_real(verus_syn::parse_quote! { x + 1int }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_int :: add"), "{out}");
        assert!(!out.contains("__vcheck_real"), "{out}");
    }

    #[test]
    fn all_real_binary_ops_route_to_vcheck_real() {
        for (src, helper) in [
            ("(x as real) - 1real", "sub"),
            ("(x as real) * 2real", "mul"),
            ("(x as real) < 1real", "lt"),
            ("(x as real) > 1real", "gt"),
            ("(x as real) >= 1real", "ge"),
            ("(x as real) == 1real", "eq"),
            ("(x as real) != 1real", "ne"),
        ] {
            let expr: Expr = verus_syn::parse_str(src).unwrap();
            let out = rewrite_real(expr, &[]);
            let expected = format!(":: verus_spec_check :: __vcheck_real :: {helper}");
            assert!(out.contains(&expected), "`{src}` -> {out}");
            assert!(
                !out.contains("__vcheck_int"),
                "`{src}` leaked to int path: {out}"
            );
        }
    }

    #[test]
    fn floor_result_compares_via_int_path() {
        // `(x as real) as int == 3`: floor returns a SpecInt, so the `==`
        // must lift through the INTEGER helper (BigInt), not the real one.
        let out = rewrite_real(verus_syn::parse_quote! { (x as real) as int == 3 }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_real :: floor"), "{out}");
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_int :: eq"),
            "compare must use int path: {out}"
        );
    }

    #[test]
    fn let_binding_registered_by_visit_local_mut() {
        // Exercise the `visit_local_mut` real-registration branch (not seeded):
        // `let r = x as real;` registers `r`, so `r * 2real` routes to real.
        let out = rewrite_real(
            verus_syn::parse_quote! { { let r = x as real; r * 2real } },
            &[],
        );
        assert!(
            out.contains(":: verus_spec_check :: __vcheck_real :: mul (& r"),
            "{out}"
        );
    }

    #[test]
    fn parenthesized_real_operand_is_detected() {
        // `expr_tail_is_vcheck_real` must see through parens.
        let out = rewrite_real(verus_syn::parse_quote! { ((x as real)) + 1real }, &[]);
        assert!(out.contains(":: verus_spec_check :: __vcheck_real :: add"), "{out}");
    }
}

/// If `expr` is `old(<id>)` -- possibly wrapped in parens and/or a deref, as in
/// `(*old(s))` -- return the ident's name. Used by the `remaining().unref()`
/// composite lowering, which must look through the wrappers the vstd
/// `IteratorSpec` idiom puts around the `old` call.
fn old_call_ident_through_wrappers(expr: &Expr) -> Option<String> {
    let mut cur = expr;
    loop {
        match cur {
            Expr::Paren(p) => cur = p.expr.as_ref(),
            Expr::Unary(u) if matches!(u.op, verus_syn::UnOp::Deref(_)) => cur = u.expr.as_ref(),
            _ => break,
        }
    }
    if let Expr::Call(call) = cur {
        if let Expr::Path(ExprPath {
            path, qself: None, ..
        }) = call.func.as_ref()
        {
            if path.leading_colon.is_none()
                && path.segments.len() == 1
                && path.segments[0].ident == "old"
                && call.args.len() == 1
            {
                return ident_of_expr(&call.args[0]);
            }
        }
    }
    None
}

#[cfg(test)]
mod std_value_projection_tests {
    use super::*;
    use std::collections::{HashMap, HashSet};
    use verus_syn::visit_mut::VisitMut;

    fn rewrite_with_return(expr: Expr, return_shape: ReturnShape) -> String {
        let spec_fn_names: HashSet<String> = HashSet::new();
        let param_call_form: HashMap<String, TokenStream2> = HashMap::new();
        let pre_view_for: HashMap<String, TokenStream2> = HashMap::new();
        let user_typed_idents: HashMap<String, Ident> = HashMap::new();
        let auto_borrow_idents: HashMap<String, TokenStream2> = HashMap::new();
        let when_used_as_spec_redirect: HashMap<String, String> = HashMap::new();
        let map_set_shaped_idents: HashMap<String, MapSetKind> = HashMap::new();
        let sampled_pred_idents: HashSet<String> = HashSet::new();
        let mut rw = ContractRewriter {
            spec_fn_names: &spec_fn_names,
            param_call_form: &param_call_form,
            pre_view_for: &pre_view_for,
            user_typed_idents: &user_typed_idents,
            auto_borrow_idents: &auto_borrow_idents,
            when_used_as_spec_redirect: &when_used_as_spec_redirect,
            map_set_shaped_idents: &map_set_shaped_idents,
            sampled_pred_idents: &sampled_pred_idents,
            return_ident: Some(format_ident!("r")),
            return_shape,
            spec_int_idents: HashSet::new(),
            spec_real_idents: HashSet::new(),
            int_returning_provided: HashSet::new(),
        };
        let mut e = expr;
        rw.visit_expr_mut(&mut e);
        quote! { #e }.to_string().split_whitespace().collect::<Vec<_>>().join(" ")
    }

    fn prim(src: &str) -> ParamElem {
        ParamElem::Primitive(verus_syn::parse_str(src).unwrap())
    }

    #[test]
    fn option_nonzero_projection_view_calls_get() {
        let out = rewrite_with_return(
            verus_syn::parse_quote! { r->Some_0@ },
            ReturnShape::OwnedOption(prim("core::num::NonZero<i32>")),
        );
        assert!(out.contains(". get ()"), "got: {out}");
        assert!(out.contains("Some (__v) => __v"), "got: {out}");
    }

    #[test]
    fn primitive_projection_view_is_unchanged() {
        let out = rewrite_with_return(
            verus_syn::parse_quote! { r->Some_0@ },
            ReturnShape::OwnedOption(prim("u32")),
        );
        assert!(!out.contains("get ()"), "got: {out}");
        assert!(!out.contains("__vcheck_range_inclusive_view"), "got: {out}");
    }
}
