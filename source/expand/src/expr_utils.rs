use super::*;

/// Like `is_call_to_vcheck_int` but restricted to *SpecInt*-returning
/// helpers (the arithmetic / lift / shift / bitwise ops), not the
/// boolean comparison helpers. Used by the if-arm unification logic
/// so that we don't accidentally treat `x % y == 0` (bool) as an
/// arm that needs sibling-arms lifted to SpecInt.
pub fn is_call_to_vcheck_int_returning_int(e: &Expr) -> bool {
    if let Expr::Call(call) = e {
        if let Expr::Path(ExprPath {
            path, qself: None, ..
        }) = call.func.as_ref()
        {
            let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
            if path.leading_colon.is_some()
                && segs.len() == 3
                && segs[0] == "verus_spec_check"
                && segs[1] == "__vcheck_int"
            {
                return matches!(
                    segs[2].as_str(),
                    "add"
                        | "sub"
                        | "mul"
                        | "div"
                        | "rem"
                        | "neg"
                        | "lift"
                        | "shl"
                        | "shr"
                        | "bitand"
                        | "bitor"
                        | "bitxor"
                        | "from_display"
                );
            }
            // `__vcheck_real::floor` returns a `SpecInt` (it bridges the real
            // domain back to integers), so a comparison/cast against its result
            // routes through the integer path — e.g. `(r as int) == n` lifts to
            // `__vcheck_int::eq(__vcheck_real::floor(..), n)`.
            if path.leading_colon.is_some()
                && segs.len() == 3
                && segs[0] == "verus_spec_check"
                && segs[1] == "__vcheck_real"
                && segs[2] == "floor"
            {
                return true;
            }
        }
    }
    false
}

/// The `real` analogue of [`is_call_to_vcheck_int_returning_int`]: is `e` a call
/// to a `::verus_spec_check::__vcheck_real::*` helper that returns a `SpecReal`? Note
/// `floor` is excluded — it returns a `SpecInt`, bridging back to the integer
/// domain (so a comparison against a `floor(..)` result lifts via the int path,
/// not the real path).
pub fn is_call_to_vcheck_real_returning_real(e: &Expr) -> bool {
    if let Expr::Call(call) = e {
        if let Expr::Path(ExprPath {
            path, qself: None, ..
        }) = call.func.as_ref()
        {
            let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
            if path.leading_colon.is_some()
                && segs.len() == 3
                && segs[0] == "verus_spec_check"
                && segs[1] == "__vcheck_real"
            {
                return matches!(
                    segs[2].as_str(),
                    "add"
                        | "sub"
                        | "mul"
                        | "div"
                        | "neg"
                        | "lift"
                        | "cast"
                        | "from_int"
                        | "from_f64"
                        | "from_f32"
                        | "from_str"
                );
            }
        }
    }
    false
}

impl<'a> ContractRewriter<'a> {
    /// Walk an `if-else` chain rooted at `expr` and ensure every tail
    /// expression in every arm is a `SpecInt`-producing expression.
    /// Tails that aren't already SpecInt get wrapped in
    /// `__vcheck_int::lift(_)`. No-op when no arm of the chain produces
    /// a SpecInt — in that case the if-else uses primitive types
    /// throughout and Rust handles it.
    pub fn unify_if_arms_into_spec_int(&self, expr: &mut Expr) {
        if !self.any_arm_is_spec_int(expr) {
            return;
        }
        self.force_arms(expr);
    }

    fn any_arm_is_spec_int(&self, e: &Expr) -> bool {
        if let Expr::If(eif) = e {
            let then_si = match eif.then_branch.stmts.last() {
                Some(verus_syn::Stmt::Expr(t, None)) => self.expr_tail_is_vcheck_int(t),
                _ => false,
            };
            let else_si = match &eif.else_branch {
                Some((_, els)) => {
                    if matches!(els.as_ref(), Expr::If(_)) {
                        self.any_arm_is_spec_int(els.as_ref())
                    } else {
                        self.expr_tail_is_vcheck_int(els.as_ref())
                    }
                }
                None => false,
            };
            then_si || else_si
        } else {
            false
        }
    }

    fn wrap_tail(&self, e: &mut Expr) {
        if self.expr_tail_is_vcheck_int(e) {
            return;
        }
        if let Expr::If(_) = e {
            self.force_arms(e);
            return;
        }
        if let Expr::Block(b) = e {
            if let Some(verus_syn::Stmt::Expr(tail, None)) = b.block.stmts.last_mut() {
                self.wrap_tail(tail);
                return;
            }
        }
        if let Expr::Paren(p) = e {
            self.wrap_tail(p.expr.as_mut());
            return;
        }
        let inner = e.clone();
        *e = verus_syn::parse_quote! { ::verus_spec_check::__vcheck_int::lift(#inner) };
    }

    fn force_arms(&self, e: &mut Expr) {
        if let Expr::If(eif) = e {
            if let Some(verus_syn::Stmt::Expr(tail, None)) = eif.then_branch.stmts.last_mut() {
                self.wrap_tail(tail);
            }
            if let Some((_, els)) = &mut eif.else_branch {
                if matches!(els.as_ref(), Expr::If(_)) {
                    self.force_arms(els.as_mut());
                } else {
                    self.wrap_tail(els.as_mut());
                }
            }
        }
    }
}

impl<'a> ContractRewriter<'a> {
    /// If `arg` is a bare ident `u` (or `*u`) matching one of the
    /// rewriter's known param shapes, replace it with the form expected by
    /// the spec-fn companion:
    ///   - User type `u: User`  -> `&__vcheck_to_exec_User(&u)`.
    ///   - Owned String `s: String` -> `&s` (so a spec fn taking `&str`
    ///     receives a borrow that derefs to `&str`).
    ///   - Owned Vec etc. -> `&v` (works for any `&[T]`/`&Vec<T>` callee).
    pub fn convert_user_arg(&self, arg: &mut Expr) {
        // Unwrap a single deref: `*p` where `p: &User`.
        let inner: &Expr = match &*arg {
            Expr::Unary(u) if matches!(u.op, verus_syn::UnOp::Deref(_)) => u.expr.as_ref(),
            other => other,
        };
        if let Some(name) = ident_of_expr(inner) {
            if let Some(user_ty) = self.user_typed_idents.get(&name) {
                let id = format_ident!("{}", name);
                *arg = verus_syn::parse_quote! {
                    &<#user_ty as ::verus_spec_check::ToExecModel>::to_exec_model(&#id)
                };
                return;
            }
            if let Some(borrow_form) = self.auto_borrow_idents.get(&name) {
                *arg = verus_syn::parse_quote! { #borrow_form };
                return;
            }
        }
    }

    pub fn rewrite_return_deep_view(&self, ret_ident: Ident) -> Expr {
        match &self.return_shape {
            ReturnShape::OwnedVec(_) => {
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident.as_slice() }
            }
            ReturnShape::OwnedVecDeque(_) => {
                // `VecDeque` has no `as_slice`; materialize its contiguous
                // order, then slice.
                verus_syn::parse_quote_spanned! { ret_ident.span() =>
                    ::verus_spec_check::__vcheck_vecdeque_slice(&#ret_ident).as_slice()
                }
            }
            ReturnShape::OwnedArray(_, _) => {
                // Returned `[E; N]` is already array-shaped; `as_slice()`
                // converts to `&[E]` for the engine's `Seq<E>` treatment.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident.as_slice() }
            }
            ReturnShape::RefSlice(_) | ReturnShape::RefArray(_, _) => {
                // Shared `&[T]` / `&[T; N]` are already slice-shaped.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
            ReturnShape::MutRefSlice(_) | ReturnShape::MutRefArray(_, _) => {
                // Mutable slice returns are rebound to owned Vec snapshots
                // immediately after the call.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident.as_slice() }
            }
            ReturnShape::OwnedUserType(_)
            | ReturnShape::OwnedOption(_)
            | ReturnShape::OwnedResult(_, _)
            | ReturnShape::OwnedHashMap
            | ReturnShape::OwnedHashSet
            | ReturnShape::OwnedBTreeMap
            | ReturnShape::OwnedBTreeSet
            | ReturnShape::OwnedMultiset => {
                verus_syn::parse_quote_spanned! { ret_ident.span() => &#ret_ident }
            }
            ReturnShape::RefUserType(_) => {
                // Already a reference; pass through.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
            ReturnShape::RefPrimitive(_) => {
                // `&T` where `T: Copy`: dereference for value comparisons.
                verus_syn::parse_quote_spanned! { ret_ident.span() => *#ret_ident }
            }
            ReturnShape::RefStr | ReturnShape::OwnedString => {
                // `&str` / `String`: collect chars via the runtime helper
                // (a free fn, not a block expression) so the rewritten
                // clause is a flat call. Block syntax `{ ... }` trips
                // proptest's format-string scanner inside prop_assert!.
                let receiver: Expr = match &self.return_shape {
                    ReturnShape::RefStr => verus_syn::parse_quote_spanned! {
                        ret_ident.span() => &#ret_ident
                    },
                    _ => verus_syn::parse_quote_spanned! {
                        ret_ident.span() => &#ret_ident[..]
                    },
                };
                verus_syn::parse_quote_spanned! { ret_ident.span() =>
                    ::verus_spec_check::__vcheck_str_chars(#receiver).as_slice()
                }
            }
            ReturnShape::Primitive | ReturnShape::Unit => {
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
            ReturnShape::OwnedOrdering | ReturnShape::OwnedOptionOrdering => {
                // `Ordering` / `Option<Ordering>` are value types with
                // `PartialEq + Eq`; contracts compare them directly to
                // `Ordering::Less` / `Some(Ordering::Less)` etc.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
            ReturnShape::OpaqueConcretize(_) => {
                // The harness holds the real opaque result; `view(ret)` in
                // the contract lowers to `ret.vcheck_realize()` via the
                // view-fn rewrite, so pass `ret` through unchanged.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
            ReturnShape::Tuple2(_, _) => {
                // Tuple returns: pass `ret` through. Contracts that
                // access `.0` / `.1` work natively; element-wise
                // deep_view isn't yet wired up, so contracts that need
                // `ret.0.deep_view()` (e.g. `Seq` projection of a slice
                // element) will fail. The common 2-tuple-of-bools /
                // 2-tuple-of-primitives case works directly.
                verus_syn::parse_quote_spanned! { ret_ident.span() => #ret_ident }
            }
        }
    }
}

pub fn ident_of_expr(expr: &Expr) -> Option<String> {
    if let Expr::Path(ExprPath {
        path, qself: None, ..
    }) = expr
    {
        if path.segments.len() == 1 && matches!(path.segments[0].arguments, PathArguments::None) {
            return Some(path.segments[0].ident.to_string());
        }
    }
    None
}

/// Borrow-normalize the argument of a lowered `call_ensures` on a sampled
/// predicate: `VcheckPred::models` takes `&T`. Spec-side the tuple element is
/// written `(&elem,)` (already a reference expression — keep as-is) or
/// `(elem,)` (borrow it). The runtime binder for quantifier-lowered
/// elements is an owned `T` (see the `.iter().cloned()` bounded-quantifier
/// lowering), so one borrow level is exactly right in both spellings.
pub fn pred_borrow_form(e: &Expr) -> Expr {
    match e {
        Expr::Reference(_) => e.clone(),
        _ => verus_syn::parse_quote! { &(#e) },
    }
}

/// Detects `a <= b <= c` (or `<`, `<=`, `<`, `<=` mix) parsed as a left-
/// associative chain `(a <= b) <= c`, and rewrites it as
/// `(a <= b) && (b <= c)`. Same handling for `a > b > c` etc., and for
/// equality runs `a == b == c`. Anything else: returns None.
///
/// Also handles longer chains: `0 <= i <= j <= s.len()` parses as
/// `(((0 <= i) <= j) <= s.len())`. After the inner `(0 <= i) <= j` rewrites
/// to `(0 <= i) && (i <= j)`, the outer `<expr> <= s.len()` needs to grab
/// the rightmost-comparison-RHS (`j` here) as the new chain pivot.
/// True if `e` (peeling `Paren`/`Group` wrappers) is a zero-arg call to
/// `Map::<...>::empty()` or `Set::<...>::empty()` — Verus's spec-side empty
/// map/set constructors. Used by the 0-empty-map comparison pass in the
/// contract rewriter, which lowers such an operand to `&Default::default()`
/// so the comparison typechecks against the `&`-borrowed runtime container
/// (HashMap or BTreeMap, inferred from the other operand).
pub fn is_map_set_empty_call(e: &Expr) -> bool {
    let mut cur = e;
    loop {
        match cur {
            Expr::Paren(p) => cur = p.expr.as_ref(),
            Expr::Group(g) => cur = g.expr.as_ref(),
            _ => break,
        }
    }
    if let Expr::Call(call) = cur {
        if !call.args.is_empty() {
            return false;
        }
        if let Expr::Path(ExprPath {
            path, qself: None, ..
        }) = call.func.as_ref()
        {
            let n = path.segments.len();
            if n >= 2 {
                let container = path.segments[n - 2].ident.to_string();
                let method = &path.segments[n - 1];
                return method.ident == "empty"
                    && matches!(method.arguments, PathArguments::None)
                    && matches!(container.as_str(), "Map" | "Set");
            }
        }
    }
    false
}

/// If `e` (peeling `Paren`/`Group` wrappers) is an `<inner> as int` or
/// `<inner> as nat` cast, return `inner`. Used by the A1 comparison-lifting
/// pass to detect operands the source explicitly promoted to the spec-integer
/// domain.
pub fn spec_int_cast_inner(e: &Expr) -> Option<Expr> {
    let mut cur = e;
    loop {
        match cur {
            Expr::Paren(p) => cur = p.expr.as_ref(),
            Expr::Group(g) => cur = g.expr.as_ref(),
            Expr::Cast(c) => {
                let mut ty_ref: &Type = c.ty.as_ref();
                while let Type::Group(g) = ty_ref {
                    ty_ref = g.elem.as_ref();
                }
                if let Type::Path(tp) = ty_ref {
                    if tp.qself.is_none()
                        && tp.path.leading_colon.is_none()
                        && tp.path.segments.len() == 1
                    {
                        let t = tp.path.segments[0].ident.to_string();
                        if t == "int" || t == "nat" {
                            // `<real> as int` is a *floor*, not a spec-int
                            // promotion — don't let the A1 comparison-lift treat
                            // it as an integer operand. Bow out so the
                            // post-recurse `real as int` -> `__vcheck_real::floor`
                            // branch handles it (and the resulting `SpecInt`
                            // floor then lifts the comparison via the int path).
                            if expr_is_syntactic_real(&c.expr) {
                                return None;
                            }
                            return Some((*c.expr).clone());
                        }
                    }
                }
                return None;
            }
            _ => return None,
        }
    }
}

/// Syntactic (pre-rewrite) test for "this expression is a `real`": an
/// `<x> as real` cast or a `<n>real` / `<f>real` literal, peeling `Paren` /
/// `Group` wrappers. Used where the rewriter must distinguish `real` operands
/// before the recursive lowering has run (e.g. the A1 comparison pass).
pub fn expr_is_syntactic_real(e: &Expr) -> bool {
    let mut cur = e;
    loop {
        match cur {
            Expr::Paren(p) => cur = p.expr.as_ref(),
            Expr::Group(g) => cur = g.expr.as_ref(),
            Expr::Cast(c) => {
                let mut ty_ref: &Type = c.ty.as_ref();
                while let Type::Group(g) = ty_ref {
                    ty_ref = g.elem.as_ref();
                }
                if let Type::Path(tp) = ty_ref {
                    if tp.qself.is_none()
                        && tp.path.leading_colon.is_none()
                        && tp.path.segments.len() == 1
                    {
                        return tp.path.segments[0].ident == "real";
                    }
                }
                return false;
            }
            Expr::Lit(verus_syn::ExprLit { lit, .. }) => {
                return match lit {
                    verus_syn::Lit::Int(li) => li.suffix() == "real",
                    verus_syn::Lit::Float(lf) => lf.suffix() == "real",
                    _ => false,
                };
            }
            _ => return false,
        }
    }
}

pub fn rewrite_chained_compare(expr: &Expr) -> Option<Expr> {
    use verus_syn::BinOp;

    fn is_comparison(op: &BinOp) -> bool {
        // Only the inequality comparisons participate in Verus's
        // chained-comparison syntax. `a == b == c` in Verus means
        // transitive equality, but at runtime `==` is left-
        // associative and the inner result is a `bool` that won't
        // compare with `c`. Limit the rewrite to ordering operators
        // so the wrapper-synthesized `ensures __vcheck_ret == s@.len()
        // == 0` (a single bool equality where the RHS happens to
        // have `==` in it) doesn't get mangled into
        // `(__vcheck_ret == s@.len()) && (s@.len() == 0)`.
        matches!(
            op,
            BinOp::Lt(..) | BinOp::Le(..) | BinOp::Gt(..) | BinOp::Ge(..)
        )
    }

    /// Recover the chain pivot from a left-side expression that may already
    /// have been rewritten to `<...> && (a OP b)` form. Returns `b` for
    /// the trailing comparison.
    fn rightmost_compare_rhs(e: &Expr) -> Option<Expr> {
        match e {
            Expr::Binary(b) if is_comparison(&b.op) => Some((*b.right).clone()),
            Expr::Binary(b) if matches!(b.op, BinOp::And(_)) => {
                // After a previous chain rewrite the right side is a
                // comparison.
                rightmost_compare_rhs(&b.right)
            }
            Expr::Paren(p) => rightmost_compare_rhs(&p.expr),
            _ => None,
        }
    }

    let outer = match expr {
        Expr::Binary(b) if is_comparison(&b.op) => b,
        _ => return None,
    };

    // Standard 2-level case: inner is a comparison.
    if let Expr::Binary(inner) = outer.left.as_ref() {
        if is_comparison(&inner.op) {
            let inner_b: Expr = (*inner.right).clone();
            let outer_left: Expr = (*outer.left).clone();
            let op2 = outer.op.clone();
            let outer_right: Expr = (*outer.right).clone();
            let new_right: Expr = verus_syn::parse_quote! { #inner_b #op2 #outer_right };
            return Some(verus_syn::parse_quote! { (#outer_left) && (#new_right) });
        }
    }

    // Longer chain case: the left side has already been rewritten to a
    // conjunction, e.g. `(0 <= i) && (i <= j)`. Walk to the rightmost
    // comparison RHS to use as the new chain pivot.
    if let Some(pivot) = rightmost_compare_rhs(&outer.left) {
        let outer_left: Expr = (*outer.left).clone();
        let op2 = outer.op.clone();
        let outer_right: Expr = (*outer.right).clone();
        let new_right: Expr = verus_syn::parse_quote! { #pivot #op2 #outer_right };
        return Some(verus_syn::parse_quote! { (#outer_left) && (#new_right) });
    }

    None
}

/// True if `expr` is `<receiver>.as_slice()` (no args). Used by the contract
/// rewriter to detect that an operand has already been lowered to a slice
/// form by a prior deep_view rewrite, so a parent `+` can route through
/// `__vcheck_seq_concat` instead of relying on a non-existent `Add` impl on
/// raw slices.
pub fn expr_is_slice_call(expr: &Expr) -> bool {
    if let Expr::MethodCall(mc) = expr {
        return mc.method == "as_slice" && mc.args.is_empty();
    }
    false
}

/// True when `expr` is a lifted spec-integer expression — a call into the
/// `::verus_spec_check::__vcheck_int::*` runtime module (produced when the contract
/// rewriter lifts spec `int`/`nat` arithmetic such as `old@.len() - 1`).
/// Such a value is a `SpecInt` (`num_bigint::BigInt`) at runtime, which
/// cannot be cast to `usize` with `as` — it must go through
/// `__vcheck_int::to_usize`.
pub fn expr_is_spec_int_call(expr: &Expr) -> bool {
    if let Expr::Call(c) = expr {
        if let Expr::Path(ExprPath { path, .. }) = c.func.as_ref() {
            return path.segments.iter().any(|s| s.ident == "__vcheck_int");
        }
    }
    false
}

/// Lower an expression used in an *index / subrange bound* position to a
/// `usize`. A lifted `SpecInt` (from spec arithmetic) is converted via
/// `__vcheck_int::to_usize` (an `as` cast on `BigInt` is invalid); any other
/// operand (a primitive from `i as int` after cast-stripping, a `.len()`
/// call, or an integer literal) keeps the cheap `as usize` cast.
pub fn lower_index_operand(idx: &Expr) -> TokenStream2 {
    if expr_is_spec_int_call(idx) {
        quote! { ::verus_spec_check::__vcheck_int::to_usize(#idx) }
    } else {
        quote! { (#idx) as usize }
    }
}

/// A `vec![...]` macro invocation — the lowered form of a `seq![...]`
/// literal (the `seq!`->`vec!` rename runs during child recursion). Used by
/// the sequence-concat detection so `seq![value] + old@` (the VecDeque
/// `push_front` front-insertion form) is recognized as a sequence `+`.
pub fn expr_is_vec_macro(expr: &Expr) -> bool {
    if let Expr::Macro(m) = expr {
        return m.mac.path.segments.len() == 1 && m.mac.path.segments[0].ident == "vec";
    }
    false
}

/// Either a `.as_slice()` projection or a `vec![...]` literal — i.e. an
/// operand of a Verus `Seq` `+` after child lowering.
pub fn expr_is_seq_operand(expr: &Expr) -> bool {
    expr_is_slice_call(expr) || expr_is_vec_macro(expr)
}

pub fn expr_is_ident(expr: &Expr, ident: &Ident) -> bool {
    if let Expr::Path(ExprPath {
        path, qself: None, ..
    }) = expr
    {
        if path.segments.len() == 1 {
            return &path.segments[0].ident == ident;
        }
    }
    false
}

pub fn return_ident_of(item_fn: &ItemFn) -> Option<Ident> {
    if let ReturnType::Type(_, _, output_pat, _) = &item_fn.sig.output {
        if let Some(boxed) = output_pat.as_ref() {
            return pat_to_ident(&boxed.1);
        }
    }
    None
}

pub fn pat_to_ident(pat: &Pat) -> Option<Ident> {
    match pat {
        Pat::Ident(pi) => Some(pi.ident.clone()),
        Pat::Type(PatType { pat, .. }) => pat_to_ident(pat),
        _ => None,
    }
}
