use super::*;

// ---------------------------------------------------------------------------
// Harness emission
// ---------------------------------------------------------------------------

pub struct HarnessOutput {
    /// The `proptest! { ... }` block.
    pub harness_tokens: TokenStream2,
    /// Synthetic spec fns this harness's clauses required.
    pub synthetic_spec_fns: Vec<TokenStream2>,
    /// Ensures clauses whose engagement antecedent could not be lowered.
    /// Coverage targets surface these as indeterminate instead of treating
    /// them as unconditionally engaged.
    pub unlowerable_ensures: Vec<(usize, &'static str)>,
}

#[derive(Clone, Debug)]
enum EnsuresEngagement {
    /// A non-implication clause constrains every execution.
    Always,
    /// A lowerable implication antecedent evaluated after the call.
    Predicate(TokenStream2),
    /// The clause may engage, but its antecedent has no runnable lowering.
    Unlowerable { reason: &'static str },
}

const INLINE_QUANTIFIER_ENGAGEMENT_REASON: &str =
    "inline quantified antecedent has no runtime engagement lowering";

fn mutable_return_snapshot_let(shape: &ReturnShape, binding: &Ident) -> TokenStream2 {
    match shape {
        ReturnShape::MutRefSlice(_) | ReturnShape::MutRefArray(_, _) => quote! {
            let #binding = #binding.to_vec();
        },
        ReturnShape::Tuple2(left, right)
            if matches!(
                left.as_ref(),
                ReturnShape::MutRefSlice(_) | ReturnShape::MutRefArray(_, _)
            ) && matches!(
                right.as_ref(),
                ReturnShape::MutRefSlice(_) | ReturnShape::MutRefArray(_, _)
            ) =>
        {
            quote! {
                let (__vcheck_return_left, __vcheck_return_right) = #binding;
                let #binding = (
                    __vcheck_return_left.to_vec(),
                    __vcheck_return_right.to_vec(),
                );
            }
        }
        _ => TokenStream2::new(),
    }
}

#[derive(Clone, Debug)]
struct StrengtheningProbe {
    suggestion: String,
    check: TokenStream2,
}

fn return_contains_mutable_slice(shape: &ReturnShape) -> bool {
    match shape {
        ReturnShape::MutRefSlice(_) | ReturnShape::MutRefArray(_, _) => true,
        ReturnShape::Tuple2(left, right) => {
            return_contains_mutable_slice(left) || return_contains_mutable_slice(right)
        }
        _ => false,
    }
}

fn return_is_mutable_slice_pair(shape: &ReturnShape) -> bool {
    matches!(
        shape,
        ReturnShape::Tuple2(left, right)
            if matches!(
                left.as_ref(),
                ReturnShape::MutRefSlice(_) | ReturnShape::MutRefArray(_, _)
            ) && matches!(
                right.as_ref(),
                ReturnShape::MutRefSlice(_) | ReturnShape::MutRefArray(_, _)
            )
    )
}

fn normalized_clause_text(expr: &Expr) -> String {
    quote!(#expr)
        .to_string()
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect()
}

fn build_strengthening_probes(
    param_idents: &[Ident],
    param_shapes: &[ParamShape],
    return_shape: &ReturnShape,
    result_binding: &Ident,
    ensures: &[Expr],
) -> Vec<StrengtheningProbe> {
    if !return_contains_mutable_slice(return_shape) {
        return Vec::new();
    }
    let source: Vec<String> = ensures.iter().map(normalized_clause_text).collect();
    let mut probes = Vec::new();
    let mutable_sequences: Vec<&Ident> = param_idents
        .iter()
        .zip(param_shapes)
        .filter_map(|(ident, shape)| match shape {
            ParamShape::MutRef(inner)
                if matches!(
                    inner.as_ref(),
                    ParamShape::OwnedVec(_) | ParamShape::Slice(_)
                ) =>
            {
                Some(ident)
            }
            _ => None,
        })
        .collect();

    for ident in &mutable_sequences {
        let compact_direct = format!("final({ident}).len()==old({ident}).len()");
        let compact_view = format!("final({ident})@==old({ident})@");
        if source
            .iter()
            .any(|clause| clause.contains(&compact_direct) || clause.contains(&compact_view))
        {
            continue;
        }
        let pre = format_ident!("__vcheck_pre_{}", ident);
        probes.push(StrengtheningProbe {
            suggestion: format!("final({ident}).len() == old({ident}).len()"),
            check: quote! { #ident.len() == #pre.len() },
        });
    }

    if return_is_mutable_slice_pair(return_shape) {
        if let Some(mid) = param_idents
            .iter()
            .zip(param_shapes)
            .find_map(|(ident, shape)| match shape {
                ParamShape::Primitive(ty)
                    if ident == "mid" && quote!(#ty).to_string() == "usize" =>
                {
                    Some(ident)
                }
                _ => None,
            })
        {
            let claimed = source.iter().any(|clause| {
                clause.contains(&format!("final({result_binding}.0)"))
                    && clause.contains(".len()")
                    && clause.contains(&mid.to_string())
            });
            if !claimed {
                probes.push(StrengtheningProbe {
                    suggestion: format!("final({result_binding}.0).len() == {mid}"),
                    check: quote! { #result_binding.0.len() == #mid },
                });
            }
        }
        for ident in mutable_sequences {
            let pre = format_ident!("__vcheck_pre_{}", ident);
            let claimed = source.iter().any(|clause| {
                clause.contains(&format!("final({result_binding}.0)"))
                    && clause.contains(&format!("final({result_binding}.1)"))
                    && clause.contains(&format!("old({ident})"))
                    && clause.contains(".len()")
            });
            if !claimed {
                probes.push(StrengtheningProbe {
                    suggestion: format!(
                        "final({result_binding}.0).len() + final({result_binding}.1).len() == old({ident}).len()"
                    ),
                    check: quote! {
                        #result_binding.0.len() + #result_binding.1.len() == #pre.len()
                    },
                });
            }
        }
    }
    probes
}

/// If `ty` is a single-segment path with a recognized ghost/permission wrapper
/// name (`Tracked`, `Ghost`, `Proof`), return the wrapper name so the harness
/// can refuse this parameter with an actionable error.
pub fn ghost_wrapper_name(ty: &Type) -> Option<&'static str> {
    let tp = match ty {
        Type::Path(tp) if tp.qself.is_none() => tp,
        // `&Tracked<...>` / `&mut Tracked<...>` etc.
        Type::Reference(r) => return ghost_wrapper_name(&r.elem),
        _ => return None,
    };
    if tp.path.segments.is_empty() {
        return None;
    }
    let seg = tp.path.segments.last().unwrap();
    match seg.ident.to_string().as_str() {
        "Tracked" => Some("Tracked"),
        "Ghost" => Some("Ghost"),
        "Proof" => Some("Proof"),
        _ => None,
    }
}

/// For a `ParamShape::OwnedVec(elem)` or `ParamShape::Slice(elem)`, build a
/// proptest element strategy producing the element type the harness samples
/// (the user's type for user-defined elements). Returns None for shapes that
/// aren't sized by a `len()` precondition.
pub fn element_strategy_for_shape(shape: &ParamShape) -> Option<TokenStream2> {
    // NOTE: `VecDeque` is deliberately absent. This helper only feeds the
    // fixed-length / array `Vec`-builder path; a `VecDeque` param there would
    // get a `Vec` builder and mismatch. Deque params instead use the
    // top-level `vcheck_strategy::<VecDeque<..>>()` generator, which already
    // edge-biases elements via the delegating `VcheckStrategy`/`VcheckGen` impls.
    let elem = match shape {
        ParamShape::OwnedVec(e) | ParamShape::Slice(e) => e,
        ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => e,
        ParamShape::MutRef(inner) => match inner.as_ref() {
            ParamShape::OwnedVec(e) | ParamShape::Slice(e) => e,
            ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => e,
            _ => return None,
        },
        _ => return None,
    };
    let elem_ty = match elem {
        ParamElem::Primitive(t) => quote! { #t },
        ParamElem::UserType(n) => quote! { #n },
    };
    Some(quote! { <#elem_ty as ::verus_spec_check::VcheckStrategy>::vcheck_strategy() })
}

/// Bolero analogue of [`element_strategy_for_shape`]. Returns
/// `Some((elem_ty, gen))` where `gen` is a `bolero_generator::ValueGenerator`
/// producing the element type (via its `VcheckGen` impl), and `elem_ty` is the
/// element type token (needed to spell the `Vec<elem_ty>` base for the
/// collection builder). Returns `None` for shapes that aren't `len()`-sized.
#[cfg_attr(not(test), allow(dead_code))]
pub fn element_gen_for_shape(shape: &ParamShape) -> Option<(TokenStream2, TokenStream2)> {
    let elem = match shape {
        // `VecDeque` deliberately absent — see `element_strategy_for_shape`.
        ParamShape::OwnedVec(e) | ParamShape::Slice(e) => e,
        ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => e,
        ParamShape::MutRef(inner) => match inner.as_ref() {
            ParamShape::OwnedVec(e) | ParamShape::Slice(e) => e,
            ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => e,
            _ => return None,
        },
        _ => return None,
    };
    let elem_ty = match elem {
        ParamElem::Primitive(t) => quote! { #t },
        ParamElem::UserType(n) => quote! { #n },
    };
    let gen = quote! { <#elem_ty as ::verus_spec_check::VcheckGen>::vcheck_gen() };
    Some((elem_ty, gen))
}

/// Scan a function's `requires` clauses for patterns of the shape
/// `<param>@.len() == <const>` (and the equivalent `<param>.deep_view().len()
/// == <const>`), returning a map from parameter name to the required length.
/// Handles either side of `==`. Used to pre-size collection strategies in the
/// harness so `prop_assume!` doesn't reject most samples.
pub fn scan_fixed_length_constraints(sig: &verus_syn::Signature) -> HashMap<String, usize> {
    use verus_syn::{BinOp, ExprBinary, ExprLit, Lit};
    let mut out: HashMap<String, usize> = HashMap::new();
    let Some(req) = &sig.spec.requires else {
        return out;
    };

    // Match `<param>@.len()` or `<param>.deep_view().len()`, returning the
    // param name. Conservative: bare ident only (no field access, no chained
    // method calls).
    fn extract_param_len(expr: &Expr) -> Option<String> {
        // Outer must be `.len()` with no args.
        let Expr::MethodCall(mc) = expr else {
            return None;
        };
        if mc.method != "len" || !mc.args.is_empty() {
            return None;
        }
        // Inner must be either `s@` (Expr::View) or `s.deep_view()`.
        match mc.receiver.as_ref() {
            Expr::View(v) => ident_of_expr(&v.expr),
            Expr::MethodCall(inner) if inner.method == "deep_view" && inner.args.is_empty() => {
                ident_of_expr(&inner.receiver)
            }
            _ => None,
        }
    }

    fn extract_usize_lit(expr: &Expr) -> Option<usize> {
        if let Expr::Lit(ExprLit {
            lit: Lit::Int(li), ..
        }) = expr
        {
            li.base10_parse::<usize>().ok()
        } else {
            None
        }
    }

    fn walk(e: &Expr, out: &mut HashMap<String, usize>) {
        match e {
            Expr::Binary(ExprBinary {
                op: BinOp::Eq(_),
                left,
                right,
                ..
            }) => {
                if let (Some(name), Some(n)) = (extract_param_len(left), extract_usize_lit(right)) {
                    out.entry(name).or_insert(n);
                }
                if let (Some(name), Some(n)) = (extract_param_len(right), extract_usize_lit(left)) {
                    out.entry(name).or_insert(n);
                }
            }
            Expr::Binary(ExprBinary {
                op: BinOp::And(_),
                left,
                right,
                ..
            }) => {
                walk(left, out);
                walk(right, out);
            }
            Expr::BigAnd(b) => {
                for inner in &b.exprs {
                    walk(&inner.expr, out);
                }
            }
            Expr::Paren(p) => walk(&p.expr, out),
            _ => {}
        }
    }

    for e in req.exprs.exprs.iter() {
        walk(e, &mut out);
    }
    out
}

/// Scan for usize-typed params whose precondition couples them to a
/// collection param's length: `i < s@.len()`, `i <= s@.len()`, etc.
/// Returns a map from the *index* param name to the maximum length the
/// strategy should sample. The "max length" comes from the engine's
/// collection bound (`DEFAULT_COLLECTION_MAX = 16`), so an index sampled
/// in `0..16` will satisfy `i < s.len()` for *some* sampled `s` — much
/// better than the default ~0% rate.
///
/// The bound is conservative: we sample the index up to the collection
/// max, then `prop_assume!` filters cases where the actually-sampled
/// collection happens to be shorter. Empirically this drops the reject rate
/// from ~100% to ~50% for the simple `i < s.len()` shape.
pub fn scan_index_bound_constraints(sig: &verus_syn::Signature) -> HashMap<String, usize> {
    use verus_syn::{BinOp, ExprBinary};
    let mut out: HashMap<String, usize> = HashMap::new();
    let Some(req) = &sig.spec.requires else {
        return out;
    };
    const DEFAULT_MAX: usize = 16;

    /// Returns the param name if `expr` is a bare ident (the index var).
    fn extract_param_name(expr: &Expr) -> Option<String> {
        ident_of_expr(expr)
    }

    /// Returns the unsigned integer value if `expr` is a literal integer
    /// (e.g. `4`, `4usize`). Used to recognise const-bound preconditions
    /// like `i < 4` for fixed-size array harnesses.
    fn extract_usize_literal(expr: &Expr) -> Option<usize> {
        if let Expr::Lit(verus_syn::ExprLit {
            lit: verus_syn::Lit::Int(li),
            ..
        }) = expr
        {
            return li.base10_parse::<usize>().ok();
        }
        None
    }

    /// True if `expr` is a `<x>@.len()` / `<x>.deep_view().len()` /
    /// `<x>.view().len()` / `<x>.len()` — anything that looks like a length
    /// call on a collection param.
    fn is_collection_len(expr: &Expr) -> bool {
        if let Expr::MethodCall(mc) = expr {
            if mc.method == "len" && mc.args.is_empty() {
                let receiver = mc.receiver.as_ref();
                if matches!(receiver, Expr::View(_)) {
                    return true;
                }
                if let Expr::MethodCall(inner) = receiver {
                    if (inner.method == "deep_view" || inner.method == "view")
                        && inner.args.is_empty()
                    {
                        return true;
                    }
                }
                if ident_of_expr(receiver).is_some() {
                    return true;
                }
            }
        }
        false
    }

    fn walk(e: &Expr, out: &mut HashMap<String, usize>) {
        match e {
            Expr::Binary(ExprBinary {
                op, left, right, ..
            }) => {
                let bound = match op {
                    BinOp::Lt(_) | BinOp::Le(_) => Some(DEFAULT_MAX),
                    _ => None,
                };
                if let Some(b) = bound {
                    if let Some(name) = extract_param_name(left) {
                        if is_collection_len(right) {
                            out.entry(name.clone()).or_insert(b);
                        }
                        // Literal upper-bound: `i < 4` or `i <= 4`. Cap the
                        // sampled range at the literal so prop_assume!
                        // doesn't reject. Strict `<` shrinks by one.
                        if let Some(lit) = extract_usize_literal(right) {
                            let cap = match op {
                                BinOp::Lt(_) => lit.saturating_sub(1),
                                _ => lit,
                            };
                            out.entry(name).or_insert(cap);
                        }
                    }
                    // Chained-compare shapes: `0 <= i < s.len()` parses as
                    // `(0 <= i) < s.len()`. Pattern-match the inner LHS (or
                    // deeper) to recover the index name. For longer chains
                    // (`0 <= i <= j < s.len()`) recurse into the left.
                    if let Some(rightmost) = rightmost_chain_param(left) {
                        if is_collection_len(right) {
                            out.entry(rightmost.clone()).or_insert(b);
                        }
                        if let Some(lit) = extract_usize_literal(right) {
                            let cap = match op {
                                BinOp::Lt(_) => lit.saturating_sub(1),
                                _ => lit,
                            };
                            out.entry(rightmost).or_insert(cap);
                        }
                    }
                    // Also recursively handle the LHS so e.g. `(0 <= i) <= j`
                    // contributes its inner relations to the map.
                    walk(left, out);
                }
                if matches!(op, BinOp::And(_)) {
                    walk(left, out);
                    walk(right, out);
                }
            }
            Expr::BigAnd(b) => {
                for inner in &b.exprs {
                    walk(&inner.expr, out);
                }
            }
            Expr::Paren(p) => walk(&p.expr, out),
            _ => {}
        }
    }

    /// Walk `<expr> <op> <expr>` where the chain is left-associative and
    /// return the rightmost ident in the chain. Used to extract the chain's
    /// trailing variable from arbitrarily deep nestings.
    fn rightmost_chain_param(e: &Expr) -> Option<String> {
        match e {
            Expr::Binary(b) => {
                if matches!(
                    b.op,
                    BinOp::Lt(_) | BinOp::Le(_) | BinOp::Gt(_) | BinOp::Ge(_)
                ) {
                    extract_param_name(&b.right)
                } else {
                    None
                }
            }
            Expr::Paren(p) => rightmost_chain_param(&p.expr),
            _ => None,
        }
    }

    /// Second pass: propagate bounds from already-mapped params to params
    /// that are bounded against them. Handles `i <= j` by giving `i` the
    /// same bound as `j` when `j` is in the map. Iterates to a fixed point.
    fn walk_transitive(e: &Expr, out: &mut HashMap<String, usize>) {
        fn walk_once(e: &Expr, out: &mut HashMap<String, usize>) -> bool {
            let mut changed = false;
            match e {
                Expr::Binary(ExprBinary {
                    op, left, right, ..
                }) => {
                    if matches!(op, BinOp::Lt(_) | BinOp::Le(_)) {
                        // Direct shape: `<lname> <op> <rname>`.
                        if let (Some(li), Some(ri)) =
                            (extract_param_name(left), extract_param_name(right))
                        {
                            if let Some(&b) = out.get(&ri) {
                                if !out.contains_key(&li) {
                                    out.insert(li, b);
                                    changed = true;
                                }
                            }
                        }
                        // Chained shape: `<inner> <op> <rname>` where inner
                        // is itself a comparison. Walk to the inner's
                        // rightmost ident and try to inherit from rname.
                        if let Some(inner_rightmost) = rightmost_chain_param(left) {
                            if let Some(ri) = extract_param_name(right) {
                                if let Some(&b) = out.get(&ri) {
                                    if !out.contains_key(&inner_rightmost) {
                                        out.insert(inner_rightmost, b);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                    if matches!(op, BinOp::And(_)) {
                        changed |= walk_once(left, out);
                        changed |= walk_once(right, out);
                    }
                    // Recurse into Lt/Le's left too — handles arbitrarily
                    // deep chains like `0 <= i <= j <= s.len()`.
                    if matches!(op, BinOp::Lt(_) | BinOp::Le(_)) {
                        changed |= walk_once(left, out);
                    }
                }
                Expr::BigAnd(b) => {
                    for inner in &b.exprs {
                        changed |= walk_once(&inner.expr, out);
                    }
                }
                Expr::Paren(p) => {
                    changed |= walk_once(&p.expr, out);
                }
                _ => {}
            }
            changed
        }
        loop {
            if !walk_once(e, out) {
                break;
            }
        }
    }

    for e in req.exprs.exprs.iter() {
        walk(e, &mut out);
    }
    // Second pass: propagate bounds through `<= other_param` chains.
    for e in req.exprs.exprs.iter() {
        walk_transitive(e, &mut out);
    }
    out
}

/// Controls which fn the emitted harness calls, and what kind of test
/// item it produces.
#[derive(Clone, Debug)]
pub enum HarnessFlavor {
    /// Standard `#[vcheck]` harness: a `proptest!` block that calls the
    /// original fn (`super::<fn>(...)` / `super::<Type>::<fn>(...)`).
    /// The harness is a `#[test]` and asserts `prop_assert!` on each
    /// ensures clause.
    Regular,
    /// Mutant runner for `#[vcheck_cov_mutate]`: a plain `fn() ->
    /// MutantOutcome` that runs an in-process proptest loop against
    /// `super::__vcheck_mutant_<k>_<orig>`. Returns `Killed` as soon as
    /// any input violates the post-condition; returns `Survived` if
    /// all inputs pass.
    MutantRunner {
        runner_name: Ident,
        mutant_call_fn: Ident,
        /// `true` if the mutant is a method on the enclosing impl
        /// type (vs a free fn). Carried through emit_harness so future
        /// phases (e.g. clause attribution) can route on this; the
        /// current emission path treats both the same way because
        /// emit_cov_mutate_block always emits the mutant as a free fn
        /// with a `self_value` positional parameter.
        #[allow(dead_code)]
        mutant_is_method: bool,
    },
    /// Coverage-guided runner for `#[vcheck_cov_fuzz]`: a plain `fn() ->
    /// CovFuzzRunStats` that drives byte-buffer inputs (decoded through
    /// the bolero generator stack) through the *instrumented twin*
    /// `super`-module fn, under an in-process coverage-guided search
    /// (`::verus_spec_check::cov_fuzz::coverage_guided_loop`). Differences from
    /// `MutantRunner`:
    ///   - inputs come from a `ByteSliceDriver`-driven bolero generator
    ///     (the byte buffer is the search genome), not proptest
    ///     strategies;
    ///   - `requires` clauses lower to skip-with-guidance: a satisfied
    ///     clause sets its per-clause guidance bit (feedback for the
    ///     search, NOT part of the reported statistic), a failed one
    ///     returns `ExecOutcome::Skipped`;
    ///   - ensures are NOT asserted — the regular `vcheck_<fn>` harness
    ///     owns contract checking. The runner does, however, evaluate
    ///     each ensures clause's ENGAGEMENT (implication antecedent
    ///     chain) after the call: arms reached by an execution at least
    ///     one clause engages on earn "covered" credit — the
    ///     spec-coverage statistic the report's threshold gates.
    CovFuzzRunner {
        /// Name of the emitted runner fn (`__vcheck_covfuzz_run_<fn>`).
        runner_name: Ident,
        /// The instrumented twin to call (`__vcheck_covfuzz_fn_<fn>`), a
        /// free fn at harness-module scope (methods get a `self_value`
        /// positional parameter, like mutant fns).
        twin_call_fn: Ident,
        /// Module-scope hit-bit static (`__VCHECK_COVF_HITS_<fn>`), included
        /// in the search's feedback set alongside the runner-local
        /// requires-guidance bits.
        hits_static: Ident,
        /// Module-scope spec-covered static (`__VCHECK_COVF_COVERED_<fn>`),
        /// parallel to the hit bits: arm i is set when a spec-ENGAGED
        /// execution reached it. Also part of the search feedback.
        covered_static: Ident,
        /// Module-scope per-execution indeterminate static
        /// (`__VCHECK_COVF_INDETERMINATE_<fn>`), parallel to the hit bits.
        /// Arm i is set when an execution reached it, no known clause
        /// engaged, and at least one clause had an unlowerable antecedent.
        indeterminate_static: Ident,
        /// Module-scope per-execution scratch (`__VCHECK_COVF_SCRATCH_<fn>`):
        /// cleared before each twin call, written by the marker alongside
        /// the cumulative hits, merged into `covered_static` when the
        /// execution turns out to be spec-engaged.
        scratch_static: Ident,
    },
    /// Engagement recorder + replay pair for an EXTERNAL
    /// (`assume_specification`) `#[vcheck_cov_fuzz]` target. Emits two
    /// items:
    ///
    ///   - `fn __vcheck_covext_record_<fn>() -> Vec<Vec<u8>>` — an
    ///     engagement-guided search run by the report in the OUTER
    ///     (uninstrumented) process: decodes byte genomes through the
    ///     wrapper's generator stack, filters through `requires` (with
    ///     guidance bits), calls the REAL external fn (free — no
    ///     coverage recorded outside the instrumented side build), and
    ///     evaluates each ensures clause's engagement with the result
    ///     in hand — result-dependent antecedents are exact. Per-clause
    ///     engagement bits join the search feedback so the loop hunts
    ///     inputs engaging EACH clause. Returns the engaged genomes.
    ///   - `#[test] fn __vcheck_covext_replay_<fn>()` — a no-op under
    ///     normal `cargo test`; inside the instrumented side build it
    ///     decodes the recorded genomes and calls the external fn once
    ///     per genome, so the llvm-cov profile reflects EXACTLY the
    ///     spec-engaged input set.
    CovExtRecorder {
        /// Name of the recorder fn (`__vcheck_covext_record_<fn>`).
        recorder_name: Ident,
        /// Name of the replay `#[test]` (`__vcheck_covext_replay_<fn>`).
        replay_test_name: Ident,
        /// Collision-safe registration identity used for replay selection.
        target_id: TokenStream2,
        /// Stable macro-time selector used to remove nonselected target
        /// calls from rescue side binaries before codegen.
        compile_selector: String,
    },
    /// Path-form `#[vcheck] assert(P)` checker. Emits a `proptest!`
    /// `#[test]` that drives the *checker fn* (a parallel clone of
    /// the enclosing fn whose targeted `assert(P)` has been rewritten
    /// to a panicking check). Differences from `Regular`:
    ///   - The body does NOT emit `prop_assert!` for ensures clauses
    ///     — the panic in the checker fn IS the failure signal.
    ///   - The body still emits `prop_assume!` for requires clauses
    ///     so unreachable inputs are filtered.
    ///   - The call routes to `checker_fn(<args>)` (a free fn at
    ///     module scope, like the mutant runner pattern).
    InlineAssertChecker {
        /// Name of the parallel fn (`__vcheck_assert_<idx>_<fn>`).
        checker_fn: Ident,
        /// Public name of the `#[test]` we emit (`__vcheck_assert_<fn>_at_lineN`).
        test_name: Ident,
        /// `true` if the enclosing fn is a method. The checker fn is
        /// always emitted as a free fn (with `self_value` positional
        /// arg), so this flag drives only the diagnostic message
        /// produced on failure — not the calling convention.
        #[allow(dead_code)]
        enclosing_is_method: bool,
    },
}

/// The emitted `#[test]` fn name for a contract target's regular
/// harness: `vcheck_<fn>` for free fns, `vcheck_<SelfTy>_<fn>` for methods.
/// Factored out because the kani report block needs the same names to
/// hand to `kani_orch::run_kani_report` (kani prints full module
/// paths ending in these).
pub fn vcheck_harness_name(target: &ContractTarget) -> String {
    match target {
        ContractTarget::Method {
            self_ty, method, ..
        } => {
            format!("vcheck_{}_{}", self_ty, method.sig.ident)
        }
        ContractTarget::FreeFn { item_fn, .. } => format!("vcheck_{}", item_fn.sig.ident),
    }
}

pub fn emit_harness(
    target: &ContractTarget,
    spec_fn_names: &HashSet<String>,
    user_types: &HashSet<String>,
    when_used_as_spec_redirect: &HashMap<String, String>,
    clause_counter: &mut u64,
) -> Result<HarnessOutput, Error> {
    emit_harness_with_flavor(
        target,
        spec_fn_names,
        user_types,
        when_used_as_spec_redirect,
        clause_counter,
        HarnessFlavor::Regular,
    )
}

pub fn emit_harness_with_flavor(
    target: &ContractTarget,
    spec_fn_names: &HashSet<String>,
    user_types: &HashSet<String>,
    when_used_as_spec_redirect: &HashMap<String, String>,
    clause_counter: &mut u64,
    flavor: HarnessFlavor,
) -> Result<HarnessOutput, Error> {
    // Pull out the bits that depend on free-fn vs method shape.
    let (sig, fn_name, is_method, self_ty_for_method): (
        &verus_syn::Signature,
        &Ident,
        bool,
        Option<Ident>,
    ) = match target {
        ContractTarget::FreeFn { item_fn, .. } => (&item_fn.sig, &item_fn.sig.ident, false, None),
        ContractTarget::Method {
            self_ty, method, ..
        } => (&method.sig, &method.sig.ident, true, Some(self_ty.clone())),
    };
    // `#[vcheck(miri = "skip")]` translates to a `#[cfg_attr(miri, ignore)]`
    // attribute on the emitted `#[test]` fn. Captured here so each
    // flavor's `quote!` block can splice it in front of `#[test]`.
    let miri_ignore_attr: TokenStream2 = if target.miri_skip() {
        quote! { #[cfg_attr(miri, ignore)] }
    } else {
        TokenStream2::new()
    };

    // Selected VCHECK backend for this target. The `Regular` flavor branches on
    // it to emit either the proptest harness or a bolero `check!` harness.
    let backend = target.backend();

    // `#[vcheck(mode = "kani")]` additionally marks the bolero harness as a kani
    // proof entry point via `#[cfg_attr(kani, kani::proof)]`. Under `cargo
    // test` this is inert (the fn stays a normal `#[test]` bolero harness on
    // the TestEngine); under kani (`cargo bolero test <t> --engine kani`, which
    // builds with `--cfg kani`) it promotes the fn to a `#[kani::proof]`
    // harness so `cargo kani --tests` discovers it — kani 0.67 does NOT
    // auto-treat `#[test]` fns as harnesses. `fuzz` mode carries no such attr
    // (the fuzz engines discover the plain `#[test]` harness directly).
    let kani_proof_attr: TokenStream2 = if matches!(
        target.bolero_mode(),
        Some(crate::vcheck_attr::VcheckBoleroMode::Kani)
    ) {
        quote! { #[cfg_attr(kani, kani::proof)] }
    } else {
        TokenStream2::new()
    };

    // 0. Reject ghost/tracked parameters early. Permission-passing methods
    // (`Tracked<&mut PointsTo<V>>`, `Ghost<...>`, etc.) have no runtime
    // representation: proptest can't sample one. Surface a clean diagnostic
    // pointing the user at the offending parameter rather than letting the
    // engine produce a confusing "unsupported type" error downstream.
    for p in &sig.inputs {
        if let FnArgKind::Typed(pat_type) = &p.kind {
            if let Some(wrapper) = ghost_wrapper_name(&pat_type.ty) {
                match tracked_points_to_resource(&pat_type.ty) {
                    Some((_, ResourceMode::Ref | ResourceMode::MutRef)) => continue,
                    Some((_, ResourceMode::Owned)) => {
                        return Err(Error::new_spanned(
                            &pat_type.ty,
                            "verus_spec_check: owned `Tracked<PointsTo<V>>` parameters are not \
supported yet",
                        ));
                    }
                    None => {}
                }
                return Err(Error::new_spanned(
                    &pat_type.ty,
                    format!(
                        "verus_spec_check: this parameter has type `{wrapper}<...>`, which carries \
ghost/permission state that doesn't exist at runtime. Property-based testing requires \
sample-able runtime values, so methods that take `Tracked<...>` / `Ghost<...>` / \
`Proof<...>` parameters can't be harnessed.\n\
\n\
Exception: `Tracked<&PointsTo<V>>` (paired with a `PPtr<V>` parameter) is materialized \
from a sampled memory model.\n\
\n\
If you want to test the runtime-observable behavior, factor it into a wrapper fn that \
takes only ordinary types and add `#[vcheck]` to that wrapper instead.",
                        wrapper = wrapper
                    ),
                ));
            }
        }
        // Tracked receivers (`tracked self` / `tracked &self`) — same
        // reasoning; Verus_syn carries this on the receiver's mode marker.
    }
    // Also reject ghost/tracked return types.
    if let ReturnType::Type(_, _, _, ty) = &sig.output {
        if let Some(wrapper) = ghost_wrapper_name(ty) {
            return Err(Error::new_spanned(
                ty,
                format!(
                    "verus_spec_check: this function returns `{wrapper}<...>`, which carries \
ghost/permission state that doesn't exist at runtime. Property-based testing requires \
the return value to be a sample-able runtime value.",
                    wrapper = wrapper
                ),
            ));
        }
    }

    let vcheck_fn_name = format_ident!("{}", vcheck_harness_name(target));

    // 1. Inspect parameters. Methods get a synthetic `self` ident bound
    // to the same shape as `&Self` (a `RefUserType`).
    let mut param_idents = Vec::new();
    let mut param_shapes = Vec::new();
    let mut self_ident: Option<Ident> = None;
    for p in &sig.inputs {
        match &p.kind {
            FnArgKind::Receiver(rcv) => {
                if !is_method {
                    return Err(Error::new_spanned(
                        p,
                        "verus_spec_check: free fns cannot have a `self` receiver",
                    ));
                }
                if rcv.reference.is_none() {
                    return Err(Error::new_spanned(
                        p,
                        "verus_spec_check: only `&self` and `&mut self` are supported (no owned `self`)",
                    ));
                }
                let is_mut = rcv.mutability.is_some();
                let self_ty = self_ty_for_method.as_ref().unwrap();
                // Recover the user-name (strip "Exec" if present). Whether or
                // not the type is defined in THIS block, we treat the self
                // receiver as a `RefUserType`: in-block types get a generated
                // strategy/converter here; external types resolve theirs by
                // trait across files (and surface the `on_unimplemented`
                // diagnostic if never `#[vcheck_provide]`'d).
                let user_name_str = self_ty.to_string();
                let canonical_user_name =
                    user_name_str.strip_prefix("Exec").unwrap_or(&user_name_str);
                let canonical_user_ident = Ident::new(canonical_user_name, self_ty.span());
                let synth_self = Ident::new("self_value", proc_macro2::Span::call_site());
                param_idents.push(synth_self.clone());
                let receiver_shape = if is_mut {
                    // `&mut self` -> wrap the user-type shape in MutRef so
                    // the harness samples an owned user value, snapshots
                    // its pre-state, and passes `&mut self_value` at the
                    // call site. Contracts mentioning `old(self)@` lower
                    // to `__vcheck_pre_self_value`'s deep_view; bare `self@`
                    // (or `final(self)@`) lowers to the post-call view.
                    ParamShape::MutRef(Box::new(ParamShape::OwnedUserType(canonical_user_ident)))
                } else {
                    ParamShape::RefUserType(canonical_user_ident)
                };
                param_shapes.push(receiver_shape);
                self_ident = Some(synth_self);
            }
            FnArgKind::Typed(pat_type) => {
                let ident = match pat_to_ident(&pat_type.pat) {
                    Some(id) => id,
                    // Permission params use the Verus unwrapping pattern
                    // `Tracked(perm): Tracked<&PointsTo<V>>`; the
                    // contract-visible ident is inside the tuple-struct
                    // pattern. Only accepted when the type actually
                    // classifies as a resource (checked in step 0).
                    None => match tracked_pat_inner_ident(&pat_type.pat) {
                        Some(id) if tracked_points_to_resource(&pat_type.ty).is_some() => id,
                        _ => {
                            return Err(Error::new_spanned(
                                &pat_type.pat,
                                "verus_spec_check: parameters must be simple `name: Type` patterns \
(or `Tracked(name): Tracked<&PointsTo<V>>` for permission parameters)",
                            ));
                        }
                    },
                };
                let mut owner_ty;
                let ty_for_classify: &Type = if let Some(self_ty) = self_ty_for_method.as_ref() {
                    owner_ty = (*pat_type.ty).clone();
                    replace_self_ty(&mut owner_ty, self_ty);
                    &owner_ty
                } else {
                    pat_type.ty.as_ref()
                };
                let shape = classify_param_type(ty_for_classify, user_types)?;
                param_idents.push(ident);
                param_shapes.push(shape);
            }
        }
    }

    let resource_models = pair_resource_params(&param_idents, &mut param_shapes)?;
    let resource_modes: HashMap<String, ResourceMode> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .filter_map(|(id, shape)| match shape {
            ParamShape::Resource { mode, .. } => Some((id.to_string(), *mode)),
            _ => None,
        })
        .collect();
    // Post-state observation plan for `&mut` permissions, filled by the
    // ensures pre-pass below and consumed by `post_call_bindings`.
    let mut resource_post_plan = ResourcePostPlan::default();

    // 2. Per-param call form for the rewriter.
    //
    // For each param we compute:
    //   - `param_call_form[id]`: how `<id>@` (or `<id>.deep_view()`)
    //     translates AT THE POST-CALL (or current) state. This is the
    //     normal deep_view form for non-mut params; for `&mut` params it's
    //     the *post-call* deep_view since the harness binding has been
    //     mutated by the real call.
    //   - `pre_view_for[id]`: how `old(<id>)@` translates. Only populated
    //     for `&mut` params; for owned/ref params there's no observable
    //     mutation, so the pre-state and post-state coincide and we leave
    //     this empty (and the rewriter resolves `old(<id>)` to bare `<id>`).
    //   - `user_typed_idents[id]`: the user-defined type name for params
    //     whose value is a sampled user type (drives the
    //     `<U as ToExecModel>::to_exec_model(&id)` insertion).
    //
    // Also: `mut_ref_param_idents` collects ParamShape::MutRef ids so we
    // can emit `let __vcheck_pre_<id> = <id>.clone();` snapshots before the
    // call.
    let mut param_call_form: HashMap<String, TokenStream2> = HashMap::new();
    let mut pre_view_for: HashMap<String, TokenStream2> = HashMap::new();
    let mut user_typed_idents: HashMap<String, Ident> = HashMap::new();
    let mut auto_borrow_idents: HashMap<String, TokenStream2> = HashMap::new();
    let mut map_set_shaped_idents: HashMap<String, MapSetKind> = HashMap::new();
    let mut sampled_pred_idents: HashSet<String> = HashSet::new();
    for (id, shape) in param_idents.iter().zip(param_shapes.iter()) {
        if matches!(shape, ParamShape::PredFn(_)) {
            sampled_pred_idents.insert(id.to_string());
        }
        param_call_form.insert(id.to_string(), shape.call_form_for_deep_view(id));
        if let Some(snap) = shape.pre_call_view_snapshot(id) {
            pre_view_for.insert(id.to_string(), snap);
        }
        // Reach into MutRef to find user-typed inner shapes.
        let inner_for_user_check: &ParamShape = match shape {
            ParamShape::MutRef(inner) => inner.as_ref(),
            other => other,
        };
        if let ParamShape::RefUserType(t) | ParamShape::OwnedUserType(t) = inner_for_user_check {
            user_typed_idents.insert(id.to_string(), t.clone());
        }
        // For shapes where the harness binding is owned but spec fns
        // typically take a borrow, register the borrow form so the
        // contract rewriter can auto-insert it. Reach through MutRef.
        let inner: &ParamShape = match shape {
            ParamShape::MutRef(i) => i.as_ref(),
            other => other,
        };
        match inner {
            ParamShape::OwnedString | ParamShape::RefStr => {
                // Both bind the harness value as an owned `String`. When
                // passed to a `&str`-taking spec fn (`f(s)`), borrow it:
                // `&String` deref-coerces to `&str`, matching the exec
                // companion's `&str` parameter. Without this a `&str` spec fn
                // argument reaches the companion as an owned `String`
                // ("expected `&str`, found `String`").
                auto_borrow_idents.insert(id.to_string(), quote! { &#id });
            }
            ParamShape::OwnedVec(_) => {
                // `Vec<T>` -> `&` for `&[T]`-taking spec fns (deref
                // coercion).
                auto_borrow_idents.insert(id.to_string(), quote! { &#id });
            }
            // `exec_*` spec-fn companions for these shapes take `&T` (see
            // `compile_type` in exec_spec.rs which lowers `Option<T>` /
            // `Result<T, E>` / `HashMap<K,V>` / `HashSet<T>` to
            // `&Option<T>` / etc. when used in spec-fn signatures). When
            // the harness has the param as an owned local (sampled by
            // proptest), the contract rewriter must auto-insert the `&`
            // borrow at the spec-fn callsite.
            ParamShape::OwnedOption(_) => {
                auto_borrow_idents.insert(id.to_string(), quote! { &#id });
            }
            ParamShape::OwnedResult(_, _) => {
                auto_borrow_idents.insert(id.to_string(), quote! { &#id });
            }
            ParamShape::OwnedHashMap(_, _) => {
                auto_borrow_idents.insert(id.to_string(), quote! { &#id });
            }
            ParamShape::OwnedHashSet(_) => {
                auto_borrow_idents.insert(id.to_string(), quote! { &#id });
            }
            ParamShape::OwnedBTreeMap(_, _) => {
                auto_borrow_idents.insert(id.to_string(), quote! { &#id });
            }
            ParamShape::OwnedBTreeSet(_) => {
                auto_borrow_idents.insert(id.to_string(), quote! { &#id });
            }
            _ => {}
        }
        // Track map/set-shaped idents (and their `&mut` pre-call snapshots)
        // so the rewriter routes their view-ops to the map/set companions.
        let kind = match inner {
            ParamShape::OwnedHashMap(_, _) => Some(MapSetKind::Map),
            ParamShape::OwnedHashSet(_) => Some(MapSetKind::Set),
            ParamShape::OwnedBTreeMap(_, _) => Some(MapSetKind::Map),
            ParamShape::OwnedBTreeSet(_) => Some(MapSetKind::Set),
            _ => None,
        };
        if let Some(k) = kind {
            map_set_shaped_idents.insert(id.to_string(), k);
            if matches!(shape, ParamShape::MutRef(_)) {
                map_set_shaped_idents.insert(format!("__vcheck_pre_{}", id), k);
            }
        }
    }
    let _ = &self_ident;

    // 3. Return shape and ident.
    let return_shape = classify_return(&sig.output, user_types, self_ty_for_method.as_ref())?;
    let return_ident = match target {
        ContractTarget::FreeFn { item_fn, .. } => return_ident_of(item_fn),
        ContractTarget::Method { method, .. } => {
            // ImplItemFn return signature follows the same shape; reuse the
            // helper by faking a temporary ItemFn-shaped accessor.
            if let ReturnType::Type(_, _, output_pat, _) = &method.sig.output {
                if let Some(boxed) = output_pat.as_ref() {
                    pat_to_ident(&boxed.1)
                } else {
                    None
                }
            } else {
                None
            }
        }
    };
    // Return identifiers participate in shape-aware Map/Set method lowering
    // just like parameters (`res@.map(...)`, `res@.contains(...)`, etc.).
    if let Some(id) = return_ident.as_ref() {
        let kind = match &return_shape {
            ReturnShape::OwnedHashMap | ReturnShape::OwnedBTreeMap => Some(MapSetKind::Map),
            ReturnShape::OwnedHashSet | ReturnShape::OwnedBTreeSet => Some(MapSetKind::Set),
            _ => None,
        };
        if let Some(kind) = kind {
            map_set_shaped_idents.insert(id.to_string(), kind);
        }
    }

    // 4. Build (name, spec_type) for synthetic-spec-fn signature use.
    let param_specs: Vec<(Ident, TokenStream2)> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| (id.clone(), shape.spec_type()))
        .collect();

    // 5. Process each requires/ensures clause.
    let mut synthetic_spec_fns: Vec<TokenStream2> = Vec::new();
    let mut rewritten_requires: Vec<TokenStream2> = Vec::new();
    let mut rewritten_ensures: Vec<TokenStream2> = Vec::new();

    let process_clause = |clause_expr: &Expr,
                          synthetic_spec_fns: &mut Vec<TokenStream2>,
                          counter: &mut u64|
     -> TokenStream2 {
        let mut clause_expr = clause_expr.clone();
        // For methods: rewrite `self` -> `<self_value>` before further
        // processing so the rewriter and quantifier-lift see ordinary idents.
        if let Some(self_id) = &self_ident {
            replace_self_with_ident(&mut clause_expr, self_id);
        }

        // Bounded-quantifier pre-pass for higher-order contracts: rewrite
        // `contains`-bounded forall/exists whose body mentions a sampled
        // predicate into runtime `.iter().cloned().all/any(..)` scans,
        // BEFORE the general quantifier lift (which would try to compile
        // the closure-typed pred through exec_spec and fail).
        if !sampled_pred_idents.is_empty() {
            rewrite_pred_bounded_quantifiers(&mut clause_expr, &sampled_pred_idents);
        }

        if contains_quantifier(&clause_expr) {
            let (synth, replacement) = lift_quantified_clause(
                &clause_expr,
                fn_name,
                counter,
                &param_specs,
                return_ident.as_ref(),
                &return_shape,
            );
            synthetic_spec_fns.push(synth);
            let mut replacement_expr: Expr =
                verus_syn::parse2(replacement).expect("synthetic clause must parse");
            let synth_name_str = if let Expr::Call(c) = &replacement_expr {
                if let Expr::Path(p) = c.func.as_ref() {
                    p.path.segments.last().map(|s| s.ident.to_string())
                } else {
                    None
                }
            } else {
                None
            };
            let mut combined_specs = spec_fn_names.clone();
            if let Some(n) = synth_name_str {
                combined_specs.insert(n);
            }
            let mut rw = ContractRewriter {
                spec_fn_names: &combined_specs,
                param_call_form: &param_call_form,
                pre_view_for: &pre_view_for,
                user_typed_idents: &user_typed_idents,
                auto_borrow_idents: &auto_borrow_idents,
                when_used_as_spec_redirect,
                map_set_shaped_idents: &map_set_shaped_idents,
                sampled_pred_idents: &sampled_pred_idents,
                return_ident: return_ident.clone(),
                return_shape: return_shape.clone(),
                spec_int_idents: HashSet::new(),
                spec_real_idents: HashSet::new(),
                int_returning_provided: int_returning_provided_registry(),
            };
            rw.visit_expr_mut(&mut replacement_expr);
            quote! { #replacement_expr }
        } else {
            let mut e = clause_expr;
            let mut rw = ContractRewriter {
                spec_fn_names,
                param_call_form: &param_call_form,
                pre_view_for: &pre_view_for,
                user_typed_idents: &user_typed_idents,
                auto_borrow_idents: &auto_borrow_idents,
                when_used_as_spec_redirect,
                map_set_shaped_idents: &map_set_shaped_idents,
                sampled_pred_idents: &sampled_pred_idents,
                return_ident: return_ident.clone(),
                return_shape: return_shape.clone(),
                spec_int_idents: HashSet::new(),
                spec_real_idents: HashSet::new(),
                int_returning_provided: int_returning_provided_registry(),
            };
            rw.visit_expr_mut(&mut e);
            quote! { #e }
        }
    };

    // Ensures clauses actually emitted (post pre-pass), paired with their
    // source exprs so the silent-no-op audit (5b) stays aligned when the
    // resource pre-pass drops unobservable clauses.
    let mut ensures_src_for_audit: Vec<Expr> = Vec::new();
    let mut skipped_unobservable_ensures = 0usize;

    // Per-ensures-clause ENGAGEMENT lowerings, parallel to
    // `rewritten_ensures`. An implication-shaped clause `A ==> B`
    // engages an execution iff its antecedent chain holds (for
    // right-nested chains `A ==> B ==> C`, iff `A && B`); a
    // non-implication clause engages every execution (it constrains all
    // of them). Unsupported antecedents remain explicitly `Unlowerable`:
    // treating them as always engaged would over-credit coverage.
    let mut ensures_engagement: Vec<EnsuresEngagement> = Vec::new();

    if let Some(req) = &sig.spec.requires {
        for e in req.exprs.exprs.iter() {
            let e = match rewrite_resource_clause(
                e,
                &resource_models,
                &resource_modes,
                false,
                &mut resource_post_plan,
            )? {
                ResourceClauseDisposition::Keep(e) => e,
                ResourceClauseDisposition::Skip | ResourceClauseDisposition::Directive => {
                    continue;
                }
            };
            let mut checked = e.clone();
            if let Some(self_id) = &self_ident {
                replace_self_with_ident(&mut checked, self_id);
            }
            check_clause_resolvable(
                &checked,
                spec_fn_names,
                &user_typed_idents,
                self_ident.as_ref(),
            )?;
            rewritten_requires.push(process_clause(&e, &mut synthetic_spec_fns, clause_counter));
        }
    }
    if let Some(ens) = &sig.spec.ensures {
        for e in ens.exprs.exprs.iter() {
            let rewritten = match rewrite_resource_clause(
                e,
                &resource_models,
                &resource_modes,
                true,
                &mut resource_post_plan,
            )? {
                ResourceClauseDisposition::Keep(e) => e,
                ResourceClauseDisposition::Skip => {
                    // Ghost bookkeeping (`final(perm).pptr() == ptr`):
                    // unobservable at runtime, dropped with a count so the
                    // all-skipped vacuity check below can fire.
                    skipped_unobservable_ensures += 1;
                    continue;
                }
                ResourceClauseDisposition::Directive => {
                    // Post-state tag: consumed as observation protocol
                    // (guard transition + read-back licensing), not
                    // asserted. Counts toward the vacuity check — a fn
                    // whose ONLY ensures are tags asserts nothing.
                    skipped_unobservable_ensures += 1;
                    continue;
                }
            };
            let mut checked = rewritten.clone();
            if let Some(self_id) = &self_ident {
                replace_self_with_ident(&mut checked, self_id);
            }
            check_clause_resolvable(
                &checked,
                spec_fn_names,
                &user_typed_idents,
                self_ident.as_ref(),
            )?;
            ensures_src_for_audit.push(e.clone());
            // Engagement antecedent (see the vec's docs above): split the
            // implication spine BEFORE the general lowering (which erases
            // `==>` into `!a || b`), then run the antecedent conjunction
            // through the same clause pipeline.
            //
            // A quantified antecedent (inline `forall`/`exists` LEFT of
            // the `==>`) degrades to always-engaged instead of being
            // lowered: the quantifier lift does not support that clause
            // shape today (the full-clause lowering rejects it at
            // compile time), and engagement must never turn a
            // compiling spec into a non-compiling one. Spec-fn
            // antecedents (`is_sorted(s) ==> ...`) — the idiomatic way
            // to write the same thing — lower exactly.
            match engagement_antecedent(&rewritten) {
                Err(reason) => {
                    ensures_engagement.push(EnsuresEngagement::Unlowerable { reason });
                }
                Ok(Some(ante)) => {
                    let lowered = process_clause(&ante, &mut synthetic_spec_fns, clause_counter);
                    ensures_engagement.push(EnsuresEngagement::Predicate(lowered));
                }
                Ok(None) => {
                    ensures_engagement.push(EnsuresEngagement::Always);
                }
            }
            rewritten_ensures.push(process_clause(
                &rewritten,
                &mut synthetic_spec_fns,
                clause_counter,
            ));
        }
    }

    // Vacuity guard for the resource pre-pass: if the fn HAS ensures
    // clauses but every one was dropped as unobservable ghost bookkeeping,
    // the harness would run the call and assert nothing — a silent no-op
    // in exactly the shape the 5b audit exists to prevent.
    if skipped_unobservable_ensures > 0 && rewritten_ensures.is_empty() {
        return Err(Error::new_spanned(
            fn_name,
            "verus_spec_check: every ensures clause of this fn projects only ghost \
handle-identity state (`pptr()` / `addr()`) or post-state tags, which the harness \
discharges by construction / consumes as observation directives.",
        ));
    }

    for name in &resource_post_plan.needs_post_value {
        if resource_post_plan.post_tag.get(name) == Some(&ResourcePostTag::Uninit) {
            return Err(Error::new_spanned(
                fn_name,
                format!(
                    "verus_spec_check: the ensures clauses project `final({name}).value()` but \
also claim `final({name}).is_uninit()` — there is no post-state value to read back \
from uninitialized memory."
                ),
            ));
        }
    }

    // Post-call bindings for `&mut` permissions: apply the contract's
    // classified state transition to the guard, then (when a
    // `final(perm).value()` clause needs it) recover the post-state
    // through the tier's certified move-out read. Spliced into the
    // harness bodies between the real call and the ensures assertions.
    let mut post_call_bindings: Vec<TokenStream2> = Vec::new();
    for (id, shape) in param_idents.iter().zip(param_shapes.iter()) {
        let ParamShape::Resource {
            value_ty,
            mode: ResourceMode::MutRef,
            tier,
            ..
        } = shape
        else {
            continue;
        };
        let name = id.to_string();
        let guard = resource_guard_ident(id);
        match resource_post_plan.post_tag.get(&name) {
            Some(ResourcePostTag::Init) => {
                post_call_bindings.push(quote! { #guard.mark_init(); });
            }
            Some(ResourcePostTag::Uninit) => {
                post_call_bindings.push(quote! { #guard.mark_uninit(); });
            }
            // No tag directive: the guard keeps the sampled pre-state tag
            // (frame heuristic). A wrong guess is Miri-visible (leak or
            // double-drop) rather than silent.
            None => {}
        }
        if resource_post_plan.needs_post_value.contains(&name) {
            let post_model = resource_post_model_ident(id);
            let v = crate::syntax::Vstd(id.span());
            let tier = tier.expect("tier set by pairing");
            let take_op = match tier {
                ResourceTier::Pptr => quote! {
                    |__vcheck_h: #v::simple_pptr::PPtr<#value_ty>| {
                        __vcheck_h.take(#v::prelude::Tracked::assume_new())
                    }
                },
                ResourceTier::Raw => quote! {
                    |__vcheck_h: *mut #value_ty| {
                        #v::raw_ptr::ptr_mut_read(
                            __vcheck_h,
                            #v::prelude::Tracked::assume_new(),
                        )
                    }
                },
            };
            post_call_bindings.push(quote! {
                let #post_model = #guard.read_back(#take_op);
            });
        }
    }

    // 5b. Audit the lowered ensures for silent-no-op patterns.
    //
    // The original `assume_specification` silent-drop bug (TASK 11 in
    // the project log) had a fingerprint that's easy to detect post-
    // lowering: the harness compiled, ran fast, and passed forever
    // because no real check made it into the body. Every subsequent
    // engine change risks reintroducing a similar shape, so we
    // statically inspect each rewritten ensures clause:
    //
    //   A1. **Empty / literal clause**: if the source had an ensures
    //       clause but the lowered form is empty or a bare boolean
    //       literal (`true`/`false`), the assertion is vacuous. Reject.
    //
    //   A3. **Tautological equality**: two flavors —
    //       (a) `<X> == <X>` where the two sides are syntactically
    //           identical (catches direct tautologies);
    //       (b) `__vcheck_ret == <call>` where `<call>` is syntactically
    //           identical to the *body* of the synthesized wrapper
    //           (catches the wrapping_<add|sub|mul> tautology where
    //           the spec body was lowered to the same intrinsic call
    //           that the wrapper makes — `__vcheck_ret` IS that call's
    //           return value, so the assertion is vacuous).
    //
    // These checks run only on ensures clauses. requires clauses can
    // legitimately be `true` (no constraint) or tautological (e.g.
    // `x == x` as a no-op precondition); they don't generate
    // pass/fail signal, just sampling guidance.
    //
    // The wrapper body is `target`'s `ItemFn`/`ImplItemFn` body. For an
    // `assume_specification` it's a single `Expr::Call` like
    // `<u8>::wrapping_add(x, y)`; we extract that single call and
    // compare it to the right-hand side of the rewritten `__vcheck_ret == X`.
    let wrapper_body_call: Option<TokenStream2> = extract_wrapper_body_call(target);
    // Zip against `ensures_src_for_audit` (NOT `ens.exprs.exprs`): the
    // resource pre-pass may have dropped unobservable clauses, and a
    // misaligned zip would audit clause i's lowering against clause j's
    // source.
    for (src_expr, rewritten) in ensures_src_for_audit.iter().zip(rewritten_ensures.iter()) {
        audit_rewritten_ensures(src_expr, rewritten, wrapper_body_call.as_ref())?;
    }

    // Does this contract reference the `real` domain? If so, its clauses may
    // hit an *unspecified* real operation (`÷0` or a non-finite float->real),
    // which Verus leaves unconstrained — the harness must SKIP such a case
    // rather than assert. We detect it from the rewritten clause tokens (the
    // rewriter emits `::verus_spec_check::__vcheck_real::*`) and, when present, wrap each
    // clause with `reset_defined()` / `is_defined()` guards. Non-real contracts
    // emit exactly as before (no behavior/shape change).
    let uses_real = rewritten_requires
        .iter()
        .chain(rewritten_ensures.iter())
        .any(|ts| ts.to_string().contains("__vcheck_real"));

    // Per-clause requires statements for the proptest `Regular` arm: a
    // `prop_assume!` (reject) normally; under `uses_real`, additionally skip
    // when the clause touched an unspecified real value.
    let proptest_requires_stmts: Vec<TokenStream2> = rewritten_requires
        .iter()
        .map(|r| {
            if uses_real {
                quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_req = { #r };
                    ::verus_spec_check::proptest::prop_assume!(
                        ::verus_spec_check::__vcheck_real::is_defined() && __vcheck_req,
                        "requires clause rejected"
                    );
                }}
            } else {
                quote! { ::verus_spec_check::proptest::prop_assume!(#r, "requires clause rejected"); }
            }
        })
        .collect();
    let proptest_ensures_stmts: Vec<TokenStream2> = rewritten_ensures
        .iter()
        .map(|e| {
            if uses_real {
                quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_ens = { #e };
                    if ::verus_spec_check::__vcheck_real::is_defined() {
                        ::verus_spec_check::proptest::prop_assert!(__vcheck_ens, "ensures clause failed");
                    }
                }}
            } else {
                quote! { ::verus_spec_check::proptest::prop_assert!(#e, "ensures clause failed"); }
            }
        })
        .collect();
    // Same, for the bolero `Regular` arm.
    //
    // `requires` handling is engine-dependent:
    //   - Under Kani (`--cfg kani`, set by `cargo bolero test --engine kani` /
    //     `cargo kani --tests`), a requires clause lowers to `kani::assume`,
    //     the native assumption form: the model checker constrains the
    //     symbolic input instead of discarding the execution path, so the
    //     proof covers the full constrained domain. (The `kani` crate is
    //     implicitly available in kani builds — bolero-kani relies on the
    //     same mechanism for `kani::cover!`.)
    //   - Under every other engine (cargo test random, libfuzzer/AFL/
    //     honggfuzz), bolero has no first-class `prop_assume!`, so a
    //     rejected input early-returns (skip). Each skip increments the
    //     harness's `__VCHECK_SKIPPED` counter so the post-run vacuity check
    //     (below) can fail loudly when a precondition rejected *every*
    //     sampled input instead of reporting a silent vacuous pass.
    //
    // Under a `real` contract, the unspecified-value guard keeps its skip
    // semantics on all engines (the thread-local defined-flag machinery has
    // no `assume` equivalent); only the skip counter is added.
    //
    // `ensures` -> `assert!` (a panic is the failure signal bolero shrinks
    // against) on all engines.
    let bolero_requires_stmts: Vec<TokenStream2> = rewritten_requires
        .iter()
        .map(|r| {
            if uses_real {
                quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_req = { #r };
                    if !(::verus_spec_check::__vcheck_real::is_defined() && __vcheck_req) {
                        #[cfg(not(kani))]
                        __VCHECK_SKIPPED.fetch_add(1, ::core::sync::atomic::Ordering::Relaxed);
                        return;
                    }
                }}
            } else {
                quote! {
                    #[cfg(kani)]
                    ::kani::assume({ #r });
                    #[cfg(not(kani))]
                    if !(#r) {
                        __VCHECK_SKIPPED.fetch_add(1, ::core::sync::atomic::Ordering::Relaxed);
                        return;
                    }
                }
            }
        })
        .collect();
    // Vacuity-detection scaffolding for the bolero arms. Only emitted when a
    // skip path exists (a `requires` clause or an unspecified-`real` guard);
    // harnesses without one are emitted exactly as before.
    //
    // The counters are function-local `static` atomics rather than closure
    // captures: the `for_each` closure then needs no environment, which
    // sidesteps engine-specific closure bounds (and `UnwindSafe` hazards)
    // entirely. Each harness fn owns its statics and runs once per process
    // under `cargo test`, so cross-run bleed isn't a concern. Under the
    // coverage-guided fuzz engines `for_each` never returns, so the post-run
    // check simply doesn't fire there — it is a `cargo test`-time guard.
    // Everything is cfg'd off under kani, where `requires` lowers to
    // `kani::assume` and rejection cannot occur.
    let bolero_has_skip_path = !rewritten_requires.is_empty() || uses_real;
    let (bolero_vacuity_statics, bolero_tested_incr, bolero_vacuity_check) = if bolero_has_skip_path
    {
        (
            quote! {
                #[cfg(not(kani))]
                static __VCHECK_TESTED: ::core::sync::atomic::AtomicU64 =
                    ::core::sync::atomic::AtomicU64::new(0);
                #[cfg(not(kani))]
                static __VCHECK_SKIPPED: ::core::sync::atomic::AtomicU64 =
                    ::core::sync::atomic::AtomicU64::new(0);
            },
            quote! {
                #[cfg(not(kani))]
                __VCHECK_TESTED.fetch_add(1, ::core::sync::atomic::Ordering::Relaxed);
            },
            quote! {
                #[cfg(not(kani))]
                {
                    let __vcheck_tested =
                        __VCHECK_TESTED.load(::core::sync::atomic::Ordering::Relaxed);
                    let __vcheck_skipped =
                        __VCHECK_SKIPPED.load(::core::sync::atomic::Ordering::Relaxed);
                    ::core::assert!(
                        !(__vcheck_tested == 0 && __vcheck_skipped > 0),
                        "verus_spec_check: vacuous bolero harness: all {} sampled inputs were \
            rejected by `requires` (or skipped as unspecified-`real` cases), so no contract check ever \
            ran. Narrow the input generator or run this contract on the proptest backend \
            (`mode = \"proptest\"`), whose reject tracking tolerates sparse preconditions.",
                        __vcheck_skipped
                    );
                }
            },
        )
    } else {
        (
            TokenStream2::new(),
            TokenStream2::new(),
            TokenStream2::new(),
        )
    };
    let bolero_ensures_stmts: Vec<TokenStream2> = rewritten_ensures
        .iter()
        .map(|e| {
            if uses_real {
                quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_ens = { #e };
                    if ::verus_spec_check::__vcheck_real::is_defined() {
                        ::core::assert!(__vcheck_ens, "ensures clause failed");
                    }
                }}
            } else {
                quote! { ::core::assert!(#e, "ensures clause failed"); }
            }
        })
        .collect();

    // 6. Build the proptest harness body.
    // Pre-scan the requires for fixed-length constraints on collection params.
    // Patterns like `s@.len() == 4` (or `s.deep_view().len() == 4`) are common
    // for binary parsing/serialization APIs and would otherwise cause proptest
    // to reject ~all sampled inputs (default Vec strategy is 0..=16).
    let fixed_lengths: HashMap<String, usize> = scan_fixed_length_constraints(sig);
    // Pre-scan for usize-typed params bounded by another collection's len
    // (e.g. `i < s@.len()`). Sample those in `0..=DEFAULT_MAX` so prop_assume
    // doesn't reject ~all samples.
    let index_bounds: HashMap<String, usize> = scan_index_bound_constraints(sig);
    // Sequence-shaped params (whose harness binding is a `Vec`/`VecDeque`)
    // bind through `::verus_spec_check::VcheckSeqSample`, whose `Debug` prints a
    // length-boundary ZST container as `[<zst>; <len>]` instead of walking
    // up to `usize::MAX` elements — proptest `Debug`-formats the failing
    // case, and that walk never terminates. The wrapper is destructured in
    // the binder pattern, so harness bodies see the plain container; for
    // sized element types the wrapper's `Debug` delegates to the
    // container's own, keeping failure output byte-identical.
    fn seq_sample_wrapped(shape: &ParamShape) -> bool {
        fn vecish(s: &ParamShape) -> bool {
            matches!(
                s,
                ParamShape::OwnedVec(_) | ParamShape::OwnedVecDeque(_) | ParamShape::Slice(_)
            )
        }
        match shape {
            ParamShape::MutRef(inner) => vecish(inner),
            s => vecish(s),
        }
    }
    // `<pattern> in <strategy>` decl, applying the `VcheckSeqSample` wrap
    // when requested (pattern-side destructure + `prop_map` on the
    // strategy side).
    fn finish_decl(lhs: TokenStream2, strategy: TokenStream2, wrap: bool) -> TokenStream2 {
        if wrap {
            quote! {
                ::verus_spec_check::VcheckSeqSample(#lhs) in
                    ::verus_spec_check::proptest::strategy::Strategy::prop_map(
                        #strategy,
                        ::verus_spec_check::VcheckSeqSample,
                    )
            }
        } else {
            quote! { #lhs in #strategy }
        }
    }
    let strategy_decls: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| {
            let ty = shape.harness_type();
            let wrap = seq_sample_wrapped(shape);
            // For `&mut`-shaped params we need to mutate the harness
            // binding through the call, so emit `mut <id>` on the
            // proptest decl. The same convention is fine for non-mut
            // params (an unused `mut` is a warning at most), but we keep
            // it scoped to actual mutation to minimize spurious warnings.
            let lhs_id: TokenStream2 = if matches!(shape, ParamShape::MutRef(_)) {
                quote! { mut #id }
            } else {
                quote! { #id }
            };
            // Handle params aren't sampled: bind a `()` placeholder that
            // the paired permission's pre-call binding shadows with
            // `guard.handle()`.
            if matches!(shape, ParamShape::ResourceHandle { .. }) {
                return quote! {
                    #lhs_id in ::verus_spec_check::proptest::strategy::Just(())
                };
            }
            // Fixed-size array params: sample a Vec<E> of exactly N
            // elements (the const expression in the array shape, after
            // const-generic substitution). This pre-empts the
            // fixed_lengths-driven path because the size is known
            // structurally rather than via a `requires` clause.
            //
            // Also matches `&mut [E; N]` (which classifies as
            // `MutRef(OwnedArray(E, N))`) so the sampler produces the
            // right-sized Vec before the harness materializes the array.
            let array_shape: Option<(&ParamElem, &Expr)> = match shape {
                ParamShape::OwnedArray(e, len) | ParamShape::RefArray(e, len) => {
                    Some((e, len))
                }
                ParamShape::MutRef(inner) => match inner.as_ref() {
                    ParamShape::OwnedArray(e, len) => Some((e, len)),
                    _ => None,
                },
                _ => None,
            };
            if let Some((_elem, len)) = array_shape {
                if let Some(elem_strategy) = element_strategy_for_shape(shape) {
                    return finish_decl(
                        lhs_id,
                        quote! {
                            ::verus_spec_check::proptest::collection::vec(#elem_strategy, (#len)..=(#len))
                        },
                        wrap,
                    );
                }
            }
            // For Vec<T> / Slice<T> params with a fixed-length precondition,
            // sample exactly that length so prop_assume! never rejects.
            if let Some(&len) = fixed_lengths.get(&id.to_string()) {
                if let Some(elem_strategy) = element_strategy_for_shape(shape) {
                    return finish_decl(
                        lhs_id,
                        quote! {
                            ::verus_spec_check::proptest::collection::vec(#elem_strategy, #len..=#len)
                        },
                        wrap,
                    );
                }
            }
            // For usize index params bounded by `< collection.len()` (or
            // `< <int-literal>`), sample in `0..=max` so a high fraction
            // of samples satisfy the precondition. The remaining
            // mismatches (where the actually sampled collection is
            // shorter) get filtered by prop_assume!.
            //
            // Gated on the param being typed `usize` — otherwise the
            // sampled `0..=max` value is the wrong type at the call
            // site (e.g. for `u32`-bounded params).
            if let Some(&max) = index_bounds.get(&id.to_string()) {
                if let ParamShape::Primitive(ty) = shape {
                    if quote!(#ty).to_string() == "usize" {
                        return quote! {
                            #lhs_id in (0usize..=#max)
                        };
                    }
                }
            }
            finish_decl(lhs_id, quote! { ::verus_spec_check::vcheck_strategy::<#ty>() }, wrap)
        })
        .collect();
    // Binder patterns matching `strategy_decls` element-for-element, for
    // flavors that drive `TestRunner::run` manually over a strategy tuple
    // (MutantRunner) instead of using `proptest!`'s `pat in strategy`
    // syntax. Wrapped params destructure `VcheckSeqSample` here too.
    let runner_bind_pats: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| {
            if seq_sample_wrapped(shape) {
                quote! { ::verus_spec_check::VcheckSeqSample(mut #id) }
            } else {
                quote! { mut #id }
            }
        })
        .collect();

    // Bolero backend: build the parallel per-param generator expressions
    // (bare, no `id in` binder) and the closure binding patterns. These
    // mirror `strategy_decls` above but target `bolero_generator`. Built
    // unconditionally (cheap token construction); only consumed by the
    // bolero arm of the `Regular` flavor. The proptest path is untouched.
    let bolero_gen_exprs: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| {
            let ty = shape.harness_type();
            // Handle params aren't sampled (see the proptest decl above).
            if matches!(shape, ParamShape::ResourceHandle { .. }) {
                return quote! { ::verus_spec_check::bolero_generator::constant(()) };
            }
            // Fixed-size array / fixed-length collection: sample a Vec of
            // exactly N elements from the element's VcheckGen generator. The
            // Vec<elem_ty> base satisfies bolero's collection builder bound;
            // `.values(..)` overrides element generation.
            let array_shape: Option<&Expr> = match shape {
                ParamShape::OwnedArray(_, len) | ParamShape::RefArray(_, len) => Some(len),
                ParamShape::MutRef(inner) => match inner.as_ref() {
                    ParamShape::OwnedArray(_, len) => Some(len),
                    _ => None,
                },
                _ => None,
            };
            if let Some(len) = array_shape {
                if let Some((elem_ty, elem_gen)) = element_gen_for_shape(shape) {
                    return quote! {
                        ::verus_spec_check::bolero_generator::prelude::produce::<::std::vec::Vec<#elem_ty>>()
                            .with().len((#len)..=(#len)).values(#elem_gen)
                    };
                }
            }
            if let Some(&len) = fixed_lengths.get(&id.to_string()) {
                if let Some((elem_ty, elem_gen)) = element_gen_for_shape(shape) {
                    return quote! {
                        ::verus_spec_check::bolero_generator::prelude::produce::<::std::vec::Vec<#elem_ty>>()
                            .with().len(#len..=#len).values(#elem_gen)
                    };
                }
            }
            // usize index param bounded by a collection len / int literal:
            // ranges are `ValueGenerator` in bolero, so the same `0..=max`
            // form used on the proptest side works verbatim.
            if let Some(&max) = index_bounds.get(&id.to_string()) {
                if let ParamShape::Primitive(pty) = shape {
                    if quote!(#pty).to_string() == "usize" {
                        return quote! { (0usize..=#max) };
                    }
                }
            }
            quote! { ::verus_spec_check::vcheck_gen::<#ty>() }
        })
        .collect();

    // Closure binding patterns for the bolero `for_each`, one per param,
    // carrying `mut` for `&mut`-shaped params (so `&mut #id` at the call
    // site is well-typed). Order matches `bolero_gen_exprs`.
    let bolero_bindings: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .map(|(id, shape)| {
            if matches!(shape, ParamShape::MutRef(_)) {
                quote! { mut #id }
            } else {
                quote! { #id }
            }
        })
        .collect();

    // The bolero `with_generator(..)` argument and the matching `for_each`
    // closure pattern. Shape adapts to param count: `()` for zero params,
    // the bare generator for one, and a tuple for many (sidesteps relying on
    // 1-tuple ValueGenerator support). Shared by the bolero arms of both the
    // Regular and InlineAssertChecker flavors.
    let (bolero_generator_expr, bolero_closure_pat): (TokenStream2, TokenStream2) =
        match bolero_gen_exprs.len() {
            0 => (
                quote! { ::verus_spec_check::bolero_generator::constant(()) },
                quote! { () },
            ),
            1 => {
                let g = &bolero_gen_exprs[0];
                let b = &bolero_bindings[0];
                (quote! { #g }, quote! { #b })
            }
            _ => (
                quote! { ( #(#bolero_gen_exprs),* ) },
                quote! { ( #(#bolero_bindings),* ) },
            ),
        };

    // Pre-call bindings: for shapes that need a stable storage location
    // (currently fixed-size arrays), emit a `let` before the call so the
    // borrow lives long enough.
    let mut pre_call_bindings: Vec<TokenStream2> = Vec::new();
    let mut prebinding_idents: Vec<Option<Ident>> = Vec::new();
    for (id, shape) in param_idents.iter().zip(param_shapes.iter()) {
        if let Some((bound, stmt)) = shape.pre_call_binding(id) {
            pre_call_bindings.push(stmt);
            prebinding_idents.push(Some(bound));
        } else {
            prebinding_idents.push(None);
        }
    }

    // Predicate priming pass. When an ensures clause constrains a sampled
    // predicate (via lowered `call_ensures` -> `models`), call the pred once
    // per element of every same-element-type container param BEFORE the fn
    // under test runs. Rationale: in Verus, positive `call_ensures` facts
    // arise only from actual calls — a caller who first probes the pred and
    // then invokes the fn under test is a legal program, and it is exactly
    // the program that exposes contracts over-assuming predicate
    // determinism (e.g. a biconditional `res <==> forall … call_ensures`).
    // For sound one-directional contracts priming is harmless: `models` is
    // trace-membership across both the priming calls and the real run.
    // Emitted after the `prop_assume!` requires-filters (alongside the
    // other pre-call bindings), so rejected samples never advance pred
    // state.
    {
        let ensures_text = rewritten_ensures
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join(" ");
        let mentions = |ident: &Ident| {
            let name = ident.to_string();
            ensures_text
                .split(|c: char| !c.is_alphanumeric() && c != '_')
                .any(|w| w == name)
        };
        for (pid, pshape) in param_idents.iter().zip(param_shapes.iter()) {
            let ParamShape::PredFn(pelem) = pshape else {
                continue;
            };
            if !mentions(pid) {
                continue;
            }
            let pred_elem_ty = pelem.harness_type().to_string();
            for (cid, cshape) in param_idents.iter().zip(param_shapes.iter()) {
                let inner = match cshape {
                    ParamShape::MutRef(i) => i.as_ref(),
                    other => other,
                };
                let celem = match inner {
                    ParamShape::OwnedVec(e)
                    | ParamShape::Slice(e)
                    | ParamShape::OwnedVecDeque(e)
                    | ParamShape::OwnedHashSet(e)
                    | ParamShape::OwnedBTreeSet(e) => Some(e),
                    _ => None,
                };
                let Some(ce) = celem else { continue };
                if ce.harness_type().to_string() != pred_elem_ty {
                    continue;
                }
                pre_call_bindings.push(quote! {
                    for __vcheck_prime_e in (#cid).iter() {
                        let _ = #pid.call(__vcheck_prime_e);
                    }
                });
            }
        }
    }

    // For each `&mut`-shaped param, snapshot the pre-call value so the
    // contract's `old(<id>)` references can read it after the call has
    // mutated `<id>`. Snapshot *before* any other pre-call binding so
    // the snapshot reflects the truly-original sampled value.
    let mut pre_state_lets: Vec<TokenStream2> = Vec::new();
    for (id, shape) in param_idents.iter().zip(param_shapes.iter()) {
        if let Some(stmt) = shape.pre_state_let(id) {
            pre_state_lets.push(stmt);
        }
    }

    // Harness arguments need to be `mut` for `&mut`-shaped params so
    // `&mut <id>` is well-typed. Walk the strategy decls and prepend
    // `mut ` where needed. We only have access to param idents here; the
    // strategy decls already emit `<id> in <strategy>` syntax — proptest
    // accepts a `mut` keyword on the binding.
    //
    // (Implemented inside the strategy decl construction below to keep
    // the normal-path emission clean.)

    let real_call_args: Vec<TokenStream2> = param_idents
        .iter()
        .zip(param_shapes.iter())
        .zip(prebinding_idents.iter())
        .map(|((id, shape), prebound)| shape.arg_with_optional_prebinding(id, prebound.as_ref()))
        .collect();

    let result_binding = return_ident
        .clone()
        .unwrap_or_else(|| Ident::new("__vcheck_result", Span::call_site()));
    let strengthening_probes = build_strengthening_probes(
        &param_idents,
        &param_shapes,
        &return_shape,
        &result_binding,
        &ensures_src_for_audit,
    );

    // Adapt the call to either `super::fn_name(...)` or
    // `super::Self::method(&self_value, ...)`. For methods the receiver is
    // already in `real_call_args[0]` (since we treat self as a ParamShape).
    //
    // For HarnessFlavor::MutantRunner the call routes through the
    // mutant's parallel fn instead of the original. The mutant fn lives
    // in the SAME harness module as the runner, so the path is bare
    // (no `super::`) — except for the `Type::method` shape, which still
    // resolves via the *parent* type, since mutant methods sit on a
    // separate impl block in the harness module's `super` scope.
    let real_call: TokenStream2 = match &flavor {
        HarnessFlavor::Regular => {
            if is_method {
                let self_ty = self_ty_for_method.as_ref().unwrap();
                quote! { super::#self_ty::#fn_name(#(#real_call_args),*) }
            } else {
                quote! { super::#fn_name(#(#real_call_args),*) }
            }
        }
        HarnessFlavor::MutantRunner {
            mutant_call_fn,
            mutant_is_method: _,
            ..
        } => {
            // The mutant fn always lives in the harness module
            // (emit_cov_mutate_block emits it as a free fn at module
            // scope, even for impl methods — the receiver is rewritten
            // to `self_value: &<Self>` / `&mut <Self>` / `<Self>`).
            // So the call is bare-ident regardless of method-ness.
            quote! { #mutant_call_fn(#(#real_call_args),*) }
        }
        HarnessFlavor::CovFuzzRunner { twin_call_fn, .. } => {
            // Like MutantRunner: the instrumented twin is a free fn at
            // harness-module scope regardless of method-ness.
            quote! { #twin_call_fn(#(#real_call_args),*) }
        }
        HarnessFlavor::CovExtRecorder { .. } => {
            // External targets are always free-fn assume wrappers; the
            // recorder/replay call the wrapper (which forwards to the
            // external path) like the Regular harness does.
            quote! { super::#fn_name(#(#real_call_args),*) }
        }
        HarnessFlavor::InlineAssertChecker { checker_fn, .. } => {
            // Like MutantRunner, the checker fn is emitted as a free
            // fn at module scope.
            quote! { #checker_fn(#(#real_call_args),*) }
        }
    };

    let return_snapshot_let = mutable_return_snapshot_let(&return_shape, &result_binding);
    let result_let = match &return_shape {
        ReturnShape::Unit => quote! {
            #real_call;
            let #result_binding: () = ();
            let _ = &#result_binding;
        },
        _ => quote! {
            let #result_binding = #real_call;
            #return_snapshot_let
        },
    };

    let harness_tokens = match &flavor {
        HarnessFlavor::Regular if matches!(backend, crate::vcheck_attr::VcheckBackend::Bolero) => {
            // Bolero backend for the regular harness. The same rewritten
            // requires/ensures clauses and pre-call bindings the proptest
            // arm uses are reused verbatim; only the wrapper differs:
            //   - generators come from `vcheck_gen::<T>()` (via `bolero_gen_exprs`);
            //   - `requires` lowers to an early `return` (skip) — bolero has
            //     no first-class `prop_assume!`, so a rejected input is a
            //     vacuous pass.
            //   - `ensures` lowers to `assert!` (a panic is the failure
            //     signal bolero shrinks against).
            //
            // The generator/closure shape (`bolero_generator_expr` /
            // `bolero_closure_pat`) is computed once above and shared with the
            // InlineAssertChecker bolero arm.
            let bolero_check_body = quote_spanned! { fn_name.span() =>
                // Vacuity counters (only present when a skip path
                // exists; see their construction above).
                #bolero_vacuity_statics
                ::verus_spec_check::bolero::check!()
                    .with_generator(#bolero_generator_expr)
                    .cloned()
                    .for_each(|#bolero_closure_pat| {
                        // Snapshot pre-call `&mut` state for `old(<id>)`.
                        #(#pre_state_lets)*
                        // requires -> `kani::assume` under Kani; skip +
                        // skip-counter under the other engines. Under a
                        // `real` contract these also skip an unspecified
                        // (÷0 / non-finite) case.
                        #(#bolero_requires_stmts)*
                        #bolero_tested_incr
                        #(#pre_call_bindings)*
                        #result_let
                        // `&mut` permission post-state: guard
                        // transitions + certified read-back.
                        #(#post_call_bindings)*
                        // ensures -> assert (skipping unspecified-real
                        // cases). The literal message avoids the
                        // `{`/`}`-in-cond format-string hazard.
                        #(#bolero_ensures_stmts)*
                    });
                // Fail loudly if every sampled input was rejected by
                // `requires` — a green run that never evaluated the
                // contract is worse than a red one.
                #bolero_vacuity_check
            };
            // `mode = "fuzz"` (and the legacy `backend = "bolero"` spelling,
            // which resolves to fuzz mode): the harness body is cfg-split.
            // Under the engine cfgs the `check!()` body above compiles in,
            // so `cargo bolero test` / kani behave exactly as before. Under
            // plain `cargo test` — where bolero would fall back to its
            // random TestEngine — an in-process coverage-guided loop runs
            // instead: an instrumented twin of the body provides branch
            // feedback, per-`requires`-clause guidance bits reward
            // precondition progress, and `ensures` violations (or body
            // panics) stop the search, shrink the byte genome, and report
            // the decoded counterexample. See `cov_fuzz::guided_contract_loop`.
            //
            // `mode = "kani"` keeps the plain `check!()` harness (its
            // cargo-test behavior stays a random smoke run).
            if matches!(
                target.bolero_mode(),
                Some(crate::vcheck_attr::VcheckBoleroMode::Fuzz)
            ) {
                emit_fuzz_mode_harness(FuzzModeHarnessInputs {
                    target,
                    fn_name,
                    vcheck_fn_name: &vcheck_fn_name,
                    miri_ignore_attr: &miri_ignore_attr,
                    bolero_check_body: &bolero_check_body,
                    bolero_generator_expr: &bolero_generator_expr,
                    bolero_closure_pat: &bolero_closure_pat,
                    rewritten_requires: &rewritten_requires,
                    rewritten_ensures: &rewritten_ensures,
                    ensures_src_for_audit: &ensures_src_for_audit,
                    uses_real,
                    pre_state_lets: &pre_state_lets,
                    pre_call_bindings: &pre_call_bindings,
                    post_call_bindings: &post_call_bindings,
                    real_call_args: &real_call_args,
                    return_shape: &return_shape,
                    result_binding: &result_binding,
                })
            } else {
                quote_spanned! { fn_name.span() =>
                    #kani_proof_attr
                    #[test]
                    #miri_ignore_attr
                    fn #vcheck_fn_name() {
                        #bolero_check_body
                    }
                }
            }
        }
        HarnessFlavor::Regular => {
            // proptest!'s zero-binder shape doesn't parse — its macro
            // requires `$($parm:pat in $strategy:expr),+` (one or more).
            // Inject a dummy `_: ()` binder so harnesses for zero-param
            // fns (e.g. `String::new()`) still emit a valid `proptest!`
            // invocation. The `()` strategy is a no-op sample.
            let strategy_decls_with_fallback: Vec<TokenStream2> = if strategy_decls.is_empty() {
                vec![quote! {
                    __vcheck_unused in ::verus_spec_check::proptest::strategy::Just(())
                }]
            } else {
                strategy_decls.clone()
            };
            quote_spanned! { fn_name.span() =>
                proptest! {
                    #![proptest_config(::verus_spec_check::proptest::test_runner::Config {
                        // Bump the global rejects ceiling so harnesses with
                        // multi-param relational preconditions (e.g.
                        // `mid <= slice.len()`) can still complete enough
                        // successful cases. proptest's default is 1024;
                        // a typical 50% reject rate at the default 256 cases
                        // run consumes ~256 rejects, so 65536 was plenty for
                        // the default. But when users raise PROPTEST_CASES
                        // (e.g. to 100000), the rejects scale linearly and
                        // 65536 runs out. We raise the engine default to
                        // 1_000_000 so most reasonable PROPTEST_CASES values
                        // (up to ~10000) work without env-var tuning. For
                        // higher case counts, set
                        // `PROPTEST_MAX_GLOBAL_REJECTS=N` (proptest applies
                        // env vars *after* this config struct, so the env
                        // var wins via `contextualize_config`).
                        max_global_rejects: 1_000_000,
                        ..::verus_spec_check::proptest::test_runner::Config::default()
                    })]

                    #[test]
                    #miri_ignore_attr
                    fn #vcheck_fn_name(
                        #(#strategy_decls_with_fallback),*
                    ) {
                        // Snapshot pre-call state for `&mut`-shaped params FIRST so
                        // both `requires` and `ensures` can reference `old(<id>)`.
                        #(#pre_state_lets)*
                        // Use the two-arg `prop_assume!` / `prop_assert!` forms
                        // with a literal format string so the cond's
                        // stringification (which may contain `{`/`}` from
                        // `if/else` blocks, struct/enum literals, etc.)
                        // doesn't get reinterpreted as `format!` placeholders.
                        // Under a `real` contract, clauses additionally skip an
                        // unspecified (÷0 / non-finite float->real) case.
                        #(#proptest_requires_stmts)*
                        #(#pre_call_bindings)*
                        #result_let
                        // `&mut` permission post-state: guard transitions +
                        // certified read-back.
                        #(#post_call_bindings)*
                        #(#proptest_ensures_stmts)*
                    }
                }
            }
        }
        HarnessFlavor::MutantRunner { runner_name, .. } => {
            // In-process mutant runner: returns `MutantOutcome::Killed` on
            // the first failed assertion, `MutantOutcome::Survived` if
            // every sample passed, `MutantOutcome::Inconclusive` if every
            // sample was rejected by `prop_assume!`.
            //
            // We build the `proptest::Strategy` value manually (one per
            // strategy decl) so we can drive it through
            // `TestRunner::run` without the `proptest!` macro's `#[test]`
            // wrapping.
            //
            // Each strategy decl is a `<id> in <strategy>` shape; we
            // collect the strategies into a tuple, run it, and unpack
            // the tuple in the body. The order of `#strategy_decls` is
            // deterministic, matching `param_idents`.
            //
            // The body of the inner closure mirrors the regular harness
            // body, but `prop_assume!` failures are converted into
            // `Inconclusive` (rather than rejected silently) via a
            // counter, and `prop_assert!` failures convert to `Killed`
            // by returning early.
            let strategy_exprs: Vec<TokenStream2> = strategy_decls
                .iter()
                .map(|decl| {
                    // Each decl looks like `id in <strategy>`. Extract
                    // the strategy expression by stripping the `id in `
                    // prefix at token level.
                    extract_strategy_expr(decl)
                })
                .collect();
            let bindings: Vec<&TokenStream2> = runner_bind_pats.iter().collect();
            quote_spanned! { fn_name.span() =>
                #[allow(non_snake_case, unused_variables, unused_mut, dead_code)]
                pub(super) fn #runner_name() -> ::verus_spec_check::cov_mutate::MutantOutcome {
                    use ::verus_spec_check::cov_mutate::MutantOutcome;
                    use ::verus_spec_check::proptest::test_runner::{Config, TestCaseError, TestRunner};
                    use ::verus_spec_check::proptest::strategy::Strategy;
                    let cfg = Config {
                        cases: 64,
                        max_global_rejects: 65536,
                        // Suppress proptest's persisted-failure file
                        // for mutant runs — we expect mutants to fail.
                        failure_persistence: None,
                        ..Config::default()
                    };
                    let mut runner = TestRunner::new(cfg);
                    let strategy = ( #( (#strategy_exprs) ,)* );
                    let killed = ::std::cell::Cell::new(false);
                    let assumed_at_least_once =
                        ::std::cell::Cell::new(false);
                    let run_result = runner.run(&strategy, |( #( #bindings , )* )| {
                        #(#pre_state_lets)*
                        // Pre-condition: skip if violated.
                        #(if !{ #rewritten_requires } {
                            return Err(TestCaseError::reject(
                                "pre-condition rejected",
                            ));
                        })*
                        assumed_at_least_once.set(true);
                        #(#pre_call_bindings)*
                        #result_let
                        #(#post_call_bindings)*
                        // Post-conditions: any failure kills the mutant.
                        #(if !{ #rewritten_ensures } {
                            killed.set(true);
                            return Err(TestCaseError::fail(
                                "ensures clause violated by mutant",
                            ));
                        })*
                        Ok(())
                    });
                    // The mutant is killed when:
                    //   (a) we explicitly set `killed` inside an ensures
                    //       check above, or
                    //   (b) `runner.run` returned Err for any other
                    //       reason — typically a panic in the mutant's
                    //       body (out-of-bounds index, integer
                    //       overflow, etc.). proptest's `catch_unwind`
                    //       turns those into TestCaseError::Fail, which
                    //       counts as a kill signal.
                    if killed.get() || run_result.is_err() {
                        MutantOutcome::Killed
                    } else if !assumed_at_least_once.get() {
                        MutantOutcome::Inconclusive
                    } else {
                        MutantOutcome::Survived
                    }
                }
            }
        }
        HarnessFlavor::CovFuzzRunner {
            runner_name,
            hits_static,
            covered_static,
            indeterminate_static,
            scratch_static,
            ..
        } => {
            // In-process coverage-guided runner for `#[vcheck_cov_fuzz]`.
            //
            // The byte buffer handed in by `coverage_guided_loop` is the
            // search genome: it decodes into the fn's parameter tuple
            // through the same bolero generator expressions the bolero
            // harness uses (`ByteSliceDriver` zero-fills past the end of
            // the buffer, so decoding is total in practice). `requires`
            // clauses filter inputs as usual, but additionally mark a
            // per-clause guidance bit when satisfied — that bit joins
            // the branch hit bits as search feedback, so the loop is
            // rewarded for progressing through the precondition even
            // before it ever reaches the body. Guidance bits are NOT in
            // the reported statistic (the report reads only
            // `#hits_static`, whose slots the instrumented twin marks).
            //
            // No ensures are asserted: contract checking belongs to the
            // regular `vcheck_<fn>` harness. A panic inside the twin is
            // caught and tallied by the loop (its arm hits stand in
            // `reached`, but earn no `covered` credit — engagement can't
            // be evaluated without a result).
            //
            // Engagement -> covered credit: the twin's markers write both
            // the cumulative hit bits and a per-execution scratch array
            // (cleared before each call). After the call, the engagement
            // disjunction over the ensures clauses is evaluated (each
            // implication clause contributes its antecedent chain;
            // non-implication clauses contribute `true`); when it holds,
            // scratch merges into the covered array. A fn with no
            // ensures clauses engages nothing — covered stays 0, which
            // is the honest reading of "the spec says nothing".
            let known_engagement_evals: Vec<TokenStream2> = ensures_engagement
                .iter()
                .filter_map(|engagement| match engagement {
                    EnsuresEngagement::Always => Some(quote! { true }),
                    EnsuresEngagement::Predicate(expr) if uses_real => Some(quote! {{
                        ::verus_spec_check::__vcheck_real::reset_defined();
                        let __vcheck_e = { #expr };
                        ::verus_spec_check::__vcheck_real::is_defined() && __vcheck_e
                    }}),
                    EnsuresEngagement::Predicate(expr) => Some(quote! { { #expr } }),
                    EnsuresEngagement::Unlowerable { .. } => None,
                })
                .collect();
            let has_unlowerable_engagement = ensures_engagement
                .iter()
                .any(|engagement| matches!(engagement, EnsuresEngagement::Unlowerable { .. }));
            let engaged_let = if known_engagement_evals.is_empty() {
                quote! { let __vcheck_engaged = false; }
            } else {
                quote! { let __vcheck_engaged = #( ( #known_engagement_evals ) )||*; }
            };
            let indeterminate_let = quote! {
                let __vcheck_engagement_indeterminate =
                    !__vcheck_engaged && #has_unlowerable_engagement;
            };
            let n_req = rewritten_requires.len();
            let requires_stmts: Vec<TokenStream2> = rewritten_requires
                .iter()
                .enumerate()
                .map(|(j, r)| {
                    if uses_real {
                        // Unspecified-real (÷0 / non-finite) cases skip,
                        // mirroring the other flavors' `real` handling.
                        quote! {{
                            ::verus_spec_check::__vcheck_real::reset_defined();
                            let __vcheck_req = { #r };
                            if ::verus_spec_check::__vcheck_real::is_defined() && __vcheck_req {
                                __VCHECK_COVF_GUIDE[#j].store(
                                    true, ::core::sync::atomic::Ordering::Relaxed);
                            } else {
                                return ::verus_spec_check::cov_fuzz::ExecOutcome::Skipped;
                            }
                        }}
                    } else {
                        quote! {
                            if { #r } {
                                __VCHECK_COVF_GUIDE[#j].store(
                                    true, ::core::sync::atomic::Ordering::Relaxed);
                            } else {
                                return ::verus_spec_check::cov_fuzz::ExecOutcome::Skipped;
                            }
                        }
                    }
                })
                .collect();
            let n_probes = strengthening_probes.len();
            let probe_stmts: Vec<TokenStream2> = strengthening_probes
                .iter()
                .enumerate()
                .map(|(index, probe)| {
                    let check = &probe.check;
                    quote! {
                        __vcheck_probe_checks[#index] += 1;
                        if !(#check) {
                            __vcheck_probe_violations[#index] += 1;
                        }
                    }
                })
                .collect();
            let probe_results: Vec<TokenStream2> = strengthening_probes
                .iter()
                .enumerate()
                .map(|(index, probe)| {
                    let suggestion = &probe.suggestion;
                    quote! {
                        ::verus_spec_check::cov_fuzz::CovFuzzProbeResult {
                            suggestion: #suggestion,
                            checks: __vcheck_probe_checks[#index],
                            violations: __vcheck_probe_violations[#index],
                        }
                    }
                })
                .collect();
            quote_spanned! { fn_name.span() =>
                #[allow(non_snake_case, unused_variables, unused_mut, dead_code)]
                pub(super) fn #runner_name() -> ::verus_spec_check::cov_fuzz::CovFuzzRunStats {
                    use ::verus_spec_check::bolero_generator::ValueGenerator;
                    // Per-requires-clause guidance bits (search feedback
                    // only; see flavor docs). Const-item repetition keeps
                    // the array init valid for non-Copy AtomicBool.
                    #[allow(clippy::declare_interior_mutable_const)]
                    const __VCHECK_COVF_FALSE: ::core::sync::atomic::AtomicBool =
                        ::core::sync::atomic::AtomicBool::new(false);
                    static __VCHECK_COVF_GUIDE:
                        [::core::sync::atomic::AtomicBool; #n_req] =
                        [__VCHECK_COVF_FALSE; #n_req];
                    static __VCHECK_COVF_RUN_LOCK: ::std::sync::Mutex<()> =
                        ::std::sync::Mutex::new(());
                    let _vcheck_run_guard = __VCHECK_COVF_RUN_LOCK
                        .lock()
                        .unwrap_or_else(|poisoned| poisoned.into_inner());
                    for __vcheck_bit in #hits_static.iter()
                        .chain(#covered_static.iter())
                        .chain(#indeterminate_static.iter())
                        .chain(#scratch_static.iter())
                        .chain(__VCHECK_COVF_GUIDE.iter())
                    {
                        __vcheck_bit.store(false, ::core::sync::atomic::Ordering::Relaxed);
                    }
                    let __vcheck_gen = #bolero_generator_expr;
                    let __vcheck_opts = ::core::default::Default::default();
                    let mut __vcheck_probe_checks = [0u64; #n_probes];
                    let mut __vcheck_probe_violations = [0u64; #n_probes];
                    let mut __vcheck_stats = ::verus_spec_check::cov_fuzz::coverage_guided_loop(
                        &[
                            &#hits_static[..],
                            &#covered_static[..],
                            &#indeterminate_static[..],
                            &__VCHECK_COVF_GUIDE[..],
                        ],
                        &mut |__vcheck_bytes: &[u8]| {
                            let mut __vcheck_driver =
                                ::verus_spec_check::bolero_generator::driver::ByteSliceDriver::new(
                                    __vcheck_bytes,
                                    &__vcheck_opts,
                                );
                            let ::core::option::Option::Some(#bolero_closure_pat) =
                                ValueGenerator::generate(&__vcheck_gen, &mut __vcheck_driver)
                            else {
                                return ::verus_spec_check::cov_fuzz::ExecOutcome::Invalid;
                            };
                            // Snapshot pre-call `&mut` state for `old(<id>)`.
                            #(#pre_state_lets)*
                            // requires -> guidance-bit mark or skip.
                            #(#requires_stmts)*
                            // Per-execution arm scratch: clear before the
                            // call (a prior panicked execution may have
                            // left bits behind).
                            for __vcheck_s in #scratch_static.iter() {
                                __vcheck_s.store(false, ::core::sync::atomic::Ordering::Relaxed);
                            }
                            #(#pre_call_bindings)*
                            #result_let
                            // `&mut` permission post-state transitions.
                            #(#post_call_bindings)*
                            // Non-failing strengthening observations run only
                            // after mutable return borrows have been snapshotted.
                            #(#probe_stmts)*
                            // Spec engagement: credit this execution's
                            // arms to `covered` iff at least one ensures
                            // clause speaks about it.
                            #engaged_let
                            #indeterminate_let
                            if __vcheck_engaged {
                                for (__vcheck_s, __vcheck_c) in
                                    #scratch_static.iter().zip(#covered_static.iter())
                                {
                                    if __vcheck_s.load(::core::sync::atomic::Ordering::Relaxed) {
                                        __vcheck_c.store(
                                            true,
                                            ::core::sync::atomic::Ordering::Relaxed,
                                        );
                                    }
                                }
                            } else if __vcheck_engagement_indeterminate {
                                for (__vcheck_s, __vcheck_i) in
                                    #scratch_static.iter().zip(#indeterminate_static.iter())
                                {
                                    if __vcheck_s.load(::core::sync::atomic::Ordering::Relaxed) {
                                        __vcheck_i.store(
                                            true,
                                            ::core::sync::atomic::Ordering::Relaxed,
                                        );
                                    }
                                }
                            }
                            let _ = &#result_binding;
                            ::verus_spec_check::cov_fuzz::ExecOutcome::Tested
                        },
                    );
                    __vcheck_stats.probes = ::std::vec![#(#probe_results),*];
                    __vcheck_stats
                }
            }
        }
        HarnessFlavor::CovExtRecorder {
            recorder_name,
            replay_test_name,
            target_id,
            compile_selector,
        } => {
            // Emitted by a standalone fn (not inline in this arm): the
            // big quote! temporaries would otherwise live in THIS
            // frame, which is on the stack during the deep clause-
            // rewriting recursion — inflating it past the 2 MiB test-
            // thread default on debug builds (same pattern as
            // `emit_fuzz_mode_harness`).
            emit_covext_recorder_harness(CovExtRecorderInputs {
                fn_name,
                recorder_name,
                replay_test_name,
                target_id,
                compile_selector,
                rewritten_requires: &rewritten_requires,
                ensures_engagement: &ensures_engagement,
                strengthening_probes: &strengthening_probes,
                uses_real,
                bolero_generator_expr: &bolero_generator_expr,
                bolero_closure_pat: &bolero_closure_pat,
                pre_state_lets: &pre_state_lets,
                pre_call_bindings: &pre_call_bindings,
                post_call_bindings: &post_call_bindings,
                result_let: &result_let,
                result_binding: &result_binding,
            })
        }
        HarnessFlavor::InlineAssertChecker { test_name, .. }
            if matches!(backend, crate::vcheck_attr::VcheckBackend::Bolero) =>
        {
            // Bolero variant of the inline-assert checker. Drives the parallel
            // checker fn (whose targeted `assert(P)` was rewritten to a
            // panicking check) with the enclosing fn's bolero generators. A
            // failed assert panics; bolero catches it, shrinks, and reports.
            //
            // Same shape as the Regular bolero arm minus the ensures asserts:
            //   - `requires` -> `kani::assume` under Kani; skip + skip-counter
            //     under the other engines (shared `bolero_requires_stmts`),
            //     with the same post-run vacuity check;
            //   - ensures are OMITTED (the panic in the checker is the signal);
            //   - the result binding is unused.
            quote_spanned! { fn_name.span() =>
                #kani_proof_attr
                #[test]
                #miri_ignore_attr
                fn #test_name() {
                    #bolero_vacuity_statics
                    ::verus_spec_check::bolero::check!()
                        .with_generator(#bolero_generator_expr)
                        .cloned()
                        .for_each(|#bolero_closure_pat| {
                            #(#pre_state_lets)*
                            #(#bolero_requires_stmts)*
                            #bolero_tested_incr
                            #(#pre_call_bindings)*
                            #result_let
                            // Guard transitions keep `&mut` permission
                            // teardown sound even though this flavor
                            // asserts no ensures.
                            #(#post_call_bindings)*
                            let _ = &#result_binding;
                        });
                    #bolero_vacuity_check
                }
            }
        }
        HarnessFlavor::InlineAssertChecker { test_name, .. } => {
            // Inline-assert checker: drive the parallel checker fn
            // (which has the targeted assert rewritten to a panicking
            // check) with the enclosing fn's strategies. The checker
            // fn panics when the assert fails; proptest catches the
            // panic, shrinks, and reports the counterexample.
            //
            // Differences from `Regular`:
            //   - `prop_assert!` for ensures clauses is OMITTED.
            //     The contract's ensures clause is still meaningful
            //     for SMT, but the test harness here is checking the
            //     inline assert, not the ensures clause.
            //   - `prop_assume!` for requires clauses IS kept. The
            //     enclosing fn's preconditions still gate the
            //     checker fn's input space.
            //   - The result binding is unused (`_`) since we don't
            //     check ensures.
            quote_spanned! { fn_name.span() =>
                proptest! {
                    #![proptest_config(::verus_spec_check::proptest::test_runner::Config {
                        // See comment on the regular harness path for
                        // why we set this to 1_000_000 (covers high
                        // PROPTEST_CASES without env-var tuning).
                        max_global_rejects: 1_000_000,
                        ..::verus_spec_check::proptest::test_runner::Config::default()
                    })]

                    #[test]
                    #miri_ignore_attr
                    fn #test_name(
                        #(#strategy_decls),*
                    ) {
                        #(#pre_state_lets)*
                        #(::verus_spec_check::proptest::prop_assume!(#rewritten_requires, "requires clause rejected");)*
                        #(#pre_call_bindings)*
                        #result_let
                        // Guard transitions keep `&mut` permission
                        // teardown sound even though this flavor asserts
                        // no ensures.
                        #(#post_call_bindings)*
                        let _ = &#result_binding;
                    }
                }
            }
        }
    };

    let unlowerable_ensures: Vec<(usize, &'static str)> = ensures_engagement
        .iter()
        .enumerate()
        .filter_map(|(clause, engagement)| match engagement {
            EnsuresEngagement::Unlowerable { reason } => Some((clause, *reason)),
            EnsuresEngagement::Always | EnsuresEngagement::Predicate(_) => None,
        })
        .collect();

    Ok(HarnessOutput {
        harness_tokens,
        synthetic_spec_fns,
        unlowerable_ensures,
    })
}

/// Inputs for [`emit_covext_recorder_harness`] — the CovExtRecorder
/// flavor's emission, hoisted out of `emit_harness_with_flavor`'s frame
/// (see the arm's comment for why).
struct CovExtRecorderInputs<'a> {
    fn_name: &'a Ident,
    recorder_name: &'a Ident,
    replay_test_name: &'a Ident,
    target_id: &'a TokenStream2,
    compile_selector: &'a str,
    rewritten_requires: &'a [TokenStream2],
    ensures_engagement: &'a [EnsuresEngagement],
    strengthening_probes: &'a [StrengtheningProbe],
    uses_real: bool,
    bolero_generator_expr: &'a TokenStream2,
    bolero_closure_pat: &'a TokenStream2,
    pre_state_lets: &'a [TokenStream2],
    pre_call_bindings: &'a [TokenStream2],
    post_call_bindings: &'a [TokenStream2],
    result_let: &'a TokenStream2,
    result_binding: &'a Ident,
}

/// Emit the engagement recorder fn + replay `#[test]` for an EXTERNAL
/// `#[vcheck_cov_fuzz]` target (see the `CovExtRecorder` flavor docs).
fn emit_covext_recorder_harness(inputs: CovExtRecorderInputs<'_>) -> TokenStream2 {
    let CovExtRecorderInputs {
        fn_name,
        recorder_name,
        replay_test_name,
        target_id,
        compile_selector,
        rewritten_requires,
        ensures_engagement,
        strengthening_probes,
        uses_real,
        bolero_generator_expr,
        bolero_closure_pat,
        pre_state_lets,
        pre_call_bindings,
        post_call_bindings,
        result_let,
        result_binding,
    } = inputs;
    // Requires lower to guidance-bit mark or skip (like CovFuzzRunner);
    // each ensures clause gets an engagement bit evaluated POST-call
    // with the real result.
    let n_req = rewritten_requires.len();
    let recorder_requires_stmts: Vec<TokenStream2> = rewritten_requires
        .iter()
        .enumerate()
        .map(|(j, r)| {
            if uses_real {
                quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_req = { #r };
                    if ::verus_spec_check::__vcheck_real::is_defined() && __vcheck_req {
                        __VCHECK_COVEXT_GUIDE[#j].store(
                            true, ::core::sync::atomic::Ordering::Relaxed);
                    } else {
                        return ::verus_spec_check::cov_fuzz::RecordOutcome::Skipped;
                    }
                }}
            } else {
                quote! {
                    if { #r } {
                        __VCHECK_COVEXT_GUIDE[#j].store(
                            true, ::core::sync::atomic::Ordering::Relaxed);
                    } else {
                        return ::verus_spec_check::cov_fuzz::RecordOutcome::Skipped;
                    }
                }
            }
        })
        .collect();
    // Replay re-checks requires without guidance bits (decode is
    // deterministic so recorded genomes should always pass; the guard
    // is cheap insurance against drift).
    let replay_requires_stmts: Vec<TokenStream2> = rewritten_requires
        .iter()
        .map(|r| {
            if uses_real {
                quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_req = { #r };
                    if !(::verus_spec_check::__vcheck_real::is_defined() && __vcheck_req) {
                        panic!("cov_fuzz replay drift: recorded genome no longer satisfies requires");
                    }
                }}
            } else {
                quote! {
                    if !{ #r } {
                        panic!("cov_fuzz replay drift: recorded genome no longer satisfies requires");
                    }
                }
            }
        })
        .collect();
    // Per-clause engagement: bit j lights when clause j engages
    // (feedback steers the search toward each clause's domain); the
    // overall flag decides whether the genome is saved.
    let n_ens = ensures_engagement.len();
    let engagement_stmts: Vec<TokenStream2> = ensures_engagement
        .iter()
        .enumerate()
        .map(|(j, engagement)| {
            let eval = match engagement {
                EnsuresEngagement::Always => Some(quote! { true }),
                EnsuresEngagement::Predicate(expr) if uses_real => Some(quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_e = { #expr };
                    ::verus_spec_check::__vcheck_real::is_defined() && __vcheck_e
                }}),
                EnsuresEngagement::Predicate(expr) => Some(quote! { { #expr } }),
                EnsuresEngagement::Unlowerable { .. } => None,
            };
            match eval {
                Some(eval) => quote! {
                    if #eval {
                        __VCHECK_COVEXT_ENGAGE[#j].store(
                            true, ::core::sync::atomic::Ordering::Relaxed);
                        __vcheck_clauses.set(#j);
                    }
                },
                None => TokenStream2::new(),
            }
        })
        .collect();
    let unlowerable_entries: Vec<TokenStream2> = ensures_engagement
        .iter()
        .enumerate()
        .filter_map(|(clause, engagement)| match engagement {
            EnsuresEngagement::Unlowerable { reason } => Some(quote! {
                ::verus_spec_check::cov_fuzz::VcheckCovFuzzUnlowerableClause {
                    clause: #clause,
                    reason: #reason,
                }
            }),
            EnsuresEngagement::Always | EnsuresEngagement::Predicate(_) => None,
        })
        .collect();
    let n_probes = strengthening_probes.len();
    let probe_stmts: Vec<TokenStream2> = strengthening_probes
        .iter()
        .enumerate()
        .map(|(index, probe)| {
            let check = &probe.check;
            quote! {
                __vcheck_probe_checks[#index] += 1;
                if !(#check) {
                    __vcheck_probe_violations[#index] += 1;
                }
            }
        })
        .collect();
    let probe_results: Vec<TokenStream2> = strengthening_probes
        .iter()
        .enumerate()
        .map(|(index, probe)| {
            let suggestion = &probe.suggestion;
            quote! {
                ::verus_spec_check::cov_fuzz::CovFuzzProbeResult {
                    suggestion: #suggestion,
                    checks: __vcheck_probe_checks[#index],
                    violations: __vcheck_probe_violations[#index],
                }
            }
        })
        .collect();
    quote_spanned! { fn_name.span() =>
        #[allow(non_snake_case, unused_variables, unused_mut, dead_code)]
        pub(super) fn #recorder_name() -> ::verus_spec_check::cov_fuzz::CovExtRecording {
            use ::verus_spec_check::bolero_generator::ValueGenerator;
            #[allow(clippy::declare_interior_mutable_const)]
            const __VCHECK_COVEXT_FALSE: ::core::sync::atomic::AtomicBool =
                ::core::sync::atomic::AtomicBool::new(false);
            static __VCHECK_COVEXT_GUIDE:
                [::core::sync::atomic::AtomicBool; #n_req] =
                [__VCHECK_COVEXT_FALSE; #n_req];
            static __VCHECK_COVEXT_ENGAGE:
                [::core::sync::atomic::AtomicBool; #n_ens] =
                [__VCHECK_COVEXT_FALSE; #n_ens];
            for __vcheck_bit in __VCHECK_COVEXT_GUIDE.iter().chain(__VCHECK_COVEXT_ENGAGE.iter()) {
                __vcheck_bit.store(false, ::core::sync::atomic::Ordering::Relaxed);
            }
            let __vcheck_gen = #bolero_generator_expr;
            let __vcheck_opts = ::core::default::Default::default();
            let mut __vcheck_probe_checks = [0u64; #n_probes];
            let mut __vcheck_probe_violations = [0u64; #n_probes];
            let mut __vcheck_recording = ::verus_spec_check::cov_fuzz::covext_record_loop(
                &[&__VCHECK_COVEXT_GUIDE[..], &__VCHECK_COVEXT_ENGAGE[..]],
                #n_ens,
                &mut |__vcheck_bytes: &[u8]| {
                    let mut __vcheck_driver =
                        ::verus_spec_check::bolero_generator::driver::ByteSliceDriver::new(
                            __vcheck_bytes,
                            &__vcheck_opts,
                        );
                    let ::core::option::Option::Some(#bolero_closure_pat) =
                        ValueGenerator::generate(&__vcheck_gen, &mut __vcheck_driver)
                    else {
                        return ::verus_spec_check::cov_fuzz::RecordOutcome::Invalid;
                    };
                    #(#pre_state_lets)*
                    #(#recorder_requires_stmts)*
                    #(#pre_call_bindings)*
                    #result_let
                    #(#post_call_bindings)*
                    #(#probe_stmts)*
                    let mut __vcheck_clauses =
                        ::verus_spec_check::cov_fuzz::ClauseMask::new(#n_ens);
                    #(#engagement_stmts)*
                    let _ = &#result_binding;
                    ::verus_spec_check::cov_fuzz::RecordOutcome::Tested {
                        clauses: __vcheck_clauses,
                    }
                },
            );
            __vcheck_recording.unlowerable_clauses =
                ::std::vec![#(#unlowerable_entries),*];
            __vcheck_recording.probes = ::std::vec![#(#probe_results),*];
            __vcheck_recording
        }

        #[test]
        #[cfg_attr(miri, ignore)]
        #[allow(non_snake_case, unused_variables, unused_mut)]
        fn #replay_test_name() {
            use ::verus_spec_check::bolero_generator::ValueGenerator;
            // Rescue-shard gating, resolved at COMPILE time: when the side
            // build sets VERUS_SPEC_CHECK_COVEXT_RESCUE_SELECTORS, targets absent
            // from the list compile to this early return — their call to
            // the external target is removed before codegen, so the rescue
            // binary's coverage map stays small enough for llvm-cov export.
            // Cargo tracks option_env! as a build input, so changing the
            // selector list recompiles only this crate, not build-std deps.
            const __VCHECK_RESCUE_SELECTED: bool =
                match ::core::option_env!("VERUS_SPEC_CHECK_COVEXT_RESCUE_SELECTORS") {
                    ::core::option::Option::None => true,
                    ::core::option::Option::Some(list) =>
                        ::verus_spec_check::cov_fuzz::covext_rescue_selector_enabled(
                            list,
                            #compile_selector,
                        ),
                };
            if !__VCHECK_RESCUE_SELECTED {
                return;
            }
            // No-op outside the selected instrumented side-profile run;
            // selected runs fail closed on any artifact error.
            let __vcheck_genomes = match
                ::verus_spec_check::cov_fuzz::covext_replay_genomes(#target_id)
            {
                ::core::result::Result::Ok(::core::option::Option::Some(genomes)) => genomes,
                ::core::result::Result::Ok(::core::option::Option::None) => return,
                ::core::result::Result::Err(error) => panic!("{error}"),
            };
            let __vcheck_gen = #bolero_generator_expr;
            let __vcheck_opts = ::core::default::Default::default();
            for __vcheck_g in __vcheck_genomes {
                let mut __vcheck_driver =
                    ::verus_spec_check::bolero_generator::driver::ByteSliceDriver::new(
                        &__vcheck_g,
                        &__vcheck_opts,
                    );
                let ::core::option::Option::Some(#bolero_closure_pat) =
                    ValueGenerator::generate(&__vcheck_gen, &mut __vcheck_driver)
                else {
                    panic!("cov_fuzz replay drift: recorded genome no longer decodes");
                };
                #(#pre_state_lets)*
                #(#replay_requires_stmts)*
                #(#pre_call_bindings)*
                #result_let
                #(#post_call_bindings)*
                let _ = &#result_binding;
            }
            ::verus_spec_check::cov_fuzz::covext_mark_replay_complete(#target_id)
                .unwrap_or_else(|error| panic!("{error}"));
        }
    }
}

fn engagement_antecedent(clause: &Expr) -> Result<Option<Expr>, &'static str> {
    match implication_antecedent_conj(clause) {
        Some(antecedent) if contains_quantifier(&antecedent) => {
            Err(INLINE_QUANTIFIER_ENGAGEMENT_REASON)
        }
        other => Ok(other),
    }
}

/// Split an ensures clause's implication spine and return the
/// conjunction of its antecedents, or `None` when the clause is not an
/// implication (it then constrains — "engages" — every execution).
///
/// `A ==> B` yields `A`; a right-nested chain `A ==> B ==> C` yields
/// `(A) && (B)` (the consequent `C` only speaks when the whole chain of
/// antecedents holds); `B <== A` is handled as `A ==> B`. Biconditionals
/// (`<==>`) and every other shape engage unconditionally — a
/// biconditional constrains both directions on every input.
///
/// Runs BEFORE the general contract lowering, which erases `==>` into
/// `!a || b` and would make the split impossible.
fn implication_antecedent_conj(clause: &Expr) -> Option<Expr> {
    // Peel parens AND invisible groups (macro-interpolation artifacts) —
    // same convention as expr_utils' peelers. Missing the Group case
    // would silently degrade a group-wrapped implication to
    // "always engaged" (over-reporting coverage).
    fn unparen(mut e: &Expr) -> &Expr {
        loop {
            match e {
                Expr::Paren(p) => e = &p.expr,
                Expr::Group(g) => e = &g.expr,
                _ => return e,
            }
        }
    }
    let mut antes: Vec<Expr> = Vec::new();
    let mut cur = unparen(clause);
    loop {
        match cur {
            Expr::Binary(b) if matches!(b.op, verus_syn::BinOp::Imply(_)) => {
                antes.push((*b.left).clone());
                cur = unparen(&b.right);
            }
            Expr::Binary(b) if matches!(b.op, verus_syn::BinOp::Exply(_)) => {
                // `B <== A` is `A ==> B`: the antecedent is the right
                // operand and the spine continues left.
                antes.push((*b.right).clone());
                cur = unparen(&b.left);
            }
            _ => break,
        }
    }
    let mut antes = antes.into_iter();
    let first = antes.next()?;
    Some(antes.fold(first, |conj, a| {
        verus_syn::parse_quote! { (#conj) && (#a) }
    }))
}

/// Given a strategy decl in `<id> in <strategy>` form, return the
/// `<strategy>` token-stream. The mutant runner builds its own tuple of
/// strategies rather than using `proptest!`'s `id in <s>` syntax, so it
/// needs to extract just the strategy expression.
pub fn extract_strategy_expr(decl: &TokenStream2) -> TokenStream2 {
    // The simplest approach is to parse the decl's source-text form
    // back into a Rust expression by skipping the leading "<id> in".
    // Use TokenStream lookahead to find the `in` keyword and take the
    // tail.
    let mut iter = decl.clone().into_iter();
    let mut saw_in = false;
    let mut tail = TokenStream2::new();
    for tt in iter.by_ref() {
        if let proc_macro2::TokenTree::Ident(id) = &tt {
            if id == "in" {
                saw_in = true;
                break;
            }
        }
    }
    if !saw_in {
        // Fallback: return the whole decl. The caller's tuple syntax
        // will still parse, just possibly with the wrong shape.
        return decl.clone();
    }
    for tt in iter {
        tail.extend(std::iter::once(tt));
    }
    tail
}

/// Walk an expression and rename every occurrence of the identifier `from`
/// to `to`. Used by the quantifier-lifting pass to give the return-value
/// binder a hygienic name inside a synthetic clause spec fn (the `exec_spec`
/// companion generator names its own return `res`, so a user contract whose
/// return binder is literally `res` would otherwise collide).
pub fn rename_ident_in_expr(expr: &mut Expr, from: &str, to: &Ident) {
    struct R<'a> {
        from: &'a str,
        to: &'a Ident,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
            for seg in p.path.segments.iter_mut() {
                if seg.ident == self.from {
                    seg.ident = self.to.clone();
                }
            }
            verus_syn::visit_mut::visit_expr_path_mut(self, p);
        }
    }
    let mut r = R { from, to };
    r.visit_expr_mut(expr);
}

/// Collect the names of single-ident arguments appearing inside `old(...)`
/// calls within an expression (e.g. `old(vec)` -> `"vec"`). Used by the
/// quantifier-lifting pass to thread `&mut` pre-state snapshots into a
/// synthetic clause spec fn.
pub fn collect_old_call_params(expr: &Expr) -> Vec<String> {
    struct F {
        names: Vec<String>,
    }
    impl<'a> Visit<'a> for F {
        fn visit_expr_call(&mut self, c: &'a ExprCall) {
            if let Expr::Path(p) = c.func.as_ref() {
                if p.path.is_ident("old") && c.args.len() == 1 {
                    if let Some(name) = ident_of_expr(&c.args[0]) {
                        if !self.names.contains(&name) {
                            self.names.push(name);
                        }
                    }
                }
            }
            verus_syn::visit::visit_expr_call(self, c);
        }
    }
    let mut f = F { names: Vec::new() };
    f.visit_expr(expr);
    f.names
}

/// Replace every `old(<param>)` call (for the given `param` name) with a bare
/// identifier `alias`. The pre-state is passed to the synthetic clause spec
/// fn as its own parameter, so inside the lifted body `old(vec)` becomes the
/// `__vcheck_old_vec` argument.
pub fn rewrite_old_call_to_ident(expr: &mut Expr, param: &str, alias: &Ident) {
    struct R<'a> {
        param: &'a str,
        alias: &'a Ident,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            if let Expr::Call(c) = e {
                if let Expr::Path(p) = c.func.as_ref() {
                    if p.path.is_ident("old")
                        && c.args.len() == 1
                        && ident_of_expr(&c.args[0]).as_deref() == Some(self.param)
                    {
                        let alias = self.alias;
                        *e = verus_syn::parse_quote! { #alias };
                        return;
                    }
                }
            }
            verus_syn::visit_mut::visit_expr_mut(self, e);
        }
    }
    let mut r = R { param, alias };
    r.visit_expr_mut(expr);
}

/// Walk an expression and replace every `self` ident with `replacement`.
pub fn replace_self_with_ident(expr: &mut Expr, replacement: &Ident) {
    struct R<'a> {
        replacement: &'a Ident,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
            for seg in p.path.segments.iter_mut() {
                if seg.ident == "self" {
                    seg.ident = self.replacement.clone();
                }
            }
            verus_syn::visit_mut::visit_expr_path_mut(self, p);
        }
    }
    let mut r = R { replacement };
    r.visit_expr_mut(expr);
}

// ---------------------------------------------------------------------------
// `mode = "fuzz"` harness (cfg-split: bolero engines / in-process guided loop)
// ---------------------------------------------------------------------------

/// Everything the fuzz-mode emitter needs from `emit_harness_with_flavor`'s
/// scope. Bundled in a struct so the borrow is one tidy hand-off instead of
/// an 17-argument fn signature.
pub(crate) struct FuzzModeHarnessInputs<'a> {
    pub target: &'a ContractTarget,
    pub fn_name: &'a Ident,
    pub vcheck_fn_name: &'a Ident,
    pub miri_ignore_attr: &'a TokenStream2,
    /// The complete bolero `check!()` body (vacuity statics + check chain +
    /// vacuity check) — compiled in verbatim under the engine cfgs.
    pub bolero_check_body: &'a TokenStream2,
    pub bolero_generator_expr: &'a TokenStream2,
    pub bolero_closure_pat: &'a TokenStream2,
    pub rewritten_requires: &'a [TokenStream2],
    pub rewritten_ensures: &'a [TokenStream2],
    /// Original (pre-rewrite) ensures exprs, parallel to
    /// `rewritten_ensures`; stringified into the failure report so the
    /// user sees their own clause text, not the lowered form.
    pub ensures_src_for_audit: &'a [Expr],
    pub uses_real: bool,
    pub pre_state_lets: &'a [TokenStream2],
    pub pre_call_bindings: &'a [TokenStream2],
    pub post_call_bindings: &'a [TokenStream2],
    pub real_call_args: &'a [TokenStream2],
    pub return_shape: &'a ReturnShape,
    pub result_binding: &'a Ident,
}

/// Emit the `mode = "fuzz"` harness: one `#[test] fn vcheck_<fn>()` whose body
/// is cfg-split between the bolero engines and an in-process
/// coverage-guided contract check, plus the module-scope instrumented twin
/// that supplies branch feedback to the latter.
///
/// Layout of the emitted items:
///
///  - `static __VCHECK_FUZZ_HITS_<fn>: [AtomicBool; N]` + marker fn
///    `__vcheck_fuzzmark_<fn>(i)` — one hit bit per branch arm
///    `instrument_branches` found in the body (cov_fuzz's instrumenter,
///    reused verbatim).
///  - An instrumented twin `__vcheck_fuzz_fn_<fn>` — same signature as the
///    original with Verus annotations stripped (methods lowered to a free
///    fn with a `self_value` positional param, via the cov_mutate twin
///    emitters), body instrumented with marker calls.
///  - The `#[test]` fn:
///      - under `any(fuzzing_libfuzzer, fuzzing_afl, fuzzing_honggfuzz,
///        fuzzing_random, kani)` — exactly the cfgs bolero's own engine
///        dispatch keys on — the untouched `check!()` body, so
///        `cargo bolero test` behavior is byte-identical to before;
///      - otherwise (plain `cargo test`) the guided loop: byte genomes
///        decode through the same bolero generator stack
///        (`ByteSliceDriver` zero-fills, so decoding is total in
///        practice), `requires` clauses skip-with-guidance-bit, the twin
///        runs, `ensures` violations return `Failed` — the loop stops,
///        shrinks the genome, and the harness panics with the decoded
///        counterexample.
///
/// The `#[allow(unexpected_cfgs)]` on the test fn keeps the engine-cfg
/// names from tripping the lint in consumer crates that haven't
/// registered them in `check-cfg` (only `cfg(kani)` registration is
/// documented; the fuzzing_* names would otherwise force a new
/// registration on every fuzz-mode user).
///
/// Naming mirrors `vcheck_fn_name`: methods get a `<SelfTy>_<fn>` suffix so
/// a free fn and a method of the same name coexist (an improvement over
/// cov_fuzz's bare-ident twins, whose collision is a documented
/// limitation).
pub(crate) fn emit_fuzz_mode_harness(inputs: FuzzModeHarnessInputs<'_>) -> TokenStream2 {
    let FuzzModeHarnessInputs {
        target,
        fn_name,
        vcheck_fn_name,
        miri_ignore_attr,
        bolero_check_body,
        bolero_generator_expr,
        bolero_closure_pat,
        rewritten_requires,
        rewritten_ensures,
        ensures_src_for_audit,
        uses_real,
        pre_state_lets,
        pre_call_bindings,
        post_call_bindings,
        real_call_args,
        return_shape,
        result_binding,
    } = inputs;

    /// Per-fn cap on instrumented branch arms — same value and rationale
    /// as cov_fuzz's emitter (bounded compile time / hit-array size).
    const PER_FN_MAX_BRANCHES: usize = 128;

    // Twin / static / marker names, disambiguated like `vcheck_fn_name`.
    let name_suffix = match target {
        ContractTarget::Method { self_ty, .. } => format!("{}_{}", self_ty, fn_name),
        ContractTarget::FreeFn { .. } => fn_name.to_string(),
    };
    let twin_ident = format_ident!("__vcheck_fuzz_fn_{}", name_suffix);
    let marker_ident = format_ident!("__vcheck_fuzzmark_{}", name_suffix);
    let hits_ident = format_ident!("__VCHECK_FUZZ_HITS_{}", name_suffix);
    let false_const_ident = format_ident!("__VCHECK_FUZZ_FALSE_{}", name_suffix);

    // Instrument the ORIGINAL body (branch arms gain marker calls); build
    // the twin from it with the same emitters cov_mutate/cov_fuzz use.
    let (sites, instrumented_body, _hit_cap) = match target {
        ContractTarget::FreeFn { item_fn, .. } => crate::vcheck_instrument::instrument_branches(
            item_fn.block.as_ref(),
            &marker_ident,
            PER_FN_MAX_BRANCHES,
        ),
        ContractTarget::Method { method, .. } => crate::vcheck_instrument::instrument_branches(
            &method.block,
            &marker_ident,
            PER_FN_MAX_BRANCHES,
        ),
    };
    let n_sites = sites.len();
    let twin_ts = match target {
        ContractTarget::FreeFn { item_fn, .. } => {
            emit_mutant_fn_freefn(item_fn, &twin_ident, &instrumented_body)
        }
        ContractTarget::Method {
            self_ty, method, ..
        } => emit_mutant_fn_method(self_ty, method, &twin_ident, &instrumented_body),
    };

    // `requires` -> guidance-bit mark or skip (the CovFuzzRunner lowering,
    // retargeted at `ContractExec`).
    let n_req = rewritten_requires.len();
    let fuzz_requires_stmts: Vec<TokenStream2> = rewritten_requires
        .iter()
        .enumerate()
        .map(|(j, r)| {
            if uses_real {
                quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_req = { #r };
                    if ::verus_spec_check::__vcheck_real::is_defined() && __vcheck_req {
                        __VCHECK_FUZZ_GUIDE[#j].store(
                            true, ::core::sync::atomic::Ordering::Relaxed);
                    } else {
                        return ::verus_spec_check::cov_fuzz::ContractExec::Skipped;
                    }
                }}
            } else {
                quote! {
                    if { #r } {
                        __VCHECK_FUZZ_GUIDE[#j].store(
                            true, ::core::sync::atomic::Ordering::Relaxed);
                    } else {
                        return ::verus_spec_check::cov_fuzz::ContractExec::Skipped;
                    }
                }
            }
        })
        .collect();

    // `ensures` -> `Failed(<original clause text>)`. Under a `real`
    // contract an unspecified case skips the clause (mirroring the
    // bolero/proptest lowerings).
    let fuzz_ensures_stmts: Vec<TokenStream2> = rewritten_ensures
        .iter()
        .zip(ensures_src_for_audit.iter())
        .map(|(e, src)| {
            let clause_txt = format!("ensures clause failed: `{}`", quote!(#src));
            if uses_real {
                quote! {{
                    ::verus_spec_check::__vcheck_real::reset_defined();
                    let __vcheck_ens = { #e };
                    if ::verus_spec_check::__vcheck_real::is_defined() && !__vcheck_ens {
                        return ::verus_spec_check::cov_fuzz::ContractExec::Failed(#clause_txt);
                    }
                }}
            } else {
                quote! {
                    if !(#e) {
                        return ::verus_spec_check::cov_fuzz::ContractExec::Failed(#clause_txt);
                    }
                }
            }
        })
        .collect();

    // Call routes through the twin (a free fn at module scope; the same
    // `real_call_args` the `super::` call uses are shape-compatible, as
    // in the MutantRunner/CovFuzzRunner flavors).
    let fuzz_call = quote! { #twin_ident(#(#real_call_args),*) };
    let fuzz_return_snapshot = mutable_return_snapshot_let(return_shape, result_binding);
    let fuzz_result_let = match return_shape {
        ReturnShape::Unit => quote! {
            #fuzz_call;
            let #result_binding: () = ();
            let _ = &#result_binding;
        },
        _ => quote! {
            let #result_binding = #fuzz_call;
            #fuzz_return_snapshot
        },
    };

    // Display name for the failure report: the fn under test, qualified
    // for methods (`Counter::step`), not the harness name.
    let fn_name_str = match target {
        ContractTarget::Method { self_ty, .. } => format!("{}::{}", self_ty, fn_name),
        ContractTarget::FreeFn { .. } => fn_name.to_string(),
    };

    quote_spanned! { fn_name.span() =>
        // Branch hit bits + marker for the fuzz twin. Const-item
        // repetition keeps the array init valid for non-Copy AtomicBool.
        #[allow(clippy::declare_interior_mutable_const)]
        const #false_const_ident: ::core::sync::atomic::AtomicBool =
            ::core::sync::atomic::AtomicBool::new(false);
        static #hits_ident: [::core::sync::atomic::AtomicBool; #n_sites] =
            [#false_const_ident; #n_sites];
        #[allow(non_snake_case, dead_code)]
        pub(super) fn #marker_ident(__vcheck_i: usize) {
            if let ::core::option::Option::Some(__vcheck_b) = #hits_ident.get(__vcheck_i) {
                __vcheck_b.store(true, ::core::sync::atomic::Ordering::Relaxed);
            }
        }
        #twin_ts

        #[test]
        #[allow(unexpected_cfgs)]
        #miri_ignore_attr
        fn #vcheck_fn_name() {
            // Engine half: exactly the cfgs bolero's own dispatch keys
            // on. `cargo bolero test --engine <e>` / kani builds land
            // here and behave as before this harness was cfg-split.
            #[cfg(any(
                fuzzing_libfuzzer,
                fuzzing_afl,
                fuzzing_honggfuzz,
                fuzzing_random,
                kani
            ))]
            {
                #bolero_check_body
            }
            // Plain `cargo test` half: the in-process guided loop.
            #[cfg(not(any(
                fuzzing_libfuzzer,
                fuzzing_afl,
                fuzzing_honggfuzz,
                fuzzing_random,
                kani
            )))]
            {
                use ::verus_spec_check::bolero_generator::ValueGenerator;
                // Per-requires-clause guidance bits (search feedback
                // only, like the CovFuzzRunner flavor's).
                #[allow(clippy::declare_interior_mutable_const)]
                const __VCHECK_FUZZ_FALSE: ::core::sync::atomic::AtomicBool =
                    ::core::sync::atomic::AtomicBool::new(false);
                static __VCHECK_FUZZ_GUIDE:
                    [::core::sync::atomic::AtomicBool; #n_req] =
                    [__VCHECK_FUZZ_FALSE; #n_req];
                let __vcheck_gen = #bolero_generator_expr;
                let __vcheck_opts = ::core::default::Default::default();
                let mut __vcheck_exec = |__vcheck_bytes: &[u8]|
                    -> ::verus_spec_check::cov_fuzz::ContractExec
                {
                    let mut __vcheck_driver =
                        ::verus_spec_check::bolero_generator::driver::ByteSliceDriver::new(
                            __vcheck_bytes,
                            &__vcheck_opts,
                        );
                    let ::core::option::Option::Some(#bolero_closure_pat) =
                        ValueGenerator::generate(&__vcheck_gen, &mut __vcheck_driver)
                    else {
                        return ::verus_spec_check::cov_fuzz::ContractExec::Invalid;
                    };
                    // Snapshot pre-call `&mut` state for `old(<id>)`.
                    #(#pre_state_lets)*
                    // requires -> guidance-bit mark or skip.
                    #(#fuzz_requires_stmts)*
                    #(#pre_call_bindings)*
                    #fuzz_result_let
                    // `&mut` permission post-state transitions.
                    #(#post_call_bindings)*
                    let _ = &#result_binding;
                    // ensures -> Failed (stops the search; the loop
                    // shrinks and the harness reports below).
                    #(#fuzz_ensures_stmts)*
                    ::verus_spec_check::cov_fuzz::ContractExec::Tested
                };
                match ::verus_spec_check::cov_fuzz::guided_contract_loop(
                    &[&#hits_ident[..], &__VCHECK_FUZZ_GUIDE[..]],
                    &mut __vcheck_exec,
                ) {
                    ::verus_spec_check::cov_fuzz::ContractVerdict::Passed(__vcheck_stats) => {
                        // Vacuity: a run whose every input was rejected
                        // (or undecodable) never evaluated the contract.
                        ::core::assert!(
                            !(__vcheck_stats.tested == 0 && __vcheck_stats.executions > 0),
                            "verus_spec_check: vacuous fuzz harness: no sampled input ever \
    reached the contract check ({} skipped by `requires`, {} undecodable). Narrow the \
    input generator or weaken the precondition.",
                            __vcheck_stats.skipped,
                            __vcheck_stats.invalid
                        );
                    }
                    ::verus_spec_check::cov_fuzz::ContractVerdict::Failed {
                        genome: __vcheck_genome,
                        failure: __vcheck_failure,
                        stats: __vcheck_stats,
                    } => {
                        // Re-decode the minimized genome for the report.
                        let mut __vcheck_driver =
                            ::verus_spec_check::bolero_generator::driver::ByteSliceDriver::new(
                                &__vcheck_genome,
                                &__vcheck_opts,
                            );
                        let __vcheck_decoded =
                            ValueGenerator::generate(&__vcheck_gen, &mut __vcheck_driver);
                        ::core::panic!(
                            "verus_spec_check: `mode = \"fuzz\"` found a contract violation \
    in `{}`\n  failure: {}\n  input:   {:?}\n  after {} executions ({} tested); the run \
    is deterministic — set VERUS_SPEC_CHECK_FUZZ_SEED to vary the search, \
    VERUS_SPEC_CHECK_FUZZ_BUDGET to extend it",
                            #fn_name_str,
                            __vcheck_failure,
                            __vcheck_decoded,
                            __vcheck_stats.executions,
                            __vcheck_stats.tested
                        );
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod engagement_tests {
    use super::*;

    fn implication(left: Expr, right: Expr) -> Expr {
        Expr::Binary(verus_syn::ExprBinary {
            attrs: Vec::new(),
            left: Box::new(left),
            op: verus_syn::BinOp::Imply(Default::default()),
            right: Box::new(right),
        })
    }

    #[test]
    fn inline_quantified_antecedent_is_unlowerable_not_always() {
        let closure: Expr = verus_syn::parse_quote! { |i: u8| i == i };
        let quantified = Expr::Unary(verus_syn::ExprUnary {
            attrs: Vec::new(),
            op: verus_syn::UnOp::Forall(Default::default()),
            expr: Box::new(closure),
        });
        let clause = implication(quantified, verus_syn::parse_quote! { true });
        assert_eq!(
            engagement_antecedent(&clause),
            Err(INLINE_QUANTIFIER_ENGAGEMENT_REASON)
        );
    }

    #[test]
    fn ordinary_implication_and_unconditional_clause_remain_distinct() {
        let implication = implication(
            verus_syn::parse_quote! { x > 0 },
            verus_syn::parse_quote! { true },
        );
        let unconditional: Expr = verus_syn::parse_quote! { x == x };
        assert!(matches!(engagement_antecedent(&implication), Ok(Some(_))));
        assert!(matches!(engagement_antecedent(&unconditional), Ok(None)));
    }
}
