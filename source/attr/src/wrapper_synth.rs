use super::*;

// ---------------------------------------------------------------------------
// The unified pass
// ---------------------------------------------------------------------------

/// Synthesize an `#[verifier::external_body]` exec wrapper fn from an
/// `assume_specification` item. The wrapper preserves the marker attributes
/// (`#[vcheck]` / `#[vcheck_provide]`), the generic params, the parameter list, the
/// return type, and the contract; its body is a trusted call into the path
/// the assume_specification names. Once the rest of the pass sees an ordinary
/// `Item::Fn` with `#[vcheck]`, the existing pipeline (closure, harness emit,
/// strategy sizing, etc.) carries the rest.
///
/// Returns `None` for shapes the synthesis can't handle (currently:
/// assume_specification with a `qself` projection — `<Vec<T> as Clone>::clone`
/// — that we don't yet emit a synthetic body for).
pub fn synthesize_vcheck_wrapper_from_assume_spec(
    asp: &verus_syn::AssumeSpecification,
) -> Option<verus_syn::ItemFn> {
    use verus_syn::token::{Brace, Paren};
    use verus_syn::{
        Block, Expr, ExprCall, ExprPath, FnArg, FnArgKind, FnMode, ModeExec, Pat, PatType,
        Signature, SignatureSpec, Stmt, Token,
    };

    // Build the call expression that goes in the wrapper body.
    let func_path: Expr = Expr::Path(ExprPath {
        attrs: Vec::new(),
        qself: asp.qself.clone(),
        path: asp.path.clone(),
    });

    // Collect the wrapper's parameter list and the call-site arguments.
    // We renumber unnamed receivers (`&self`) to `__vcheck_self` so the
    // synthesized body has a name to pass through.
    let mut wrapper_inputs: verus_syn::punctuated::Punctuated<FnArg, Token![,]> =
        verus_syn::punctuated::Punctuated::new();
    let mut call_args: Vec<Expr> = Vec::new();
    let mut had_self = false;
    let mut any_param_adapted = false;
    if let Some((_, inputs)) = &asp.inputs {
        for arg in inputs.iter() {
            match &arg.kind {
                FnArgKind::Receiver(rcv) => {
                    // Synthesize a typed-style first argument: `__vcheck_self: <Self type>`.
                    // For an `assume_specification`, the receiver's type is
                    // recoverable from the path's qself or first segment.
                    had_self = true;
                    let synth_name = Ident::new("__vcheck_self", rcv.self_token.span);
                    // Best-effort Self type recovery: if the path is
                    // `T::method`, the type is `T`. Use the qself if present;
                    // otherwise build a `Type::Path` from all-but-the-last
                    // segment.
                    let recv_ty = recover_receiver_type(asp);
                    let ref_ty: Type = if rcv.reference.is_some() {
                        if rcv.mutability.is_some() {
                            verus_syn::parse_quote! { &mut #recv_ty }
                        } else {
                            verus_syn::parse_quote! { &#recv_ty }
                        }
                    } else {
                        recv_ty
                    };
                    let pat: Pat = verus_syn::parse_quote! { #synth_name };
                    wrapper_inputs.push(FnArg {
                        kind: FnArgKind::Typed(PatType {
                            attrs: Vec::new(),
                            pat: Box::new(pat),
                            colon_token: Token![:](rcv.self_token.span),
                            ty: Box::new(ref_ty),
                        }),
                        tracked: None,
                    });
                    call_args.push(verus_syn::parse_quote! { #synth_name });
                }
                FnArgKind::Typed(pt) => {
                    // Special-case `&Container<E>` parameters: my harness
                    // pipeline doesn't support `&Vec<T>` / `&Option<T>` /
                    // etc. as parameters yet (the current `classify_param_type`
                    // only handles `&[E]` and `&UserType`). Adapt by
                    // stripping the outer reference and passing `&name` at
                    // the call site, so the harness samples the owned form
                    // and the trusted body still receives a borrow.
                    //
                    // `&mut Container<T>` is NOT adapted — we keep it as-is.
                    // The harness emitter handles `&mut` by sampling the
                    // owned form of the inner shape and passing
                    // `&mut <id>` at the call site (see ParamShape::MutRef).
                    let mut adapted = arg.clone();
                    let mut needs_borrow = false;
                    if let FnArgKind::Typed(adapted_pt) = &mut adapted.kind {
                        if let Type::Reference(rty) = adapted_pt.ty.as_ref() {
                            // Skip `&mut` — the harness emitter handles it
                            // via the MutRef shape.
                            if rty.mutability.is_none() {
                                if let Type::Path(tp) = rty.elem.as_ref() {
                                    if tp.qself.is_none() && !tp.path.segments.is_empty() {
                                        let last =
                                            tp.path.segments.last().unwrap().ident.to_string();
                                        if matches!(
                                            last.as_str(),
                                            "Vec"
                                                | "Option"
                                                | "Result"
                                                | "HashMap"
                                                | "HashSet"
                                                | "BTreeMap"
                                                | "BTreeSet"
                                                | "VecDeque"
                                                | "Multiset"
                                                | "String"
                                                // Primitive number / Copy types
                                                // — strip outer `&` so the
                                                // harness samples by value and
                                                // passes `&v` at the call.
                                                | "f32" | "f64"
                                                | "u8" | "u16" | "u32" | "u64" | "u128" | "usize"
                                                | "i8" | "i16" | "i32" | "i64" | "i128" | "isize"
                                                | "bool" | "char"
                                        ) {
                                            // Strip the outer `&`.
                                            let inner = (*rty.elem).clone();
                                            adapted_pt.ty = Box::new(inner);
                                            needs_borrow = true;
                                            any_param_adapted = true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    wrapper_inputs.push(adapted);
                    if let Some(name) = simple_pat_ident(&pt.pat) {
                        if needs_borrow {
                            call_args.push(verus_syn::parse_quote! { &#name });
                        } else {
                            call_args.push(verus_syn::parse_quote! { #name });
                        }
                    } else {
                        // Unnamed/complex pattern: we can't synthesize a
                        // call-arg ident.
                        return None;
                    }
                }
            }
        }
    }
    let _ = had_self; // currently unused but kept for clarity

    let mut body_call: Expr = Expr::Call(ExprCall {
        attrs: Vec::new(),
        func: Box::new(func_path),
        paren_token: Paren::default(),
        args: call_args.into_iter().collect(),
        // verus_syn 2026-07-27+: synthesized wrapper calls are never atomic.
        atomically: None,
    });

    // If we adapted any `&Container` param to its owned form, the wrapper's
    // owned param is dropped at function exit. A `&T` return that borrows
    // from such a param would dangle (E0515). Materialize an owned `T`
    // instead by appending `.to_owned()` and rewriting the wrapper's
    // output type from `&T` to the owned form. The contract was written
    // with `res@`/`*res` semantics that work the same on the owned value
    // because `View` impls agree (e.g. `String@ == &str@` for the same
    // contents).
    //
    // The same dangle problem applies to `Option<&T>` and `Result<&T, E>`
    // returns even when no `&Container` param was adapted — the harness
    // pipeline's `classify_return` rejects `Option<&T>` because the
    // nested `&T` element isn't classifiable. We rewrite ALL such returns
    // (regardless of `any_param_adapted`) to `Option<T>` / `Result<T, E>`
    // and append `.cloned()` / `.map(|x| x.clone())` so the harness sees
    // an owned form.
    let mut adjusted_output = asp.output.clone();
    // Set when a `&X` return is materialized to owned `X`: the named
    // return ident whose `*ret` derefs must be stripped from the contract.
    let mut ret_deref_strip: Option<String> = None;
    if let verus_syn::ReturnType::Type(_, _, _, ty) = &asp.output {
        // Case 1: bare `&T` return (only adapt if a `&Container` param
        // was stripped to owned, otherwise the original lifetime is fine).
        if any_param_adapted {
            if let Type::Reference(rty) = ty.as_ref() {
                let inner = (*rty.elem).clone();
                let inner_name: Option<String> = if let Type::Path(tp) = &inner {
                    tp.path.segments.last().map(|s| s.ident.to_string())
                } else {
                    None
                };
                let owned_ty: Option<Type> = match inner_name.as_deref() {
                    // `&str` materializes as `String`; this matches the
                    // engine's String/Seq<char> view interchangeability.
                    Some("str") => Some(verus_syn::parse_quote! { ::std::string::String }),
                    Some("Vec") | Some("String") | Some("Option") | Some("Result")
                    | Some("HashMap") | Some("HashSet") | Some("BTreeMap") | Some("BTreeSet")
                    | Some("VecDeque") => Some(inner.clone()),
                    _ => None,
                };
                // Bare single-segment `&X` (a type param like `&T`, or a
                // primitive like `&u32`): materialize as owned `X` via the
                // appended `.to_owned()`. The wrapper is fully
                // monomorphized before rustc sees it (the unbound-params
                // diagnostic guarantees every param is substituted), so
                // `X: Clone` holds for the shapes that reach here; anything
                // else fails loudly at the `.to_owned()` call.
                let owned_ty: Option<Type> = owned_ty.or_else(|| {
                    if let Type::Path(tp) = &inner {
                        if tp.qself.is_none()
                            && tp.path.segments.len() == 1
                            && matches!(tp.path.segments[0].arguments, PathArguments::None)
                        {
                            return Some(inner.clone());
                        }
                    }
                    None
                });
                // `&[T]` return (e.g. `Vec::as_slice`, `Option::as_slice`):
                // the elem is a `Type::Slice`, not a path. Materialize an
                // owned `Vec<T>` — `<[T] as ToOwned>::Owned = Vec<T>`, so the
                // appended `.to_owned()` below does the conversion, and the
                // engine's `OwnedVec` return shape gives contracts the same
                // `Seq<T>` view the original `&[T]` had.
                let owned_ty: Option<Type> = owned_ty.or_else(|| {
                    if let Type::Slice(sl) = &inner {
                        let elem = (*sl.elem).clone();
                        Some(verus_syn::parse_quote! { ::std::vec::Vec<#elem> })
                    } else {
                        None
                    }
                });
                if let Some(owned) = owned_ty {
                    // Replace the wrapper's output type.
                    if let verus_syn::ReturnType::Type(arrow, tracked, ret_pat, _) = &asp.output {
                        adjusted_output = verus_syn::ReturnType::Type(
                            arrow.clone(),
                            tracked.clone(),
                            ret_pat.clone(),
                            Box::new(owned.clone()),
                        );
                        // The contract was written against a `&X` return;
                        // now that the wrapper returns owned `X`, bare
                        // `*ret` derefs in the contract no longer type.
                        // Record the ret ident so requires/ensures get a
                        // deref-strip below.
                        if let Some(boxed) = ret_pat {
                            if let verus_syn::Pat::Ident(pi) = &boxed.1 {
                                ret_deref_strip = Some(pi.ident.to_string());
                            }
                        }
                    }
                    // Append `.to_owned()` to the trusted call so we
                    // materialize an owned value before the wrapper's
                    // owned params are dropped. `to_owned` works for `str
                    // -> String` via `ToOwned` and for `T: Clone -> T`
                    // via the blanket impl.
                    body_call = verus_syn::parse_quote! { (#body_call).to_owned() };
                }
            }
        }
        // Case 2: `Option<&T>` or `Result<&T, E>` or `Result<&T, &E>`
        // return — the inner `&T` always blocks classify_return
        // regardless of param adaptation. Always rewrite to the owned
        // form.
        if let Type::Path(tp) = ty.as_ref() {
            if tp.qself.is_none() && !tp.path.segments.is_empty() {
                let last_seg = tp.path.segments.last().unwrap();
                let last_name = last_seg.ident.to_string();
                if matches!(last_name.as_str(), "Option" | "Result") {
                    // Get the first generic arg.
                    if let PathArguments::AngleBracketed(args) = &last_seg.arguments {
                        if let Some(GenericArgument::Type(inner_ty)) = args.args.first() {
                            if let Type::Reference(inner_rty) = inner_ty {
                                let owned_inner: Type = (*inner_rty.elem).clone();
                                // Also peel `&E` on the second arg for
                                // `Result<&T, &E>`. The wrapper rewrite
                                // strips both sides; the `.map(|x|
                                // x.clone())` call lowered below handles
                                // only the Ok side, so a separate
                                // `.map_err(|e| e.clone())` is appended
                                // when both sides were references.
                                let mut err_was_ref = false;
                                let owned_err: Option<Type> = if last_name == "Result" {
                                    if let Some(GenericArgument::Type(err_ty)) =
                                        args.args.iter().nth(1)
                                    {
                                        if let Type::Reference(err_rty) = err_ty {
                                            err_was_ref = true;
                                            Some((*err_rty.elem).clone())
                                        } else {
                                            None
                                        }
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                };
                                // Build the new `Option<T>` / `Result<T, E>`.
                                let mut new_path = tp.clone();
                                let new_last = new_path.path.segments.last_mut().unwrap();
                                if let PathArguments::AngleBracketed(ab) = &mut new_last.arguments {
                                    let mut args_iter = ab.args.iter_mut();
                                    if let Some(arg0) = args_iter.next() {
                                        *arg0 = GenericArgument::Type(owned_inner.clone());
                                    }
                                    if let (Some(owned_e), Some(arg1)) =
                                        (owned_err.clone(), args_iter.next())
                                    {
                                        *arg1 = GenericArgument::Type(owned_e);
                                    }
                                }
                                let owned_outer: Type = Type::Path(new_path);
                                if let verus_syn::ReturnType::Type(arrow, tracked, ret_pat, _) =
                                    &asp.output
                                {
                                    adjusted_output = verus_syn::ReturnType::Type(
                                        arrow.clone(),
                                        tracked.clone(),
                                        ret_pat.clone(),
                                        Box::new(owned_outer.clone()),
                                    );
                                }
                                // Append `.cloned()` for Option, or
                                // `.map(|x| x.clone())` for Result. Both
                                // materialize the inner reference into
                                // an owned value before the param drops.
                                // For `Result<&T, &E>`, also map_err so
                                // the Err side is owned.
                                if last_name == "Option" {
                                    body_call = verus_syn::parse_quote! { (#body_call).cloned() };
                                } else if err_was_ref {
                                    body_call = verus_syn::parse_quote! {
                                        (#body_call)
                                            .map(|__x| __x.clone())
                                            .map_err(|__e| __e.clone())
                                    };
                                } else {
                                    body_call = verus_syn::parse_quote! {
                                        (#body_call).map(|__x| __x.clone())
                                    };
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // The target may be an `unsafe fn` (e.g. `str::from_utf8_unchecked`) —
    // syntactically undetectable from an assume_specification. Wrap the
    // trusted call in `unsafe {}` unconditionally; `allow(unused_unsafe)`
    // silences the warning for safe targets. Soundness note: the wrapper's
    // requires clauses ARE the documented safety conditions (that's what
    // the assume_specification asserts), and the harness only calls with
    // requires satisfied.
    let body_call: Expr = verus_syn::parse_quote! {
        #[allow(unused_unsafe)] unsafe { #body_call }
    };
    let block = Block {
        brace_token: Brace::default(),
        stmts: vec![Stmt::Expr(body_call, None)],
    };

    // Build the wrapper fn name. A unique counter wouldn't be stable across
    // engine emissions; instead, derive from the path's last segment plus
    // an ident-safe hash of the qself type (when present) so wrappers for
    // different `<T as Trait>::method` instances don't collide on the
    // last-segment name. Without this, marking both
    // `<f32 as Clone>::clone` and `<f64 as Clone>::clone` would
    // produce two identically-named wrappers. The same logic also
    // disambiguates `Type::<T>::method` for different `T` in the second-
    // to-last segment's path arguments (e.g. `Option::<u32>::is_some` vs
    // `Option::<u64>::is_some`).
    let last_seg_name = asp
        .path
        .segments
        .last()
        .map(|s| s.ident.to_string())
        .unwrap_or_else(|| "fn".to_string());
    fn ident_sanitize(raw: &str) -> String {
        let mut s = String::with_capacity(raw.len());
        for c in raw.chars() {
            if c.is_ascii_alphanumeric() {
                s.push(c);
            } else if !s.ends_with('_') {
                s.push('_');
            }
        }
        s.trim_matches('_').to_string()
    }
    let qself_suffix: String = if let Some(qself) = &asp.qself {
        let ty = &*qself.ty;
        let toks = quote! { #ty };
        ident_sanitize(&toks.to_string())
    } else {
        // No qself: include path-but-last to disambiguate `Foo::method` from
        // `Bar::method` when both are marked. Also include any path
        // arguments from each segment, sanitized, so that
        // `Option::<u32>::is_some` and `Option::<u64>::is_some` produce
        // distinct wrapper names.
        let segs: Vec<String> = asp
            .path
            .segments
            .iter()
            .take(asp.path.segments.len().saturating_sub(1))
            .map(|s| {
                let toks = quote! { #s };
                ident_sanitize(&toks.to_string())
            })
            .collect();
        if !segs.is_empty() {
            segs.join("_")
        } else {
            String::new()
        }
    };
    let wrapper_ident = if qself_suffix.is_empty() {
        format_ident!("__vcheck_assume_{}", last_seg_name)
    } else {
        format_ident!("__vcheck_assume_{}_{}", qself_suffix, last_seg_name)
    };

    // Construct the SignatureSpec from the assume_spec's clauses.
    //
    // `returns expr` semantically means "the return value equals expr" but
    // the harness emitter only walks `requires` / `ensures`. If the output
    // has a named pattern (e.g. `-> (len: usize)`), translate the returns
    // clause into an equivalent ensures clause `name == expr` so the
    // harness can drive it. Without this conversion, `assume_specification`
    // items written with `returns` instead of `ensures` produce no harness.
    //
    // When the source `assume_specification` has an UNNAMED return type
    // (e.g. `-> u8` instead of `-> (res: u8)`), the synthesized wrapper
    // gets a fresh `__vcheck_ret` name injected into the output type so the
    // ensures-clause translation can refer to it. Without this, the
    // returns clause is silently dropped and the harness emits no
    // contract assertion at all — the test runs the call and discards
    // the result, passing vacuously.
    let mut requires = asp.requires.clone();
    let _ = &mut requires; // suppress unused-mut warning when no transform happens
    let mut ensures = asp.ensures.clone();
    // Deref-strip for owned-materialized returns: rewrite `*ret` -> `ret`
    // everywhere in the contract.
    if let Some(ret_name) = &ret_deref_strip {
        struct StripDeref<'a> {
            name: &'a str,
        }
        impl<'a> verus_syn::visit_mut::VisitMut for StripDeref<'a> {
            fn visit_expr_mut(&mut self, e: &mut Expr) {
                if let Expr::Unary(u) = e {
                    if matches!(u.op, verus_syn::UnOp::Deref(_)) {
                        if let Expr::Path(p) = u.expr.as_ref() {
                            if p.qself.is_none()
                                && p.path.segments.len() == 1
                                && p.path.segments[0].ident == self.name
                            {
                                *e = (*u.expr).clone();
                                return;
                            }
                        }
                    }
                }
                verus_syn::visit_mut::visit_expr_mut(self, e);
            }
        }
        let mut v = StripDeref { name: ret_name };
        if let Some(req) = &mut requires {
            for e in req.exprs.exprs.iter_mut() {
                verus_syn::visit_mut::VisitMut::visit_expr_mut(&mut v, e);
            }
        }
        if let Some(ens) = &mut ensures {
            for e in ens.exprs.exprs.iter_mut() {
                verus_syn::visit_mut::VisitMut::visit_expr_mut(&mut v, e);
            }
        }
    }
    let mut returns = asp.returns.clone();
    if let Some(ret_clause) = &asp.returns {
        // Recover the named ret-pat (if any) from the output type.
        let existing_ret_ident: Option<Ident> = match &asp.output {
            verus_syn::ReturnType::Type(_, _, Some(boxed), _) => {
                fn pat_to_ident(p: &verus_syn::Pat) -> Option<Ident> {
                    match p {
                        verus_syn::Pat::Ident(pi) => Some(pi.ident.clone()),
                        verus_syn::Pat::Type(pt) => pat_to_ident(&pt.pat),
                        _ => None,
                    }
                }
                pat_to_ident(&boxed.1)
            }
            _ => None,
        };
        // Choose a return ident, synthesizing one if the source had no
        // name. Inject the synthesized name into `adjusted_output` so
        // the wrapper signature exposes it.
        let ret_id = match existing_ret_ident {
            Some(id) => Some(id),
            None => {
                if let verus_syn::ReturnType::Type(arrow, tracked, _, ty) = &adjusted_output {
                    let synth_id = format_ident!("__vcheck_ret");
                    let synth_pat: verus_syn::Pat = verus_syn::Pat::Ident(verus_syn::PatIdent {
                        attrs: Vec::new(),
                        by_ref: None,
                        mutability: None,
                        ident: synth_id.clone(),
                        subpat: None,
                    });
                    let colon: Token![:] = Token![:](proc_macro2::Span::call_site());
                    let paren = verus_syn::token::Paren::default();
                    adjusted_output = verus_syn::ReturnType::Type(
                        arrow.clone(),
                        tracked.clone(),
                        Some(Box::new((paren, synth_pat, colon))),
                        ty.clone(),
                    );
                    Some(synth_id)
                } else {
                    // No return type (Unit). The `returns` clause is
                    // semantically irrelevant; leave it untouched.
                    None
                }
            }
        };
        if let Some(ret_id) = ret_id {
            // Translate `returns expr` into `ensures (ret_id == expr)`.
            let ret_exprs: Vec<Expr> = ret_clause
                .exprs
                .exprs
                .iter()
                .map(|e| {
                    let lhs: Expr = verus_syn::parse_quote! { #ret_id };
                    let rhs = e.clone();
                    // Wrap rhs in parens to avoid Rust's
                    // chained-comparison parse error when the source
                    // `returns` clause body itself contains a comparison
                    // (e.g. `returns s@.len() == 0` would otherwise
                    // produce `__vcheck_ret == s@.len() == 0` which Rust
                    // refuses to parse as left-associative `==`).
                    verus_syn::parse_quote! { #lhs == (#rhs) }
                })
                .collect();
            let new_specification = {
                let mut p: verus_syn::punctuated::Punctuated<Expr, Token![,]> =
                    verus_syn::punctuated::Punctuated::new();
                for ex in ret_exprs {
                    p.push(ex);
                }
                verus_syn::Specification { exprs: p }
            };
            let merged = match ensures {
                Some(mut existing) => {
                    for ex in new_specification.exprs.iter() {
                        existing.exprs.exprs.push(ex.clone());
                    }
                    existing
                }
                None => verus_syn::Ensures {
                    attrs: Vec::new(),
                    token: Token![ensures](ret_clause.token.span),
                    exprs: new_specification,
                },
            };
            ensures = Some(merged);
            // Drop the returns clause now that it's been folded into ensures.
            returns = None;
        }
    }
    let spec = SignatureSpec {
        prover: None,
        requires,
        recommends: None,
        ensures,
        default_ensures: asp.default_ensures.clone(),
        returns,
        decreases: None,
        invariants: asp.invariants.clone(),
        unwind: asp.unwind.clone(),
        with: None,
        // verus_syn 2026-07-27+: synthesized wrapper specs carry no
        // atomic clause (assume_specification targets are plain exec fns).
        atomic_spec: None,
    };

    let sig = Signature {
        publish: verus_syn::Publish::Default,
        constness: None,
        asyncness: None,
        unsafety: None,
        abi: None,
        broadcast: None,
        mode: FnMode::Exec(ModeExec {
            exec_token: Token![exec](proc_macro2::Span::call_site()),
        }),
        fn_token: Token![fn](proc_macro2::Span::call_site()),
        ident: wrapper_ident,
        generics: asp.generics.clone(),
        paren_token: Paren::default(),
        inputs: wrapper_inputs,
        spec,
        variadic: None,
        output: adjusted_output,
    };

    // Carry the marker attributes through, plus stamp `#[verifier::external_body]`
    // so verification doesn't try to check the body matches the contract.
    // Keep the synthetic forwarding wrapper out of line as well. This does
    // not control inlining of the external subject, but avoids erasing the
    // stable wrapper boundary used by vcheck harnesses and diagnostics.
    //
    // Strip `#[verifier::when_used_as_spec(...)]` if present: it pairs the
    // assume_specification with a spec fn whose generic signature we may
    // have monomorphized via `#[vcheck(T = ...)]`. Keeping it on the wrapper
    // would surface a mismatch ("when_used_as_spec function should have the
    // same type parameters") at verification time. The original
    // assume_specification still carries it and continues to satisfy the
    // verifier; the wrapper is only consumed by the harness.
    let mut attrs: Vec<Attribute> = asp
        .attrs
        .iter()
        .filter(|a| {
            let p = a.path();
            if p.leading_colon.is_some() {
                return true;
            }
            let segs: Vec<String> = p.segments.iter().map(|s| s.ident.to_string()).collect();
            let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
            !matches!(segs.as_slice(), ["verifier", "when_used_as_spec"])
                && !matches!(segs.as_slice(), ["when_used_as_spec"])
        })
        .cloned()
        .collect();
    let ext_body: Attribute = verus_syn::parse_quote! {
        #[verifier::external_body]
    };
    if !attrs.iter().any(|a| {
        let p = a.path();
        p.segments.len() == 2
            && p.segments[0].ident == "verifier"
            && p.segments[1].ident == "external_body"
    }) {
        attrs.push(ext_body);
    }
    attrs.retain(|a| !a.path().is_ident("inline"));
    let no_inline: Attribute = verus_syn::parse_quote! { #[inline(never)] };
    attrs.push(no_inline);

    // Stamp the assume-spec-target sentinel: which external fn the
    // wrapper's trusted body calls (e.g. `u32::checked_add`). Stamped
    // unconditionally so downstream passes can distinguish "wrapper over
    // external code" from an ordinary fn — `#[vcheck_cov_fuzz]` uses this
    // to route the target to external (instrumented-side-profile)
    // measurement instead of source-level twin instrumentation, and the
    // path string is what the profile extractor matches against
    // demangled llvm-cov function names.
    {
        let path = &asp.path;
        let compact = |tokens: String| tokens.replace(' ', "");
        let rendered = if let Some(qself) = &asp.qself {
            let ty_tokens = &qself.ty;
            let ty = compact(quote::quote!(#ty_tokens).to_string());
            let trait_path = path
                .segments
                .iter()
                .take(qself.position)
                .map(|segment| compact(quote::quote!(#segment).to_string()))
                .collect::<Vec<_>>()
                .join("::");
            let tail = path
                .segments
                .iter()
                .skip(qself.position)
                .map(|segment| compact(quote::quote!(#segment).to_string()))
                .collect::<Vec<_>>()
                .join("::");
            if trait_path.is_empty() {
                format!("<{ty}>::{tail}")
            } else {
                format!("<{ty} as {trait_path}>::{tail}")
            }
        } else {
            compact(quote::quote!(#path).to_string())
        };
        crate::stamp_assume_spec_target_on_attrs(&mut attrs, &rendered);
        let generic_type_params: Vec<String> = asp
            .generics
            .type_params()
            .map(|param| param.ident.to_string())
            .collect();
        crate::stamp_assume_spec_type_params_on_attrs(&mut attrs, &generic_type_params);
    }

    Some(verus_syn::ItemFn {
        attrs,
        vis: asp.vis.clone(),
        sig,
        block: Box::new(block),
        semi_token: None,
    })
}

/// Synthesize an `#[verifier::external_body]` + `#[vcheck]` exec wrapper fn from
/// a `broadcast axiom fn` or `broadcast proof fn` item carrying `#[vcheck_axiom]`.
///
/// The wrapper has:
///   - The same generics, params, and return type (typically `-> ()`).
///   - `FnMode::Exec` instead of `FnMode::Proof` / `FnMode::ProofAxiom`.
///   - The original `requires` and `ensures` clauses, with `#[trigger]`
///     attribute strips on each expression (SMT-only annotations that
///     would confuse the contract rewriter at runtime).
///   - The `decreases` clause stripped (proof-only).
///   - The `broadcast` modifier stripped.
///   - An empty body `{}` (the trusted `external_body` body).
///   - Stamped attributes: `#[vcheck]`, `#[verifier::external_body]`,
///     `#[allow(dead_code, non_snake_case)]`.
///
/// Returns `None` when the source fn is not in `FnMode::Proof` or
/// `FnMode::ProofAxiom`. The caller stripper should have ensured that
/// before calling.
///
/// The wrapper ident is the original ident prefixed with `__vcheck_axiom_` so
/// rust sees a distinct fn (the original proof fn is preserved so the
/// verifier still uses it).
pub fn synthesize_vcheck_wrapper_from_proof_fn(
    item_fn: &verus_syn::ItemFn,
) -> Option<verus_syn::ItemFn> {
    use verus_syn::token::Brace;
    use verus_syn::{Block, FnMode, ModeExec, Signature, Token};

    // Only accept proof/axiom shapes. Plain `Exec` or `Spec` fns shouldn't
    // be `#[vcheck_axiom]`-marked; if they are, surface as no-op so the
    // verifier sees the original unchanged. A future diagnostic could
    // catch this earlier.
    match &item_fn.sig.mode {
        FnMode::Proof(_) | FnMode::ProofAxiom(_) => {}
        _ => return None,
    }

    let wrapper_ident = format_ident!("__vcheck_axiom_{}", item_fn.sig.ident);

    // Strip `#[trigger]` attributes from each expression inside requires /
    // ensures. The contract rewriter at harness emission time evaluates
    // each predicate as a runtime expression; `#[trigger]` is a `[NestedMeta]`
    // attribute valid inside spec context only, and `quote!`-ing it into
    // proptest's `prop_assert!` arguments produces invalid Rust.
    let mut spec = item_fn.sig.spec.clone();
    if let Some(req) = &mut spec.requires {
        for e in req.exprs.exprs.iter_mut() {
            strip_trigger_attrs_in_expr(e);
        }
    }
    if let Some(ens) = &mut spec.ensures {
        for e in ens.exprs.exprs.iter_mut() {
            strip_trigger_attrs_in_expr(e);
        }
    }
    // Drop `decreases` (proof-only termination machinery). The harness
    // doesn't recurse; no termination obligation applies.
    spec.decreases = None;
    // Drop `recommends` (spec-only hints). The harness doesn't enforce
    // them; the SMT solver does at the original proof fn site.
    spec.recommends = None;

    let sig = Signature {
        publish: verus_syn::Publish::Default,
        constness: item_fn.sig.constness,
        asyncness: item_fn.sig.asyncness,
        unsafety: item_fn.sig.unsafety,
        abi: item_fn.sig.abi.clone(),
        // Strip `broadcast` — only proof/axiom items broadcast, and the
        // wrapper is exec.
        broadcast: None,
        mode: FnMode::Exec(ModeExec {
            exec_token: Token![exec](proc_macro2::Span::call_site()),
        }),
        fn_token: item_fn.sig.fn_token,
        ident: wrapper_ident,
        generics: item_fn.sig.generics.clone(),
        paren_token: item_fn.sig.paren_token,
        inputs: item_fn.sig.inputs.clone(),
        spec,
        variadic: item_fn.sig.variadic.clone(),
        output: item_fn.sig.output.clone(),
    };

    // Empty trusted body. The harness emitter never executes it (the
    // outer `external_body` annotation tells Verus to treat the body as
    // opaque); proptest only checks the ensures clauses against sampled
    // inputs.
    let block = Block {
        brace_token: Brace::default(),
        stmts: Vec::new(),
    };

    let vcheck_attr: Attribute = {
        // If the source `#[vcheck_axiom(K = V, ...)]` carried substitution
        // args, propagate them as `#[vcheck(K = V, ...)]` so the engine
        // monomorphizes the wrapper with the same instantiation.
        let subst_attr = item_fn
            .attrs
            .iter()
            .find(|a| attr_is(a, "vcheck_axiom"))
            .cloned();
        match subst_attr {
            Some(orig) => {
                // Replace the path segment `vcheck_axiom` -> `vcheck`.
                let tokens = match &orig.meta {
                    Meta::List(list) => list.tokens.clone(),
                    _ => proc_macro2::TokenStream::new(),
                };
                if tokens.is_empty() {
                    verus_syn::parse_quote! { #[vcheck] }
                } else {
                    verus_syn::parse_quote! { #[vcheck( #tokens )] }
                }
            }
            None => verus_syn::parse_quote! { #[vcheck] },
        }
    };
    let ext_body: Attribute = verus_syn::parse_quote! { #[verifier::external_body] };
    let allow_attr: Attribute = verus_syn::parse_quote! { #[allow(dead_code, non_snake_case)] };
    let attrs = vec![vcheck_attr, ext_body, allow_attr];

    Some(verus_syn::ItemFn {
        attrs,
        vis: item_fn.vis.clone(),
        sig,
        block: Box::new(block),
        semi_token: None,
    })
}

/// Synthesize a monomorphizing `#[vcheck]` wrapper from a *generic exec fn*
/// carrying `#[vcheck(K = V, ...)]`. Substituting into the fn item itself
/// (the previous behavior) breaks every generic caller of the fn, so —
/// exactly like `synthesize_vcheck_wrapper_from_assume_spec` — we synthesize
/// a parallel `#[verifier::external_body]` wrapper with the same generics,
/// params, and contract, whose trusted body calls the original with an
/// explicit turbofish (`orig::<K, ...>(args)`). The `#[vcheck(...)]` marker
/// moves to the wrapper; the original keeps its generics and stays
/// available to callers. The later `substitute_item` pass monomorphizes
/// the wrapper's signature and rewrites the turbofish in its body
/// (`visit_expr_path_mut` substitutes generic args in expression paths).
///
/// Returns `None` for shapes the synthesis can't handle: receivers
/// (impl methods take a different path) and parameter patterns other than
/// plain idents or `Tracked(x)` / `Ghost(x)` bindings.
///
/// Two internal paths:
/// - fns with `Tracked(x)`/`Ghost(x)` params use a direct synthesis that
///   rebuilds the permission constructors at the call site;
/// - everything else delegates to
///   `synthesize_vcheck_wrapper_from_assume_spec` via a synthetic
///   `AssumeSpecification` whose path carries the turbofish — inheriting
///   its `&Container`-param and reference-return adaptations.
pub fn synthesize_vcheck_wrapper_from_generic_exec_fn(
    item_fn: &verus_syn::ItemFn,
) -> Option<verus_syn::ItemFn> {
    use verus_syn::token::Brace;
    use verus_syn::{
        Block, Expr, FnArgKind, FnMode, GenericParam, ModeExec, Pat, Signature, Stmt, Token,
    };

    // Only exec-mode (or default-mode) fns.
    match &item_fn.sig.mode {
        FnMode::Exec(_) | FnMode::Default => {}
        _ => return None,
    }
    // Must actually have type/const params (else in-place subst is a no-op
    // and the ordinary path is fine).
    let has_ty_or_const = item_fn
        .sig
        .generics
        .params
        .iter()
        .any(|p| matches!(p, GenericParam::Type(_) | GenericParam::Const(_)));
    if !has_ty_or_const {
        return None;
    }

    // Delegation path: no receiver, no Tracked/Ghost patterns — build a
    // synthetic assume_specification and reuse its synthesizer (which
    // adapts `&Container` params and materializes reference returns).
    let has_tracked_pattern = item_fn.sig.inputs.iter().any(|arg| {
        matches!(&arg.kind, FnArgKind::Typed(pt) if matches!(pt.pat.as_ref(), Pat::TupleStruct(_)))
    });
    let has_receiver = item_fn
        .sig
        .inputs
        .iter()
        .any(|arg| matches!(&arg.kind, FnArgKind::Receiver(_)));
    if has_receiver {
        return None;
    }
    if !has_tracked_pattern {
        // Turbofish path: `name::<T, N, ...>` in declaration order.
        let orig_ident = &item_fn.sig.ident;
        let mut tf_args: Vec<proc_macro2::TokenStream> = Vec::new();
        for p in item_fn.sig.generics.params.iter() {
            match p {
                GenericParam::Type(tp) => {
                    let id = &tp.ident;
                    tf_args.push(quote! { #id });
                }
                GenericParam::Const(cp) => {
                    let id = &cp.ident;
                    tf_args.push(quote! { #id });
                }
                GenericParam::Lifetime(_) => {}
            }
        }
        let path: verus_syn::Path = if tf_args.is_empty() {
            verus_syn::parse_quote! { #orig_ident }
        } else {
            verus_syn::parse_quote! { #orig_ident::<#(#tf_args),*> }
        };
        let mut spec = item_fn.sig.spec.clone();
        if let Some(req) = &mut spec.requires {
            for e in req.exprs.exprs.iter_mut() {
                strip_trigger_attrs_in_expr(e);
            }
        }
        if let Some(ens) = &mut spec.ensures {
            for e in ens.exprs.exprs.iter_mut() {
                strip_trigger_attrs_in_expr(e);
            }
        }
        let marker_attrs: Vec<Attribute> = item_fn
            .attrs
            .iter()
            .filter(|a| attr_is(a, "vcheck") || attr_is(a, "vcheck_provide"))
            .cloned()
            .collect();
        let synthetic = verus_syn::AssumeSpecification {
            attrs: marker_attrs,
            vis: verus_syn::Visibility::Inherited,
            assume_specification: Default::default(),
            generics: item_fn.sig.generics.clone(),
            bracket_token: Default::default(),
            qself: None,
            path,
            inputs: Some((Default::default(), item_fn.sig.inputs.clone())),
            output: item_fn.sig.output.clone(),
            requires: spec.requires.clone(),
            ensures: spec.ensures.clone(),
            default_ensures: None,
            returns: spec.returns.clone(),
            invariants: None,
            unwind: None,
            semi: Default::default(),
        };
        let mut wrapper = synthesize_vcheck_wrapper_from_assume_spec(&synthetic)?;
        // Rename `__vcheck_assume_<name>` -> `__vcheck_mono_<name>` so the
        // harness name records the mono-wrapper provenance.
        wrapper.sig.ident = format_ident!("__vcheck_mono_{}", orig_ident);
        // Unsafe originals: wrap the trusted body in an unsafe block.
        if item_fn.sig.unsafety.is_some() {
            let old_block = wrapper.block.clone();
            wrapper.block = Box::new(verus_syn::parse_quote! {{ unsafe #old_block }});
        }
        return Some(wrapper);
    }

    // Build the turbofish: type/const params in declaration order
    // (lifetimes omitted; they're inferred at the call).
    let mut turbofish_args: Vec<proc_macro2::TokenStream> = Vec::new();
    for p in item_fn.sig.generics.params.iter() {
        match p {
            GenericParam::Type(tp) => {
                let id = &tp.ident;
                turbofish_args.push(quote! { #id });
            }
            GenericParam::Const(cp) => {
                let id = &cp.ident;
                turbofish_args.push(quote! { #id });
            }
            GenericParam::Lifetime(_) => {}
        }
    }

    // Tracked/Ghost path: direct synthesis rebuilding the permission
    // constructors at the call site.
    let mut call_args: Vec<Expr> = Vec::new();
    for arg in item_fn.sig.inputs.iter() {
        match &arg.kind {
            FnArgKind::Receiver(_) => return None,
            FnArgKind::Typed(pt) => match pt.pat.as_ref() {
                Pat::Ident(pi) => {
                    let id = &pi.ident;
                    call_args.push(verus_syn::parse_quote! { #id });
                }
                // `Tracked(x): Tracked<..>` / `Ghost(x): Ghost<..>`
                // patterns: rebuild the constructor at the call site,
                // like the handwritten permission wrappers do.
                Pat::TupleStruct(ts) if ts.elems.len() == 1 => {
                    let ctor = &ts.path;
                    let inner = ts.elems.first().unwrap();
                    if let Pat::Ident(pi) = inner {
                        let id = &pi.ident;
                        call_args.push(verus_syn::parse_quote! { #ctor(#id) });
                    } else {
                        return None;
                    }
                }
                _ => return None,
            },
        }
    }

    let orig_ident = &item_fn.sig.ident;
    let wrapper_ident = format_ident!("__vcheck_mono_{}", orig_ident);
    let call_expr: Expr = verus_syn::parse_quote! {
        #orig_ident::<#(#turbofish_args),*>(#(#call_args),*)
    };
    // Unsafe originals get an unsafe block; the wrapper itself stays safe
    // (its body is trusted anyway under external_body).
    let call_expr: Expr = if item_fn.sig.unsafety.is_some() {
        verus_syn::parse_quote! { unsafe { #call_expr } }
    } else {
        call_expr
    };

    // Contract: same requires/ensures, minus proof-only machinery.
    let mut spec = item_fn.sig.spec.clone();
    if let Some(req) = &mut spec.requires {
        for e in req.exprs.exprs.iter_mut() {
            strip_trigger_attrs_in_expr(e);
        }
    }
    if let Some(ens) = &mut spec.ensures {
        for e in ens.exprs.exprs.iter_mut() {
            strip_trigger_attrs_in_expr(e);
        }
    }
    spec.decreases = None;
    spec.recommends = None;
    // Wrapper doesn't unwind-spec: `no_unwind` clauses stay valid on the
    // original; keep them off the wrapper (the harness doesn't check them).
    spec.unwind = None;

    // `&X` return (shared): materialize as owned `X` via `.to_owned()` and
    // strip `*ret` derefs from the contract — same adaptation the
    // delegation path inherits from the assume-spec synthesizer. `&mut`
    // returns stay unsupported (write-through unobservable).
    let mut output = item_fn.sig.output.clone();
    let mut call_expr = call_expr;
    if let verus_syn::ReturnType::Type(arrow, tracked, ret_pat, ty) = &item_fn.sig.output {
        if let Type::Reference(rty) = ty.as_ref() {
            if rty.mutability.is_none() {
                if let Type::Path(tp) = rty.elem.as_ref() {
                    if tp.qself.is_none()
                        && tp.path.segments.len() == 1
                        && matches!(tp.path.segments[0].arguments, PathArguments::None)
                    {
                        let inner = (*rty.elem).clone();
                        output = verus_syn::ReturnType::Type(
                            arrow.clone(),
                            tracked.clone(),
                            ret_pat.clone(),
                            Box::new(inner),
                        );
                        call_expr = verus_syn::parse_quote! { (#call_expr).to_owned() };
                        if let Some(boxed) = ret_pat {
                            if let Pat::Ident(pi) = &boxed.1 {
                                let name = pi.ident.to_string();
                                struct StripDeref<'a> {
                                    name: &'a str,
                                }
                                impl<'a> verus_syn::visit_mut::VisitMut for StripDeref<'a> {
                                    fn visit_expr_mut(&mut self, e: &mut Expr) {
                                        if let Expr::Unary(u) = e {
                                            if matches!(u.op, verus_syn::UnOp::Deref(_)) {
                                                if let Expr::Path(p) = u.expr.as_ref() {
                                                    if p.qself.is_none()
                                                        && p.path.segments.len() == 1
                                                        && p.path.segments[0].ident == self.name
                                                    {
                                                        *e = (*u.expr).clone();
                                                        return;
                                                    }
                                                }
                                            }
                                        }
                                        verus_syn::visit_mut::visit_expr_mut(self, e);
                                    }
                                }
                                let mut v = StripDeref { name: &name };
                                if let Some(req) = &mut spec.requires {
                                    for e in req.exprs.exprs.iter_mut() {
                                        verus_syn::visit_mut::VisitMut::visit_expr_mut(&mut v, e);
                                    }
                                }
                                if let Some(ens) = &mut spec.ensures {
                                    for e in ens.exprs.exprs.iter_mut() {
                                        verus_syn::visit_mut::VisitMut::visit_expr_mut(&mut v, e);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    let sig = Signature {
        publish: verus_syn::Publish::Default,
        constness: None,
        asyncness: None,
        unsafety: None,
        abi: None,
        broadcast: None,
        mode: FnMode::Exec(ModeExec {
            exec_token: Token![exec](proc_macro2::Span::call_site()),
        }),
        fn_token: item_fn.sig.fn_token,
        ident: wrapper_ident,
        generics: item_fn.sig.generics.clone(),
        paren_token: item_fn.sig.paren_token,
        inputs: item_fn.sig.inputs.clone(),
        spec,
        variadic: None,
        output,
    };

    let block = Block {
        brace_token: Brace::default(),
        stmts: vec![Stmt::Expr(call_expr, None)],
    };

    // Move the marker (with its subst tokens) onto the wrapper.
    let vcheck_attr: Attribute = {
        let orig = item_fn.attrs.iter().find(|a| attr_is(a, "vcheck")).cloned();
        match orig {
            Some(a) => {
                let tokens = match &a.meta {
                    Meta::List(list) => list.tokens.clone(),
                    _ => proc_macro2::TokenStream::new(),
                };
                if tokens.is_empty() {
                    verus_syn::parse_quote! { #[vcheck] }
                } else {
                    verus_syn::parse_quote! { #[vcheck( #tokens )] }
                }
            }
            None => verus_syn::parse_quote! { #[vcheck] },
        }
    };
    let ext_body: Attribute = verus_syn::parse_quote! { #[verifier::external_body] };
    let allow_attr: Attribute = verus_syn::parse_quote! { #[allow(dead_code, non_snake_case)] };
    let attrs = vec![vcheck_attr, ext_body, allow_attr];

    Some(verus_syn::ItemFn {
        attrs,
        vis: verus_syn::Visibility::Inherited,
        sig,
        block: Box::new(block),
        semi_token: None,
    })
}

/// Visit an `Expr` and remove any leading `#[trigger]` attributes (and
/// `#![trigger ...]` inner attrs) from the expression itself and any of
/// its sub-expressions. The Verus SMT solver consumes triggers; at the
/// runtime harness level they're noise that proptest can't parse.
///
/// We use a `VisitMut` rather than the existing `ContractRewriter`
/// machinery because the strip needs to happen *before*
/// the wrapper item gets fed back into the engine — at that point the
/// `Expr` nodes are still raw and not yet inside a `verus_spec_check_unverified!`
/// engine block.
pub fn strip_trigger_attrs_in_expr(e: &mut Expr) {
    use verus_syn::visit_mut::{visit_expr_mut, VisitMut};
    struct R;
    impl VisitMut for R {
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            if let Some(attrs) = expr_attrs_mut(e) {
                attrs.retain(|a| !attr_is(a, "trigger"));
            }
            verus_syn::visit_mut::visit_expr_mut(self, e);
        }
    }
    R.visit_expr_mut(e);
    // Also strip inner `#![trigger ...]` attrs if present at this level.
    if let Some(attrs) = expr_attrs_mut(e) {
        attrs.retain(|a| !attr_is(a, "trigger"));
    }
    let _ = visit_expr_mut::<R>;
}

/// Return mutable access to the outer attribute slice of an `Expr`. Only
/// expression kinds that carry attributes return `Some`; for kinds without
/// an `attrs` field this returns `None`.
pub fn expr_attrs_mut(e: &mut Expr) -> Option<&mut Vec<Attribute>> {
    match e {
        Expr::Array(x) => Some(&mut x.attrs),
        Expr::Assign(x) => Some(&mut x.attrs),
        Expr::Async(x) => Some(&mut x.attrs),
        Expr::Await(x) => Some(&mut x.attrs),
        Expr::Binary(x) => Some(&mut x.attrs),
        Expr::Block(x) => Some(&mut x.attrs),
        Expr::Break(x) => Some(&mut x.attrs),
        Expr::Call(x) => Some(&mut x.attrs),
        Expr::Cast(x) => Some(&mut x.attrs),
        Expr::Closure(x) => Some(&mut x.attrs),
        Expr::Const(x) => Some(&mut x.attrs),
        Expr::Continue(x) => Some(&mut x.attrs),
        Expr::Field(x) => Some(&mut x.attrs),
        Expr::ForLoop(x) => Some(&mut x.attrs),
        Expr::Group(x) => Some(&mut x.attrs),
        Expr::If(x) => Some(&mut x.attrs),
        Expr::Index(x) => Some(&mut x.attrs),
        Expr::Infer(x) => Some(&mut x.attrs),
        Expr::Let(x) => Some(&mut x.attrs),
        Expr::Lit(x) => Some(&mut x.attrs),
        Expr::Loop(x) => Some(&mut x.attrs),
        Expr::Macro(x) => Some(&mut x.attrs),
        Expr::Match(x) => Some(&mut x.attrs),
        Expr::MethodCall(x) => Some(&mut x.attrs),
        Expr::Paren(x) => Some(&mut x.attrs),
        Expr::Path(x) => Some(&mut x.attrs),
        Expr::Range(x) => Some(&mut x.attrs),
        Expr::Reference(x) => Some(&mut x.attrs),
        Expr::Repeat(x) => Some(&mut x.attrs),
        Expr::Return(x) => Some(&mut x.attrs),
        Expr::Struct(x) => Some(&mut x.attrs),
        Expr::Try(x) => Some(&mut x.attrs),
        Expr::TryBlock(x) => Some(&mut x.attrs),
        Expr::Tuple(x) => Some(&mut x.attrs),
        Expr::Unary(x) => Some(&mut x.attrs),
        Expr::Unsafe(x) => Some(&mut x.attrs),
        Expr::While(x) => Some(&mut x.attrs),
        Expr::Yield(x) => Some(&mut x.attrs),
        _ => None,
    }
}

/// Recover the receiver type for a method-shaped assume_specification path.
pub fn simple_pat_ident(pat: &verus_syn::Pat) -> Option<Ident> {
    use verus_syn::Pat;
    match pat {
        Pat::Ident(pi) => Some(pi.ident.clone()),
        Pat::Type(pt) => simple_pat_ident(&pt.pat),
        _ => None,
    }
}

/// Recover the receiver type for a method-shaped assume_specification path.
/// `Vec::<T>::push` -> `Vec::<T>`. `<Vec<T> as Clone>::clone` -> `Vec<T>`
/// (recovered from the qself).
pub fn recover_receiver_type(asp: &verus_syn::AssumeSpecification) -> Type {
    if let Some(qself) = &asp.qself {
        return (*qself.ty).clone();
    }
    // Drop the last path segment and reconstitute as a Type.
    let mut path = asp.path.clone();
    if path.segments.len() >= 2 {
        // Pop the last segment; rebuild the punctuated list because there's
        // no public API to flush trailing punctuation cleanly.
        let mut segs: Vec<verus_syn::PathSegment> = path.segments.iter().cloned().collect();
        segs.pop();
        path.segments = segs.into_iter().collect();
    }
    Type::Path(verus_syn::TypePath { qself: None, path })
}

/// Diagnostic for a body-less / `uninterp spec fn` reached from a `#[vcheck]`
/// closure. The exec_spec engine cannot generate a runnable companion for
/// it, so the harness has nothing to evaluate the contract against.
pub fn uninterp_spec_message(qualified_name: &str) -> String {
    format!(
        "verus_spec_check: the spec function `{name}` has no body (it is `uninterp` or otherwise \
body-less), so the engine cannot generate a runnable `exec_*` companion for it.\n\
\n\
A `#[vcheck]` contract that reaches an uninterpreted spec fn cannot be property-tested: \
proptest needs an executable definition to evaluate the requires/ensures clauses against.\n\
\n\
Resolve it at the first applicable tier:\n\
\u{20} 1. Replace the `uninterp spec fn` with an `open spec fn` that has a body, when you can \
provide one;\n\
\u{20} 2. Or wrap the property test so it does not depend on the uninterp spec fn (rewrite \
the `#[vcheck]` contract to use only spec fns with bodies);\n\
\u{20} 3. Or supply a trusted exec stub next to your `#[vcheck]` fn:\n\
\u{20}      external_vcheck_provide! {{ fn {name}(/* args */) -> /* ret */ {{ /* exec body */ }} }}\n\
\u{20}    The trusted body is `#[cfg(test)]`-only and never participates in verification.",
        name = qualified_name
    )
}

#[cfg(test)]
mod vcheck_axiom_tests {
    use super::synthesize_vcheck_wrapper_from_proof_fn;
    use quote::quote;
    use verus_syn::parse_quote;

    /// `#[vcheck_axiom]` on a `broadcast proof fn` should produce a sibling
    /// exec wrapper named `__vcheck_axiom_<original>` with the same params
    /// and ensures, `FnMode::Exec`, and an empty body.
    #[test]
    fn proof_fn_wrapper_basic() {
        let f: verus_syn::ItemFn = parse_quote! {
            pub broadcast proof fn ax(x: u32)
                ensures x as int + 0 == x as int,
            {}
        };
        let w = synthesize_vcheck_wrapper_from_proof_fn(&f).expect("wrapper synthesized");
        assert_eq!(w.sig.ident, "__vcheck_axiom_ax");
        // Block must be empty (trusted external_body).
        assert!(w.block.stmts.is_empty());
        // Decreases stripped — proof-only.
        assert!(w.sig.spec.decreases.is_none());
        // Broadcast stripped (the wrapper is a plain exec fn).
        assert!(w.sig.broadcast.is_none());
        // Mode lowered to Exec.
        assert!(matches!(w.sig.mode, verus_syn::FnMode::Exec(_)));
        // The wrapper should have the marker attrs we stamp.
        let attr_strs: Vec<String> = w.attrs.iter().map(|a| quote!(#a).to_string()).collect();
        let joined = attr_strs.join(" ");
        assert!(joined.contains("vcheck"));
        assert!(joined.contains("external_body"));
    }

    /// `#[vcheck_axiom]` on a `broadcast axiom fn` (no body, semicolon-
    /// terminated) should also produce a wrapper. Same conditions as
    /// the proof-fn case.
    #[test]
    fn axiom_fn_wrapper_basic() {
        let f: verus_syn::ItemFn = parse_quote! {
            pub broadcast axiom fn ax(x: u8)
                ensures x as int >= 0,
            {}
        };
        let w = synthesize_vcheck_wrapper_from_proof_fn(&f).expect("wrapper synthesized");
        assert_eq!(w.sig.ident, "__vcheck_axiom_ax");
        assert!(matches!(w.sig.mode, verus_syn::FnMode::Exec(_)));
    }

    /// `#[vcheck_axiom(T = u8, N = 4)]` on a generic proof fn should
    /// propagate the substitution into the synthesized wrapper's
    /// `#[vcheck(T = u8, N = 4)]` attribute so the engine's
    /// monomorphization path picks it up.
    #[test]
    fn proof_fn_wrapper_carries_subst_attr() {
        let f: verus_syn::ItemFn = parse_quote! {
            #[vcheck_axiom(T = u8, N = 4)]
            pub broadcast axiom fn ax<T, const N: usize>(a: [T; N])
                ensures true,
            {}
        };
        let w = synthesize_vcheck_wrapper_from_proof_fn(&f).expect("wrapper synthesized");
        let attr_strs: Vec<String> = w.attrs.iter().map(|a| quote!(#a).to_string()).collect();
        let joined = attr_strs.join(" ");
        // The wrapper's `#[vcheck(...)]` should carry over the
        // `T = u8 , N = 4` substitution. Token-level check tolerates
        // whitespace variations from `quote!`.
        assert!(joined.contains("vcheck"));
        assert!(joined.contains("T = u8"));
        assert!(joined.contains("N = 4"));
    }

    /// `#[vcheck_axiom]` on a plain exec fn must return `None` — the
    /// wrapper synthesis is only meaningful for proof / axiom fns.
    #[test]
    fn rejects_exec_fn() {
        let f: verus_syn::ItemFn = parse_quote! {
            pub exec fn not_an_axiom(x: u32) -> u32 { x }
        };
        assert!(synthesize_vcheck_wrapper_from_proof_fn(&f).is_none());
    }
}

#[cfg(test)]
mod ref_container_adaptation_tests {
    //! Fix coverage: `&BTreeMap` / `&BTreeSet` / `&VecDeque` params adapt
    //! to owned form (like `&Vec` / `&HashMap`), and `&[T]` returns from
    //! adapted-param wrappers materialize an owned `Vec<T>` via
    //! `.to_owned()` instead of emitting a lifetime-less `&[T]`.
    use super::*;
    use quote::quote;
    use verus_syn::parse_quote;

    fn get_assume_spec(item: &Item) -> &verus_syn::AssumeSpecification {
        match item {
            Item::AssumeSpecification(a) => a,
            _ => panic!("expected assume_specification"),
        }
    }

    #[test]
    fn assume_spec_wrapper_is_always_inline_never() {
        let item: Item = parse_quote! {
            #[inline(always)]
            #[vcheck(Key = u32, Value = u32)]
            pub assume_specification<Key, Value>[ BTreeMap::<Key, Value>::is_empty ](
                map: &BTreeMap<Key, Value>,
            ) -> (res: bool)
                ensures
                    res == map@.is_empty(),
            ;
        };
        let wrapper = synthesize_vcheck_wrapper_from_assume_spec(get_assume_spec(&item))
            .expect("wrapper synthesized");
        let attrs = wrapper
            .attrs
            .iter()
            .map(|attr| quote!(#attr).to_string())
            .collect::<Vec<_>>()
            .join(" ");
        assert!(
            attrs.contains("inline (never)"),
            "missing inline-never: {attrs}"
        );
        assert!(
            !attrs.contains("inline (always)"),
            "source inline attribute leaked: {attrs}"
        );
    }

    /// `&BTreeMap<K, V>` param: the wrapper's param becomes the owned
    /// `BTreeMap<K, V>` and the call site borrows it.
    #[test]
    fn btree_map_ref_param_adapts_to_owned() {
        let item: Item = parse_quote! {
            #[vcheck(Key = u32, Value = u32)]
            pub assume_specification<Key, Value>[ BTreeMap::<Key, Value>::is_empty ](
                m: &BTreeMap<Key, Value>,
            ) -> (res: bool)
                ensures
                    res == m@.is_empty(),
            ;
        };
        let asp = get_assume_spec(&item);
        let w = synthesize_vcheck_wrapper_from_assume_spec(asp)
            .expect("wrapper synthesized for &BTreeMap param");
        let text = quote!(#w).to_string();
        assert!(
            text.contains("m : BTreeMap"),
            "&BTreeMap param should adapt to owned BTreeMap: {text}"
        );
        assert!(
            text.contains("& m"),
            "call site should borrow the owned param: {text}"
        );
    }

    /// `&Vec<T>` param with a `&[T]` return (`Vec::as_slice`): the return
    /// type must rewrite to the owned `Vec<T>` with a `.to_owned()`
    /// materialization (previously emitted a lifetime-less `&[T]`, E0106).
    #[test]
    fn slice_return_materializes_owned_vec() {
        let item: Item = parse_quote! {
            #[vcheck(T = u32)]
            pub assume_specification<T>[ Vec::<T>::as_slice ](
                vec: &Vec<T>,
            ) -> (slice: &[T])
                ensures
                    slice@ == vec@,
            ;
        };
        let asp = get_assume_spec(&item);
        let w = synthesize_vcheck_wrapper_from_assume_spec(asp)
            .expect("wrapper synthesized for &[T] return");
        let text = quote!(#w).to_string();
        assert!(
            text.contains("Vec < T >") || text.contains("Vec<T>"),
            "return should rewrite to owned Vec<T>: {text}"
        );
        assert!(
            text.contains("to_owned"),
            "body should materialize via .to_owned(): {text}"
        );
        assert!(
            !text.contains("-> (slice : & ["),
            "return must not stay a bare &[T]: {text}"
        );
    }
}

#[cfg(test)]
mod allocator_generic_diag {
    //! Diagnostic tests: an `assume_specification` on an allocator-generic
    //! method (`<T, A: Allocator>`) with a full `#[vcheck(T = .., A = ..)]`
    //! instantiation should produce a monomorphic synthesized wrapper, the
    //! same way the single-`<T>` Option/Result specs do.
    use super::*;
    use verus_syn::parse_quote;

    fn get_assume_spec(item: &Item) -> &verus_syn::AssumeSpecification {
        match item {
            Item::AssumeSpecification(a) => a,
            _ => panic!("expected assume_specification"),
        }
    }

    /// Sanity: the wrapper synthesis itself succeeds for an allocator-generic
    /// `&mut Vec<T, A>` receiver-less spec.
    #[test]
    fn synth_wrapper_for_allocator_generic() {
        let item: Item = parse_quote! {
            #[vcheck(T = u32, A = core::alloc::Global, backend = "bolero")]
            pub assume_specification<T, A: Allocator>[ Vec::<T, A>::swap_remove ](
                vec: &mut Vec<T, A>,
                i: usize,
            ) -> (element: T)
                ensures
                    element == old(vec)[i as int],
            ;
        };
        let asp = get_assume_spec(&item);
        let w = synthesize_vcheck_wrapper_from_assume_spec(asp);
        assert!(
            w.is_some(),
            "wrapper synthesis returned None for allocator-generic spec"
        );
    }

    fn preprocess_dump(items_ts: proc_macro2::TokenStream) -> String {
        let file: verus_syn::File = verus_syn::parse2(items_ts).expect("parse file");
        let mut items = file.items;
        vcheck_provide_preprocess(&mut items);
        let mut out = String::new();
        for it in &items {
            out.push_str(&quote::quote!(#it).to_string());
            out.push_str("\n=====\n");
        }
        out
    }

    /// End-to-end preprocess: the folded engine block should contain a
    /// monomorphic `__vcheck_assume_*` wrapper (T and A substituted away).
    #[test]
    fn preprocess_monomorphizes_allocator_generic() {
        let dump = preprocess_dump(quote::quote! {
            #[vcheck(T = u32, A = core::alloc::Global, backend = "bolero")]
            pub assume_specification<T, A: Allocator>[ Vec::<T, A>::swap_remove ](
                vec: &mut Vec<T, A>,
                i: usize,
            ) -> (element: T)
                ensures
                    element == old(vec)[i as int],
            ;
        });
        assert!(
            dump.contains("__vcheck_assume"),
            "no __vcheck_assume wrapper in folded output"
        );
        // Both generic params (T and A) must be substituted away.
        assert!(
            dump.contains("Vec < u32 , core :: alloc :: Global >"),
            "wrapper not monomorphized: {dump}"
        );
    }

    /// Contrast baseline: single-`<T>` Option-shaped spec (known to work).
    #[test]
    fn preprocess_monomorphizes_single_type_param() {
        let dump = preprocess_dump(quote::quote! {
            #[vcheck(T = u32, backend = "bolero")]
            pub assume_specification<T>[ Option::<T>::is_some ](option: &Option<T>) -> (b: bool)
                ensures
                    b == option.is_some(),
            ;
        });
        assert!(
            dump.contains("__vcheck_assume"),
            "no __vcheck_assume wrapper in folded output"
        );
    }
}
