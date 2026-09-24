use super::*;

/// Conflict info for diagnostics: which sibling item, and the two
/// disagreeing instantiations encountered.
#[derive(Debug)]
pub struct InstantiationConflict {
    pub item_idx: usize,
    pub item_name: String,
    pub first: Subst,
    pub second: Subst,
}

/// Result of the generics-aware closure pass.
pub struct ClosureResult {
    /// Per-item subst (empty for non-generic items).
    pub chosen: HashMap<usize, Subst>,
    /// Disagreeing instantiations encountered during the walk.
    pub conflicts: Vec<InstantiationConflict>,
}

/// Build a substitution from a positional list of concrete type args,
/// mapping the callee's type-param names to those args. If `args` is
/// shorter than `params`, fall back to inheriting the caller's binding by
/// matching param names (so `nonzero<T>(...)` reached from `check<T = u32>`
/// inherits `T = u32` even when the callsite has no turbofish).
pub fn subst_from_args(params: &[Ident], args: &[Type], caller_subst: &Subst) -> Subst {
    let mut map = HashMap::new();
    for (i, p) in params.iter().enumerate() {
        let key = p.to_string();
        if let Some(a) = args.get(i) {
            let mut resolved = a.clone();
            substitute_type(&mut resolved, caller_subst);
            map.insert(key, resolved);
        } else if let Some(t) = caller_subst.map.get(&key) {
            map.insert(key, t.clone());
        }
    }
    // Propagate the caller's const-generic substitutions verbatim — there
    // is no positional `args`-style binding for const generics in our
    // closure walk yet (we don't track the path of the call's turbofish
    // const args), so the safest and most useful behavior is to inherit
    // the caller's consts unchanged. When const generics are used by name
    // inside the callee item, the inherited map drives them to the same
    // value as in the caller.
    let consts = caller_subst.consts.clone();
    Subst { map, consts }
}

/// Generics-aware closure: like `compute_closure` but propagates
/// substitutions along the call/reference graph. The return preserves a
/// per-item subst so the engine emits monomorphized versions of generic
/// items folded by `#[vcheck]` callsites.
pub fn compute_closure_with_substs(
    seeds: Vec<(String, Vec<Type>, Subst)>,
    externally_provided: &HashSet<String>,
    items: &[Item],
    index: &SiblingIndex,
) -> ClosureResult {
    let mut chosen: HashMap<usize, Subst> = HashMap::new();
    let mut conflicts: Vec<InstantiationConflict> = Vec::new();
    let mut chosen_types: HashSet<String> = HashSet::new();
    // Worklist entries: (name, callsite type-args, caller subst).
    let mut worklist: Vec<(String, Vec<Type>, Subst)> = seeds;
    // Already-explored (name, subst-fingerprint) pairs.
    let mut seen: HashSet<(String, String)> = HashSet::new();

    while let Some((name, args, caller)) = worklist.pop() {
        // Resource-native names (PPtr / PointsTo / ...) are handled by the
        // harness emitter's linear-resource path, never by sibling folding
        // (see `is_resource_native_ident`).
        if is_resource_native_ident(&name) {
            continue;
        }
        // Routed spec carriers (Seq/Set/Map/Multiset): the exec_spec
        // rewriter lowers their method calls to runtime exec models, so
        // their sibling definitions must not be folded (see
        // `is_routed_spec_carrier`).
        if is_routed_spec_carrier(&name) {
            continue;
        }
        // Resolve args under caller subst before further use.
        let resolved_args: Vec<Type> = args
            .iter()
            .map(|t| resolve_type_under(t, &caller))
            .collect();
        let key = (name.clone(), {
            let s = Subst {
                map: caller.map.clone(),
                consts: caller.consts.clone(),
            };
            s.render()
        });
        if !seen.insert(key) {
            continue;
        }

        // Option 1 (see `compute_closure`): an `external_vcheck_provide!` stub
        // overrides sibling folding — don't fold `name`'s definition here
        // either.
        if externally_provided.contains(&name) {
            continue;
        }

        // Try to resolve as a sibling type.
        if let Some(&def_idx) = index.type_defs.get(&name) {
            let params = index
                .type_params_by_idx
                .get(&def_idx)
                .cloned()
                .unwrap_or_default();
            let new_subst = subst_from_args(&params, &resolved_args, &caller);
            record_subst(
                def_idx,
                &name,
                new_subst.clone(),
                &mut chosen,
                &mut conflicts,
            );
            chosen_types.insert(name.clone());
            // Recurse into field types under the new subst.
            let mut refs = Vec::<(String, Vec<Type>)>::new();
            collect_type_field_typed_refs(&items[def_idx], &mut refs);
            for (n, a) in refs {
                worklist.push((n, a, new_subst.clone()));
            }
            // Pull in inherent impls.
            if let Some(impl_idxs) = index.type_impls.get(&name) {
                for &ix in impl_idxs {
                    let impl_params = index
                        .type_params_by_idx
                        .get(&ix)
                        .cloned()
                        .unwrap_or_default();
                    // For an `impl<V> Stack<V>` block, the impl's params line
                    // up positionally with the type's params via the Self
                    // type's type-args. Use the new_subst (which already maps
                    // the type's params to concrete types) to derive the
                    // impl's subst.
                    let impl_subst = derive_impl_subst(&impl_params, &items[ix], &new_subst);
                    record_subst(
                        ix,
                        &format!("{} impl block", name),
                        impl_subst.clone(),
                        &mut chosen,
                        &mut conflicts,
                    );
                    let mut impl_refs = Vec::<(String, Vec<Type>)>::new();
                    collect_impl_spec_typed_refs(&items[ix], &mut impl_refs);
                    for (n, a) in impl_refs {
                        worklist.push((n, a, impl_subst.clone()));
                    }
                }
            }
        }

        // Sibling free fn.
        if let Some(&fn_idx) = index.free_fns.get(&name) {
            let params = index
                .type_params_by_idx
                .get(&fn_idx)
                .cloned()
                .unwrap_or_default();
            let new_subst = subst_from_args(&params, &resolved_args, &caller);
            record_subst(
                fn_idx,
                &name,
                new_subst.clone(),
                &mut chosen,
                &mut conflicts,
            );
            let mut refs = Vec::<(String, Vec<Type>)>::new();
            collect_fn_spec_typed_refs(&items[fn_idx], &mut refs);
            for (n, a) in refs {
                worklist.push((n, a, new_subst.clone()));
            }
        }

        // Sibling method name -> owning type(s).
        if let Some(owners) = index.method_owners.get(&name) {
            for owner in owners {
                // Method-only references propagate the *caller's* subst —
                // the method site itself has no type-args we can pin to a
                // type's params.
                worklist.push((owner.clone(), Vec::new(), caller.clone()));
            }
        }
    }

    ClosureResult { chosen, conflicts }
}

/// Record a `(idx, subst)` pair, detecting conflicts with previously-recorded
/// substs for the same idx.
pub fn record_subst(
    idx: usize,
    name: &str,
    new_subst: Subst,
    chosen: &mut HashMap<usize, Subst>,
    conflicts: &mut Vec<InstantiationConflict>,
) {
    match chosen.get(&idx) {
        Some(old) if old.agrees_with(&new_subst) => {}
        Some(old) => {
            conflicts.push(InstantiationConflict {
                item_idx: idx,
                item_name: name.to_string(),
                first: old.clone(),
                second: new_subst,
            });
        }
        None => {
            chosen.insert(idx, new_subst);
        }
    }
}

/// Given an `impl<V> Stack<V>` block and the type-level subst `{V->u64}`
/// inferred from the type def, compute the impl's subst. Walks the impl's
/// Self type, matches its type-args positionally against the type def's
/// params, and substitutes back. Conservative: if the Self type is anything
/// other than a single-segment path, returns the type's subst unchanged.
pub fn derive_impl_subst(impl_params: &[Ident], impl_item: &Item, type_subst: &Subst) -> Subst {
    let Item::Impl(im) = impl_item else {
        return type_subst.clone();
    };
    // For inherent impls, the impl's type-params are conventionally listed
    // in the same order as the type's. Just propagate the subst's keys
    // re-mapped to the impl's own param names if they differ — but since
    // verus_syn impls usually re-use the same names (`impl<V> Stack<V>`),
    // this almost always reduces to subst pass-through.
    // The robust thing: read the impl's Self type-args; for each `Type::Path`
    // arg whose name matches an impl_param, bind that impl_param to the
    // corresponding key from type_subst.
    if let Type::Path(tp) = im.self_ty.as_ref() {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let seg = &tp.path.segments[0];
            if let PathArguments::AngleBracketed(ab) = &seg.arguments {
                let args: Vec<&GenericArgument> = ab.args.iter().collect();
                let mut map = HashMap::new();
                let type_keys: Vec<String> = {
                    let mut k: Vec<String> = type_subst.map.keys().cloned().collect();
                    k.sort();
                    k
                };
                // Best-effort: assume Self's type-args are referenced in the
                // declaration order of the type's params.
                let mut concrete_for_pos: Vec<Option<Type>> = Vec::new();
                for arg in &args {
                    match arg {
                        GenericArgument::Type(Type::Path(p))
                            if p.qself.is_none()
                                && p.path.segments.len() == 1
                                && matches!(p.path.segments[0].arguments, PathArguments::None) =>
                        {
                            // Fetch type_subst entry by ident name.
                            let n = p.path.segments[0].ident.to_string();
                            concrete_for_pos.push(type_subst.map.get(&n).cloned());
                        }
                        _ => concrete_for_pos.push(None),
                    }
                }
                let _ = type_keys;
                for (p, opt) in impl_params.iter().zip(concrete_for_pos) {
                    if let Some(t) = opt {
                        map.insert(p.to_string(), t);
                    }
                }
                return Subst {
                    map,
                    consts: type_subst.consts.clone(),
                };
            }
        }
    }
    // Fallback: for impls whose params share names with the type, the type's
    // subst applies as-is.
    let mut map = HashMap::new();
    for p in impl_params {
        if let Some(t) = type_subst.map.get(&p.to_string()) {
            map.insert(p.to_string(), t.clone());
        }
    }
    Subst {
        map,
        consts: type_subst.consts.clone(),
    }
}

/// Given a set of referenced identifiers, compute the transitive closure of
/// sibling item indices to pull into the engine block: type defs, their
/// inherent impls, and free spec fns, recursing into spec-fn bodies and
/// type fields.
pub fn compute_closure(
    seed_idents: HashSet<String>,
    externally_provided: &HashSet<String>,
    items: &[Item],
    index: &SiblingIndex,
) -> HashSet<usize> {
    let mut chosen: HashSet<usize> = HashSet::new();
    let mut chosen_types: HashSet<String> = HashSet::new();
    let mut worklist: Vec<String> = seed_idents.into_iter().collect();
    let mut seen_idents: HashSet<String> = HashSet::new();

    while let Some(name) = worklist.pop() {
        if !seen_idents.insert(name.clone()) {
            continue;
        }

        // Resource-native names are handled by the harness emitter's
        // linear-resource path, never by sibling folding (see
        // `is_resource_native_ident`).
        if is_resource_native_ident(&name) {
            continue;
        }
        // Routed spec carriers: definitions never fold (see
        // `is_routed_spec_carrier`).
        if is_routed_spec_carrier(&name) {
            continue;
        }

        // Option 1: an `external_vcheck_provide!` stub takes precedence over a
        // sibling definition. If the user supplied a trusted exec twin for
        // `name`, do NOT fold the sibling spec fn (and do NOT recurse into its
        // body). This lets a `#[vcheck]` reach a spec fn whose body depends 
        // on a cross-module spec fn (which the sibling closure cannot pull), 
        // by short-circuiting at `name` with the stub. Type defs / methods of
        // the same name are unaffected (a provide names a free fn).
        if externally_provided.contains(&name) {
            continue;
        }

        // A referenced type: pull its def + all inherent impls.
        if let Some(&def_idx) = index.type_defs.get(&name) {
            if chosen.insert(def_idx) {
                // recurse into field types
                let mut refs = HashSet::new();
                collect_type_field_idents(&items[def_idx], &mut refs);
                worklist.extend(refs);
            }
            chosen_types.insert(name.clone());
            if let Some(impl_idxs) = index.type_impls.get(&name) {
                for &ix in impl_idxs {
                    if chosen.insert(ix) {
                        let mut refs = HashSet::new();
                        collect_impl_spec_idents(&items[ix], &mut refs);
                        worklist.extend(refs);
                    }
                }
            }
        }

        // A referenced free spec fn: pull it + recurse into its body.
        if let Some(&fn_idx) = index.free_fns.get(&name) {
            if chosen.insert(fn_idx) {
                let mut refs = HashSet::new();
                collect_fn_spec_idents(&items[fn_idx], &mut refs);
                worklist.extend(refs);
            }
        }

        // A referenced spec method name: pull the owning type(s) so the impl
        // (and thus the method) is included.
        if let Some(owners) = index.method_owners.get(&name) {
            for owner in owners {
                if !seen_idents.contains(owner) {
                    worklist.push(owner.clone());
                }
            }
        }
    }

    chosen
}
