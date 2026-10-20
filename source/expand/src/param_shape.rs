use super::*;

// ---------------------------------------------------------------------------
// Param / return type analysis
// ---------------------------------------------------------------------------

/// Categorisation of a parameter's type for harness-side strategy / call
/// adaptation.
#[derive(Clone, Debug)]
pub enum ParamShape {
    /// `i64`, `u8`, `bool`, `char`, ...: harness gets a `T`, call site uses
    /// `x` directly.
    Primitive(Type),
    /// `&u8`, `&i32`, `&bool`, `&char`, ... -- reference to a primitive.
    /// The harness samples the primitive by value and a pre-call `let`
    /// binding borrows it so the call-site can pass `&id`. Contracts that
    /// dereference via `*x` rewrite identically to bare `x` because the
    /// underlying value is a Copy primitive.
    RefPrimitive(Type),
    /// `Vec<E>` where `E` is a ParamElem (primitive or user-type Exec*).
    OwnedVec(ParamElem),
    /// `VecDeque<E>`. Mirrors `OwnedVec` (spec view is `Seq<E>`), but has no
    /// `as_slice()` (ring buffer), so every slice-view site materializes a
    /// contiguous `Vec` via `::verus_spec_check::__vcheck_vecdeque_slice`.
    OwnedVecDeque(ParamElem),
    /// `&[E]`.
    Slice(ParamElem),
    /// `[E; N]` -- fixed-size array. `N` is a const expression (an integer
    /// literal after substitution by `#[vcheck(N = 4)]`). The harness samples
    /// a `Vec<E>` of length `N` and converts via `core::array::from_fn`.
    OwnedArray(ParamElem, Expr),
    /// `&[E; N]` -- fixed-size array reference. Same shape as `OwnedArray`,
    /// but the call site borrows the sampled array.
    RefArray(ParamElem, Expr),
    /// `Option<E>`.
    OwnedOption(ParamElem),
    /// `Result<T, E>`. Both T and E are `ParamElem` (one level of nesting).
    OwnedResult(ParamElem, ParamElem),
    /// `HashMap<K, V>`. Both K and V are `ParamElem`.
    OwnedHashMap(ParamElem, ParamElem),
    /// `HashSet<E>`.
    OwnedHashSet(ParamElem),
    /// `BTreeMap<K, V>`. Spec view is `Map<K, V>`, identical to
    /// `OwnedHashMap`; only the harness type and the concrete exec
    /// companions differ. Routed to `MapSetKind::Map`.
    OwnedBTreeMap(ParamElem, ParamElem),
    /// `BTreeSet<E>`. Spec view is `Set<E>`, identical to `OwnedHashSet`.
    /// Routed to `MapSetKind::Set`
    OwnedBTreeSet(ParamElem),
    /// An opaque foreign type `T` with a `#[vcheck_view]` view and a
    /// `VcheckConcretize` impl (e.g. `UBig`)
    OpaqueConcretize(Ident),
    /// `Multiset<E>` -- compiles to ExecMultiset<exec(E)>.
    OwnedMultiset(ParamElem),
    /// `&UserType`.
    RefUserType(Ident),
    /// `UserType` (owned).
    OwnedUserType(Ident),
    /// `&str` -- string slice. The harness samples a `String` and passes
    /// it via `as_str()`. Contracts that read `s@` get a deep_view onto the
    /// `Seq<char>` projection (`s.chars().collect::<Vec<_>>()`).
    RefStr,
    /// `String` -- owned string. Harness samples directly.
    OwnedString,
    /// `&mut <inner>`. 
    MutRef(Box<ParamShape>),
    /// `Tracked<&PointsTo<V>>` -- a linear permission parameter.
    Resource {
        value_ty: Box<Type>,
        mode: ResourceMode,
        handle_ident: Option<Ident>,
        tier: Option<ResourceTier>,
    },
    /// The exec handle coupled to a `Resource` permission param of the
    /// same `V`: `PPtr<V>` (tier `Pptr`) or `*mut V` / `*const V` (tier
    /// `Raw`). 
    ResourceHandle {
        value_ty: Box<Type>,
        tier: ResourceTier,
    },
    /// `impl Fn(&T) -> bool`
    PredFn(ParamElem),
    /// `&mut slice::Iter<'a, T>` / `&mut hash_set::Iter<'a, T>` /
    /// `&mut Keys<'a, K, V>` -- an iterator parameter, sampled as
    /// `(collection, cursor)` and materialized as a REAL iterator advanced
    /// `cursor % (len+1)` steps.
    IterState {
        kind: IterKind,
        elem: ParamElem,
        val_elem: Option<ParamElem>,
    },
    /// A std value type sampled whole, see [`StdValueKind`].
    StdValue {
        ty: Type,
        kind: StdValueKind,
        by_ref: bool,
    },
}

/// Std value types with a runtime `VcheckStrategy` and `VcheckGen`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StdValueKind {
    Range,
    RangeInclusive,
    RangeFrom,
    RangeTo,
    RangeToInclusive,
    RangeFull,
    Ordering,
    NonZero,
}

impl StdValueKind {
    /// Runtime form of `<value>@`.
    pub fn view_form(&self, value: &Ident) -> TokenStream2 {
        match self {
            StdValueKind::NonZero => quote! { #value.get() },
            StdValueKind::RangeInclusive => {
                quote! { ::verus_spec_check::__vcheck_range_inclusive_view(&#value) }
            }
            _ => quote! { #value },
        }
    }

    /// Spec-side form of `(<value>)@` for an arbitrary expression.
    pub fn view_form_expr(&self, value: &Expr) -> Expr {
        match self {
            StdValueKind::NonZero => verus_syn::parse_quote! { (#value).get() },
            StdValueKind::RangeInclusive => verus_syn::parse_quote! {
                ::verus_spec_check::__vcheck_range_inclusive_view(&(#value))
            },
            _ => value.clone(),
        }
    }
}

const NONZERO_ALIASES: [&str; 12] = [
    "NonZeroU8",
    "NonZeroU16",
    "NonZeroU32",
    "NonZeroU64",
    "NonZeroU128",
    "NonZeroUsize",
    "NonZeroI8",
    "NonZeroI16",
    "NonZeroI32",
    "NonZeroI64",
    "NonZeroI128",
    "NonZeroIsize",
];

/// Recognize a std value type by its last path segment.
pub fn std_value_kind(ty: &Type, user_types: &HashSet<String>) -> Option<StdValueKind> {
    let ty = match ty {
        Type::Group(g) => g.elem.as_ref(),
        Type::Paren(p) => p.elem.as_ref(),
        other => other,
    };
    let Type::Path(tp) = ty else {
        return None;
    };
    if tp.qself.is_some() {
        return None;
    }
    let seg = tp.path.segments.last()?;
    let name = seg.ident.to_string();
    let bare = matches!(seg.arguments, PathArguments::None);
    if bare && tp.path.segments.len() == 1 && user_types.contains(&name) {
        return None;
    }
    let one_arg = || match &seg.arguments {
        PathArguments::AngleBracketed(ab) => {
            ab.args.len() == 1 && matches!(ab.args.first(), Some(GenericArgument::Type(_)))
        }
        _ => false,
    };
    let kind = match name.as_str() {
        "Range" if one_arg() => StdValueKind::Range,
        "RangeInclusive" if one_arg() => StdValueKind::RangeInclusive,
        "RangeFrom" if one_arg() => StdValueKind::RangeFrom,
        "RangeTo" if one_arg() => StdValueKind::RangeTo,
        "RangeToInclusive" if one_arg() => StdValueKind::RangeToInclusive,
        "RangeFull" if bare => StdValueKind::RangeFull,
        "NonZero" if one_arg() => StdValueKind::NonZero,
        n if bare && NONZERO_ALIASES.contains(&n) => StdValueKind::NonZero,
        "Ordering" if bare && !tp.path.segments.iter().any(|s| s.ident == "atomic") => {
            StdValueKind::Ordering
        }
        _ => return None,
    };
    Some(kind)
}

/// Which std iterator family an `IterState` param belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IterKind {
    /// `std::slice::Iter<'a, T>` -- container sampled as `Vec<T>`.
    SliceIter,
    /// `std::collections::hash_set::Iter<'a, T>` -- container `HashSet<T>`.
    HashSetIter,
    /// `std::collections::hash_map::Keys<'a, K, V>` -- container
    /// `HashMap<K, V>`; the iteration order seq is over the keys.
    HashMapKeys,
}

/// Borrow mode of a `Tracked<..>` permission parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceMode {
    /// `Tracked<PointsTo<V>>` -- the callee consumes the permission.
    Owned,
    /// `Tracked<&PointsTo<V>>` -- shared borrow; state can't change.
    Ref,
    /// `Tracked<&mut PointsTo<V>>` -- mutable borrow; post-state may differ.
    MutRef,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceTier {
    /// `PPtr<V>` + `simple_pptr::PointsTo<V>`: `PPtr::new`/`empty`,
    /// teardown via `into_inner`/`free`, read-back via `take`.
    Pptr,
    /// `*mut V` / `*const V` + `raw_ptr::PointsTo<V>`:
    /// `allocate` + `ptr_mut_write`, teardown via `ptr_mut_read` +
    /// `deallocate`, read-back via `ptr_mut_read`.
    Raw,
}

/// Element type used inside a parametrised collection (`Vec<E>`, `&[E]`,
/// `Option<E>`, etc.) 
#[derive(Clone, Debug)]
pub enum ParamElem {
    Primitive(Type),
    UserType(Ident),
}

impl ParamElem {
    /// The type the harness samples for this element. For user types we
    /// sample the user's OWN type (e.g. `User`), not the engine's `ExecUser`,
    /// so the user never has to mention `Exec*`.
    pub fn harness_type(&self) -> TokenStream2 {
        match self {
            ParamElem::Primitive(ty) => quote! { #ty },
            ParamElem::UserType(name) => quote! { #name },
        }
    }
}

impl ParamShape {
    pub fn harness_type(&self) -> TokenStream2 {
        match self {
            ParamShape::Primitive(ty) => quote! { #ty },
            ParamShape::RefPrimitive(ty) => quote! { #ty },
            ParamShape::OwnedVec(e) | ParamShape::Slice(e) => {
                let inner = e.harness_type();
                quote! { ::std::vec::Vec<#inner> }
            }
            ParamShape::OwnedVecDeque(e) => {
                let inner = e.harness_type();
                quote! { ::std::collections::VecDeque<#inner> }
            }
            // The harness samples the developer-declared `sample` type; the
            // opaque value is materialized via the `inject` fn at the call
            // site and in the contract's `view` substitution.
            ParamShape::OpaqueConcretize(t) => {
                let sample = concretize_info(&t.to_string())
                    .map(|i| parse_concretize_type(&i.sample))
                    .unwrap_or_else(|| verus_syn::parse_quote! { () });
                quote! { #sample }
            }
            ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => {
                // Sample as a Vec<E>; fixed-length convergence is enforced
                // by the strategy decl (vec(elem_strategy, N..=N)). The
                // harness converts the Vec to `[E; N]` at the call site.
                let inner = e.harness_type();
                quote! { ::std::vec::Vec<#inner> }
            }
            ParamShape::OwnedOption(e) => {
                let inner = e.harness_type();
                quote! { ::std::option::Option<#inner> }
            }
            ParamShape::OwnedResult(t, e) => {
                let t_ty = t.harness_type();
                let e_ty = e.harness_type();
                quote! { ::std::result::Result<#t_ty, #e_ty> }
            }
            ParamShape::OwnedHashMap(k, v) => {
                let kt = k.harness_type();
                let vt = v.harness_type();
                quote! { ::std::collections::HashMap<#kt, #vt> }
            }
            ParamShape::OwnedHashSet(e) => {
                let inner = e.harness_type();
                quote! { ::std::collections::HashSet<#inner> }
            }
            ParamShape::OwnedBTreeMap(k, v) => {
                let kt = k.harness_type();
                let vt = v.harness_type();
                quote! { ::std::collections::BTreeMap<#kt, #vt> }
            }
            ParamShape::OwnedBTreeSet(e) => {
                let inner = e.harness_type();
                quote! { ::std::collections::BTreeSet<#inner> }
            }
            // For `Multiset<T>` the engine compiles to `ExecMultiset<T>`; the
            // proptest harness gets a `HashMap<T, usize>` and wraps it in
            // `ExecMultiset { m: ... }` at the call site.
            ParamShape::OwnedMultiset(e) => {
                let inner = e.harness_type();
                quote! { ::std::collections::HashMap<#inner, usize> }
            }
            ParamShape::RefUserType(name) | ParamShape::OwnedUserType(name) => {
                // Sample the user's OWN type, not Exec*.
                quote! { #name }
            }
            ParamShape::RefStr | ParamShape::OwnedString => {
                quote! { ::std::string::String }
            }
            ParamShape::MutRef(inner) => inner.harness_type(),
            // Permission param
            ParamShape::Resource { value_ty, .. } => {
                quote! { ::std::option::Option<#value_ty> }
            }
            // Handle para
            ParamShape::ResourceHandle { .. } => quote! { () },
            // Predicate param
            ParamShape::PredFn(e) => {
                let inner = e.harness_type();
                quote! { ::verus_spec_check::VcheckPred<#inner> }
            }
            // Iterator param
            ParamShape::IterState {
                kind,
                elem,
                val_elem,
            } => {
                let t = elem.harness_type();
                match kind {
                    IterKind::SliceIter => quote! { (::std::vec::Vec<#t>, usize) },
                    IterKind::HashSetIter => {
                        quote! { (::std::collections::HashSet<#t>, usize) }
                    }
                    IterKind::HashMapKeys => {
                        let v = val_elem
                            .as_ref()
                            .expect("Keys carries a value elem")
                            .harness_type();
                        quote! { (::std::collections::HashMap<#t, #v>, usize) }
                    }
                }
            }
            ParamShape::StdValue { ty, .. } => quote! { #ty },
        }
    }

    /// What to put in the call to `super::<fn>(...)` at the harness site.
    fn arg_for_real_call(&self, harness_ident: &Ident) -> TokenStream2 {
        match self {
            ParamShape::Primitive(_) => quote! { #harness_ident },
            // `&Primitive` materializes via a `let` ref-binding stamped
            // by `pre_call_binding`
            ParamShape::RefPrimitive(_) => quote! { &#harness_ident },
            ParamShape::OwnedVec(_) | ParamShape::OwnedVecDeque(_) => {
                quote! { #harness_ident.clone() }
            }
            // Inject the sampled value into the opaque type and pass a borrow.
            ParamShape::OpaqueConcretize(t) => {
                let inject = concretize_info(&t.to_string())
                    .map(|i| i.inject_expr(t))
                    .unwrap_or_else(|| verus_syn::parse_quote! { compile_error!() });
                quote! { &#inject(#harness_ident.clone()) }
            }
            ParamShape::Slice(_) => quote! { #harness_ident.as_slice() },
            ParamShape::OwnedArray(elem, len) => {
                // `[E; N]` by value: use array::from_fn to map the sampled
                // Vec into a fixed-size array.
                let elem_ty = elem.harness_type();
                quote! {
                    ::core::array::from_fn::<#elem_ty, #len, _>(|i| #harness_ident[i].clone())
                }
            }
            ParamShape::RefArray(elem, len) => {
                // `&[E; N]`: build the array, then borrow.
                let elem_ty = elem.harness_type();
                quote! {
                    &::core::array::from_fn::<#elem_ty, #len, _>(|i| #harness_ident[i].clone())
                }
            }
            ParamShape::OwnedOption(_) => quote! { #harness_ident.clone() },
            ParamShape::OwnedResult(_, _) => quote! { #harness_ident.clone() },
            ParamShape::OwnedHashMap(_, _) => quote! { #harness_ident.clone() },
            ParamShape::OwnedHashSet(_) => quote! { #harness_ident.clone() },
            ParamShape::OwnedBTreeMap(_, _) => quote! { #harness_ident.clone() },
            ParamShape::OwnedBTreeSet(_) => quote! { #harness_ident.clone() },
            ParamShape::OwnedMultiset(_) => {
                let v = crate::syntax::Vstd(harness_ident.span());
                quote! {
                    #v::contrib::exec_spec::ExecMultiset { m: #harness_ident.clone() }
                }
            }
            // The user's exec fn takes their OWN type (`&User` / `User`).
            ParamShape::RefUserType(_) => quote! { &#harness_ident },
            ParamShape::OwnedUserType(_) => quote! { #harness_ident.clone() },
            ParamShape::RefStr => quote! { #harness_ident.as_str() },
            ParamShape::OwnedString => quote! { #harness_ident.clone() },
            ParamShape::Resource { .. } => {
                // `Vstd` resolves to `crate` when expanding inside vstd
                // itself (the in-place instrumentation case) and `::vstd`
                // downstream.
                let v = crate::syntax::Vstd(harness_ident.span());
                quote! { #v::prelude::Tracked::assume_new() }
            }
            // Handle param: by the time the call happens, the sampled `()`
            // binding has been shadowed with `guard.handle()` (see the
            // paired Resource's `pre_call_binding`), so pass it through.
            ParamShape::ResourceHandle { .. } => quote! { #harness_ident },
            ParamShape::MutRef(inner) => match inner.as_ref() {
                ParamShape::Slice(_) => quote! { #harness_ident.as_mut_slice() },
                _ => quote! { &mut #harness_ident },
            },
            ParamShape::PredFn(e) => {
                let inner = e.harness_type();
                quote! { |__vcheck_x: &#inner| #harness_ident.call(__vcheck_x) }
            }
            ParamShape::IterState { .. } => quote! {
                compile_error!("verus_spec_check internal: iterator param requires its prebinding")
            },
            ParamShape::StdValue { by_ref: true, .. } => quote! { &#harness_ident },
            ParamShape::StdValue { by_ref: false, .. } => quote! { #harness_ident.clone() },
        }
    }

    /// Emit a pre-call `let` binding for shapes that need to materialize a
    /// non-temporary so the borrow can outlive the call. Returns
    /// `(prebound_ident, let_stmt)` if a pre-binding is needed; the harness
    /// uses `prebound_ident` as the call argument in place of the
    /// `arg_for_real_call` form.
    pub fn pre_call_binding(&self, harness_ident: &Ident) -> Option<(Ident, TokenStream2)> {
        match self {
            ParamShape::OwnedArray(elem, len) | ParamShape::RefArray(elem, len) => {
                let elem_ty = elem.harness_type();
                let bound = format_ident!("__vcheck_arr_{}", harness_ident);
                let stmt = quote! {
                    let #bound: [#elem_ty; #len] =
                        ::core::array::from_fn(|i| #harness_ident[i].clone());
                };
                Some((bound, stmt))
            }
            // `&Primitive`: bind a local reference so the address is
            // stable across the call (avoids temporary borrows of a
            // freshly-named pattern binding).
            ParamShape::RefPrimitive(ty) => {
                let bound = format_ident!("__vcheck_ref_{}", harness_ident);
                let stmt = quote! {
                    let #bound: &#ty = &#harness_ident;
                };
                Some((bound, stmt))
            }
            ParamShape::MutRef(inner) => match inner.as_ref() {
                // `&mut [E; N]`: same shape as the immutable OwnedArray
                // prebinding, but the local must be `mut` so the call
                // can mutate through `&mut bound`.
                ParamShape::OwnedArray(elem, len) => {
                    let elem_ty = elem.harness_type();
                    let bound = format_ident!("__vcheck_arr_{}", harness_ident);
                    let stmt = quote! {
                        let mut #bound: [#elem_ty; #len] =
                            ::core::array::from_fn(|i| #harness_ident[i].clone());
                    };
                    Some((bound, stmt))
                }
                _ => inner.pre_call_binding(harness_ident),
            },
            // Iterator param: build the live iterator from the container
            // local (bound in `pre_state_let`) and advance it to the
            // sampled cursor. Emitted after the requires filters, so
            // rejected samples never construct iterators.
            ParamShape::IterState { kind, .. } => {
                let c = format_ident!("__vcheck_iter_c_{}", harness_ident);
                let cur = format_ident!("__vcheck_iter_cur_{}", harness_ident);
                let bound = format_ident!("__vcheck_it_{}", harness_ident);
                let make_iter = match kind {
                    IterKind::SliceIter | IterKind::HashSetIter => quote! { #c.iter() },
                    IterKind::HashMapKeys => quote! { #c.keys() },
                };
                let stmt = quote! {
                    let mut #bound = #make_iter;
                    for _ in 0..#cur {
                        let _ = #bound.next();
                    }
                };
                Some((bound, stmt))
            }
            // Permission param: materialize the sampled model into real
            // memory (constructor replay -- real alloc + optional write)
            // and shadow the paired handle binding with the materialized
            // pointer. 
            ParamShape::Resource {
                value_ty,
                handle_ident,
                mode,
                tier,
            } => {
                let guard = resource_guard_ident(harness_ident);
                let handle = handle_ident
                    .as_ref()
                    .expect("resource param must be paired before emission");
                let tier = tier.expect("tier set by pairing");
                let v = crate::syntax::Vstd(harness_ident.span());
                // The constructor / teardown operations are emitted HERE
                // (as non-capturing closures coerced to fn pointers) rather
                // than baked into a vstd_ext trait impl, so they
                // monomorphize against whichever vstd is in scope at the
                // expansion site -- `crate` when instrumenting vstd itself,
                // `::vstd` downstream. See `VcheckDynResourceGuard`.
                let ops = match tier {
                    ResourceTier::Pptr => quote! {
                        // Init(v): certified alloc+write (view pinned to Init(v)).
                        |__vcheck_v: #value_ty| #v::simple_pptr::PPtr::<#value_ty>::new(__vcheck_v).0,
                        // Uninit: certified alloc (view pinned to Uninit).
                        || #v::simple_pptr::PPtr::<#value_ty>::empty().0,
                        // Teardown, model says Init: move the payload out
                        // (dropping it exactly once), then free.
                        |__vcheck_h: #v::simple_pptr::PPtr<#value_ty>| {
                            let _ = __vcheck_h.into_inner(#v::prelude::Tracked::assume_new());
                        },
                        // Teardown, model says Uninit: free raw memory only.
                        |__vcheck_h: #v::simple_pptr::PPtr<#value_ty>| {
                            __vcheck_h.free(#v::prelude::Tracked::assume_new());
                        },
                    },
                    ResourceTier::Raw => quote! {
                        |__vcheck_v: #value_ty| {
                            let (__vcheck_p8, _, _) = #v::raw_ptr::allocate(
                                ::core::mem::size_of::<#value_ty>(),
                                ::core::mem::align_of::<#value_ty>(),
                            );
                            let __vcheck_p = __vcheck_p8 as *mut #value_ty;
                            #v::raw_ptr::ptr_mut_write(
                                __vcheck_p,
                                #v::prelude::Tracked::assume_new(),
                                __vcheck_v,
                            );
                            __vcheck_p
                        },
                        || {
                            let (__vcheck_p8, _, _) = #v::raw_ptr::allocate(
                                ::core::mem::size_of::<#value_ty>(),
                                ::core::mem::align_of::<#value_ty>(),
                            );
                            __vcheck_p8 as *mut #value_ty
                        },
                        |__vcheck_h: *mut #value_ty| {
                            // Move the payload out (dropping it exactly
                            // once), then release the raw allocation.
                            let _ = #v::raw_ptr::ptr_mut_read(
                                __vcheck_h,
                                #v::prelude::Tracked::assume_new(),
                            );
                            #v::raw_ptr::deallocate(
                                __vcheck_h as *mut u8,
                                ::core::mem::size_of::<#value_ty>(),
                                ::core::mem::align_of::<#value_ty>(),
                                #v::prelude::Tracked::assume_new(),
                                #v::prelude::Tracked::assume_new(),
                            );
                        },
                        |__vcheck_h: *mut #value_ty| {
                            #v::raw_ptr::deallocate(
                                __vcheck_h as *mut u8,
                                ::core::mem::size_of::<#value_ty>(),
                                ::core::mem::align_of::<#value_ty>(),
                                #v::prelude::Tracked::assume_new(),
                                #v::prelude::Tracked::assume_new(),
                            );
                        },
                    },
                };
                // `&mut` permissions transition the guard after the call
                // (mark_* / read_back take `&mut self`); shared borrows
                // never touch it again. `allow(unused_mut)` keeps the
                // no-directive `&mut` case warning-free.
                let let_guard = if matches!(mode, ResourceMode::MutRef) {
                    quote! { #[allow(unused_mut)] let mut #guard }
                } else {
                    quote! { let #guard }
                };
                let stmt = quote! {
                    // Consume the `()` placeholder the handle binder
                    // sampled, so the shadowing below doesn't leave an
                    // unused-variable warning in the generated harness.
                    let _ = &#handle;
                    #let_guard = ::verus_spec_check_vstd_ext::resource::VcheckDynResourceGuard::materialize(
                        ::verus_spec_check_vstd_ext::exec_mem_contents_from_option(
                            #harness_ident.clone(),
                        ),
                        #ops
                    );
                    let #handle = #guard.handle();
                };
                Some((guard, stmt))
            }
            _ => None,
        }
    }

    /// Like `arg_for_real_call`, but uses a pre-bound name when one was
    /// produced by `pre_call_binding`.
    pub fn arg_with_optional_prebinding(
        &self,
        harness_ident: &Ident,
        prebound: Option<&Ident>,
    ) -> TokenStream2 {
        match (self, prebound) {
            (ParamShape::OwnedArray(_, _), Some(b)) => quote! { #b },
            (ParamShape::RefArray(_, _), Some(b)) => quote! { &#b },
            // `&Primitive`: the prebinding is already `let bound: &T =
            // &harness;`, so pass it through directly.
            (ParamShape::RefPrimitive(_), Some(b)) => quote! { #b },
            // `&mut [E; N]`: the prebinding materializes a mutable
            // `[E; N]` local (see `pre_call_binding`); pass it by
            // mutable ref.
            (ParamShape::MutRef(inner), Some(b))
                if matches!(inner.as_ref(), ParamShape::OwnedArray(_, _)) =>
            {
                quote! { &mut #b }
            }
            // Iterator param: pass the cursor-advanced live iterator.
            (ParamShape::IterState { .. }, Some(b)) => quote! { &mut #b },
            _ => self.arg_for_real_call(harness_ident),
        }
    }

    /// What does `<param>.deep_view()` (or `*self` for a method receiver)
    /// become in a contract clause? The result is the `Exec*` value the
    /// `exec_*` spec fns expect. For user types we convert via the generated
    /// `__vcheck_to_exec_*` fn.
    pub fn call_form_for_deep_view(&self, harness_ident: &Ident) -> TokenStream2 {
        match self {
            ParamShape::Primitive(_) => quote! { #harness_ident },
            // `&Primitive` is Copy; contracts that deref see the same
            // value as the bare harness binding.
            ParamShape::RefPrimitive(_) => quote! { #harness_ident },
            ParamShape::OwnedVec(_) => quote! { #harness_ident.as_slice() },
            // `VecDeque` has no `as_slice`; materialize a contiguous `Vec`
            // of its front-to-back order, then slice that.
            ParamShape::OwnedVecDeque(_) => {
                quote! { ::verus_spec_check::__vcheck_vecdeque_slice(&#harness_ident).as_slice() }
            }
            // In the contract the param stands for a borrow of the injected
            // opaque value (params of view-based specs are `&T`), so `view(a)`
            // -> `realize(a)` composes to `realize(&inject(sample))`.
            ParamShape::OpaqueConcretize(t) => {
                let inject = concretize_info(&t.to_string())
                    .map(|i| i.inject_expr(t))
                    .unwrap_or_else(|| verus_syn::parse_quote! { compile_error!() });
                quote! { &#inject(#harness_ident.clone()) }
            }
            ParamShape::Slice(_) => quote! { #harness_ident.as_slice() },
            ParamShape::OwnedArray(_, _) | ParamShape::RefArray(_, _) => {
                // Treat the sampled `Vec<E>` as a slice for the `Exec*`
                // companion's purposes; this matches how `&[E]` deep_view
                // is dispatched.
                quote! { #harness_ident.as_slice() }
            }
            ParamShape::OwnedOption(_) => quote! { &#harness_ident },
            ParamShape::OwnedResult(_, _) => quote! { &#harness_ident },
            ParamShape::OwnedHashMap(_, _) => quote! { &#harness_ident },
            ParamShape::OwnedHashSet(_) => quote! { &#harness_ident },
            ParamShape::OwnedBTreeMap(_, _) => quote! { &#harness_ident },
            ParamShape::OwnedBTreeSet(_) => quote! { &#harness_ident },
            ParamShape::OwnedMultiset(_) => {
                let v = crate::syntax::Vstd(harness_ident.span());
                quote! {
                    &#v::contrib::exec_spec::ExecMultiset { m: #harness_ident.clone() }
                }
            }
            ParamShape::RefUserType(name) | ParamShape::OwnedUserType(name) => {
                // Fully-qualified trait call so it (a) resolves across files
                // by trait lookup and (b) triggers the ToExecModel
                // `on_unimplemented` diagnostic if the type was never
                // `#[vcheck_provide]`'d. (Method syntax `x.to_exec_model()`
                // would yield a generic E0599 instead.)
                quote! {
                    &<#name as ::verus_spec_check::ToExecModel>::to_exec_model(&#harness_ident)
                }
            }
            ParamShape::RefStr | ParamShape::OwnedString => {
                // Lower the spec view `s@: Seq<char>` to a runtime
                // `Vec<char>` via `__vcheck_str_chars`, then take a slice. We
                // call the runtime helper (rather than emitting a block) to
                // keep the rewritten clause a flat call expression -- block
                // syntax `{ ... }` trips proptest's format-string scanner
                // inside `prop_assert!`.
                quote! {
                    ::verus_spec_check::__vcheck_str_chars(&#harness_ident).as_slice()
                }
            }
            // For `&mut <inner>`, the *post-call* deep_view is the inner
            // shape's normal call form. The pre-call view is computed
            // separately and stashed in `pre_view_for` keyed on the ident.
            //
            // Special case for `&mut [E; N]`: the call mutates a
            // separately-materialized `[E; N]` local
            // (`__vcheck_arr_<id>`), so the deep_view must read from that
            // bound array, NOT the Vec that was the harness binding.
            ParamShape::MutRef(inner) => match inner.as_ref() {
                ParamShape::OwnedArray(_, _) => {
                    let arr_id = format_ident!("__vcheck_arr_{}", harness_ident);
                    quote! { #arr_id.as_slice() }
                }
                _ => inner.call_form_for_deep_view(harness_ident),
            },
            // Permission param: `perm@`-style whole-view projections are
            // rejected in the resource clause pre-pass (only method
            // projections are supported), so this form is defensive: point
            // at the shadow model.
            ParamShape::Resource { .. } => {
                let model = resource_model_ident(harness_ident);
                quote! { &#model }
            }
            // Handle param: by contract-eval time the binding holds the
            // materialized `PPtr<V>` (Copy).
            ParamShape::ResourceHandle { .. } => quote! { #harness_ident },
            // Predicate param: contracts never take the pred's deep_view;
            // occurrences appear only under `call_ensures`/`call_requires`,
            // which route through `VcheckPred::models`/`requires`. Defensive
            // passthrough.
            ParamShape::PredFn(_) => quote! { #harness_ident },
            // Iterator param: post-call view. `.1` (the sequence) is
            // constant across `next()` per vstd's own spec, so the
            // pre-call tuple is correct for it; `.0` (the cursor) is NOT
            // updated post-call -- see the variant's documented limitation.
            ParamShape::IterState { .. } => {
                let cur = format_ident!("__vcheck_iter_cur_{}", harness_ident);
                let order = format_ident!("__vcheck_iter_order_{}", harness_ident);
                quote! { (#cur as i64, #order.as_slice()) }
            }
            ParamShape::StdValue { kind, .. } => kind.view_form(harness_ident),
        }
    }

    /// For `&mut`-receiving shapes, build a *value* (cloned where
    /// necessary) that captures the pre-call deep_view of `harness_ident`.
    /// The snapshot is stored in a local before the call so that
    /// `old(<id>)@` rewrites in the contract resolve to it. Returns `None`
    /// for non-mut shapes -- they don't need a separate pre-state because
    /// the post-call value is the same as the pre-call value.
    ///
    /// The snapshot deliberately materializes an OWNED value (not a
    /// borrow), so that mutation through the `&mut` arg doesn't invalidate
    /// it. For `OwnedVec`/`OwnedHashMap`/`OwnedHashSet`/`OwnedString`/
    /// `OwnedOption`/`OwnedUserType` the harness binding already holds an
    /// owned value, so a `.clone()` is sufficient. The snapshot is
    /// returned in the form expected by `call_form_for_deep_view` (e.g.
    /// `slice` for `OwnedVec`) so the rewriter can substitute it
    /// pointwise wherever `<id>@` would have appeared.
    pub fn pre_call_view_snapshot(&self, harness_ident: &Ident) -> Option<TokenStream2> {
        // Iterator param: the vstd view is `(int, Seq<T>)`. Expose the
        // sampled cursor and the materialized iteration order (both bound
        // in `pre_state_let`) as a runtime tuple, so `old(<id>)@.0` /
        // `old(<id>)@.1` project naturally.
        if let ParamShape::IterState { .. } = self {
            let cur = format_ident!("__vcheck_iter_cur_{}", harness_ident);
            let order = format_ident!("__vcheck_iter_order_{}", harness_ident);
            return Some(quote! { (#cur as i64, #order.as_slice()) });
        }
        let inner = match self {
            ParamShape::MutRef(inner) => inner,
            _ => return None,
        };
        // For each owned shape, we just clone the harness binding into a
        // snapshot ident; the deep_view path then reads from the snapshot.
        // The actual snapshot value is stored in a local named
        // `__vcheck_pre_<id>` and returned here as the deep_view form for
        // the contract rewriter.
        let snap = format_ident!("__vcheck_pre_{}", harness_ident);
        match inner.as_ref() {
            ParamShape::OwnedVec(_) => Some(quote! { #snap.as_slice() }),
            // `&mut VecDeque<E>`: snapshot is the cloned deque; materialize
            // its contiguous order via the runtime helper, then slice.
            ParamShape::OwnedVecDeque(_) => Some(quote! {
                ::verus_spec_check::__vcheck_vecdeque_slice(&#snap).as_slice()
            }),
            // `&mut [E]`: harness binding is `Vec<E>`, so snapshot is
            // the cloned Vec; expose as a slice for spec companions.
            ParamShape::Slice(_) => Some(quote! { #snap.as_slice() }),
            // `&mut [E; N]`: harness binding is the `Vec<E>` strategy
            // value (NOT the array, because the array is built
            // post-snapshot via `pre_call_binding`). The deep_view of
            // the pre state is therefore over the Vec's items.
            ParamShape::OwnedArray(_, _) => Some(quote! { #snap.as_slice() }),
            ParamShape::OwnedString => Some(quote! {
                ::verus_spec_check::__vcheck_str_chars(&#snap).as_slice()
            }),
            ParamShape::OwnedOption(_)
            | ParamShape::OwnedResult(_, _)
            | ParamShape::OwnedHashMap(_, _)
            | ParamShape::OwnedHashSet(_)
            | ParamShape::OwnedBTreeMap(_, _)
            | ParamShape::OwnedBTreeSet(_)
            | ParamShape::OwnedUserType(_) => Some(quote! { &#snap }),
            ParamShape::Primitive(_) => Some(quote! { #snap }),
            // `&Primitive`: snapshot is the primitive itself; spec
            // companions read it directly.
            ParamShape::RefPrimitive(_) => Some(quote! { #snap }),
            ParamShape::StdValue { kind, .. } => Some(kind.view_form(&snap)),
            _ => None,
        }
    }

    /// Emit the `let __vcheck_pre_<id> = ...;` statement that captures the
    /// pre-call value of a `&mut`-shaped param. Paired with
    /// `pre_call_view_snapshot`. Returns `None` for non-mut shapes.
    pub fn pre_state_let(&self, harness_ident: &Ident) -> Option<TokenStream2> {
        // Permission param: lower the sampled `Option<V>` into the
        // `ExecMemContents<V>` shadow model. Emitted with the pre-state
        // snapshots (i.e. BEFORE the requires filters) because requires
        // clauses over the permission evaluate on this model -- that's what
        // lets precondition filtering run without materializing memory
        // for rejected samples. Shared borrows are state-constant, so this
        // one model serves pre- and post-state alike; `&mut` permissions
        // read post-state from a separate post model (see resource.rs).
        if let ParamShape::Resource { .. } = self {
            let model = resource_model_ident(harness_ident);
            return Some(quote! {
                let #model = ::verus_spec_check_vstd_ext::exec_mem_contents_from_option(
                    #harness_ident.clone(),
                );
            });
        }
        // Iterator param: bind the container, materialize its iteration
        // order ONCE (stable for an untouched container, so the live
        // iterator built later in `pre_call_binding` yields exactly this
        // sequence), and normalize the sampled cursor into 0..=len.
        // Emitted with the pre-state snapshots (before requires filters)
        // because contracts can reference the view from `requires` too.
        if let ParamShape::IterState { kind, elem, .. } = self {
            let c = format_ident!("__vcheck_iter_c_{}", harness_ident);
            let cur = format_ident!("__vcheck_iter_cur_{}", harness_ident);
            let order = format_ident!("__vcheck_iter_order_{}", harness_ident);
            let t = elem.harness_type();
            let collect_order = match kind {
                IterKind::SliceIter | IterKind::HashSetIter => {
                    quote! { #c.iter().cloned().collect() }
                }
                IterKind::HashMapKeys => quote! { #c.keys().cloned().collect() },
            };
            return Some(quote! {
                let #c = #harness_ident.0.clone();
                let #order: ::std::vec::Vec<#t> = #collect_order;
                let #cur: usize = if #order.len() == 0 {
                    0
                } else {
                    #harness_ident.1 % (#order.len() + 1)
                };
            });
        }
        let inner = match self {
            ParamShape::MutRef(inner) => inner,
            _ => return None,
        };
        let snap = format_ident!("__vcheck_pre_{}", harness_ident);
        // `&mut VecDeque<E>`: `VecDeque::clone` walks elements one by one
        // (no `Copy` memcpy specialization like `Vec`'s), so cloning a
        // length-boundary ZST deque from the boundary strategy arm would
        // never terminate. The runtime helper replicates ZST deques in
        // O(1) and falls back to `clone` for sized elements.
        if matches!(inner.as_ref(), ParamShape::OwnedVecDeque(_)) {
            return Some(quote! {
                let #snap = ::verus_spec_check::__vcheck_vecdeque_snapshot(&#harness_ident);
            });
        }
        // A blanket clone covers the remaining shapes we currently
        // support (Owned*, String, primitive). Non-Clone shapes wouldn't
        // be routed here because emit_harness rejects them.
        Some(quote! {
            let #snap = #harness_ident.clone();
        })
    }

    /// The spec-side type the original parameter ends up viewed as, for the
    /// purposes of synthesising helper spec fns (quantifier lifting).
    /// Returned as an UNQUALIFIED type path because the engine recognises
    /// `Seq<T>`, `Map<K,V>`, etc. only when written without a leading path.
    pub fn spec_type(&self) -> TokenStream2 {
        match self {
            ParamShape::Primitive(ty) => quote! { #ty },
            ParamShape::RefPrimitive(ty) => quote! { #ty },
            // The opaque type's view is a mathematical integer.
            ParamShape::OpaqueConcretize(_) => quote! { int },
            ParamShape::OwnedVec(e) | ParamShape::Slice(e) | ParamShape::OwnedVecDeque(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Seq<#inner> }
            }
            ParamShape::OwnedArray(e, _) | ParamShape::RefArray(e, _) => {
                // Spec view of `[E; N]` is a `Seq<E>`; the engine treats it
                // identically to a slice for the purpose of contract
                // companions.
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Seq<#inner> }
            }
            ParamShape::OwnedOption(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Option<#inner> }
            }
            ParamShape::OwnedResult(t, e) => {
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
            ParamShape::OwnedHashMap(k, v) => {
                let kt = match k {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                let vt = match v {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Map<#kt, #vt> }
            }
            ParamShape::OwnedHashSet(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Set<#inner> }
            }
            ParamShape::OwnedBTreeMap(k, v) => {
                let kt = match k {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                let vt = match v {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Map<#kt, #vt> }
            }
            ParamShape::OwnedBTreeSet(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Set<#inner> }
            }
            ParamShape::OwnedMultiset(e) => {
                let inner = match e {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { Multiset<#inner> }
            }
            ParamShape::RefUserType(n) | ParamShape::OwnedUserType(n) => quote! { #n },
            ParamShape::RefStr | ParamShape::OwnedString => {
                // Spec view of a string is a `Seq<char>`; the engine
                // recognises it identically to a slice of `char`.
                quote! { Seq<char> }
            }
            ParamShape::MutRef(inner) => inner.spec_type(),
            // Permission param: the spec-side value contracts project is
            // the abstract memory state.
            ParamShape::Resource { value_ty, .. } => quote! { MemContents<#value_ty> },
            // Handle param: quantifier lifting over raw handles isn't
            // supported (there's nothing spec-meaningful to quantify);
            // unit keeps the synthetic signature well-formed.
            ParamShape::ResourceHandle { .. } => quote! { () },
            // Predicate param: there is no spec-side value type for a
            // closure (its contract is reached via call_ensures, which the
            // rewriter lowers before quantifier lifting sees it). Unit
            // keeps synthetic signatures well-formed; a quantified clause
            // that actually captures the pred outside the supported
            // bounded forms will fail in exec_spec with its diagnostic.
            ParamShape::PredFn(_) => quote! { () },
            // Iterator param: vstd's view type.
            ParamShape::IterState { elem, .. } => {
                let inner = match elem {
                    ParamElem::Primitive(t) => quote! { #t },
                    ParamElem::UserType(n) => quote! { #n },
                };
                quote! { (int, Seq<#inner>) }
            }
            ParamShape::StdValue { ty, .. } => quote! { #ty },
        }
    }
}

/// Name of the generated `User -> ExecUser` converter fn for a user type.
pub fn to_exec_fn_name(user_ty: &Ident) -> Ident {
    format_ident!("__vcheck_to_exec_{}", user_ty)
}

/// Strip a leading `Exec` from a name. Returns the original name if the
/// stripped name corresponds to a user-defined type. Used by the classifier
/// to recognise `&ExecPair` / `ExecPair` parameter types and route them
/// through the user-type code paths (which sample `ExecPair`).
pub fn strip_exec_prefix<'a>(name: &'a str, user_types: &HashSet<String>) -> Option<&'a str> {
    if let Some(rest) = name.strip_prefix("Exec") {
        if user_types.contains(rest) {
            return Some(rest);
        }
    }
    None
}

pub fn classify_param_elem(ty: &Type, user_types: &HashSet<String>) -> Result<ParamElem, Error> {
    // Peel off `Type::Group` / `Type::Paren` for the same reason as
    // `classify_param_type` above (macro-substitution hygiene wrappers).
    let ty = match ty {
        Type::Group(g) => g.elem.as_ref(),
        Type::Paren(p) => p.elem.as_ref(),
        _ => ty,
    };
    // The unit type: one value, zero bytes. Primitive-shaped for element
    // classification (the runtime provides `VcheckStrategy for ()` and
    // `VcheckGen for ()`); enables ZST container instantiations such as
    // `Vec<()>`, where maximum-length containers are O(1) memory -- the
    // route to length-arithmetic boundary findings (append overflow).
    if matches!(ty, Type::Tuple(t) if t.elems.is_empty()) {
        return Ok(ParamElem::Primitive(ty.clone()));
    }
    if std_value_kind(ty, user_types).is_some() {
        return Ok(ParamElem::Primitive(ty.clone()));
    }
    if let Type::Path(tp) = ty {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let seg = &tp.path.segments[0];
            let name = seg.ident.to_string();
            if user_types.contains(&name) && matches!(seg.arguments, PathArguments::None) {
                return Ok(ParamElem::UserType(seg.ident.clone()));
            }
            // Recognise `ExecFoo` as the user's `Foo` for nested elements.
            if let Some(stripped) = strip_exec_prefix(&name, user_types) {
                if matches!(seg.arguments, PathArguments::None) {
                    return Ok(ParamElem::UserType(Ident::new(stripped, seg.ident.span())));
                }
            }
            if is_primitive_like(&name) {
                return Ok(ParamElem::Primitive(ty.clone()));
            }
            // A capitalized single-segment name we don't recognise is treated
            // as an EXTERNAL user type: one defined (and `#[vcheck_provide]`'d) in
            // another module/file. We don't need its definition here -- the
            // generated strategy uses `<Name as VcheckStrategy>` and the
            // converter uses `<Name as ToExecModel>`, both resolved by trait
            // lookup across files. If the type was never provided, the
            // `on_unimplemented` diagnostic fires at the harness.
            if matches!(seg.arguments, PathArguments::None)
                && name.chars().next().is_some_and(|c| c.is_uppercase())
            {
                return Ok(ParamElem::UserType(seg.ident.clone()));
            }
        }
    }
    Err(Error::new_spanned(
        ty,
        "verus_spec_check: nested element must be a primitive or a user-defined struct/enum",
    ))
}

/// Classify the `Err` element of a *returned* `Result<T, E>` (B3).
///
/// Unlike a param element, the error payload of a returned Result is never
/// sampled and never compared by value -- the harness only observes the
/// variant (`ret is Err`). So when `E` is an opaque std error type that
/// `classify_param_elem` can't map (e.g. `core::num::TryFromIntError`, a
/// multi-segment path), we fall back to treating it as a primitive-shaped
/// placeholder rather than rejecting the whole `#[vcheck]`. The placeholder is
/// only ever reachable through `ReturnShape::OwnedResult(_, _)` match arms,
/// which ignore the error element, so no error-typed value is generated or
/// compared. (Specs that actually inspect `ret->Err_0` should give `E` a
/// classifiable type.)
pub fn classify_return_result_err_elem(ty: &Type, user_types: &HashSet<String>) -> ParamElem {
    match classify_param_elem(ty, user_types) {
        Ok(elem) => elem,
        Err(_) => {
            let ty = match ty {
                Type::Group(g) => g.elem.as_ref(),
                Type::Paren(p) => p.elem.as_ref(),
                other => other,
            };
            ParamElem::Primitive(ty.clone())
        }
    }
}

/// If `ty` is a `Tracked<..>` wrapper over a `PointsTo<V>` permission
/// (directly, `&PointsTo<V>`, or `&mut PointsTo<V>`; the `PointsTo` path may
/// be module-qualified, e.g. `simple_pptr::PointsTo<V>`), return the value
/// type `V` and the borrow mode. 
pub fn tracked_points_to_resource(ty: &Type) -> Option<(Type, ResourceMode)> {
    // Outer `Tracked<X>` (last path segment; tolerate `vstd::prelude::`
    // qualification), with exactly one angle-bracketed type argument.
    let tp = match ty {
        Type::Path(tp) if tp.qself.is_none() => tp,
        _ => return None,
    };
    let seg = tp.path.segments.last()?;
    if seg.ident != "Tracked" {
        return None;
    }
    let inner = match &seg.arguments {
        PathArguments::AngleBracketed(ab) if ab.args.len() == 1 => match &ab.args[0] {
            verus_syn::GenericArgument::Type(t) => t,
            _ => return None,
        },
        _ => return None,
    };
    // Peel an optional reference to get the borrow mode.
    let (perm_ty, mode) = match inner {
        Type::Reference(r) => (
            r.elem.as_ref(),
            if r.mutability.is_some() {
                ResourceMode::MutRef
            } else {
                ResourceMode::Ref
            },
        ),
        other => (other, ResourceMode::Owned),
    };
    // The permission must be a `PointsTo<V>` (any module qualification).
    let ptp = match perm_ty {
        Type::Path(ptp) if ptp.qself.is_none() => ptp,
        _ => return None,
    };
    let pseg = ptp.path.segments.last()?;
    if pseg.ident != "PointsTo" {
        return None;
    }
    match &pseg.arguments {
        PathArguments::AngleBracketed(ab) if ab.args.len() == 1 => match &ab.args[0] {
            verus_syn::GenericArgument::Type(v) => Some((v.clone(), mode)),
            _ => None,
        },
        _ => None,
    }
}

/// If `ty` is a `PPtr<V>` handle (any module qualification), return `V`.
pub fn pptr_handle_value_ty(ty: &Type) -> Option<Type> {
    let tp = match ty {
        Type::Path(tp) if tp.qself.is_none() => tp,
        _ => return None,
    };
    let seg = tp.path.segments.last()?;
    if seg.ident != "PPtr" {
        return None;
    }
    match &seg.arguments {
        PathArguments::AngleBracketed(ab) if ab.args.len() == 1 => match &ab.args[0] {
            verus_syn::GenericArgument::Type(v) => Some(v.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// If `pat` is the Verus permission-unwrapping pattern `Tracked(name)`,
/// return `name`. `#[vcheck]` fns take permissions as
/// `Tracked(perm): Tracked<&PointsTo<V>>`, so the contract-visible ident
/// lives one level inside the tuple-struct pattern.
pub fn tracked_pat_inner_ident(pat: &Pat) -> Option<Ident> {
    if let Pat::TupleStruct(ts) = pat {
        if ts
            .path
            .segments
            .last()
            .map(|s| s.ident == "Tracked")
            .unwrap_or(false)
            && ts.elems.len() == 1
        {
            if let Pat::Ident(pi) = &ts.elems[0] {
                return Some(pi.ident.clone());
            }
        }
    }
    None
}

/// Naming conventions for the resource harness bindings.
pub fn resource_model_ident(perm: &Ident) -> Ident {
    format_ident!("__vcheck_model_{}", perm)
}
pub fn resource_guard_ident(perm: &Ident) -> Ident {
    format_ident!("__vcheck_guard_{}", perm)
}
pub fn resource_post_model_ident(perm: &Ident) -> Ident {
    format_ident!("__vcheck_post_model_{}", perm)
}

/// Recognize `impl Fn(&T) -> bool` and return the classified `T`.
/// Returns `None` if the impl-trait isn't that exact shape (so the caller
/// can emit its diagnostic), `Some(Err(..))` if the shape matches but `T`
/// itself doesn't classify as a supported element.
pub fn pred_fn_elem(
    it: &verus_syn::TypeImplTrait,
    user_types: &HashSet<String>,
) -> Option<Result<ParamElem, Error>> {
    for bound in &it.bounds {
        if let verus_syn::TypeParamBound::Trait(tb) = bound {
            let seg = tb.path.segments.last()?;
            if seg.ident != "Fn" {
                continue;
            }
            let verus_syn::PathArguments::Parenthesized(pargs) = &seg.arguments else {
                continue;
            };
            // Exactly one argument, of shape `&T`.
            if pargs.inputs.len() != 1 {
                continue;
            }
            let Type::Reference(arg_ref) = &pargs.inputs[0] else {
                continue;
            };
            if arg_ref.mutability.is_some() {
                continue;
            }
            // Return type must be `bool`.
            let verus_syn::ReturnType::Type(_, _, _, out_ty) = &pargs.output else {
                continue;
            };
            let is_bool = matches!(
                out_ty.as_ref(),
                Type::Path(tp) if tp.qself.is_none()
                    && tp.path.segments.len() == 1
                    && tp.path.segments[0].ident == "bool"
            );
            if !is_bool {
                continue;
            }
            return Some(classify_param_elem(&arg_ref.elem, user_types));
        }
    }
    None
}

pub fn classify_param_type(ty: &Type, user_types: &HashSet<String>) -> Result<ParamShape, Error> {
    // Peel off `Type::Group` (macro-substitution hygiene wrappers) and
    // `Type::Paren` (parenthesized types) so a macro-expanded `$uN`
    // primitive like `u8` reaches the inner match arms as a plain
    // `Type::Path`. Without this, `verus!` items inside a `macro_rules!`
    // (e.g. `std_specs::num::num_specs!`) reject every `#[vcheck]`
    // marker with "unsupported parameter type".
    let ty = match ty {
        Type::Group(g) => g.elem.as_ref(),
        Type::Paren(p) => p.elem.as_ref(),
        _ => ty,
    };
    // Linear-permission params
    if let Some((value_ty, mode)) = tracked_points_to_resource(ty) {
        return Ok(ParamShape::Resource {
            value_ty: Box::new(value_ty),
            mode,
            handle_ident: None,
            tier: None,
        });
    }
    if let Some(value_ty) = pptr_handle_value_ty(ty) {
        return Ok(ParamShape::ResourceHandle {
            value_ty: Box::new(value_ty),
            tier: ResourceTier::Pptr,
        });
    }
    // Raw pointer handle (`*mut V` / `*const V`), the `raw_ptr` tier.
    // Raw-pointer params were previously rejected outright ("unsupported
    // parameter type"), so treating them as resource handles is strictly
    // additive; an unpaired one gets the pairing diagnostic instead.
    if let Type::Ptr(type_ptr) = ty {
        return Ok(ParamShape::ResourceHandle {
            value_ty: Box::new((*type_ptr.elem).clone()),
            tier: ResourceTier::Raw,
        });
    }
    match ty {
        // The unit type -- a bare `x: ()` param, arising when a generic
        // element param (`x: T`) is instantiated at `#[vcheck(T = ())]` for
        // ZST length-boundary testing (`Vec::push` / `insert` growth
        // specs). One value, no bytes; sampled by the `()` strategy like
        // any other primitive. Mirrors the unit arm in
        // `classify_param_elem`.
        Type::Tuple(t) if t.elems.is_empty() => {
            return Ok(ParamShape::Primitive(ty.clone()));
        }
        // `[E; N]` by value.
        Type::Array(arr) => {
            let elem = classify_param_elem(&arr.elem, user_types)?;
            return Ok(ParamShape::OwnedArray(elem, arr.len.clone()));
        }
        // `impl Fn(&T) -> bool` -- predicate parameter. Recognized shape is
        // exactly a unary borrowed argument returning `bool`; anything else
        // (FnMut/FnOnce, multi-arg, non-bool return, owned arg) keeps the
        // unsupported-parameter diagnostic below.
        Type::ImplTrait(it) => {
            if let Some(elem) = pred_fn_elem(it, user_types) {
                return Ok(ParamShape::PredFn(elem?));
            }
            return Err(Error::new_spanned(
                ty,
                "verus_spec_check: unsupported `impl Trait` parameter. The only \
                 supported form is a predicate `impl Fn(&T) -> bool` (sampled \
                 from the `VcheckPred` family; see verus_spec_check_runtime::pred).",
            ));
        }
        Type::Reference(type_ref) => {
            let is_mut = type_ref.mutability.is_some();
            // `&mut [E]`: structurally vcheck can't easily diff slice elements
            // because the call could return a sub-slice mutated in place
            // and we have no way to compute "what was". Reject with a
            // clean diagnostic.
            if is_mut {
                if let Type::Slice(slice) = type_ref.elem.as_ref() {
                    // `&mut [E]`: sample as `Vec<E>` and pass via
                    // `.as_mut_slice()` at the call site. Contracts that
                    // read `old(s)@` / `s@` resolve to the pre/post
                    // deep_view of the underlying Vec.
                    let elem = classify_param_elem(&slice.elem, user_types)?;
                    return Ok(ParamShape::MutRef(Box::new(ParamShape::Slice(elem))));
                }
                if let Type::Array(arr) = type_ref.elem.as_ref() {
                    // `&mut [E; N]`: sample a `Vec<E>` of length N,
                    // materialize as a mutable `[E; N]` local, and pass
                    // `&mut local` at the call site.
                    let elem = classify_param_elem(&arr.elem, user_types)?;
                    return Ok(ParamShape::MutRef(Box::new(ParamShape::OwnedArray(
                        elem,
                        arr.len.clone(),
                    ))));
                }
                // Iterator params: `&mut slice::Iter<'a,T>` /
                // `&mut hash_set::Iter<'a,T>` / `&mut Keys<'a,K,V>`.
                // Recognized by the path's last segment; a bare `Iter`
                // (single-segment import) defaults to the slice iterator --
                // qualify the path (`hash_set::Iter<..>`) for set iterators.
                if let Type::Path(tp) = type_ref.elem.as_ref() {
                    if tp.qself.is_none() && !tp.path.segments.is_empty() {
                        let seg = tp.path.segments.last().unwrap();
                        let last = seg.ident.to_string();
                        let path_text: Vec<String> = tp
                            .path
                            .segments
                            .iter()
                            .map(|s| s.ident.to_string())
                            .collect();
                        if last == "Iter" || last == "Keys" {
                            let mut type_args = match &seg.arguments {
                                PathArguments::AngleBracketed(ab) => ab
                                    .args
                                    .iter()
                                    .filter_map(|a| match a {
                                        GenericArgument::Type(t) => Some(t),
                                        _ => None,
                                    })
                                    .collect::<Vec<_>>(),
                                _ => Vec::new(),
                            };
                            if last == "Keys" && type_args.len() == 2 {
                                let k = classify_param_elem(type_args.remove(0), user_types)?;
                                let v = classify_param_elem(type_args.remove(0), user_types)?;
                                return Ok(ParamShape::IterState {
                                    kind: IterKind::HashMapKeys,
                                    elem: k,
                                    val_elem: Some(v),
                                });
                            }
                            if last == "Iter" && type_args.len() == 1 {
                                let elem = classify_param_elem(type_args.remove(0), user_types)?;
                                let kind = if path_text.iter().any(|s| s == "hash_set") {
                                    IterKind::HashSetIter
                                } else {
                                    IterKind::SliceIter
                                };
                                return Ok(ParamShape::IterState {
                                    kind,
                                    elem,
                                    val_elem: None,
                                });
                            }
                        }
                    }
                }
                if let Type::Path(tp) = type_ref.elem.as_ref() {
                    if tp.qself.is_none() && tp.path.segments.len() == 1 {
                        let name = tp.path.segments[0].ident.to_string();
                        if name == "str" {
                            return Err(Error::new_spanned(
                                ty,
                                "verus_spec_check: `&mut str` parameters are not supported. \
Pass the data by `&mut String` so the harness can snapshot it.",
                            ));
                        }
                    }
                }
                // Recurse on the inner without the `mut` to get the inner
                // shape, then wrap in MutRef. We synthesize a non-mut
                // reference type wrapper so the inner classification
                // doesn't itself need to know about mutability -- except
                // we don't actually want a reference wrap, we want the
                // OWNED form. For `&mut Vec<T>`, the harness samples a
                // `Vec<T>` and passes `&mut <id>`. So drop the reference
                // and reclassify the inner as the owned shape.
                let inner_owned: Type = (*type_ref.elem).clone();
                let inner_shape = classify_param_type(&inner_owned, user_types)?;
                // Disallow nested mut-refs and other forms that don't
                // round-trip via clone+snapshot.
                match &inner_shape {
                    ParamShape::OwnedVec(_)
                    | ParamShape::OwnedVecDeque(_)
                    | ParamShape::OwnedHashMap(_, _)
                    | ParamShape::OwnedHashSet(_)
                    | ParamShape::OwnedBTreeMap(_, _)
                    | ParamShape::OwnedBTreeSet(_)
                    | ParamShape::OwnedString
                    | ParamShape::OwnedOption(_)
                    | ParamShape::OwnedResult(_, _)
                    | ParamShape::OwnedUserType(_)
                    | ParamShape::Primitive(_)
                    | ParamShape::StdValue { by_ref: false, .. }
                    // Slice & OwnedArray fall through here from the
                    // direct-match arms above. They're already wrapped
                    // by then, but accept them here too in case future
                    // call paths recurse.
                    | ParamShape::Slice(_)
                    | ParamShape::OwnedArray(_, _) => {}
                    _ => {
                        return Err(Error::new_spanned(
                            ty,
                            "verus_spec_check: `&mut <T>` is supported for owned shapes \
(Vec, HashMap, HashSet, String, Option, user type, primitive). The inner type \
here doesn't fit; pass an owned form instead.",
                        ));
                    }
                }
                return Ok(ParamShape::MutRef(Box::new(inner_shape)));
            }
            // `&[E]`
            if let Type::Slice(slice) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&slice.elem, user_types)?;
                return Ok(ParamShape::Slice(elem));
            }
            // `&[E; N]` -- fixed-size array reference.
            if let Type::Array(arr) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&arr.elem, user_types)?;
                return Ok(ParamShape::RefArray(elem, arr.len.clone()));
            }
            if let Some(kind) = std_value_kind(&type_ref.elem, user_types) {
                return Ok(ParamShape::StdValue {
                    ty: (*type_ref.elem).clone(),
                    kind,
                    by_ref: true,
                });
            }
            // `&str` -- string slice. Classify here BEFORE the user-type
            // path, since `str` isn't a user type and isn't capitalized.
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if name == "str" && matches!(seg.arguments, PathArguments::None) {
                        return Ok(ParamShape::RefStr);
                    }
                }
            }
            // `&Primitive` (e.g. `&u32`, `&i64`, `&bool`, `&char`). The
            // harness samples the primitive by value and a pre-call
            // `let bound: &T = &harness;` ref-binding ensures the call
            // sees a stable address. Excludes `&String` (handled below
            // by the user-type fallthrough), since `String` requires
            // its own sampling path.
            //
            // Peel `Type::Group`/`Type::Paren` off the inner so a
            // macro-substituted `&$uN` (which arrives as
            // `&Group(Path(u8))`) is recognized.
            {
                let inner = match type_ref.elem.as_ref() {
                    Type::Group(g) => g.elem.as_ref(),
                    Type::Paren(p) => p.elem.as_ref(),
                    other => other,
                };
                if let Type::Path(tp) = inner {
                    if tp.qself.is_none() && tp.path.segments.len() == 1 {
                        let seg = &tp.path.segments[0];
                        let name = seg.ident.to_string();
                        if matches!(seg.arguments, PathArguments::None)
                            && is_primitive_like(&name)
                            // `String` lives in `is_primitive_like` but
                            // sampling it as `RefPrimitive` would skip the
                            // dedicated `OwnedString` machinery. Keep
                            // `&String` falling through to the user-type
                            // path, which currently rejects it with a clean
                            // diagnostic.
                            && name != "String"
                            // `nat`/`int`/`real` are spec-only types -- they're
                            // in `is_primitive_like` so spec-level use sites
                            // accept them, but the harness can't sample
                            // them as values. Skip.
                            && name != "nat"
                            && name != "int"
                            && name != "real"
                        {
                            // Use the peeled `inner` so the carried `Type`
                            // is the canonical primitive (rather than the
                            // hygiene-wrapped form).
                            return Ok(ParamShape::RefPrimitive(inner.clone()));
                        }
                    }
                }
            }
            // `&OpaqueType` where the opaque type has a `VcheckConcretize` impl
            // (registered via `#[vcheck_view]`). Sampled + injected like the
            // owned form; the harness always passes a borrow anyway.
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if is_concretize_type(&name) && matches!(seg.arguments, PathArguments::None) {
                        return Ok(ParamShape::OpaqueConcretize(seg.ident.clone()));
                    }
                }
            }
            // `&UserType` or `&ExecUserType` (no generic args).
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if user_types.contains(&name) && matches!(seg.arguments, PathArguments::None) {
                        return Ok(ParamShape::RefUserType(seg.ident.clone()));
                    }
                    if let Some(stripped) = strip_exec_prefix(&name, user_types) {
                        if matches!(seg.arguments, PathArguments::None) {
                            return Ok(ParamShape::RefUserType(Ident::new(
                                stripped,
                                seg.ident.span(),
                            )));
                        }
                    }
                }
            }
            // A capitalized single-segment ref type that we don't recognise
            // is most likely a user-defined type living in another module.
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if name.chars().next().is_some_and(|c| c.is_uppercase()) {
                        return Err(Error::new_spanned(
                            ty,
                            format!(
                                "verus_spec_check: `&{name}` refers to a type that is not defined \
                                 inside this verus_spec_check_unverified! block.\n\n\
                                 The macro can only build a proptest strategy for types it can \
                                 see between its own braces; it cannot reach a `struct`/`enum` \
                                 declared in another module or file. Move `{name}` (and the \
                                 spec fns its contract uses) into this block to test against it.",
                                name = name
                            ),
                        ));
                    }
                }
            }
            Err(Error::new_spanned(
                ty,
                "verus_spec_check: unsupported reference parameter type. Supported: `&[E]` and \
                 `&UserType`. For `&Container<E>` (e.g. `&Vec<T>`, `&Option<T>`), supply \
                 the parameter by value (`Container<E>`) at the harness layer; the \
                 trusted body can still borrow internally.",
            ))
        }
        Type::Path(tp) if tp.qself.is_none() && !tp.path.segments.is_empty() => {
            let seg = tp.path.segments.last().unwrap();
            let name = seg.ident.to_string();
            let is_single_seg = tp.path.segments.len() == 1;
            match name.as_str() {
                "Vec" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_spec_check: expected Vec<T> with a type argument")
                    })?;
                    Ok(ParamShape::OwnedVec(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "VecDeque" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_spec_check: expected VecDeque<T> with a type argument",
                        )
                    })?;
                    Ok(ParamShape::OwnedVecDeque(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "Option" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_spec_check: expected Option<T> with a type argument")
                    })?;
                    Ok(ParamShape::OwnedOption(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "Result" => {
                    let (t, e) = first_two_type_args(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_spec_check: expected Result<T, E> with two type arguments",
                        )
                    })?;
                    Ok(ParamShape::OwnedResult(
                        classify_param_elem(t, user_types)?,
                        classify_param_elem(e, user_types)?,
                    ))
                }
                "HashMap" => {
                    let (k, v) = first_two_type_args(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_spec_check: expected HashMap<K, V> with two type arguments",
                        )
                    })?;
                    Ok(ParamShape::OwnedHashMap(
                        classify_param_elem(k, user_types)?,
                        classify_param_elem(v, user_types)?,
                    ))
                }
                "HashSet" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_spec_check: expected HashSet<T> with a type argument",
                        )
                    })?;
                    Ok(ParamShape::OwnedHashSet(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "BTreeMap" => {
                    let (k, v) = first_two_type_args(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_spec_check: expected BTreeMap<K, V> with two type arguments",
                        )
                    })?;
                    Ok(ParamShape::OwnedBTreeMap(
                        classify_param_elem(k, user_types)?,
                        classify_param_elem(v, user_types)?,
                    ))
                }
                "BTreeSet" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_spec_check: expected BTreeSet<T> with a type argument",
                        )
                    })?;
                    Ok(ParamShape::OwnedBTreeSet(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "Multiset" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(
                            ty,
                            "verus_spec_check: expected Multiset<T> with a type argument",
                        )
                    })?;
                    Ok(ParamShape::OwnedMultiset(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "String" if is_single_seg => Ok(ParamShape::OwnedString),
                _ => {
                    // Opaque `VcheckConcretize` type (registered via `#[vcheck_view]`).
                    if is_single_seg
                        && is_concretize_type(&name)
                        && matches!(seg.arguments, PathArguments::None)
                    {
                        return Ok(ParamShape::OpaqueConcretize(seg.ident.clone()));
                    }
                    if is_single_seg
                        && user_types.contains(&name)
                        && matches!(seg.arguments, PathArguments::None)
                    {
                        return Ok(ParamShape::OwnedUserType(seg.ident.clone()));
                    }
                    if is_single_seg {
                        if let Some(stripped) = strip_exec_prefix(&name, user_types) {
                            if matches!(seg.arguments, PathArguments::None) {
                                return Ok(ParamShape::OwnedUserType(Ident::new(
                                    stripped,
                                    seg.ident.span(),
                                )));
                            }
                        }
                    }
                    if is_single_seg && is_primitive_like(&name) {
                        return Ok(ParamShape::Primitive(ty.clone()));
                    }
                    if let Some(kind) = std_value_kind(ty, user_types) {
                        return Ok(ParamShape::StdValue {
                            ty: ty.clone(),
                            kind,
                            by_ref: false,
                        });
                    }
                    Err(Error::new_spanned(
                        ty,
                        format!(
                            "verus_spec_check: unsupported parameter type `{}`. Supported: primitives, \
                             `Vec<E>`, `&[E]`, `Option<E>`, `HashMap<K, V>`, `HashSet<E>`, \
                             `Multiset<E>`, `Range<E>` and the other `core::ops` ranges, \
                             `NonZero<E>`, `Ordering`, `&UserType`, and user-defined types.",
                            name
                        ),
                    ))
                }
            }
        }
        _ => Err(Error::new_spanned(
            ty,
            "verus_spec_check: unsupported parameter type.",
        )),
    }
}

pub fn first_type_arg(args: &PathArguments) -> Option<&Type> {
    if let PathArguments::AngleBracketed(ab) = args {
        for a in &ab.args {
            if let GenericArgument::Type(t) = a {
                return Some(t);
            }
        }
    }
    None
}

pub fn first_two_type_args(args: &PathArguments) -> Option<(&Type, &Type)> {
    if let PathArguments::AngleBracketed(ab) = args {
        let mut tys = ab.args.iter().filter_map(|a| match a {
            GenericArgument::Type(t) => Some(t),
            _ => None,
        });
        let a = tys.next()?;
        let b = tys.next()?;
        return Some((a, b));
    }
    None
}

pub fn is_primitive_like(name: &str) -> bool {
    matches!(
        name,
        "bool"
            | "char"
            | "u8"
            | "u16"
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
            | "String"
            // Verus spec integer types -- `nat` (non-negative ghost) and
            // `int` (unbounded ghost). At vcheck time we lower them to runtime
            // counterparts (u64 / i128) so contracts written in spec
            // arithmetic compile.
            | "nat"
            | "int"
            // Verus spec real type (unbounded ghost rational/real). Like
            // `int`/`nat`, it's spec-only: accepted at contract use sites
            // (lowered to `::verus_spec_check::__vcheck_real::*` / `SpecReal`), but never
            // sampled as an exec parameter.
            | "real"
    )
}

#[derive(Clone, Debug)]
pub enum ReturnShape {
    Unit,
    Primitive,
    OwnedVec(ParamElem),
    /// `VecDeque<T>` returned by value (e.g. `VecDeque::split_off`). Its
    /// view is `Seq<T>`; deep-view lowering materializes a contiguous `Vec`
    /// via `::verus_spec_check::__vcheck_vecdeque_slice`.
    OwnedVecDeque(ParamElem),
    /// `[T; N]` returned by value. The const length is retained for
    /// symmetry with `OwnedArray` on the param side; current emission only
    /// reads the element shape.
    #[allow(dead_code)]
    OwnedArray(ParamElem, Expr),
    OwnedOption(ParamElem),
    /// `Result<T, E>` returned by value.
    OwnedResult(ParamElem, ParamElem),
    OwnedHashMap,
    OwnedHashSet,
    OwnedBTreeMap,
    OwnedBTreeSet,
    OwnedMultiset,
    /// Opaque `VcheckConcretize` type returned by value (e.g. `UBig`). The
    /// harness holds the real result; contract `view(ret)` calls lower to
    /// `ret.vcheck_realize()`.
    OpaqueConcretize(Ident),
    OwnedUserType(Ident),
    /// `&T` where `T: Copy` (or known primitive). The harness adapts by
    /// dereferencing the result before checking the contract.
    RefPrimitive(Type),
    /// `&[T]`. The harness passes the borrowed slice through for
    /// `deep_view` purposes.
    RefSlice(ParamElem),
    /// `&mut [T]`. The harness snapshots the referent into an owned `Vec<T>`
    /// immediately after the call so the source mutable borrow can end before
    /// post-state parameters and advisory probes are evaluated.
    MutRefSlice(ParamElem),
    /// `&[T; N]`. Same engine treatment as `RefSlice`. The const length is
    /// retained on the variant for symmetry with `OwnedArray` and so future
    /// emission paths (e.g. fixed-length contract folding) can read it.
    #[allow(dead_code)]
    RefArray(ParamElem, Expr),
    /// `&mut [T; N]`, snapshotted like `MutRefSlice` after the call.
    #[allow(dead_code)]
    MutRefArray(ParamElem, Expr),
    /// `&UserType`. Same engine treatment as `OwnedUserType` once
    /// dereferenced.
    RefUserType(Ident),
    /// `&str`. Lowered to `Seq<char>` for contract evaluation.
    RefStr,
    /// `String`. Same as `RefStr` for contract purposes; harness binds the
    /// returned `String` and converts to chars on demand.
    OwnedString,
    /// `core::cmp::Ordering` returned by value. The harness compares against
    /// `Ordering` constants via `PartialEq` (which `Ordering` derives).
    /// Recognized regardless of the path qualifier (`Ordering` / `cmp::Ordering`
    /// / `core::cmp::Ordering` / `std::cmp::Ordering`) so contracts can use
    /// the common forms.
    OwnedOrdering,
    /// `Option<core::cmp::Ordering>` returned by value (the `partial_cmp`
    /// shape). Like `OwnedOrdering`, contracts compare it directly against
    /// `Some(Ordering::Less)` / `None` via the derived `PartialEq`; it is
    /// never sampled, so `Ordering` needs no `ParamElem` entry.
    OwnedOptionOrdering,
    /// A 2-tuple `(A, B)` returned by value. Each element has its own
    /// `ReturnShape` (boxed for size). Contracts access `.0` / `.1` and
    /// the harness emits `let ret = call(); let __ret_0 = ret.0; ...`
    /// to project for `deep_view` evaluation.
    ///
    /// Limitation: only 2-tuples are supported in this initial round
    /// because the most common use case (`<[T]>::split_at` etc.) is
    /// 2-tuple. Larger arities are rejected with a clean diagnostic.
    /// Field reads happen via match destructuring elsewhere; the dead-
    /// code lint can't see through that pattern, so suppress it.
    #[allow(dead_code)]
    Tuple2(Box<ReturnShape>, Box<ReturnShape>),
    /// A std value type returned by value, see [`StdValueKind`].
    StdValue(Type, StdValueKind),
}

pub fn classify_return(
    ret: &ReturnType,
    user_types: &HashSet<String>,
    self_ty_for_method: Option<&Ident>,
) -> Result<ReturnShape, Error> {
    let ty = match ret {
        ReturnType::Default => return Ok(ReturnShape::Unit),
        ReturnType::Type(_, _, _, ty) => ty,
    };
    // Substitute `Self` (capital-S identifier or `Self::...` path) with the
    // concrete impl's Self type before classification. This is what lets a
    // method written as `fn make() -> Self` be sampled and converted as the
    // user type.
    let mut owner;
    let ty_ref: &Type = if let Some(self_ty) = self_ty_for_method {
        owner = (**ty).clone();
        replace_self_ty(&mut owner, self_ty);
        &owner
    } else {
        ty.as_ref()
    };
    // Peel off `Type::Group` (macro-substitution hygiene) and `Type::Paren`
    // (parenthesized) wrappers so a macro-expanded `$uN` return like `u8`
    // reaches the inner match arms as a plain `Type::Path`. Same fix as in
    // `classify_param_type` / `classify_param_elem`.
    let ty_ref: &Type = match ty_ref {
        Type::Group(g) => g.elem.as_ref(),
        Type::Paren(p) => p.elem.as_ref(),
        _ => ty_ref,
    };
    match ty_ref {
        // `[E; N]` by value.
        Type::Array(arr) => {
            let elem = classify_param_elem(&arr.elem, user_types)?;
            return Ok(ReturnShape::OwnedArray(elem, arr.len.clone()));
        }
        Type::Reference(type_ref) => {
            // `&[T]`
            if let Type::Slice(slice) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&slice.elem, user_types)?;
                return Ok(if type_ref.mutability.is_some() {
                    ReturnShape::MutRefSlice(elem)
                } else {
                    ReturnShape::RefSlice(elem)
                });
            }
            // `&[T; N]`
            if let Type::Array(arr) = type_ref.elem.as_ref() {
                let elem = classify_param_elem(&arr.elem, user_types)?;
                return Ok(if type_ref.mutability.is_some() {
                    ReturnShape::MutRefArray(elem, arr.len.clone())
                } else {
                    ReturnShape::RefArray(elem, arr.len.clone())
                });
            }
            // `&str`
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if name == "str" && matches!(seg.arguments, PathArguments::None) {
                        return Ok(ReturnShape::RefStr);
                    }
                }
            }
            // `&Path`
            if let Type::Path(tp) = type_ref.elem.as_ref() {
                if tp.qself.is_none() && tp.path.segments.len() == 1 {
                    let seg = &tp.path.segments[0];
                    let name = seg.ident.to_string();
                    if user_types.contains(&name) && matches!(seg.arguments, PathArguments::None) {
                        return Ok(ReturnShape::RefUserType(seg.ident.clone()));
                    }
                    if is_primitive_like(&name) {
                        return Ok(ReturnShape::RefPrimitive((*type_ref.elem).clone()));
                    }
                    if name.chars().next().is_some_and(|c| c.is_uppercase()) {
                        return Ok(ReturnShape::RefUserType(seg.ident.clone()));
                    }
                }
            }
            Err(Error::new_spanned(
                ty,
                "verus_spec_check: unsupported reference return type. Supported: \
`&T` for primitives, `&[T]`, and `&UserType`.",
            ))
        }
        Type::Path(tp) if tp.qself.is_none() && !tp.path.segments.is_empty() => {
            // Use the LAST segment as the type's name. This lets us handle
            // both bare `Vec<T>` and qualified `alloc::vec::Vec<T>` /
            // `std::collections::HashMap<K, V>` / etc. -- common in vstd code.
            let seg = tp.path.segments.last().unwrap();
            let name = seg.ident.to_string();
            // Single-segment paths can be user types; multi-segment paths
            // can't (we'd need full path resolution to map them).
            let is_single_seg = tp.path.segments.len() == 1;
            match name.as_str() {
                "Vec" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_spec_check: expected Vec<T> in return type")
                    })?;
                    Ok(ReturnShape::OwnedVec(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "VecDeque" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_spec_check: expected VecDeque<T> in return type")
                    })?;
                    Ok(ReturnShape::OwnedVecDeque(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "Option" => {
                    let inner = first_type_arg(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_spec_check: expected Option<T> in return type")
                    })?;
                    // `Option<Ordering>` (the `partial_cmp` return): `Ordering`
                    // is not a `ParamElem` (it's never sampled), but as a
                    // return it needs no deep-view -- contracts compare it
                    // directly against `Some(Ordering::Less)` etc. via the
                    // derived `PartialEq`. Recognized by last path segment
                    // like the bare `Ordering` arm below.
                    if let Type::Path(inner_tp) = inner {
                        if inner_tp
                            .path
                            .segments
                            .last()
                            .is_some_and(|s| s.ident == "Ordering")
                        {
                            return Ok(ReturnShape::OwnedOptionOrdering);
                        }
                    }
                    Ok(ReturnShape::OwnedOption(classify_param_elem(
                        inner, user_types,
                    )?))
                }
                "Result" => {
                    let (t, e) = first_two_type_args(&seg.arguments).ok_or_else(|| {
                        Error::new_spanned(ty, "verus_spec_check: expected Result<T, E> in return type")
                    })?;
                    // B3: the `Ok` element must classify normally (its value is
                    // commonly extracted/compared via `ret->Ok_0`), but the
                    // `Err` element of a *returned* Result is only ever observed
                    // through its variant (`ret is Err`) -- the harness never
                    // generates it and never compares its payload. So an opaque
                    // std error type (e.g. `core::num::TryFromIntError`) is
                    // acceptable there: classify it leniently rather than
                    // rejecting the whole spec.
                    Ok(ReturnShape::OwnedResult(
                        classify_param_elem(t, user_types)?,
                        classify_return_result_err_elem(e, user_types),
                    ))
                }
                "HashMap" => Ok(ReturnShape::OwnedHashMap),
                "HashSet" => Ok(ReturnShape::OwnedHashSet),
                "BTreeMap" => Ok(ReturnShape::OwnedBTreeMap),
                "BTreeSet" => Ok(ReturnShape::OwnedBTreeSet),
                "Multiset" => Ok(ReturnShape::OwnedMultiset),
                "String" => Ok(ReturnShape::OwnedString),
                // `Ordering` / `cmp::Ordering` / `core::cmp::Ordering` /
                // `std::cmp::Ordering`. We recognize the type by its last
                // segment name and accept any path prefix because the
                // canonical form varies across vstd specs.
                "Ordering" => Ok(ReturnShape::OwnedOrdering),
                _ => {
                    if is_single_seg && is_concretize_type(&name) {
                        Ok(ReturnShape::OpaqueConcretize(seg.ident.clone()))
                    } else if is_single_seg && user_types.contains(&name) {
                        Ok(ReturnShape::OwnedUserType(seg.ident.clone()))
                    } else if let Some(kind) = std_value_kind(ty_ref, user_types) {
                        Ok(ReturnShape::StdValue(ty_ref.clone(), kind))
                    } else if is_single_seg && is_primitive_like(&name) {
                        Ok(ReturnShape::Primitive)
                    } else if is_single_seg && name.chars().next().is_some_and(|c| c.is_uppercase())
                    {
                        // External user type (defined + `#[vcheck_provide]`'d in
                        // another module). Same trait-resolved treatment as
                        // a user type.
                        Ok(ReturnShape::OwnedUserType(seg.ident.clone()))
                    } else {
                        Err(Error::new_spanned(
                            ty,
                            format!(
                                "verus_spec_check: unsupported return type `{}`. Supported: \
primitives, `Vec<E>`, `Option<E>`, `HashMap<K, V>`, `HashSet<E>`, `Multiset<E>`, \
and user-defined types (including `Self` inside an impl).",
                                name
                            ),
                        ))
                    }
                }
            }
        }
        Type::Tuple(tt) if tt.elems.is_empty() => Ok(ReturnShape::Unit),
        Type::Tuple(tt) if tt.elems.len() == 2 => {
            // 2-tuple return. Each element is classified as if it were
            // its own return type, then composed into Tuple2. The
            // recursive call goes through classify_return so each elem
            // can be e.g. `&[T]` or `Option<T>` etc.
            let mut iter = tt.elems.iter();
            let a = iter.next().unwrap();
            let b = iter.next().unwrap();
            // Build a synthetic ReturnType for each elem and classify.
            let synth_a = ReturnType::Type(
                verus_syn::Token![->](proc_macro2::Span::call_site()),
                None,
                None,
                Box::new(a.clone()),
            );
            let synth_b = ReturnType::Type(
                verus_syn::Token![->](proc_macro2::Span::call_site()),
                None,
                None,
                Box::new(b.clone()),
            );
            let sa = classify_return(&synth_a, user_types, self_ty_for_method)?;
            let sb = classify_return(&synth_b, user_types, self_ty_for_method)?;
            Ok(ReturnShape::Tuple2(Box::new(sa), Box::new(sb)))
        }
        Type::Tuple(_) => Err(Error::new_spanned(
            ty,
            "verus_spec_check: tuple returns of arity > 2 are not yet supported. \
             Restructure the spec to return a 2-tuple or a struct.",
        )),
        _ => Err(Error::new_spanned(
            ty,
            "verus_spec_check: unsupported return type. Supported: primitives, `Vec<E>`, \
`Option<E>`, `HashMap<K, V>`, `HashSet<E>`, `Multiset<E>`, and user-defined types \
(including `Self` inside an impl).",
        )),
    }
}

/// Replace every occurrence of the `Self` type (in `Type::Path`s) with the
/// concrete impl Self type. Recurses into generic arguments, references,
/// slices, and tuples.
pub fn replace_self_ty(ty: &mut Type, self_ty: &Ident) {
    use verus_syn::visit_mut::{self, VisitMut};
    struct R<'a> {
        self_ty: &'a Ident,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_path_mut(&mut self, tp: &mut verus_syn::TypePath) {
            // Replace a leading `Self` segment in a non-qualified path with the
            // concrete type (works for `Self`, `Self::Item`, etc.).
            if tp.qself.is_none() && !tp.path.segments.is_empty() {
                if tp.path.segments[0].ident == "Self" {
                    let span = tp.path.segments[0].ident.span();
                    tp.path.segments[0].ident = Ident::new(&self.self_ty.to_string(), span);
                }
            }
            visit_mut::visit_type_path_mut(self, tp);
        }
    }
    let mut r = R { self_ty };
    r.visit_type_mut(ty);
}

#[cfg(test)]
mod real_acceptance_tests {
    //! `real` is accepted at spec-level use sites exactly like the
    //! other Verus spec numeric types (`int`/`nat`) -- it lives in
    //! `is_primitive_like` so contract expressions referencing it classify,
    //! while the dedicated sampling-skip keeps it from being generated as a
    //! parameter value (a `real` value only ever arises derived via `as real`).

    use super::is_primitive_like;

    #[test]
    fn real_is_primitive_like_alongside_int_and_nat() {
        assert!(is_primitive_like("real"));
        assert!(is_primitive_like("int"));
        assert!(is_primitive_like("nat"));
    }

    #[test]
    fn non_spec_types_are_not_primitive_like() {
        assert!(!is_primitive_like("Foo"));
        assert!(!is_primitive_like("Seq"));
    }
}

#[cfg(test)]
mod std_value_tests {
    use super::*;

    fn uts(names: &[&str]) -> HashSet<String> {
        names.iter().map(|n| n.to_string()).collect()
    }

    fn ty(src: &str) -> Type {
        verus_syn::parse_str(src).unwrap()
    }

    fn kind_of(src: &str) -> Option<StdValueKind> {
        std_value_kind(&ty(src), &uts(&[]))
    }

    fn param(src: &str) -> ParamShape {
        classify_param_type(&ty(src), &uts(&[])).unwrap()
    }

    #[test]
    fn recognizes_std_value_types() {
        assert_eq!(kind_of("core::ops::Range<u8>"), Some(StdValueKind::Range));
        assert_eq!(kind_of("RangeInclusive<char>"), Some(StdValueKind::RangeInclusive));
        assert_eq!(kind_of("RangeFull"), Some(StdValueKind::RangeFull));
        assert_eq!(kind_of("core::num::NonZero<i64>"), Some(StdValueKind::NonZero));
        assert_eq!(kind_of("NonZeroU8"), Some(StdValueKind::NonZero));
        assert_eq!(kind_of("core::cmp::Ordering"), Some(StdValueKind::Ordering));
        assert_eq!(kind_of("std::sync::atomic::Ordering"), None);
        assert_eq!(kind_of("Range<usize, usize>"), None);
        assert_eq!(std_value_kind(&ty("Ordering"), &uts(&["Ordering"])), None);
    }

    #[test]
    fn params_classify_and_lower() {
        let id = format_ident!("x");
        let owned = param("Range<usize>");
        assert_eq!(owned.arg_for_real_call(&id).to_string(), quote! { x.clone() }.to_string());
        let by_ref = param("&RangeInclusive<u8>");
        assert_eq!(by_ref.arg_for_real_call(&id).to_string(), quote! { &x }.to_string());
        assert_eq!(
            by_ref.call_form_for_deep_view(&id).to_string(),
            quote! { ::verus_spec_check::__vcheck_range_inclusive_view(&x) }.to_string()
        );
        assert_eq!(
            param("NonZero<u32>").call_form_for_deep_view(&id).to_string(),
            quote! { x.get() }.to_string()
        );
        let mutable = param("&mut Range<u16>");
        assert!(matches!(&mutable, ParamShape::MutRef(inner)
            if matches!(**inner, ParamShape::StdValue { by_ref: false, .. })));
        assert!(mutable.pre_state_let(&id).is_some());
        assert!(matches!(param("Option<Ordering>"), ParamShape::OwnedOption(ParamElem::Primitive(_))));
    }

    #[test]
    fn std_value_returns_classify() {
        let ret = |src: &str| {
            let r: ReturnType = verus_syn::parse_str(&format!("-> {src}")).unwrap();
            classify_return(&r, &uts(&[]), None).unwrap()
        };
        assert!(matches!(ret("NonZero<u32>"), ReturnShape::StdValue(_, StdValueKind::NonZero)));
        assert!(matches!(ret("Option<NonZeroU16>"), ReturnShape::OwnedOption(ParamElem::Primitive(_))));
        assert!(matches!(ret("Ordering"), ReturnShape::OwnedOrdering));
    }
}
