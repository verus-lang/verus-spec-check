use super::*;

// ---------------------------------------------------------------------------
// Bolero backend: TypeGenerator + VcheckGen emission for user types.
//
// Only emitted when a `#[vcheck(backend = "bolero")]` target exists in the same
// block (the impls reference feature-gated `::verus_spec_check::{VcheckGen,
// bolero_generator}` paths that don't exist unless the umbrella's `bolero`
// feature is on). The `TypeGenerator` impl generates each field through its
// edge-biased `VcheckGen` generator (parity with the proptest field strategies);
// the `VcheckGen` impl is a thin `produce::<Self>()` over that `TypeGenerator`.
// ---------------------------------------------------------------------------

/// Expression that pulls one field value of type `ty` from `driver`, using the
/// field type's edge-biased `VcheckGen` generator. UFCS-qualified so no trait
/// import is needed in the generated `generate` body.
pub fn bolero_field_generate_expr(
    ty: &Type,
    user_types: &HashSet<String>,
) -> Result<TokenStream2, Error> {
    let elem = classify_param_elem(ty, user_types)?;
    let elem_ty = elem.harness_type();
    Ok(quote! {
        ::verus_spec_check::bolero_generator::ValueGenerator::generate(
            &<#elem_ty as ::verus_spec_check::VcheckGen>::vcheck_gen(),
            driver,
        )?
    })
}

/// Emit `TypeGenerator` + `VcheckGen` for a user struct (bolero backend).
pub fn emit_struct_bolero_impls(
    item_struct: &ItemStruct,
    user_types: &HashSet<String>,
) -> Result<TokenStream2, Error> {
    let name = &item_struct.ident;
    let ctor = match &item_struct.fields {
        Fields::Named(named) => {
            let inits = named
                .named
                .iter()
                .map(|f| {
                    let fname = f.ident.as_ref().unwrap();
                    let g = bolero_field_generate_expr(&f.ty, user_types)?;
                    Ok(quote! { #fname: #g })
                })
                .collect::<Result<Vec<_>, Error>>()?;
            quote! { #name { #(#inits),* } }
        }
        Fields::Unnamed(unnamed) => {
            let inits = unnamed
                .unnamed
                .iter()
                .map(|f| bolero_field_generate_expr(&f.ty, user_types))
                .collect::<Result<Vec<_>, Error>>()?;
            quote! { #name( #(#inits),* ) }
        }
        Fields::Unit => quote! { #name },
    };
    Ok(quote! {
        impl ::verus_spec_check::bolero_generator::TypeGenerator for #name {
            fn generate<D: ::verus_spec_check::bolero_generator::Driver>(
                driver: &mut D,
            ) -> ::std::option::Option<Self> {
                ::std::option::Option::Some(#ctor)
            }
        }
        impl ::verus_spec_check::VcheckGen for #name {
            fn vcheck_gen() -> impl ::verus_spec_check::bolero_generator::ValueGenerator<Output = Self> {
                ::verus_spec_check::bolero_generator::produce::<#name>()
            }
        }
    })
}

/// Emit `TypeGenerator` + `VcheckGen` for a user enum (bolero backend). A uniform
/// tag picks the variant; each variant's fields use their edge-biased
/// `VcheckGen` generators.
pub fn emit_enum_bolero_impls(
    item_enum: &ItemEnum,
    user_types: &HashSet<String>,
) -> Result<TokenStream2, Error> {
    let name = &item_enum.ident;
    let n = item_enum.variants.len() as u32;
    if n == 0 {
        return Err(Error::new_spanned(
            item_enum,
            "verus_spec_check: cannot generate a bolero generator for an empty enum",
        ));
    }

    let mut arms: Vec<TokenStream2> = Vec::new();
    for (i, variant) in item_enum.variants.iter().enumerate() {
        let vname = &variant.ident;
        let build = match &variant.fields {
            Fields::Named(named) => {
                let inits = named
                    .named
                    .iter()
                    .map(|f| {
                        let fname = f.ident.as_ref().unwrap();
                        let g = bolero_field_generate_expr(&f.ty, user_types)?;
                        Ok(quote! { #fname: #g })
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                quote! { #name::#vname { #(#inits),* } }
            }
            Fields::Unnamed(unnamed) => {
                let inits = unnamed
                    .unnamed
                    .iter()
                    .map(|f| bolero_field_generate_expr(&f.ty, user_types))
                    .collect::<Result<Vec<_>, Error>>()?;
                quote! { #name::#vname( #(#inits),* ) }
            }
            Fields::Unit => quote! { #name::#vname },
        };
        // Last variant is the catch-all so the match is exhaustive over u32.
        if i as u32 == n - 1 {
            arms.push(quote! { _ => #build });
        } else {
            let idx = i as u32;
            arms.push(quote! { #idx => #build });
        }
    }

    Ok(quote! {
        impl ::verus_spec_check::bolero_generator::TypeGenerator for #name {
            fn generate<D: ::verus_spec_check::bolero_generator::Driver>(
                driver: &mut D,
            ) -> ::std::option::Option<Self> {
                // Uniform tag (not edge-biased) so variant selection is even.
                let __vcheck_tag: u32 = ::verus_spec_check::bolero_generator::ValueGenerator::generate(
                    &::verus_spec_check::bolero_generator::produce::<u32>(),
                    driver,
                )?;
                ::std::option::Option::Some(match __vcheck_tag % #n {
                    #(#arms),*
                })
            }
        }
        impl ::verus_spec_check::VcheckGen for #name {
            fn vcheck_gen() -> impl ::verus_spec_check::bolero_generator::ValueGenerator<Output = Self> {
                ::verus_spec_check::bolero_generator::produce::<#name>()
            }
        }
    })
}

/// Build the expression converting a field of type `ty` (accessed via `expr`,
/// which yields the user-side value) into its `Exec*` form.
pub fn elem_to_exec_expr(
    ty: &Type,
    expr: TokenStream2,
    user_types: &HashSet<String>,
) -> TokenStream2 {
    match classify_param_elem(ty, user_types) {
        Ok(ParamElem::Primitive(_)) => expr,
        Ok(ParamElem::UserType(name)) => {
            // Fully-qualified trait call: resolves across files and triggers
            // the ToExecModel `on_unimplemented` diagnostic if unprovided.
            quote! {
                <#name as ::verus_spec_check::ToExecModel>::to_exec_model(&#expr)
            }
        }
        // Total fallback: keep as-is.
        Err(_) => quote! { #expr },
    }
}

pub fn emit_clone_impl_struct(name: &Ident, fields: &Fields) -> TokenStream2 {
    let body = match fields {
        Fields::Named(named) => {
            let field_clones = named.named.iter().map(|f| {
                let n = f.ident.as_ref().unwrap();
                quote! { #n: self.#n.clone() }
            });
            quote! { #name { #(#field_clones),* } }
        }
        Fields::Unnamed(unnamed) => {
            let field_clones = (0..unnamed.unnamed.len()).map(|i| {
                let idx = verus_syn::Index::from(i);
                quote! { self.#idx.clone() }
            });
            quote! { #name(#(#field_clones),*) }
        }
        Fields::Unit => quote! { #name },
    };
    quote! {
        impl ::std::clone::Clone for #name {
            fn clone(&self) -> Self {
                #body
            }
        }
    }
}

pub fn emit_debug_impl(name: &Ident) -> TokenStream2 {
    // We can't `#[derive(Debug)]` on the Verus-side type (Verus's derive
    // handling rejects it), and we can't reference the user type's fields
    // generically here without re-deriving. Instead, Debug delegates to the
    // engine's `Exec*` companion (which DOES derive a full Debug) by
    // converting through the generated `__vcheck_to_exec_*` fn. This gives
    // useful counterexample output ("ExecUser { name_len: 1, ... }").
    let conv = to_exec_fn_name(name);
    quote! {
        impl ::std::fmt::Debug for #name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                ::std::fmt::Debug::fmt(&#conv(self), f)
            }
        }
    }
}

pub fn emit_clone_impl_enum(name: &Ident, item_enum: &ItemEnum) -> TokenStream2 {
    let arms = item_enum.variants.iter().map(|variant| {
        let vname = &variant.ident;
        match &variant.fields {
            Fields::Named(named) => {
                let names: Vec<&Ident> = named
                    .named
                    .iter()
                    .map(|f| f.ident.as_ref().unwrap())
                    .collect();
                let clones = names.iter().map(|n| quote! { #n: #n.clone() });
                quote! {
                    #name::#vname { #(#names),* } => #name::#vname { #(#clones),* }
                }
            }
            Fields::Unnamed(unnamed) => {
                let n = unnamed.unnamed.len();
                let names: Vec<Ident> = (0..n).map(|i| format_ident!("__f{}", i)).collect();
                let clones = names.iter().map(|n| quote! { #n.clone() });
                quote! {
                    #name::#vname(#(#names),*) => #name::#vname(#(#clones),*)
                }
            }
            Fields::Unit => quote! {
                #name::#vname => #name::#vname
            },
        }
    });
    quote! {
        impl ::std::clone::Clone for #name {
            fn clone(&self) -> Self {
                match self {
                    #(#arms),*
                }
            }
        }
    }
}

#[cfg(test)]
mod bolero_emit_tests {
    //! Unit tests for the bolero backend emission. These
    //! exercise the pure token-producing functions directly so we don't need
    //! the full verus toolchain.

    use super::*;
    use crate::vcheck_attr::VcheckBackend;
    use std::collections::HashSet;

    /// Collapse a token stream to whitespace-normalized text for substring
    /// assertions (quote! already single-spaces, but this is robust).
    fn norm(ts: &TokenStream2) -> String {
        ts.to_string()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn no_user_types() -> HashSet<String> {
        HashSet::new()
    }

    // ---- struct generator emission -----------------------------------------

    #[test]
    fn struct_named_emits_typegenerator_and_vcheckgen() {
        let s: ItemStruct = verus_syn::parse_quote! {
            struct Point { x: u32, y: i64 }
        };
        let out = norm(&emit_struct_bolero_impls(&s, &no_user_types()).unwrap());
        assert!(
            out.contains(":: verus_spec_check :: bolero_generator :: TypeGenerator for Point"),
            "{out}"
        );
        assert!(out.contains(":: verus_spec_check :: VcheckGen for Point"), "{out}");
        // VcheckGen delegates to produce::<Point>().
        assert!(
            out.contains(":: verus_spec_check :: bolero_generator :: produce :: < Point > ()"),
            "{out}"
        );
        // Each field is generated through its edge-biased VcheckGen generator.
        assert!(
            out.contains("< u32 as :: verus_spec_check :: VcheckGen > :: vcheck_gen"),
            "{out}"
        );
        assert!(
            out.contains("< i64 as :: verus_spec_check :: VcheckGen > :: vcheck_gen"),
            "{out}"
        );
        // Named-field construction.
        assert!(out.contains("Point { x :"), "{out}");
    }

    #[test]
    fn struct_tuple_emits_positional_ctor() {
        let s: ItemStruct = verus_syn::parse_quote! {
            struct Pair(u8, u8);
        };
        let out = norm(&emit_struct_bolero_impls(&s, &no_user_types()).unwrap());
        assert!(out.contains("TypeGenerator for Pair"), "{out}");
        assert!(out.contains("Pair ("), "{out}");
        assert!(
            out.contains("< u8 as :: verus_spec_check :: VcheckGen > :: vcheck_gen"),
            "{out}"
        );
    }

    #[test]
    fn struct_unit_emits_bare_ctor() {
        let s: ItemStruct = verus_syn::parse_quote! {
            struct Marker;
        };
        let out = norm(&emit_struct_bolero_impls(&s, &no_user_types()).unwrap());
        assert!(out.contains("TypeGenerator for Marker"), "{out}");
        assert!(out.contains("VcheckGen for Marker"), "{out}");
        // Unit ctor: `Some(Marker)` — no field generation.
        assert!(
            out.contains("Some (Marker)") || out.contains("Some ( Marker )"),
            "{out}"
        );
    }

    // ---- enum generator emission ----------------------------------

    #[test]
    fn enum_emits_tag_selector_and_catchall() {
        let e: ItemEnum = verus_syn::parse_quote! {
            enum Choice { Left, Right(u32), Both { x: i32, y: i32 } }
        };
        let out = norm(&emit_enum_bolero_impls(&e, &no_user_types()).unwrap());
        assert!(out.contains("TypeGenerator for Choice"), "{out}");
        assert!(out.contains("VcheckGen for Choice"), "{out}");
        // Uniform tag over 3 variants.
        assert!(out.contains("% 3u32"), "{out}");
        // Uniform tag draws via produce::<u32>() (not edge-biased).
        assert!(
            out.contains(":: verus_spec_check :: bolero_generator :: produce :: < u32 > ()"),
            "{out}"
        );
        // Variant field generation uses VcheckGen.
        assert!(
            out.contains("< u32 as :: verus_spec_check :: VcheckGen > :: vcheck_gen"),
            "{out}"
        );
        assert!(
            out.contains("< i32 as :: verus_spec_check :: VcheckGen > :: vcheck_gen"),
            "{out}"
        );
        // Exhaustive match: last variant is the catch-all arm.
        assert!(out.contains("_ =>"), "{out}");
        // First variant maps to literal index 0.
        assert!(out.contains("0u32 =>"), "{out}");
    }

    #[test]
    fn enum_empty_is_error() {
        let e: ItemEnum = verus_syn::parse_quote! {
            enum Void {}
        };
        assert!(emit_enum_bolero_impls(&e, &no_user_types()).is_err());
    }

    #[test]
    fn enum_single_variant_is_just_catchall() {
        let e: ItemEnum = verus_syn::parse_quote! {
            enum One { Only(u8) }
        };
        let out = norm(&emit_enum_bolero_impls(&e, &no_user_types()).unwrap());
        // n == 1: the sole variant is the catch-all; no `0u32 =>` arm.
        assert!(out.contains("_ =>"), "{out}");
        assert!(out.contains("% 1u32"), "{out}");
    }

    // ---- User-type fields inside a struct ----------------------------------

    #[test]
    fn struct_with_user_type_field_uses_vcheckgen_of_that_type() {
        let mut uts = HashSet::new();
        uts.insert("Inner".to_string());
        let s: ItemStruct = verus_syn::parse_quote! {
            struct Outer { inner: Inner, n: u8 }
        };
        let out = norm(&emit_struct_bolero_impls(&s, &uts).unwrap());
        // The user-type field is generated via <Inner as VcheckGen>::vcheck_gen().
        assert!(
            out.contains("< Inner as :: verus_spec_check :: VcheckGen > :: vcheck_gen"),
            "{out}"
        );
    }

    // ---- element_gen_for_shape ---------------------------------------------

    #[test]
    fn element_gen_some_for_collections_none_for_scalars() {
        let u8_ty: Type = verus_syn::parse_quote! { u8 };
        // Vec<u8> / &[u8] / [u8; N] yield an element generator.
        for shape in [
            ParamShape::OwnedVec(ParamElem::Primitive(u8_ty.clone())),
            ParamShape::Slice(ParamElem::Primitive(u8_ty.clone())),
        ] {
            let (elem_ty, gen) = element_gen_for_shape(&shape).expect("collection has elem gen");
            assert_eq!(norm(&elem_ty), "u8");
            assert!(norm(&gen).contains("< u8 as :: verus_spec_check :: VcheckGen > :: vcheck_gen"));
        }
        // A bare primitive is not a len()-sized collection.
        assert!(element_gen_for_shape(&ParamShape::Primitive(u8_ty)).is_none());
    }

    #[test]
    fn element_gen_user_type_element() {
        let shape = ParamShape::OwnedVec(ParamElem::UserType(Ident::new(
            "Widget",
            proc_macro2::Span::call_site(),
        )));
        let (elem_ty, gen) = element_gen_for_shape(&shape).unwrap();
        assert_eq!(norm(&elem_ty), "Widget");
        assert!(norm(&gen).contains("< Widget as :: verus_spec_check :: VcheckGen > :: vcheck_gen"));
    }

    // ---- backend threading through ContractTarget -----------------

    #[test]
    fn contract_target_reports_selected_backend() {
        let bolero = ContractTarget::FreeFn {
            item_fn: verus_syn::parse_quote! { fn foo() {} },
            miri_skip: false,
            backend: VcheckBackend::Bolero,
            bolero_mode: Some(crate::vcheck_attr::VcheckBoleroMode::Fuzz),
            skip_regular_harness: false,
        };
        assert_eq!(bolero.backend(), VcheckBackend::Bolero);
        assert_eq!(
            bolero.bolero_mode(),
            Some(crate::vcheck_attr::VcheckBoleroMode::Fuzz)
        );

        let proptest = ContractTarget::FreeFn {
            item_fn: verus_syn::parse_quote! { fn bar() {} },
            miri_skip: false,
            backend: VcheckBackend::Proptest,
            bolero_mode: None,
            skip_regular_harness: false,
        };
        assert_eq!(proptest.backend(), VcheckBackend::Proptest);
        assert_eq!(proptest.bolero_mode(), None);
    }

    // ---- &mut Vec<T, A> (allocator-generic) end-to-end expand --------------

    /// The monomorphized wrapper for an allocator-generic `&mut Vec<T, A>`
    /// spec (as produced by `vcheck_provide_preprocess`) should expand into a
    /// real harness. This mirrors vstd's `Vec::swap_remove` after
    /// monomorphization to `Vec<u32, core::alloc::Global>`.
    #[test]
    fn expand_mut_vec_allocator_generic_produces_harness() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_Vec_T_A_swap_remove(
                vec: &mut ::std::vec::Vec<u32, core::alloc::Global>,
                i: usize,
            ) -> (element: u32)
                requires
                    i < old(vec).len(),
                ensures
                    element == old(vec)[i as int],
                    final(vec)@ == old(vec)@.update(i as int, old(vec)@.last()).drop_last(),
            {
                ::std::vec::Vec::<u32, core::alloc::Global>::swap_remove(vec, i)
            }
        };
        let out = expand(input.into(), false);
        let out_s: TokenStream2 = out.into();
        let text = out_s.to_string();
        assert!(
            text.contains("swap_remove") && text.contains("fn vcheck_"),
            "expected a harness fn referencing swap_remove: {text}"
        );
    }

    // ---- VecDeque param-shape support --------------------------------------

    /// `VecDeque<u32>` classifies as `OwnedVecDeque`, and `&mut VecDeque<u32>`
    /// as `MutRef(OwnedVecDeque)`.
    #[test]
    fn vecdeque_param_classification() {
        let uts = no_user_types();
        let owned: Type = verus_syn::parse_quote! { VecDeque<u32> };
        assert!(
            matches!(
                classify_param_type(&owned, &uts).unwrap(),
                ParamShape::OwnedVecDeque(_)
            ),
            "VecDeque<u32> should classify as OwnedVecDeque"
        );
        let mut_ref: Type = verus_syn::parse_quote! { &mut VecDeque<u32> };
        let shape = classify_param_type(&mut_ref, &uts).unwrap();
        match shape {
            ParamShape::MutRef(inner) => assert!(
                matches!(*inner, ParamShape::OwnedVecDeque(_)),
                "inner should be OwnedVecDeque"
            ),
            other => panic!("expected MutRef(OwnedVecDeque), got {other:?}"),
        }
    }

    // ---- BTreeMap / BTreeSet param-shape support ---------------------------

    /// `BTreeMap<u32,u32>` classifies as `OwnedBTreeMap` and `BTreeSet<u32>`
    /// as `OwnedBTreeSet`; the `&mut` forms wrap them in `MutRef`. These share
    /// the `Map`/`Set` routing with their Hash counterparts (verified by the
    /// example harnesses), but must classify to their own shapes so the
    /// harness type is a real `BTreeMap`/`BTreeSet`.
    #[test]
    fn btree_param_classification() {
        let uts = no_user_types();
        let map: Type = verus_syn::parse_quote! { BTreeMap<u32, u32> };
        assert!(
            matches!(
                classify_param_type(&map, &uts).unwrap(),
                ParamShape::OwnedBTreeMap(_, _)
            ),
            "BTreeMap<u32,u32> should classify as OwnedBTreeMap"
        );
        let set: Type = verus_syn::parse_quote! { BTreeSet<u32> };
        assert!(
            matches!(
                classify_param_type(&set, &uts).unwrap(),
                ParamShape::OwnedBTreeSet(_)
            ),
            "BTreeSet<u32> should classify as OwnedBTreeSet"
        );
        let mut_map: Type = verus_syn::parse_quote! { &mut BTreeMap<u32, u32> };
        match classify_param_type(&mut_map, &uts).unwrap() {
            ParamShape::MutRef(inner) => assert!(
                matches!(*inner, ParamShape::OwnedBTreeMap(_, _)),
                "inner should be OwnedBTreeMap"
            ),
            other => panic!("expected MutRef(OwnedBTreeMap), got {other:?}"),
        }
        let mut_set: Type = verus_syn::parse_quote! { &mut BTreeSet<u32> };
        match classify_param_type(&mut_set, &uts).unwrap() {
            ParamShape::MutRef(inner) => assert!(
                matches!(*inner, ParamShape::OwnedBTreeSet(_)),
                "inner should be OwnedBTreeSet"
            ),
            other => panic!("expected MutRef(OwnedBTreeSet), got {other:?}"),
        }
    }

    /// A `&mut VecDeque<u32>` `push_back` wrapper expands into a harness that
    /// samples a `VecDeque<u32>` and materializes its view via the
    /// `__vcheck_vecdeque_slice` helper (VecDeque has no `as_slice`).
    #[test]
    fn expand_mut_vecdeque_push_back_produces_harness() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_vd_push_back(
                v: &mut ::std::collections::VecDeque<u32>,
                value: u32,
            )
                ensures
                    v@ == old(v)@.push(value),
            {
                ::std::collections::VecDeque::<u32>::push_back(v, value)
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("push_back") && text.contains("fn vcheck_"),
            "expected a harness fn referencing push_back: {text}"
        );
        assert!(
            text.contains("__vcheck_vecdeque_slice"),
            "expected VecDeque view to route through __vcheck_vecdeque_slice: {text}"
        );
    }

    /// The `push_front` front-insertion form `seq![value] + old@` lowers to a
    /// `__vcheck_seq_concat` call (the widened AsRef-based concat helper).
    #[test]
    fn expand_vecdeque_push_front_lowers_front_insertion() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_vd_push_front(
                v: &mut ::std::collections::VecDeque<u32>,
                value: u32,
            )
                ensures
                    v@ == seq![value] + old(v)@,
            {
                ::std::collections::VecDeque::<u32>::push_front(v, value)
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("__vcheck_seq_concat"),
            "expected front-insertion to lower via __vcheck_seq_concat: {text}"
        );
    }

    /// Int-index lowering: a lifted `SpecInt` subscript (a
    /// `::verus_spec_check::__vcheck_int::*` call) must route through
    /// `__vcheck_int::to_usize` (an `as usize` cast on `BigInt` is invalid),
    /// while a plain primitive subscript keeps the cheap `as usize` cast.
    #[test]
    fn lower_index_operand_routes_specint_through_to_usize() {
        // Lifted spec-int arithmetic (as produced for `old@.len() - 1`).
        let specint: Expr = verus_syn::parse_quote! {
            ::verus_spec_check::__vcheck_int::sub(a.len(), 1)
        };
        assert!(expr_is_spec_int_call(&specint));
        let lowered = norm(&lower_index_operand(&specint));
        assert!(
            lowered.contains(":: verus_spec_check :: __vcheck_int :: to_usize"),
            "SpecInt subscript should use to_usize, got: {lowered}"
        );
        assert!(
            !lowered.contains("as usize"),
            "SpecInt subscript must not use `as usize`, got: {lowered}"
        );

        // A plain primitive index keeps the fast `as usize` cast.
        let prim: Expr = verus_syn::parse_quote! { i };
        assert!(!expr_is_spec_int_call(&prim));
        let lowered_prim = norm(&lower_index_operand(&prim));
        assert!(
            lowered_prim.contains("as usize") && !lowered_prim.contains("to_usize"),
            "primitive subscript should keep `as usize`, got: {lowered_prim}"
        );
    }

    /// Map/Set disambiguation: a `&mut HashMap` `insert` wrapper lowers the
    /// view's `insert` to `exec_insert` (the functional Map companion), NOT
    /// the `Seq` `__vcheck_seq_insert` helper.
    #[test]
    fn expand_hashmap_insert_routes_to_exec_insert() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_hm_insert(
                m: &mut ::std::collections::HashMap<u32, u32>,
                k: u32,
                v: u32,
            ) -> (result: Option<u32>)
                ensures
                    m@ == old(m)@.insert(k, v),
            {
                ::std::collections::HashMap::<u32, u32>::insert(m, k, v)
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("exec_insert"),
            "map insert should route to exec_insert: {text}"
        );
        assert!(
            !text.contains("__vcheck_seq_insert"),
            "map insert must NOT hit the Seq insert helper: {text}"
        );
    }

    /// `mode = "fuzz"` and `mode = "kani"` both emit the identical bolero
    /// `check!` harness (bolero selects its engine by a compile-time cfg, not
    /// by codegen). The engine sees the post-preprocess doc sentinels, so we
    /// supply them directly: `backend = bolero` (drives the bolero arm) plus
    /// the `bolero::mode` tag.
    fn expand_text_with_sentinels(mode_sentinel: &str) -> String {
        let mode_doc = format!("verus_spec_check::bolero::mode = {mode_sentinel}");
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            #[doc = #mode_doc]
            pub exec fn __vcheck_assume_double(x: u32) -> (r: u32)
                requires x <= u32::MAX / 2,
                ensures r == x + x,
            {
                x + x
            }
        };
        let out = expand(input.into(), false);
        Into::<TokenStream2>::into(out).to_string()
    }

    #[test]
    fn expand_mode_fuzz_emits_bolero_harness() {
        let text = expand_text_with_sentinels("fuzz");
        assert!(
            text.contains("bolero :: check"),
            "expected bolero harness: {text}"
        );
        assert!(
            !text.contains("proptest !"),
            "should not emit a proptest! block: {text}"
        );
        // fuzz mode: no kani proof attribute (the fuzz engines discover the
        // plain `#[test]` harness directly).
        assert!(
            !text.contains("kani :: proof"),
            "fuzz harness must not carry a kani::proof attr: {text}"
        );
    }

    #[test]
    fn expand_mode_kani_emits_bolero_harness_with_proof_attr() {
        // kani mode emits the same bolero harness as fuzz, plus a
        // `#[cfg_attr(kani, kani::proof)]` so `cargo kani` discovers it (kani
        // 0.67 does not auto-treat `#[test]` fns as harnesses).
        let text = expand_text_with_sentinels("kani");
        assert!(
            text.contains("bolero :: check"),
            "expected bolero harness: {text}"
        );
        assert!(
            !text.contains("proptest !"),
            "should not emit a proptest! block: {text}"
        );
        assert!(
            text.contains("cfg_attr (kani , kani :: proof)"),
            "kani harness must carry #[cfg_attr(kani, kani::proof)]: {text}"
        );
    }

    /// A bolero harness with a `requires` clause carries the full
    /// requires-support machinery:
    ///   - `kani::assume` under `cfg(kani)` (native assumption — the model
    ///     checker constrains the input instead of discarding the path);
    ///   - skip + `__VCHECK_SKIPPED` counter under `cfg(not(kani))`;
    ///   - the post-run vacuity check that fails the test when every
    ///     sampled input was rejected.
    #[test]
    fn expand_bolero_requires_emits_assume_and_vacuity_check() {
        let text = expand_text_with_sentinels("fuzz");
        assert!(
            text.contains("kani :: assume"),
            "requires should lower to kani::assume under cfg(kani): {text}"
        );
        assert!(
            text.contains("__VCHECK_SKIPPED") && text.contains("__VCHECK_TESTED"),
            "requires should carry the skip/tested vacuity counters: {text}"
        );
        assert!(
            text.contains("vacuous bolero harness"),
            "harness should end with the post-run vacuity check: {text}"
        );
    }

    /// A bolero harness with NO `requires` (and no `real` guard) has no skip
    /// path, so none of the vacuity machinery is emitted — the harness shape
    /// is unchanged from before the requires-support work.
    #[test]
    fn expand_bolero_no_requires_omits_vacuity_machinery() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_wrap(x: u32) -> (r: u32)
                ensures r == x,
            {
                x
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("bolero :: check"),
            "expected bolero harness: {text}"
        );
        assert!(
            !text.contains("__VCHECK_SKIPPED") && !text.contains("__VCHECK_TESTED"),
            "no-requires harness must not carry vacuity counters: {text}"
        );
        assert!(
            !text.contains("kani :: assume"),
            "no-requires harness must not emit kani::assume: {text}"
        );
    }

    /// The unspecified-`real` guard keeps skip semantics on all engines (no
    /// `assume` form exists for the thread-local defined-flag machinery), but
    /// still participates in the vacuity accounting.
    #[test]
    fn expand_bolero_real_requires_counts_skips_without_assume() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_real_gated(x: u32) -> (r: u32)
                requires (x as real) > 1real,
                ensures r == x,
            {
                x
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            !text.contains("kani :: assume"),
            "real-guarded requires must keep skip semantics under kani too: {text}"
        );
        assert!(
            text.contains("__VCHECK_SKIPPED") && text.contains("vacuous bolero harness"),
            "real-guarded requires still participates in vacuity accounting: {text}"
        );
    }

    /// Fix coverage: `&&&` conjunction chains nested inside match arms
    /// lower to parenthesized `&&` chains (previously left as `&&&` tokens,
    /// which have no Rust form).
    // #[test]
    // fn expand_big_and_inside_match_lowers_to_and() {
    // let input: TokenStream2 = quote! {
    // #[verifier::external_body]
    // #[doc = "verus_spec_check::backend = bolero"]
    // pub exec fn __vcheck_assume_popish(v: &mut Vec<u32>) -> (value: Option<u32>)
    // ensures
    // match value {
    // Some(x) => {
    // &&& old(v)@.len() > 0
    // &&& x == old(v)@[old(v)@.len() - 1]
    // },
    // None => {
    // &&& old(v)@.len() == 0
    // &&& final(v)@ == old(v)@
    // },
    // },
    // {
    // v.pop()
    // }
    // };
    // let out = expand(input.into(), false);
    // let text: String = Into::<TokenStream2>::into(out).to_string();
    // assert!(text.contains("fn vcheck_"), "expected a harness: {text}");
    // assert!(
    // !text.contains("&&&"),
    // "BigAnd chains must lower to `&&`: {text}"
    // );
    // }

    /// Fix coverage: `ret@ == Map::empty()` on a map-returning fn lowers the
    /// constructor operand to `&Default::default()` (borrowed +
    /// carrier-agnostic) instead of an owned `HashMap::new()`.
    #[test]
    fn expand_map_empty_comparison_borrows_default() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_fresh_map() -> (m: HashMap<u32, u32>)
                ensures
                    m@ == Map::<u32, u32>::empty(),
            {
                HashMap::new()
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("Default :: default"),
            "Map::empty() in comparison should lower to &Default::default(): {text}"
        );
    }

    /// Fix coverage: `Option<Ordering>` classifies as a supported return
    /// shape (the `partial_cmp` shape) and produces a harness.
    #[test]
    fn expand_option_ordering_return_produces_harness() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_pc(x: u32, y: u32) -> (ret: Option<core::cmp::Ordering>)
                ensures
                    ret == (if x < y {
                        Some(core::cmp::Ordering::Less)
                    } else if x > y {
                        Some(core::cmp::Ordering::Greater)
                    } else {
                        Some(core::cmp::Ordering::Equal)
                    }),
            {
                x.partial_cmp(&y)
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("fn vcheck_") && text.contains("partial_cmp"),
            "Option<Ordering> return should produce a harness: {text}"
        );
    }

    /// Fix coverage: a turbofish call to an `external_vcheck_provide!`d spec
    /// fn (`obeys::<u32>()` — the guard-predicate shape on monomorphized
    /// container specs) renames to the monomorphic exec companion with the
    /// turbofish stripped.
    #[test]
    fn expand_turbofish_stub_call_strips_generics() {
        let input: TokenStream2 = quote! {
            external_vcheck_provide! {
                fn obeys() -> bool {
                    true
                }
            }

            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_guarded(x: u32) -> (r: u32)
                ensures
                    !obeys::<u32>() || r == x,
            {
                x
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("exec_obeys ()"),
            "turbofish stub call should rename to bare exec companion: {text}"
        );
        assert!(
            !text.contains("exec_obeys :: <"),
            "turbofish must be stripped from the renamed call: {text}"
        );
    }

    #[test]
    fn expand_mode_proptest_emits_proptest_harness() {
        // No bolero sentinel ⇒ default proptest backend ⇒ proptest! block.
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            pub exec fn __vcheck_assume_double_pt(x: u32) -> (r: u32)
                requires x <= u32::MAX / 2,
                ensures r == x + x,
            {
                x + x
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("proptest !"),
            "expected proptest! block: {text}"
        );
        assert!(
            !text.contains("bolero :: check"),
            "should not emit a bolero harness: {text}"
        );
    }

    /// A contract that reasons in `real` (here `(x as real)/2` as an exact
    /// rational) lowers to `__vcheck_real::*` and wraps its clauses with the
    /// `reset_defined()` / `is_defined()` skip guard (so an unspecified case —
    /// ÷0 or a non-finite float->real — is skipped, not asserted).
    #[test]
    fn expand_real_contract_emits_vcheck_real_and_skip_guard() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            pub exec fn __vcheck_assume_half(x: u32) -> (r: u32)
                ensures (r as real) * 2real == (x as real),
            {
                x / 2
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        let harness = text
            .split("mod __verus_spec_check_")
            .nth(1)
            .expect("expansion should contain the generated harness module");
        assert!(
            harness.contains(":: verus_spec_check :: __vcheck_real"),
            "real contract should lower to __vcheck_real: {harness}"
        );
        assert!(
            harness.contains("reset_defined") && harness.contains("is_defined"),
            "real contract clauses should carry the defined/skip guard: {harness}"
        );
    }

    /// The bolero `Regular` arm also carries the real skip-guard (the earlier
    /// test exercised the proptest arm via the default backend).
    #[test]
    fn expand_real_contract_bolero_arm_has_skip_guard() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            #[doc = "verus_spec_check::bolero::mode = fuzz"]
            pub exec fn __vcheck_assume_half_b(x: u32) -> (r: u32)
                ensures (r as real) * 2real == (x as real),
            {
                x / 2
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("bolero :: check"),
            "expected bolero harness: {text}"
        );
        assert!(
            text.contains("reset_defined") && text.contains("is_defined"),
            "bolero real harness should carry the defined/skip guard: {text}"
        );
    }

    /// The skip-guard also wraps a `requires` clause that references `real`
    /// (a distinct emission branch from `ensures`): the `__vcheck_req` temp +
    /// `is_defined()`-gated `prop_assume!` must appear.
    #[test]
    fn expand_real_requires_clause_is_guarded() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            pub exec fn __vcheck_assume_rr(x: u32) -> (r: u32)
                requires (x as real) > 1real,
                ensures r == x,
            {
                x
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        let harness = text
            .split("mod __verus_spec_check_")
            .nth(1)
            .expect("harness module");
        assert!(
            harness.contains("__vcheck_req"),
            "requires guard temp expected: {harness}"
        );
        assert!(
            harness.contains("prop_assume"),
            "requires -> prop_assume expected: {harness}"
        );
        assert!(
            harness.contains("reset_defined"),
            "requires guard reset expected: {harness}"
        );
    }

    /// Regression: a non-real contract must NOT emit the real skip-guard (so
    /// existing harnesses are byte-for-byte unchanged by real support).
    #[test]
    fn expand_non_real_contract_has_no_skip_guard() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            pub exec fn __vcheck_assume_inc(x: u32) -> (r: u32)
                requires x < u32::MAX,
                ensures r == x + 1,
            {
                x + 1
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            !text.contains("__vcheck_real"),
            "no real lowering expected: {text}"
        );
        assert!(
            !text.contains("reset_defined"),
            "no skip guard expected: {text}"
        );
    }

    /// Regression: a `&mut Vec` `insert` still lowers to the `Seq`
    /// `__vcheck_seq_insert` helper (the disambiguation must not steal it).
    #[test]
    fn expand_vec_insert_still_routes_to_seq_helper() {
        let input: TokenStream2 = quote! {
            #[verifier::external_body]
            #[doc = "verus_spec_check::backend = bolero"]
            pub exec fn __vcheck_assume_vec_insert2(
                vec: &mut ::std::vec::Vec<u32>,
                i: usize,
                element: u32,
            )
                ensures
                    vec@ == old(vec)@.insert(i as int, element),
            {
                ::std::vec::Vec::<u32>::insert(vec, i, element)
            }
        };
        let out = expand(input.into(), false);
        let text: String = Into::<TokenStream2>::into(out).to_string();
        assert!(
            text.contains("__vcheck_seq_insert"),
            "Vec insert should still use the Seq helper: {text}"
        );
    }
}
