//! VcheckStrategy impl emission for user types.

use super::*;

/// Build a `BoxedStrategy` expression for a single field type. The strategy
/// produces the harness type (user's own type for user-defined elements).
pub fn strategy_for_type(ty: &Type, user_types: &HashSet<String>) -> Result<TokenStream2, Error> {
    let elem = classify_param_elem(ty, user_types)?;
    let elem_ty = elem.harness_type();
    Ok(quote! {
        <#elem_ty as ::verus_spec_check::VcheckStrategy>::vcheck_strategy()
    })
}

/// Emit everything the harness needs for a user-defined struct:
///   - `VcheckStrategy for <Struct>` (samples the user's OWN type)
///   - manual `Clone` + `Debug` (we can't derive on the Verus type without
///     tripping Verus's auto-derive checks)
///   - `__vcheck_to_exec_<Struct>(&Struct) -> ExecStruct` converter.
pub fn emit_struct_support(
    item_struct: &ItemStruct,
    user_types: &HashSet<String>,
) -> Result<TokenStream2, Error> {
    let name = &item_struct.ident;
    let exec_name = format_ident!("Exec{}", name);
    let conv = to_exec_fn_name(name);

    let clone_impl = emit_clone_impl_struct(name, &item_struct.fields);
    let debug_impl = emit_debug_impl(name);

    let strategy_impl = match &item_struct.fields {
        Fields::Named(named) => {
            let field_names: Vec<&Ident> = named
                .named
                .iter()
                .map(|f| f.ident.as_ref().unwrap())
                .collect();
            let field_strats: Vec<TokenStream2> = named
                .named
                .iter()
                .map(|f| strategy_for_type(&f.ty, user_types))
                .collect::<Result<Vec<_>, _>>()?;
            let tuple_pat = quote! { (#(#field_names),*) };
            quote! {
                impl ::verus_spec_check::VcheckStrategy for #name {
                    type Strategy = ::verus_spec_check::proptest::strategy::BoxedStrategy<#name>;
                    fn vcheck_strategy() -> Self::Strategy {
                        use ::verus_spec_check::proptest::strategy::Strategy;
                        (#(#field_strats),*)
                            .prop_map(|#tuple_pat| #name { #(#field_names),* })
                            .boxed()
                    }
                }
            }
        }
        Fields::Unnamed(unnamed) => {
            let n = unnamed.unnamed.len();
            let field_strats: Vec<TokenStream2> = unnamed
                .unnamed
                .iter()
                .map(|f| strategy_for_type(&f.ty, user_types))
                .collect::<Result<Vec<_>, _>>()?;
            let var_names: Vec<Ident> = (0..n).map(|i| format_ident!("__f{}", i)).collect();
            let tuple_pat = quote! { (#(#var_names),*) };
            quote! {
                impl ::verus_spec_check::VcheckStrategy for #name {
                    type Strategy = ::verus_spec_check::proptest::strategy::BoxedStrategy<#name>;
                    fn vcheck_strategy() -> Self::Strategy {
                        use ::verus_spec_check::proptest::strategy::Strategy;
                        (#(#field_strats),*)
                            .prop_map(|#tuple_pat| #name(#(#var_names),*))
                            .boxed()
                    }
                }
            }
        }
        Fields::Unit => quote! {
            impl ::verus_spec_check::VcheckStrategy for #name {
                type Strategy = ::verus_spec_check::proptest::strategy::BoxedStrategy<#name>;
                fn vcheck_strategy() -> Self::Strategy {
                    use ::verus_spec_check::proptest::strategy::Strategy;
                    ::verus_spec_check::proptest::strategy::Just(#name).boxed()
                }
            }
        },
    };

    // Converter body.
    let conv_body = match &item_struct.fields {
        Fields::Named(named) => {
            let inits = named.named.iter().map(|f| {
                let fname = f.ident.as_ref().unwrap();
                let conv_field = elem_to_exec_expr(&f.ty, quote! { self_value.#fname }, user_types);
                quote! { #fname: #conv_field }
            });
            quote! { #exec_name { #(#inits),* } }
        }
        Fields::Unnamed(unnamed) => {
            let inits = unnamed.unnamed.iter().enumerate().map(|(i, f)| {
                let idx = verus_syn::Index::from(i);
                elem_to_exec_expr(&f.ty, quote! { self_value.#idx }, user_types)
            });
            quote! { #exec_name(#(#inits),*) }
        }
        Fields::Unit => quote! { #exec_name },
    };

    Ok(quote! {
        #clone_impl
        #debug_impl
        #strategy_impl
        impl ::verus_spec_check::ToExecModel for #name {
            type Exec = #exec_name;
            fn to_exec_model(&self) -> #exec_name {
                let self_value = self;
                #conv_body
            }
        }
        impl ::verus_spec_check::VcheckSpecCompanion for #name {}
        // Back-compat free fn (used by older call sites); delegates to the trait.
        #[allow(non_snake_case)]
        fn #conv(self_value: &#name) -> #exec_name {
            <#name as ::verus_spec_check::ToExecModel>::to_exec_model(self_value)
        }
    })
}

pub fn emit_enum_support(
    item_enum: &ItemEnum,
    user_types: &HashSet<String>,
) -> Result<TokenStream2, Error> {
    let name = &item_enum.ident;
    let exec_name = format_ident!("Exec{}", name);
    let conv = to_exec_fn_name(name);

    if item_enum.variants.is_empty() {
        return Err(Error::new_spanned(
            item_enum,
            "verus_spec_check: cannot generate a strategy for an empty enum",
        ));
    }

    let clone_impl = emit_clone_impl_enum(name, item_enum);
    let debug_impl = emit_debug_impl(name);

    let mut variant_arms: Vec<TokenStream2> = Vec::new();
    let mut conv_arms: Vec<TokenStream2> = Vec::new();
    for variant in &item_enum.variants {
        let vname = &variant.ident;
        match &variant.fields {
            Fields::Named(named) => {
                let field_names: Vec<&Ident> = named
                    .named
                    .iter()
                    .map(|f| f.ident.as_ref().unwrap())
                    .collect();
                let field_strats: Vec<TokenStream2> = named
                    .named
                    .iter()
                    .map(|f| strategy_for_type(&f.ty, user_types))
                    .collect::<Result<Vec<_>, _>>()?;
                let tuple_pat = quote! { (#(#field_names),*) };
                variant_arms.push(quote! {
                    (#(#field_strats),*)
                        .prop_map(|#tuple_pat| #name::#vname { #(#field_names),* })
                        .boxed()
                });
                // converter arm
                let conv_inits = named.named.iter().map(|f| {
                    let fname = f.ident.as_ref().unwrap();
                    let conv_field =
                        elem_to_exec_expr(&f.ty, quote! { #fname.clone() }, user_types);
                    quote! { #fname: #conv_field }
                });
                conv_arms.push(quote! {
                    #name::#vname { #(#field_names),* } => #exec_name::#vname { #(#conv_inits),* }
                });
            }
            Fields::Unnamed(unnamed) => {
                let n = unnamed.unnamed.len();
                let field_strats: Vec<TokenStream2> = unnamed
                    .unnamed
                    .iter()
                    .map(|f| strategy_for_type(&f.ty, user_types))
                    .collect::<Result<Vec<_>, _>>()?;
                let var_names: Vec<Ident> = (0..n).map(|i| format_ident!("__f{}", i)).collect();
                let tuple_pat = quote! { (#(#var_names),*) };
                variant_arms.push(quote! {
                    (#(#field_strats),*)
                        .prop_map(|#tuple_pat| #name::#vname(#(#var_names),*))
                        .boxed()
                });
                let conv_inits = unnamed.unnamed.iter().enumerate().map(|(i, f)| {
                    let vn = &var_names[i];
                    elem_to_exec_expr(&f.ty, quote! { #vn.clone() }, user_types)
                });
                conv_arms.push(quote! {
                    #name::#vname(#(#var_names),*) => #exec_name::#vname(#(#conv_inits),*)
                });
            }
            Fields::Unit => {
                variant_arms.push(quote! {
                    ::verus_spec_check::proptest::strategy::Just(#name::#vname).boxed()
                });
                conv_arms.push(quote! {
                    #name::#vname => #exec_name::#vname
                });
            }
        }
    }

    Ok(quote! {
        #clone_impl
        #debug_impl
        impl ::verus_spec_check::VcheckStrategy for #name {
            type Strategy = ::verus_spec_check::proptest::strategy::BoxedStrategy<#name>;
            fn vcheck_strategy() -> Self::Strategy {
                use ::verus_spec_check::proptest::strategy::Strategy;
                ::verus_spec_check::proptest::prop_oneof![
                    #(#variant_arms),*
                ]
                .boxed()
            }
        }
        impl ::verus_spec_check::ToExecModel for #name {
            type Exec = #exec_name;
            fn to_exec_model(&self) -> #exec_name {
                match self {
                    #(#conv_arms),*
                }
            }
        }
        impl ::verus_spec_check::VcheckSpecCompanion for #name {}
        #[allow(non_snake_case)]
        fn #conv(self_value: &#name) -> #exec_name {
            <#name as ::verus_spec_check::ToExecModel>::to_exec_model(self_value)
        }
    })
}
