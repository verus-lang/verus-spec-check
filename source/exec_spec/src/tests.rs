use crate::exec_spec::*;

#[cfg(test)]
mod tracked_hardening_tests {
    use super::{compile_enum, compile_spec_fn, compile_struct};
    use verus_syn::parse_quote;

    /// `tracked` parameter marker on a spec fn -> rejected at the marker.
    #[test]
    fn rejects_tracked_param() {
        let f: verus_syn::ItemFn = parse_quote! {
            spec fn f(tracked x: u64) -> bool { x > 0 }
        };
        let err = compile_spec_fn(&f, true).unwrap_err();
        assert!(
            err.to_string().contains("`tracked` parameters"),
            "got: {err}"
        );
    }

    /// `let tracked` in a spec-fn body -> rejected at the marker.
    #[test]
    fn rejects_let_tracked() {
        let f: verus_syn::ItemFn = parse_quote! {
            spec fn f(x: u64) -> u64 {
                let tracked y = x;
                y
            }
        };
        let err = compile_spec_fn(&f, true).unwrap_err();
        assert!(err.to_string().contains("`let tracked`"), "got: {err}");
    }

    /// `let ghost` in a spec-fn body -> rejected (redundant at best).
    #[test]
    fn rejects_let_ghost() {
        let f: verus_syn::ItemFn = parse_quote! {
            spec fn f(x: u64) -> u64 {
                let ghost y = x;
                y
            }
        };
        let err = compile_spec_fn(&f, true).unwrap_err();
        assert!(err.to_string().contains("`let ghost`"), "got: {err}");
    }

    /// `tracked struct` (a permission type) -> rejected with view-type guidance.
    #[test]
    fn rejects_tracked_struct() {
        let s: verus_syn::ItemStruct = parse_quote! {
            tracked struct Perm { x: u64 }
        };
        let err = compile_struct(&s).unwrap_err();
        assert!(
            err.to_string().contains("`tracked` datatypes"),
            "got: {err}"
        );
    }

    /// `tracked enum` -> same rejection as `tracked struct`.
    #[test]
    fn rejects_tracked_enum() {
        let e: verus_syn::ItemEnum = parse_quote! {
            tracked enum Perm { A, B(u64) }
        };
        let err = compile_enum(&e).unwrap_err();
        assert!(
            err.to_string().contains("`tracked` datatypes"),
            "got: {err}"
        );
    }

    /// `ghost struct` stays accepted: ghost datatypes are the spec-side
    /// values exec_spec exists to mirror (e.g. `MemContents`-like views).
    #[test]
    fn accepts_ghost_struct() {
        let s: verus_syn::ItemStruct = parse_quote! {
            ghost struct View { x: u64, y: bool }
        };
        assert!(compile_struct(&s).is_ok());
    }

    /// `ghost enum` stays accepted (vstd's `MemContents<T>` is one).
    #[test]
    fn accepts_ghost_enum() {
        let e: verus_syn::ItemEnum = parse_quote! {
            ghost enum View { Uninit, Init(u64) }
        };
        assert!(compile_enum(&e).is_ok());
    }

    /// Per-field `tracked` marker -> rejected (permission state in an
    /// otherwise-mirrorable struct).
    #[test]
    fn rejects_tracked_field() {
        let s: verus_syn::ItemStruct = parse_quote! {
            ghost struct S { tracked x: u64 }
        };
        let err = compile_struct(&s).unwrap_err();
        assert!(err.to_string().contains("`tracked` fields"), "got: {err}");
    }

    /// Per-field explicit `ghost` marker -> rejected (would desynchronize
    /// the Exec* mirror from the runtime layout).
    #[test]
    fn rejects_ghost_field_marker() {
        let s: verus_syn::ItemStruct = parse_quote! {
            struct S { x: u64, ghost g: u64 }
        };
        let err = compile_struct(&s).unwrap_err();
        assert!(
            err.to_string().contains("`ghost` field markers"),
            "got: {err}"
        );
    }

    /// Per-field markers inside enum variants are caught too.
    #[test]
    fn rejects_tracked_field_in_enum_variant() {
        let e: verus_syn::ItemEnum = parse_quote! {
            ghost enum E { A { tracked x: u64 }, B }
        };
        let err = compile_enum(&e).unwrap_err();
        assert!(err.to_string().contains("`tracked` fields"), "got: {err}");
    }
}

#[cfg(test)]
mod mem_contents_routing_tests {
    use super::compile_spec_fn;
    use verus_syn::parse_quote;

    fn compile_ok(f: verus_syn::ItemFn) -> String {
        compile_spec_fn(&f, true)
            .expect("should compile")
            .to_string()
    }

    /// Param + return positions: `MemContents<u32>` lowers to
    /// `ExecMemContents<u32>` (Ref for params, Owned for returns).
    #[test]
    fn type_lowers_to_exec_mirror() {
        let out = compile_ok(parse_quote! {
            spec fn f(mc: MemContents<u32>) -> MemContents<u32> { mc }
        });
        // Note: the inner type arg lowers through the ExecSpecType trait
        // fallback (`<u32 as ExecSpecType>::ExecOwnedType`), matching the
        // Multiset arm's behavior — assert on the wrapper only.
        assert!(
            out.contains("mc : & ExecMemContents <"),
            "param should lower to &ExecMemContents<..>: {out}"
        );
        assert!(
            out.contains("res : ExecMemContents <"),
            "return should lower to ExecMemContents<..>: {out}"
        );
    }

    /// View-projection methods (`is_init`, `is_uninit`, `value`) route via
    /// the `exec_<name>` method-rename fallback onto the
    /// `ExecSpecMemContents` trait impls in vstd_ext.
    #[test]
    fn projection_methods_get_exec_prefix() {
        let out = compile_ok(parse_quote! {
            spec fn f(mc: MemContents<u32>) -> bool { mc.is_init() || mc.is_uninit() }
        });
        assert!(out.contains("exec_is_init"), "is_init should route: {out}");
        assert!(
            out.contains("exec_is_uninit"),
            "is_uninit should route: {out}"
        );
    }

    /// `value()` routes too (the `recommends self.is_init()` is spec-side
    /// only; the exec mirror's requires covers the harness obligation).
    #[test]
    fn value_method_routes() {
        let out = compile_ok(parse_quote! {
            spec fn f(mc: MemContents<u32>) -> u32 { mc.value() }
        });
        assert!(out.contains("exec_value"), "value should route: {out}");
    }

    /// Ctor paths and match patterns get the `Exec` prefix:
    /// `MemContents::Init(v)` -> `ExecMemContents::Init(v)`.
    #[test]
    fn ctors_and_patterns_get_exec_prefix() {
        let out = compile_ok(parse_quote! {
            spec fn f(mc: MemContents<u32>) -> MemContents<u32> {
                match mc {
                    MemContents::Init(v) => MemContents::Init(v),
                    MemContents::Uninit => MemContents::Uninit,
                }
            }
        });
        assert!(
            out.contains("ExecMemContents :: Init"),
            "Init ctor/pattern should be prefixed: {out}"
        );
        assert!(
            out.contains("ExecMemContents :: Uninit"),
            "Uninit ctor/pattern should be prefixed: {out}"
        );
    }

    /// `&MemContents<T>` in param position recurses like `&Option<T>`
    /// instead of bouncing off the ExecSpecType trait-lookup fallback.
    #[test]
    fn ref_mem_contents_recurses() {
        let out = compile_ok(parse_quote! {
            spec fn f(mc: &MemContents<u32>) -> bool { mc.is_init() }
        });
        assert!(
            out.contains("mc : & ExecMemContents <"),
            "&MemContents should lower to &ExecMemContents: {out}"
        );
        assert!(
            !out.contains("< & MemContents"),
            "the reference must not bounce off the trait-lookup fallback: {out}"
        );
    }
}
