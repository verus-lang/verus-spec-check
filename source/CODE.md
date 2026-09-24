# Verus-spec-check Architecture Overview

This document provides an overview of the `verus-spec-check` internals
for developers contributing to the project.

## Testing Pipeline Overview

`verus-spec-check` transforms Verus code through the following pipeline:

```
#[vcheck]-labeled Verus code
   ↓ (verus_attr: preprocess attributes)
Verus w/ folded vcheck engine groups 
   ↓ (rustc: expand verus_spec_check_unverified!)
Verus w/ proptest blocks
   ↓ (rustc: expand verus!, proptest!)
Verus HIR 
   ↓ (verus: materialize spec types, erase ghost code)
Rust code w/ proptest blocks
   ↓ (vstd_ext: sample materialized spec types, e.g. iter)
Testing results
```

## Crate Architecture

### Pipeline Call Graph Overview
```
verus_builtin_macros::contrib_preprocess_items 
   ↓
verus_spec_check_engine::vcheck_provide_preprocess
   ↓
vcheck_attr::vcheck_provide_preprocess
   ├─ [per item] 
   │   ├─ item_has_attr(item, ["vcheck"/"vcheck_provide"/"vcheck_axiom"]) 
   │   ├─ if vcheck_assert::block_has_vcheck_inline_assert ...
   │   └─ if let Item::AssumeSpecification ... 
   │      └─ items.extend(synthesized_wrappers);
   │
   ├─ [per item] 
   │   └─ if Item:Impl 
   │       └─ self_ty_supports_inherent_impl() -> lift_trait_method_to_free_fn()
   │                                           -> rewrite_trait_impl_to_inherent()
   │
   ├─ build_index(items)   [O(1) name -> definition resolver]
   │
   ├─ [per item] 
   │   ├─ if item_has_attr("vcheck")
   │   ├─ if vcheck_assert::block_has_vcheck_inline_assert()
   │   ├─ if Item::Impl
   │   └─ collect_contract_idents, collect_free_call_names, collect_contract_typed_refs -> generic_seeds
   │
   ├─ compute_closure()
   ├─ compute_closure_with_substs()
   ├─ engine_items::new()
   ├─ [per item] 
   │   └─ strip_attr_item()
   └─ ::verus_spec_check::verus_spec_check_unverified! { #(#engine_items))* } 
   ↓
verus_spec_check_expand::expand
   ├─ verus_spec_check_expand::classify
   ├─ verus_spec_check_expand::emit_harness
   │   └─ emit_harness_with_flavor()
   │
   ├─ let engine_items = verus_spec_check_exec_spec::exec_spec
   ├─ let strategy_impls = classified.map({
   │   ├─ UserType::Struct => emit_struct_support()
   │   ├─ UserType::Enum => emit_enum_support()
   │   └─ if wants_bolero 
   │       ├─ UserType::Struct => emit_struct_bolero_support()
   │       └─ UserType::Enum => emit_enum_bolero_support()
   │
   ├─ external_vcheck_provide::emit_companions()
   ├─ emit_cov_mutate_block()
   ├─ emit_cov_fuzz_block()
   ├─ emit_inline_assert_block()
   └─ generate_combined_vcheck_block().into()
   ↓
   #engine_block
   exec_* companions
   DeepView impls
   verus!{ passthrough }
   #[cfg(test)] mod__vcheck_* {
       strategies / VcheckGen
       vcheck_<fn> harnesses
       cov-mutate, cov-fuzz, inline-assert
   }
   ↓
rustc_resolve::macros      [expands verus!, proptest!]
   ↓
cargo test
   ↓
verus::rust_verify::erase  [erase ghost code]
   ↓
[vcheck execution]
```

## Crate Architecture

Each pipeline stage is a dedicated crate under `source/`:

- `verus_spec_check_syntax` (`source/syntax`) -- forked Verus helpers (`Vstd` resolver, `vstd_kind`, `quote_vstd!`) 
- `verus_spec_check_assert` (`source/assert`) -- inline `#[vcheck] assert(...)` discovery/rewriting
- `verus_spec_check_mutator` (`source/mutator`) -- `#[vcheck_cov_mutate]` mutation-site enumeration 
- `verus_spec_check_instrument` (`source/instrument`) -- `#[vcheck_cov_fuzz]` branch-site enumeration + body instrumentation 
- `verus_spec_check_exec_spec` (`source/exec_spec`) -- spec-to-exec lowering (`exec_spec_*!`) 
- `verus_spec_check_external_provide` (`source/external_provide`) -- `external_vcheck_provide!` companions 
- `verus_spec_check_attr` (`source/attr`) -- `#[vcheck]`/`#[vcheck_provide]` preprocessing (folding pass) 
- `verus_spec_check_expand` (`source/expand`) -- `verus_spec_check_*!` expansion (classify, lower, emit) 
- `verus_spec_check_engine` (`source/engine) -- stable facade over the above; the crate downstream `[patch.crates-io]` users pin 
- `verus_spec_check_macros` (`source/macros`) -- proc-macro wrapper around the engine 
- `verus_spec_check_runtime` (`source/runtime`) -- proptest/bolero result parsing, SpecInt/SpecReal 
- `verus_spec_check_vstd_ext` (`source/vstd_ext`) -- exec_spec translations of spec types 
- `verus_spec_check` (`source/verus_spec_check`) -- user-facing umbrella crate

Shared dependency versions (including the `verus_syn` pin) live in the
root `Cargo.toml` `[workspace.dependencies]` table.

### verus_spec_check_attr (`source/attr`)

**Key functions:**
- `vcheck_provide_preprocess`: entry point, argument parsing, passing to `verus_spec_check`
- `substitute_item`: binds generics to values
- `compute_closure`: collects all associated items for a contract
- `synthesize_vcheck_wrapper_from_assume_spec`: generates a `#[verifier::external_body]` fn from an `assume_specification` call
- `synthesize_vcheck_wrapper_from_proof fn`: generates a `#[verifier::external_body]` fn from a `axiom fn` call

**Main data structures:**
- `Subst`: tracks generic to value substitutions
- `VcheckMiriMode`/`VcheckBackend`/`VcheckBoleroMode`: per-target configs
- `SiblingIndex`: index built for efficient name resolution
- `ClosureResult`: carries per-item chosen substitutions

Module map: `config.rs` (marker parsing: `VcheckMiriMode`/`VcheckBackend`/
`VcheckBoleroMode` + sentinels), `subst.rs` (`Subst`, generics
substitution), `attr_helpers.rs` (attribute/item helpers, harness
sentinel), `refs.rs` (reference collection + unresolved-spec-fn
diagnostics), `index.rs` (`SiblingIndex`), `closure.rs`
(`compute_closure`, `ClosureResult`), `wrapper_synth.rs`
(assume_specification / `#[vcheck_axiom]` wrapper synthesis),
`impl_lift.rs` (trait-impl lifting), `pass.rs` (the unified pass).

### verus_spec_check_expand (`source/expand`)

**Key functions:**
- `expand`: entry point, calls into `exec_spec` for each engine item
- `classify`: sorts items into `Classified`, registers view fns
- `classify_param_type`: type-pattern match that maps syntactic types to a `ParamShape`
- `visit_expr_mut`: handles the exec lowering for all types `verus-spec-check` supports
- `pair_resource_params`: pairs permissions with their handles (see: `vstd_ext::resource.rs`
- `emit_harness`: compiles declarations into `prop_assume!`/`prop_assert!`
- `emit_inline_assert_block`: handles inline #[vcheck] insertions
- `emit_cov_mutate_block`: handles mutation testing harness
- `emit_cov_fuzz_block`: handles branch-coverage instrumentation +
  coverage-guided runner emission (`#[vcheck_cov_fuzz]`)

**Main data structures**
- `Classified`: contains the state of all classified input items, 
  e.g. passthrough items, engine items, spec fn names, user types, 
  external_provide bodies, contract targets, inline assert targets,
  cov_mutate targets, and cov_fuzz targets
- `ParamShape`: specifies the parameter shape for all types `verus-spec-check` supports
- `ContractRewriter`: impl lowers spec expressions to exec code
- `ResourceClauseDisposition`: outcome of the resource clause passes
- `HarnessFlavor`: tracks proptest vs bolero emission mode
- `ConcretizeInfo`: the `#[vcheck_view]` registry entry state

Module map: `concretize.rs` (`#[vcheck_view]`/`VcheckConcretize` registry),
`classify.rs` (item parsing, `Classified`, cov-mutate detection),
`param_shape.rs` (param/return type analysis, `ParamShape`,
`ReturnShape`), `contract_rewriter.rs` (`ContractRewriter` exec
lowering), `expr_utils.rs` (expression predicates/helpers),
`inline_quant.rs` (forall/exists lifting), `strategy_emit.rs`
(proptest `VcheckStrategy` emission), `bolero_emit.rs` (bolero
`TypeGenerator`/`VcheckGen` emission), `harness_emit.rs` (harness
emission, `HarnessFlavor`), `resource.rs` (tracked-permission clause
passes), `audit.rs` (silent-no-op audit), `inline_assert_emit.rs`,
`cov_mutate_emit.rs`, `expand.rs` (top-level entry).

### Supporting crates
- `builtin_macros_overlay`: manages the hooks for `verus_builtin_macros`; 
  target of the [patch.crates.io] call
- `vstd_ext`: carries the `exec_spec` translations of spec types. Largely a mirror
  of upstream Verus, except the tracked permission support with `mem_contents.rs` 
  and `resource.rs`
- `verus_spec_check`: top-level crate
- `runtime`: infrastructure for parsing proptest/bolero results
- `macros`: exports macros and attributes provided by `verus-spec-check`
- `engine`: thin facade re-exporting the split crates' entry points
  (`vcheck_provide_preprocess`, `expand_verus_spec_check`, `expand_exec_spec`,
  `compile_error_external_vcheck_provide`); keeps the public API and the
  `path = "../engine"` location stable for the overlay and downstream
  `[patch.crates-io]` users
- `syntax`/`assert`/`mutator`/`exec_spec`/`external_provide`/`attr`/`expand`:
  the engine internals as dedicated crates (see table above)

## Detailed Pipeline Stages

todo...
