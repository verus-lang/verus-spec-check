# verus-spec-check
`verus-spec-check` is a tool for automatically testing [Verus](https://github.com/verus-lang/verus) specifications. `verus-spec-check` integrates smoothly with existing cargo-based Verus codebases and works directly with stock Verus through patching the `verus!` macro.

Using [proptest](https://github.com/proptest-rs/proptest) and [Bolero](https://github.com/camshaft/bolero) as backends, `verus-spec-check` supports the property-based testing, fuzzing, model checking, and mutation testing of Verus specifications. Concrete use cases for `verus-spec-check` include automatically testing the soundness of assumed specifications and axioms, automatically testing the completeness of the specifications on top-level functions, generating concrete counterexamples for failing verification conditions, and empirically validating verification conditions before embarking on proving them.

## Status
Like Verus, `verus-spec-check` is under active development. Features may be broken and/or missing, and documentation is still incomplete.

## Usage
Users interact with `verus-spec-check` by labeling executable functions, inline assertions, proof functions, axioms, and `assume_specification` calls inside the `verus!` macro with the `#[vcheck]` attribute:

```rust
use verus_spec_check::*;
use vstd::prelude::*;

verus! {

#[vcheck]
fn safe_double(x: u32) -> (r: u32)
    requires x <= u32::MAX / 2,
    ensures r == x * 2,
{
    x + x
}

fn midpoint(a: u32, b: u32) -> (m: u32)
    requires a <= b,
{
    let m = a + (b - a) / 2;
    #[vcheck] assert(a <= m && m <= b);
    m
}

#[vcheck]
assume_specification [ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
    ensures
        r.is_some() ==> r.unwrap() == x + y,
        r.is_none() ==> x + y > u32::MAX,
;

}
```

Run with:

```bash
cargo test         # run tests (default: proptest) 
cargo verus verify # verus verification is not affected
```

Several additional examples are present in the `examples` folder,
and a complete guide on `verus-spec-check`'s full capabilities is present in `USAGE.md`. 
. The complete cargo environment for this example is present in `examples/readme`

### Backends

The `verus-spec-check` harnesses target [proptest](https://docs.rs/proptest) 
by default, but other evaluation modes are supported. Pick a
testing mode per-annotation with `#[vcheck(mode = "...")]`:

- `mode = "proptest"` (default): a proptest harness.
- `mode = "fuzz"`: coverage-guided fuzzer based upon libfuzzer, provided by 
   [Bolero](https://github.com/camshaft/bolero). 
- `mode = "kani"`: [Kani](https://model-checking.github.io/kani/) model checking, also provided by [Bolero](https://github.com/camshaft/bolero).

See `USAGE.md` for more information.

### Coverage reports

Two attributes turn `cargo test` into a spec-completeness report, from
opposite directions:

- `#[vcheck_cov_mutate]` -- mutation coverage: is the spec strong enough
  to detect subtle changes in the implementation? Mutates the body and 
  reports which mutants the subject contract kills
  (`examples/cov_mutate/`).
- `#[vcheck_cov_fuzz]` -- branch coverage: does the spec properly exercise
  all branches of the implementation? Instruments the function body, and 
  runs a coverage-guided search over precondition-conforming inputs, reporting
  which implementation arms they 
  reach and listing unreached ones (`examples/cov_fuzz/`).

Both run under plain `cargo test`, and both
take an optional `threshold = N` option to fail the build below N%. 
See `USAGE.md` for more information.

## Quick start

In your project's `Cargo.toml`:

```toml
[package]
name = "my_verus_project"
version = "0.1.0"
edition = "2021"

[lib]
path = "src/lib.rs"

[dependencies]
# Match the version your verus binary expects
vstd = "=0.0.0-2026-09-20-0158"
verus_spec_check = { path = "/path/to/verus-spec-check/source/verus_spec_check" }
verus_spec_check_vstd_ext = { path = "/path/to/verus-spec-check/source/vstd_ext" }
verus_builtin_macros = { version = "=0.0.0-2026-09-20-0158", features = ["contrib-hooks"] }

[package.metadata.verus]
verify = true

# substitutes the verus_builtin_macros overlay for the stock crate,
# providing the support for the #[vcheck] attribute
[patch.crates-io]
verus_builtin_macros = { path = "/path/to/verus-spec-check/source/builtin_macros_overlay" }
```

Additionally, a Nix flake is provided for the instantiation of a compatible version of Verus, the Verus standard library, and `verus-spec-check`.

## License

MIT, matching Verus.
