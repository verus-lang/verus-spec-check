# Using verus-spec-check
This is a brief guide for `verus-spec-check`.

## Automated testing of Verus contracts
`verus-spec-check` enables users to automatically test Verus contracts using 
property-based testing, fuzzing, or model-checking. This is useful for
empirically validating the soundness of assumptions, finding counterexamples 
to failing contracts, or testing theorems before you prove them.

### Labeling function bodies
The simplest functionality of verus-spec-check is directly labeling function bodies:

```rust
verus! {
    #[vcheck]
    fn safe_double(x: u32) -> (r: u32)
        requires x <= u32::MAX / 2,
        ensures r == x * 2,
    {
        x + x
    }

    #[vcheck]
    #[verifier::external_body]
    fn safe_double_2(x: u32) -> (r: u32)
        requires x <= u32::MAX / 2,
        ensures r == x * 2,
    {
        x + x
    }
}
```
Each `#[vcheck] fn myfn(...)` becomes a separate test (`__verus_spec_check_<fn>`),
which is automatically evaluated with the `proptest` back-end by default.

### Inline `assert(...)` in fn bodies
Inline assertions may be labeled alongside function-level contracts.

```rust
verus! {
    #[vcheck]
    #[verifier::external_body]
    pub fn safe_div(num: u32, den: u32) -> (r: u32)
        ensures r == spec_safe_div(num, den),
    {
        let result = if den != 0u32 { num / den } else { 0u32 };
        #[vcheck] assert(if den != 0u32 { result == num / den } else { result == 0u32 });
        result
    }
}
```
Each `#[vcheck] assert(...)` becomes a separate test (`__vcheck_assert_<fn>_at_lineN`).

There's also a `forall` form for quantified asserts. See
`examples/assert/`.

### Labeling `assume_specification` bodies
Similar to function-level contracts, `assume_specifications` calls may be labeled with
`#[vcheck]`. In this scenario, the precondition is assumed to be vacuous; the vcheck checks
for whether the executable function always agrees with the specification. 

In the scenario the vcheck fails on an `assume_specification` call, you should be
able to use [`runtime_assert`](https://verus-lang.github.io/verus/verusdoc/vstd/pervasive/fn.runtime_assert.html)
to prove there is a discrepancy between the Verus specification and the runtime behavior
using the vcheck counterexample. 
For an example, see [Verus issue #2674](https://github.com/verus-lang/verus/issues/2674). 
You may additionally be able to prove false using the unsound assumed specification, 
depending on the circumstances.

```rust
verus! {
    #[vcheck]
    assume_specification [ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
        ensures
            r.is_some() ==> r.unwrap() == x + y,
            r.is_none() ==> x + y > u32::MAX,
    ;
}
```

```rust
verus! {
    #[vcheck]
    #[verifier::external_body]
    pub fn safe_div(num: u32, den: u32) -> (r: u32)
        ensures r == spec_safe_div(num, den),
    {
        let result = if den != 0u32 { num / den } else { 0u32 };
        #[vcheck]
        assert(if den != 0u32 { result == num / den } else { result == 0u32 });
        result
    }
}
```

### User-defined types

```rust
verus! {
    #[vcheck_provide]
    pub struct Point { pub x: i64, pub y: i64 }

    #[vcheck]
    fn nearest(p: Point, points: &[Point]) -> (r: usize)
        requires points.len() > 0,
        // ... contracts mentioning Point ...
    { /* ... */ }
}
```

`#[vcheck_provide]` synthesizes a `VcheckStrategy` impl and exec converters
for the type. Generally required when a type is referenced from a `#[vcheck]`
contract.

### Cross-crate spec fns

For using verus-spec-check on specifications that are inherited from external crates (e.g. `vstd`),
you may use `external_vcheck_provide!` to inline a trusted exec stub.

```rust
verus! {
    external_vcheck_provide! {
        fn is_sorted(s: Seq<i64>) -> bool {
            s.windows(2).all(|w| w[0] <= w[1])
        }
    }

    #[vcheck]
    fn sort_it(s: &[i64]) -> (r: Vec<i64>)
        ensures is_sorted(r.deep_view()),
    { /* ... */ }
}
```

### Instantiating Generic Types
In lieu of Rust's [built-in monomorphization procedure](https://rustc-dev-guide.rust-lang.org/backend/monomorph.html),
verus-spec-check supports instantiating generics with primitive types for the sake of testing.

```rust
verus! {
    #[vcheck(T = u32)]
    #[verifier::external_body]
    pub exec fn vec_push<T>(v: &mut Vec<T>, x: T)
        ensures
            final(v)@ == old(v)@.push(x),
    {
        v.push(x);
    }
}
```

### Proof fns and Axioms
verus-spec-check is able to generate property-based tests for Verus proof fns and axiom fns, through instantiating a no-op intermediate 
executable function to test on.

```rust
verus! {
    #[vcheck_axiom]
    pub proof fn mult_iden(a: u32, b: u32)
        requires
            a + b <= u32::MAX,
        ensures
            a + b == b + a,
    { }

    #[vcheck_axiom]
    pub axiom fn another_iden(a: i32)
        requires
            a != 0,
        ensures
            a > 0,
    { }
}
```

### Different backends
By default `#[vcheck]` emits a [proptest](https://docs.rs/proptest)
harness. Select a different testing mode per annotation with
`mode = "..."`:

```rust
verus! {
    #[vcheck(mode = "fuzz")]
    fn safe_double(x: u32) -> (r: u32)
        requires x <= u32::MAX / 2,
        ensures r == x * 2,
    { x + x }
}
```

`mode` accepts `"proptest"`, `"fuzz"`, and `"kani"`; the respective evaluation suites are invoked
by just running `cargo test`. For fuzzing and kani support, verus-spec-check emits a ([bolero](https://github.com/camshaft/bolero)) harness. 
Bolero is packaged with verus-spec-check by default. 
All types are runnable with a simple `cargo test`. 

Under `mode = "fuzz"`, several environment variables are exposed for tuning, including
`VERUS_SPEC_CHECK_FUZZ_BUDGET` (default 4096 executions per harness) and `VERUS_SPEC_CHECK_FUZZ_SEED`.

Under `mode = "kani"`, you'll be prompted to install kani if you do not have it:
```bash
cargo install --locked kani-verifier && cargo kani setup   # once
cargo test                                                 # run tests
```

Environment variables to tune kani include `VERUS_SPEC_CHECK_KANI_TIMEOUT=<secs>` caps the kani run, and `VERUS_SPEC_CHECK_KANI_QUIET=1` routes the report to stderr.

### Opaque types with uninterpreted views
Some specifications are stated over an opaque type (e.g. a bignum from an external crate)
through an `uninterp` view function. verus-spec-check can neither sample the opaque type
nor evaluate the view, so you may use `#[vcheck_view]` on the view to tell it how.

```rust
verus! {
    #[vcheck_view(sample = u64)]
    pub uninterp spec fn ubig_view(n: &UBig) -> nat;

    #[vcheck]
    assume_specification [ ubig_add ](a: &UBig, b: &UBig) -> (ret: UBig)
        ensures
            ubig_view(&ret) == ubig_view(a) + ubig_view(b),
    ;
}
```
By default, `#[vcheck_view]` attempts to use the [From trait](https://doc.rust-lang.org/std/convert/trait.From.html)
on the desired type. The view must be an `uninterp spec fn view(x: &T) -> nat` (or `-> int`). 

`#[vcheck_view]` has three parameters:

- `sample` (required): the type the harness actually generates.
- `inject`: a `fn(Sample) -> T` building the opaque value from a sample. Defaults to
  `From::from`.
- `realize`: a `fn(&T) -> verus_spec_check::Spec<Type>` giving the view an executable meaning.

For example:
```rust
#[vcheck_view(sample = u32, inject = ubig_inject, realize = ubig_realize)]
```

Types or paths that don't parse as bare expressions may be quoted, e.g. `sample = "Vec<u8>"`.

## Weak Specification Detection
Inversely to using verus-spec-check for finding soundness bugs in specifications and (unproven) theorems,
verus-spec-check also enables the detection of "weak" specifications that do not sufficiently specify 
the implementation. 

Two methods currently exist to do this: mutation testing, and branch counting via a fuzzer.

### Mutation coverage

If you control the subject function you are proptesting, you may use `#[vcheck_cov_mutate]` to run
a mutation testing analysis. 

```rust
verus! {
    #[vcheck]
    #[vcheck_cov_mutate]
    fn double(x: u32) -> (r: u32)
        requires x <= u32::MAX / 2,
        ensures r == x * 2,
    { x + x }
}
```

`cargo test` then prints a per-fn kill-rate report, explicitly stating
which mutations the specification fails to kill. To fail when the
rate is below a threshold:

```rust
#[vcheck_cov_mutate(threshold = 80)]
```

### Branch coverage

If you do not control the subject function you are proptesting, you may use `#[vcheck_cov_fuzz]`
to empirically test how many branches of the executable function the specification function exercises. 
This is antithetical to mutation testing; mutation testing is generally a
better approach for hunting for explicit bugs in weak specs
but, branch coverage provides a better empirical analysis.

A branch arm counts as *spec-covered* when some `requires`-conforming input
reaches it *and* at least one `ensures` clause *engages* on that input. 
Ablating an ensures clause
therefore should visibly shrink the covered percentage.
The report also shows
plain reachability (`[inputs reach N/M]`) separately, and lists arms that
are reached but *unspecified* (e.g. no clause speaks about the inputs that get
there). 

Besides regular function-level contracts, `#[vcheck_cov_fuzz]` may be ran on `assume_specification`
contracts.

```rust
verus! {
    #[vcheck]
    #[vcheck_cov_fuzz]
    fn double(x: u32) -> (r: u32)
        requires x <= u32::MAX / 2,
        ensures r == x * 2,
    { x + x }

    #[vcheck]
    #[vcheck_cov_fuzz]
    assume_specification [ u32::checked_add ](x: u32, y: u32) -> (r: Option<u32>)
        ensures
            r.is_some() ==> r.unwrap() == x + y,
            r.is_none() ==> x + y > u32::MAX,
    ;
}
```

`cargo test` then prints a fuzz-discovered branch coverage ratio. To fail when the
rate is below a threshold:

```rust
#[vcheck_cov_fuzz(threshold = 80)]
```
External (`assume_specification`) targets are measured through an
instrumented side profile, which requires `llvm-profdata`/`llvm-cov`.
The user will be prompted to install `llvm-tools` if the Nix 
packaging is not already provided:

```bash
$ rustup component add llvm-tools --toolchain nightly
```

When measuring external functions, the report first runs an
engagement-guided *recorder* in the ordinary (uninstrumented) test
process, calling the real external fn freely, evaluating each clause's
engagement with the result in hand, and saving the spec-engaged input
genomes (cap: `VERUS_SPEC_CHECK_COVEXT_SAMPLES`, default 256; search budget:
`VERUS_SPEC_CHECK_COV_FUZZ_BUDGET`). The instrumented side build then *replays*
exactly those genomes such that the llvm-cov numbers reflect only inputs the
spec speaks about, ablating any ensures clause, result-dependent or
not, shrinks external coverage. 

## Running tests with Miri
The generated proptest harnesses run unchanged under [Miri](https://github.com/rust-lang/miri),
which interprets each test and dynamically checks the executable code for undefined behavior
(out-of-bounds accesses, use-after-free, uninitialized reads, misaligned pointers, data races).
This is especially useful for `#[verifier::external_body]` functions and `assume_specification`
targets, whose implementations Verus never checks.

```bash
rustup component add --toolchain nightly miri rust-src                        # once
PROPTEST_CASES=8 MIRIFLAGS=-Zmiri-disable-isolation cargo +nightly miri test  # run tests
```

Miri is roughly 100x slower than native execution, so keep `PROPTEST_CASES` low and
raise it when you want stronger coverage. `-Zmiri-disable-isolation` is needed for proptest
to read `PROPTEST_CASES` from inside Miri's sandbox.

`tools/run_miri.sh` wraps the above with the same defaults (plus `--lib --no-fail-fast`).
Extra arguments are passed through to `cargo miri test`, so you can filter by harness name:

```bash
bash path/to/verus-spec-check/tools/run_miri.sh safe_double
```

### Skipping harnesses under Miri
Harnesses that reach code Miri cannot model (e.g. FFI, file handles), or that are too slow
when interpreted, may opt out with `miri = "skip"`:

```rust
verus! {
    #[vcheck(miri = "skip")]
    fn safe_double(x: u32) -> (r: u32)
        requires x <= u32::MAX / 2,
        ensures r == x * 2,
    { x + x }
}
```

If Miri fails with `unsupported operation: can't call foreign function`, the function under test
reached into FFI that Miri can't model; mark it with `miri = "skip"`. Other Miri errors on a
vcheck harness generally indicate real undefined behavior in the executable code.

## Notes and Gotchas

### Running Verus Verification
`verus verify` is entirely unchanged. The backend only affects the generated
test harness, not verification.

### Strong `requires` clauses
To cope with strong preconditions on subject 
contracts, it is generally recommended to use 
`mode = "fuzz"`. The fuzzing support is designed to instrument the
precondition such that the coverage-guided feedback may learn its
structure and subsequently generate effective random inputs.
This is significantly better than default proptest, which relies upon
`prop_assume` to simply drop randomly generated inputs that do not satisfy 
the precondition without improving the generator.

Under kani, `requires` lowers to `kani::assume` (a native assumption: the
proof covers the full constrained domain). The engine still narrows
generators for the precondition shapes it recognizes (fixed lengths,
`usize` index bounds).

### Deep `ensures` clauses
Similarly, to cope with strong postconditions on subject contracts,
it is generally recommended to use `mode = fuzz` or `mode = kani`.

### Spec types in contracts (`int` / `nat` / `real`)
Verus's ghost numeric types can be used freely in `requires` / `ensures`
even though they're never exec parameters — they arise from casts
(`x as int`, `x as real`) and literals (`5nat`, `1.5real`). The engine
evaluates them in *exact* unbounded domains so contracts written in spec
arithmetic run faithfully:

- `int` / `nat` -> `num_bigint::BigInt` (exact unbounded integers;
  Euclidean `/` and `%`).
- `real` -> `num_rational::BigRational` (exact rationals; `+ - * /`, unary
  `-`, and `floor`/`as int`). A `real` literal is the exact decimal
  (`0.1real` = 1/10, not the `f64` rounding).

`real` supports both conversion directions:

```rust
verus! {
    // integer -> real: exact rational arithmetic
    #[vcheck]
    fn double_via_real(x: u32) -> (r: u64)
        ensures (r as real) == (x as real) * 2real,
    { x as u64 * 2 }

    // float <-> real: the real value of a float is exact for finite floats;
    // NaN / +-inf are unspecified in Verus, so those inputs are skipped.
    #[vcheck]
    fn float_identity(x: f64) -> (r: f64)
        ensures (r as real) == (x as real),
    { x }
}
```

Two `real` operations are unspecified in Verus and are therefore
*skipped* (not asserted) at test time: division by zero (`r / 0`) and the
real value of a non-finite float. 

### Tuning Execution

```bash
PROPTEST_CASES=10000 cargo test
```

For high case counts with many filtered preconditions:

```bash
PROPTEST_MAX_GLOBAL_REJECTS=1000000 PROPTEST_CASES=10000 cargo test
```

Aliases (in `.cargo/config.toml`):

- `cargo vcheck` -- `cargo test --lib`
- `cargo vcheck-only` -- only the harness module's tests
- `cargo vcheck-build` -- `cargo test --lib --no-run`
- `cargo vcheck-fuzz <harness>` -- `cargo bolero test <harness>` (needs
  `cargo-bolero` and a nightly toolchain; the `bolero` backend is bundled
  by default)

### Inspecting generated harnesses
To see the property-based tests verus-spec-check generates for your crate,
set `VERUS_SPEC_CHECK_PRINT_EXPANSION` during a testing run:

```bash
VERUS_SPEC_CHECK_PRINT_EXPANSION=1 cargo test 2> my_vchecks
```

Each generated test module (`#[cfg(test)] mod __verus_spec_check_<n>`) is
pretty-printed to stderr, bracketed by `==== verus-spec-check expansion: ... ====`
markers -- the proptest harnesses, strategies, and generated support
impls, *before* rustc expands proptest's internals and the `#[test]`
plumbing. 

For the fully-expanded view instead, use
`cargo expand --lib --tests __verus_spec_check_0` (`cargo-expand` is included
in the nix dev shell).

## Troubleshooting

### `unresolved import 'verus_spec_check'`

`verus_spec_check` is in `[dev-dependencies]` but you might have wrote `use verus_spec_check::*;`
at the top of `lib.rs`. Either move it to `[dependencies]` or
gate the imports with `#[cfg(test)]`.

### `cannot find function 'vcheck_gen' in crate 'verus_spec_check'` (or `bolero` / `bolero_generator` unresolved)

You have a `#[vcheck(mode = "fuzz" | "kani")]` fn (or the legacy
`#[vcheck(backend = "bolero")]`) but the `bolero` backend has been switched
off. It's bundled by default, so this only happens if you disabled
default features. Drop the opt-out:

```toml
verus_spec_check = { path = "..." }   # not default-features = false
```

The bolero generator layer and the `::verus_spec_check::bolero` re-exports only
compile when the `bolero` feature is on (which it is by default).

### `unresolved import 'verus_spec_check_vstd_ext'`

`verus_spec_check_vstd_ext` MUST be in `[dependencies]`, not
`[dev-dependencies]`. The engine emits absolute paths into it from
non-test code paths.

### `expected generics to match found bool` (or similar deep vstd errors)

vstd version doesn't match the verus binary expectation. Check:

```bash
verus --version              # check the date in the version string
cargo info vstd | grep version
```

Bump `vstd` to match the verus binary's date.

### `package collision in the lockfile: packages verus_builtin_macros...`

Something in your dep tree path-deps stock `verus_builtin_macros`
while you're trying to use the overlay. Either:

- Convert all path-deps to crates.io entries.
- Remove the overlay patch and use the block-form path instead.

### `failed to resolve: could not find tracked in proc_macro`

Your verus binary is older than `2026-06-14-0213`. 

### Tests in `cargo test` show 0 results

The harness module is gated `#[cfg(test)]`. If your project has
`#[cfg(not(test))]` on a parent module or `[lib] test = false`, the
harness gets pruned.

### `cargo verus verify` fails on the overlay

The most common cause is your verus binary is from a 
different release than the version verus-spec-check is paired with.

To ensure you're using the correct version of verus-spec-check, 
you can run `nix develop` on the main verus-spec-check directory,
change directories into your main project, and run `cargo verus verify`
there normally.

## Hand-written wrappers

Sometimes you may not be able to label your specification functions directly with
`#[vcheck]`, and you'll need to write your own _wrapper_ around your 
desired functions to check their behavior.

Shapes that still need a hand-written wrapper: receivers on generic
*inherent* impls, `&mut` returns (write-through unobservable),
implicit spec-trait preconditions (e.g. `index_req`), and contracts
reaching uninterp spec fns. (Whole-`mem_contents()`/`opt_value()`
comparisons against a `MemContents` constructor are supported: they
decompose to `is_init()`/`value()`/`is_uninit()` projections, at the
clause level when the receiver is `final(perm)`.)

## Known limitations

- rust-analyzer red squigglies: rust-analyzer doesn't fully
  understand the `proptest!` macro expansion, so you may see false
  errors in your editor. The compiler is the source of truth.
- there is no support for testing loop invariants, currently. 
- `verus-spec-check` does not yet support traits specified with 
  `external_trait_specification`, e.g. `verus::vstd::std_specs::iter`
- `verus-spec-check` does not yet support [prophetic specifications](https://verus-lang.github.io/verus/guide/reference-attributes.html?highlight=prophetic#verifierprophetic).
- `verus-spec-check` does not yet support asynchronous and dynamic types
