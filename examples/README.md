# verus-spec-check examples

## Running

Results are reproducible by entering the target example directory, and bringing in the proper Verus
version with Nix. For example:
```
$ cd examples/assert
$ nix develop           # enter nix development shell
$ cargo verus verify    # run verus verification
$ cargo test --lib      # run verus-spec-check tests
```

## Cargo.toml shape

Every example follows this template:

```toml
[package]
name = "verus_spec_check_<name>"
version = "0.1.0"
edition = "2021"

[lib]
path = "src/lib.rs"

[dependencies]
vstd = "=0.0.0-2026-06-14-0213"
verus_spec_check = { path = "../../source/verus_spec_check" }
verus_spec_check_vstd_ext = { path = "../../source/vstd_ext" }
verus_builtin_macros = { version = "=0.0.0-2026-06-14-0213", features = ["contrib-hooks"] }

[package.metadata.verus]
verify = true

[patch.crates-io]
verus_builtin_macros = { path = "../../source/builtin_macros_overlay" }

[workspace]
```
