// Supplies the compile-time path to the contrib hooks provider for the
// upstream `contrib::hooks` seam. `hooks.rs` reads this via
// `include!(env!("VERUS_CONTRIB_HOOKS_FILE"))`, but only when this crate is
// built with `--features contrib-hooks` (off by default). Setting it
// unconditionally is harmless: with the feature off the `external` module
// that reads it is not compiled.
fn main() {
    let provider = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("contrib_hooks_provider.rs");
    println!("cargo:rustc-env=VERUS_CONTRIB_HOOKS_FILE={}", provider.display());
    println!("cargo:rerun-if-changed=contrib_hooks_provider.rs");
}
