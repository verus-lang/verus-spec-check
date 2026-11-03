#![cfg(all(feature = "alloc", feature = "std"))]

pub mod resource;

// Flat re-export of every `pub` item under `exec_spec` so the engine's
// `::verus_spec_check_vstd_ext::ExecSpecType` paths resolve.
pub use vstd::contrib::exec_spec::*;

pub fn exec_mem_contents_from_option<T>(o: Option<T>) -> ExecMemContents<T> {
    match o {
        Some(t) => ExecMemContents::Init(t),
        None => ExecMemContents::Uninit,
    }
}
