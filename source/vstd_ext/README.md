# `verus_spec_check_vstd_ext`: exec_spec runtime types for verus_spec_check

These types were originally hosted in `vstd::contrib::exec_spec::*`. 
We make several additions, and hence the exec_spec types are housed as a crate
within `verus-spec-check`. The verus_spec_check engine emits absolute paths into
`::verus_spec_check_vstd_ext::*`. The umbrella `verus_spec_check` crate re-exports this.

Besides the types already provided by upstream `exec_spec`, we 
provide a dedicated exec concretization for `vstd::raw_ptr::MemContents` in
`exec_spec/mem_contents.rs`, and a dependent exec concretization for
tracked permissions in `resource.rs`.
