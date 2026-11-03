# `verus_spec_check_vstd_ext`: exec_spec runtime types for verus_spec_check

The verus_spec_check engine emits absolute paths into
`::verus_spec_check_vstd_ext::*`. The umbrella `verus_spec_check` crate re-exports this.

Besides the types already provided by upstream `exec_spec`, we 
provide a dependent exec concretization for
tracked permissions in `resource.rs`.
