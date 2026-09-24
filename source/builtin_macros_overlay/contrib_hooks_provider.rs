// contrib hooks provider (list-based).
//
// This file is NOT a module of the crate. It is textually `include!`d into
// `verus_builtin_macros::contrib::hooks::external` when the crate is built
// with `--features contrib-hooks`. Its path is handed to rustc via the
// `VERUS_CONTRIB_HOOKS_FILE` environment variable (set by this overlay's
// build.rs). It therefore runs with the same `verus_syn` instance and the
// same dependencies as the surrounding macros crate.
//
// It must define exactly these two functions:
//     pub(super) fn preprocess_items(items: &mut Vec<Item>)
//     pub(super) fn preprocess_impl_items(items: &mut Vec<ImplItem>)
// (`Item` / `ImplItem` are in scope via the `use` in the `external` module.)
//
// Adding a hook = add one entry to the relevant list below. Hooks run in
// listed order; each sees items added by earlier hooks, and any items a hook
// pushes are still visited by the per-item contrib pass afterward.

/// Hooks over the top-level item list, run in order.
const ITEM_HOOKS: &[fn(&mut Vec<Item>)] = &[
    vcheck::preprocess_items,
    // add more top-level-item hooks here, e.g.:
    // my_hook::preprocess_items,
];

/// Hooks over impl-item lists, run in order.
const IMPL_ITEM_HOOKS: &[fn(&mut Vec<ImplItem>)] = &[
    // vcheck currently has no impl-item pass; add impl-item hooks here.
];

pub(super) fn preprocess_items(items: &mut Vec<Item>) {
    for hook in ITEM_HOOKS {
        hook(items);
    }
}

pub(super) fn preprocess_impl_items(items: &mut Vec<ImplItem>) {
    for hook in IMPL_ITEM_HOOKS {
        hook(items);
    }
}

// --- individual hooks -------------------------------------------------------

/// Property-based testing: fold `#[vcheck]` / `#[vcheck_provide]` / etc. marked
/// items into the engine's whole-block pass.
mod vcheck {
    use super::Item;

    pub(super) fn preprocess_items(items: &mut Vec<Item>) {
        verus_spec_check_engine::vcheck_provide_preprocess(items);
    }
}

// Template for an additional, independent hook. Uncomment and add to the
// ITEM_HOOKS list above.
//
// mod my_hook {
//     use super::Item;
//
//     pub(super) fn preprocess_items(_items: &mut Vec<Item>) {
//         // inspect / rewrite `_items` here
//     }
// }
