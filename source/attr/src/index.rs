use super::*;

// ---------------------------------------------------------------------------
// Sibling index
// ---------------------------------------------------------------------------

/// Index over the block's sibling items so the closure can resolve names.
pub struct SiblingIndex {
    /// type name -> index of its struct/enum definition in `items`
    pub type_defs: HashMap<String, usize>,
    /// type name -> indices of its inherent impl blocks
    pub type_impls: HashMap<String, Vec<usize>>,
    /// free spec/fn name -> index
    pub free_fns: HashMap<String, usize>,
    /// spec method name -> set of owning type names (so a `.m()` call can pull
    /// in the owning type's impl)
    pub method_owners: HashMap<String, HashSet<String>>,
    /// item index -> ordered list of its type-param names (e.g. `["V"]`).
    /// Empty for items without generics.
    pub type_params_by_idx: HashMap<usize, Vec<Ident>>,
}

pub fn build_index(items: &[Item]) -> SiblingIndex {
    let mut type_defs = HashMap::new();
    let mut type_impls: HashMap<String, Vec<usize>> = HashMap::new();
    let mut free_fns = HashMap::new();
    let mut method_owners: HashMap<String, HashSet<String>> = HashMap::new();
    let mut type_params_by_idx: HashMap<usize, Vec<Ident>> = HashMap::new();

    for (i, item) in items.iter().enumerate() {
        let tps = item_type_params(item);
        if !tps.is_empty() {
            type_params_by_idx.insert(i, tps);
        }
        if let Some(n) = type_def_name(item) {
            type_defs.insert(n.to_string(), i);
        }
        if let Some(n) = free_spec_or_fn_name(item) {
            free_fns.insert(n.to_string(), i);
        }
        if let Some(self_name) = inherent_impl_self_name(item) {
            type_impls.entry(self_name.to_string()).or_default().push(i);
            if let Item::Impl(im) = item {
                for ii in &im.items {
                    if let ImplItem::Fn(f) = ii {
                        method_owners
                            .entry(f.sig.ident.to_string())
                            .or_default()
                            .insert(self_name.to_string());
                    }
                }
            }
        }
    }

    SiblingIndex {
        type_defs,
        type_impls,
        free_fns,
        method_owners,
        type_params_by_idx,
    }
}
