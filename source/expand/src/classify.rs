use super::*;
/// Item parsing & classification

/// Custom parser for a list of items.
pub struct VcheckItems(pub Vec<Item>);

impl Parse for VcheckItems {
    fn parse(input: ParseStream) -> verus_syn::parse::Result<VcheckItems> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(VcheckItems(items))
    }
}

/// Either or enum the user defined; carried with us so we can emit
/// strategy impls.
#[derive(Clone)]
pub enum UserType {
    Struct(ItemStruct),
    Enum(ItemEnum),
}

impl UserType {
    #[allow(dead_code)]
    fn name(&self) -> &Ident {
        match self {
            UserType::Struct(s) => &s.ident,
            UserType::Enum(e) => &e.ident,
        }
    }
}

/// A contract-bearing function we need to emit a harness for. Free fns and
/// `&self`-receiver methods on user-defined `Exec*` types are both supported.
#[derive(Clone)]
pub enum ContractTarget {
    /// A free `fn` with at least one of `requires` / `ensures`.
    FreeFn {
        item_fn: ItemFn,
        /// `true` when the source attribute carried `miri = "skip"`.
        /// Propagated to harness emission as `#[cfg_attr(miri, ignore)]`.
        miri_skip: bool,
        /// Which VCHECK backend the source attribute selected
        /// (`#[vcheck(mode = "...")]` or the legacy `#[vcheck(backend = "...")]`).
        /// Defaults to `Proptest`. Threaded to harness emission.
        backend: crate::vcheck_attr::VcheckBackend,
        /// Which bolero mode the source attribute selected
        /// (`#[vcheck(mode = "fuzz" | "kani")]`). `None` on the proptest backend.
        /// Both modes emit identical harness code; carried
        /// for tooling/gating.
        bolero_mode: Option<crate::vcheck_attr::VcheckBoleroMode>,
        /// `true` when the fn reached the engine block solely because it
        /// contains a stmt-level `#[vcheck] assert(...)` (i.e. it was NOT
        /// `#[vcheck]`-tagged at the item level). The inline-assert harness
        /// still uses this target as its enclosing context, but we skip
        /// emitting the regular `vcheck_<fn>` harness for it.
        skip_regular_harness: bool,
    },
    /// A method on an `Exec*` type with at least one of `requires` /
    /// `ensures`. Carries the impl's Self ident (e.g. `ExecUser`) so the
    /// harness can call `super::ExecUser::method(&u, ...)`.
    Method {
        self_ty: Ident,
        method: verus_syn::ImplItemFn,
        miri_skip: bool,
        /// See `FreeFn::backend`
        backend: crate::vcheck_attr::VcheckBackend,
        /// See `FreeFn::bolero_mode`
        bolero_mode: Option<crate::vcheck_attr::VcheckBoleroMode>,
        /// See `FreeFn::skip_regular_harness`
        skip_regular_harness: bool,
    },
}

impl ContractTarget {
    pub fn miri_skip(&self) -> bool {
        match self {
            ContractTarget::FreeFn { miri_skip, .. } => *miri_skip,
            ContractTarget::Method { miri_skip, .. } => *miri_skip,
        }
    }

    /// The VCHECK backend selected for this target. Defaults to `Proptest`.
    /// Consumed by the harness emitter to pick the proptest vs bolero harness.
    pub fn backend(&self) -> crate::vcheck_attr::VcheckBackend {
        match self {
            ContractTarget::FreeFn { backend, .. } => *backend,
            ContractTarget::Method { backend, .. } => *backend,
        }
    }

    /// The bolero mode (`fuzz`/`kani`) selected for this target, or `None` on
    /// the proptest backend. Both modes emit identical harness code; this is
    /// carried for tooling and future `cfg`-gating.
    #[allow(dead_code)]
    pub fn bolero_mode(&self) -> Option<crate::vcheck_attr::VcheckBoleroMode> {
        match self {
            ContractTarget::FreeFn { bolero_mode, .. } => *bolero_mode,
            ContractTarget::Method { bolero_mode, .. } => *bolero_mode,
        }
    }

    pub fn skip_regular_harness(&self) -> bool {
        match self {
            ContractTarget::FreeFn {
                skip_regular_harness,
                ..
            } => *skip_regular_harness,
            ContractTarget::Method {
                skip_regular_harness,
                ..
            } => *skip_regular_harness,
        }
    }
}

/// Result of classifying the macro's input items.
pub struct Classified {
    /// Items the user wrote, passed through verus! verbatim.
    pub passthrough_items: Vec<Item>,
    /// Items the engine compiles (spec fn / struct / enum / spec-only impl).
    pub engine_items: Vec<Item>,
    /// Names of spec fns (for the contract rewriter's call-site renaming).
    pub spec_fn_names: HashSet<String>,
    /// Definitions of user-defined types (for strategy emission).
    pub user_types: Vec<UserType>,
    /// Set of user-defined type names (faster lookups during type analysis).
    pub user_type_names: HashSet<String>,
    /// Contract-bearing fns / methods that need a harness.
    pub contract_targets: Vec<ContractTarget>,
    /// Token bodies of `external_vcheck_provide!` invocations 
    pub external_provide_bodies: Vec<TokenStream2>,
    /// `runtime fn name -> spec fn name` redirect from
    /// `#[verifier::when_used_as_spec(spec_X)]` attributes. The contract
    /// rewriter consults this when emitting `exec_<...>` calls so a runtime
    /// fn marked as a spec proxy lowers to the right companion.
    pub when_used_as_spec_redirect: HashMap<String, String>,
    /// Functions marked `#[vcheck_cov_mutate]` whose ensures-clause coverage
    /// is to be assessed via `cargo-mutants`. Each entry records enough
    /// metadata for the runtime runner to scope mutations to that fn's
    /// body and run only its harness.
    pub cov_mutate_targets: Vec<CovMutateTarget>,
    /// Functions marked `#[vcheck_cov_fuzz]` whose implementation branch
    /// coverage is to be assessed by the coverage-guided runner. Each
    /// entry carries the body source for the instrumenter plus the
    /// report options.
    pub cov_fuzz_targets: Vec<CovFuzzTarget>,
    /// `#[vcheck]`-marked inline asserts found inside the bodies of any
    /// `#[vcheck]`-able fn. Each target carries enough info for the harness
    /// emitter to either rewrite the parallel fn (path-form) or build a
    /// standalone `#[test]` (forall-form).
    pub inline_assert_targets: Vec<InlineAssertContext>,
    /// Hard classification errors: `#[vcheck]`-marked fns with no contract
    /// clauses (the silent-no-harness shape). Surfaced by `expand()` as
    /// compile errors BEFORE any emission — unlike the engine-items
    /// error embedding, which exec_spec would mangle into a generic
    /// "unsupported item".
    pub contract_errors: Vec<Error>,
}

/// Pairing of an `InlineAssertTarget` with the enclosing fn's
/// `ContractTarget`. The harness emitter needs both: the target tells
/// it what to test, and the enclosing fn provides the parameter
/// strategies for the path-form harness.
#[derive(Clone)]
pub struct InlineAssertContext {
    pub target: crate::vcheck_assert::InlineAssertTarget,
    pub enclosing: Option<ContractTarget>,
}

/// Metadata for a `#[vcheck_cov_mutate]` target. Captured at macro time and
/// flowed through to `expand`'s cov_mutate emission step.
#[derive(Clone, Debug)]
pub struct CovMutateTarget {
    /// Display name (qualified for impl methods, e.g. `Counter::step`).
    pub fn_name: String,
    /// Bare function ident (matches the source) — used to scope mutant
    /// fn naming.
    pub fn_ident: String,
    /// Optional kill-rate threshold (0..=100). When set and the kill rate
    /// falls below it, the report test panics so `cargo test` fails.
    pub threshold: Option<u8>,
    /// Optional skip flag. When set, the runner records the target but
    /// does not run any mutants. Useful for muting one fn temporarily
    /// without removing the attribute (which would change the per-crate
    /// target list).
    pub skip: bool,
    /// For free fns: cloned `ItemFn`; for impl methods: `(self_ty,
    /// ImplItemFn)`. The mutator pulls the body from here at expand
    /// time.
    pub body_source: CovMutateBodySource,
}

/// Original source from which to enumerate mutation sites and emit
/// parallel `__vcheck_mutant_*` fns. Shared with `#[vcheck_cov_fuzz]`, whose
/// instrumenter consumes the same free-fn / method body shapes.
#[derive(Clone, Debug)]
pub enum CovMutateBodySource {
    FreeFn(verus_syn::ItemFn),
    Method {
        self_ty: Ident,
        method: verus_syn::ImplItemFn,
    },
}

/// Metadata for a `#[vcheck_cov_fuzz]` target. Captured at macro time and
/// flowed through to `expand`'s cov_fuzz emission step. The structural
/// twin of [`CovMutateTarget`].
#[derive(Clone, Debug)]
pub struct CovFuzzTarget {
    /// Display name (qualified for impl methods, e.g. `Counter::step`).
    pub fn_name: String,
    /// Bare function ident (matches the source) — used to scope the
    /// instrumented twin / marker / hits-static naming.
    pub fn_ident: String,
    /// Optional branch-coverage threshold (0..=100). When set and the
    /// reached percentage falls below it, the report test panics so
    /// `cargo test` fails.
    pub threshold: Option<u8>,
    /// Optional skip flag: record the target in the report but do not
    /// run the search.
    pub skip: bool,
    /// `Some(target path)` when this fn is an `assume_specification`
    /// wrapper (detected via the `verus_spec_check::assume_spec_target` doc
    /// sentinel stamped at wrapper synthesis). The implementation behind
    /// the wrapper lives in an external crate, so the source-level
    /// instrumenter has nothing to instrument — the emitter skips the
    /// twin/runner and the report routes the target to external
    /// (instrumented-side-profile) measurement instead. The path (e.g.
    /// `u32::checked_add`) is what the profile extractor matches.
    pub external: Option<String>,
    /// Original assume-specification type parameters retained by a doc
    /// sentinel before concrete VCHECK substitution erases wrapper generics.
    pub generic_type_params: Vec<String>,
    /// Body source for the branch instrumenter (same shape cov_mutate
    /// feeds the mutator).
    pub body_source: CovMutateBodySource,
}

/// Extract the spec-fn target from a `#[verifier::when_used_as_spec(spec_X)]`
/// attribute on a runtime fn. Returns the spec fn name as a String.
pub fn extract_when_used_as_spec(attrs: &[verus_syn::Attribute]) -> Option<String> {
    for attr in attrs {
        let path = attr.path();
        if path.leading_colon.is_some() {
            continue;
        }
        let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
        let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
        if !matches!(&segs[..], ["verifier", "when_used_as_spec"]) {
            continue;
        }
        if let verus_syn::Meta::List(list) = &attr.meta {
            if let Ok(id) = verus_syn::parse2::<Ident>(list.tokens.clone()) {
                return Some(id.to_string());
            }
        }
    }
    None
}

/// Lenient match for the `external_vcheck_provide` macro path: bare,
/// `contrib::`-, or `vstd::contrib::`-qualified.
pub fn macro_path_is_external_provide(path: &verus_syn::Path) -> bool {
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    matches!(
        &segs[..],
        ["external_vcheck_provide"]
            | ["contrib", "external_vcheck_provide"]
            | ["vstd", "contrib", "external_vcheck_provide"]
    )
}

// ---------------------------------------------------------------------------
// `#[vcheck_cov_mutate]` attribute detection
// ---------------------------------------------------------------------------

/// Returns `true` if `attr` is a `#[vcheck_cov_mutate]` (or qualified variant)
/// marker. The attribute may be bare (`#[vcheck_cov_mutate]`) or carry a
/// parenthesized config like `#[vcheck_cov_mutate(threshold = 90)]` or
/// `#[vcheck_cov_mutate(skip)]`.
pub fn attr_is_vcheck_cov_mutate(attr: &verus_syn::Attribute) -> bool {
    let path = attr.path();
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    matches!(
        &segs[..],
        ["vcheck_cov_mutate"] | ["contrib", "vcheck_cov_mutate"] | ["vstd", "contrib", "vcheck_cov_mutate"]
    )
}

/// Parsed options on a `#[vcheck_cov_mutate(...)]` attribute. All fields are
/// optional. Unparseable args are silently ignored — the report runner is
/// informational by default and the attribute should never break a build.
#[derive(Clone, Debug, Default)]
pub struct CovMutateAttrOpts {
    pub threshold: Option<u8>,
    pub skip: bool,
}

/// Parse `#[vcheck_cov_mutate]` / `#[vcheck_cov_mutate(threshold = 90)]` /
/// `#[vcheck_cov_mutate(skip)]`. Returns `None` if the attribute is not a
/// cov_mutate marker. Returns `Some(default)` for the bare form.
pub fn parse_vcheck_cov_mutate_attr(attr: &verus_syn::Attribute) -> Option<CovMutateAttrOpts> {
    if !attr_is_vcheck_cov_mutate(attr) {
        return None;
    }
    let mut opts = CovMutateAttrOpts::default();
    let tokens = match &attr.meta {
        verus_syn::Meta::Path(_) => return Some(opts),
        verus_syn::Meta::List(list) => list.tokens.clone(),
        // `#[vcheck_cov_mutate = ...]` is not the supported shape; ignore.
        verus_syn::Meta::NameValue(_) => return Some(opts),
    };
    use verus_syn::parse::Parser;
    use verus_syn::punctuated::Punctuated;
    use verus_syn::Token;

    enum CovMutateArg {
        Threshold(u8),
        Skip,
    }
    impl verus_syn::parse::Parse for CovMutateArg {
        fn parse(input: verus_syn::parse::ParseStream) -> verus_syn::parse::Result<Self> {
            let key: Ident = input.parse()?;
            match key.to_string().as_str() {
                "skip" => Ok(CovMutateArg::Skip),
                "threshold" => {
                    let _eq: Token![=] = input.parse()?;
                    let lit: verus_syn::LitInt = input.parse()?;
                    let n: u64 = lit.base10_parse()?;
                    if n > 100 {
                        return Err(verus_syn::Error::new_spanned(
                            lit,
                            "verus_spec_check: vcheck_cov_mutate threshold must be 0..=100",
                        ));
                    }
                    Ok(CovMutateArg::Threshold(n as u8))
                }
                other => Err(verus_syn::Error::new_spanned(
                    key,
                    format!(
                        "verus_spec_check: unrecognized vcheck_cov_mutate option `{other}`. \
Supported: `skip`, `threshold = <0..=100>`."
                    ),
                )),
            }
        }
    }

    let parser = |s: verus_syn::parse::ParseStream| {
        Punctuated::<CovMutateArg, Token![,]>::parse_terminated(s)
    };
    if let Ok(args) = parser.parse2(tokens) {
        for a in args {
            match a {
                CovMutateArg::Threshold(n) => opts.threshold = Some(n),
                CovMutateArg::Skip => opts.skip = true,
            }
        }
    }
    Some(opts)
}

// ---------------------------------------------------------------------------
// `#[vcheck_cov_fuzz]` attribute detection
// ---------------------------------------------------------------------------

/// Returns `true` if `attr` is a `#[vcheck_cov_fuzz]` (or qualified variant)
/// marker. The attribute may be bare (`#[vcheck_cov_fuzz]`) or carry a
/// parenthesized config like `#[vcheck_cov_fuzz(threshold = 90)]` or
/// `#[vcheck_cov_fuzz(skip)]`.
pub fn attr_is_vcheck_cov_fuzz(attr: &verus_syn::Attribute) -> bool {
    let path = attr.path();
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    matches!(
        &segs[..],
        ["vcheck_cov_fuzz"] | ["contrib", "vcheck_cov_fuzz"] | ["vstd", "contrib", "vcheck_cov_fuzz"]
    )
}

/// Parsed options on a `#[vcheck_cov_fuzz(...)]` attribute.
#[derive(Clone, Debug, Default)]
pub struct CovFuzzAttrOpts {
    pub threshold: Option<u8>,
    pub skip: bool,
}

/// Parse a cov-fuzz attribute. `None` means this is a different attribute;
/// malformed cov-fuzz syntax is retained as an error instead of silently
/// dropping a requested gate.
pub fn parse_vcheck_cov_fuzz_attr(
    attr: &verus_syn::Attribute,
) -> Option<Result<CovFuzzAttrOpts, Error>> {
    if !attr_is_vcheck_cov_fuzz(attr) {
        return None;
    }
    let mut opts = CovFuzzAttrOpts::default();
    let tokens = match &attr.meta {
        verus_syn::Meta::Path(_) => return Some(Ok(opts)),
        verus_syn::Meta::List(list) => list.tokens.clone(),
        verus_syn::Meta::NameValue(value) => {
            return Some(Err(Error::new_spanned(
                value,
                "verus_spec_check: expected #[vcheck_cov_fuzz(...)]",
            )))
        }
    };
    use verus_syn::parse::Parser;
    use verus_syn::punctuated::Punctuated;
    use verus_syn::Token;

    enum CovFuzzArg {
        Threshold(u8),
        Skip,
    }
    impl verus_syn::parse::Parse for CovFuzzArg {
        fn parse(input: verus_syn::parse::ParseStream) -> verus_syn::parse::Result<Self> {
            let key: Ident = input.parse()?;
            match key.to_string().as_str() {
                "skip" => Ok(CovFuzzArg::Skip),
                "threshold" => {
                    let _eq: Token![=] = input.parse()?;
                    let lit: verus_syn::LitInt = input.parse()?;
                    let n: u64 = lit.base10_parse()?;
                    if n > 100 {
                        return Err(verus_syn::Error::new_spanned(
                            lit,
                            "verus_spec_check: vcheck_cov_fuzz threshold must be 0..=100",
                        ));
                    }
                    Ok(CovFuzzArg::Threshold(n as u8))
                }
                other => Err(verus_syn::Error::new_spanned(
                    key,
                    format!(
                        "verus_spec_check: unrecognized vcheck_cov_fuzz option `{other}`. \
Supported: `skip`, `threshold = <0..=100>`."
                    ),
                )),
            }
        }
    }

    let parser =
        |s: verus_syn::parse::ParseStream| Punctuated::<CovFuzzArg, Token![,]>::parse_terminated(s);
    let args = match parser.parse2(tokens) {
        Ok(args) => args,
        Err(error) => return Some(Err(error)),
    };
    for arg in args {
        match arg {
            CovFuzzArg::Threshold(n) => opts.threshold = Some(n),
            CovFuzzArg::Skip => opts.skip = true,
        }
    }
    Some(Ok(opts))
}

pub fn item_cov_fuzz_opts(item: &Item) -> Result<Option<CovFuzzAttrOpts>, Error> {
    let Some(attrs) = item_attrs(item) else {
        return Ok(None);
    };
    cov_fuzz_opts_from_attrs(attrs)
}

pub fn impl_fn_cov_fuzz_opts(f: &verus_syn::ImplItemFn) -> Result<Option<CovFuzzAttrOpts>, Error> {
    cov_fuzz_opts_from_attrs(&f.attrs)
}

fn cov_fuzz_opts_from_attrs(
    attrs: &[verus_syn::Attribute],
) -> Result<Option<CovFuzzAttrOpts>, Error> {
    let mut found = None;
    for attr in attrs {
        if let Some(parsed) = parse_vcheck_cov_fuzz_attr(attr) {
            let opts = parsed?;
            if found.is_none() {
                found = Some(opts);
            }
        }
    }
    Ok(found)
}

/// Strip every `#[vcheck_cov_fuzz]` (and qualified variants) attribute from
/// an item. Called after metadata capture so the post-classify items are
/// valid Verus syntax.
pub fn strip_cov_fuzz_attr_item(item: &mut Item) {
    if let Some(attrs) = item_attrs_mut(item) {
        attrs.retain(|a| !attr_is_vcheck_cov_fuzz(a));
    }
}

pub fn strip_cov_fuzz_attr_impl_fn(f: &mut verus_syn::ImplItemFn) {
    f.attrs.retain(|a| !attr_is_vcheck_cov_fuzz(a));
}

/// Returns the parsed cov_mutate options for an item, or `None` if the
/// attribute is absent.
pub fn item_cov_mutate_opts(item: &Item) -> Option<CovMutateAttrOpts> {
    let attrs = item_attrs(item)?;
    attrs.iter().find_map(parse_vcheck_cov_mutate_attr)
}

/// Same as `item_cov_mutate_opts` but for an `ImplItemFn`.
pub fn impl_fn_cov_mutate_opts(f: &verus_syn::ImplItemFn) -> Option<CovMutateAttrOpts> {
    f.attrs.iter().find_map(parse_vcheck_cov_mutate_attr)
}

/// Strip every `#[vcheck_cov_mutate]` (and qualified variants) attribute from
/// an item. Called after metadata capture so the post-classify items are
/// valid Verus syntax.
pub fn strip_cov_mutate_attr_item(item: &mut Item) {
    if let Some(attrs) = item_attrs_mut(item) {
        attrs.retain(|a| !attr_is_vcheck_cov_mutate(a));
    }
}

pub fn strip_cov_mutate_attr_impl_fn(f: &mut verus_syn::ImplItemFn) {
    f.attrs.retain(|a| !attr_is_vcheck_cov_mutate(a));
}

/// Recover an item's mutable attribute list. Mirrors `item_attrs` from the
/// `vcheck_attr` module but is duplicated here to avoid a cross-module
/// import; the read-only `item_attrs` is already used elsewhere in this
/// file via the path shown.
pub fn item_attrs(item: &Item) -> Option<&Vec<verus_syn::Attribute>> {
    match item {
        Item::Const(i) => Some(&i.attrs),
        Item::Enum(i) => Some(&i.attrs),
        Item::ExternCrate(i) => Some(&i.attrs),
        Item::Fn(i) => Some(&i.attrs),
        Item::ForeignMod(i) => Some(&i.attrs),
        Item::Impl(i) => Some(&i.attrs),
        Item::Macro(i) => Some(&i.attrs),
        Item::Mod(i) => Some(&i.attrs),
        Item::Static(i) => Some(&i.attrs),
        Item::Struct(i) => Some(&i.attrs),
        Item::Trait(i) => Some(&i.attrs),
        Item::TraitAlias(i) => Some(&i.attrs),
        Item::Type(i) => Some(&i.attrs),
        Item::Union(i) => Some(&i.attrs),
        Item::Use(i) => Some(&i.attrs),
        _ => None,
    }
}

pub fn item_attrs_mut(item: &mut Item) -> Option<&mut Vec<verus_syn::Attribute>> {
    match item {
        Item::Const(i) => Some(&mut i.attrs),
        Item::Enum(i) => Some(&mut i.attrs),
        Item::ExternCrate(i) => Some(&mut i.attrs),
        Item::Fn(i) => Some(&mut i.attrs),
        Item::ForeignMod(i) => Some(&mut i.attrs),
        Item::Impl(i) => Some(&mut i.attrs),
        Item::Macro(i) => Some(&mut i.attrs),
        Item::Mod(i) => Some(&mut i.attrs),
        Item::Static(i) => Some(&mut i.attrs),
        Item::Struct(i) => Some(&mut i.attrs),
        Item::Trait(i) => Some(&mut i.attrs),
        Item::TraitAlias(i) => Some(&mut i.attrs),
        Item::Type(i) => Some(&mut i.attrs),
        Item::Union(i) => Some(&mut i.attrs),
        Item::Use(i) => Some(&mut i.attrs),
        _ => None,
    }
}

pub fn classify(items: Vec<Item>) -> Classified {
    let mut passthrough_items = Vec::new();
    let mut engine_items = Vec::new();
    let mut spec_fn_names = HashSet::new();
    let mut user_types = Vec::new();
    let mut user_type_names = HashSet::new();
    let mut contract_targets: Vec<ContractTarget> = Vec::new();
    // `#[vcheck]`-marked fns (sentinel present) with NO contract clauses —
    // a shape that used to silently produce no harness; surfaced as
    // compile errors at the end of classification.
    let mut contract_errors: Vec<Error> = Vec::new();
    let mut external_provide_bodies: Vec<TokenStream2> = Vec::new();
    let mut when_used_as_spec_redirect: HashMap<String, String> = HashMap::new();
    let mut cov_mutate_targets: Vec<CovMutateTarget> = Vec::new();
    let mut cov_fuzz_targets: Vec<CovFuzzTarget> = Vec::new();

    // Pass 0: populate the per-expansion `#[vcheck_view]` / `VcheckConcretize`
    // registry. A `#[vcheck_view]` uninterp spec fn `view(x: &T) -> nat/int`
    // registers `view` as a view fn and `T` as an opaque concretizable type,
    // so `classify_*` treats `T`/`&T` params as `OpaqueConcretize` and the
    // rewriter lowers `view(x)` to `x.vcheck_realize()`.
    reset_concretize_registry();
    for item in &items {
        if let Item::Fn(f) = item {
            if let Some(attr) = f.attrs.iter().find(|a| attr_is_ident(a, "vcheck_view")) {
                if let (Some(subject), Some(info)) =
                    (view_fn_subject_type(&f.sig), parse_vcheck_view_attr(attr))
                {
                    register_view_fn(f.sig.ident.to_string(), subject, info);
                }
            }
        }
    }

    // First pass: collect when_used_as_spec mappings before classifying so
    // contract rewrites for any item see the full redirect map.
    for item in &items {
        match item {
            Item::Fn(f) => {
                if let Some(t) = extract_when_used_as_spec(&f.attrs) {
                    when_used_as_spec_redirect.insert(f.sig.ident.to_string(), t);
                }
            }
            Item::Impl(im) => {
                for ii in &im.items {
                    if let verus_syn::ImplItem::Fn(f) = ii {
                        if let Some(t) = extract_when_used_as_spec(&f.attrs) {
                            when_used_as_spec_redirect.insert(f.sig.ident.to_string(), t);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    for item in items {
        match &item {
            Item::Fn(item_fn) => match &item_fn.sig.mode {
                FnMode::Spec(..) => {
                    // `#[vcheck_view]` uninterp views have no body to compile into
                    // a companion; the rewriter lowers `view(x)` to
                    // `x.vcheck_realize()` instead. Keep it out of the engine
                    // block (it would trip the uninterp diagnostic) and out of
                    // `spec_fn_names` (so calls route to the view rewrite, not
                    // an `exec_view` rename).
                    if item_fn.attrs.iter().any(|a| attr_is_ident(a, "vcheck_view")) {
                        // Nothing to emit; the original stays in the user's
                        // (non-test) source for the verifier.
                    } else {
                        spec_fn_names.insert(item_fn.sig.ident.to_string());
                        engine_items.push(item.clone());
                    }
                }
                // `fn` (default) and explicit `exec fn` both denote
                // executable code. Either is valid as a contract-bearing
                // target that the harness should sample and run.
                FnMode::Default | FnMode::Exec(..) => {
                    let has_contract = item_fn.sig.spec.requires.is_some()
                        || item_fn.sig.spec.ensures.is_some()
                        || item_fn.sig.spec.returns.is_some();
                    if has_contract {
                        // Read `#[vcheck(miri = "skip")]` (if any) before we
                        // strip the marker, so the harness can carry the
                        // `#[cfg_attr(miri, ignore)]` translation.
                        let miri_skip =
                            crate::vcheck_attr::item_vcheck_miri_mode(&item).should_skip_under_miri();
                        // Read the selected backend from the same source
                        // (`#[vcheck(backend = "...")]`, recovered via the doc
                        // sentinel after the marker strip).
                        let backend = crate::vcheck_attr::item_vcheck_backend(&item);
                        // Bolero mode (`fuzz`/`kani`), recovered from the same
                        // sentinel. `None` on the proptest backend.
                        let bolero_mode = crate::vcheck_attr::item_vcheck_bolero_mode(&item);
                        // Inline-assert-only fold: the inline-assert
                        // harness needs this target as its enclosing
                        // context, but we suppress the regular
                        // `vcheck_<fn>` harness emitted for it.
                        let skip_regular_harness =
                            crate::vcheck_attr::attrs_have_skip_regular_harness_sentinel(
                                &item_fn.attrs,
                            );
                        contract_targets.push(ContractTarget::FreeFn {
                            item_fn: item_fn.clone(),
                            miri_skip,
                            backend,
                            bolero_mode,
                            skip_regular_harness,
                        });
                    } else if item_fn_has_harness_sentinel(item_fn)
                        && !crate::vcheck_attr::attrs_have_skip_regular_harness_sentinel(
                            &item_fn.attrs,
                        )
                    {
                        // Explicitly `#[vcheck]`-marked, but no contract to
                        // test: hard error instead of silently emitting
                        // no harness (see `no_contract_error`).
                        contract_errors.push(no_contract_error(
                            &item_fn.sig.ident,
                            &item_fn.sig.ident.to_string(),
                        ));
                    }
                    // Capture #[vcheck_cov_mutate] metadata before moving the
                    // item into passthrough_items. We snapshot the fn ident
                    // and opts now so we can stop borrowing `item` before
                    // the move below.
                    let cov_meta = item_cov_mutate_opts(&item).map(|opts| {
                        let fn_ident = item_fn.sig.ident.to_string();
                        CovMutateTarget {
                            fn_name: fn_ident.clone(),
                            fn_ident: fn_ident.clone(),
                            threshold: opts.threshold,
                            skip: opts.skip,
                            body_source: CovMutateBodySource::FreeFn(item_fn.clone()),
                        }
                    });
                    // Same capture-then-strip dance for #[vcheck_cov_fuzz].
                    // Parse errors are retained as compile errors, and the
                    // attribute is stripped on every path so downstream Verus
                    // parsing never sees an unknown attribute.
                    let cov_fuzz_meta = match item_cov_fuzz_opts(&item) {
                        Ok(Some(opts)) => {
                            let fn_ident = item_fn.sig.ident.to_string();
                            // An assume_specification wrapper carries the
                            // target-path sentinel; its body is a trusted
                            // call into external code, so the target is
                            // routed to external measurement.
                            let external = crate::vcheck_attr::assume_spec_target_from_doc_sentinel(
                                &item_fn.attrs,
                            );
                            let generic_type_params = if external.is_some() {
                                crate::vcheck_attr::assume_spec_type_params_from_doc_sentinel(
                                    &item_fn.attrs,
                                )
                            } else {
                                Vec::new()
                            };
                            Some(CovFuzzTarget {
                                fn_name: fn_ident.clone(),
                                fn_ident: fn_ident.clone(),
                                threshold: opts.threshold,
                                skip: opts.skip,
                                external,
                                generic_type_params,
                                body_source: CovMutateBodySource::FreeFn(item_fn.clone()),
                            })
                        }
                        Ok(None) => None,
                        Err(error) => {
                            contract_errors.push(error);
                            None
                        }
                    };
                    let mut item = item;
                    if let Some(target) = cov_meta {
                        cov_mutate_targets.push(target);
                        // Strip the attr so Verus doesn't see an unknown
                        // attribute downstream.
                        strip_cov_mutate_attr_item(&mut item);
                    }
                    if let Some(target) = cov_fuzz_meta {
                        cov_fuzz_targets.push(target);
                    }
                    strip_cov_fuzz_attr_item(&mut item);
                    passthrough_items.push(item);
                }
                _ => {
                    passthrough_items.push(item);
                }
            },
            Item::Struct(item_struct) => {
                user_type_names.insert(item_struct.ident.to_string());
                user_types.push(UserType::Struct(item_struct.clone()));
                engine_items.push(item);
            }
            Item::Enum(item_enum) => {
                user_type_names.insert(item_enum.ident.to_string());
                user_types.push(UserType::Enum(item_enum.clone()));
                engine_items.push(item);
            }
            Item::Impl(item_impl) => {
                // Three cases:
                //   1. All spec methods -> route the whole impl to the engine.
                //   2. All exec methods -> passthrough; harvest contracts.
                //   3. Mixed -> split into two impl blocks.
                let self_ty_ident = impl_self_ty_ident(item_impl);
                // If the impl block has any sentinel-marked method, only
                // sentinel-bearing methods become harness targets. Without
                // the sentinel (e.g. `#[vcheck]` was on the type, not on
                // individual methods), every contract-bearing exec method
                // is a target — preserves prior behavior.
                let impl_has_sentinel = impl_has_harness_sentinel(item_impl);
                let mut spec_methods: Vec<verus_syn::ImplItem> = Vec::new();
                let mut exec_methods: Vec<verus_syn::ImplItem> = Vec::new();
                let mut other_items: Vec<verus_syn::ImplItem> = Vec::new();
                for ii in &item_impl.items {
                    match ii {
                        verus_syn::ImplItem::Fn(impl_fn) => {
                            if matches!(impl_fn.sig.mode, FnMode::Spec(..)) {
                                spec_fn_names.insert(impl_fn.sig.ident.to_string());
                                spec_methods.push(ii.clone());
                            } else if matches!(impl_fn.sig.mode, FnMode::Default | FnMode::Exec(..))
                            {
                                let mut method_clone = impl_fn.clone();
                                let cov_opts = impl_fn_cov_mutate_opts(&method_clone);
                                if let Some(opts) = cov_opts {
                                    if let Some(self_ty) = self_ty_ident.clone() {
                                        let fn_ident_s = method_clone.sig.ident.to_string();
                                        let self_ty_s = self_ty.to_string();
                                        cov_mutate_targets.push(CovMutateTarget {
                                            fn_name: format!("{}::{}", self_ty_s, fn_ident_s),
                                            fn_ident: fn_ident_s.clone(),
                                            threshold: opts.threshold,
                                            skip: opts.skip,
                                            body_source: CovMutateBodySource::Method {
                                                self_ty: self_ty.clone(),
                                                method: impl_fn.clone(),
                                            },
                                        });
                                    }
                                    strip_cov_mutate_attr_impl_fn(&mut method_clone);
                                }
                                match impl_fn_cov_fuzz_opts(&method_clone) {
                                    Ok(Some(opts)) => {
                                        if let Some(self_ty) = self_ty_ident.clone() {
                                            let fn_ident_s = method_clone.sig.ident.to_string();
                                            let self_ty_s = self_ty.to_string();
                                            cov_fuzz_targets.push(CovFuzzTarget {
                                                fn_name: format!("{}::{}", self_ty_s, fn_ident_s),
                                                fn_ident: fn_ident_s.clone(),
                                                threshold: opts.threshold,
                                                skip: opts.skip,
                                                // assume_spec wrappers are
                                                // always free fns; methods
                                                // are never external.
                                                external: None,
                                                generic_type_params: Vec::new(),
                                                body_source: CovMutateBodySource::Method {
                                                    self_ty: self_ty.clone(),
                                                    method: impl_fn.clone(),
                                                },
                                            });
                                        }
                                    }
                                    Ok(None) => {}
                                    Err(error) => contract_errors.push(error),
                                }
                                // Strip even after a parse error so the
                                // accumulated diagnostic, rather than an
                                // unrelated unknown-attribute error, wins.
                                strip_cov_fuzz_attr_impl_fn(&mut method_clone);
                                exec_methods.push(verus_syn::ImplItem::Fn(method_clone.clone()));
                                let has_contract = impl_fn.sig.spec.requires.is_some()
                                    || impl_fn.sig.spec.ensures.is_some()
                                    || impl_fn.sig.spec.returns.is_some();
                                let is_harness_target = if impl_has_sentinel {
                                    impl_fn_has_harness_sentinel(impl_fn)
                                } else {
                                    true
                                };
                                if has_contract && is_harness_target {
                                    if let Some(self_ty) = self_ty_ident.clone() {
                                        let miri_skip =
                                            crate::vcheck_attr::impl_fn_vcheck_miri_mode(impl_fn)
                                                .should_skip_under_miri();
                                        let backend = crate::vcheck_attr::impl_fn_vcheck_backend(impl_fn);
                                        let bolero_mode =
                                            crate::vcheck_attr::impl_fn_vcheck_bolero_mode(impl_fn);
                                        // See FreeFn equivalent above for
                                        // skip_regular_harness rationale.
                                        let skip_regular_harness =
                                            crate::vcheck_attr::attrs_have_skip_regular_harness_sentinel(
                                                &impl_fn.attrs,
                                            );
                                        contract_targets.push(ContractTarget::Method {
                                            self_ty,
                                            method: method_clone,
                                            miri_skip,
                                            backend,
                                            bolero_mode,
                                            skip_regular_harness,
                                        });
                                    }
                                    // If we can't resolve Self type, the
                                    // method still goes into passthrough but
                                    // isn't harnessed (we lack a strategy).
                                } else if !has_contract
                                    && impl_fn_has_harness_sentinel(impl_fn)
                                    && !crate::vcheck_attr::attrs_have_skip_regular_harness_sentinel(
                                        &impl_fn.attrs,
                                    )
                                {
                                    // Explicitly `#[vcheck]`-marked method with
                                    // no contract: same hard error as the
                                    // free-fn shape. Scoped to the method's
                                    // OWN sentinel (not the whole-impl
                                    // fallback) so unmarked helper methods
                                    // in a folded impl stay exempt.
                                    let display = match &self_ty_ident {
                                        Some(t) => {
                                            format!("{}::{}", t, impl_fn.sig.ident)
                                        }
                                        None => impl_fn.sig.ident.to_string(),
                                    };
                                    contract_errors
                                        .push(no_contract_error(&impl_fn.sig.ident, &display));
                                }
                            } else {
                                other_items.push(ii.clone());
                            }
                        }
                        _ => other_items.push(ii.clone()),
                    }
                }

                let make_impl_with = |items: Vec<verus_syn::ImplItem>| -> ItemImpl {
                    let mut new_impl = item_impl.clone();
                    new_impl.items = items;
                    new_impl
                };

                if !spec_methods.is_empty() && exec_methods.is_empty() && other_items.is_empty() {
                    // Pure spec impl -> engine.
                    engine_items.push(item);
                } else if spec_methods.is_empty() {
                    // Pure exec (no spec methods): build the impl from
                    // `exec_methods + other_items` rather than the original
                    // `item` so per-method modifications (e.g. stripping
                    // `#[vcheck_cov_mutate]` after metadata capture) are
                    // preserved.
                    let mut all = exec_methods;
                    all.extend(other_items);
                    let exec_only = make_impl_with(all);
                    passthrough_items.push(Item::Impl(exec_only));
                } else {
                    // Mixed: split.
                    let spec_only = make_impl_with(spec_methods);
                    let mut others = exec_methods;
                    others.extend(other_items);
                    let exec_only = make_impl_with(others);
                    engine_items.push(Item::Impl(spec_only));
                    passthrough_items.push(Item::Impl(exec_only));
                }
            }
            _ => {
                // external_vcheck_provide! { ... }: register the provided names
                // as spec fns (so contract calls `f(..)` rename to
                // `exec_f(..)`) and stash the body for companion emission. The
                // macro item itself does not pass through to verus!.
                if let Item::Macro(m) = &item {
                    if macro_path_is_external_provide(&m.mac.path) {
                        for n in crate::external_vcheck_provide::provided_names(m.mac.tokens.clone()) {
                            spec_fn_names.insert(n);
                        }
                        // int/nat-returning twins: register so the contract
                        // rewriter routes their call results through the
                        // SpecInt domain (casts, comparisons).
                        for n in
                            crate::external_vcheck_provide::int_returning_names(m.mac.tokens.clone())
                        {
                            register_int_returning_provided(n);
                        }
                        external_provide_bodies.push(m.mac.tokens.clone());
                        continue;
                    }
                }
                passthrough_items.push(item);
            }
        }
    }

    // After all items are classified, walk the passthrough items'
    // bodies looking for `#[vcheck]`-marked inline asserts. The walker
    // both collects targets and strips the `#[vcheck]` attribute (so the
    // verifier doesn't choke on an unknown attribute when the items
    // are re-emitted). Errors here are accumulated into the result
    // `Classified` and surfaced by the caller as compile errors.
    let mut inline_assert_targets: Vec<InlineAssertContext> = Vec::new();
    let mut inline_assert_errors: Vec<Error> = Vec::new();
    discover_inline_asserts_in_items(
        &mut passthrough_items,
        &contract_targets,
        &mut inline_assert_targets,
        &mut inline_assert_errors,
    );

    // The `contract_targets` clones above were taken before the
    // discovery pass stripped `#[vcheck]` from the asserts in
    // `passthrough_items`. Rebuild the matching entries from the now-
    // stripped `passthrough_items` so the checker fn we emit later
    // doesn't re-introduce the marker. (The checker fn is built by
    // re-emitting the enclosing fn's body via `emit_mutant_fn_*`, so a
    // stale `#[vcheck]` on the assert would leak through and the
    // verifier would reject it.)
    refresh_contract_targets_from_items(&passthrough_items, &mut contract_targets);

    // We surface inline-assert errors by attaching them to the first
    // affected target's span. They cause the macro to emit
    // compile_error! at the harness emission step. Currently the
    // simpler approach is to package them into the `passthrough_items`
    // unchanged — they show up at expand time. For now, drop a
    // compile_error per error into the engine_items so the user sees
    // it as a build failure with the right span.
    for err in &inline_assert_errors {
        let ts = err.to_compile_error();
        engine_items.push(verus_syn::Item::Verbatim(ts));
    }

    Classified {
        passthrough_items,
        engine_items,
        spec_fn_names,
        user_types,
        user_type_names,
        contract_targets,
        external_provide_bodies,
        when_used_as_spec_redirect,
        cov_mutate_targets,
        cov_fuzz_targets,
        inline_assert_targets,
        contract_errors,
    }
}

/// Walk every fn body in `items` looking for `#[vcheck]`-marked inline
/// asserts. For each one found:
///
///  - Strip the `#[vcheck]` attribute (in place) so the verifier doesn't
///    see an unknown attribute when the item is later re-emitted.
///  - Look up the enclosing fn's `ContractTarget` clone (free fn or
///    impl method) by ident match. Path-form asserts need the
///    enclosing fn's signature for harness sampling; forall-form
///    don't (they sample the binders directly), but we still record
///    a match so the user can mix the two forms in one fn.
///  - Push an `InlineAssertContext` into `out_targets`.
///  - Push any discovery error into `out_errors`.
///
/// We walk the same item set that gets re-emitted to the verifier, so
/// the `#[vcheck]` strip is the only side effect on `items`. The
/// discovery is purely structural — no spec->exec lowering happens at
/// this stage.
pub fn discover_inline_asserts_in_items(
    items: &mut [Item],
    contract_targets: &[ContractTarget],
    out_targets: &mut Vec<InlineAssertContext>,
    out_errors: &mut Vec<Error>,
) {
    for item in items.iter_mut() {
        match item {
            Item::Fn(item_fn) => {
                let label = item_fn.sig.ident.to_string();
                let mut local_targets = Vec::new();
                if let Err(e) = crate::vcheck_assert::discover_in_block(
                    &mut item_fn.block,
                    &label,
                    &mut local_targets,
                ) {
                    out_errors.push(e);
                    continue;
                }
                let enclosing = contract_targets.iter().find(|ct| match ct {
                    ContractTarget::FreeFn { item_fn: f, .. } => f.sig.ident == item_fn.sig.ident,
                    ContractTarget::Method { .. } => false,
                });
                for tgt in local_targets {
                    out_targets.push(InlineAssertContext {
                        target: tgt,
                        enclosing: enclosing.cloned(),
                    });
                }
            }
            Item::Impl(item_impl) => {
                let self_ty_ident = impl_self_ty_ident(item_impl);
                for ii in item_impl.items.iter_mut() {
                    if let verus_syn::ImplItem::Fn(impl_fn) = ii {
                        let label = match &self_ty_ident {
                            Some(t) => format!("{}::{}", t, impl_fn.sig.ident),
                            None => impl_fn.sig.ident.to_string(),
                        };
                        let mut local_targets = Vec::new();
                        if let Err(e) = crate::vcheck_assert::discover_in_block(
                            &mut impl_fn.block,
                            &label,
                            &mut local_targets,
                        ) {
                            out_errors.push(e);
                            continue;
                        }
                        let enclosing = contract_targets.iter().find(|ct| match ct {
                            ContractTarget::Method {
                                method, self_ty, ..
                            } => {
                                method.sig.ident == impl_fn.sig.ident
                                    && Some(self_ty) == self_ty_ident.as_ref()
                            }
                            ContractTarget::FreeFn { .. } => false,
                        });
                        for tgt in local_targets {
                            out_targets.push(InlineAssertContext {
                                target: tgt,
                                enclosing: enclosing.cloned(),
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Walk `passthrough_items` and replace each `ContractTarget` body
/// with the corresponding (now-stripped) item's body. This keeps the
/// `contract_targets` clones in sync with the post-discovery state of
/// the passthrough items, so that re-emitting bodies via
/// `emit_mutant_fn_*` doesn't re-introduce the `#[vcheck]` markers we
/// just stripped.
///
/// We match by ident (free fn) or by `(self_ty, method_ident)` pair
/// (impl method). When no match is found we leave the target alone —
/// it's a stale clone but there's no enclosing item to refresh from.
pub fn refresh_contract_targets_from_items(items: &[Item], targets: &mut Vec<ContractTarget>) {
    for target in targets.iter_mut() {
        match target {
            ContractTarget::FreeFn { item_fn, .. } => {
                for item in items {
                    if let Item::Fn(updated) = item {
                        if updated.sig.ident == item_fn.sig.ident {
                            *item_fn = updated.clone();
                            break;
                        }
                    }
                }
            }
            ContractTarget::Method {
                self_ty, method, ..
            } => {
                for item in items {
                    if let Item::Impl(im) = item {
                        let st = impl_self_ty_ident(im);
                        if st.as_ref() != Some(self_ty) {
                            continue;
                        }
                        for ii in &im.items {
                            if let verus_syn::ImplItem::Fn(updated) = ii {
                                if updated.sig.ident == method.sig.ident {
                                    *method = updated.clone();
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub fn impl_self_ty_ident(item_impl: &ItemImpl) -> Option<Ident> {
    if item_impl.trait_.is_some() {
        return None;
    }
    if let Type::Path(tp) = item_impl.self_ty.as_ref() {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let seg = &tp.path.segments[0];
            if matches!(seg.arguments, PathArguments::None) {
                return Some(seg.ident.clone());
            }
        }
    }
    None
}

/// Free-fn counterpart of [`impl_fn_has_harness_sentinel`]: true if the
/// fn carries the harness sentinel the `vcheck_attr` pass leaves behind on
/// originally-`#[vcheck]`-marked FREE fns (see
/// `vcheck_attr::convert_vcheck_to_sentinel_item`).
pub fn item_fn_has_harness_sentinel(f: &verus_syn::ItemFn) -> bool {
    for attr in &f.attrs {
        if let verus_syn::Meta::NameValue(nv) = &attr.meta {
            if !nv.path.is_ident("doc") {
                continue;
            }
            if let verus_syn::Expr::Lit(lit) = &nv.value {
                if let verus_syn::Lit::Str(s) = &lit.lit {
                    if s.value() == crate::vcheck_attr::VERUS_SPEC_CHECK_HARNESS_SENTINEL {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// The compile error for a `#[vcheck]`-marked fn with no contract clauses.
/// Before this check existed, such a fn silently produced NO harness —
/// commenting out a contract during spec ablation left `#[vcheck]` (and any
/// coverage-report threshold implying a tested contract) in place while
/// the fn dropped out of the pipeline entirely: a green run that tested
/// nothing. Fail loudly instead.
fn no_contract_error(fn_name: &dyn quote::ToTokens, display: &str) -> Error {
    Error::new_spanned(
        fn_name,
        format!(
            "verus_spec_check: `#[vcheck]` on `{display}`, but the fn has no `requires`, \
             `ensures`, or `returns` clause — the harness would run the fn and \
             assert nothing (a vacuous pass). Add a contract clause, or remove \
             the fn-level `#[vcheck]` (a stmt-level `#[vcheck] assert(...)` inside \
             the body keeps working without it)."
        ),
    )
}

/// True if the impl-fn carries the harness sentinel doc-attribute that the
/// `vcheck_attr` strip pass leaves behind on originally-marked methods. See
/// `vcheck_attr::VERUS_SPEC_CHECK_HARNESS_SENTINEL`.
pub fn impl_fn_has_harness_sentinel(f: &verus_syn::ImplItemFn) -> bool {
    for attr in &f.attrs {
        let path = attr.path();
        if path.leading_colon.is_some() || path.segments.len() != 1 {
            continue;
        }
        if path.segments[0].ident != "doc" {
            continue;
        }
        if let verus_syn::Meta::NameValue(nv) = &attr.meta {
            if let verus_syn::Expr::Lit(lit) = &nv.value {
                if let verus_syn::Lit::Str(s) = &lit.lit {
                    if s.value() == crate::vcheck_attr::VERUS_SPEC_CHECK_HARNESS_SENTINEL {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// True if any method in the impl block carries the harness sentinel.
pub fn impl_has_harness_sentinel(item_impl: &ItemImpl) -> bool {
    item_impl.items.iter().any(|ii| match ii {
        verus_syn::ImplItem::Fn(f) => impl_fn_has_harness_sentinel(f),
        _ => false,
    })
}
