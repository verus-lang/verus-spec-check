use super::*;

/// Sentinel doc string prefixes used to stash the target
/// path of synthesized wrappers
pub const BACKEND_DOC_PREFIX: &str = "verus_spec_check::backend = ";
pub const BOLERO_MODE_DOC_PREFIX: &str = "verus_spec_check::bolero::mode = ";
pub const ASSUME_SPEC_TARGET_DOC_PREFIX: &str = "verus_spec_check::assume_spec_target = ";
pub const ASSUME_SPEC_TYPE_PARAMS_DOC_PREFIX: &str = "verus_spec_check::assume_spec_type_params = ";
pub const MIRI_MODE_DOC_PREFIX: &str = "verus_spec_check::miri::mode = ";
pub const SKIP_REGULAR_HARNESS_DOC: &str = "verus_spec_check::skip_regular_harness";

/// Per-`#[vcheck]` Miri opt-in/opt-out mode. Carried alongside the contract
/// target through to the harness emitter, which translates `Skip` into a
/// `#[cfg_attr(miri, ignore)]` attribute on the emitted `#[test]` fn.
///
/// `Auto` is the default and currently equivalent to `Run`. Reserved as a
/// distinct variant so future heuristics (e.g. "skip if the param list
/// references `String`/`Vec` with a high case count") can flip the default
/// without breaking explicit opt-in callers.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum VcheckMiriMode {
    #[default]
    Auto,
    Run,
    Skip,
}

impl VcheckMiriMode {
    /// True if the emitted harness should carry `#[cfg_attr(miri, ignore)]`.
    pub fn should_skip_under_miri(self) -> bool {
        matches!(self, VcheckMiriMode::Skip)
    }
}

/// Scan a single `#[vcheck(...)]` attribute for `miri = "..."`. Returns the
/// parsed mode if a `miri = "..."` pair is present and recognised; returns
/// `Auto` for any other form (bare `#[vcheck]`, `#[vcheck(N = 4)]` without a
/// `miri` key, etc.). Unknown string values fall back to `Auto` and trigger
/// no error — emission silently runs the harness, matching the default.
pub fn parse_marker_miri_mode(attr: &Attribute) -> VcheckMiriMode {
    let tokens = match &attr.meta {
        Meta::Path(_) => return VcheckMiriMode::Auto,
        Meta::List(list) => list.tokens.clone(),
        Meta::NameValue(_) => return VcheckMiriMode::Auto,
    };
    // Walk the attribute's token stream looking for the `miri = "..."`
    // pair. We do a token-tree scan rather than re-using the Subst parser
    // because Subst silently routes string-literal RHS into the const-param
    // map, where it'd silently no-op for the `miri` key.
    let mut iter = tokens.into_iter().peekable();
    while let Some(tt) = iter.next() {
        if let proc_macro2::TokenTree::Ident(id) = &tt {
            if id == "miri" {
                // Expect `= "<mode>"`.
                if let Some(proc_macro2::TokenTree::Punct(p)) = iter.peek() {
                    if p.as_char() == '=' {
                        let _ = iter.next();
                        if let Some(proc_macro2::TokenTree::Literal(lit)) = iter.next() {
                            let s = lit.to_string();
                            // Literal::to_string includes the surrounding
                            // quotes for string literals.
                            let trimmed = s.trim_matches('"');
                            return match trimmed {
                                "skip" => VcheckMiriMode::Skip,
                                "run" => VcheckMiriMode::Run,
                                "auto" => VcheckMiriMode::Auto,
                                _ => VcheckMiriMode::Auto,
                            };
                        }
                    }
                }
            }
        }
    }
    VcheckMiriMode::Auto
}

/// Return the `miri` mode for a `#[vcheck(...)]` attribute on a free fn
/// (`Item`). Returns `Auto` if no `#[vcheck]` attribute is present.
///
/// Looks at two sources, in order:
///
/// 1. The doc-comment sentinel stamped by `stamp_miri_mode_sentinel_item`
///    during `vcheck_provide_preprocess`. This is the form the
///    `verus_spec_check_unverified!` macro sees on items handed off to the
///    engine, since the original `#[vcheck(...)]` attribute is stripped
///    before fold.
/// 2. The original `#[vcheck(...)]` attribute itself. This covers callers
///    that read the mode before `vcheck_provide_preprocess` strips it (no
///    such call exists today, but the redundant scan is cheap and
///    forward-compatible).
pub fn item_vcheck_miri_mode(item: &Item) -> VcheckMiriMode {
    if let Some(attrs) = item_attrs(item) {
        if let Some(mode) = miri_mode_from_doc_sentinel(attrs) {
            return mode;
        }
    }
    item_attrs(item)
        .and_then(|attrs| attrs.iter().find(|a| attr_is(a, "vcheck")))
        .map(parse_marker_miri_mode)
        .unwrap_or_default()
}

/// Return the `miri` mode for a `#[vcheck(...)]` attribute on an impl method.
///
/// See [`item_vcheck_miri_mode`] for the sentinel-vs-attribute resolution
/// order.
pub fn impl_fn_vcheck_miri_mode(f: &verus_syn::ImplItemFn) -> VcheckMiriMode {
    if let Some(mode) = miri_mode_from_doc_sentinel(&f.attrs) {
        return mode;
    }
    f.attrs
        .iter()
        .find(|a| attr_is(a, "vcheck"))
        .map(parse_marker_miri_mode)
        .unwrap_or_default()
}



/// Stamp a `#[doc = "verus_spec_check::miri::mode = <mode>"]` sentinel attribute on
/// the item when its `#[vcheck(...)]` carried `miri = "..."`. No-op when the
/// item has no `#[vcheck]` attribute, no `miri` key, or the mode is the default
/// `Auto` (which doesn't need to survive — `Auto` is the engine default).
pub fn stamp_miri_mode_sentinel_item(item: &mut Item) {
    let mode = item_vcheck_miri_mode(item);
    stamp_miri_mode_sentinel_on_attrs(item_attrs_mut(item), mode);
}

/// Same as [`stamp_miri_mode_sentinel_item`] but for impl-fn items.
pub fn stamp_miri_mode_sentinel_impl_fn(f: &mut verus_syn::ImplItemFn) {
    let mode = impl_fn_vcheck_miri_mode(f);
    stamp_miri_mode_sentinel_on_attrs(Some(&mut f.attrs), mode);
}

/// Push the doc sentinel onto the given attrs slot. No-op for `Auto`
/// (which carries no information that needs to survive a strip) and for
/// items without an attribute slot.
pub fn stamp_miri_mode_sentinel_on_attrs(attrs: Option<&mut Vec<Attribute>>, mode: VcheckMiriMode) {
    let attrs = match attrs {
        Some(a) => a,
        None => return,
    };
    let token = match mode {
        VcheckMiriMode::Skip => "skip",
        VcheckMiriMode::Run => "run",
        // Auto is the engine default; no need to materialize.
        VcheckMiriMode::Auto => return,
    };
    let doc_value = format!("{MIRI_MODE_DOC_PREFIX}{token}");
    let attr: Attribute = verus_syn::parse_quote! { #[doc = #doc_value] };
    attrs.push(attr);
}

/// Recover the Miri mode from a doc-comment sentinel attribute. Returns
/// `None` when no sentinel is present (in which case callers should fall
/// back to scanning the original `#[vcheck(...)]` attribute, if any).
pub fn miri_mode_from_doc_sentinel(attrs: &[Attribute]) -> Option<VcheckMiriMode> {
    for a in attrs {
        // Looking for `#[doc = "verus_spec_check::miri::mode = <mode>"]`.
        let mnv = match &a.meta {
            Meta::NameValue(mnv) => mnv,
            _ => continue,
        };
        if !mnv.path.get_ident().map(|id| id == "doc").unwrap_or(false) {
            continue;
        }
        // The RHS is an expression; the literal form is a string.
        if let Expr::Lit(lit) = &mnv.value {
            if let verus_syn::Lit::Str(s) = &lit.lit {
                let v = s.value();
                if let Some(rest) = v.strip_prefix(MIRI_MODE_DOC_PREFIX) {
                    return Some(match rest {
                        "skip" => VcheckMiriMode::Skip,
                        "run" => VcheckMiriMode::Run,
                        _ => VcheckMiriMode::Auto,
                    });
                }
            }
        }
    }
    None
}

/// Which property-testing backend a `#[vcheck]` harness should target?
/// By default, proptest and bolero are supported. Miri may be supported 
/// in the future.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum VcheckBackend {
    #[default]
    Proptest,
    Bolero,
}

/// Which bolero *mode* a `#[vcheck(mode = "...")]` selects when the backend is
/// bolero. Both modes emit the identical `bolero::check!()` harness (bolero
/// picks its engine from compile-time `cfg` set by the `cargo bolero`
/// subcommand. THis records *intent*, so tooling knows which
/// `cargo bolero test --engine <e>` to drive and so later phases can `cfg`-gate
/// a harness (never via `#[ignore]`, which is invisible to cargo-bolero).
///
/// - `Fuzz`: coverage-guided fuzzing (libfuzzer / AFL / honggfuzz).
/// - `Kani`: bounded model checking via kani.
/// - `None`: no bolero mode, so revert to the proptest backend.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VcheckBoleroMode {
    Fuzz,
    Kani,
}

/// Extract the string value of a `key = "..."` pair from a `#[vcheck(...)]`
/// attribute's token stream. Returns `None` for bare `#[vcheck]`, a name-value
/// `#[vcheck = ...]`, a missing key, or a non-string-literal RHS. A token-tree
/// scan (rather than the `Subst` parser) so a string RHS isn't silently
/// swallowed into the const-param map — same rationale as
/// `parse_marker_miri_mode`.
pub fn marker_string_value(attr: &Attribute, key: &str) -> Option<String> {
    let tokens = match &attr.meta {
        Meta::List(list) => list.tokens.clone(),
        _ => return None,
    };
    let mut iter = tokens.into_iter().peekable();
    while let Some(tt) = iter.next() {
        if let proc_macro2::TokenTree::Ident(id) = &tt {
            if id == key {
                if let Some(proc_macro2::TokenTree::Punct(p)) = iter.peek() {
                    if p.as_char() == '=' {
                        let _ = iter.next();
                        if let Some(proc_macro2::TokenTree::Literal(lit)) = iter.next() {
                            // `Literal::to_string` includes the surrounding
                            // quotes for string literals.
                            return Some(lit.to_string().trim_matches('"').to_string());
                        }
                    }
                }
            }
        }
    }
    None
}

/// Resolve the vcheck backend for a single `#[vcheck(...)]` attribute.
///
/// Recognises two spellings, with `mode` taking precedence over `backend`:
///
/// - `mode = "proptest" | "fuzz" | "kani"` -- the user-facing selector.
///   `proptest` -> `Proptest`; `fuzz` / `kani` -> `Bolero`.
/// - `backend = "bolero" | "proptest"` -- the original spelling, kept for
///   back-compat. `bolero` -> `Bolero`.
///
/// Any other form (bare `#[vcheck]`, a missing/unknown value) falls back to
/// `Proptest`, matching the `miri` key's lenient handling.
pub fn parse_marker_backend(attr: &Attribute) -> VcheckBackend {
    // `mode` wins if present.
    if let Some(m) = marker_string_value(attr, "mode") {
        return match m.as_str() {
            "fuzz" | "kani" => VcheckBackend::Bolero,
            // "proptest" and any unknown value -> the default backend.
            _ => VcheckBackend::Proptest,
        };
    }
    match marker_string_value(attr, "backend").as_deref() {
        Some("bolero") => VcheckBackend::Bolero,
        // "proptest" and any unknown value -> the default backend.
        _ => VcheckBackend::Proptest,
    }
}

/// Resolve the bolero mode for a single `#[vcheck(...)]` attribute. Returns
/// `None` when the resolved backend is proptest.
///
/// - `mode = "fuzz"` -> `Fuzz`; `mode = "kani"` -> `Kani`.
/// - No `mode`, but `backend = "bolero"` -> `Fuzz` (the general bolero default,
///   preserving the pre-`mode` behavior for the `backend` spelling).
pub fn parse_marker_bolero_mode(attr: &Attribute) -> Option<VcheckBoleroMode> {
    if let Some(m) = marker_string_value(attr, "mode") {
        return match m.as_str() {
            "fuzz" => Some(VcheckBoleroMode::Fuzz),
            "kani" => Some(VcheckBoleroMode::Kani),
            _ => None,
        };
    }
    match marker_string_value(attr, "backend").as_deref() {
        Some("bolero") => Some(VcheckBoleroMode::Fuzz),
        _ => None,
    }
}

/// Return the backend for a `#[vcheck(...)]` attribute on a free fn (`Item`).
/// Returns the default (`Proptest`) if no `#[vcheck]` attribute is present.
pub fn item_vcheck_backend(item: &Item) -> VcheckBackend {
    if let Some(attrs) = item_attrs(item) {
        if let Some(backend) = backend_from_doc_sentinel(attrs) {
            return backend;
        }
    }
    item_attrs(item)
        .and_then(|attrs| attrs.iter().find(|a| attr_is(a, "vcheck")))
        .map(parse_marker_backend)
        .unwrap_or_default()
}

/// Return the backend for a `#[vcheck(...)]` attribute on an impl method.
/// See [`item_vcheck_backend`] for the sentinel-vs-attribute resolution order.
pub fn impl_fn_vcheck_backend(f: &verus_syn::ImplItemFn) -> VcheckBackend {
    if let Some(backend) = backend_from_doc_sentinel(&f.attrs) {
        return backend;
    }
    f.attrs
        .iter()
        .find(|a| attr_is(a, "vcheck"))
        .map(parse_marker_backend)
        .unwrap_or_default()
}

/// Return the bolero mode for a `#[vcheck(...)]` attribute on a free fn (`Item`).
/// Returns `None` when there is no `#[vcheck]` or the backend is proptest.
/// Resolution order mirrors [`item_vcheck_backend`]: doc sentinel first, then the
/// original `#[vcheck(...)]` attribute.
pub fn item_vcheck_bolero_mode(item: &Item) -> Option<VcheckBoleroMode> {
    if let Some(attrs) = item_attrs(item) {
        if let Some(mode) = bolero_mode_from_doc_sentinel(attrs) {
            return Some(mode);
        }
    }
    item_attrs(item)
        .and_then(|attrs| attrs.iter().find(|a| attr_is(a, "vcheck")))
        .and_then(parse_marker_bolero_mode)
}

/// Return the bolero mode for a `#[vcheck(...)]` attribute on an impl method.
/// See [`item_vcheck_bolero_mode`] for the sentinel-vs-attribute resolution order.
pub fn impl_fn_vcheck_bolero_mode(f: &verus_syn::ImplItemFn) -> Option<VcheckBoleroMode> {
    if let Some(mode) = bolero_mode_from_doc_sentinel(&f.attrs) {
        return Some(mode);
    }
    f.attrs
        .iter()
        .find(|a| attr_is(a, "vcheck"))
        .and_then(parse_marker_bolero_mode)
}


/// Stamp a `#[doc = "verus_spec_check::backend = <name>"]` sentinel on the item when
/// its `#[vcheck(...)]` selected a non-default backend. No-op when no `#[vcheck]`
/// attribute is present or the backend is the default `Proptest`.
pub fn stamp_backend_sentinel_item(item: &mut Item) {
    let backend = item_vcheck_backend(item);
    stamp_backend_sentinel_on_attrs(item_attrs_mut(item), backend);
}

/// Same as [`stamp_backend_sentinel_item`] but for impl-fn items.
pub fn stamp_backend_sentinel_impl_fn(f: &mut verus_syn::ImplItemFn) {
    let backend = impl_fn_vcheck_backend(f);
    stamp_backend_sentinel_on_attrs(Some(&mut f.attrs), backend);
}

/// Push the backend doc sentinel onto the given attrs slot. No-op for the
/// default `Proptest` (which carries no information that needs to survive a
/// strip) and for items without an attribute slot.
pub fn stamp_backend_sentinel_on_attrs(attrs: Option<&mut Vec<Attribute>>, backend: VcheckBackend) {
    let attrs = match attrs {
        Some(a) => a,
        None => return,
    };
    let token = match backend {
        VcheckBackend::Bolero => "bolero",
        // Proptest is the engine default; no need to materialize.
        VcheckBackend::Proptest => return,
    };
    let doc_value = format!("{BACKEND_DOC_PREFIX}{token}");
    let attr: Attribute = verus_syn::parse_quote! { #[doc = #doc_value] };
    attrs.push(attr);
}

/// Recover the backend from a doc-comment sentinel attribute. Returns `None`
/// when no sentinel is present (callers fall back to scanning the original
/// `#[vcheck(...)]` attribute, if any).
pub fn backend_from_doc_sentinel(attrs: &[Attribute]) -> Option<VcheckBackend> {
    for a in attrs {
        let mnv = match &a.meta {
            Meta::NameValue(mnv) => mnv,
            _ => continue,
        };
        if !mnv.path.get_ident().map(|id| id == "doc").unwrap_or(false) {
            continue;
        }
        if let Expr::Lit(lit) = &mnv.value {
            if let verus_syn::Lit::Str(s) = &lit.lit {
                let v = s.value();
                if let Some(rest) = v.strip_prefix(BACKEND_DOC_PREFIX) {
                    return Some(match rest {
                        "bolero" => VcheckBackend::Bolero,
                        _ => VcheckBackend::Proptest,
                    });
                }
            }
        }
    }
    None
}

/// Stamp a `#[doc = "verus_spec_check::bolero::mode = <mode>"]` sentinel on the item
/// when its `#[vcheck(...)]` selected a bolero mode. No-op for the proptest
/// backend (no bolero mode) and for items without an attribute slot.
pub fn stamp_bolero_mode_sentinel_item(item: &mut Item) {
    let mode = item_vcheck_bolero_mode(item);
    stamp_bolero_mode_sentinel_on_attrs(item_attrs_mut(item), mode);
}

/// Same as [`stamp_bolero_mode_sentinel_item`] but for impl-fn items.
pub fn stamp_bolero_mode_sentinel_impl_fn(f: &mut verus_syn::ImplItemFn) {
    let mode = impl_fn_vcheck_bolero_mode(f);
    stamp_bolero_mode_sentinel_on_attrs(Some(&mut f.attrs), mode);
}

/// Push the bolero-mode doc sentinel onto the given attrs slot. No-op for
/// `None` (proptest backend) and for items without an attribute slot.
pub fn stamp_bolero_mode_sentinel_on_attrs(
    attrs: Option<&mut Vec<Attribute>>,
    mode: Option<VcheckBoleroMode>,
) {
    let attrs = match attrs {
        Some(a) => a,
        None => return,
    };
    let token = match mode {
        Some(VcheckBoleroMode::Fuzz) => "fuzz",
        Some(VcheckBoleroMode::Kani) => "kani",
        None => return,
    };
    let doc_value = format!("{BOLERO_MODE_DOC_PREFIX}{token}");
    let attr: Attribute = verus_syn::parse_quote! { #[doc = #doc_value] };
    attrs.push(attr);
}

/// Recover the bolero mode from a doc-comment sentinel attribute. Returns
/// `None` when no sentinel is present.
pub fn bolero_mode_from_doc_sentinel(attrs: &[Attribute]) -> Option<VcheckBoleroMode> {
    for a in attrs {
        let mnv = match &a.meta {
            Meta::NameValue(mnv) => mnv,
            _ => continue,
        };
        if !mnv.path.get_ident().map(|id| id == "doc").unwrap_or(false) {
            continue;
        }
        if let Expr::Lit(lit) = &mnv.value {
            if let verus_syn::Lit::Str(s) = &lit.lit {
                let v = s.value();
                if let Some(rest) = v.strip_prefix(BOLERO_MODE_DOC_PREFIX) {
                    return match rest {
                        "fuzz" => Some(VcheckBoleroMode::Fuzz),
                        "kani" => Some(VcheckBoleroMode::Kani),
                        _ => None,
                    };
                }
            }
        }
    }
    None
}

/// Push the assume-spec-target doc sentinel onto `attrs`. `target_path` is
/// the rendered path the assume_specification names (e.g.
/// `u32::checked_add`, `<[u8]>::binary_search`), whitespace-normalized.
pub fn stamp_assume_spec_target_on_attrs(attrs: &mut Vec<Attribute>, target_path: &str) {
    let doc_value = format!("{ASSUME_SPEC_TARGET_DOC_PREFIX}{target_path}");
    let attr: Attribute = verus_syn::parse_quote! { #[doc = #doc_value] };
    attrs.push(attr);
}

/// Recover the assume-spec target path from a doc-comment sentinel. Returns
/// `None` when no sentinel is present (the fn is not an assume_specification
/// wrapper).
pub fn assume_spec_target_from_doc_sentinel(attrs: &[Attribute]) -> Option<String> {
    for a in attrs {
        let mnv = match &a.meta {
            Meta::NameValue(mnv) => mnv,
            _ => continue,
        };
        if !mnv.path.get_ident().map(|id| id == "doc").unwrap_or(false) {
            continue;
        }
        if let Expr::Lit(lit) = &mnv.value {
            if let verus_syn::Lit::Str(s) = &lit.lit {
                let v = s.value();
                if let Some(rest) = v.strip_prefix(ASSUME_SPEC_TARGET_DOC_PREFIX) {
                    return Some(rest.to_string());
                }
            }
        }
    }
    None
}

pub fn stamp_assume_spec_type_params_on_attrs(attrs: &mut Vec<Attribute>, type_params: &[String]) {
    if type_params.is_empty() {
        return;
    }
    let doc_value = format!(
        "{ASSUME_SPEC_TYPE_PARAMS_DOC_PREFIX}{}",
        type_params.join(",")
    );
    let attr: Attribute = verus_syn::parse_quote! { #[doc = #doc_value] };
    attrs.push(attr);
}

pub fn assume_spec_type_params_from_doc_sentinel(attrs: &[Attribute]) -> Vec<String> {
    for attr in attrs {
        let Meta::NameValue(name_value) = &attr.meta else {
            continue;
        };
        if !name_value
            .path
            .get_ident()
            .map(|ident| ident == "doc")
            .unwrap_or(false)
        {
            continue;
        }
        let Expr::Lit(lit) = &name_value.value else {
            continue;
        };
        let verus_syn::Lit::Str(value) = &lit.lit else {
            continue;
        };
        if let Some(rest) = value
            .value()
            .strip_prefix(ASSUME_SPEC_TYPE_PARAMS_DOC_PREFIX)
        {
            return rest
                .split(',')
                .filter(|param| !param.is_empty())
                .map(str::to_string)
                .collect();
        }
    }
    Vec::new()
}

/// Stamp `#[doc = "verus_spec_check::skip_regular_harness"]` onto the given attrs
/// slot. Used when an item is folded into the engine block solely because
/// of an inline `#[vcheck] assert(...)`; the downstream classify pass reads
/// the sentinel to suppress the regular `vcheck_<fn>` harness while still
/// emitting the inline-assert harness.
pub fn stamp_skip_regular_harness_on_attrs(attrs: Option<&mut Vec<Attribute>>) {
    let attrs = match attrs {
        Some(a) => a,
        None => return,
    };
    let doc_value = SKIP_REGULAR_HARNESS_DOC;
    let attr: Attribute = verus_syn::parse_quote! { #[doc = #doc_value] };
    attrs.push(attr);
}

/// True iff `attrs` contains the skip-regular-harness sentinel stamped by
/// [`stamp_skip_regular_harness_on_attrs`].
pub fn attrs_have_skip_regular_harness_sentinel(attrs: &[Attribute]) -> bool {
    for a in attrs {
        let mnv = match &a.meta {
            Meta::NameValue(mnv) => mnv,
            _ => continue,
        };
        if !mnv.path.get_ident().map(|id| id == "doc").unwrap_or(false) {
            continue;
        }
        if let Expr::Lit(lit) = &mnv.value {
            if let verus_syn::Lit::Str(s) = &lit.lit {
                if s.value() == SKIP_REGULAR_HARNESS_DOC {
                    return true;
                }
            }
        }
    }
    false
}

#[cfg(test)]
mod miri_mode_tests {
    use super::{parse_marker_miri_mode, VcheckMiriMode};
    use verus_syn::parse_quote;

    #[test]
    fn bare_vcheck_is_auto() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck] };
        assert_eq!(parse_marker_miri_mode(&attr), VcheckMiriMode::Auto);
        assert!(!VcheckMiriMode::Auto.should_skip_under_miri());
    }

    #[test]
    fn miri_skip_parses() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(miri = "skip")] };
        assert_eq!(parse_marker_miri_mode(&attr), VcheckMiriMode::Skip);
        assert!(VcheckMiriMode::Skip.should_skip_under_miri());
    }

    #[test]
    fn miri_run_parses() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(miri = "run")] };
        assert_eq!(parse_marker_miri_mode(&attr), VcheckMiriMode::Run);
        assert!(!VcheckMiriMode::Run.should_skip_under_miri());
    }

    #[test]
    fn miri_auto_parses() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(miri = "auto")] };
        assert_eq!(parse_marker_miri_mode(&attr), VcheckMiriMode::Auto);
    }

    #[test]
    fn miri_unknown_value_falls_back_to_auto() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(miri = "banana")] };
        assert_eq!(parse_marker_miri_mode(&attr), VcheckMiriMode::Auto);
    }

    #[test]
    fn miri_among_other_keys() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(N = 4, miri = "skip", T = u32)] };
        assert_eq!(parse_marker_miri_mode(&attr), VcheckMiriMode::Skip);
    }

    #[test]
    fn other_keys_without_miri_yield_auto() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(T = u32, N = 4)] };
        assert_eq!(parse_marker_miri_mode(&attr), VcheckMiriMode::Auto);
    }

    #[test]
    fn sentinel_round_trip_skip() {
        use super::{item_vcheck_miri_mode, stamp_miri_mode_sentinel_item, strip_attr_item};
        let mut item: verus_syn::Item = parse_quote! {
            #[vcheck(miri = "skip")]
            fn dummy() {}
        };
        // Read mode before strip.
        assert_eq!(item_vcheck_miri_mode(&item), VcheckMiriMode::Skip);
        // Stamp sentinel and strip the original `#[vcheck]` attribute. After
        // strip, `item_vcheck_miri_mode` must still report `Skip`.
        stamp_miri_mode_sentinel_item(&mut item);
        strip_attr_item(&mut item, "vcheck");
        assert_eq!(item_vcheck_miri_mode(&item), VcheckMiriMode::Skip);
    }

    #[test]
    fn sentinel_round_trip_auto_emits_nothing() {
        use super::{item_vcheck_miri_mode, stamp_miri_mode_sentinel_item, strip_attr_item};
        let mut item: verus_syn::Item = parse_quote! {
            #[vcheck]
            fn dummy() {}
        };
        assert_eq!(item_vcheck_miri_mode(&item), VcheckMiriMode::Auto);
        // Auto stamps nothing; after strip the item should still resolve
        // to `Auto` (via the fallback path's failure to find `#[vcheck]`).
        stamp_miri_mode_sentinel_item(&mut item);
        strip_attr_item(&mut item, "vcheck");
        assert_eq!(item_vcheck_miri_mode(&item), VcheckMiriMode::Auto);
    }
}

#[cfg(test)]
mod backend_tests {
    use super::{parse_marker_backend, VcheckBackend};
    use verus_syn::parse_quote;

    #[test]
    fn bare_vcheck_is_proptest() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Proptest);
    }

    #[test]
    fn backend_bolero_parses() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(backend = "bolero")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Bolero);
    }

    #[test]
    fn backend_proptest_parses() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(backend = "proptest")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Proptest);
    }

    #[test]
    fn backend_unknown_value_falls_back_to_proptest() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(backend = "banana")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Proptest);
    }

    #[test]
    fn backend_among_other_keys() {
        let attr: verus_syn::Attribute =
            parse_quote! { #[vcheck(miri = "skip", backend = "bolero", N = 4)] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Bolero);
    }

    #[test]
    fn other_keys_without_backend_yield_proptest() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(miri = "run", N = 4)] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Proptest);
    }

    #[test]
    fn sentinel_round_trip_bolero() {
        use super::{item_vcheck_backend, stamp_backend_sentinel_item, strip_attr_item};
        let mut item: verus_syn::Item = parse_quote! {
            #[vcheck(backend = "bolero")]
            fn dummy() {}
        };
        assert_eq!(item_vcheck_backend(&item), VcheckBackend::Bolero);
        // Stamp sentinel and strip the original `#[vcheck]`. The backend must
        // survive the strip via the doc sentinel.
        stamp_backend_sentinel_item(&mut item);
        strip_attr_item(&mut item, "vcheck");
        assert_eq!(item_vcheck_backend(&item), VcheckBackend::Bolero);
    }

    #[test]
    fn sentinel_round_trip_default_emits_nothing() {
        use super::{item_vcheck_backend, stamp_backend_sentinel_item, strip_attr_item};
        let mut item: verus_syn::Item = parse_quote! {
            #[vcheck]
            fn dummy() {}
        };
        assert_eq!(item_vcheck_backend(&item), VcheckBackend::Proptest);
        // Proptest (default) stamps nothing; after strip it still resolves
        // to Proptest via the fallback path.
        stamp_backend_sentinel_item(&mut item);
        strip_attr_item(&mut item, "vcheck");
        assert_eq!(item_vcheck_backend(&item), VcheckBackend::Proptest);
    }
}

#[cfg(test)]
mod assume_spec_target_sentinel_tests {
    use super::{
        assume_spec_target_from_doc_sentinel, assume_spec_type_params_from_doc_sentinel,
        stamp_assume_spec_target_on_attrs, stamp_assume_spec_type_params_on_attrs,
    };
    use verus_syn::parse_quote;

    #[test]
    fn sentinel_round_trip() {
        let mut item: verus_syn::ItemFn = parse_quote! {
            fn __vcheck_assume_checked_add(x: u32, y: u32) -> Option<u32> {
                u32::checked_add(x, y)
            }
        };
        assert_eq!(assume_spec_target_from_doc_sentinel(&item.attrs), None);
        stamp_assume_spec_target_on_attrs(&mut item.attrs, "u32::checked_add");
        assert_eq!(
            assume_spec_target_from_doc_sentinel(&item.attrs).as_deref(),
            Some("u32::checked_add")
        );
    }

    #[test]
    fn qualified_self_path_round_trips_verbatim() {
        let mut attrs: Vec<verus_syn::Attribute> = Vec::new();
        stamp_assume_spec_target_on_attrs(&mut attrs, "<[u8]>::binary_search");
        assert_eq!(
            assume_spec_target_from_doc_sentinel(&attrs).as_deref(),
            Some("<[u8]>::binary_search")
        );
    }

    #[test]
    fn generic_type_params_round_trip() {
        let mut attrs: Vec<verus_syn::Attribute> = Vec::new();
        stamp_assume_spec_type_params_on_attrs(
            &mut attrs,
            &["T".to_string(), "Allocator".to_string()],
        );
        assert_eq!(
            assume_spec_type_params_from_doc_sentinel(&attrs),
            vec!["T".to_string(), "Allocator".to_string()]
        );
    }
}

#[cfg(test)]
mod mode_tests {
    //! The user-facing `#[vcheck(mode = "proptest" | "fuzz" | "kani")]` selector.
    //! `mode` resolves to a backend (`proptest` -> Proptest, `fuzz`/`kani` ->
    //! Bolero) plus a bolero-mode tag (`fuzz`/`kani`), and takes precedence
    //! over the legacy `backend` key. Both spellings round-trip through the
    //! doc sentinels that survive the `#[vcheck]` strip.

    use super::{
        item_vcheck_backend, item_vcheck_bolero_mode, parse_marker_backend, parse_marker_bolero_mode,
        stamp_backend_sentinel_item, stamp_bolero_mode_sentinel_item, strip_attr_item, VcheckBackend,
        VcheckBoleroMode,
    };
    use verus_syn::parse_quote;

    #[test]
    fn mode_proptest_is_proptest_backend_no_bolero_mode() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(mode = "proptest")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Proptest);
        assert_eq!(parse_marker_bolero_mode(&attr), None);
    }

    #[test]
    fn mode_fuzz_is_bolero_backend_fuzz_mode() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(mode = "fuzz")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Bolero);
        assert_eq!(parse_marker_bolero_mode(&attr), Some(VcheckBoleroMode::Fuzz));
    }

    #[test]
    fn mode_kani_is_bolero_backend_kani_mode() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(mode = "kani")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Bolero);
        assert_eq!(parse_marker_bolero_mode(&attr), Some(VcheckBoleroMode::Kani));
    }

    #[test]
    fn mode_unknown_value_falls_back_to_proptest() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(mode = "banana")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Proptest);
        assert_eq!(parse_marker_bolero_mode(&attr), None);
    }

    #[test]
    fn bare_vcheck_has_no_bolero_mode() {
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck] };
        assert_eq!(parse_marker_bolero_mode(&attr), None);
    }

    #[test]
    fn mode_takes_precedence_over_backend() {
        // `mode` wins over a conflicting `backend` key.
        let attr: verus_syn::Attribute =
            parse_quote! { #[vcheck(backend = "proptest", mode = "fuzz")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Bolero);
        assert_eq!(parse_marker_bolero_mode(&attr), Some(VcheckBoleroMode::Fuzz));
    }

    #[test]
    fn legacy_backend_bolero_maps_to_fuzz_mode() {
        // Back-compat: the pre-`mode` spelling implies the general fuzz mode.
        let attr: verus_syn::Attribute = parse_quote! { #[vcheck(backend = "bolero")] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Bolero);
        assert_eq!(parse_marker_bolero_mode(&attr), Some(VcheckBoleroMode::Fuzz));
    }

    #[test]
    fn mode_among_other_keys() {
        let attr: verus_syn::Attribute =
            parse_quote! { #[vcheck(miri = "skip", mode = "kani", N = 4)] };
        assert_eq!(parse_marker_backend(&attr), VcheckBackend::Bolero);
        assert_eq!(parse_marker_bolero_mode(&attr), Some(VcheckBoleroMode::Kani));
    }

    #[test]
    fn sentinel_round_trip_mode_fuzz() {
        let mut item: verus_syn::Item = parse_quote! {
            #[vcheck(mode = "fuzz")]
            fn dummy() {}
        };
        assert_eq!(item_vcheck_backend(&item), VcheckBackend::Bolero);
        assert_eq!(item_vcheck_bolero_mode(&item), Some(VcheckBoleroMode::Fuzz));
        // Stamp both sentinels (as preprocess does) then strip `#[vcheck]`. Both
        // the backend and the bolero mode must survive via the doc sentinels.
        stamp_backend_sentinel_item(&mut item);
        stamp_bolero_mode_sentinel_item(&mut item);
        strip_attr_item(&mut item, "vcheck");
        assert_eq!(item_vcheck_backend(&item), VcheckBackend::Bolero);
        assert_eq!(item_vcheck_bolero_mode(&item), Some(VcheckBoleroMode::Fuzz));
    }

    #[test]
    fn sentinel_round_trip_mode_kani() {
        let mut item: verus_syn::Item = parse_quote! {
            #[vcheck(mode = "kani")]
            fn dummy() {}
        };
        stamp_backend_sentinel_item(&mut item);
        stamp_bolero_mode_sentinel_item(&mut item);
        strip_attr_item(&mut item, "vcheck");
        assert_eq!(item_vcheck_backend(&item), VcheckBackend::Bolero);
        assert_eq!(item_vcheck_bolero_mode(&item), Some(VcheckBoleroMode::Kani));
    }

    #[test]
    fn sentinel_round_trip_proptest_emits_no_bolero_mode() {
        let mut item: verus_syn::Item = parse_quote! {
            #[vcheck(mode = "proptest")]
            fn dummy() {}
        };
        stamp_backend_sentinel_item(&mut item);
        stamp_bolero_mode_sentinel_item(&mut item);
        strip_attr_item(&mut item, "vcheck");
        assert_eq!(item_vcheck_backend(&item), VcheckBackend::Proptest);
        assert_eq!(item_vcheck_bolero_mode(&item), None);
    }
}
