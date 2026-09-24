use super::*;

// ---------------------------------------------------------------------------
// Attribute helpers
// ---------------------------------------------------------------------------

/// Sentinel doc attribute the `#[vcheck]` strip pass leaves behind on impl
/// methods that were originally marked 
pub const VERUS_SPEC_CHECK_HARNESS_SENTINEL: &str = "__verus_spec_check_harness_marker__";

/// Lenient match for our marker attributes, mirroring `collect_attrs`:
/// accepts `#[m]`, `#[contrib::m]`, `#[vstd::contrib::m]`.
pub fn attr_is(attr: &Attribute, name: &str) -> bool {
    let path = attr.path();
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    match &segs[..] {
        [s] => *s == name,
        ["contrib", s] => *s == name,
        ["vstd", "contrib", s] => *s == name,
        _ => false,
    }
}

pub fn item_attrs_mut(item: &mut Item) -> Option<&mut Vec<Attribute>> {
    match item {
        Item::Enum(i) => Some(&mut i.attrs),
        Item::Struct(i) => Some(&mut i.attrs),
        Item::Impl(i) => Some(&mut i.attrs),
        Item::Fn(i) => Some(&mut i.attrs),
        Item::Mod(i) => Some(&mut i.attrs),
        Item::Use(i) => Some(&mut i.attrs),
        Item::Const(i) => Some(&mut i.attrs),
        Item::Static(i) => Some(&mut i.attrs),
        Item::Type(i) => Some(&mut i.attrs),
        Item::Macro(i) => Some(&mut i.attrs),
        Item::ExternCrate(i) => Some(&mut i.attrs),
        Item::ForeignMod(i) => Some(&mut i.attrs),
        Item::Trait(i) => Some(&mut i.attrs),
        Item::TraitAlias(i) => Some(&mut i.attrs),
        Item::Union(i) => Some(&mut i.attrs),
        Item::AssumeSpecification(i) => Some(&mut i.attrs),
        _ => None,
    }
}

pub fn item_attrs(item: &Item) -> Option<&Vec<Attribute>> {
    match item {
        Item::Enum(i) => Some(&i.attrs),
        Item::Struct(i) => Some(&i.attrs),
        Item::Impl(i) => Some(&i.attrs),
        Item::Fn(i) => Some(&i.attrs),
        Item::Mod(i) => Some(&i.attrs),
        Item::Use(i) => Some(&i.attrs),
        Item::Const(i) => Some(&i.attrs),
        Item::Static(i) => Some(&i.attrs),
        Item::Type(i) => Some(&i.attrs),
        Item::Macro(i) => Some(&i.attrs),
        Item::ExternCrate(i) => Some(&i.attrs),
        Item::ForeignMod(i) => Some(&i.attrs),
        Item::Trait(i) => Some(&i.attrs),
        Item::TraitAlias(i) => Some(&i.attrs),
        Item::Union(i) => Some(&i.attrs),
        Item::AssumeSpecification(i) => Some(&i.attrs),
        _ => None,
    }
}

pub fn item_has_attr(item: &Item, name: &str) -> bool {
    item_attrs(item).map_or(false, |attrs| attrs.iter().any(|a| attr_is(a, name)))
}

/// Find the span of an attribute named `name` on `item` (for error reporting).
pub fn item_attr_span(item: &Item, name: &str) -> Option<proc_macro2::Span> {
    item_attrs(item)?
        .iter()
        .find(|a| attr_is(a, name))
        .map(|a| {
            a.path()
                .segments
                .last()
                .map(|s| s.ident.span())
                .unwrap_or_else(|| a.path().span())
        })
}

/// Find the span of an attribute named `name` on an impl-item fn.
pub fn impl_fn_attr_span(f: &verus_syn::ImplItemFn, name: &str) -> Option<proc_macro2::Span> {
    f.attrs.iter().find(|a| attr_is(a, name)).map(|a| {
        a.path()
            .segments
            .last()
            .map(|s| s.ident.span())
            .unwrap_or_else(|| a.path().span())
    })
}

/// Item kinds `#[vcheck_provide]` knows how to fold into the engine block.
/// Returns a static description of the item kind for error messages, or None
/// when the item kind is supported.
pub fn vcheck_provide_unsupported_item_kind(item: &Item) -> Option<&'static str> {
    match item {
        // Supported: types, free fns (spec or exec), inherent impl blocks
        // (generic or not), `assume_specification` items (which the pass
        // synthesizes into an exec wrapper that gets vcheck'd), and trait
        // impl blocks (which the pass pre-rewrites to inherent shape with
        // mangled method names).
        Item::Struct(_) | Item::Enum(_) | Item::Fn(_) | Item::AssumeSpecification(_) => None,
        Item::Impl(_) => None,
        Item::Trait(_) => Some("a trait declaration"),
        Item::TraitAlias(_) => Some("a trait alias"),
        Item::Mod(_) => Some("a module"),
        Item::Use(_) => Some("a `use` declaration"),
        Item::Const(_) => Some("a `const` item"),
        Item::Static(_) => Some("a `static` item"),
        Item::Type(_) => Some("a type alias"),
        Item::Macro(_) => Some("a macro invocation"),
        Item::ExternCrate(_) => Some("an `extern crate` declaration"),
        Item::ForeignMod(_) => Some("an `extern { ... }` block"),
        Item::Union(_) => Some("a union (only structs and enums are supported)"),
        _ => Some("an item of an unsupported kind"),
    }
}

/// True if `f` is a body-less spec fn (i.e. an `uninterp spec fn` or a spec fn
/// declared without a body that the parser flagged with a deprecation warning).
/// The exec_spec engine cannot compile body-less specs into runnable companions,
/// so we surface a tailored error before invoking it.
pub fn is_uninterp_spec_fn(f: &ItemFn) -> bool {
    matches!(f.sig.mode, FnMode::Spec(..) | FnMode::SpecChecked(..))
        && (f.semi_token.is_some() || f.block.stmts.is_empty())
}

pub fn impl_fn_is_uninterp_spec(f: &verus_syn::ImplItemFn) -> bool {
    matches!(f.sig.mode, FnMode::Spec(..) | FnMode::SpecChecked(..))
        && (f.semi_token.is_some() || f.block.stmts.is_empty())
}

/// Lenient match for a macro invocation path: `m!`, `contrib::m!`,
/// `vstd::contrib::m!`.
pub fn macro_path_is(mac: &verus_syn::Macro, name: &str) -> bool {
    let path = &mac.path;
    if path.leading_colon.is_some() {
        return false;
    }
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let segs: Vec<&str> = segs.iter().map(|s| s.as_str()).collect();
    match &segs[..] {
        [s] => *s == name,
        ["contrib", s] => *s == name,
        ["vstd", "contrib", s] => *s == name,
        _ => false,
    }
}

/// If `item` is an `external_vcheck_provide! { ... }` invocation, return the names
/// of the spec fns it provides
pub fn external_provide_names(item: &Item) -> Option<Vec<String>> {
    if let Item::Macro(m) = item {
        if macro_path_is(&m.mac, "external_vcheck_provide") {
            return Some(crate::external_vcheck_provide::provided_names(
                m.mac.tokens.clone(),
            ));
        }
    }
    None
}

pub fn strip_attr_item(item: &mut Item, name: &str) {
    if let Some(attrs) = item_attrs_mut(item) {
        attrs.retain(|a| !attr_is(a, name));
    }
}

pub fn impl_fn_has_attr(f: &verus_syn::ImplItemFn, name: &str) -> bool {
    f.attrs.iter().any(|a| attr_is(a, name))
}

pub fn strip_attr_impl_fn(f: &mut verus_syn::ImplItemFn, name: &str) {
    f.attrs.retain(|a| !attr_is(a, name));
}



/// Replace `#[vcheck]` on an impl method with the sentinel doc attribute. Used
/// in place of `strip_attr_impl_fn(f, "vcheck")` when we want classify to know
/// which methods were originally marked.
pub fn convert_vcheck_to_sentinel_impl_fn(f: &mut verus_syn::ImplItemFn) {
    let was_marked = f.attrs.iter().any(|a| attr_is(a, "vcheck"));
    f.attrs.retain(|a| !attr_is(a, "vcheck"));
    if was_marked {
        let s = VERUS_SPEC_CHECK_HARNESS_SENTINEL;
        let attr: Attribute = verus_syn::parse_quote! { #[doc = #s] };
        f.attrs.push(attr);
    }
}

/// Free-fn counterpart of [`convert_vcheck_to_sentinel_impl_fn`]: replace
/// `#[vcheck]` on a FREE fn with the harness sentinel, so classify can
/// distinguish "was explicitly `#[vcheck]`-marked" from "context item that
/// rode along". Without this trace, a marked fn whose contract clauses
/// were removed (spec ablation, refactoring) silently stopped producing
/// a harness — a green run that tested nothing. Classify now turns that
/// shape into a compile error, which requires knowing the marker was
/// there.
///
/// Non-fn items (impls, structs) keep plain-strip behavior: the impl
/// path stamps its METHODS individually, and a sentinel on the impl
/// item itself would be dead weight.
pub fn convert_vcheck_to_sentinel_item(item: &mut Item) {
    let was_marked = matches!(item, Item::Fn(_))
        && item_attrs(item)
            .map(|attrs| attrs.iter().any(|a| attr_is(a, "vcheck")))
            .unwrap_or(false);
    strip_attr_item(item, "vcheck");
    if was_marked {
        if let Some(attrs) = item_attrs_mut(item) {
            let s = VERUS_SPEC_CHECK_HARNESS_SENTINEL;
            let attr: Attribute = verus_syn::parse_quote! { #[doc = #s] };
            attrs.push(attr);
        }
    }
}

// ---------------------------------------------------------------------------
// Item identity helpers
// ---------------------------------------------------------------------------

pub fn type_def_name(item: &Item) -> Option<Ident> {
    match item {
        Item::Struct(s) => Some(s.ident.clone()),
        Item::Enum(e) => Some(e.ident.clone()),
        _ => None,
    }
}

pub fn free_spec_or_fn_name(item: &Item) -> Option<Ident> {
    if let Item::Fn(f) = item {
        Some(f.sig.ident.clone())
    } else {
        None
    }
}

pub fn inherent_impl_self_name(item: &Item) -> Option<Ident> {
    if let Item::Impl(im) = item {
        if im.trait_.is_some() {
            return None;
        }
        if let Type::Path(tp) = im.self_ty.as_ref() {
            if tp.qself.is_none() && tp.path.segments.len() == 1 {
                return Some(tp.path.segments[0].ident.clone());
            }
        }
    }
    None
}
