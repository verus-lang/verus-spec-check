use super::*;

// ---------------------------------------------------------------------------
// `#[vcheck_view]` / `VcheckConcretize` registry
//
// A `#[vcheck_view]`-marked `uninterp spec fn view(x: &T) -> nat/int` declares
// that `T` is an opaque type with a developer-supplied `VcheckConcretize` impl.
// The engine samples `T` by injecting a sampled `<T as VcheckConcretize>::Sample`
// and evaluates `view(x)` via `<T>::vcheck_realize(x)`. The registry is populated
// per-expansion by scanning the folded block; proc-macro expansion is single-
// threaded per invocation, so a thread-local avoids threading a second set
// through the ~40 `classify_*` call sites.
// ---------------------------------------------------------------------------

/// Concretization recipe supplied by `#[vcheck_view(sample=.., inject=.., realize=..)]`.
/// All fields are stored as source strings and re-parsed at emission (keeps the
/// thread-local free of `Span`-bearing syn nodes). `inject`/`realize` are paths
/// to developer free fns; `sample` is a type. Orphan-rule-safe: no trait impl on
/// a foreign type is required.
#[derive(Clone)]
pub struct ConcretizeInfo {
    /// Sample type the harness generates (e.g. `u32`).
    pub sample: String,
    /// `fn(Sample) -> Opaque` injector. `None` -> default to
    /// `<Opaque as From<Sample>>::from`.
    pub inject: Option<String>,
    /// `fn(&Opaque) -> SpecInt` view realizer. `None` -> default to
    /// `__vcheck_int::from_display` (`Display`-parse), valid for integer-like types.
    pub realize: Option<String>,
}

impl ConcretizeInfo {
    /// The injector expression, given the opaque subject type. Defaults to
    /// `<Subject as ::core::convert::From<Sample>>::from` when unspecified.
    pub fn inject_expr(&self, subject: &Ident) -> Expr {
        match &self.inject {
            Some(s) => parse_concretize_path(s),
            None => {
                let sample = parse_concretize_type(&self.sample);
                verus_syn::parse_quote! {
                    <#subject as ::core::convert::From<#sample>>::from
                }
            }
        }
    }

    /// The realizer expression. Defaults to `__vcheck_int::from_display`.
    fn realize_expr(&self) -> Expr {
        match &self.realize {
            Some(s) => parse_concretize_path(s),
            None => verus_syn::parse_quote! { ::verus_spec_check::__vcheck_int::from_display },
        }
    }
}

thread_local! {
    /// `#[vcheck_view]` view fn name -> opaque subject type name (e.g. `ubig_view` -> `UBig`).
    static VIEW_FNS: std::cell::RefCell<HashMap<String, String>> =
        std::cell::RefCell::new(HashMap::new());
    /// Opaque subject type name -> its concretization recipe.
    static CONCRETIZE_TYPES: std::cell::RefCell<HashMap<String, ConcretizeInfo>> =
        std::cell::RefCell::new(HashMap::new());
}

pub fn reset_concretize_registry() {
    VIEW_FNS.with(|v| v.borrow_mut().clear());
    CONCRETIZE_TYPES.with(|c| c.borrow_mut().clear());
    INT_RETURNING_PROVIDED.with(|s| s.borrow_mut().clear());
}

thread_local! {
    /// Names of `external_vcheck_provide!` twins with `int`/`nat` returns
    /// (exec companions return `SpecInt`). Populated per-expansion by the
    /// classify pass, read by the contract rewriter's SpecInt routing.
    static INT_RETURNING_PROVIDED: std::cell::RefCell<std::collections::HashSet<String>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
}

pub fn register_int_returning_provided(name: String) {
    INT_RETURNING_PROVIDED.with(|s| {
        s.borrow_mut().insert(name);
    });
}

pub fn int_returning_provided_registry() -> std::collections::HashSet<String> {
    INT_RETURNING_PROVIDED.with(|s| s.borrow().clone())
}

pub fn register_view_fn(view_name: String, subject_type: String, info: ConcretizeInfo) {
    VIEW_FNS.with(|v| {
        v.borrow_mut().insert(view_name, subject_type.clone());
    });
    CONCRETIZE_TYPES.with(|c| {
        c.borrow_mut().insert(subject_type, info);
    });
}

pub fn is_view_fn(name: &str) -> bool {
    VIEW_FNS.with(|v| v.borrow().contains_key(name))
}

pub fn is_concretize_type(name: &str) -> bool {
    CONCRETIZE_TYPES.with(|c| c.borrow().contains_key(name))
}

/// Recipe for an opaque subject type, if registered.
pub fn concretize_info(type_name: &str) -> Option<ConcretizeInfo> {
    CONCRETIZE_TYPES.with(|c| c.borrow().get(type_name).cloned())
}

/// The realizer expression for a `#[vcheck_view]` view fn, via its subject type.
pub fn view_realize_expr(view_name: &str) -> Option<Expr> {
    let subject = VIEW_FNS.with(|v| v.borrow().get(view_name).cloned())?;
    concretize_info(&subject).map(|i| i.realize_expr())
}

/// Parse `sample`/`inject`/`realize` tokens as `<T>`, a `Path`, or an `Expr`.
pub fn parse_concretize_type(s: &str) -> Type {
    verus_syn::parse_str::<Type>(s).unwrap_or_else(|_| verus_syn::parse_quote! { () })
}

pub fn parse_concretize_path(s: &str) -> Expr {
    verus_syn::parse_str::<Expr>(s).unwrap_or_else(|_| verus_syn::parse_quote! { compile_error!() })
}

/// True if `attr` is a single-segment attribute named `name` (e.g. `#[vcheck_view]`).
pub fn attr_is_ident(attr: &verus_syn::Attribute, name: &str) -> bool {
    attr.path().segments.len() == 1 && attr.path().segments[0].ident == name
}

/// Extract the opaque subject type of a `#[vcheck_view]` view fn from its first
/// parameter (`view(x: &T) -> ...` -> `"T"`). Peels a single `&`.
pub fn view_fn_subject_type(sig: &verus_syn::Signature) -> Option<String> {
    let first = sig.inputs.iter().next()?;
    let ty: &Type = match &first.kind {
        FnArgKind::Typed(pt) => pt.ty.as_ref(),
        FnArgKind::Receiver(_) => return None,
    };
    let inner: &Type = match ty {
        Type::Reference(r) => r.elem.as_ref(),
        other => other,
    };
    if let Type::Path(tp) = inner {
        if tp.qself.is_none() {
            return tp.path.segments.last().map(|s| s.ident.to_string());
        }
    }
    None
}

/// Parse `#[vcheck_view(sample = u32, inject = ubig_inject, realize = ubig_realize)]`
/// into a `ConcretizeInfo`. Returns `None` if any key is missing.
pub fn parse_vcheck_view_attr(attr: &verus_syn::Attribute) -> Option<ConcretizeInfo> {
    use verus_syn::punctuated::Punctuated;
    use verus_syn::{Expr as SynExpr, ExprAssign, Token};
    let list = match &attr.meta {
        verus_syn::Meta::List(l) => l,
        _ => return None,
    };
    let assigns: Punctuated<SynExpr, Token![,]> =
        list.parse_args_with(Punctuated::parse_terminated).ok()?;
    let (mut sample, mut inject, mut realize) = (None, None, None);
    for a in assigns {
        if let SynExpr::Assign(ExprAssign { left, right, .. }) = a {
            let key = match left.as_ref() {
                SynExpr::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
                _ => None,
            }?;
            // Accept a quoted value (`sample = "Vec<u8>"`) for types/paths that
            // don't parse as bare expressions (generics, `<T as Tr>::f`, ...).
            let val = match right.as_ref() {
                SynExpr::Lit(l) => {
                    if let verus_syn::Lit::Str(s) = &l.lit {
                        s.value()
                    } else {
                        quote! { #right }.to_string().replace(' ', "")
                    }
                }
                _ => quote! { #right }.to_string().replace(' ', ""),
            };
            match key.as_str() {
                "sample" => sample = Some(val),
                "inject" => inject = Some(val),
                "realize" => realize = Some(val),
                _ => {}
            }
        }
    }
    // Only `sample` is required; `inject`/`realize` fall back to
    // `From::from` / `Display`-parse defaults.
    Some(ConcretizeInfo {
        sample: sample?,
        inject,
        realize,
    })
}
