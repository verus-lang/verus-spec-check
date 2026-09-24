use super::*;

// ---------------------------------------------------------------------------
// Generics / instantiation
// ---------------------------------------------------------------------------

/// A substitution map carrying both type-param and const-param bindings the
/// user supplied at a `#[vcheck(...)]` callsite. Type bindings (e.g.
/// `#[vcheck(T = u64)]`) live in `map`; const-generic bindings (e.g.
/// `#[vcheck(N = 4)]`) live in `consts`. The two maps are kept parallel rather
/// than merged because their substitution semantics differ — type-params
/// substitute inside `Type` nodes (visit_type_mut), const-params substitute
/// inside expression positions of `[T; N]` arrays and turbofish const args
/// (visit_expr_mut + a `Type::Array` case).
#[derive(Clone, Default, Debug)]
pub struct Subst {
    pub map: HashMap<String, Type>,
    pub consts: HashMap<String, Expr>,
}

impl Subst {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty() && self.consts.is_empty()
    }

    /// Equality on textual representation of the bound types and const
    /// expressions — robust enough for the conflict-detection use case.
    pub fn agrees_with(&self, other: &Subst) -> bool {
        if self.map.len() != other.map.len() {
            return false;
        }
        if self.consts.len() != other.consts.len() {
            return false;
        }
        for (k, v) in &self.map {
            match other.map.get(k) {
                Some(v2) if quote!(#v).to_string() == quote!(#v2).to_string() => {}
                _ => return false,
            }
        }
        for (k, v) in &self.consts {
            match other.consts.get(k) {
                Some(v2) if quote!(#v).to_string() == quote!(#v2).to_string() => {}
                _ => return false,
            }
        }
        true
    }

    /// Pretty-print as `K = T, N = 4` for diagnostics.
    pub fn render(&self) -> String {
        let mut keys: Vec<(&String, String)> = self
            .map
            .iter()
            .map(|(k, v)| (k, format!("{}", quote!(#v))))
            .chain(
                self.consts
                    .iter()
                    .map(|(k, v)| (k, format!("{}", quote!(#v)))),
            )
            .collect();
        keys.sort_by(|a, b| a.0.cmp(b.0));
        keys.iter()
            .map(|(k, v)| format!("{} = {}", k, v))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// Parse the body of a `#[vcheck(K = T, V = U)]` (or `#[vcheck_provide(...)]`)
/// attribute into a `Subst`.
///
/// Each pair's RHS is first attempted as a `Type` (for type-param bindings),
/// and on parse failure as an `Expr` (for const-param bindings like
/// `#[vcheck(N = 4)]`). The resolution into the type vs. const map is delayed
/// to the substitution step, where we look at the surrounding item's
/// generics to decide which slot a given key goes into. This keeps parsing
/// liberal so a malformed entry doesn't kill the whole `#[vcheck(...)]`. Returns
/// `None` if `attr` is the bare `#[vcheck]` form (no parens).
pub fn parse_marker_subst(attr: &Attribute) -> Option<Subst> {
    let tokens = match &attr.meta {
        Meta::Path(_) => return None,
        Meta::List(list) => list.tokens.clone(),
        Meta::NameValue(_) => return None,
    };
    use verus_syn::parse::Parser;
    use verus_syn::punctuated::Punctuated;
    use verus_syn::Token;

    /// A single `K = <Type-or-Expr>` pair. `value` carries the RHS as raw
    /// tokens so we can speculatively re-parse it as a `Type` first and an
    /// `Expr` second; this avoids the order-dependent failure mode where a
    /// `Type` parse consumes input even when it's actually an `Expr`.
    struct Pair {
        key: Ident,
        _eq: Token![=],
        value: TokenStream2,
    }
    impl verus_syn::parse::Parse for Pair {
        fn parse(input: verus_syn::parse::ParseStream) -> verus_syn::parse::Result<Self> {
            let key: Ident = input.parse()?;
            let _eq: Token![=] = input.parse()?;
            // Greedily collect tokens until a comma at the current
            // bracket-depth. This mirrors how attribute meta args are
            // typically tokenized and lets us delay the Type-vs-Expr choice.
            let value: TokenStream2 = input.step(|cursor| {
                let mut acc = TokenStream2::new();
                let mut cur = *cursor;
                while let Some((tt, next)) = cur.token_tree() {
                    if let proc_macro2::TokenTree::Punct(p) = &tt {
                        if p.as_char() == ',' {
                            return Ok((acc, cur));
                        }
                    }
                    acc.extend(std::iter::once(tt));
                    cur = next;
                }
                Ok((acc, cur))
            })?;
            Ok(Pair { key, _eq, value })
        }
    }

    let parser =
        |s: verus_syn::parse::ParseStream| Punctuated::<Pair, Token![,]>::parse_terminated(s);
    let pairs = match parser.parse2(tokens) {
        Ok(p) => p,
        Err(_) => return Some(Subst::default()),
    };
    let mut map = HashMap::new();
    let mut consts = HashMap::new();
    for p in pairs {
        // Try Type first, then Expr. Both are valid surface forms; prefer
        // the Type interpretation when both succeed because the common case
        // is `T = u32`. The const-param path triggers only for entries like
        // `N = 4`, which fail the Type parse since a bare integer literal
        // isn't a Type.
        let v_ts = p.value.clone();
        if let Ok(ty) = verus_syn::parse2::<Type>(v_ts.clone()) {
            map.insert(p.key.to_string(), ty);
        } else if let Ok(e) = verus_syn::parse2::<Expr>(v_ts) {
            consts.insert(p.key.to_string(), e);
        }
        // Silently drop unparseable RHS — caller's bad form, downstream
        // errors will fire when the user tries to use the key.
    }
    Some(Subst { map, consts })
}

/// Find a `#[vcheck]`-family marker on an item and return its parsed subst.
pub fn item_marker_subst(item: &Item, name: &str) -> Option<Subst> {
    item_attrs(item)?
        .iter()
        .find(|a| attr_is(a, name))
        .and_then(parse_marker_subst)
}

pub fn impl_fn_marker_subst(f: &verus_syn::ImplItemFn, name: &str) -> Option<Subst> {
    f.attrs
        .iter()
        .find(|a| attr_is(a, name))
        .and_then(parse_marker_subst)
}

/// Returns the names of an item's type parameters (e.g. `["V"]` for
/// `struct Stack<V> { ... }`). Empty for non-generic items.
pub fn item_type_params(item: &Item) -> Vec<Ident> {
    let generics: Option<&Generics> = match item {
        Item::Struct(s) => Some(&s.generics),
        Item::Enum(e) => Some(&e.generics),
        Item::Impl(im) => Some(&im.generics),
        Item::Fn(f) => Some(&f.sig.generics),
        _ => None,
    };
    generics
        .map(|g| {
            g.params
                .iter()
                .filter_map(|p| match p {
                    GenericParam::Type(tp) => Some(tp.ident.clone()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Returns the names of an item's const-generic parameters (e.g. `["N"]` for
/// `fn foo<const N: usize>() { ... }`). Empty for non-generic items.
pub fn item_const_params(item: &Item) -> Vec<Ident> {
    let generics: Option<&Generics> = match item {
        Item::Struct(s) => Some(&s.generics),
        Item::Enum(e) => Some(&e.generics),
        Item::Impl(im) => Some(&im.generics),
        Item::Fn(f) => Some(&f.sig.generics),
        _ => None,
    };
    generics
        .map(|g| {
            g.params
                .iter()
                .filter_map(|p| match p {
                    GenericParam::Const(cp) => Some(cp.ident.clone()),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Best-effort display name for diagnostics: type name for struct/enum/impl,
/// fn name for fns, fallback to "item" otherwise.
pub fn item_display_name(item: &Item) -> String {
    match item {
        Item::Struct(s) => s.ident.to_string(),
        Item::Enum(e) => e.ident.to_string(),
        Item::Fn(f) => f.sig.ident.to_string(),
        Item::Impl(im) => {
            if let Type::Path(tp) = im.self_ty.as_ref() {
                if let Some(seg) = tp.path.segments.last() {
                    return format!("impl {}", seg.ident);
                }
            }
            "impl".into()
        }
        _ => "item".into(),
    }
}

/// Strip the type-args from any in-block reference to a monomorphized sibling.
/// After substitution, `struct Cell<V>` becomes `struct Cell` (no params), so
/// references like `Cell<u64>` in fields, impl Self types, and turbofish
/// uses must lose their `<u64>` to compile. Walks types and expr-paths;
/// matches by single-segment ident name only.
pub fn strip_type_args_for_names(item: &mut Item, names: &HashSet<String>) {
    if names.is_empty() {
        return;
    }
    struct R<'a> {
        names: &'a HashSet<String>,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_path_mut(&mut self, tp: &mut verus_syn::TypePath) {
            if tp.qself.is_none() && tp.path.segments.len() == 1 {
                let seg = &mut tp.path.segments[0];
                if self.names.contains(&seg.ident.to_string()) {
                    seg.arguments = PathArguments::None;
                }
            }
            verus_syn::visit_mut::visit_type_path_mut(self, tp);
        }
        fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
            for seg in p.path.segments.iter_mut() {
                if self.names.contains(&seg.ident.to_string()) {
                    seg.arguments = PathArguments::None;
                }
            }
            verus_syn::visit_mut::visit_expr_path_mut(self, p);
        }
    }
    R { names }.visit_item_mut(item);
}

/// Apply a substitution to a `Type`. Replaces every single-segment
/// `TypePath` whose ident is a key in `subst.map` with the bound type, and
/// every `Type::Array(_, len)` whose `len` expression is a single-ident path
/// matching a key in `subst.consts` with the bound expression — recursively
/// inside generic args, references, slices, tuples, etc.
pub fn substitute_type(ty: &mut Type, subst: &Subst) {
    if subst.is_empty() {
        return;
    }
    struct R<'a> {
        subst: &'a Subst,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_mut(&mut self, t: &mut Type) {
            // First, pre-empt `Type::Path` whose head ident matches: replace
            // the whole node, since `T<X>` doesn't make sense if `T` is a
            // primitive.
            if let Type::Path(tp) = t {
                if tp.qself.is_none()
                    && tp.path.leading_colon.is_none()
                    && tp.path.segments.len() == 1
                    && matches!(tp.path.segments[0].arguments, PathArguments::None)
                {
                    let name = tp.path.segments[0].ident.to_string();
                    if let Some(replacement) = self.subst.map.get(&name) {
                        *t = replacement.clone();
                        return;
                    }
                }
            }
            // `[T; N]`: recurse into `elem` (handled by visit_type_mut) AND
            // substitute the length expression if it's a single-ident path
            // matching a const-param key.
            if let Type::Array(arr) = t {
                substitute_const_expr(&mut arr.len, self.subst);
            }
            verus_syn::visit_mut::visit_type_mut(self, t);
        }
        fn visit_path_arguments_mut(&mut self, args: &mut PathArguments) {
            // Substitute const generic arguments inside `Foo::<T, N>` when
            // `N` resolves to a const-bound key. We walk the args here
            // because the default visitor would visit `GenericArgument::Const`
            // expressions but our `visit_expr_mut` is currently scoped to
            // const positions only via this path.
            if let PathArguments::AngleBracketed(ab) = args {
                for arg in ab.args.iter_mut() {
                    if let GenericArgument::Const(e) = arg {
                        substitute_const_expr(e, self.subst);
                    }
                }
            }
            verus_syn::visit_mut::visit_path_arguments_mut(self, args);
        }
    }
    R { subst }.visit_type_mut(ty);
}

/// If `e` is a single-segment path expression matching a key in
/// `subst.consts`, replace it with the bound expression. Otherwise no-op.
/// The replacement is whole-expression: a const generic name appears in
/// const position only, so we don't need to recurse into its substructure.
pub fn substitute_const_expr(e: &mut Expr, subst: &Subst) {
    if subst.consts.is_empty() {
        return;
    }
    if let Expr::Path(p) = e {
        if p.qself.is_none()
            && p.path.leading_colon.is_none()
            && p.path.segments.len() == 1
            && matches!(p.path.segments[0].arguments, PathArguments::None)
        {
            let name = p.path.segments[0].ident.to_string();
            if let Some(replacement) = subst.consts.get(&name) {
                *e = replacement.clone();
            }
        }
    }
}

/// Apply a substitution everywhere inside an item: field types, method
/// signatures, return types, generic args inside expression paths in spec fn
/// bodies, etc. After substitution, strip type-params from `generics.params`
/// and `where` clauses so the post-subst item is monomorphic.
pub fn substitute_item(item: &mut Item, subst: &Subst) {
    if subst.is_empty() {
        return;
    }
    struct R<'a> {
        subst: &'a Subst,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_mut(&mut self, t: &mut Type) {
            substitute_type(t, self.subst);
            // Don't recurse — substitute_type already walks the subtree.
        }
        fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
            // Substitute inside generic args of expression paths
            // (e.g. `Vec::<V>::new()`).
            for seg in p.path.segments.iter_mut() {
                if let PathArguments::AngleBracketed(ab) = &mut seg.arguments {
                    for arg in ab.args.iter_mut() {
                        match arg {
                            GenericArgument::Type(t) => {
                                // A bare const-param ident in turbofish
                                // position (`orig::<T, N>`) parses as a
                                // Type — if it matches a const binding,
                                // rewrite the whole argument to Const.
                                let const_replacement = match &t {
                                    Type::Path(tp)
                                        if tp.qself.is_none()
                                            && tp.path.segments.len() == 1
                                            && matches!(
                                                tp.path.segments[0].arguments,
                                                PathArguments::None
                                            ) =>
                                    {
                                        self.subst
                                            .consts
                                            .get(&tp.path.segments[0].ident.to_string())
                                            .cloned()
                                    }
                                    _ => None,
                                };
                                if let Some(e) = const_replacement {
                                    *arg = GenericArgument::Const(e);
                                } else {
                                    substitute_type(t, self.subst);
                                }
                            }
                            GenericArgument::Const(e) => {
                                substitute_const_expr(e, self.subst);
                            }
                            _ => {}
                        }
                    }
                }
            }
            verus_syn::visit_mut::visit_expr_path_mut(self, p);
        }
    }
    R { subst }.visit_item_mut(item);
    strip_substituted_generics(item, subst);
}

/// Remove substituted type-params from an item's generics list and prune any
/// `where` clauses that reference only substituted params. Conservative:
/// leaves untouched anything we don't fully understand.
pub fn strip_substituted_generics(item: &mut Item, subst: &Subst) {
    let generics: Option<&mut Generics> = match item {
        Item::Struct(s) => Some(&mut s.generics),
        Item::Enum(e) => Some(&mut e.generics),
        Item::Impl(im) => Some(&mut im.generics),
        Item::Fn(f) => Some(&mut f.sig.generics),
        _ => None,
    };
    if let Some(g) = generics {
        // Remove substituted type AND const params.
        let keep = |p: &GenericParam| -> bool {
            match p {
                GenericParam::Type(tp) => !subst.map.contains_key(&tp.ident.to_string()),
                GenericParam::Const(cp) => !subst.consts.contains_key(&cp.ident.to_string()),
                _ => true,
            }
        };
        let new_params: verus_syn::punctuated::Punctuated<_, _> =
            g.params.iter().filter(|p| keep(p)).cloned().collect();
        g.params = new_params;
        if g.params.is_empty() {
            g.lt_token = None;
            g.gt_token = None;
        }
        // Drop the whole where-clause if all bounded types have been
        // substituted away. (Attempting to selectively keep bounds whose
        // types reference unsubstituted params is fragile; rustc will catch
        // any leftover bound that no longer makes sense.)
        if let Some(wc) = &mut g.where_clause {
            let preds: verus_syn::punctuated::Punctuated<_, _> = wc
                .predicates
                .iter()
                .filter(|pred| match pred {
                    verus_syn::WherePredicate::Type(pt) => {
                        !type_is_fully_substituted(&pt.bounded_ty, subst)
                    }
                    _ => true,
                })
                .cloned()
                .collect();
            wc.predicates = preds;
        }
        if g.where_clause
            .as_ref()
            .map_or(false, |wc| wc.predicates.is_empty())
        {
            g.where_clause = None;
        }
    }
    // For impls, also substitute the Self type and trait_ args.
    if let Item::Impl(im) = item {
        substitute_type(&mut im.self_ty, subst);
        if let Some((_, path, _)) = &mut im.trait_ {
            for seg in path.segments.iter_mut() {
                if let PathArguments::AngleBracketed(ab) = &mut seg.arguments {
                    for arg in ab.args.iter_mut() {
                        if let GenericArgument::Type(t) = arg {
                            substitute_type(t, subst);
                        }
                    }
                }
            }
        }
        // And substitute inside each impl-fn's signature/body — covered by
        // the generic visitor above, but be explicit about clauses too.
        for ii in &mut im.items {
            if let ImplItem::Fn(f) = ii {
                substitute_signature(&mut f.sig, subst);
            }
        }
    }
    if let Item::Fn(f) = item {
        substitute_signature(&mut f.sig, subst);
    }
}

pub fn substitute_signature(sig: &mut verus_syn::Signature, subst: &Subst) {
    if subst.is_empty() {
        return;
    }
    // Substitute inside spec.requires / spec.ensures / spec.recommends / etc.
    if let Some(req) = &mut sig.spec.requires {
        for e in req.exprs.exprs.iter_mut() {
            substitute_expr_types(e, subst);
        }
    }
    if let Some(ens) = &mut sig.spec.ensures {
        for e in ens.exprs.exprs.iter_mut() {
            substitute_expr_types(e, subst);
        }
    }
}

pub fn substitute_expr_types(expr: &mut Expr, subst: &Subst) {
    struct R<'a> {
        subst: &'a Subst,
    }
    impl<'a> VisitMut for R<'a> {
        fn visit_type_mut(&mut self, t: &mut Type) {
            substitute_type(t, self.subst);
        }
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            // Substitute const-generic name expressions wherever they appear
            // (e.g. `i < N` in a `requires` clause where `N` was bound to
            // `4` by `#[vcheck(N = 4)]`). Recurse first so substitution happens
            // bottom-up and we don't re-visit the replacement.
            verus_syn::visit_mut::visit_expr_mut(self, e);
            substitute_const_expr(e, self.subst);
        }
    }
    R { subst }.visit_expr_mut(expr);
}

/// True if every `TypePath` head ident in `ty` is a substituted param. Used to
/// decide whether to drop a `where` predicate after substitution.
pub fn type_is_fully_substituted(ty: &Type, subst: &Subst) -> bool {
    if let Type::Path(tp) = ty {
        if tp.qself.is_none() && tp.path.segments.len() == 1 {
            let name = tp.path.segments[0].ident.to_string();
            return subst.map.contains_key(&name);
        }
    }
    false
}

/// Resolve a single `Type` argument under the active substitution, ignoring
/// unbound names (they pass through unchanged).
pub fn resolve_type_under(ty: &Type, subst: &Subst) -> Type {
    let mut copy = ty.clone();
    substitute_type(&mut copy, subst);
    copy
}

/// Suggest a default concrete type for an unbound type parameter, used in
/// the diagnostic that fires when a `#[vcheck]` is missing an instantiation. A
/// best-effort guess based on common bounds; rustc will provide a better
/// error if our guess fails to satisfy a more specific bound.
pub fn suggest_default_type(_param: &Ident, bounds: &[String]) -> Type {
    // Return a token-parseable Type for `u32`, the safe default that
    // satisfies most common numeric / Copy / Eq / Hash / Debug bounds we
    // see in vstd-style spec code.
    let _ = bounds;
    verus_syn::parse_quote!(u32)
}
