use super::*;
// Reference collection (for closure analysis)

/// Collect every single-segment identifier referenced anywhere in an
/// expression, incl spec-fn calls `f(..)`, method calls `.m(..)`, type-ish path
/// segments, struct literals, etc. Over-collection is fine: we only keep the
/// ones that resolve to a sibling type/spec fn.
pub fn collect_idents_in_expr(expr: &Expr, out: &mut HashSet<String>) {
    struct C<'a> {
        out: &'a mut HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr_path(&mut self, p: &'ast ExprPath) {
            for seg in &p.path.segments {
                self.out.insert(seg.ident.to_string());
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
        fn visit_expr_method_call(&mut self, mc: &'ast verus_syn::ExprMethodCall) {
            self.out.insert(mc.method.to_string());
            verus_syn::visit::visit_expr_method_call(self, mc);
        }
    }
    let mut c = C { out };
    c.visit_expr(expr);
}

/// Like `collect_idents_in_expr` but also captures type arguments at each
/// use site. Returns a list of `(name, type_args)` pairs so the generics-
/// aware closure pass can propagate substitutions through the call graph.
pub fn collect_typed_refs_in_expr(expr: &Expr, out: &mut Vec<(String, Vec<Type>)>) {
    struct C<'a> {
        out: &'a mut Vec<(String, Vec<Type>)>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr_path(&mut self, p: &'ast ExprPath) {
            for seg in &p.path.segments {
                let args = path_seg_type_args(&seg.arguments);
                self.out.push((seg.ident.to_string(), args));
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
        fn visit_expr_method_call(&mut self, mc: &'ast verus_syn::ExprMethodCall) {
            let args = mc
                .turbofish
                .as_ref()
                .map(|tf| {
                    tf.args
                        .iter()
                        .filter_map(|a| match a {
                            GenericArgument::Type(t) => Some(t.clone()),
                            _ => None,
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            self.out.push((mc.method.to_string(), args));
            verus_syn::visit::visit_expr_method_call(self, mc);
        }
    }
    let mut c = C { out };
    c.visit_expr(expr);
}

pub fn path_seg_type_args(args: &PathArguments) -> Vec<Type> {
    if let PathArguments::AngleBracketed(ab) = args {
        ab.args
            .iter()
            .filter_map(|a| match a {
                GenericArgument::Type(t) => Some(t.clone()),
                _ => None,
            })
            .collect()
    } else {
        Vec::new()
    }
}

/// Collect identifiers referenced in a type (for transitive type closure):
/// the type name itself and any generic argument type names.
pub fn collect_idents_in_type(ty: &Type, out: &mut HashSet<String>) {
    struct C<'a> {
        out: &'a mut HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_type_path(&mut self, tp: &'ast verus_syn::TypePath) {
            for seg in &tp.path.segments {
                self.out.insert(seg.ident.to_string());
                if let PathArguments::AngleBracketed(ab) = &seg.arguments {
                    for arg in &ab.args {
                        if let verus_syn::GenericArgument::Type(inner) = arg {
                            collect_idents_in_type(inner, self.out);
                        }
                    }
                }
            }
            verus_syn::visit::visit_type_path(self, tp);
        }
    }
    let mut c = C { out };
    c.visit_type(ty);
}

/// Like `collect_idents_in_type` but captures `(name, type_args)` at each
/// type reference. Used by the generics-aware closure pass to propagate
/// substitutions through field types and signatures.
pub fn collect_typed_refs_in_type(ty: &Type, out: &mut Vec<(String, Vec<Type>)>) {
    struct C<'a> {
        out: &'a mut Vec<(String, Vec<Type>)>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_type_path(&mut self, tp: &'ast verus_syn::TypePath) {
            // Only single-segment paths are siblings we can resolve.
            if tp.qself.is_none() && tp.path.leading_colon.is_none() && tp.path.segments.len() == 1
            {
                let seg = &tp.path.segments[0];
                let args = path_seg_type_args(&seg.arguments);
                self.out.push((seg.ident.to_string(), args.clone()));
                for a in &args {
                    collect_typed_refs_in_type(a, self.out);
                }
                return;
            }
            verus_syn::visit::visit_type_path(self, tp);
        }
    }
    let mut c = C { out };
    c.visit_type(ty);
}

/// Collect identifiers referenced by a struct/enum's field types.
pub fn collect_type_field_idents(item: &Item, out: &mut HashSet<String>) {
    match item {
        Item::Struct(s) => {
            for f in &s.fields {
                collect_idents_in_type(&f.ty, out);
            }
        }
        Item::Enum(e) => {
            for v in &e.variants {
                for f in &v.fields {
                    collect_idents_in_type(&f.ty, out);
                }
            }
        }
        _ => {}
    }
}

pub fn collect_type_field_typed_refs(item: &Item, out: &mut Vec<(String, Vec<Type>)>) {
    match item {
        Item::Struct(s) => {
            for f in &s.fields {
                collect_typed_refs_in_type(&f.ty, out);
            }
        }
        Item::Enum(e) => {
            for v in &e.variants {
                for f in &v.fields {
                    collect_typed_refs_in_type(&f.ty, out);
                }
            }
        }
        _ => {}
    }
}

/// Collect identifiers referenced by the spec fns of an inherent impl block
/// (bodies + signature types).
pub fn collect_impl_spec_idents(item: &Item, out: &mut HashSet<String>) {
    if let Item::Impl(im) = item {
        for ii in &im.items {
            if let ImplItem::Fn(f) = ii {
                collect_sig_idents(&f.sig, out);
                if matches!(f.sig.mode, FnMode::Spec(..)) {
                    collect_block_idents(&f.block, out);
                }
            }
        }
    }
}

pub fn collect_impl_spec_typed_refs(item: &Item, out: &mut Vec<(String, Vec<Type>)>) {
    if let Item::Impl(im) = item {
        for ii in &im.items {
            if let ImplItem::Fn(f) = ii {
                collect_sig_typed_refs(&f.sig, out);
                if matches!(f.sig.mode, FnMode::Spec(..)) {
                    collect_block_typed_refs(&f.block, out);
                }
            }
        }
    }
}

/// Collect identifiers referenced by a free fn (body if spec + signature).
pub fn collect_fn_spec_idents(item: &Item, out: &mut HashSet<String>) {
    if let Item::Fn(f) = item {
        collect_sig_idents(&f.sig, out);
        if matches!(f.sig.mode, FnMode::Spec(..)) {
            collect_block_idents(&f.block, out);
        }
    }
}

pub fn collect_fn_spec_typed_refs(item: &Item, out: &mut Vec<(String, Vec<Type>)>) {
    if let Item::Fn(f) = item {
        collect_sig_typed_refs(&f.sig, out);
        if matches!(f.sig.mode, FnMode::Spec(..)) {
            collect_block_typed_refs(&f.block, out);
        }
    }
}

pub fn collect_sig_idents(sig: &verus_syn::Signature, out: &mut HashSet<String>) {
    for input in &sig.inputs {
        if let verus_syn::FnArgKind::Typed(pt) = &input.kind {
            collect_idents_in_type(&pt.ty, out);
        }
    }
    if let verus_syn::ReturnType::Type(_, _, _, ty) = &sig.output {
        collect_idents_in_type(ty, out);
    }
}

pub fn collect_sig_typed_refs(sig: &verus_syn::Signature, out: &mut Vec<(String, Vec<Type>)>) {
    for input in &sig.inputs {
        if let verus_syn::FnArgKind::Typed(pt) = &input.kind {
            collect_typed_refs_in_type(&pt.ty, out);
        }
    }
    if let verus_syn::ReturnType::Type(_, _, _, ty) = &sig.output {
        collect_typed_refs_in_type(ty, out);
    }
}

pub fn collect_block_idents(block: &verus_syn::Block, out: &mut HashSet<String>) {
    struct C<'a> {
        out: &'a mut HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr(&mut self, e: &'ast Expr) {
            collect_idents_in_expr(e, self.out);
            verus_syn::visit::visit_expr(self, e);
        }
        fn visit_type(&mut self, t: &'ast Type) {
            collect_idents_in_type(t, self.out);
        }
    }
    let mut c = C { out };
    c.visit_block(block);
}

pub fn collect_block_typed_refs(block: &verus_syn::Block, out: &mut Vec<(String, Vec<Type>)>) {
    struct C<'a> {
        out: &'a mut Vec<(String, Vec<Type>)>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr(&mut self, e: &'ast Expr) {
            collect_typed_refs_in_expr(e, self.out);
            verus_syn::visit::visit_expr(self, e);
        }
        fn visit_type(&mut self, t: &'ast Type) {
            collect_typed_refs_in_type(t, self.out);
        }
    }
    let mut c = C { out };
    c.visit_block(block);
}

/// Seed identifiers from a `#[vcheck]` exec fn's contract (requires/ensures).
pub fn collect_contract_idents(sig: &verus_syn::Signature, out: &mut HashSet<String>) {
    if let Some(req) = &sig.spec.requires {
        for e in req.exprs.exprs.iter() {
            collect_idents_in_expr(e, out);
        }
    }
    if let Some(ens) = &sig.spec.ensures {
        for e in ens.exprs.exprs.iter() {
            collect_idents_in_expr(e, out);
        }
    }
    // Also the signature's own parameter/return types (e.g. `&User`).
    collect_sig_idents(sig, out);
}

pub fn collect_contract_typed_refs(sig: &verus_syn::Signature, out: &mut Vec<(String, Vec<Type>)>) {
    if let Some(req) = &sig.spec.requires {
        for e in req.exprs.exprs.iter() {
            collect_typed_refs_in_expr(e, out);
        }
    }
    if let Some(ens) = &sig.spec.ensures {
        for e in ens.exprs.exprs.iter() {
            collect_typed_refs_in_expr(e, out);
        }
    }
    collect_sig_typed_refs(sig, out);
}

// Step 1: tier-aware diagnostic for unresolved external spec fns

/// Collect names of *free function calls* `f(..)` appearing in a `#[vcheck]`
/// contract. These are the only references whose resolution this pass is
/// responsible for: a free spec-fn call lowers to `exec_f(..)` in the harness,
/// so if `f` is defined in another file/crate it has no in-block companion and
/// nothing resolves it across files (unlike method calls on user types, which
/// resolve through the `ToExecModel`/`VcheckSpecCompanion` traits at test time).
///
/// We deliberately ignore method calls (`x.m(..)`) — they go through traits —
/// and constructor-shaped calls (`Some(..)`, `Ok(..)`, `Permission::Read`),
/// which are paths into known types, not spec fns. The lowercase-initial
/// heuristic on a single-segment path name distinguishes a spec fn `is_small`
/// from an enum/tuple-struct constructor `Some`/`Pair`.
pub fn collect_free_call_names(sig: &verus_syn::Signature, out: &mut HashSet<String>) {
    struct C<'a> {
        out: &'a mut HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for C<'a> {
        fn visit_expr_call(&mut self, call: &'ast verus_syn::ExprCall) {
            if let Expr::Path(ExprPath {
                path, qself: None, ..
            }) = call.func.as_ref()
            {
                if path.leading_colon.is_none() && path.segments.len() == 1 {
                    let seg = &path.segments[0];
                    // Accept both bare calls (`f(x)`) and turbofish calls
                    // (`obeys_cmp::<u32>()` — the guard-predicate shape on
                    // monomorphized container specs). The contract rewriter
                    // strips the turbofish when renaming to the (always
                    // monomorphic) exec companion.
                    if matches!(
                        seg.arguments,
                        PathArguments::None | PathArguments::AngleBracketed(_)
                    ) {
                        let name = seg.ident.to_string();
                        if name.starts_with(|c: char| c.is_lowercase() || c == '_') {
                            self.out.insert(name);
                        }
                    }
                }
            }
            verus_syn::visit::visit_expr_call(self, call);
        }
    }
    let mut c = C { out };
    if let Some(req) = &sig.spec.requires {
        for e in req.exprs.exprs.iter() {
            c.visit_expr(e);
        }
    }
    if let Some(ens) = &sig.spec.ensures {
        for e in ens.exprs.exprs.iter() {
            c.visit_expr(e);
        }
    }
}

/// Walk a `use` tree and record, for every leaf identifier, the dotted path
/// that leads to it.
pub fn record_use_tree(tree: &UseTree, prefix: &str, out: &mut HashMap<String, String>) {
    match tree {
        UseTree::Path(p) => {
            let next = if prefix.is_empty() {
                p.ident.to_string()
            } else {
                format!("{}::{}", prefix, p.ident)
            };
            record_use_tree(&p.tree, &next, out);
        }
        UseTree::Name(n) => {
            let full = if prefix.is_empty() {
                n.ident.to_string()
            } else {
                format!("{}::{}", prefix, n.ident)
            };
            out.insert(n.ident.to_string(), full);
        }
        UseTree::Rename(r) => {
            let full = if prefix.is_empty() {
                r.ident.to_string()
            } else {
                format!("{}::{}", prefix, r.ident)
            };
            // The contract refers to the renamed name; the definition lives at
            // the original path.
            out.insert(r.rename.to_string(), full);
        }
        UseTree::Glob(_) => {
            // `use a::b::*;`
            if !prefix.is_empty() {
                out.insert(format!("{}::*", prefix), format!("{}::*", prefix));
            }
        }
        UseTree::Group(g) => {
            for item in &g.items {
                record_use_tree(item, prefix, out);
            }
        }
    }
}

/// Build the name->path index from all sibling `use` items in the block.
pub fn build_use_index(items: &[Item]) -> HashMap<String, String> {
    let mut out = HashMap::new();
    for item in items {
        if let Item::Use(u) = item {
            record_use_tree(&u.tree, "", &mut out);
        }
    }
    out
}

/// Type / projection names the harness emitter handles NATIVELY through the
/// linear-resource path: `Tracked<&PointsTo<V>>` params
/// become sampled memory models + guard materialization, and their view
/// projections (`is_init` / `is_uninit` / `value` / `pptr`) are rewritten or
/// discharged by the clause pre-pass. 
pub fn is_resource_native_ident(name: &str) -> bool {
    matches!(
        name,
        // Permission / handle types.
        "PPtr" | "PointsTo" | "MemContents" | "Tracked"
        // View projections consumed by the clause pre-pass. 
        | "is_init" | "is_uninit" | "value" | "ptr" | "pptr" | "addr"
    )
}

/// Spec-carrier types the exec_spec rewriter routes to runtime exec models
/// (`ExecMultiset`, `HashMap`/`HashSet` shims, `Vec` for `Seq`, ...). Their
/// *definitions* must never be folded into an engine block — folding would
/// monomorphize the crate-visible type in place and shadow the runtime
/// routing. (Matters when a `#[vcheck]`/`#[vcheck_axiom]` contract references the
/// carrier from the same file that defines it, e.g. vstd's multiset.rs.)
pub fn is_routed_spec_carrier(name: &str) -> bool {
    matches!(name, "Seq" | "Set" | "Map" | "Multiset")
}

/// Free spec-fn-like names that are built into the engine / Verus prelude and
/// therefore always resolvable without a sibling definition or `#[vcheck_provide]`.
/// These must not be flagged as unresolved external specs.
pub fn is_builtin_free_spec_fn(name: &str) -> bool {
    matches!(
        name,
        "arbitrary" | "spec_affirm" | "old"
        // Verus arithmetic builtins (`add(a, b)`, `sub(a, b)`, `mul(a, b)`).
        // The engine lowers these to wrapping-arithmetic at call sites
        // inside `exec_spec::compile_expr`, so they shouldn't fire the
        // unresolved-spec-fn diagnostic.
        | "add" | "sub" | "mul"
        // `call_ensures/requires(f, args, ret)` is Verus's spec-side
        // "function f produces ret when called with args" relation.
        | "call_ensures"
        | "call_requires"
        // `cloned::<T>(a, b)`
        | "cloned"
    )
}

/// Infer the most plausible fully-qualified path for an unresolved free spec
/// fn `name`, using the sibling `use` index. Falls back to any glob-imported
/// module, then to the bare name.
pub fn infer_path_for(name: &str, use_index: &HashMap<String, String>) -> String {
    if let Some(p) = use_index.get(name) {
        return p.clone();
    }
    // Glob fallback: if exactly one `a::b::*` is in scope, suggest `a::b::name`.
    let globs: Vec<&String> = use_index.keys().filter(|k| k.ends_with("::*")).collect();
    if globs.len() == 1 {
        let base = globs[0].trim_end_matches("::*");
        return format!("{}::{}", base, name);
    }
    name.to_string()
}

/// Construct the tier-aware diagnostic message for an unresolved free spec fn.
pub fn unresolved_spec_fn_message(name: &str, inferred_path: &str) -> String {
    let path_is_known = inferred_path != name;
    let location = if path_is_known {
        format!("`{}` (resolved from a `use` in this file)", inferred_path)
    } else {
        format!("`{}`", name)
    };
    format!(
        "verus_spec_check: the spec function {loc} is used in a `#[vcheck]` contract but is \
defined outside this `verus!` block, so no exec companion can be generated for it.\n\
\n\
Resolve it at the first applicable tier:\n\
  1. If it is a container method (Seq/Map/Set/Multiset/Option), rewrite the \
contract to use the method form so the engine compiles it directly.\n\
  2. If you own its definition, add `#[vcheck_provide]` to it (and the spec fns it \
calls) at its definition site so a companion is generated and resolved by path.\n\
  3. Otherwise, supply a trusted exec stub next to your `#[vcheck]` fn:\n\
       external_vcheck_provide! {{ fn {path}(/* args */) -> /* ret */ {{ /* exec body */ }} }}\n\
\n\
(Method calls on `#[vcheck_provide]`'d types resolve across files automatically; \
only free spec-fn calls need one of the tiers above.)",
        loc = location,
        path = inferred_path,
    )
}
