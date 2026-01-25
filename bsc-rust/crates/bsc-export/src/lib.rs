//! JSON export for ISyntax (for backend consumption).
//!
//! This crate provides serialization of the internal syntax (ISyntax) to JSON,
//! suitable for:
//! 1. Differential testing against Haskell BSC
//! 2. Consumption by modified BSC backend
//! 3. Other backend implementations
//!
//! The JSON format closely mirrors the Haskell ISyntax structure to facilitate
//! interoperability and testing.

use bsc_syntax::{
    DefProp, IArg, IConInfo, IDef, IExpr, IInterface, IKind, IMethod, IModule, IPackage, IPragma,
    IProperty, IRule, IRules, IEFace, IStateElement, ITyCon, ITyConInfo, ITySort, ITyVar, IType,
    Id, Qualifier, WireProps, VFieldInfo, ISchedulePragma, Backend, VWireInfo, IAbstractInput,
};
use serde_json::{Map, Value, json};

/// Export options for controlling JSON output.
#[derive(Debug, Clone, Default)]
pub struct ExportOptions {
    /// Include source positions in the output.
    pub include_positions: bool,
    /// Pretty print the JSON output.
    pub pretty: bool,
}

/// Export an `IPackage` to a JSON `Value`.
#[must_use]
pub fn export_package(pkg: &IPackage) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IPackage"));
    obj.insert("name".to_string(), export_id(&pkg.name));
    obj.insert(
        "depends".to_string(),
        Value::Array(pkg.depends.iter().map(|(id, sig)| {
            json!([export_id(id), sig])
        }).collect()),
    );
    obj.insert(
        "pragmas".to_string(),
        Value::Array(pkg.pragmas.iter().map(export_pragma).collect()),
    );
    obj.insert(
        "defs".to_string(),
        Value::Array(pkg.defs.iter().map(export_def).collect()),
    );
    Value::Object(obj)
}

/// Export an `IModule` to a JSON `Value`.
#[must_use]
pub fn export_module(module: &IModule) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IModule"));
    obj.insert("name".to_string(), export_id(&module.name));
    obj.insert("is_wrapped".to_string(), json!(module.is_wrapped));
    obj.insert(
        "pragmas".to_string(),
        Value::Array(module.pragmas.iter().map(export_pragma).collect()),
    );
    obj.insert(
        "local_defs".to_string(),
        Value::Array(module.local_defs.iter().map(export_def).collect()),
    );
    obj.insert("rules".to_string(), export_rules(&module.rules));
    obj.insert(
        "interface".to_string(),
        Value::Array(module.interface.iter().map(export_eface).collect()),
    );
    Value::Object(obj)
}

/// Export `IRules` to a JSON `Value`.
#[must_use]
fn export_rules(rules: &IRules) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IRules"));
    obj.insert(
        "pragmas".to_string(),
        Value::Array(rules.pragmas.iter().map(export_schedule_pragma).collect()),
    );
    obj.insert(
        "rules".to_string(),
        Value::Array(rules.rules.iter().map(export_rule).collect()),
    );
    Value::Object(obj)
}

/// Export `ISchedulePragma` to a JSON `Value`.
#[must_use]
fn export_schedule_pragma(pragma: &ISchedulePragma) -> Value {
    match pragma {
        ISchedulePragma::MutuallyExclusive(ids) => json!({
            "tag": "MutuallyExclusive",
            "ids": ids.iter().map(export_id).collect::<Vec<_>>()
        }),
        ISchedulePragma::ConflictFree(ids) => json!({
            "tag": "ConflictFree",
            "ids": ids.iter().map(export_id).collect::<Vec<_>>()
        }),
        ISchedulePragma::Preempt(a, b) => json!({
            "tag": "Preempt",
            "first": a.iter().map(export_id).collect::<Vec<_>>(),
            "second": b.iter().map(export_id).collect::<Vec<_>>()
        }),
        ISchedulePragma::Before(a, b) => json!({
            "tag": "Before",
            "first": a.iter().map(export_id).collect::<Vec<_>>(),
            "second": b.iter().map(export_id).collect::<Vec<_>>()
        }),
        ISchedulePragma::ExecutionOrder(ids) => json!({
            "tag": "ExecutionOrder",
            "ids": ids.iter().map(export_id).collect::<Vec<_>>()
        }),
    }
}

/// Export `IEFace` to a JSON `Value`.
#[must_use]
fn export_eface(face: &IEFace) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IEFace"));
    obj.insert("name".to_string(), export_id(&face.name));
    obj.insert(
        "args".to_string(),
        Value::Array(face.args.iter().map(|(id, ty)| {
            json!([export_id(id), export_type(ty)])
        }).collect()),
    );
    if let Some((expr, ty)) = &face.value {
        obj.insert("value".to_string(), json!([export_expr(expr), export_type(ty)]));
    }
    if let Some(body) = &face.body {
        obj.insert("body".to_string(), export_rules(body));
    }
    Value::Object(obj)
}

/// Export an `IPackage` with options, returning a JSON string.
///
/// # Errors
///
/// Returns an error if JSON serialization fails (should not happen with valid data).
pub fn export_package_with_options(pkg: &IPackage, opts: &ExportOptions) -> String {
    let value = if opts.include_positions {
        export_package(pkg)
    } else {
        export_package_without_positions(pkg)
    };

    if opts.pretty {
        serde_json::to_string_pretty(&value).unwrap_or_else(|_| value.to_string())
    } else {
        serde_json::to_string(&value).unwrap_or_else(|_| value.to_string())
    }
}

/// Export an `IModule` with options, returning a JSON string.
///
/// # Errors
///
/// Returns an error if JSON serialization fails (should not happen with valid data).
pub fn export_module_with_options(module: &IModule, opts: &ExportOptions) -> String {
    let value = if opts.include_positions {
        export_module(module)
    } else {
        export_module_without_positions(module)
    };

    if opts.pretty {
        serde_json::to_string_pretty(&value).unwrap_or_else(|_| value.to_string())
    } else {
        serde_json::to_string(&value).unwrap_or_else(|_| value.to_string())
    }
}

// ============================================================================
// Internal serialization helpers
// ============================================================================

/// Export an identifier to JSON.
fn export_id(id: &Id) -> Value {
    let mut obj = Map::new();
    obj.insert("name".to_string(), json!(id.name().as_str()));

    if id.is_qualified() {
        obj.insert("qualifier".to_string(), export_qualifier(id.qualifier()));
    }

    let pos = id.position();
    if pos.line > 0 {
        obj.insert(
            "position".to_string(),
            json!({
                "line": pos.line,
                "column": pos.column
            }),
        );
    }

    Value::Object(obj)
}

/// Export an identifier without position information.
fn export_id_no_pos(id: &Id) -> Value {
    let mut obj = Map::new();
    obj.insert("name".to_string(), json!(id.name().as_str()));

    if id.is_qualified() {
        obj.insert("qualifier".to_string(), export_qualifier(id.qualifier()));
    }

    Value::Object(obj)
}

/// Export a qualifier to JSON.
fn export_qualifier(qual: &Qualifier) -> Value {
    if qual.is_empty() {
        Value::Null
    } else {
        json!(qual.as_str())
    }
}

/// Export a pragma to JSON.
fn export_pragma(pragma: &IPragma) -> Value {
    match pragma {
        IPragma::Properties(id, props) => {
            json!({
                "tag": "Properties",
                "id": export_id(id),
                "properties": props.iter().map(export_property).collect::<Vec<_>>()
            })
        }
    }
}

/// Export a property to JSON.
fn export_property(prop: &IProperty) -> Value {
    let mut obj = Map::new();
    obj.insert("name".to_string(), json!(prop.name));
    if let Some(ref v) = prop.value {
        obj.insert("value".to_string(), json!(v));
    }
    Value::Object(obj)
}

/// Export a definition to JSON.
fn export_def(def: &IDef) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IDef"));
    obj.insert("name".to_string(), export_id(&def.name));
    obj.insert("type".to_string(), export_type(&def.ty));
    obj.insert("expr".to_string(), export_expr(&def.expr));
    obj.insert(
        "props".to_string(),
        Value::Array(def.props.iter().map(export_def_prop).collect()),
    );
    Value::Object(obj)
}

/// Export a definition property to JSON.
fn export_def_prop(prop: &DefProp) -> Value {
    match prop {
        DefProp::NoInline => json!({"tag": "NoInline"}),
        DefProp::AlwaysInline => json!({"tag": "AlwaysInline"}),
        DefProp::Arity(n) => json!({"tag": "Arity", "value": n}),
        DefProp::Primitive => json!({"tag": "Primitive"}),
    }
}

/// Export an expression to JSON.
fn export_expr(expr: &IExpr) -> Value {
    match expr {
        IExpr::Lam(id, ty, body) => {
            json!({
                "tag": "ILam",
                "param": export_id(id),
                "paramType": export_type(ty),
                "body": export_expr(body)
            })
        }
        IExpr::TyLam(id, kind, body) => {
            json!({
                "tag": "ITyLam",
                "tyVar": export_id(id),
                "kind": export_kind(kind),
                "body": export_expr(body)
            })
        }
        IExpr::App(func, args) => {
            json!({
                "tag": "IApp",
                "func": export_expr(func),
                "args": args.iter().map(export_arg).collect::<Vec<_>>()
            })
        }
        IExpr::Var(id) => {
            // IVar only stores the Id, type comes from environment
            json!({
                "tag": "IVar",
                "name": export_id(id)
            })
        }
        IExpr::Con(id, info) => {
            let mut obj = Map::new();
            obj.insert("tag".to_string(), json!("ICon"));
            obj.insert("name".to_string(), export_id(id));
            obj.insert("info".to_string(), export_con_info(info));
            Value::Object(obj)
        }
        IExpr::RefT { ty, expr, position } => {
            // IRefT is only used during evaluation, not in final output
            json!({
                "tag": "IRefT",
                "type": export_type(ty),
                "expr": export_expr(expr),
                "position": format!("{:?}", position)
            })
        }
    }
}

/// Export an argument to JSON.
fn export_arg(arg: &IArg) -> Value {
    match arg {
        IArg::Expr(e) => json!({"tag": "Expr", "value": export_expr(e)}),
        IArg::Type(t) => json!({"tag": "Type", "value": export_type(t)}),
    }
}

/// Export constructor info to JSON.
fn export_con_info(info: &IConInfo) -> Value {
    // Delegate to the no_pos version since position is in the type, not the info
    export_con_info_no_pos(info)
}

/// Export a type to JSON.
fn export_type(ty: &IType) -> Value {
    match ty {
        IType::Var(tv) => {
            json!({
                "tag": "ITVar",
                "var": export_ty_var(tv)
            })
        }
        IType::Con(tc) => {
            json!({
                "tag": "ITCon",
                "con": export_ty_con(tc)
            })
        }
        IType::App(t1, t2) => {
            json!({
                "tag": "ITApp",
                "func": export_type(t1),
                "arg": export_type(t2)
            })
        }
        IType::Gen(n) => {
            json!({
                "tag": "ITGen",
                "index": n
            })
        }
    }
}

/// Export a type variable to JSON.
fn export_ty_var(tv: &ITyVar) -> Value {
    json!({
        "name": export_id(&tv.name),
        "num": tv.num,
        "kind": export_kind(&tv.kind)
    })
}

/// Export a type constructor to JSON.
fn export_ty_con(tc: &ITyCon) -> Value {
    match tc {
        ITyCon::Named(info) => {
            json!({
                "tag": "Named",
                "info": export_ty_con_info(info)
            })
        }
        ITyCon::Num(n) => {
            json!({
                "tag": "Num",
                "value": n.to_string()
            })
        }
        ITyCon::Str(s) => {
            json!({
                "tag": "Str",
                "value": s
            })
        }
    }
}

/// Export type constructor info to JSON.
fn export_ty_con_info(info: &ITyConInfo) -> Value {
    json!({
        "name": export_id(&info.name),
        "kind": export_kind(&info.kind),
        "sort": export_ty_sort(&info.sort)
    })
}

/// Export a type sort to JSON.
fn export_ty_sort(sort: &ITySort) -> Value {
    match sort {
        ITySort::Synonym(arity, expansion) => {
            json!({
                "tag": "Synonym",
                "arity": arity,
                "expansion": export_type(expansion)
            })
        }
        ITySort::Data(ctors) => {
            json!({
                "tag": "Data",
                "constructors": ctors.iter().map(export_id).collect::<Vec<_>>()
            })
        }
        ITySort::Struct(fields) => {
            json!({
                "tag": "Struct",
                "fields": fields.iter().map(export_id).collect::<Vec<_>>()
            })
        }
        ITySort::Abstract => json!({"tag": "Abstract"}),
    }
}

/// Export a kind to JSON.
fn export_kind(kind: &IKind) -> Value {
    match kind {
        IKind::Star => json!({"tag": "KStar"}),
        IKind::Num => json!({"tag": "KNum"}),
        IKind::Str => json!({"tag": "KStr"}),
        IKind::Fun(k1, k2) => {
            json!({
                "tag": "KFun",
                "from": export_kind(k1),
                "to": export_kind(k2)
            })
        }
        IKind::Var(n) => {
            json!({
                "tag": "KVar",
                "index": n
            })
        }
    }
}

/// Export a state element to JSON.
fn export_state_element(elem: &IStateElement) -> Value {
    json!({
        "name": export_id(&elem.name),
        "type": export_type(&elem.ty),
        "init": export_expr(&elem.init)
    })
}

/// Export a rule to JSON.
fn export_rule(rule: &IRule) -> Value {
    let mut obj = Map::new();
    obj.insert("name".to_string(), export_id(&rule.name));
    obj.insert("description".to_string(), json!(rule.description));
    obj.insert("condition".to_string(), export_expr(&rule.condition));
    obj.insert("body".to_string(), export_expr(&rule.body));
    if let Some(ref original) = rule.original {
        obj.insert("original".to_string(), export_id(original));
    }
    Value::Object(obj)
}

/// Export an interface to JSON.
fn export_interface(iface: &IInterface) -> Value {
    json!({
        "type": export_type(&iface.ty),
        "methods": iface.methods.iter().map(export_method).collect::<Vec<_>>()
    })
}

/// Export a method to JSON.
fn export_method(method: &IMethod) -> Value {
    let mut obj = Map::new();
    obj.insert("name".to_string(), export_id(&method.name));
    obj.insert("type".to_string(), export_type(&method.ty));
    obj.insert("body".to_string(), export_expr(&method.body));
    if let Some(ref cond) = method.condition {
        obj.insert("condition".to_string(), export_expr(cond));
    }
    Value::Object(obj)
}

// ============================================================================
// Variants without position information (for cleaner diff testing)
// ============================================================================

/// Export a package without position information.
fn export_package_without_positions(pkg: &IPackage) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IPackage"));
    obj.insert("name".to_string(), export_id_no_pos(&pkg.name));
    obj.insert(
        "depends".to_string(),
        Value::Array(pkg.depends.iter().map(|(id, sig)| {
            json!([export_id_no_pos(id), sig])
        }).collect()),
    );
    obj.insert(
        "pragmas".to_string(),
        Value::Array(pkg.pragmas.iter().map(|p| export_pragma_no_pos(p)).collect()),
    );
    obj.insert(
        "defs".to_string(),
        Value::Array(pkg.defs.iter().map(|d| export_def_no_pos(d)).collect()),
    );
    Value::Object(obj)
}

/// Export a module without position information.
fn export_module_without_positions(module: &IModule) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IModule"));
    obj.insert("name".to_string(), export_id_no_pos(&module.name));
    obj.insert("is_wrapped".to_string(), json!(module.is_wrapped));
    obj.insert(
        "pragmas".to_string(),
        Value::Array(module.pragmas.iter().map(export_pragma_no_pos).collect()),
    );
    obj.insert(
        "local_defs".to_string(),
        Value::Array(module.local_defs.iter().map(export_def_no_pos).collect()),
    );
    obj.insert("rules".to_string(), export_rules_no_pos(&module.rules));
    obj.insert(
        "interface".to_string(),
        Value::Array(module.interface.iter().map(export_eface_no_pos).collect()),
    );
    Value::Object(obj)
}

/// Export `IRules` without position information.
fn export_rules_no_pos(rules: &IRules) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IRules"));
    obj.insert(
        "pragmas".to_string(),
        Value::Array(rules.pragmas.iter().map(export_schedule_pragma).collect()),
    );
    obj.insert(
        "rules".to_string(),
        Value::Array(rules.rules.iter().map(export_rule_no_pos).collect()),
    );
    Value::Object(obj)
}

/// Export `IEFace` without position information.
fn export_eface_no_pos(face: &IEFace) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IEFace"));
    obj.insert("name".to_string(), export_id_no_pos(&face.name));
    obj.insert(
        "args".to_string(),
        Value::Array(face.args.iter().map(|(id, ty)| {
            json!([export_id_no_pos(id), export_type_no_pos(ty)])
        }).collect()),
    );
    if let Some((expr, ty)) = &face.value {
        obj.insert("value".to_string(), json!([export_expr_no_pos(expr), export_type_no_pos(ty)]));
    }
    if let Some(body) = &face.body {
        obj.insert("body".to_string(), export_rules_no_pos(body));
    }
    Value::Object(obj)
}

/// Export a pragma without position information.
fn export_pragma_no_pos(pragma: &IPragma) -> Value {
    match pragma {
        IPragma::Properties(id, props) => {
            json!({
                "tag": "Properties",
                "id": export_id_no_pos(id),
                "properties": props.iter().map(export_property).collect::<Vec<_>>()
            })
        }
    }
}

/// Export a definition without position information.
fn export_def_no_pos(def: &IDef) -> Value {
    let mut obj = Map::new();
    obj.insert("tag".to_string(), json!("IDef"));
    obj.insert("name".to_string(), export_id_no_pos(&def.name));
    obj.insert("type".to_string(), export_type_no_pos(&def.ty));
    obj.insert("expr".to_string(), export_expr_no_pos(&def.expr));
    obj.insert(
        "props".to_string(),
        Value::Array(def.props.iter().map(export_def_prop).collect()),
    );
    Value::Object(obj)
}

/// Export an expression without position information.
fn export_expr_no_pos(expr: &IExpr) -> Value {
    match expr {
        IExpr::Lam(id, ty, body) => {
            json!({
                "tag": "ILam",
                "param": export_id_no_pos(id),
                "paramType": export_type_no_pos(ty),
                "body": export_expr_no_pos(body)
            })
        }
        IExpr::TyLam(id, kind, body) => {
            json!({
                "tag": "ITyLam",
                "tyVar": export_id_no_pos(id),
                "kind": export_kind(kind),
                "body": export_expr_no_pos(body)
            })
        }
        IExpr::App(func, args) => {
            json!({
                "tag": "IApp",
                "func": export_expr_no_pos(func),
                "args": args.iter().map(|a| export_arg_no_pos(a)).collect::<Vec<_>>()
            })
        }
        IExpr::Var(id) => {
            // IVar only stores the Id, type comes from environment
            json!({
                "tag": "IVar",
                "name": export_id_no_pos(id)
            })
        }
        IExpr::Con(id, info) => {
            let mut obj = Map::new();
            obj.insert("tag".to_string(), json!("ICon"));
            obj.insert("name".to_string(), export_id_no_pos(id));
            obj.insert("info".to_string(), export_con_info_no_pos(info));
            Value::Object(obj)
        }
        IExpr::RefT { ty, expr, .. } => {
            // IRefT is only used during evaluation, not in final output
            json!({
                "tag": "IRefT",
                "type": export_type_no_pos(ty),
                "expr": export_expr_no_pos(expr)
            })
        }
    }
}

/// Export an argument without position information.
fn export_arg_no_pos(arg: &IArg) -> Value {
    match arg {
        IArg::Expr(e) => json!({"tag": "Expr", "value": export_expr_no_pos(e)}),
        IArg::Type(t) => json!({"tag": "Type", "value": export_type_no_pos(t)}),
    }
}

/// Export constructor info without position information.
fn export_con_info_no_pos(info: &IConInfo) -> Value {
    match info {
        IConInfo::Def { ty, .. } => {
            json!({
                "tag": "ICDef",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::Value { ty, .. } => {
            json!({
                "tag": "ICValue",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::Prim { ty, op } => {
            json!({
                "tag": "ICPrim",
                "type": export_type_no_pos(ty),
                "op": format!("{op:?}")
            })
        }
        IConInfo::Foreign { ty, name, is_c, .. } => {
            json!({
                "tag": "ICForeign",
                "type": export_type_no_pos(ty),
                "name": name,
                "isC": is_c
            })
        }
        IConInfo::Con { ty, tag_info } => {
            json!({
                "tag": "ICCon",
                "type": export_type_no_pos(ty),
                "conNo": tag_info.con_no,
                "numCon": tag_info.num_con,
                "conTag": tag_info.con_tag,
                "tagSize": tag_info.tag_size
            })
        }
        IConInfo::Is { ty, tag_info } => {
            json!({
                "tag": "ICIs",
                "type": export_type_no_pos(ty),
                "conNo": tag_info.con_no,
                "numCon": tag_info.num_con
            })
        }
        IConInfo::Out { ty, tag_info } => {
            json!({
                "tag": "ICOut",
                "type": export_type_no_pos(ty),
                "conNo": tag_info.con_no,
                "numCon": tag_info.num_con
            })
        }
        IConInfo::Tuple { ty, field_ids } => {
            json!({
                "tag": "ICTuple",
                "type": export_type_no_pos(ty),
                "fieldIds": field_ids.iter().map(export_id_no_pos).collect::<Vec<_>>()
            })
        }
        IConInfo::Sel { ty, sel_no, num_sel } => {
            json!({
                "tag": "ICSel",
                "type": export_type_no_pos(ty),
                "selNo": sel_no,
                "numSel": num_sel
            })
        }
        IConInfo::Verilog { ty, is_user_import, info, .. } => {
            json!({
                "tag": "ICVerilog",
                "type": export_type_no_pos(ty),
                "isUserImport": is_user_import,
                "moduleName": info.name
            })
        }
        IConInfo::Undet { ty, kind, .. } => {
            json!({
                "tag": "ICUndet",
                "type": export_type_no_pos(ty),
                "kind": format!("{kind:?}")
            })
        }
        IConInfo::Int { ty, value } => {
            json!({
                "tag": "ICInt",
                "type": export_type_no_pos(ty),
                "value": value.value.to_string()
            })
        }
        IConInfo::Real { ty, value } => {
            json!({
                "tag": "ICReal",
                "type": export_type_no_pos(ty),
                "value": value
            })
        }
        IConInfo::String { ty, value } => {
            json!({
                "tag": "ICString",
                "type": export_type_no_pos(ty),
                "value": value
            })
        }
        IConInfo::Char { ty, value } => {
            json!({
                "tag": "ICChar",
                "type": export_type_no_pos(ty),
                "value": value.to_string()
            })
        }
        IConInfo::Handle { ty, handle_id } => {
            json!({
                "tag": "ICHandle",
                "type": export_type_no_pos(ty),
                "handleId": handle_id
            })
        }
        IConInfo::StateVar { ty, .. } => {
            json!({
                "tag": "ICStateVar",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::MethArg { ty } => {
            json!({
                "tag": "ICMethArg",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::ModPort { ty } => {
            json!({
                "tag": "ICModPort",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::ModParam { ty } => {
            json!({
                "tag": "ICModParam",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::IFace { ty, ifc_ty_id, .. } => {
            json!({
                "tag": "ICIFace",
                "type": export_type_no_pos(ty),
                "ifcTyId": export_id_no_pos(ifc_ty_id)
            })
        }
        IConInfo::RuleAssert { ty, .. } => {
            json!({
                "tag": "ICRuleAssert",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::SchedPragmas { ty, .. } => {
            json!({
                "tag": "ICSchedPragmas",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::Clock { ty, .. } => {
            json!({
                "tag": "ICClock",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::Reset { ty, .. } => {
            json!({
                "tag": "ICReset",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::Inout { ty, .. } => {
            json!({
                "tag": "ICInout",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::LazyArray { ty, .. } => {
            json!({
                "tag": "ICLazyArray",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::Name { ty, name } => {
            json!({
                "tag": "ICName",
                "type": export_type_no_pos(ty),
                "name": export_id_no_pos(name)
            })
        }
        IConInfo::Attrib { ty, .. } => {
            json!({
                "tag": "ICAttrib",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::Position { ty, .. } => {
            json!({
                "tag": "ICPosition",
                "type": export_type_no_pos(ty)
            })
        }
        IConInfo::Type { ty, inner_type } => {
            json!({
                "tag": "ICType",
                "type": export_type_no_pos(ty),
                "innerType": export_type_no_pos(inner_type)
            })
        }
        IConInfo::Pred { ty, pred } => {
            json!({
                "tag": "ICPred",
                "type": export_type_no_pos(ty),
                "class": export_id_no_pos(&pred.class),
                "args": pred.args.iter().map(export_type_no_pos).collect::<Vec<_>>()
            })
        }
    }
}

/// Export a type without position information.
fn export_type_no_pos(ty: &IType) -> Value {
    match ty {
        IType::Var(tv) => {
            json!({
                "tag": "ITVar",
                "var": export_ty_var_no_pos(tv)
            })
        }
        IType::Con(tc) => {
            json!({
                "tag": "ITCon",
                "con": export_ty_con_no_pos(tc)
            })
        }
        IType::App(t1, t2) => {
            json!({
                "tag": "ITApp",
                "func": export_type_no_pos(t1),
                "arg": export_type_no_pos(t2)
            })
        }
        IType::Gen(n) => {
            json!({
                "tag": "ITGen",
                "index": n
            })
        }
    }
}

/// Export a type variable without position information.
fn export_ty_var_no_pos(tv: &ITyVar) -> Value {
    json!({
        "name": export_id_no_pos(&tv.name),
        "num": tv.num,
        "kind": export_kind(&tv.kind)
    })
}

/// Export a type constructor without position information.
fn export_ty_con_no_pos(tc: &ITyCon) -> Value {
    match tc {
        ITyCon::Named(info) => {
            json!({
                "tag": "Named",
                "info": export_ty_con_info_no_pos(info)
            })
        }
        ITyCon::Num(n) => {
            json!({
                "tag": "Num",
                "value": n.to_string()
            })
        }
        ITyCon::Str(s) => {
            json!({
                "tag": "Str",
                "value": s
            })
        }
    }
}

/// Export type constructor info without position information.
fn export_ty_con_info_no_pos(info: &ITyConInfo) -> Value {
    json!({
        "name": export_id_no_pos(&info.name),
        "kind": export_kind(&info.kind),
        "sort": export_ty_sort_no_pos(&info.sort)
    })
}

/// Export a type sort without position information.
fn export_ty_sort_no_pos(sort: &ITySort) -> Value {
    match sort {
        ITySort::Synonym(arity, expansion) => {
            json!({
                "tag": "Synonym",
                "arity": arity,
                "expansion": export_type_no_pos(expansion)
            })
        }
        ITySort::Data(ctors) => {
            json!({
                "tag": "Data",
                "constructors": ctors.iter().map(export_id_no_pos).collect::<Vec<_>>()
            })
        }
        ITySort::Struct(fields) => {
            json!({
                "tag": "Struct",
                "fields": fields.iter().map(export_id_no_pos).collect::<Vec<_>>()
            })
        }
        ITySort::Abstract => json!({"tag": "Abstract"}),
    }
}

/// Export a state element without position information.
fn export_state_element_no_pos(elem: &IStateElement) -> Value {
    json!({
        "name": export_id_no_pos(&elem.name),
        "type": export_type_no_pos(&elem.ty),
        "init": export_expr_no_pos(&elem.init)
    })
}

/// Export a rule without position information.
fn export_rule_no_pos(rule: &IRule) -> Value {
    let mut obj = Map::new();
    obj.insert("name".to_string(), export_id_no_pos(&rule.name));
    obj.insert("description".to_string(), json!(rule.description));
    obj.insert("condition".to_string(), export_expr_no_pos(&rule.condition));
    obj.insert("body".to_string(), export_expr_no_pos(&rule.body));
    if let Some(ref original) = rule.original {
        obj.insert("original".to_string(), export_id_no_pos(original));
    }
    Value::Object(obj)
}

/// Export an interface without position information.
fn export_interface_no_pos(iface: &IInterface) -> Value {
    json!({
        "type": export_type_no_pos(&iface.ty),
        "methods": iface.methods.iter().map(|m| export_method_no_pos(m)).collect::<Vec<_>>()
    })
}

/// Export a method without position information.
fn export_method_no_pos(method: &IMethod) -> Value {
    let mut obj = Map::new();
    obj.insert("name".to_string(), export_id_no_pos(&method.name));
    obj.insert("type".to_string(), export_type_no_pos(&method.ty));
    obj.insert("body".to_string(), export_expr_no_pos(&method.body));
    if let Some(ref cond) = method.condition {
        obj.insert("condition".to_string(), export_expr_no_pos(cond));
    }
    Value::Object(obj)
}

