//! ImperativeStatement type and conversion to CSyntax.
//!
//! This module mirrors the Haskell `CVParserCommon.lhs` ImperativeStatement type
//! and `CVParserImperative.lhs` conversion functions.
//!
//! BSV uses an imperative style with declarations, assignments, and control flow.
//! This intermediate representation captures that style and is then converted to
//! functional CSyntax (let expressions, case expressions, etc.).

use bsc_diagnostics::{Position, Span};
use bsc_syntax::csyntax::*;
use bsc_syntax::id::Id;
use bsc_syntax::Literal;
use smol_str::SmolStr;

fn get_naked_expr_name(expr: &CExpr) -> Option<CExpr> {
    let id_def = match expr {
        CExpr::Apply(func, _, _) => {
            if let CExpr::Var(id) = func.as_ref() {
                Some(id.clone())
            } else {
                None
            }
        }
        CExpr::Var(id) => Some(id.clone()),
        _ => None,
    };
    let id_def = id_def.filter(|id| id.name().as_str() != "_f__")?;
    let display_name = id_def.name().clone();
    let new_name = format!("_inst_{}", display_name);
    let mut id_prime = id_def;
    id_prime.set_name(new_name);
    id_prime.add_prop(bsc_syntax::id::IdProp::Keep);
    id_prime.set_naked_inst();
    id_prime.set_display_name(display_name);
    let name_expr = CExpr::Apply(
        Box::new(CExpr::Var(Id::qualified("Prelude", "primGetName", id_prime.position()))),
        vec![CExpr::Var(id_prime)],
        Span::DUMMY,
    );
    Some(name_expr)
}

fn clet_seq(defls: Vec<CDefl>, body: CExpr) -> CExpr {
    if defls.is_empty() {
        return body;
    }
    match body {
        CExpr::LetSeq(mut inner_defls, inner_body, span) => {
            let mut merged = defls;
            merged.append(&mut inner_defls);
            CExpr::LetSeq(merged, inner_body, span)
        }
        _ => CExpr::LetSeq(defls, Box::new(body), Span::DUMMY),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImperativeStmtContext {
    ISCToplevel,
    ISCModule,
    ISCAction,
    ISCActionValue,
    ISCExpression,
    ISCRules,
    ISCInterface,
    ISCInstance,
    ISCBVI,
    ISCSequence,
    ISCIsModule,
}

#[derive(Debug, Clone)]
pub struct ImperativeFlags {
    pub function_name_args: Option<(Id, Vec<(Option<CType>, Id)>)>,
    pub stmt_context: ImperativeStmtContext,
    pub filestr: Option<String>,
    pub ifc_type: Option<CType>,
    pub end_keyword: Option<String>,
    pub allow_eq: bool,
    pub allow_bind: bool,
    pub allow_reg_write: bool,
    pub allow_subscript_assign: bool,
    pub allow_field_assign: bool,
    pub allow_return: bool,
    pub allow_naked_expr: bool,
    pub allow_let: bool,
    pub allow_function: bool,
    pub allow_inst: bool,
    pub allow_rule: bool,
    pub allow_method: bool,
    pub allow_subinterface: bool,
    pub allow_conditionals: bool,
    pub allow_loops: bool,
    pub allow_module: bool,
    pub allow_interface: bool,
    pub allow_foreign: bool,
    pub allow_typedef: bool,
    pub allow_typeclass: bool,
}

#[derive(Debug, Clone)]
pub enum ImperativeStatement {
    Import(Vec<Id>),
    Export(Vec<CExport>),
    Typedef(Vec<CDefn>),

    InterfaceDecl {
        pos: Position,
        name: Id,
        type_vars: Vec<Id>,
        members: Vec<CField>,
    },

    ModuleDefn {
        pos: Position,
        name: Id,
        pragma: Option<CPragma>,
        module_type: CQType,
        def_clause: CClause,
    },

    FunctionDefn {
        pos: Position,
        name: Id,
        ret_type: Option<CType>,
        params: Vec<(Id, Option<CType>)>,
        provisos: Vec<CPred>,
        body: Vec<ImperativeStatement>,
        attrs: Vec<(Id, Option<CExpr>)>,
    },

    Rule {
        pos: Position,
        name: Id,
        guard: Option<CExpr>,
        body_pos: Position,
        body: Vec<ImperativeStatement>,
    },

    MethodDefn {
        pos: Position,
        name: Id,
        ret_type: Option<CType>,
        params: Vec<(Id, Option<CType>)>,
        guard: Option<CExpr>,
        body: Vec<ImperativeStatement>,
    },

    InstanceDefn {
        class_name: Id,
        type_args: Vec<CType>,
        provisos: Vec<CPred>,
        body: Vec<CDefl>,
    },

    TypeclassDefn {
        name: Id,
        type_vars: Vec<Id>,
        provisos: Vec<CPred>,
        fundeps: Vec<(Vec<Id>, Vec<Id>)>,
        members: Vec<CField>,
    },

    Decl {
        name: Id,
        ty: Option<CType>,
        init: Option<CExpr>,
    },

    ArrayDecl {
        name: Id,
        base_type: CType,
        dimensions: Vec<CExpr>,
        init: Option<CExpr>,
        init_pos: Option<Position>,
    },

    TupleDecl {
        names: Vec<Id>,
        ty: Option<CType>,
        init: Option<CExpr>,
    },

    InterfaceVarDecl {
        name: Id,
        ty: CType,
    },

    Let {
        name: Id,
        expr: CExpr,
    },

    LetBind {
        name: Id,
        expr: CExpr,
    },

    Equal {
        name: Id,
        expr: CExpr,
    },

    Update {
        pos: Position,
        lhs: CExpr,
        rhs: CExpr,
    },

    Bind {
        name: Id,
        ty: Option<CType>,
        expr: CExpr,
    },

    RegWrite {
        lhs: CExpr,
        rhs: CExpr,
    },

    If {
        pos: Position,
        cond: CExpr,
        then_branch: Vec<ImperativeStatement>,
        else_branch: Option<Vec<ImperativeStatement>>,
    },

    For {
        pos: Position,
        init: Vec<ImperativeStatement>,
        cond: CExpr,
        update: Vec<ImperativeStatement>,
        body: Vec<ImperativeStatement>,
    },

    While {
        pos: Position,
        cond: CExpr,
        body: Vec<ImperativeStatement>,
    },

    Case {
        pos: Position,
        subject: CExpr,
        arms: Vec<(Position, Vec<CExpr>, Vec<ImperativeStatement>)>,
        default: Option<(Position, Vec<ImperativeStatement>)>,
    },

    CaseTagged {
        pos: Position,
        subject: CExpr,
        arms: Vec<(Position, CPat, Vec<CExpr>, Vec<ImperativeStatement>)>,
        default: Option<Vec<ImperativeStatement>>,
    },

    BeginEnd {
        pos: Position,
        stmts: Vec<ImperativeStatement>,
    },

    Action {
        pos: Position,
        stmts: Vec<ImperativeStatement>,
    },

    Return {
        pos: Position,
        expr: Option<CExpr>,
    },

    NakedExpr(CExpr),

    InterfaceExpr {
        ty: Option<CType>,
        members: Vec<ImperativeStatement>,
    },

    SubinterfaceMethod {
        pos: Position,
        name: Id,
        expr: CExpr,
    },

    SubinterfaceBody {
        pos: Position,
        ty: Option<CType>,
        name: Id,
        members: Vec<ImperativeStatement>,
    },

    /// Module instantiation statement
    /// Corresponds to ISInst in Haskell BSC
    Inst {
        pos: Position,
        attrs: Vec<(Position, CPragma)>,
        ifc_var: Id,    // interface variable name
        inst_var: Id,   // instance variable name
        ifc_type: Option<CType>,  // interface type
        clocked_by: Option<CExpr>, // clocked_by expression
        reset_by: Option<CExpr>,   // reset_by expression
        powered_by: Option<CExpr>, // powered_by expression
        constructor: CExpr,        // module constructor expression
    },

    #[allow(dead_code)]
    Attributes(Vec<(Id, Option<CExpr>)>),
}

impl ImperativeStatement {
    pub fn set_attributes(&mut self, new_attrs: Vec<(Id, Option<CExpr>)>) {
        match self {
            ImperativeStatement::FunctionDefn { attrs, .. } => {
                *attrs = new_attrs;
            }
            _ => {}
        }
    }
}

pub fn convert_top_statements_to_csyntax(
    stmts: Vec<ImperativeStatement>,
) -> (Vec<CImport>, ExportSpec, Vec<CDefn>) {
    let mut imports = Vec::new();
    let mut exports = Vec::new();
    let mut definitions = Vec::new();

    for stmt in stmts {
        match stmt {
            ImperativeStatement::Import(pkgs) => {
                for pkg in pkgs {
                    imports.push(CImport::Simple {
                        qualified: false,
                        module: pkg,
                        alias: None,
                        spec: None,
                        span: Span::DUMMY,
                    });
                }
            }
            ImperativeStatement::Export(items) => {
                exports.extend(items);
            }
            ImperativeStatement::Typedef(defs) => {
                definitions.extend(defs);
            }
            ImperativeStatement::InterfaceDecl {
                name,
                type_vars,
                members,
                ..
            } => {
                definitions.push(CDefn::Struct(CStructDef {
                    visible: true,
                    sub_type: StructSubType::Interface(vec![]),
                    name: IdK::Plain(name),
                    params: type_vars,
                    fields: members,
                    deriving: vec![],
                    span: Span::DUMMY,
                }));
            }
            ImperativeStatement::ModuleDefn {
                name,
                pragma,
                module_type,
                def_clause,
                ..
            } => {
                if let Some(prag) = pragma {
                    definitions.push(CDefn::Pragma(prag));
                }
                definitions.push(CDefn::ValueSign(CDef::Untyped {
                    name,
                    ty: module_type,
                    clauses: vec![def_clause],
                    span: Span::DUMMY,
                }));
            }
            ImperativeStatement::FunctionDefn {
                name,
                ret_type,
                params,
                provisos,
                body,
                attrs,
                ..
            } => {
                let has_noinline = attrs.iter().any(|(n, _)| n.name() == "noinline");
                if has_noinline {
                    definitions.push(CDefn::Pragma(CPragma::NoInline(name.clone())));
                }

                let body_expr = convert_stmts_to_expr(body);
                let patterns: Vec<CPat> = params.iter().map(|(n, _)| CPat::Var(n.clone())).collect();
                let clauses = vec![CClause {
                    patterns,
                    qualifiers: vec![],
                    body: body_expr,
                    span: Span::DUMMY,
                }];
                if let Some(func_type) = build_function_type(params, provisos, ret_type) {
                    definitions.push(CDefn::ValueSign(CDef::Untyped {
                        name,
                        ty: func_type,
                        clauses,
                        span: Span::DUMMY,
                    }));
                } else {
                    definitions.push(CDefn::Value(CValueDef {
                        name,
                        clauses,
                        span: Span::DUMMY,
                    }));
                }
            }
            ImperativeStatement::InstanceDefn {
                class_name,
                type_args,
                provisos,
                body,
            } => {
                let instance_type = build_instance_type(class_name, type_args, provisos);
                definitions.push(CDefn::Instance(CInstanceDef {
                    ty: instance_type,
                    methods: body,
                    span: Span::DUMMY,
                }));
            }
            ImperativeStatement::TypeclassDefn {
                name,
                type_vars,
                provisos,
                fundeps,
                members,
            } => {
                let fundep_structs: Vec<CFunDep> = fundeps
                    .into_iter()
                    .map(|(from, to)| CFunDep { from, to })
                    .collect();
                definitions.push(CDefn::Class(CClassDef {
                    incoherent_matches: None,
                    supers: provisos,
                    name: IdK::Plain(name),
                    params: type_vars,
                    fundeps: fundep_structs,
                    methods: members,
                    span: Span::DUMMY,
                }));
            }
            ImperativeStatement::Decl { name, init, .. } => {
                if let Some(expr) = init {
                    definitions.push(CDefn::Value(CValueDef {
                        name,
                        clauses: vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: expr,
                            span: Span::DUMMY,
                        }],
                        span: Span::DUMMY,
                    }));
                }
            }
            _ => {}
        }
    }

    let export_spec = if exports.is_empty() {
        ExportSpec::Hiding(vec![])
    } else {
        ExportSpec::Only(exports)
    };

    (imports, export_spec, definitions)
}

fn build_module_type(params: Vec<(Id, CType)>, mut provisos: Vec<CPred>, ifc: CType) -> CQType {
    let m_var = CType::Var(Id::new("_m__", Position::unknown()));
    let c_var = CType::Var(Id::new("_c__", Position::unknown()));

    let is_module_pred = CPred {
        class: Id::qualified("Prelude", "IsModule", Position::unknown()),
        args: vec![m_var.clone(), c_var],
        span: Span::DUMMY,
    };
    provisos.insert(0, is_module_pred);

    let module_result = CType::Apply(Box::new(m_var), Box::new(ifc), Span::DUMMY);

    let full_type = params.into_iter().rev().fold(module_result, |acc, (_, param_type)| {
        crate::make_fn_type(param_type, acc)
    });

    CQType {
        context: provisos,
        ty: full_type,
        span: Span::DUMMY,
    }
}

fn build_function_type(params: Vec<(Id, Option<CType>)>, provisos: Vec<CPred>, ret_type: Option<CType>) -> Option<CQType> {
    let ret_type = ret_type?;
    let param_types: Option<Vec<CType>> = params.into_iter()
        .map(|(_, t)| t)
        .collect();
    let param_types = param_types?;

    let full_type = param_types.into_iter().rev().fold(ret_type, |acc, param_type| {
        crate::make_fn_type(param_type, acc)
    });

    Some(CQType {
        context: provisos,
        ty: full_type,
        span: Span::DUMMY,
    })
}

fn build_instance_type(class_name: Id, type_args: Vec<CType>, provisos: Vec<CPred>) -> CQType {
    let instance_ty = if type_args.is_empty() {
        CType::Con(class_name.into())
    } else {
        let base = CType::Con(class_name.into());
        type_args.into_iter().fold(base, |acc, arg| {
            CType::Apply(Box::new(acc), Box::new(arg), Span::DUMMY)
        })
    };

    CQType {
        context: provisos,
        ty: instance_ty,
        span: Span::DUMMY,
    }
}

fn convert_case_to_expr(
    pos: Position,
    subject: CExpr,
    arms: Vec<(Position, Vec<CExpr>, Vec<ImperativeStatement>)>,
    default: Option<(Position, Vec<ImperativeStatement>)>,
) -> CExpr {
    let mut case_arms: Vec<CCaseArm> = Vec::new();

    for (arm_pos, tests, body) in arms {

        let body_expr = convert_stmts_to_expr(body);

        let filters = if tests.is_empty() {
            vec![]
        } else {
            let eq_tests: Vec<COperand> = tests
                .iter()
                .map(|test| {
                    let test_pos = get_expr_position(test);
                    COperand::Expr(CExpr::OperChain(
                        vec![
                            COperand::Expr(subject.clone()),
                            COperand::Operator {
                                arity: 2,
                                name: Id::qualified("Prelude", "==", test_pos),
                            },
                            COperand::Expr(test.clone()),
                        ],
                        Span::DUMMY,
                    ))
                })
                .collect();

            let filter_expr = if eq_tests.len() == 1 {
                CExpr::OperChain(vec![eq_tests.into_iter().next().unwrap()], Span::DUMMY)
            } else {
                let mut ops: Vec<COperand> = Vec::new();
                for (i, test) in eq_tests.into_iter().enumerate() {
                    if i > 0 {
                        ops.push(COperand::Operator {
                            arity: 2,
                            name: Id::qualified("Prelude", "||", arm_pos.clone()),
                        });
                    }
                    ops.push(test);
                }
                CExpr::OperChain(ops, Span::DUMMY)
            };
            vec![CQual::Filter(filter_expr)]
        };

        case_arms.push(CCaseArm {
            pattern: CPat::Wildcard(arm_pos),
            qualifiers: filters,
            body: body_expr,
            span: Span::DUMMY,
        });
    }

    if let Some((dflt_pos, dflt_body)) = default {
        let dflt_expr = convert_stmts_to_expr(dflt_body);
        case_arms.push(CCaseArm {
            pattern: CPat::Wildcard(dflt_pos),
            qualifiers: vec![],
            body: dflt_expr,
            span: Span::DUMMY,
        });
    }

    let case_subject = CExpr::Struct(
        Some(true),
        Id::qualified("Prelude", "PrimUnit", pos.clone()),
        vec![],
        Span::DUMMY,
    );

    CExpr::Case(pos, Box::new(case_subject), case_arms)
}

fn convert_case_tagged_to_expr(
    pos: Position,
    subject: CExpr,
    arms: Vec<(Position, CPat, Vec<CExpr>, Vec<ImperativeStatement>)>,
    default: Option<Vec<ImperativeStatement>>,
) -> CExpr {
    let mut case_arms: Vec<CCaseArm> = Vec::new();

    for (_arm_pos, pat, tests, body) in arms {
        let body_expr = convert_stmts_to_expr(body);
        let filters = tests.into_iter().map(CQual::Filter).collect();
        case_arms.push(CCaseArm {
            pattern: pat,
            qualifiers: filters,
            body: body_expr,
            span: Span::DUMMY,
        });
    }

    if let Some(dflt_body) = default {
        let dflt_pos = pos.clone();
        let dflt_expr = convert_stmts_to_expr(dflt_body);
        case_arms.push(CCaseArm {
            pattern: CPat::Wildcard(dflt_pos),
            qualifiers: vec![],
            body: dflt_expr,
            span: Span::DUMMY,
        });
    }

    CExpr::Case(pos, Box::new(subject), case_arms)
}

fn get_expr_position(expr: &CExpr) -> Position {
    match expr {
        CExpr::Lit(_, pos) => pos.clone(),
        CExpr::Var(id) => id.position(),
        CExpr::Con(id, _, _) => id.position(),
        CExpr::Apply(func, _, _) => get_expr_position(func),
        CExpr::Any { position, .. } => position.clone(),
        _ => Position::unknown(),
    }
}

fn convert_list_to_cons(exprs: Vec<CExpr>) -> CExpr {
    let nil = CExpr::Con(Id::unpositioned("Nil"), vec![], Span::DUMMY);
    exprs.into_iter().rev().fold(nil, |acc, elem| {
        CExpr::Con(Id::unpositioned("Cons"), vec![elem, acc], Span::DUMMY)
    })
}

fn get_list_item_position(expr: &CExpr, _fallback: &Position, _index: usize) -> Position {
    match expr {
        CExpr::Lit(_, pos) => pos.clone(),
        CExpr::List(_, _) => _fallback.clone(),
        CExpr::Var(id) => id.position(),
        CExpr::Apply(func, _, _) => get_list_item_position(func, _fallback, _index),
        CExpr::Any { position, .. } => position.clone(),
        _ => _fallback.clone(),
    }
}

fn build_array_init_expr(
    dimensions: &[CExpr],
    init: Option<CExpr>,
    pos: Position,
    inner_dim: Option<&CExpr>,
) -> CExpr {
    if dimensions.is_empty() {
        return init.unwrap_or_else(|| CExpr::Any {
            position: pos,
            kind: UndefKind::NoMatch,
            span: Span::DUMMY,
        });
    }

    let dim = &dimensions[0];
    let remaining_dims = &dimensions[1..];

    if let Some(init_expr) = init {
        match init_expr {
            CExpr::List(exprs, _) => {
                if remaining_dims.is_empty() {
                    let cons_list = convert_list_to_cons(exprs);
                    let arr_init = CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayInitialize", pos.clone()))),
                        vec![cons_list],
                        Span::DUMMY,
                    );
                    CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayCheck", pos.clone()))),
                        vec![
                            CExpr::Lit(bsc_syntax::literal::Literal::Position, pos),
                            inner_dim.cloned().unwrap_or_else(|| dim.clone()),
                            arr_init,
                        ],
                        Span::DUMMY,
                    )
                } else {
                    let inner_exprs: Vec<CExpr> = exprs
                        .into_iter()
                        .enumerate()
                        .map(|(i, e)| {
                            let inner_pos = get_list_item_position(&e, &pos, i);
                            build_array_init_expr(remaining_dims, Some(e), inner_pos, Some(&dimensions[1]))
                        })
                        .collect();
                    let cons_list = convert_list_to_cons(inner_exprs);
                    let arr_init = CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayInitialize", pos.clone()))),
                        vec![cons_list],
                        Span::DUMMY,
                    );
                    CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayCheck", pos.clone()))),
                        vec![
                            CExpr::Lit(bsc_syntax::literal::Literal::Position, pos),
                            dim.clone(),
                            arr_init,
                        ],
                        Span::DUMMY,
                    )
                }
            }
            CExpr::List(exprs, _) => {
                if remaining_dims.is_empty() {
                    let cons_list = convert_list_to_cons(exprs);
                    let arr_init = CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayInitialize", pos.clone()))),
                        vec![cons_list],
                        Span::DUMMY,
                    );
                    CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayCheck", pos.clone()))),
                        vec![
                            CExpr::Lit(bsc_syntax::literal::Literal::Position, pos.clone()),
                            inner_dim.cloned().unwrap_or_else(|| dim.clone()),
                            arr_init,
                        ],
                        Span::DUMMY,
                    )
                } else {
                    let inner_exprs: Vec<CExpr> = exprs
                        .into_iter()
                        .enumerate()
                        .map(|(i, e)| {
                            let inner_pos = get_list_item_position(&e, &pos, i);
                            build_array_init_expr(remaining_dims, Some(e), inner_pos, Some(&dimensions[1]))
                        })
                        .collect();
                    let cons_list = convert_list_to_cons(inner_exprs);
                    let arr_init = CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayInitialize", pos.clone()))),
                        vec![cons_list],
                        Span::DUMMY,
                    );
                    CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayCheck", pos.clone()))),
                        vec![
                            CExpr::Lit(bsc_syntax::literal::Literal::Position, pos.clone()),
                            dim.clone(),
                            arr_init,
                        ],
                        Span::DUMMY,
                    )
                }
            }
            other => {
                CExpr::Apply(
                    Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayCheck", pos.clone()))),
                    vec![
                        CExpr::Lit(bsc_syntax::literal::Literal::Position, pos),
                        inner_dim.cloned().unwrap_or_else(|| dim.clone()),
                        other,
                    ],
                    Span::DUMMY,
                )
            }
        }
    } else {
        CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "primArrayNewU", pos))),
            vec![dim.clone()],
            Span::DUMMY,
        )
    }
}

fn build_array_type(base_type: CType, num_dimensions: usize) -> CType {
    (0..num_dimensions).fold(base_type, |acc, _| {
        let mut array_con_id = Id::qualified("Prelude", "Array", Position::unknown());
        array_con_id.add_prop(bsc_syntax::id::IdProp::ParserGenerated);
        CType::Apply(
            Box::new(CType::Con(array_con_id.into())),
            Box::new(acc),
            Span::DUMMY,
        )
    })
}

fn extract_interface_id(ty: &CType) -> Option<Id> {
    match ty {
        CType::Con(tycon) => Some(tycon.name.clone()),
        CType::Apply(inner, _, _) => extract_interface_id(inner),
        _ => None,
    }
}

fn convert_module_body_to_expr(stmts: Vec<ImperativeStatement>, pos: Position, ifc_id: Option<Id>) -> CExpr {
    use std::collections::HashMap;
    let mut module_items = Vec::new();
    let mut rules = Vec::new();
    let mut methods: Vec<CField> = Vec::new();
    let mut untyped_methods: Vec<CDefl> = Vec::new();
    let mut has_explicit_interface = false;
    let mut var_types: HashMap<SmolStr, CType> = HashMap::new();

    for stmt in stmts {
        match stmt {
            ImperativeStatement::Rule { name, guard, body_pos, body, .. } => {
                let body_stmts = convert_action_stmts_to_stmts(body);
                let name_expr = Some(CExpr::Lit(
                    bsc_syntax::literal::Literal::String(name.name().to_string()),
                    name.position(),
                ));
                let qualifiers = if let Some(g) = guard {
                    vec![CQual::Filter(g)]
                } else {
                    vec![CQual::Filter(CExpr::Con(
                        Id::qualified("Prelude", "True", Position::unknown()),
                        vec![],
                        Span::DUMMY,
                    ))]
                };
                rules.push(CRule::Rule {
                    pragmas: vec![],
                    name: name_expr,
                    qualifiers,
                    body: CExpr::Action(body_pos, body_stmts),
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::MethodDefn {
                pos: method_pos,
                name,
                params,
                guard,
                body,
                ret_type,
            } => {
                let is_action = ret_type.as_ref().map(|t| {
                    if let CType::Con(tycon) = t {
                        tycon.name.name() == "Action"
                    } else {
                        false
                    }
                }).unwrap_or(false);

                let body_expr = if is_action {
                    let body_stmts = convert_action_stmts_to_stmts(body);
                    CExpr::Action(method_pos, body_stmts)
                } else {
                    convert_stmts_to_expr(body)
                };

                let patterns: Vec<CPat> = params.iter().map(|(n, _)| CPat::Var(n.clone())).collect();
                let param_types: Vec<Option<CType>> = params.into_iter().map(|(_, t)| t).collect();
                let all_types_present = ret_type.is_some() && param_types.iter().all(|t| t.is_some());

                let method_type = if all_types_present {
                    let base_type = ret_type.unwrap();
                    let param_types: Vec<CType> = param_types.into_iter().map(|t| t.unwrap()).collect();
                    if param_types.is_empty() {
                        base_type
                    } else {
                        param_types.into_iter().rev().fold(base_type, |acc, param_ty| {
                            crate::make_fn_type(param_ty, acc)
                        })
                    }
                } else {
                    CType::Var(Id::new(SmolStr::new_static("_"), Position::unknown()))
                };

                methods.push(CField {
                    name,
                    pragmas: None,
                    ty: CQType {
                        context: vec![],
                        ty: method_type,
                        span: Span::DUMMY,
                    },
                    default: vec![CClause {
                        patterns,
                        qualifiers: guard.map(|g| vec![CQual::Filter(g)]).unwrap_or_default(),
                        body: body_expr,
                        span: Span::DUMMY,
                    }],
                    orig_type: None,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::Bind { name, ty, expr } => {
                let mut name_with_keep = name.clone();
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

                let instance_name_expr = CExpr::Apply(
                    Box::new(CExpr::Var(Id::qualified("Prelude", "primGetName", Position::unknown()))),
                    vec![CExpr::Var(name_with_keep.clone())],
                    Span::DUMMY,
                );

                if let Some(bind_type) = ty {
                    module_items.push(CModuleItem::Stmt(CStmt::BindT {
                        pattern: CPat::Var(name_with_keep),
                        instance_name: Some(Box::new(instance_name_expr)),
                        pragmas: vec![],
                        ty: CQType {
                            context: vec![],
                            ty: bind_type,
                            span: Span::DUMMY,
                        },
                        expr,
                        span: Span::DUMMY,
                    }));
                } else {
                    module_items.push(CModuleItem::Stmt(CStmt::Bind {
                        pattern: CPat::Var(name_with_keep),
                        instance_name: Some(Box::new(instance_name_expr)),
                        pragmas: vec![],
                        expr,
                        span: Span::DUMMY,
                    }));
                }
            }
            ImperativeStatement::Decl { name, ty, init } => {
                let mut name_with_keep = name.clone();
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

                let decl_type = ty.clone().unwrap_or_else(|| {
                    CType::Var(Id::new(SmolStr::new_static("_"), Position::unknown()))
                });

                if let Some(ref t) = ty {
                    var_types.insert(name.name().clone(), t.clone());
                }

                let body_expr = if let Some(expr) = init {
                    expr
                } else {
                    let pos = name.position().clone();
                    CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primUninitialized", Position::unknown()))),
                        vec![
                            CExpr::Lit(Literal::Position, pos.clone()),
                            CExpr::Lit(Literal::String(name.name().to_string()), pos),
                        ],
                        Span::DUMMY,
                    )
                };

                module_items.push(CModuleItem::Stmt(CStmt::LetSeq(
                    vec![CDefl::ValueSign(
                        CDef::Untyped {
                            name: name_with_keep,
                            ty: CQType {
                                context: vec![],
                                ty: decl_type,
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: body_expr,
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    )],
                    Span::DUMMY,
                )));
            }
            ImperativeStatement::ArrayDecl {
                name,
                base_type,
                dimensions,
                init,
                init_pos,
            } => {
                let pos_for_check = init_pos.unwrap_or_else(|| name.position());
                let array_expr = build_array_init_expr(&dimensions, init, pos_for_check, None);

                let mut name_with_keep = name.clone();
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

                let array_type = build_array_type(base_type, dimensions.len());

                var_types.insert(name.name().clone(), array_type.clone());

                module_items.push(CModuleItem::Stmt(CStmt::LetSeq(
                    vec![CDefl::ValueSign(
                        CDef::Untyped {
                            name: name_with_keep,
                            ty: CQType {
                                context: vec![],
                                ty: array_type,
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: array_expr,
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    )],
                    Span::DUMMY,
                )));
            }
            ImperativeStatement::Let { name, expr } => {
                let mut name_with_keep = name;
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);
                module_items.push(CModuleItem::Stmt(CStmt::LetSeq(
                    vec![CDefl::Value(
                        name_with_keep,
                        vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: expr,
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    )],
                    Span::DUMMY,
                )));
            }
            ImperativeStatement::LetBind { name, expr } => {
                let mut name_with_keep = name.clone();
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

                let instance_name_expr = CExpr::Apply(
                    Box::new(CExpr::Var(Id::qualified("Prelude", "primGetName", Position::unknown()))),
                    vec![CExpr::Var(name_with_keep.clone())],
                    Span::DUMMY,
                );

                module_items.push(CModuleItem::Stmt(CStmt::Bind {
                    pattern: CPat::Var(name_with_keep),
                    instance_name: Some(Box::new(instance_name_expr)),
                    pragmas: vec![],
                    expr,
                    span: Span::DUMMY,
                }));
            }
            ImperativeStatement::InterfaceExpr { ty, members } => {
                has_explicit_interface = true;
                let ifc_expr = convert_interface_expr_with_pos_and_type(pos.clone(), ty, members);
                module_items.push(CModuleItem::Interface(ifc_expr));
            }
            ImperativeStatement::NakedExpr(expr) => {
                let instance_name = get_naked_expr_name(&expr);
                module_items.push(CModuleItem::Stmt(CStmt::Expr {
                    instance_name: instance_name.map(Box::new),
                    expr,
                    span: Span::DUMMY,
                }));
            }
            ImperativeStatement::Update { pos: _, lhs, rhs } => {
                if let Some((var_name, update_expr)) = build_nested_update(&lhs, rhs) {
                    let var_type = var_types.get(var_name.name()).cloned();
                    let defl = if let Some(ty) = var_type {
                        CDefl::ValueSign(
                            CDef::Untyped {
                                name: var_name,
                                ty: CQType {
                                    context: vec![],
                                    ty,
                                    span: Span::DUMMY,
                                },
                                clauses: vec![CClause {
                                    patterns: vec![],
                                    qualifiers: vec![],
                                    body: update_expr,
                                    span: Span::DUMMY,
                                }],
                                span: Span::DUMMY,
                            },
                            vec![],
                            Span::DUMMY,
                        )
                    } else {
                        CDefl::Value(
                            var_name,
                            vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: update_expr,
                                span: Span::DUMMY,
                            }],
                            vec![],
                            Span::DUMMY,
                        )
                    };
                    module_items.push(CModuleItem::Stmt(CStmt::LetSeq(
                        vec![defl],
                        Span::DUMMY,
                    )));
                }
            }
            ImperativeStatement::For { pos, init, cond, update, body } => {
                let for_stmts = convert_for_loop_to_module_stmts(pos, init, cond, update, body, &var_types);
                for stmt in for_stmts {
                    module_items.push(CModuleItem::Stmt(stmt));
                }
            }
            ImperativeStatement::FunctionDefn {
                name,
                ret_type,
                params,
                provisos,
                body,
                ..
            } => {
                let body_expr = convert_stmts_to_expr(body);
                let patterns: Vec<CPat> = params.iter().map(|(n, _)| CPat::Var(n.clone())).collect();
                let clauses = vec![CClause {
                    patterns,
                    qualifiers: vec![],
                    body: body_expr,
                    span: Span::DUMMY,
                }];
                let defl = if let Some(func_type) = build_function_type(params, provisos, ret_type) {
                    CDefl::ValueSign(
                        CDef::Untyped {
                            name,
                            ty: func_type,
                            clauses,
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    )
                } else {
                    CDefl::Value(
                        name,
                        clauses,
                        vec![],
                        Span::DUMMY,
                    )
                };
                module_items.push(CModuleItem::Stmt(CStmt::LetRec(
                    vec![defl],
                    Span::DUMMY,
                )));
            }
            ImperativeStatement::SubinterfaceMethod { name, expr, .. } => {
                untyped_methods.push(CDefl::Value(
                    name,
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                ));
            }
            ImperativeStatement::SubinterfaceBody { name, ty, members, .. } => {
                let sub_ifc_ty = ty.and_then(|t| {
                    if let CType::Con(tycon) = &t {
                        Some(Id::unpositioned(tycon.name().name().clone()))
                    } else if let CType::Apply(base, _, _) = &t {
                        if let CType::Con(tycon) = base.as_ref() {
                            Some(Id::unpositioned(tycon.name().name().clone()))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                });
                let sub_ifc_expr = convert_interface_members_to_struct(members, sub_ifc_ty);
                untyped_methods.push(CDefl::Value(
                    name,
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: sub_ifc_expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                ));
            }
            _ => {}
        }
    }

    if !rules.is_empty() {
        let rules_expr = CExpr::Rules(vec![], rules, Span::DUMMY);
        let add_rules_call = CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "addRules", Position::unknown()))),
            vec![rules_expr],
            Span::DUMMY,
        );
        let mut add_rules_id = Id::new(SmolStr::new_static("_add_rules"), Position::unknown());
        add_rules_id.add_prop(bsc_syntax::id::IdProp::Hide);
        let get_name_call = CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "primGetName", Position::unknown()))),
            vec![CExpr::Var(add_rules_id)],
            Span::DUMMY,
        );
        module_items.push(CModuleItem::Stmt(CStmt::Expr {
            instance_name: Some(Box::new(get_name_call)),
            expr: add_rules_call,
            span: Span::DUMMY,
        }));
    }

    if !methods.is_empty() || !untyped_methods.is_empty() {
        has_explicit_interface = true;
        let mut defls: Vec<CDefl> = methods
            .iter()
            .map(|m| {
                CDefl::ValueSign(
                    CDef::Untyped {
                        name: m.name.clone(),
                        ty: m.ty.clone(),
                        clauses: m.default.clone(),
                        span: Span::DUMMY,
                    },
                    vec![],
                    Span::DUMMY,
                )
            })
            .collect();
        defls.extend(untyped_methods);
        let ifc_expr = CExpr::Interface(pos.clone(), ifc_id.clone(), defls);
        module_items.push(CModuleItem::Interface(ifc_expr));
    }

    if !has_explicit_interface {
        let ifc_expr = CExpr::Interface(pos.clone(), ifc_id, vec![]);
        module_items.push(CModuleItem::Interface(ifc_expr));
    }

    CExpr::Module(pos, module_items)
}

fn get_innermost_index_position(expr: &CExpr) -> Position {
    match expr {
        CExpr::Index { expr: base, .. } => {
            match base.as_ref() {
                CExpr::Index { .. } => get_innermost_index_position(base),
                _ => get_expr_position(base),
            }
        }
        _ => Position::unknown(),
    }
}

fn build_nested_update(lhs: &CExpr, value: CExpr) -> Option<(Id, CExpr)> {
    match lhs {
        CExpr::Var(id) => Some((id.clone(), value)),
        CExpr::Index { expr: base, index, .. } => {
            let update_pos = get_innermost_index_position(lhs);
            let inner_update = CExpr::Apply(
                Box::new(CExpr::Var(Id::new(
                    SmolStr::new_static("primUpdateFn"),
                    update_pos.clone(),
                ))),
                vec![
                    CExpr::Lit(Literal::Position, update_pos),
                    (**base).clone(),
                    (**index).clone(),
                    value,
                ],
                Span::DUMMY,
            );
            build_nested_update(base, inner_update)
        }
        _ => None,
    }
}

fn extract_update_var(expr: &CExpr) -> Option<Id> {
    match expr {
        CExpr::Var(id) => Some(id.clone()),
        CExpr::Index { expr: base, .. } => extract_update_var(base),
        CExpr::Select(base, _, _) => extract_update_var(base),
        _ => None,
    }
}

fn convert_interface_expr_with_pos_and_type(pos: Position, ty: Option<CType>, members: Vec<ImperativeStatement>) -> CExpr {
    let mut defls = Vec::new();

    for member in members {
        match member {
            ImperativeStatement::MethodDefn { name, body, params, ret_type, .. } => {
                let body_expr = convert_stmts_to_expr(body);
                let patterns: Vec<CPat> = params.iter().map(|(n, _)| CPat::Var(n.clone())).collect();
                let param_types: Vec<Option<CType>> = params.into_iter().map(|(_, t)| t).collect();

                let all_types_present = ret_type.is_some() && param_types.iter().all(|t| t.is_some());

                if all_types_present {
                    let base_type = ret_type.unwrap();
                    let param_types: Vec<CType> = param_types.into_iter().map(|t| t.unwrap()).collect();
                    let method_type = if param_types.is_empty() {
                        base_type
                    } else {
                        param_types.into_iter().rev().fold(base_type, |acc, param_ty| {
                            crate::make_fn_type(param_ty, acc)
                        })
                    };

                    defls.push(CDefl::ValueSign(
                        CDef::Untyped {
                            name,
                            ty: CQType {
                                context: vec![],
                                ty: method_type,
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns,
                                qualifiers: vec![],
                                body: body_expr,
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    ));
                } else {
                    defls.push(CDefl::Value(
                        name,
                        vec![CClause {
                            patterns,
                            qualifiers: vec![],
                            body: body_expr,
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    ));
                }
            }
            ImperativeStatement::InterfaceExpr { ty: inner_ty, members: inner_members, .. } => {
                let inner_expr = convert_interface_expr_with_pos_and_type(pos.clone(), inner_ty, inner_members);
                defls.push(CDefl::Value(
                    Id::new(SmolStr::new_static("_sub"), Position::unknown()),
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: inner_expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                ));
            }
            ImperativeStatement::Equal { name, expr } => {
                defls.push(CDefl::Value(
                    name,
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                ));
            }
            _ => {}
        }
    }

    let type_name = ty.and_then(|t| {
        if let CType::Con(tycon) = t {
            Some(Id::unpositioned(tycon.name().name().clone()))
        } else {
            None
        }
    });

    CExpr::Interface(pos, type_name, defls)
}

fn convert_interface_expr(members: Vec<ImperativeStatement>) -> CExpr {
    convert_interface_expr_with_pos_and_type(Position::unknown(), None, members)
}

fn convert_interface_members_to_struct(members: Vec<ImperativeStatement>, type_name: Option<Id>) -> CExpr {
    let mut defls = Vec::new();

    for member in members {
        match member {
            ImperativeStatement::MethodDefn { name, body, params, ret_type, .. } => {
                let body_expr = convert_stmts_to_expr(body);
                let patterns: Vec<CPat> = params.iter().map(|(n, _)| CPat::Var(n.clone())).collect();
                let param_types: Vec<Option<CType>> = params.into_iter().map(|(_, t)| t).collect();

                let all_types_present = ret_type.is_some() && param_types.iter().all(|t| t.is_some());

                if all_types_present {
                    let base_type = ret_type.unwrap();
                    let param_types: Vec<CType> = param_types.into_iter().map(|t| t.unwrap()).collect();
                    let method_type = if param_types.is_empty() {
                        base_type
                    } else {
                        param_types.into_iter().rev().fold(base_type, |acc, param_ty| {
                            crate::make_fn_type(param_ty, acc)
                        })
                    };

                    defls.push(CDefl::ValueSign(
                        CDef::Untyped {
                            name,
                            ty: CQType {
                                context: vec![],
                                ty: method_type,
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns,
                                qualifiers: vec![],
                                body: body_expr,
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    ));
                } else {
                    defls.push(CDefl::Value(
                        name,
                        vec![CClause {
                            patterns,
                            qualifiers: vec![],
                            body: body_expr,
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    ));
                }
            }
            ImperativeStatement::SubinterfaceBody { name, ty: inner_ty, members: inner_members, .. } => {
                let inner_type_name = inner_ty.and_then(|t| {
                    if let CType::Con(tycon) = &t {
                        Some(Id::unpositioned(tycon.name().name().clone()))
                    } else if let CType::Apply(base, _, _) = &t {
                        if let CType::Con(tycon) = base.as_ref() {
                            Some(Id::unpositioned(tycon.name().name().clone()))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                });
                let inner_expr = convert_interface_members_to_struct(inner_members, inner_type_name);
                defls.push(CDefl::Value(
                    name,
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: inner_expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                ));
            }
            _ => {}
        }
    }

    CExpr::Interface(Position::unknown(), type_name, defls)
}

fn collect_updated_vars_from_stmts(stmts: &[ImperativeStatement]) -> Vec<Id> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            ImperativeStatement::Equal { name, .. } => {
                if !result.iter().any(|v: &Id| v.name() == name.name()) {
                    result.push(name.clone());
                }
            }
            ImperativeStatement::Update { lhs, .. } => {
                if let Some(var_name) = extract_update_var(lhs) {
                    if !result.iter().any(|v: &Id| v.name() == var_name.name()) {
                        result.push(var_name);
                    }
                }
            }
            ImperativeStatement::For { body, update, .. } => {
                result.extend(collect_updated_vars_from_stmts(body));
                result.extend(collect_updated_vars_from_stmts(update));
            }
            ImperativeStatement::While { body, .. } => {
                result.extend(collect_updated_vars_from_stmts(body));
            }
            ImperativeStatement::If { then_branch, else_branch, .. } => {
                result.extend(collect_updated_vars_from_stmts(then_branch));
                if let Some(else_stmts) = else_branch {
                    result.extend(collect_updated_vars_from_stmts(else_stmts));
                }
            }
            ImperativeStatement::BeginEnd { stmts, .. } => {
                result.extend(collect_updated_vars_from_stmts(stmts));
            }
            _ => {}
        }
    }
    result
}

fn convert_for_loop_to_expr_pure(
    pos: Position,
    init: Vec<ImperativeStatement>,
    cond: CExpr,
    update: Vec<ImperativeStatement>,
    body: Vec<ImperativeStatement>,
    var_types: &std::collections::HashMap<SmolStr, CType>,
) -> Vec<CDefl> {
    let mut all_stmts = body.clone();
    all_stmts.extend(update.clone());
    let updated_vars: Vec<Id> = collect_updated_vars_from_stmts(&all_stmts);

    if updated_vars.is_empty() {
        return Vec::new();
    }

    let integer_ty = CType::Con(Id::new(SmolStr::new_static("Integer"), Position::unknown()).into());

    let loop_vars: Vec<(Id, CType)> = init.iter().filter_map(|stmt| {
        if let ImperativeStatement::Decl { name, ty, .. } = stmt {
            let ty = ty.clone().unwrap_or_else(|| integer_ty.clone());
            Some((name.clone(), ty))
        } else {
            None
        }
    }).collect();

    let updated_vars_with_types: Vec<(Id, CType)> = updated_vars.iter().map(|v| {
        let ty = loop_vars.iter()
            .find(|(loop_v, _)| loop_v.name() == v.name())
            .map(|(_, t)| t.clone())
            .or_else(|| var_types.get(v.name()).cloned())
            .unwrap_or_else(|| {
                CType::Var(Id::new(SmolStr::new_static("a"), Position::unknown()))
            });
        (v.clone(), ty)
    }).collect();

    let all_vars: Vec<(Id, CType)> = {
        let mut result = updated_vars_with_types.clone();
        for (loop_var, loop_ty) in &loop_vars {
            if !result.iter().any(|(v, _)| v.name() == loop_var.name()) {
                result.push((loop_var.clone(), loop_ty.clone()));
            }
        }
        result
    };

    let tuple_type = build_tuple_type(&all_vars);
    let fn_type = crate::make_fn_type(tuple_type.clone(), tuple_type.clone());

    let f_id = Id::new(SmolStr::new_static("_f__"), pos.clone());
    let tuple_pattern = build_tuple_pattern(&all_vars);
    let result_tuple = build_tuple_expr(&all_vars);

    let recursive_call = CExpr::Apply(
        Box::new(CExpr::Var(f_id.clone())),
        vec![build_tuple_expr(&all_vars)],
        Span::DUMMY,
    );

    let mut while_body_stmts = body.clone();
    while_body_stmts.extend(update.clone());
    while_body_stmts.push(ImperativeStatement::NakedExpr(recursive_call.clone()));

    let mut while_var_types = var_types.clone();
    for (v, t) in &loop_vars {
        while_var_types.insert(v.name().clone(), t.clone());
    }
    for (v, t) in &updated_vars_with_types {
        while_var_types.insert(v.name().clone(), t.clone());
    }

    let then_body = convert_stmts_to_expr_with_types(while_body_stmts, &while_var_types);

    let if_expr = CExpr::If(
        pos.clone(),
        Box::new(cond),
        Box::new(then_body),
        Box::new(result_tuple.clone()),
    );

    let f_def = CDef::Untyped {
        name: f_id.clone(),
        ty: CQType {
            context: vec![],
            ty: fn_type,
            span: Span::DUMMY,
        },
        clauses: vec![CClause {
            patterns: vec![tuple_pattern.clone()],
            qualifiers: vec![],
            body: if_expr,
            span: Span::DUMMY,
        }],
        span: Span::DUMMY,
    };

    let letrec_expr = CExpr::LetRec(
        vec![CDefl::ValueSign(f_def, vec![], Span::DUMMY)],
        Box::new(CExpr::Apply(
            Box::new(CExpr::Var(f_id)),
            vec![build_tuple_expr(&all_vars)],
            Span::DUMMY,
        )),
        Span::DUMMY,
    );

    let mut inner_result_id = Id::new(SmolStr::new_static("_theResult__"), pos.clone());
    inner_result_id.add_prop(bsc_syntax::id::IdProp::Renaming);

    let inner_result_def = CDefl::ValueSign(
        CDef::Untyped {
            name: inner_result_id.clone(),
            ty: CQType {
                context: vec![],
                ty: tuple_type,
                span: Span::DUMMY,
            },
            clauses: vec![CClause {
                patterns: vec![],
                qualifiers: vec![],
                body: letrec_expr,
                span: Span::DUMMY,
            }],
            span: Span::DUMMY,
        },
        vec![],
        Span::DUMMY,
    );

    let inner_match = CDefl::Match(
        tuple_pattern,
        CExpr::Var(inner_result_id),
        Span::DUMMY,
    );

    let first_updated_var = &updated_vars[0];
    let inner_body = CExpr::Var(first_updated_var.clone());

    let mut inner_defls: Vec<CDefl> = Vec::new();
    for stmt in &init {
        if let ImperativeStatement::Decl { name, init: Some(expr), ty } = stmt {
            let mut name_with_keep = name.clone();
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

            let ty = ty.clone().unwrap_or_else(|| integer_ty.clone());

            inner_defls.push(CDefl::ValueSign(
                CDef::Untyped {
                    name: name_with_keep,
                    ty: CQType {
                        context: vec![],
                        ty,
                        span: Span::DUMMY,
                    },
                    clauses: vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr.clone(),
                        span: Span::DUMMY,
                    }],
                    span: Span::DUMMY,
                },
                vec![],
                Span::DUMMY,
            ));
        }
    }

    inner_defls.push(inner_result_def);
    inner_defls.push(inner_match);

    let inner_letseq = CExpr::LetSeq(inner_defls, Box::new(inner_body), Span::DUMMY);

    let outer_result_type = updated_vars_with_types[0].1.clone();
    let mut outer_result_id = Id::new(SmolStr::new_static("_theResult__"), pos);
    outer_result_id.add_prop(bsc_syntax::id::IdProp::Renaming);

    let outer_result_def = CDefl::ValueSign(
        CDef::Untyped {
            name: outer_result_id.clone(),
            ty: CQType {
                context: vec![],
                ty: outer_result_type,
                span: Span::DUMMY,
            },
            clauses: vec![CClause {
                patterns: vec![],
                qualifiers: vec![],
                body: inner_letseq,
                span: Span::DUMMY,
            }],
            span: Span::DUMMY,
        },
        vec![],
        Span::DUMMY,
    );

    let outer_match = CDefl::Match(
        CPat::Var(first_updated_var.clone()),
        CExpr::Var(outer_result_id),
        Span::DUMMY,
    );

    vec![outer_result_def, outer_match]
}

pub fn convert_module_body_for_instance(stmts: Vec<ImperativeStatement>, pos: Position, ifc: &CType) -> CExpr {
    let ifc_id = extract_interface_id(ifc);
    convert_module_body_to_expr(stmts, pos, ifc_id)
}

pub fn convert_stmts_to_expr(stmts: Vec<ImperativeStatement>) -> CExpr {
    convert_stmts_to_expr_with_types(stmts, &std::collections::HashMap::new())
}

pub fn convert_stmts_to_expr_with_types(stmts: Vec<ImperativeStatement>, var_types: &std::collections::HashMap<SmolStr, CType>) -> CExpr {
    if stmts.is_empty() {
        return CExpr::Struct(
            Some(true),
            Id::qualified("Prelude", "PrimUnit", Position::unknown()),
            vec![],
            Span::DUMMY,
        );
    }

    let mut var_types = var_types.clone();
    for stmt in &stmts {
        if let ImperativeStatement::Decl { name, ty: Some(ty), .. } = stmt {
            var_types.insert(name.name().clone(), ty.clone());
        }
    }

    let mut stmts = stmts;
    let last = stmts.pop();

    let mut result = match last {
        Some(ImperativeStatement::Return { expr, .. }) => {
            expr.unwrap_or_else(|| {
                CExpr::Struct(
                    Some(true),
                    Id::qualified("Prelude", "PrimUnit", Position::unknown()),
                    vec![],
                    Span::DUMMY,
                )
            })
        }
        Some(ImperativeStatement::NakedExpr(expr)) => expr,
        Some(ImperativeStatement::Case { pos, subject, arms, default }) => {
            convert_case_to_expr(pos, subject, arms, default)
        }
        Some(ImperativeStatement::CaseTagged { pos, subject, arms, default }) => {
            convert_case_tagged_to_expr(pos, subject, arms, default)
        }
        Some(ImperativeStatement::If { pos, cond, then_branch, else_branch }) => {
            let then_expr = convert_stmts_to_expr(then_branch);
            let else_expr = else_branch
                .map(convert_stmts_to_expr)
                .unwrap_or_else(|| {
                    CExpr::Struct(
                        Some(true),
                        Id::qualified("Prelude", "PrimUnit", Position::unknown()),
                        vec![],
                        Span::DUMMY,
                    )
                });
            CExpr::If(pos, Box::new(cond), Box::new(then_expr), Box::new(else_expr))
        }
        Some(ImperativeStatement::BeginEnd { stmts: inner_stmts, .. }) => {
            convert_stmts_to_expr(inner_stmts)
        }
        Some(other) => {
            stmts.push(other);
            CExpr::Struct(
                Some(true),
                Id::qualified("Prelude", "PrimUnit", Position::unknown()),
                vec![],
                Span::DUMMY,
            )
        }
        None => {
            CExpr::Struct(
                Some(true),
                Id::qualified("Prelude", "PrimUnit", Position::unknown()),
                vec![],
                Span::DUMMY,
            )
        }
    };

    let mut pending_defls: Vec<CDefl> = Vec::new();
    let mut local_var_types = var_types.clone();

    for stmt in &stmts {
        if let ImperativeStatement::Decl { name, ty: Some(t), .. } = stmt {
            local_var_types.insert(name.name().clone(), t.clone());
        }
    }

    for stmt in stmts.into_iter().rev() {
        if let Some(defl) = stmt_to_defl(&stmt, &local_var_types) {
            pending_defls.push(defl);
        } else if let ImperativeStatement::For { pos, init, cond, update, body } = stmt {
            let for_defls = convert_for_loop_to_expr_pure(pos, init, cond, update, body, &local_var_types);
            for defl in for_defls.into_iter().rev() {
                pending_defls.push(defl);
            }
        } else {
            if !pending_defls.is_empty() {
                pending_defls.reverse();
                result = clet_seq(pending_defls, result);
                pending_defls = Vec::new();
            }
            result = wrap_non_defl_stmt(stmt, result, &local_var_types);
        }
    }

    if !pending_defls.is_empty() {
        pending_defls.reverse();
        result = clet_seq(pending_defls, result);
    }

    result
}

fn stmt_to_defl(stmt: &ImperativeStatement, var_types: &std::collections::HashMap<SmolStr, CType>) -> Option<CDefl> {
    match stmt {
        ImperativeStatement::Let { name, expr } => {
            let mut name_with_keep = name.clone();
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);
            Some(CDefl::Value(
                name_with_keep,
                vec![CClause {
                    patterns: vec![],
                    qualifiers: vec![],
                    body: expr.clone(),
                    span: Span::DUMMY,
                }],
                vec![],
                Span::DUMMY,
            ))
        }
        ImperativeStatement::Decl { name, ty, init } => {
            if let Some(expr) = init {
                let mut name_with_keep = name.clone();
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

                let defl = if let Some(t) = ty {
                    CDefl::ValueSign(
                        CDef::Untyped {
                            name: name_with_keep,
                            ty: CQType {
                                context: vec![],
                                ty: t.clone(),
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: expr.clone(),
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    )
                } else {
                    CDefl::Value(
                        name_with_keep,
                        vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: expr.clone(),
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    )
                };
                Some(defl)
            } else {
                None
            }
        }
        ImperativeStatement::Equal { name, expr } => {
            let mut name_with_keep = name.clone();
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);
            let cls = vec![CClause {
                patterns: vec![],
                qualifiers: vec![],
                body: expr.clone(),
                span: Span::DUMMY,
            }];
            if let Some(t) = var_types.get(name.name()) {
                Some(CDefl::ValueSign(
                    CDef::Untyped {
                        name: name_with_keep,
                        ty: CQType {
                            context: vec![],
                            ty: t.clone(),
                            span: Span::DUMMY,
                        },
                        clauses: cls,
                        span: Span::DUMMY,
                    },
                    vec![],
                    Span::DUMMY,
                ))
            } else {
                Some(CDefl::Value(
                    name_with_keep,
                    cls,
                    vec![],
                    Span::DUMMY,
                ))
            }
        }
        ImperativeStatement::ArrayDecl {
            name,
            base_type,
            dimensions,
            init,
            init_pos,
        } => {
            let pos_for_check = init_pos.clone().unwrap_or_else(|| name.position());
            let array_expr = build_array_init_expr(dimensions, init.clone(), pos_for_check, None);

            let mut name_with_keep = name.clone();
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

            let array_type = build_array_type(base_type.clone(), dimensions.len());

            Some(CDefl::ValueSign(
                CDef::Untyped {
                    name: name_with_keep,
                    ty: CQType {
                        context: vec![],
                        ty: array_type,
                        span: Span::DUMMY,
                    },
                    clauses: vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: array_expr,
                        span: Span::DUMMY,
                    }],
                    span: Span::DUMMY,
                },
                vec![],
                Span::DUMMY,
            ))
        }
        _ => None,
    }
}

fn make_result_expr(pos: Position, updated_vars: &[Id], inner_expr: CExpr, rest: CExpr, var_types: &std::collections::HashMap<SmolStr, CType>) -> CExpr {
    if updated_vars.is_empty() {
        return rest;
    }

    let mut result_id = Id::new(SmolStr::new_static("_theResult__"), pos.clone());
    result_id.add_prop(bsc_syntax::id::IdProp::Renaming);

    let first_var = &updated_vars[0];

    let var_type = var_types.get(first_var.name())
        .cloned()
        .unwrap_or_else(|| CType::Var(Id::new(SmolStr::new_static("a"), Position::unknown())));

    let result_def = CDefl::ValueSign(
        CDef::Untyped {
            name: result_id.clone(),
            ty: CQType {
                context: vec![],
                ty: var_type,
                span: Span::DUMMY,
            },
            clauses: vec![CClause {
                patterns: vec![],
                qualifiers: vec![],
                body: inner_expr,
                span: Span::DUMMY,
            }],
            span: Span::DUMMY,
        },
        vec![],
        Span::DUMMY,
    );

    let match_defl = CDefl::Match(
        CPat::Var(first_var.clone()),
        CExpr::Var(result_id),
        Span::DUMMY,
    );

    clet_seq(vec![result_def, match_defl], rest)
}

fn convert_if_to_expr_with_updated_vars(
    pos: Position,
    cond: CExpr,
    then_branch: Vec<ImperativeStatement>,
    else_branch: Option<Vec<ImperativeStatement>>,
    updated_vars: &[Id],
    var_types: &std::collections::HashMap<SmolStr, CType>,
) -> CExpr {
    let result_var = if !updated_vars.is_empty() {
        Some(CExpr::Var(updated_vars[0].clone()))
    } else {
        None
    };

    let then_stmts = if let Some(ref result) = result_var {
        let mut stmts = then_branch;
        stmts.push(ImperativeStatement::NakedExpr(result.clone()));
        stmts
    } else {
        then_branch
    };

    let then_expr = convert_stmts_to_expr_with_types(then_stmts, var_types);

    let else_expr = if let Some(else_stmts) = else_branch {
        let stmts = if let Some(ref result) = result_var {
            let mut s = else_stmts;
            s.push(ImperativeStatement::NakedExpr(result.clone()));
            s
        } else {
            else_stmts
        };
        convert_stmts_to_expr_with_types(stmts, var_types)
    } else {
        if let Some(ref result) = result_var {
            result.clone()
        } else {
            CExpr::Struct(
                Some(true),
                Id::qualified("Prelude", "PrimUnit", Position::unknown()),
                vec![],
                Span::DUMMY,
            )
        }
    };

    CExpr::If(pos, Box::new(cond), Box::new(then_expr), Box::new(else_expr))
}

fn wrap_non_defl_stmt(stmt: ImperativeStatement, rest: CExpr, var_types: &std::collections::HashMap<SmolStr, CType>) -> CExpr {
    match stmt {
        ImperativeStatement::If {
            pos,
            cond,
            then_branch,
            else_branch,
        } => {
            let mut all_stmts = then_branch.clone();
            if let Some(ref else_stmts) = else_branch {
                all_stmts.extend(else_stmts.clone());
            }
            let updated_vars = collect_updated_vars_from_stmts(&all_stmts);

            if updated_vars.is_empty() {
                let then_expr = convert_stmts_to_expr_with_types(then_branch, var_types);
                let else_expr = else_branch
                    .map(|s| convert_stmts_to_expr_with_types(s, var_types))
                    .unwrap_or_else(|| {
                        CExpr::Struct(
                            Some(true),
                            Id::qualified("Prelude", "PrimUnit", Position::unknown()),
                            vec![],
                            Span::DUMMY,
                        )
                    });
                CExpr::LetSeq(
                    vec![],
                    Box::new(CExpr::If(pos, Box::new(cond), Box::new(then_expr), Box::new(else_expr))),
                    Span::DUMMY,
                )
            } else {
                let if_expr = convert_if_to_expr_with_updated_vars(
                    pos.clone(), cond, then_branch, else_branch, &updated_vars, var_types
                );
                make_result_expr(pos, &updated_vars, if_expr, rest, var_types)
            }
        }
        ImperativeStatement::For { pos, init, cond, update, body } => {
            let for_stmts = convert_for_loop_to_cstmts(pos, init, cond, update, body);
            let for_defl = for_stmts.into_iter().filter_map(|s| match s {
                CStmt::LetSeq(defls, _) => Some(defls),
                _ => None,
            }).flatten().collect::<Vec<_>>();
            CExpr::LetSeq(for_defl, Box::new(rest), Span::DUMMY)
        }
        ImperativeStatement::Case { pos, subject, arms, default } => {
            let case_expr = convert_case_to_expr(pos, subject, arms, default);
            CExpr::LetSeq(
                vec![],
                Box::new(case_expr),
                Span::DUMMY,
            )
        }
        ImperativeStatement::CaseTagged { pos, subject, arms, default } => {
            let case_expr = convert_case_tagged_to_expr(pos, subject, arms, default);
            CExpr::LetSeq(
                vec![],
                Box::new(case_expr),
                Span::DUMMY,
            )
        }
        ImperativeStatement::BeginEnd { pos, stmts } => {
            let updated_vars = collect_updated_vars_from_stmts(&stmts);
            if updated_vars.is_empty() {
                let inner = convert_stmts_to_expr_with_types(stmts, var_types);
                CExpr::LetSeq(
                    vec![],
                    Box::new(inner),
                    Span::DUMMY,
                )
            } else {
                let result_var = CExpr::Var(updated_vars[0].clone());
                let mut inner_stmts = stmts;
                inner_stmts.push(ImperativeStatement::NakedExpr(result_var));
                let inner = convert_stmts_to_expr_with_types(inner_stmts, var_types);
                make_result_expr(pos, &updated_vars, inner, rest, var_types)
            }
        }
        _ => rest,
    }
}

fn wrap_stmt_around_expr(stmt: ImperativeStatement, rest: CExpr) -> CExpr {
    match stmt {
        ImperativeStatement::Let { name, expr } => {
            let mut name_with_keep = name;
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);
            CExpr::LetSeq(
                vec![CDefl::Value(
                    name_with_keep,
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                )],
                Box::new(rest),
                Span::DUMMY,
            )
        }
        ImperativeStatement::Decl { name, ty, init } => {
            if let Some(expr) = init {
                let mut name_with_keep = name;
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

                let defl = if let Some(t) = ty {
                    CDefl::ValueSign(
                        CDef::Untyped {
                            name: name_with_keep,
                            ty: CQType {
                                context: vec![],
                                ty: t,
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: expr,
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    )
                } else {
                    CDefl::Value(
                        name_with_keep,
                        vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: expr,
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    )
                };

                CExpr::LetSeq(
                    vec![defl],
                    Box::new(rest),
                    Span::DUMMY,
                )
            } else {
                rest
            }
        }
        ImperativeStatement::Equal { name, expr } => {
            CExpr::LetSeq(
                vec![CDefl::Value(
                    name,
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                )],
                Box::new(rest),
                Span::DUMMY,
            )
        }
        ImperativeStatement::Update { .. } => {
            rest
        }
        ImperativeStatement::If {
            pos,
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            let then_stmts = convert_action_stmts_to_stmts(then_branch);
            let then_expr = CExpr::Action(pos.clone(), then_stmts);
            let else_expr = else_branch
                .map(|stmts| {
                    let else_stmts = convert_action_stmts_to_stmts(stmts);
                    CExpr::Action(pos.clone(), else_stmts)
                })
                .unwrap_or_else(|| {
                    CExpr::Action(pos.clone(), vec![])
                });
            let if_expr = CExpr::If(pos, Box::new(cond), Box::new(then_expr), Box::new(else_expr));
            if matches!(
                rest,
                CExpr::Struct(Some(true), _, ref fields, _) if fields.is_empty()
            ) {
                if_expr
            } else {
                CExpr::LetSeq(
                    vec![CDefl::Value(
                        Id::new(SmolStr::new_static("_if_result"), Position::unknown()),
                        vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: if_expr,
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    )],
                    Box::new(rest),
                    Span::DUMMY,
                )
            }
        }
        ImperativeStatement::BeginEnd { stmts, .. } => {
            let inner = convert_stmts_to_expr(stmts);
            CExpr::LetSeq(
                vec![CDefl::Value(
                    Id::new(SmolStr::new_static("_block"), Position::unknown()),
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: inner,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                )],
                Box::new(rest),
                Span::DUMMY,
            )
        }
        ImperativeStatement::NakedExpr(expr) => {
            CExpr::LetSeq(
                vec![CDefl::Value(
                    Id::new(SmolStr::new_static("_"), Position::unknown()),
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                )],
                Box::new(rest),
                Span::DUMMY,
            )
        }
        _ => rest,
    }
}

fn convert_for_loop_to_cstmts(
    pos: Position,
    init: Vec<ImperativeStatement>,
    cond: CExpr,
    update: Vec<ImperativeStatement>,
    body: Vec<ImperativeStatement>,
) -> Vec<CStmt> {
    let mut result = Vec::new();

    let loop_vars: Vec<Id> = init
        .iter()
        .filter_map(|stmt| match stmt {
            ImperativeStatement::Decl { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();

    for stmt in &init {
        if let ImperativeStatement::Decl { name, init: Some(expr), ty } = stmt {
            let mut name_with_keep = name.clone();
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

            let ty = ty.clone().unwrap_or_else(|| {
                CType::Con(Id::new(SmolStr::new_static("Integer"), Position::unknown()).into())
            });

            result.push(CStmt::LetSeq(
                vec![CDefl::ValueSign(
                    CDef::Untyped {
                        name: name_with_keep,
                        ty: CQType {
                            context: vec![],
                            ty,
                            span: Span::DUMMY,
                        },
                        clauses: vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: expr.clone(),
                            span: Span::DUMMY,
                        }],
                        span: Span::DUMMY,
                    },
                    vec![],
                    Span::DUMMY,
                )],
                Span::DUMMY,
            ));
        }
    }

    let f_id = Id::new(SmolStr::new_static("_f__"), pos.clone());
    let result_id = Id::new(SmolStr::new_static("_theResult__"), pos.clone())
        .with_props(vec![
            bsc_syntax::id::IdProp::Renaming,
            bsc_syntax::id::IdProp::Keep,
            bsc_syntax::id::IdProp::DisplayName(SmolStr::new_static("Loop")),
        ]);

    let loop_var = loop_vars.first().cloned().unwrap_or_else(|| {
        Id::new(SmolStr::new_static("_loop_var_"), pos.clone())
    });

    let body_pos = Position::unknown();

    let mut body_action_stmts = convert_action_stmts_to_stmts(body.clone());
    body_action_stmts.push(CStmt::Expr {
        instance_name: None,
        expr: CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "return", Position::unknown()))),
            vec![CExpr::Struct(
                Some(true),
                Id::qualified("Prelude", "PrimUnit", Position::unknown()),
                vec![],
                Span::DUMMY,
            )],
            Span::DUMMY,
        ),
        span: Span::DUMMY,
    });

    let body_caction = CExpr::Action(body_pos, body_action_stmts);

    let mut while_body_stmts = vec![CStmt::Expr {
        instance_name: None,
        expr: body_caction,
        span: Span::DUMMY,
    }];

    for stmt in &update {
        if let ImperativeStatement::Equal { name, expr } = stmt {
            let mut name_with_keep = name.clone();
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);
            let ty = CType::Con(Id::new(SmolStr::new_static("Integer"), Position::unknown()).into());
            while_body_stmts.push(CStmt::LetSeq(
                vec![CDefl::ValueSign(
                    CDef::Untyped {
                        name: name_with_keep,
                        ty: CQType {
                            context: vec![],
                            ty,
                            span: Span::DUMMY,
                        },
                        clauses: vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: expr.clone(),
                            span: Span::DUMMY,
                        }],
                        span: Span::DUMMY,
                    },
                    vec![],
                    Span::DUMMY,
                )],
                Span::DUMMY,
            ));
        }
    }

    while_body_stmts.push(CStmt::Expr {
        instance_name: None,
        expr: CExpr::Apply(
            Box::new(CExpr::Var(f_id.clone())),
            vec![CExpr::Var(loop_var.clone())],
            Span::DUMMY,
        ),
        span: Span::DUMMY,
    });

    let else_body_stmts = vec![CStmt::Expr {
        instance_name: None,
        expr: CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "return", pos.clone()))),
            vec![CExpr::Var(loop_var.clone())],
            Span::DUMMY,
        ),
        span: Span::DUMMY,
    }];
    let else_body = CExpr::Do {
        recursive: false,
        stmts: else_body_stmts,
        span: Span::DUMMY,
    };

    let if_expr = CExpr::If(
        pos.clone(),
        Box::new(cond),
        Box::new(CExpr::Do {
            recursive: false,
            stmts: while_body_stmts,
            span: Span::DUMMY,
        }),
        Box::new(else_body),
    );

    let loop_var_ty = CType::Con(Id::new(SmolStr::new_static("Integer"), Position::unknown()).into());
    let action_value_ty = CType::Apply(
        Box::new(CType::Con(Id::qualified("Prelude", "ActionValue", Position::unknown()).into())),
        Box::new(loop_var_ty.clone()),
        Span::DUMMY,
    );
    let fn_type = crate::make_fn_type(loop_var_ty.clone(), action_value_ty);

    result.push(CStmt::LetRec(
        vec![CDefl::ValueSign(
            CDef::Untyped {
                name: f_id.clone(),
                ty: CQType {
                    context: vec![],
                    ty: fn_type,
                    span: Span::DUMMY,
                },
                clauses: vec![CClause {
                    patterns: vec![CPat::Var(loop_var.clone())],
                    qualifiers: vec![],
                    body: if_expr,
                    span: Span::DUMMY,
                }],
                span: Span::DUMMY,
            },
            vec![],
            Span::DUMMY,
        )],
        Span::DUMMY,
    ));

    result.push(CStmt::BindT {
        pattern: CPat::Var(result_id.clone()),
        instance_name: None,
        pragmas: vec![],
        ty: CQType {
            context: vec![],
            ty: loop_var_ty.clone(),
            span: Span::DUMMY,
        },
        expr: CExpr::Apply(
            Box::new(CExpr::Var(f_id)),
            vec![CExpr::Var(loop_var.clone())],
            Span::DUMMY,
        ),
        span: Span::DUMMY,
    });

    result.push(CStmt::LetSeq(
        vec![CDefl::Match(
            CPat::Var(loop_var),
            CExpr::Var(result_id),
            Span::DUMMY,
        )],
        Span::DUMMY,
    ));

    result.push(CStmt::Expr {
        instance_name: None,
        expr: CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "return", pos.clone()))),
            vec![CExpr::Struct(
                Some(true),
                Id::qualified("Prelude", "PrimUnit", pos),
                vec![],
                Span::DUMMY,
            )],
            Span::DUMMY,
        ),
        span: Span::DUMMY,
    });

    result
}

fn convert_for_loop_to_module_stmts(
    pos: Position,
    init: Vec<ImperativeStatement>,
    cond: CExpr,
    update: Vec<ImperativeStatement>,
    body: Vec<ImperativeStatement>,
    var_types: &std::collections::HashMap<SmolStr, CType>,
) -> Vec<CStmt> {
    let mut loop_vars: Vec<(Id, CType)> = Vec::new();
    for stmt in &init {
        if let ImperativeStatement::Decl { name, ty, .. } = stmt {
            let ty = ty.clone().unwrap_or_else(|| {
                CType::Apply(
                    Box::new(CType::Con(Id::qualified("Prelude", "Int", name.position()).into())),
                    Box::new(CType::Num(32, name.position())),
                    Span::DUMMY,
                )
            });
            loop_vars.push((name.clone(), ty));
        }
    }

    fn collect_updated_vars(stmts: &[ImperativeStatement], vars: &mut Vec<Id>) {
        for stmt in stmts {
            match stmt {
                ImperativeStatement::Equal { name, .. } => {
                    if !vars.iter().any(|v| v.name() == name.name()) {
                        vars.push(name.clone());
                    }
                }
                ImperativeStatement::Update { lhs, .. } => {
                    if let Some(var_name) = extract_update_var(lhs) {
                        if !vars.iter().any(|v| v.name() == var_name.name()) {
                            vars.push(var_name);
                        }
                    }
                }
                ImperativeStatement::For { body, .. } => {
                    collect_updated_vars(body, vars);
                }
                ImperativeStatement::While { body, .. } => {
                    collect_updated_vars(body, vars);
                }
                ImperativeStatement::If { then_branch, else_branch, .. } => {
                    collect_updated_vars(then_branch, vars);
                    if let Some(else_stmts) = else_branch {
                        collect_updated_vars(else_stmts, vars);
                    }
                }
                _ => {}
            }
        }
    }

    let mut body_updated_vars: Vec<Id> = Vec::new();
    collect_updated_vars(&body, &mut body_updated_vars);

    let mut free_vars: Vec<(Id, CType)> = Vec::new();
    for var in &body_updated_vars {
        if !loop_vars.iter().any(|(v, _)| v.name() == var.name()) {
            let ty = var_types.get(var.name()).cloned().unwrap_or_else(|| {
                CType::Apply(
                    Box::new(CType::Con(Id::qualified("Prelude", "Int", var.position()).into())),
                    Box::new(CType::Num(32, var.position())),
                    Span::DUMMY,
                )
            });
            free_vars.push((var.clone(), ty));
        }
    }

    let mut all_updated_vars = free_vars.clone();
    all_updated_vars.extend(loop_vars.clone());

    if free_vars.is_empty() {
        return Vec::new();
    }

    let f_id = Id::new(SmolStr::new_static("_f__"), pos.clone());
    let mut result_id = Id::new(SmolStr::new_static("_theResult__"), pos.clone());
    result_id.add_prop(bsc_syntax::id::IdProp::Renaming);

    let inner_result_type = build_tuple_type(&all_updated_vars);
    let outer_result_type = build_tuple_type(&free_vars);
    let fn_type = crate::make_fn_type(inner_result_type.clone(), inner_result_type.clone());

    let inner_body = build_for_loop_inner_body(
        pos.clone(),
        &all_updated_vars,
        cond.clone(),
        update,
        body,
        f_id.clone(),
        var_types,
    );

    let tuple_pattern = build_tuple_pattern(&all_updated_vars);
    let f_clause = CClause {
        patterns: vec![tuple_pattern.clone()],
        qualifiers: vec![],
        body: inner_body,
        span: Span::DUMMY,
    };

    let f_def = CDef::Untyped {
        name: f_id.clone(),
        ty: CQType {
            context: vec![],
            ty: fn_type,
            span: Span::DUMMY,
        },
        clauses: vec![f_clause],
        span: Span::DUMMY,
    };

    let mut inner_defs = Vec::new();
    for stmt in &init {
        if let ImperativeStatement::Decl { name, init: Some(expr), ty } = stmt {
            let mut name_with_keep = name.clone();
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

            let ty = ty.clone().unwrap_or_else(|| {
                CType::Apply(
                    Box::new(CType::Con(Id::qualified("Prelude", "Int", name.position()).into())),
                    Box::new(CType::Num(32, name.position())),
                    Span::DUMMY,
                )
            });

            inner_defs.push(CDefl::ValueSign(
                CDef::Untyped {
                    name: name_with_keep,
                    ty: CQType {
                        context: vec![],
                        ty,
                        span: Span::DUMMY,
                    },
                    clauses: vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr.clone(),
                        span: Span::DUMMY,
                    }],
                    span: Span::DUMMY,
                },
                vec![],
                Span::DUMMY,
            ));
        }
    }

    let init_tuple = build_tuple_expr(&all_updated_vars);

    let letrec_content = CExpr::LetRec(
        vec![CDefl::ValueSign(f_def, vec![], Span::DUMMY)],
        Box::new(CExpr::Apply(
            Box::new(CExpr::Var(f_id)),
            vec![init_tuple],
            Span::DUMMY,
        )),
        Span::DUMMY,
    );

    let mut inner_result_id = Id::new(SmolStr::new_static("_theResult__"), pos.clone());
    inner_result_id.add_prop(bsc_syntax::id::IdProp::Renaming);

    let inner_result_def = CDefl::ValueSign(
        CDef::Untyped {
            name: inner_result_id.clone(),
            ty: CQType {
                context: vec![],
                ty: inner_result_type.clone(),
                span: Span::DUMMY,
            },
            clauses: vec![CClause {
                patterns: vec![],
                qualifiers: vec![],
                body: letrec_content,
                span: Span::DUMMY,
            }],
            span: Span::DUMMY,
        },
        vec![],
        Span::DUMMY,
    );

    let inner_match = CDefl::Match(
        tuple_pattern,
        CExpr::Var(inner_result_id),
        Span::DUMMY,
    );

    let free_vars_expr = build_tuple_expr(&free_vars);

    let mut full_inner_defs = inner_defs;
    full_inner_defs.push(inner_result_def);
    full_inner_defs.push(inner_match);

    let inner_expr = CExpr::LetSeq(
        full_inner_defs,
        Box::new(free_vars_expr),
        Span::DUMMY,
    );

    let result_def = CDef::Untyped {
        name: result_id.clone(),
        ty: CQType {
            context: vec![],
            ty: outer_result_type.clone(),
            span: Span::DUMMY,
        },
        clauses: vec![CClause {
            patterns: vec![],
            qualifiers: vec![],
            body: inner_expr,
            span: Span::DUMMY,
        }],
        span: Span::DUMMY,
    };

    let outer_tuple_pattern = build_tuple_pattern(&free_vars);

    let outer_letseq = CStmt::LetSeq(
        vec![
            CDefl::ValueSign(result_def, vec![], Span::DUMMY),
            CDefl::Match(
                outer_tuple_pattern,
                CExpr::Var(result_id),
                Span::DUMMY,
            ),
        ],
        Span::DUMMY,
    );

    vec![outer_letseq]
}

fn build_tuple_type(vars: &[(Id, CType)]) -> CType {
    match vars.len() {
        0 => CType::Con(Id::qualified("Prelude", "PrimUnit", Position::unknown()).into()),
        1 => vars[0].1.clone(),
        _ => {
            let first_ty = vars[0].1.clone();
            let rest_ty = build_tuple_type(&vars[1..]);
            CType::Apply(
                Box::new(CType::Apply(
                    Box::new(CType::Con(Id::qualified("Prelude", "PrimPair", Position::unknown()).into())),
                    Box::new(first_ty),
                    Span::DUMMY,
                )),
                Box::new(rest_ty),
                Span::DUMMY,
            )
        }
    }
}

fn build_tuple_pattern(vars: &[(Id, CType)]) -> CPat {
    if vars.len() == 1 {
        CPat::Var(vars[0].0.clone())
    } else {
        let comma_id = Id::new(SmolStr::new_static(","), Position::unknown());
        let patterns: Vec<CPat> = vars.iter().map(|(v, _)| CPat::Var(v.clone())).collect();
        CPat::Con(comma_id, patterns, Span::DUMMY)
    }
}

fn build_tuple_expr(vars: &[(Id, CType)]) -> CExpr {
    if vars.len() == 1 {
        CExpr::Var(vars[0].0.clone())
    } else {
        let comma_id = Id::new(SmolStr::new_static(","), Position::unknown());
        let mut exprs: Vec<CExpr> = vars.iter().map(|(v, _)| CExpr::Var(v.clone())).collect();
        let last = exprs.pop().unwrap();
        let second_last = exprs.pop().unwrap();
        let mut result = CExpr::Infix(Box::new(second_last), comma_id.clone(), Box::new(last), Span::DUMMY);
        for expr in exprs.into_iter().rev() {
            result = CExpr::Infix(Box::new(expr), comma_id.clone(), Box::new(result), Span::DUMMY);
        }
        result
    }
}

fn build_for_loop_inner_body(
    pos: Position,
    vars: &[(Id, CType)],
    cond: CExpr,
    update: Vec<ImperativeStatement>,
    body: Vec<ImperativeStatement>,
    f_id: Id,
    var_types: &std::collections::HashMap<SmolStr, CType>,
) -> CExpr {
    let result_tuple = build_tuple_expr(vars);

    let mut inner_defls: Vec<CDefl> = Vec::new();

    for stmt in body {
        match stmt {
            ImperativeStatement::Update { lhs, rhs, .. } => {
                if let Some((var_name, update_expr)) = build_nested_update(&lhs, rhs) {
                    let var_type = vars.iter()
                        .find(|(v, _)| v.name() == var_name.name())
                        .map(|(_, t)| t.clone())
                        .or_else(|| var_types.get(var_name.name()).cloned())
                        .unwrap_or_else(|| {
                            CType::Apply(
                                Box::new(CType::Con(Id::qualified("Prelude", "Int", var_name.position()).into())),
                                Box::new(CType::Num(32, var_name.position())),
                                Span::DUMMY,
                            )
                        });

                    inner_defls.push(CDefl::ValueSign(
                        CDef::Untyped {
                            name: var_name,
                            ty: CQType {
                                context: vec![],
                                ty: var_type,
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: update_expr,
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    ));
                }
            }
            ImperativeStatement::For { pos: inner_pos, init, cond: inner_cond, update: inner_update, body: inner_body } => {
                let inner_for_stmts = convert_for_loop_to_module_stmts(inner_pos, init, inner_cond, inner_update, inner_body, var_types);
                for stmt in inner_for_stmts {
                    if let CStmt::LetSeq(defs, _) = stmt {
                        inner_defls.extend(defs);
                    }
                }
            }
            _ => {}
        }
    }

    for stmt in update {
        if let ImperativeStatement::Equal { name, expr } = stmt {
            let mut name_with_keep = name.clone();
            name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

            let var_type = vars.iter()
                .find(|(v, _)| v.name() == name.name())
                .map(|(_, t)| t.clone())
                .unwrap_or_else(|| {
                    CType::Apply(
                        Box::new(CType::Con(Id::qualified("Prelude", "Int", name.position()).into())),
                        Box::new(CType::Num(32, name.position())),
                        Span::DUMMY,
                    )
                });

            inner_defls.push(CDefl::ValueSign(
                CDef::Untyped {
                    name: name_with_keep,
                    ty: CQType {
                        context: vec![],
                        ty: var_type,
                        span: Span::DUMMY,
                    },
                    clauses: vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr,
                        span: Span::DUMMY,
                    }],
                    span: Span::DUMMY,
                },
                vec![],
                Span::DUMMY,
            ));
        }
    }

    let recursive_call = CExpr::Apply(
        Box::new(CExpr::Var(f_id)),
        vec![build_tuple_expr(vars)],
        Span::DUMMY,
    );

    let then_body = if inner_defls.is_empty() {
        recursive_call
    } else {
        CExpr::LetSeq(inner_defls, Box::new(recursive_call), Span::DUMMY)
    };

    CExpr::If(
        pos,
        Box::new(cond),
        Box::new(then_body),
        Box::new(result_tuple),
    )
}

fn convert_while_loop_to_cstmts(
    _pos: Position,
    _cond: CExpr,
    _body: Vec<ImperativeStatement>,
) -> Vec<CStmt> {
    Vec::new()
}

fn branch_has_block(stmts: &[ImperativeStatement]) -> bool {
    stmts.iter().any(|s| matches!(s,
        ImperativeStatement::BeginEnd { .. } |
        ImperativeStatement::Action { .. }))
}

fn make_return_unit() -> CStmt {
    CStmt::Expr {
        instance_name: None,
        expr: CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "return", Position::unknown()))),
            vec![CExpr::Struct(
                Some(true),
                Id::qualified("Prelude", "PrimUnit", Position::unknown()),
                vec![],
                Span::DUMMY,
            )],
            Span::DUMMY,
        ),
        span: Span::DUMMY,
    }
}

pub fn convert_action_stmts_to_stmts(stmts: Vec<ImperativeStatement>) -> Vec<CStmt> {
    convert_action_stmts_to_stmts_inner(stmts, true)
}

fn convert_action_stmts_to_stmts_inner(stmts: Vec<ImperativeStatement>, at_top_level: bool) -> Vec<CStmt> {
    let mut result = Vec::new();
    let mut var_types: std::collections::HashMap<String, CType> = std::collections::HashMap::new();
    let stmts_len = stmts.len();

    for (idx, stmt) in stmts.into_iter().enumerate() {
        let is_last = idx == stmts_len - 1;
        match stmt {
            ImperativeStatement::Let { name, expr } => {
                let mut name_with_keep = name;
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);
                result.push(CStmt::LetSeq(
                    vec![CDefl::Value(
                        name_with_keep,
                        vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: expr,
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    )],
                    Span::DUMMY,
                ));
            }
            ImperativeStatement::ArrayDecl {
                name,
                base_type,
                dimensions,
                init,
                init_pos,
            } => {
                let pos_for_check = init_pos.unwrap_or_else(|| name.position());
                let array_expr = build_array_init_expr(&dimensions, init, pos_for_check, None);

                let mut name_with_keep = name.clone();
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

                let array_type = build_array_type(base_type, dimensions.len());

                var_types.insert(name.name().to_string(), array_type.clone());

                result.push(CStmt::LetSeq(
                    vec![CDefl::ValueSign(
                        CDef::Untyped {
                            name: name_with_keep,
                            ty: CQType {
                                context: vec![],
                                ty: array_type,
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: array_expr,
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    )],
                    Span::DUMMY,
                ));
            }
            ImperativeStatement::Decl { name, init, ty } => {
                if let Some(ref t) = ty {
                    var_types.insert(name.name().to_string(), t.clone());
                }
                let body_expr = if let Some(expr) = init {
                    expr
                } else {
                    let pos = name.position().clone();
                    CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primUninitialized", Position::unknown()))),
                        vec![
                            CExpr::Lit(Literal::Position, pos.clone()),
                            CExpr::Lit(Literal::String(name.name().to_string()), pos),
                        ],
                        Span::DUMMY,
                    )
                };

                let mut name_with_keep = name.clone();
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);

                if let Some(ty) = ty {
                    result.push(CStmt::LetSeq(
                        vec![CDefl::ValueSign(
                            CDef::Untyped {
                                name: name_with_keep,
                                ty: CQType {
                                    context: vec![],
                                    ty,
                                    span: Span::DUMMY,
                                },
                                clauses: vec![CClause {
                                    patterns: vec![],
                                    qualifiers: vec![],
                                    body: body_expr,
                                    span: Span::DUMMY,
                                }],
                                span: Span::DUMMY,
                            },
                            vec![],
                            Span::DUMMY,
                        )],
                        Span::DUMMY,
                    ));
                } else {
                    result.push(CStmt::LetSeq(
                        vec![CDefl::Value(
                            name_with_keep,
                            vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: body_expr,
                                span: Span::DUMMY,
                            }],
                            vec![],
                            Span::DUMMY,
                        )],
                        Span::DUMMY,
                    ));
                }
            }
            ImperativeStatement::Equal { name, expr } => {
                result.push(CStmt::LetSeq(
                    vec![CDefl::Value(
                        name,
                        vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: expr,
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    )],
                    Span::DUMMY,
                ));
            }
            ImperativeStatement::Bind { name, expr, .. } => {
                result.push(CStmt::Bind {
                    pattern: CPat::Var(name),
                    instance_name: None,
                    pragmas: vec![],
                    expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::RegWrite { lhs, rhs } => {
                let write_expr = if matches!(&lhs, CExpr::Index { .. }) {
                    let position = match &lhs {
                        CExpr::Index { expr, .. } => get_expr_position(expr),
                        _ => Position::unknown(),
                    };
                    CExpr::Write {
                        position,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                        span: Span::DUMMY,
                    }
                } else {
                    CExpr::Infix(
                        Box::new(lhs),
                        Id::new(SmolStr::new_static(":="), Position::unknown()),
                        Box::new(rhs),
                        Span::DUMMY,
                    )
                };
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: write_expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::If {
                pos,
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let is_non_terminal = at_top_level && !is_last;
                let then_has_block = branch_has_block(&then_branch);
                let else_has_block = else_branch.as_ref().map(|b| branch_has_block(b)).unwrap_or(false);

                let mut then_stmts = convert_action_stmts_to_stmts_inner(then_branch, false);
                if is_non_terminal && !then_has_block {
                    then_stmts.push(make_return_unit());
                }
                let then_action = CExpr::Action(pos.clone(), then_stmts);

                let else_action = else_branch
                    .map(|stmts| {
                        let mut else_stmts = convert_action_stmts_to_stmts_inner(stmts, false);
                        if is_non_terminal && !else_has_block {
                            else_stmts.push(make_return_unit());
                        }
                        CExpr::Action(pos.clone(), else_stmts)
                    })
                    .unwrap_or_else(|| {
                        let mut else_stmts = vec![];
                        if is_non_terminal {
                            else_stmts.push(make_return_unit());
                        }
                        CExpr::Action(pos.clone(), else_stmts)
                    });

                let if_expr = CExpr::If(
                    pos,
                    Box::new(cond),
                    Box::new(then_action),
                    Box::new(else_action),
                );
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: if_expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::BeginEnd { pos, stmts, .. } => {
                let inner = convert_action_stmts_to_stmts_inner(stmts, false);
                let action_expr = CExpr::Action(pos, inner);
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: action_expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::Action { stmts, .. } => {
                let inner = convert_action_stmts_to_stmts_inner(stmts, false);
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: CExpr::Do {
                        recursive: false,
                        stmts: inner,
                        span: Span::DUMMY,
                    },
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::NakedExpr(expr) => {
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::Return { expr, .. } => {
                if let Some(e) = expr {
                    result.push(CStmt::Expr {
                        instance_name: None,
                        expr: CExpr::Apply(
                            Box::new(CExpr::Var(Id::qualified(
                                "Prelude",
                                "return",
                                Position::unknown(),
                            ))),
                            vec![e],
                            Span::DUMMY,
                        ),
                        span: Span::DUMMY,
                    });
                }
            }
            ImperativeStatement::For {
                pos,
                init,
                cond,
                update,
                body,
            } => {
                let inner = convert_for_loop_to_cstmts(pos.clone(), init, cond, update, body);
                let for_action = CExpr::Action(pos, inner);
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: for_action,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::While { pos, cond, body } => {
                let inner = convert_while_loop_to_cstmts(pos.clone(), cond, body);
                let while_action = CExpr::Action(pos, inner);
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: while_action,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::Update { pos: _, lhs, rhs } => {
                if let Some((var_name, update_expr)) = build_nested_update(&lhs, rhs) {
                    let var_type = var_types.get(var_name.name().as_str()).cloned();
                    let defl = if let Some(ty) = var_type {
                        CDefl::ValueSign(
                            CDef::Untyped {
                                name: var_name,
                                ty: CQType {
                                    context: vec![],
                                    ty,
                                    span: Span::DUMMY,
                                },
                                clauses: vec![CClause {
                                    patterns: vec![],
                                    qualifiers: vec![],
                                    body: update_expr,
                                    span: Span::DUMMY,
                                }],
                                span: Span::DUMMY,
                            },
                            vec![],
                            Span::DUMMY,
                        )
                    } else {
                        CDefl::Value(
                            var_name,
                            vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: update_expr,
                                span: Span::DUMMY,
                            }],
                            vec![],
                            Span::DUMMY,
                        )
                    };
                    result.push(CStmt::LetSeq(vec![defl], Span::DUMMY));
                }
            }
            _ => {}
        }
    }

    result
}

pub fn imperative_to_cstmts(
    context: ImperativeStmtContext,
    ifc_type: Option<CType>,
    stmts: Vec<ImperativeStatement>,
) -> Vec<CStmt> {
    conv_imperative_stmts_to_cstmts(context, ifc_type, true, stmts)
}

fn conv_imperative_stmts_to_cstmts(
    context: ImperativeStmtContext,
    ifc_type: Option<CType>,
    at_end: bool,
    stmts: Vec<ImperativeStatement>,
) -> Vec<CStmt> {
    if stmts.is_empty() {
        if at_end && matches!(context, ImperativeStmtContext::ISCIsModule | ImperativeStmtContext::ISCModule) {
            let ifc_id = ifc_type.as_ref().and_then(left_con);
            let ifc_expr = CExpr::Interface(Position::unknown(), ifc_id, vec![]);
            let return_expr = CExpr::Apply(
                Box::new(CExpr::Var(Id::qualified("Prelude", "return", Position::unknown()))),
                vec![ifc_expr],
                Span::DUMMY,
            );
            return vec![CStmt::Expr {
                instance_name: None,
                expr: return_expr,
                span: Span::DUMMY,
            }];
        }
        return vec![];
    }

    // Pre-process: merge InterfaceVarDecl + Inst pairs into a single Inst with type info
    // In Haskell BSV, "Type name();\n constructor instName(name);" produces one ISInst.
    let stmts = {
        let mut merged = Vec::new();
        let mut iter = stmts.into_iter().peekable();
        while let Some(stmt) = iter.next() {
            if let ImperativeStatement::InterfaceVarDecl { ref name, ref ty } = stmt {
                // Check if next statement is an Inst that uses this var decl
                if let Some(ImperativeStatement::Inst { ifc_var, .. }) = iter.peek() {
                    if ifc_var.name() == name.name() {
                        // Merge: take the Inst and add the type from InterfaceVarDecl
                        if let Some(ImperativeStatement::Inst { pos, attrs, ifc_var, inst_var, ifc_type: _, clocked_by, reset_by, powered_by, constructor }) = iter.next() {
                            merged.push(ImperativeStatement::Inst {
                                pos,
                                attrs,
                                ifc_var,
                                inst_var,
                                ifc_type: Some(ty.clone()),
                                clocked_by,
                                reset_by,
                                powered_by,
                                constructor,
                            });
                            continue;
                        }
                    }
                }
            }
            merged.push(stmt);
        }
        merged
    };

    let mut result = Vec::new();
    let len = stmts.len();
    let mut has_return = false;

    for (i, stmt) in stmts.into_iter().enumerate() {
        let is_last = i == len - 1;
        let stmt_at_end = at_end && is_last;

        if is_last && matches!(stmt, ImperativeStatement::Return { .. }) {
            has_return = true;
        }

        match stmt {
            ImperativeStatement::Decl { name, ty, init } => {
                let body_expr = init.unwrap_or_else(|| {
                    CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "primUninitialized", Position::unknown()))),
                        vec![
                            CExpr::Lit(Literal::Position, name.position().clone()),
                            CExpr::Lit(Literal::String(name.name().to_string()), name.position().clone()),
                        ],
                        Span::DUMMY,
                    )
                });
                let defl = if let Some(decl_type) = ty {
                    CDefl::ValueSign(
                        CDef::Untyped {
                            name,
                            ty: CQType {
                                context: vec![],
                                ty: decl_type,
                                span: Span::DUMMY,
                            },
                            clauses: vec![CClause {
                                patterns: vec![],
                                qualifiers: vec![],
                                body: body_expr,
                                span: Span::DUMMY,
                            }],
                            span: Span::DUMMY,
                        },
                        vec![],
                        Span::DUMMY,
                    )
                } else {
                    CDefl::Value(
                        name,
                        vec![CClause {
                            patterns: vec![],
                            qualifiers: vec![],
                            body: body_expr,
                            span: Span::DUMMY,
                        }],
                        vec![],
                        Span::DUMMY,
                    )
                };
                result.push(CStmt::LetSeq(vec![defl], Span::DUMMY));
            }
            ImperativeStatement::Let { name, expr } | ImperativeStatement::Equal { name, expr } => {
                let defl = CDefl::Value(
                    name,
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: expr,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                );
                result.push(CStmt::LetSeq(vec![defl], Span::DUMMY));
            }
            ImperativeStatement::Bind { name, ty, expr } => {
                let mut name_with_keep = name.clone();
                name_with_keep.add_prop(bsc_syntax::id::IdProp::Keep);
                let instance_name_expr = CExpr::Apply(
                    Box::new(CExpr::Var(Id::qualified("Prelude", "primGetName", Position::unknown()))),
                    vec![CExpr::Var(name_with_keep.clone())],
                    Span::DUMMY,
                );

                if let Some(bind_type) = ty {
                    result.push(CStmt::BindT {
                        pattern: CPat::Var(name_with_keep),
                        instance_name: Some(Box::new(instance_name_expr)),
                        pragmas: vec![],
                        ty: CQType {
                            context: vec![],
                            ty: bind_type,
                            span: Span::DUMMY,
                        },
                        expr,
                        span: Span::DUMMY,
                    });
                } else {
                    result.push(CStmt::Bind {
                        pattern: CPat::Var(name_with_keep),
                        instance_name: Some(Box::new(instance_name_expr)),
                        pragmas: vec![],
                        expr,
                        span: Span::DUMMY,
                    });
                }
            }
            ImperativeStatement::Rule { pos, name, guard, body_pos, body } => {
                let body_stmts = conv_imperative_stmts_to_cstmts(
                    ImperativeStmtContext::ISCAction,
                    None,
                    true,
                    body,
                );
                let name_expr = Some(CExpr::Lit(
                    Literal::String(name.name().to_string()),
                    name.position(),
                ));
                let qualifiers = if let Some(g) = guard {
                    vec![CQual::Filter(g)]
                } else {
                    vec![CQual::Filter(CExpr::Con(
                        Id::qualified("Prelude", "True", pos.clone()),
                        vec![],
                        Span::DUMMY,
                    ))]
                };
                let rule = CRule::Rule {
                    pragmas: vec![],
                    name: name_expr,
                    qualifiers,
                    body: CExpr::Action(body_pos, body_stmts),
                    span: Span::DUMMY,
                };
                let can_merge = matches!(
                    result.last(),
                    Some(CStmt::Expr { expr: CExpr::Apply(func, args, _), .. })
                    if matches!(func.as_ref(), CExpr::Var(id) if id.name() == "addRules")
                       && matches!(args.first(), Some(CExpr::Rules(..)))
                );
                if can_merge {
                    if let Some(CStmt::Expr { expr: CExpr::Apply(_, args, _), .. }) = result.last_mut() {
                        if let Some(CExpr::Rules(_, existing_rules, _)) = args.first_mut() {
                            existing_rules.push(rule);
                        }
                    }
                } else {
                    let rules_expr = CExpr::Apply(
                        Box::new(CExpr::Var(Id::qualified("Prelude", "addRules", pos.clone()))),
                        vec![CExpr::Rules(vec![], vec![rule], Span::DUMMY)],
                        Span::DUMMY,
                    );
                    let instance_name = if matches!(context, ImperativeStmtContext::ISCIsModule | ImperativeStmtContext::ISCModule) {
                        let mut add_rules_id = Id::new(SmolStr::new_static("_add_rules"), pos.clone());
                        add_rules_id.add_prop(bsc_syntax::id::IdProp::Hide);
                        let name_expr = CExpr::Apply(
                            Box::new(CExpr::Var(Id::qualified("Prelude", "primGetName", pos))),
                            vec![CExpr::Var(add_rules_id)],
                            Span::DUMMY,
                        );
                        Some(Box::new(name_expr))
                    } else {
                        None
                    };
                    result.push(CStmt::Expr {
                        instance_name,
                        expr: rules_expr,
                        span: Span::DUMMY,
                    });
                }
            }
            ImperativeStatement::MethodDefn { pos, name, ret_type, params, guard, body } => {
                let is_action = ret_type.as_ref().map(|t| {
                    if let CType::Con(tycon) = t {
                        tycon.name.name() == "Action"
                    } else {
                        false
                    }
                }).unwrap_or(false);

                let body_expr = if is_action {
                    let body_stmts = conv_imperative_stmts_to_cstmts(
                        ImperativeStmtContext::ISCAction,
                        None,
                        true,
                        body,
                    );
                    CExpr::Action(pos, body_stmts)
                } else {
                    convert_stmts_to_expr(body)
                };

                let patterns: Vec<CPat> = params.iter().map(|(n, _)| CPat::Var(n.clone())).collect();
                let qualifiers = guard.map(|g| vec![CQual::Filter(g)]).unwrap_or_default();
                let method_type = build_method_type(&params, ret_type);

                let method_field = CField {
                    name,
                    pragmas: None,
                    ty: CQType {
                        context: vec![],
                        ty: method_type,
                        span: Span::DUMMY,
                    },
                    default: vec![CClause {
                        patterns,
                        qualifiers,
                        body: body_expr,
                        span: Span::DUMMY,
                    }],
                    orig_type: None,
                    span: Span::DUMMY,
                };

                let defl = CDefl::Value(
                    method_field.name.clone(),
                    method_field.default.clone(),
                    vec![],
                    Span::DUMMY,
                );
                result.push(CStmt::LetSeq(vec![defl], Span::DUMMY));
            }
            ImperativeStatement::Return { pos, expr } => {
                let return_expr = CExpr::Apply(
                    Box::new(CExpr::Var(Id::qualified("Prelude", "return", Position::unknown()))),
                    vec![expr.unwrap_or_else(|| CExpr::Con(
                        Id::qualified("Prelude", "()", Position::unknown()),
                        vec![],
                        Span::DUMMY,
                    ))],
                    Span::DUMMY,
                );
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: return_expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::NakedExpr(expr) => {
                let instance_name = if matches!(context, ImperativeStmtContext::ISCIsModule | ImperativeStmtContext::ISCModule) {
                    get_naked_expr_name(&expr)
                } else {
                    None
                };
                result.push(CStmt::Expr {
                    instance_name: instance_name.map(Box::new),
                    expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::If { pos, cond, then_branch, else_branch } => {
                let then_stmts = conv_imperative_stmts_to_cstmts(context, ifc_type.clone(), stmt_at_end, then_branch);
                let else_stmts = conv_imperative_stmts_to_cstmts(
                    context,
                    ifc_type.clone(),
                    stmt_at_end,
                    else_branch.unwrap_or_default(),
                );
                let if_expr = if context == ImperativeStmtContext::ISCAction {
                    CExpr::If(
                        pos.clone(),
                        Box::new(cond),
                        Box::new(CExpr::Action(pos.clone(), then_stmts)),
                        Box::new(CExpr::Action(pos, else_stmts)),
                    )
                } else {
                    CExpr::If(
                        pos,
                        Box::new(cond),
                        Box::new(CExpr::Do { recursive: false, stmts: then_stmts, span: Span::DUMMY }),
                        Box::new(CExpr::Do { recursive: false, stmts: else_stmts, span: Span::DUMMY }),
                    )
                };
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: if_expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::InterfaceExpr { ty, members } => {
                let ifc_id = ty.as_ref().and_then(left_con);
                let defls = convert_interface_members_to_defls(members);
                let ifc_expr = CExpr::Interface(Position::unknown(), ifc_id, defls);
                let return_expr = CExpr::Apply(
                    Box::new(CExpr::Var(Id::qualified("Prelude", "return", Position::unknown()))),
                    vec![ifc_expr],
                    Span::DUMMY,
                );
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: return_expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::BeginEnd { pos, stmts: inner } => {
                let inner_stmts = conv_imperative_stmts_to_cstmts(context, ifc_type.clone(), stmt_at_end, inner);
                if context == ImperativeStmtContext::ISCAction {
                    result.push(CStmt::Expr {
                        instance_name: None,
                        expr: CExpr::Action(pos, inner_stmts),
                        span: Span::DUMMY,
                    });
                } else {
                    result.push(CStmt::Expr {
                        instance_name: None,
                        expr: CExpr::Do { recursive: false, stmts: inner_stmts, span: Span::DUMMY },
                        span: Span::DUMMY,
                    });
                }
            }
            ImperativeStatement::Action { pos, stmts: inner } => {
                let inner_stmts = conv_imperative_stmts_to_cstmts(ImperativeStmtContext::ISCAction, None, true, inner);
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: CExpr::Action(pos, inner_stmts),
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::RegWrite { lhs, rhs } => {
                let write_expr = CExpr::Infix(
                    Box::new(lhs),
                    Id::new(SmolStr::new_static(":="), Position::unknown()),
                    Box::new(rhs),
                    Span::DUMMY,
                );
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: write_expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::Inst { pos, attrs: _, ifc_var, inst_var, ifc_type, clocked_by: _, reset_by: _, powered_by: _, constructor } => {
                let instance_name_expr = CExpr::Apply(
                    Box::new(CExpr::Var(Id::qualified("Prelude", "primGetName", Position::unknown()))),
                    vec![CExpr::Var(inst_var)],
                    Span::DUMMY,
                );
                if let Some(ref ty) = ifc_type {
                    result.push(CStmt::BindT {
                        pattern: CPat::Var(ifc_var.clone()),
                        instance_name: Some(Box::new(instance_name_expr)),
                        pragmas: vec![],
                        ty: CQType {
                            context: vec![],
                            ty: ty.clone(),
                            span: Span::DUMMY,
                        },
                        expr: constructor,
                        span: Span::DUMMY,
                    });
                } else {
                    result.push(CStmt::Bind {
                        pattern: CPat::Var(ifc_var),
                        instance_name: Some(Box::new(instance_name_expr)),
                        pragmas: vec![],
                        expr: constructor,
                        span: Span::DUMMY,
                    });
                }
            }
            ImperativeStatement::InterfaceVarDecl { name, ty } => {
                let mut name_keep = name.clone();
                name_keep.add_prop(bsc_syntax::id::IdProp::Keep);
                let instance_name_expr = CExpr::Apply(
                    Box::new(CExpr::Var(Id::qualified("Prelude", "primGetName", Position::unknown()))),
                    vec![CExpr::Var(name_keep.clone())],
                    Span::DUMMY,
                );
                let constructor = CExpr::Var(name_keep.clone());
                result.push(CStmt::BindT {
                    pattern: CPat::Var(name_keep),
                    instance_name: Some(Box::new(instance_name_expr)),
                    pragmas: vec![],
                    ty: CQType {
                        context: vec![],
                        ty,
                        span: Span::DUMMY,
                    },
                    expr: constructor,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::Case { pos, subject, arms, default } => {
                let mut case_arms: Vec<CCaseArm> = Vec::new();
                for (arm_pos, tests, body) in arms {
                    let body_cstmts = conv_imperative_stmts_to_cstmts(context, ifc_type.clone(), true, body);
                    let body_expr = if context == ImperativeStmtContext::ISCAction {
                        CExpr::Action(arm_pos.clone(), body_cstmts)
                    } else {
                        CExpr::Do { recursive: false, stmts: body_cstmts, span: Span::DUMMY }
                    };
                    let filters = if tests.is_empty() {
                        vec![]
                    } else {
                        let eq_tests: Vec<COperand> = tests
                            .iter()
                            .map(|test| {
                                let test_pos = get_expr_position(test);
                                COperand::Expr(CExpr::OperChain(
                                    vec![
                                        COperand::Expr(subject.clone()),
                                        COperand::Operator {
                                            arity: 2,
                                            name: Id::qualified("Prelude", "==", test_pos),
                                        },
                                        COperand::Expr(test.clone()),
                                    ],
                                    Span::DUMMY,
                                ))
                            })
                            .collect();
                        let filter_expr = if eq_tests.len() == 1 {
                            CExpr::OperChain(vec![eq_tests.into_iter().next().unwrap()], Span::DUMMY)
                        } else {
                            let mut ops: Vec<COperand> = Vec::new();
                            for (j, test) in eq_tests.into_iter().enumerate() {
                                if j > 0 {
                                    ops.push(COperand::Operator {
                                        arity: 2,
                                        name: Id::qualified("Prelude", "||", arm_pos.clone()),
                                    });
                                }
                                ops.push(test);
                            }
                            CExpr::OperChain(ops, Span::DUMMY)
                        };
                        vec![CQual::Filter(filter_expr)]
                    };
                    case_arms.push(CCaseArm {
                        pattern: CPat::Wildcard(arm_pos),
                        qualifiers: filters,
                        body: body_expr,
                        span: Span::DUMMY,
                    });
                }
                if context == ImperativeStmtContext::ISCAction {
                    let (dflt_pos, dflt_body) = default.unwrap_or_else(|| (pos.clone(), vec![]));
                    let dflt_cstmts = conv_imperative_stmts_to_cstmts(context, ifc_type.clone(), true, dflt_body);
                    let dflt_expr = CExpr::Action(dflt_pos.clone(), dflt_cstmts);
                    case_arms.push(CCaseArm {
                        pattern: CPat::Wildcard(dflt_pos),
                        qualifiers: vec![],
                        body: dflt_expr,
                        span: Span::DUMMY,
                    });
                } else if let Some((dflt_pos, dflt_body)) = default {
                    let dflt_cstmts = conv_imperative_stmts_to_cstmts(context, ifc_type.clone(), true, dflt_body);
                    let dflt_expr = CExpr::Do { recursive: false, stmts: dflt_cstmts, span: Span::DUMMY };
                    case_arms.push(CCaseArm {
                        pattern: CPat::Wildcard(dflt_pos),
                        qualifiers: vec![],
                        body: dflt_expr,
                        span: Span::DUMMY,
                    });
                }
                let case_subject = CExpr::Struct(
                    Some(true),
                    Id::qualified("Prelude", "PrimUnit", pos.clone()),
                    vec![],
                    Span::DUMMY,
                );
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: CExpr::Case(pos, Box::new(case_subject), case_arms),
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::For { pos, init, cond, update, body } => {
                let init_stmts = conv_imperative_stmts_to_cstmts(context, ifc_type.clone(), false, init);
                let update_stmts = conv_imperative_stmts_to_cstmts(context, ifc_type.clone(), false, update);
                let body_stmts = conv_imperative_stmts_to_cstmts(context, ifc_type.clone(), false, body);
                result.extend(init_stmts);
                let for_body_expr = if context == ImperativeStmtContext::ISCAction {
                    CExpr::Action(pos.clone(), body_stmts)
                } else {
                    CExpr::Do { recursive: false, stmts: body_stmts, span: Span::DUMMY }
                };
                result.push(CStmt::Expr {
                    instance_name: None,
                    expr: for_body_expr,
                    span: Span::DUMMY,
                });
            }
            ImperativeStatement::TupleDecl { names, ty: _, init } => {
                if let Some(init_expr) = init {
                    let pat = CPat::Con(
                        Id::new(SmolStr::new_static(","), Position::unknown()),
                        names.iter().map(|n| {
                            let mut nk = n.clone();
                            nk.add_prop(bsc_syntax::id::IdProp::Keep);
                            CPat::Var(nk)
                        }).collect(),
                        Span::DUMMY,
                    );
                    result.push(CStmt::LetSeq(vec![
                        CDefl::Match(pat, init_expr, Span::DUMMY),
                    ], Span::DUMMY));
                }
            }
            _ => {}
        }
    }

    if !has_return && at_end && matches!(context, ImperativeStmtContext::ISCIsModule | ImperativeStmtContext::ISCModule) {
        let ifc_id = ifc_type.as_ref().and_then(left_con);
        let ifc_expr = CExpr::Interface(Position::unknown(), ifc_id, vec![]);
        let return_expr = CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "return", Position::unknown()))),
            vec![ifc_expr],
            Span::DUMMY,
        );
        result.push(CStmt::Expr {
            instance_name: None,
            expr: return_expr,
            span: Span::DUMMY,
        });
    }

    result
}

fn build_method_type(params: &[(Id, Option<CType>)], ret_type: Option<CType>) -> CType {
    let base_type = ret_type.unwrap_or_else(|| {
        CType::Var(Id::new(SmolStr::new_static("_"), Position::unknown()))
    });
    let param_types: Vec<CType> = params.iter()
        .map(|(_, t)| t.clone().unwrap_or_else(|| {
            CType::Var(Id::new(SmolStr::new_static("_"), Position::unknown()))
        }))
        .collect();

    if param_types.is_empty() {
        base_type
    } else {
        param_types.into_iter().rev().fold(base_type, |acc, param_ty| {
            crate::make_fn_type(param_ty, acc)
        })
    }
}

fn convert_interface_members_to_defls(members: Vec<ImperativeStatement>) -> Vec<CDefl> {
    let mut defls = Vec::new();
    for member in members {
        match member {
            ImperativeStatement::MethodDefn { name, params, body, guard, .. } => {
                let body_expr = convert_stmts_to_expr(body);
                let patterns: Vec<CPat> = params.iter().map(|(n, _)| CPat::Var(n.clone())).collect();
                let qualifiers = guard.map(|g| vec![CQual::Filter(g)]).unwrap_or_default();
                let clause = CClause {
                    patterns,
                    qualifiers,
                    body: body_expr,
                    span: Span::DUMMY,
                };
                defls.push(CDefl::Value(name, vec![clause], vec![], Span::DUMMY));
            }
            ImperativeStatement::SubinterfaceMethod { name, expr, .. } => {
                let clause = CClause {
                    patterns: vec![],
                    qualifiers: vec![],
                    body: expr,
                    span: Span::DUMMY,
                };
                defls.push(CDefl::Value(name, vec![clause], vec![], Span::DUMMY));
            }
            _ => {}
        }
    }
    defls
}

pub fn cstmts_to_cm_stmts(schedule_pragmas: Vec<CSchedulePragma>, cstmts: Vec<CStmt>) -> Vec<CModuleItem> {
    if cstmts.is_empty() {
        return vec![];
    }

    let len = cstmts.len();
    let (init_stmts, last_stmt) = cstmts.split_at(len - 1);

    let mut result: Vec<CModuleItem> = init_stmts.iter().cloned().map(CModuleItem::Stmt).collect();

    if !schedule_pragmas.is_empty() {
        let add_rules = CExpr::Apply(
            Box::new(CExpr::Var(Id::qualified("Prelude", "addRulesAt", Position::unknown()))),
            vec![CExpr::Rules(schedule_pragmas, vec![], Span::DUMMY)],
            Span::DUMMY,
        );
        result.push(CModuleItem::Stmt(CStmt::Expr {
            instance_name: None,
            expr: add_rules,
            span: Span::DUMMY,
        }));
    }

    match &last_stmt[0] {
        CStmt::Expr { instance_name, expr, .. } if instance_name.is_none() => {
            if let CExpr::Apply(_func, args, _) = expr {
                if args.len() == 1 {
                    result.push(CModuleItem::Interface(args[0].clone()));
                } else {
                    result.push(CModuleItem::Stmt(last_stmt[0].clone()));
                }
            } else {
                result.push(CModuleItem::Stmt(last_stmt[0].clone()));
            }
        }
        _ => {
            result.push(CModuleItem::Stmt(last_stmt[0].clone()));
        }
    }

    result
}

pub fn build_module_body_expr(pos: Position, ifc_type: Option<CType>, stmts: Vec<ImperativeStatement>) -> CExpr {
    let cstmts = imperative_to_cstmts(ImperativeStmtContext::ISCIsModule, ifc_type, stmts);
    let cm_stmts = cstmts_to_cm_stmts(vec![], cstmts);
    let fixed = cm_stmts.into_iter().map(|stmt| {
        match stmt {
            CModuleItem::Interface(CExpr::Interface(_, name, def)) => {
                CModuleItem::Interface(CExpr::Interface(pos.clone(), name, def))
            }
            other => other,
        }
    }).collect();
    CExpr::Module(pos, fixed)
}

fn left_con(ty: &CType) -> Option<Id> {
    match ty {
        CType::Con(tycon) => Some(tycon.name.clone()),
        CType::Apply(left, _, _) => left_con(left),
        _ => None,
    }
}
