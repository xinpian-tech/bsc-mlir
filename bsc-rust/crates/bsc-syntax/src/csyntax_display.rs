//! Display implementations for CSyntax types.
//!
//! These implementations produce output matching Haskell BSC's `-show-csyntax` format
//! for differential testing.
//!
//! The Id type already has Display in id.rs, so we don't redefine it here.

use std::fmt::{self, Display, Formatter};
use crate::csyntax::*;
use crate::id::Id;
use crate::literal::Literal;
use bsc_diagnostics::Position;

impl Display for UndefKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            UndefKind::General => write!(f, "UNotUsed"),
            UndefKind::DontCare => write!(f, "UDontCare"),
            UndefKind::Uninitialized => write!(f, "UNotUsed"),
            UndefKind::NoMatch => write!(f, "UNoMatch"),
            UndefKind::NoImplicitCond => write!(f, "UNotUsed"),
        }
    }
}

fn haskell_bool(b: bool) -> &'static str {
    if b { "True" } else { "False" }
}

fn fmt_char_escaped(f: &mut Formatter<'_>, c: char) -> fmt::Result {
    match c {
        '\n' => write!(f, "\\n"),
        '\t' => write!(f, "\\t"),
        '\r' => write!(f, "\\r"),
        '\x0B' => write!(f, "\\v"),
        '\x0C' => write!(f, "\\f"),
        '\\' => write!(f, "\\\\"),
        '\'' => write!(f, "\\'"),
        '"' => write!(f, "\\\""),
        '\0' => write!(f, "\\NUL"),
        c if c.is_ascii_control() => write!(f, "\\{}", c as u32),
        c => write!(f, "{}", c),
    }
}

fn fmt_list<T: Display>(f: &mut Formatter<'_>, items: &[T]) -> fmt::Result {
    write!(f, "[")?;
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "{}", item)?;
    }
    write!(f, "]")
}

fn fmt_id_list(f: &mut Formatter<'_>, items: &[Id]) -> fmt::Result {
    write!(f, "[")?;
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "{}", item)?;
    }
    write!(f, "]")
}

fn fmt_longname(f: &mut Formatter<'_>, longname: &[Id]) -> fmt::Result {
    fmt_id_list(f, longname)
}

fn fmt_longname_list(f: &mut Formatter<'_>, items: &[Vec<Id>]) -> fmt::Result {
    write!(f, "[")?;
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        fmt_longname(f, item)?;
    }
    write!(f, "]")
}

fn fmt_option<T: Display>(f: &mut Formatter<'_>, opt: &Option<T>) -> fmt::Result {
    match opt {
        Some(v) => {
            let s = format!("{}", v);
            if s.contains(' ') {
                write!(f, "(Just ({}))", s)
            } else {
                write!(f, "(Just {})", s)
            }
        }
        None => write!(f, "Nothing"),
    }
}

fn fmt_option_bool(f: &mut Formatter<'_>, opt: &Option<bool>) -> fmt::Result {
    match opt {
        Some(true) => write!(f, "(Just True)"),
        Some(false) => write!(f, "(Just False)"),
        None => write!(f, "Nothing"),
    }
}

fn fmt_position(f: &mut Formatter<'_>, pos: &Position) -> fmt::Result {
    let file = &*pos.file;
    let l = pos.line;
    let c = pos.column;

    if l == -2 && c < 0 && file.is_empty() {
        write!(f, "Command line")
    } else if l < 0 && c < 0 && file.is_empty() {
        write!(f, "Unknown position")
    } else {
        let lc = if l < 0 {
            String::new()
        } else if c < 0 {
            format!("line {}", l)
        } else {
            format!("line {}, column {}", l, c)
        };

        if file.is_empty() {
            write!(f, "{}", lc)
        } else if lc.is_empty() {
            write!(f, "{:?}", file)
        } else {
            write!(f, "{:?}, {}", file, lc)
        }
    }
}


fn fmt_pos_pprop_list(f: &mut Formatter<'_>, items: &[(Position, PProp)]) -> fmt::Result {
    write!(f, "[")?;
    for (i, (pos, prop)) in items.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "(")?;
        fmt_position(f, pos)?;
        write!(f, ",{})", prop)?;
    }
    write!(f, "]")
}

struct HaskellLit<'a>(&'a Literal);

impl Display for HaskellLit<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Literal::Integer(int) => write!(f, "LInt {}", int),
            Literal::Float(fl) => write!(f, "LReal {}", fl),
            Literal::Char(c) => {
                write!(f, "LChar '")?;
                fmt_char_escaped(f, *c)?;
                write!(f, "'")
            }
            Literal::String(s) => write!(f, "LString {:?}", s),
            Literal::Position => write!(f, "LPosition"),
        }
    }
}

impl Display for CPackage {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CPackage {} ", self.name)?;
        write!(f, "{} ", self.exports)?;
        fmt_list(f, &self.imports)?;
        write!(f, " ")?;
        fmt_list(f, &self.fixities)?;
        write!(f, " ")?;
        fmt_list(f, &self.definitions)?;
        write!(f, " ")?;
        fmt_list(f, &self.includes)
    }
}

impl Display for ExportSpec {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ExportSpec::Only(exports) => {
                write!(f, "(Left ")?;
                fmt_list(f, exports)?;
                write!(f, ")")
            }
            ExportSpec::Hiding(exports) => {
                write!(f, "(Right ")?;
                fmt_list(f, exports)?;
                write!(f, ")")
            }
        }
    }
}

impl Display for CExport {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CExport::Var(id) => write!(f, "CExpVar {}", id),
            CExport::Con(id) => write!(f, "CExpCon {}", id),
            CExport::ConAll(id) => write!(f, "CExpConAll {}", id),
            CExport::Type(id, cons) => {
                write!(f, "CExpType {} ", id)?;
                fmt_id_list(f, cons)
            }
            CExport::Package(id) => write!(f, "CExpPkg {}", id),
        }
    }
}

impl Display for CImport {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CImport::Simple { qualified, module, .. } => {
                write!(f, "CImpId {} {}", haskell_bool(*qualified), module)
            }
            CImport::Signature { name, qualified, signature, .. } => {
                write!(f, "CImpSign {:?} {} {}", name, haskell_bool(*qualified), signature)
            }
        }
    }
}

impl Display for CPackageSignature {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CSignature {} ", self.name)?;
        fmt_id_list(f, &self.imports)?;
        write!(f, " ")?;
        fmt_list(f, &self.fixities)?;
        write!(f, " ")?;
        fmt_list(f, &self.definitions)
    }
}

impl Display for CFixity {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CFixity::Infix(prec, id) => write!(f, "CInfix {} {}", prec, id),
            CFixity::Infixl(prec, id) => write!(f, "CInfixl {} {}", prec, id),
            CFixity::Infixr(prec, id) => write!(f, "CInfixr {} {}", prec, id),
        }
    }
}

impl Display for CInclude {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CInclude {:?}", self.0)
    }
}

impl Display for CDefn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CDefn::Type(def) => write!(f, "{}", def),
            CDefn::Data(def) => write!(f, "{}", def),
            CDefn::Struct(def) => write!(f, "{}", def),
            CDefn::Class(def) => write!(f, "{}", def),
            CDefn::Instance(def) => write!(f, "{}", def),
            CDefn::Value(def) => {
                write!(f, "CValue {} ", def.name)?;
                fmt_list(f, &def.clauses)
            }
            CDefn::ValueSign(def) => write!(f, "CValueSign ({})", def),
            CDefn::Signature(sig) => write!(f, "Csign {} {}", sig.name, sig.ty),
            CDefn::Foreign(def) => write!(f, "{}", def),
            CDefn::Primitive(def) => write!(f, "Cprimitive {} ({})", def.name, def.ty),
            CDefn::PrimitiveType(def) => {
                write!(f, "CprimType (IdKind {} ", def.name)?;
                fmt_kind_as_arg(f, &def.kind)?;
                write!(f, ")")
            }
            CDefn::Pragma(pragma) => write!(f, "CPragma ({})", pragma),
            CDefn::SigInstance { name, ty } => write!(f, "CIinstance {} {}", name, ty),
            CDefn::SigType { name, params, .. } => {
                write!(f, "CItype {} ", name)?;
                fmt_id_list(f, params)
            }
            CDefn::SigClass { incoherent_matches, supers, name, params, fundeps, methods } => {
                write!(f, "CIclass ")?;
                fmt_option(f, incoherent_matches)?;
                write!(f, " ")?;
                fmt_list(f, supers)?;
                write!(f, " {} ", name)?;
                fmt_id_list(f, params)?;
                write!(f, " ")?;
                fmt_list(f, fundeps)?;
                write!(f, " ")?;
                fmt_id_list(f, methods)
            }
            CDefn::SigValue { name, ty } => write!(f, "CIValueSign {} {}", name, ty),
        }
    }
}

impl Display for CTypeDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Ctype ({}) ", self.name)?;
        fmt_id_list(f, &self.params)?;
        write!(f, " ({})", self.body)
    }
}

impl Display for CDataDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Cdata {{cd_visible = {}, cd_name = {}, cd_type_vars = ",
            if self.visible { "True" } else { "False" }, self.name)?;
        fmt_id_list(f, &self.params)?;
        write!(f, ", cd_original_summands = ")?;
        fmt_list(f, &self.original_summands)?;
        write!(f, ", cd_internal_summands = ")?;
        fmt_list(f, &self.internal_summands)?;
        write!(f, ", cd_derivings = ")?;
        fmt_list(f, &self.deriving)?;
        write!(f, "}}")
    }
}

impl Display for COriginalSummand {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "COriginalSummand {{cos_names = ")?;
        fmt_id_list(f, &self.names)?;
        write!(f, ", cos_arg_types = ")?;
        fmt_list(f, &self.arg_types)?;
        write!(f, ", cos_field_names = ")?;
        match &self.field_names {
            Some(names) => {
                write!(f, "(Just ")?;
                fmt_id_list(f, names)?;
                write!(f, ")")?;
            }
            None => write!(f, "Nothing")?,
        }
        write!(f, ", cos_tag_encoding = ")?;
        fmt_option(f, &self.tag_encoding)?;
        write!(f, "}}")
    }
}

impl Display for CInternalSummand {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CInternalSummand {{cis_names = ")?;
        fmt_id_list(f, &self.names)?;
        write!(f, ", cis_arg_type = {}, cis_tag_encoding = {}}}", self.arg_type, self.tag_encoding)
    }
}

impl Display for CTypeclass {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CTypeclass {}", self.name)
    }
}

impl Display for CStructDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Cstruct {} ",
            if self.visible { "True" } else { "False" })?;
        match &self.sub_type {
            StructSubType::Struct => write!(f, "SStruct")?,
            StructSubType::Class => write!(f, "SClass")?,
            _ => write!(f, "({})", self.sub_type)?,
        }
        write!(f, " ({}) ", self.name)?;
        fmt_id_list(f, &self.params)?;
        write!(f, " ")?;
        fmt_list(f, &self.fields)?;
        write!(f, " ")?;
        fmt_list(f, &self.deriving)
    }
}

impl Display for StructSubType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            StructSubType::Struct => write!(f, "SStruct"),
            StructSubType::Class => write!(f, "SClass"),
            StructSubType::DataCon { type_id, named_fields } => {
                write!(f, "SDataCon {{sdatacon_id = {}, sdatacon_named_fields = {}}}",
                    type_id, if *named_fields { "True" } else { "False" })
            }
            StructSubType::Interface(pragmas) => {
                write!(f, "SInterface ")?;
                fmt_list(f, pragmas)
            }
            StructSubType::PolyWrap { original_id, constructor, field } => {
                write!(f, "SPolyWrap {} ", original_id)?;
                fmt_option(f, constructor)?;
                write!(f, " {}", field)
            }
        }
    }
}

impl Display for CField {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CField {{cf_name = {}, cf_pragmas = ", self.name)?;
        match &self.pragmas {
            Some(p) => {
                write!(f, "Just ")?;
                fmt_list(f, p)?;
            }
            None => write!(f, "Nothing")?,
        }
        write!(f, ", cf_type = {}, cf_default = ", self.ty)?;
        fmt_list(f, &self.default)?;
        write!(f, ", cf_orig_type = ")?;
        match &self.orig_type {
            Some(t) => write!(f, "(Just {})", t)?,
            None => write!(f, "Nothing")?,
        }
        write!(f, "}}")
    }
}

impl Display for IfcPragma {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            IfcPragma::AlwaysReady => write!(f, "PIAlwaysRdy"),
            IfcPragma::AlwaysEnabled => write!(f, "PIAlwaysEnabled"),
            IfcPragma::Prefix(s) => write!(f, "PIPrefixStr {:?}", s),
            IfcPragma::Result(s) => write!(f, "PIResultName {:?}", s),
            IfcPragma::Ready(s) => write!(f, "PIRdySignalName {:?}", s),
            IfcPragma::Enable(s) => write!(f, "PIEnSignalName {:?}", s),
            IfcPragma::ArgNames(ids) => {
                write!(f, "PIArgNames ")?;
                fmt_id_list(f, ids)
            }
            IfcPragma::ArgClock(s) => write!(f, "PIArgClock {:?}", s),
            IfcPragma::ArgReset(s) => write!(f, "PIArgReset {:?}", s),
            IfcPragma::ArgInout(s) => write!(f, "PIArgInout {:?}", s),
        }
    }
}

impl Display for CClassDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Cclass ")?;
        fmt_option_bool(f, &self.incoherent_matches)?;
        write!(f, " ")?;
        fmt_list(f, &self.supers)?;
        write!(f, " ({}) ", self.name)?;
        fmt_id_list(f, &self.params)?;
        write!(f, " ")?;
        fmt_list(f, &self.fundeps)?;
        write!(f, " ")?;
        fmt_list(f, &self.methods)
    }
}

impl Display for CFunDep {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        fmt_id_list(f, &self.from)?;
        write!(f, ",")?;
        fmt_id_list(f, &self.to)?;
        write!(f, ")")
    }
}

impl Display for CInstanceDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Cinstance ({}) ", self.ty)?;
        fmt_list(f, &self.methods)
    }
}

impl Display for CDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CDef::Untyped { name, ty, clauses, .. } => {
                write!(f, "CDef {} ({}) ", name, ty)?;
                fmt_list(f, clauses)
            }
            CDef::Typed { name, type_vars, ty, clauses, .. } => {
                write!(f, "CDefT {} ", name)?;
                fmt_list(f, type_vars)?;
                write!(f, " ({}) ", ty)?;
                fmt_list(f, clauses)
            }
        }
    }
}

impl Display for CTyVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "TyVar {{tv_name = {}, tv_num = {}, tv_kind = {}}}",
            self.name, self.num, self.kind)
    }
}

impl Display for CClause {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CClause ")?;
        fmt_list(f, &self.patterns)?;
        write!(f, " ")?;
        fmt_list(f, &self.qualifiers)?;
        write!(f, " ({})", self.body)
    }
}

impl Display for CForeignDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Cforeign {{cforg_name = {}, cforg_type = {}, cforg_foreign_name = ",
            self.name, self.ty)?;
        match &self.foreign_name {
            Some(n) => write!(f, "Just {:?}", n)?,
            None => write!(f, "Nothing")?,
        }
        write!(f, ", cforg_ports = ")?;
        match &self.ports {
            Some((inputs, outputs)) => {
                write!(f, "Just (")?;
                write!(f, "[")?;
                for (i, s) in inputs.iter().enumerate() {
                    if i > 0 { write!(f, ",")?; }
                    write!(f, "{:?}", s)?;
                }
                write!(f, "],[")?;
                for (i, s) in outputs.iter().enumerate() {
                    if i > 0 { write!(f, ",")?; }
                    write!(f, "{:?}", s)?;
                }
                write!(f, "])")?;
            }
            None => write!(f, "Nothing")?,
        }
        write!(f, "}}")
    }
}

impl Display for IdK {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            IdK::Plain(id) => write!(f, "IdK {}", id),
            IdK::WithKind(id, k) => {
                write!(f, "IdKind {} ", id)?;
                fmt_kind_as_arg(f, k)
            }
            IdK::WithPartialKind(id, pk) => write!(f, "IdPKind {} {}", id, pk),
        }
    }
}

fn fmt_kind_as_arg(f: &mut Formatter<'_>, k: &CKind) -> fmt::Result {
    match k {
        CKind::Star(_) | CKind::Num(_) | CKind::Str(_) => write!(f, "{}", k),
        CKind::Fun(_, _, _) => write!(f, "({})", k),
        CKind::Paren(inner, _) => fmt_kind_as_arg(f, inner),
    }
}

fn expr_needs_parens(e: &CExpr) -> bool {
    match e {
        CExpr::Paren(inner, _) => expr_needs_parens(inner),
        _ => true,
    }
}

fn fmt_expr_as_arg(f: &mut Formatter<'_>, e: &CExpr) -> fmt::Result {
    if expr_needs_parens(e) {
        write!(f, "({})", e)
    } else {
        write!(f, "{}", e)
    }
}

impl Display for CPartialKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CPartialKind::NoInfo => write!(f, "PKNoInfo"),
            CPartialKind::Star => write!(f, "PKStar"),
            CPartialKind::Num => write!(f, "PKNum"),
            CPartialKind::Str => write!(f, "PKStr"),
            CPartialKind::Fun(a, b) => write!(f, "PKfun {} {}", a, b),
        }
    }
}

impl Display for CExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CExpr::Var(id) => write!(f, "CVar {}", id),
            CExpr::Con(id, args, _) => {
                if args.is_empty() {
                    write!(f, "CCon {} []", id)
                } else {
                    write!(f, "CCon {} ", id)?;
                    fmt_list(f, args)
                }
            }
            CExpr::Lit(lit, pos) => {
                write!(f, "CLit (CLiteral ")?;
                fmt_position(f, pos)?;
                write!(f, " ({}))", HaskellLit(lit))
            }
            CExpr::Lambda(pats, body, _) => {
                fn fmt_nested_lambda(pats: &[CPat], body: &CExpr, f: &mut Formatter<'_>) -> fmt::Result {
                    if pats.is_empty() {
                        write!(f, "{}", body)
                    } else {
                        write!(f, "CLam ")?;
                        match &pats[0] {
                            CPat::Var(id) => write!(f, "(Right {}) ", id)?,
                            CPat::Wildcard(pos) => {
                                write!(f, "(Left ")?;
                                fmt_position(f, pos)?;
                                write!(f, ") ")?;
                            }
                            other => write!(f, "(Left {}) ", other)?,
                        }
                        if pats.len() == 1 {
                            fmt_expr_as_arg(f, body)
                        } else {
                            write!(f, "(")?;
                            fmt_nested_lambda(&pats[1..], body, f)?;
                            write!(f, ")")
                        }
                    }
                }
                fmt_nested_lambda(pats, body, f)
            }
            CExpr::LambdaTyped { param, param_type, body, .. } => {
                write!(f, "CLamT {} {} {}", param, param_type, body)
            }
            CExpr::Apply(func, args, _) => {
                write!(f, "CApply ({}) ", func)?;
                fmt_list(f, args)
            }
            CExpr::Infix(l, op, r, _) => {
                write!(f, "CApply (CVar {}) [{},{}]", op, l, r)
            }
            CExpr::OperChain(operands, _) => {
                write!(f, "COper ")?;
                fmt_list(f, operands)
            }
            CExpr::SectionL(op, e, _) => {
                write!(f, "CSectionL {} {}", op, e)
            }
            CExpr::SectionR(e, op, _) => {
                write!(f, "CSectionR {} {}", e, op)
            }
            CExpr::If(pos, cond, then_e, else_e) => {
                write!(f, "Cif ")?;
                fmt_position(f, pos)?;
                write!(f, " ({}) ({}) ({})", cond, then_e, else_e)
            }
            CExpr::Case(pos, scrut, arms) => {
                write!(f, "Ccase ")?;
                fmt_position(f, pos)?;
                write!(f, " ({}) ", scrut)?;
                fmt_list(f, arms)
            }
            CExpr::LetSeq(defls, body, _) => {
                write!(f, "Cletseq ")?;
                fmt_list(f, defls)?;
                write!(f, " ")?;
                fmt_expr_as_arg(f, body)
            }
            CExpr::LetRec(defls, body, _) => {
                write!(f, "Cletrec ")?;
                fmt_list(f, defls)?;
                write!(f, " ({})", body)
            }
            CExpr::Do { recursive, stmts, .. } => {
                write!(f, "Cdo {} ", if *recursive { "True" } else { "False" })?;
                fmt_list(f, stmts)
            }
            CExpr::Module(pos, items) => {
                write!(f, "Cmodule ")?;
                fmt_position(f, pos)?;
                write!(f, " ")?;
                fmt_list(f, items)
            }
            CExpr::Interface(pos, maybe_name, defls) => {
                write!(f, "Cinterface ")?;
                fmt_position(f, pos)?;
                write!(f, " ")?;
                fmt_option(f, maybe_name)?;
                write!(f, " ")?;
                fmt_list(f, defls)
            }
            CExpr::Rules(pragmas, rules, _) => {
                write!(f, "Crules ")?;
                fmt_list(f, pragmas)?;
                write!(f, " ")?;
                fmt_list(f, rules)
            }
            CExpr::Struct(vis, id, fields, _) => {
                write!(f, "CStruct ")?;
                fmt_option_bool(f, vis)?;
                write!(f, " {} ", id)?;
                fmt_list(f, fields)
            }
            CExpr::Update(e, fields, _) => {
                write!(f, "CStructUpd ({}) ", e)?;
                fmt_list(f, fields)
            }
            CExpr::Select(e, field, _) => {
                write!(f, "CSelect ({}) {}", e, field)
            }
            CExpr::Write { lhs, rhs, .. } => {
                write!(f, "Cwrite {} {}", lhs, rhs)
            }
            CExpr::Any { position, kind, .. } => {
                write!(f, "CAny ")?;
                fmt_position(f, position)?;
                write!(f, " {}", kind)
            }
            CExpr::Index { expr, index, .. } => {
                write!(f, "CSub ({}) ({})", expr, index)
            }
            CExpr::IndexRange { expr, hi, lo, .. } => {
                write!(f, "CSub2 ({}) ({}) ({})", expr, hi, lo)
            }
            CExpr::IndexUpdate { expr, range: (hi, lo), value, .. } => {
                write!(f, "CSubUpdate ({}) ({},{}) ({})", expr, hi, lo, value)
            }
            CExpr::TaskApply(func, args, _) => {
                write!(f, "CTaskApply ")?;
                fmt_expr_as_arg(f, func)?;
                write!(f, " ")?;
                fmt_list(f, args)
            }
            CExpr::TaskApplyTyped(func, ty, args, _) => {
                write!(f, "CTaskApplyT ")?;
                fmt_expr_as_arg(f, func)?;
                write!(f, " {} ", ty)?;
                fmt_list(f, args)
            }
            CExpr::TypeAscription(e, ty, _) => {
                write!(f, "CHasType ({}) ({})", e, ty)
            }
            CExpr::TypeApply(e, tys, _) => {
                write!(f, "CTApply {} ", e)?;
                fmt_list(f, tys)
            }
            CExpr::ValueOf(ty, _) => {
                write!(f, "CValueOf {}", ty)
            }
            CExpr::StringOf(ty, _) => {
                write!(f, "CStringOf {}", ty)
            }
            CExpr::Paren(e, _) => write!(f, "{}", e),
            CExpr::List(es, _) => {
                write!(f, "CCon Prelude::List ")?;
                fmt_list(f, es)
            }
            CExpr::Tuple(es, _) => {
                match es.len() {
                    0 => write!(f, "CStruct (Just True) Prelude::PrimUnit []"),
                    1 => write!(f, "{}", es[0]),
                    _ => {
                        fn fmt_nested_tuple_expr(es: &[CExpr], f: &mut Formatter<'_>) -> fmt::Result {
                            if es.len() == 1 {
                                write!(f, "{}", es[0])
                            } else {
                                write!(f, "CBinOp ({}) , (", es[0])?;
                                fmt_nested_tuple_expr(&es[1..], f)?;
                                write!(f, ")")
                            }
                        }
                        fmt_nested_tuple_expr(es, f)
                    }
                }
            }
            CExpr::Verilog(v, _) => write!(f, "Cverilog {}", v),
            CExpr::ModuleVerilog { name_expr, user_imported, clock_info, reset_info, args, fields, sched_info, path_info } => {
                write!(f, "CmoduleVerilog ({}) {} ({}) ({}) ", name_expr, haskell_bool(*user_imported), clock_info, reset_info)?;
                write!(f, "[")?;
                for (i, (arg_info, arg_expr)) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "({},{})", arg_info, arg_expr)?;
                }
                write!(f, "] ")?;
                fmt_list(f, fields)?;
                write!(f, " ({}) ({})", sched_info, path_info)
            }
            CExpr::ForeignFuncC { name, ty, .. } => {
                write!(f, "CforeignFuncC {} {}", name, ty)
            }
            CExpr::Action(pos, stmts) => {
                write!(f, "Caction ")?;
                fmt_position(f, pos)?;
                write!(f, " ")?;
                fmt_list(f, stmts)
            }
            CExpr::ActionValue(stmts, _) => {
                write!(f, "CactionValue ")?;
                fmt_list(f, stmts)
            }
            CExpr::Attributed(attrs, e, _) => {
                write!(f, "Cattributed ")?;
                fmt_list(f, attrs)?;
                write!(f, " ")?;
                fmt_expr_as_arg(f, e)
            }
            CExpr::ConTyped { type_name, con_name, args, .. } => {
                write!(f, "CConT {} {} ", type_name, con_name)?;
                fmt_list(f, args)
            }
            CExpr::LitTyped(ty, lit, _) => {
                write!(f, "CLitT {} (CLiteral <pos> ({}))", ty, HaskellLit(lit))
            }
            CExpr::AnyTyped { position, kind, ty, .. } => {
                write!(f, "CAnyT ")?;
                fmt_position(f, position)?;
                write!(f, " {} {}", kind, ty)
            }
            CExpr::SelectTyped { type_name, expr, field, .. } => {
                write!(f, "CSelectT {} ({}) {}", type_name, expr, field)
            }
            CExpr::StructTyped(ty, fields, _) => {
                write!(f, "CstructT {} ", ty)?;
                fmt_list(f, fields)
            }
            CExpr::VerilogTyped(ty, v, _) => {
                write!(f, "CverilogT {} {}", ty, v)
            }
            CExpr::ForeignFuncCTyped { name, ty, .. } => {
                write!(f, "CforeignFuncCT {} {}", name, ty)
            }
            CExpr::Con1 { type_id, con_id, arg, .. } => {
                write!(f, "CCon1 {} {} {}", type_id, con_id, arg)
            }
            CExpr::SelectTT { type_id, expr, field_id, .. } => {
                write!(f, "CSelectTT {} ({}) {}", type_id, expr, field_id)
            }
            CExpr::Con0 { type_id, con_id, .. } => {
                write!(f, "CCon0 ")?;
                fmt_option(f, type_id)?;
                write!(f, " {}", con_id)
            }
            CExpr::SelectT { type_id, field_id, .. } => {
                write!(f, "CSelectT {} {}", type_id, field_id)
            }
        }
    }
}

impl Display for LambdaParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            LambdaParam::Implicit(_) => write!(f, "<implicit>"),
            LambdaParam::Explicit(id) => write!(f, "{}", id),
        }
    }
}

impl Display for COperand {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            COperand::Expr(e) => write!(f, "CRand ({})", e),
            COperand::Operator { arity, name } => write!(f, "CRator {} {}", arity, name),
        }
    }
}

impl Display for CDefl {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CDefl::ValueSign(def, quals, _) => {
                write!(f, "CLValueSign ({}) ", def)?;
                fmt_list(f, quals)
            }
            CDefl::Value(id, clauses, quals, _) => {
                write!(f, "CLValue {} ", id)?;
                fmt_list(f, clauses)?;
                write!(f, " ")?;
                fmt_list(f, quals)
            }
            CDefl::Match(pat, expr, _) => {
                write!(f, "CLMatch ({}) ({})", pat, expr)
            }
        }
    }
}

impl Display for CQual {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CQual::Gen(ty, pat, expr) => {
                write!(f, "CQGen ({}) ({}) ({})", ty, pat, expr)
            }
            CQual::Filter(expr) => {
                write!(f, "CQFilter ({})", expr)
            }
        }
    }
}

impl Display for CCaseArm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CCaseArm {{cca_pattern = {}, cca_filters = ", self.pattern)?;
        fmt_list(f, &self.qualifiers)?;
        write!(f, ", cca_consequent = {}}}", self.body)
    }
}

impl Display for CStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CStmt::BindT { pattern, instance_name, pragmas, ty, expr, .. } => {
                write!(f, "CSBindT ({}) ", pattern)?;
                match instance_name {
                    Some(e) => write!(f, "(Just {}) ", e)?,
                    None => write!(f, "Nothing ")?,
                }
                fmt_pos_pprop_list(f, pragmas)?;
                write!(f, " ({}) ({})", ty, expr)
            }
            CStmt::Bind { pattern, instance_name, pragmas, expr, .. } => {
                write!(f, "CSBind ({}) ", pattern)?;
                match instance_name {
                    Some(e) => write!(f, "(Just {}) ", e)?,
                    None => write!(f, "Nothing ")?,
                }
                fmt_pos_pprop_list(f, pragmas)?;
                write!(f, " ({})", expr)
            }
            CStmt::LetSeq(defls, _) => {
                write!(f, "CSletseq ")?;
                fmt_list(f, defls)
            }
            CStmt::LetRec(defls, _) => {
                write!(f, "CSletrec ")?;
                fmt_list(f, defls)
            }
            CStmt::Expr { instance_name, expr, .. } => {
                write!(f, "CSExpr ")?;
                match instance_name {
                    Some(e) => write!(f, "(Just {}) ", e)?,
                    None => write!(f, "Nothing ")?,
                }
                write!(f, "({})", expr)
            }
        }
    }
}

impl Display for CModuleItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CModuleItem::Stmt(s) => write!(f, "CMStmt ({})", s),
            CModuleItem::Rules(e) => write!(f, "CMrules ({})", e),
            CModuleItem::Interface(e) => write!(f, "CMinterface ({})", e),
            CModuleItem::TupleInterface(pos, es) => {
                write!(f, "CMTupleInterface ")?;
                fmt_position(f, pos)?;
                write!(f, " ")?;
                fmt_list(f, es)
            }
        }
    }
}

impl Display for CMethodDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CMethodDef {} ", self.name)?;
        fmt_list(f, &self.params)?;
        write!(f, " ")?;
        match &self.condition {
            Some(c) => write!(f, "(Just {}) ", c)?,
            None => write!(f, "Nothing ")?,
        }
        write!(f, "{}", self.body)
    }
}

impl Display for CRule {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CRule::Rule { pragmas, name, qualifiers, body, .. } => {
                write!(f, "CRule ")?;
                fmt_list(f, pragmas)?;
                write!(f, " ")?;
                fmt_option(f, name)?;
                write!(f, " ")?;
                fmt_list(f, qualifiers)?;
                write!(f, " ")?;
                fmt_expr_as_arg(f, body)
            }
            CRule::Nested { pragmas, name, qualifiers, rules, .. } => {
                write!(f, "CRuleNest ")?;
                fmt_list(f, pragmas)?;
                write!(f, " ")?;
                fmt_option(f, name)?;
                write!(f, " ")?;
                fmt_list(f, qualifiers)?;
                write!(f, " ")?;
                fmt_list(f, rules)
            }
        }
    }
}

impl Display for RulePragma {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RulePragma::FireWhenEnabled => write!(f, "RPfireWhenEnabled"),
            RulePragma::NoImplicitConditions => write!(f, "RPnoImplicitConditions"),
            RulePragma::CanFire => write!(f, "RPcanFire"),
            RulePragma::NoFire => write!(f, "RPnoFire"),
            RulePragma::AggressiveConditions => write!(f, "RPaggressiveImplicitConditions"),
            RulePragma::ConservativeConditions => write!(f, "RPconservativeConditions"),
            RulePragma::Clock(id) => write!(f, "RPclock {}", id),
            RulePragma::Reset(id) => write!(f, "RPreset {}", id),
            RulePragma::Doc(s) => write!(f, "RPdoc {:?}", s),
            RulePragma::Hide => write!(f, "RPhide"),
            RulePragma::NoWarn => write!(f, "RPnoWarn"),
            RulePragma::WarnAllConflicts => write!(f, "RPwarnAllConflicts"),
            RulePragma::ClockCrossingRule => write!(f, "RPclockCrossingRule"),
        }
    }
}

impl Display for CSchedulePragma {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CSchedulePragma::Mutually { exclusive } => {
                write!(f, "SPMutuallyExclusive ")?;
                fmt_list(f, exclusive)
            }
            CSchedulePragma::Conflict { rules } => {
                write!(f, "SPConflict ")?;
                fmt_list(f, rules)
            }
            CSchedulePragma::Preempt { first, second } => {
                write!(f, "SPPreempt ")?;
                fmt_list(f, first)?;
                write!(f, " ")?;
                fmt_list(f, second)
            }
            CSchedulePragma::Before { first, second } => {
                write!(f, "SPSequence ")?;
                fmt_list(f, first)?;
                write!(f, " ")?;
                fmt_list(f, second)
            }
            CSchedulePragma::ExecutionOrder(es) => {
                write!(f, "SPExecutionOrder ")?;
                fmt_list(f, es)
            }
        }
    }
}

impl Display for CSubmodule {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CSubmodule {} {}", self.name, self.module)
    }
}

impl Display for CFieldInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({},{})", self.name, self.value)
    }
}

impl Display for CVerilog {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CVerilog {:?} ", self.name)?;
        write!(f, "[")?;
        for (i, (name, expr)) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "({:?},{})", name, expr)?;
        }
        write!(f, "] ")?;
        fmt_list(f, &self.ports)
    }
}

impl Display for CVerilogPort {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({:?},{},{})", self.name, self.direction, self.expr)
    }
}

impl Display for CVerilogDir {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CVerilogDir::Input => write!(f, "VPinput"),
            CVerilogDir::Output => write!(f, "VPoutput"),
            CVerilogDir::Inout => write!(f, "VPinout"),
        }
    }
}

impl Display for CAttribute {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CAttribute {:?} ", self.name)?;
        fmt_option(f, &self.value)
    }
}

impl Display for CPat {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CPat::Var(id) => write!(f, "CPVar {}", id),
            CPat::Wildcard(pos) => write!(f, "CPAny {}", pos),
            CPat::Con(id, pats, _) => {
                write!(f, "CPCon {} ", id)?;
                fmt_list(f, pats)
            }
            CPat::Struct(vis, id, fields, _) => {
                write!(f, "CPstruct ")?;
                fmt_option_bool(f, vis)?;
                write!(f, " {} ", id)?;
                fmt_list(f, fields)
            }
            CPat::Lit(lit, pos) => {
                write!(f, "CPLit (CLiteral ")?;
                fmt_position(f, pos)?;
                write!(f, " ({}))", HaskellLit(lit))
            }
            CPat::As(id, pat, _) => {
                write!(f, "CPAs {} ({})", id, pat)
            }
            CPat::Typed(pat, ty, _) => {
                write!(f, "CPTyped ({}) ({})", pat, ty)
            }
            CPat::Paren(pat, _) => write!(f, "{}", pat),
            CPat::Tuple(pats, _) => {
                match pats.len() {
                    0 => write!(f, "CPstruct (Just True) Prelude::PrimUnit []"),
                    1 => write!(f, "{}", pats[0]),
                    _ => {
                        fn fmt_nested_tuple_pat(pats: &[CPat], f: &mut Formatter<'_>) -> fmt::Result {
                            if pats.len() == 1 {
                                write!(f, "{}", pats[0])
                            } else {
                                write!(f, "CPCon , [{},", pats[0])?;
                                fmt_nested_tuple_pat(&pats[1..], f)?;
                                write!(f, "]")
                            }
                        }
                        fmt_nested_tuple_pat(pats, f)
                    }
                }
            }
            CPat::List(pats, _) => {
                write!(f, "CPList ")?;
                fmt_list(f, pats)
            }
            CPat::Infix(l, op, r, _) => {
                write!(f, "CPOper [CRand ({}),CRator 2 {},CRand ({})]", l, op, r)
            }
            CPat::MixedLit { base, parts, .. } => {
                write!(f, "CPMixedLit {} ", base)?;
                write!(f, "[")?;
                for (i, (len, val)) in parts.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "({},", len)?;
                    match val {
                        Some(v) => write!(f, "Just {})", v)?,
                        None => write!(f, "Nothing)")?,
                    }
                }
                write!(f, "]")
            }
            CPat::Con1 { type_id, con_id, arg, .. } => {
                write!(f, "CPCon1 {} {} {}", type_id, con_id, arg)
            }
            CPat::ConTs { type_id, con_id, type_args, args, .. } => {
                write!(f, "CPConTs {} {} ", type_id, con_id)?;
                fmt_list(f, type_args)?;
                write!(f, " ")?;
                fmt_list(f, args)
            }
        }
    }
}

impl Display for CPatField {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({},{})", self.name, self.pattern)
    }
}

impl Display for CQType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CQType ")?;
        fmt_list(f, &self.context)?;
        write!(f, " ({})", self.ty)
    }
}

impl Display for CPred {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CPred {{cpred_tc = CTypeclass {}, cpred_args = ", self.class)?;
        fmt_list(f, &self.args)?;
        write!(f, "}}")
    }
}

impl Display for CType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CType::NoType => write!(f, "TGen Unknown position (-1)"),
            CType::Var(id) => {
                write!(f, "TVar (TyVar {{tv_name = {}, tv_num = -1, tv_kind = KVar (-42)}})", id)
            }
            CType::Con(id) => {
                let id_str = format!("{}", id);
                let kind_str = if id_str == "Prelude::Clock" || id_str == "Prelude::Reset" {
                    "Just KStar"
                } else {
                    "Nothing"
                };
                write!(f, "TCon (TyCon {{tcon_name = {}, tcon_kind = {}, tcon_sort = TIabstract}})", id, kind_str)
            }
            CType::Apply(a, b, _) => {
                write!(f, "TAp ({}) ({})", a, b)
            }
            CType::Num(n, pos) => {
                write!(f, "TCon (TyNum {{tynum_value = {}, tynum_pos = ", n)?;
                fmt_position(f, pos)?;
                write!(f, "}})")
            }
            CType::Str(s, pos) => {
                write!(f, "TCon (TyStr {{tystr_value = {:?}, tystr_pos = ", s)?;
                fmt_position(f, pos)?;
                write!(f, "}})")
            }
            CType::Fun(a, b, _) => {
                write!(f, "TAp (TAp (TCon (TyCon {{tcon_name = Prelude::->, tcon_kind = Nothing, tcon_sort = TIabstract}})) ({})) ({})", a, b)
            }
            CType::Forall(params, body, _) => {
                write!(f, "TForall ")?;
                fmt_list(f, params)?;
                write!(f, " ({})", body)
            }
            CType::Paren(t, _) => write!(f, "{}", t),
            CType::Tuple(ts, _) => {
                match ts.len() {
                    0 => write!(f, "TCon (TyCon {{tcon_name = Prelude::PrimUnit, tcon_kind = Nothing, tcon_sort = TIabstract}})"),
                    1 => write!(f, "{}", ts[0]),
                    _ => {
                        fn fmt_nested_pair(ts: &[CType], f: &mut Formatter<'_>) -> fmt::Result {
                            if ts.len() == 1 {
                                write!(f, "{}", ts[0])
                            } else {
                                write!(f, "TAp (TAp (TCon (TyCon {{tcon_name = Prelude::PrimPair, tcon_kind = Nothing, tcon_sort = TIabstract}})) ({})) (", ts[0])?;
                                fmt_nested_pair(&ts[1..], f)?;
                                write!(f, ")")
                            }
                        }
                        fmt_nested_pair(ts, f)
                    }
                }
            }
            CType::List(t, _) => {
                write!(f, "TAp (TCon (TyCon {{tcon_name = Prelude::List, tcon_kind = Nothing, tcon_sort = TIabstract}})) ({})", t)
            }
            CType::Infix(l, op, r, _) => {
                write!(f, "TAp (TAp (TCon (TyCon {{tcon_name = {}, tcon_kind = Nothing, tcon_sort = TIabstract}})) ({})) ({})", op, l, r)
            }
            CType::DefMonad(pos) => {
                write!(f, "TDefMonad ")?;
                fmt_position(f, pos)
            }
        }
    }
}

impl Display for CTypeParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self.kind {
            Some(k) => write!(f, "TyVar {{tv_name = {}, tv_num = -1, tv_kind = {}}}", self.name, k),
            None => write!(f, "TyVar {{tv_name = {}, tv_num = -1, tv_kind = KVar (-42)}}", self.name),
        }
    }
}

impl Display for CKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CKind::Star(_) => write!(f, "KStar"),
            CKind::Num(_) => write!(f, "KNum"),
            CKind::Str(_) => write!(f, "KStr"),
            CKind::Fun(a, b, _) => {
                write!(f, "Kfun ")?;
                fmt_kind_as_arg(f, a)?;
                write!(f, " ")?;
                fmt_kind_as_arg(f, b)
            }
            CKind::Paren(k, _) => write!(f, "{}", k),
        }
    }
}

impl Display for CPragma {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CPragma::Properties(id, props) => {
                write!(f, "Pproperties {} [", id)?;
                for (i, prop) in props.iter().enumerate() {
                    if i > 0 { write!(f, ",")?; }
                    write!(f, "{}", prop)?;
                }
                write!(f, "]")
            }
            CPragma::Synthesize(id) => {
                write!(f, "Pproperties {} [PPverilog]", id)
            }
            CPragma::NoInline(id) => {
                write!(f, "Pnoinline [{}]", id)
            }
        }
    }
}

impl Display for CPragmaProperty {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match (self.name.as_str(), &self.value) {
            ("verilog", _) => write!(f, "PPverilog"),
            ("deprecate", Some(msg)) => write!(f, "PPdeprecate {:?}", msg),
            ("deprecate", None) => write!(f, "PPdeprecate \"\""),
            (name, Some(val)) => write!(f, "PP{} {:?}", name, val),
            (name, None) => write!(f, "PP{}", name),
        }
    }
}

impl Display for PProp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            PProp::Verilog => write!(f, "PPverilog"),
            PProp::ForeignImport(id) => write!(f, "PPforeignImport {}", id),
            PProp::AlwaysReady(names) => {
                write!(f, "PPalwaysReady ")?;
                fmt_longname_list(f, names)
            }
            PProp::AlwaysEnabled(names) => {
                write!(f, "PPalwaysEnabled ")?;
                fmt_longname_list(f, names)
            }
            PProp::EnabledWhenReady(names) => {
                write!(f, "PPenabledWhenReady ")?;
                fmt_longname_list(f, names)
            }
            PProp::ScanInsert(n) => write!(f, "PPscanInsert {}", n),
            PProp::BitBlast => write!(f, "PPbitBlast"),
            PProp::ClockPrefix(s) => write!(f, "PPCLK {:?}", s),
            PProp::GatePrefix(s) => write!(f, "PPGATE {:?}", s),
            PProp::ResetPrefix(s) => write!(f, "PPRSTN {:?}", s),
            PProp::ClockOsc(pairs) => {
                write!(f, "PPclock_osc ")?;
                fmt_id_string_pairs(f, pairs)
            }
            PProp::ClockGate(pairs) => {
                write!(f, "PPclock_gate ")?;
                fmt_id_string_pairs(f, pairs)
            }
            PProp::GateInhigh(ids) => {
                write!(f, "PPgate_inhigh ")?;
                fmt_id_list(f, ids)
            }
            PProp::GateUnused(ids) => {
                write!(f, "PPgate_unused ")?;
                fmt_id_list(f, ids)
            }
            PProp::ResetPort(pairs) => {
                write!(f, "PPreset_port ")?;
                fmt_id_string_pairs(f, pairs)
            }
            PProp::ArgParam(pairs) => {
                write!(f, "PParg_param ")?;
                fmt_id_string_pairs(f, pairs)
            }
            PProp::ArgPort(pairs) => {
                write!(f, "PParg_port ")?;
                fmt_id_string_pairs(f, pairs)
            }
            PProp::ArgClockedBy(pairs) => {
                write!(f, "PParg_clocked_by ")?;
                fmt_id_string_pairs(f, pairs)
            }
            PProp::ArgResetBy(pairs) => {
                write!(f, "PParg_reset_by ")?;
                fmt_id_string_pairs(f, pairs)
            }
            PProp::Options(opts) => {
                write!(f, "PPoptions ")?;
                write!(f, "[")?;
                for (i, s) in opts.iter().enumerate() {
                    if i > 0 { write!(f, ",")?; }
                    write!(f, "{:?}", s)?;
                }
                write!(f, "]")
            }
            PProp::GateInputClocks(ids) => {
                write!(f, "PPgate_input_clocks ")?;
                fmt_id_list(f, ids)
            }
            PProp::MethodScheduling(_info) => {
                write!(f, "PPmethod_scheduling <MethodConflictInfo>")
            }
            PProp::Doc(s) => write!(f, "PPdoc {:?}", s),
            PProp::PerfSpec(specs) => {
                write!(f, "PPperf_spec ")?;
                write!(f, "[")?;
                for (i, spec) in specs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    fmt_id_list(f, spec)?;
                }
                write!(f, "]")
            }
            PProp::ClockFamily(ids) => {
                write!(f, "PPclock_family ")?;
                fmt_id_list(f, ids)
            }
            PProp::ClockAncestors(ancestors) => {
                write!(f, "PPclock_ancestors ")?;
                write!(f, "[")?;
                for (i, anc) in ancestors.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    fmt_id_list(f, anc)?;
                }
                write!(f, "]")
            }
            PProp::Param(ids) => {
                write!(f, "PPparam ")?;
                fmt_id_list(f, ids)
            }
            PProp::InstName(id) => write!(f, "PPinst_name {}", id),
            PProp::InstHide => write!(f, "PPinst_hide"),
            PProp::InstHideAll => write!(f, "PPinst_hide_all"),
            PProp::Deprecate(s) => write!(f, "PPdeprecate {:?}", s),
        }
    }
}

fn fmt_id_string_pairs(f: &mut Formatter<'_>, pairs: &[(Id, String)]) -> fmt::Result {
    write!(f, "[")?;
    for (i, (id, s)) in pairs.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "({},{:?})", id, s)?;
    }
    write!(f, "]")
}
