//! Token types for the BSV (SystemVerilog-like) lexer.
//!
//! Mirrors `SystemVerilogTokens.lhs` and `SystemVerilogKeywords.lhs` from the Haskell implementation.
//!
//! In Haskell: `data SV_Token = SV_Token_Keyword | SV_Token_Id | ...`

use bsc_diagnostics::{Position, Span};
use bsc_syntax::literal::OrderedFloat;
use num_bigint::BigInt;
use smol_str::SmolStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SvBit {
    Zero,
    One,
    X,
    Z,
    DontCare,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SvNumericBase {
    Bin,
    Oct,
    Dec,
    Hex,
}

impl SvNumericBase {
    #[must_use]
    pub fn value(self) -> u32 {
        match self {
            SvNumericBase::Bin => 2,
            SvNumericBase::Oct => 8,
            SvNumericBase::Dec => 10,
            SvNumericBase::Hex => 16,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum SvNumber {
    Integer(BigInt),
    Real(f64),
    Repeated(SvBit),
    Mixed(Vec<(u64, MixedDigit)>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MixedDigit {
    Value(BigInt),
    Bit(SvBit),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub position: Position,
}

impl Token {
    #[must_use]
    pub fn new(kind: TokenKind, span: Span, position: Position) -> Self {
        Self { kind, span, position }
    }

    #[must_use]
    pub fn is_eof(&self) -> bool {
        matches!(self.kind, TokenKind::Eof)
    }
}

impl std::hash::Hash for Token {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        self.span.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Id(SmolStr),
    SystemId(SmolStr),

    Number {
        value: SvNumber,
        bitwidth: Option<BigInt>,
        base: Option<SvNumericBase>,
        signed: bool,
    },
    Integer {
        size: Option<BigInt>,
        base: u32,
        value: BigInt,
    },
    Float(OrderedFloat),
    String(String),
    Directive(SmolStr),

    // SystemVerilog keywords (from SystemVerilogKeywords.lhs)
    KwAlias,
    KwAlways,
    KwAlwaysComb,
    KwAlwaysFf,
    KwAlwaysLatch,
    KwAnd,
    KwAssert,
    KwAssertStrobe,
    KwAssign,
    KwAssume,
    KwAutomatic,
    KwBefore,
    KwBegin,
    KwBind,
    KwBins,
    KwBinsof,
    KwBit,
    KwBreak,
    KwBuf,
    KwBufif0,
    KwBufif1,
    KwByte,
    KwCase,
    KwCasex,
    KwCasez,
    KwCell,
    KwChandle,
    KwClass,
    KwClocking,
    KwCmos,
    KwConfig,
    KwConst,
    KwConstraint,
    KwContext,
    KwContinue,
    KwCover,
    KwCovergroup,
    KwCoverpoint,
    KwCross,
    KwDeassign,
    KwDefault,
    KwDefparam,
    KwDesign,
    KwDisable,
    KwDist,
    KwDo,
    KwEdge,
    KwElse,
    KwEnd,
    KwEndcase,
    KwEndclass,
    KwEndclocking,
    KwEndconfig,
    KwEndfunction,
    KwEndgenerate,
    KwEndgroup,
    KwEndinterface,
    KwEndmodule,
    KwEndpackage,
    KwEndprimitive,
    KwEndprogram,
    KwEndproperty,
    KwEndspecify,
    KwEndsequence,
    KwEndtable,
    KwEndtask,
    KwEnum,
    KwEvent,
    KwExpect,
    KwExport,
    KwExtends,
    KwExtern,
    KwFinal,
    KwFirstMatch,
    KwFor,
    KwForce,
    KwForeach,
    KwForever,
    KwFork,
    KwForkjoin,
    KwFunction,
    KwGenerate,
    KwGenvar,
    KwHighz0,
    KwHighz1,
    KwIf,
    KwIff,
    KwIfnone,
    KwIgnoreBins,
    KwIllegalBins,
    KwImport,
    KwIncdir,
    KwInclude,
    KwInitial,
    KwInout,
    KwInput,
    KwInside,
    KwInstance,
    KwInt,
    KwInteger,
    KwInterface,
    KwIntersect,
    KwJoin,
    KwJoinAny,
    KwJoinNone,
    KwLarge,
    KwLiblist,
    KwLibrary,
    KwLocal,
    KwLocalparam,
    KwLogic,
    KwLongint,
    KwMacromodule,
    KwMatch,
    KwMatches,
    KwMedium,
    KwModport,
    KwModule,
    KwNand,
    KwNegedge,
    KwNew,
    KwNmos,
    KwNor,
    KwNoshowcancelled,
    KwNot,
    KwNotif0,
    KwNotif1,
    KwNull,
    KwOr,
    KwOutput,
    KwPackage,
    KwPacked,
    KwParameter,
    KwPmos,
    KwPosedge,
    KwPrimitive,
    KwPriority,
    KwProgram,
    KwProperty,
    KwProtected,
    KwPull0,
    KwPull1,
    KwPulldown,
    KwPullup,
    KwPulsestyleOnevent,
    KwPulsestyleOndetect,
    KwPure,
    KwRand,
    KwRandc,
    KwRandcase,
    KwRandsequence,
    KwRcmos,
    KwReal,
    KwRealtime,
    KwRef,
    KwReg,
    KwRelease,
    KwRepeat,
    KwReturn,
    KwRnmos,
    KwRpmos,
    KwRtran,
    KwRtranif0,
    KwRtranif1,
    KwScalared,
    KwSequence,
    KwShortint,
    KwShortreal,
    KwShowcancelled,
    KwSigned,
    KwSmall,
    KwSolve,
    KwSpecify,
    KwSpecparam,
    KwStatic,
    KwString,
    KwStrong0,
    KwStrong1,
    KwStruct,
    KwSuper,
    KwSupply0,
    KwSupply1,
    KwTable,
    KwTagged,
    KwTask,
    KwThis,
    KwThroughout,
    KwTime,
    KwTimeprecision,
    KwTimeunit,
    KwTran,
    KwTranif0,
    KwTranif1,
    KwTri,
    KwTri0,
    KwTri1,
    KwTriand,
    KwTrior,
    KwTrireg,
    KwType,
    KwTypedef,
    KwUnion,
    KwUnique,
    KwUnsigned,
    KwUse,
    KwVar,
    KwVectored,
    KwVirtual,
    KwVoid,
    KwWait,
    KwWaitOrder,
    KwWand,
    KwWeak0,
    KwWeak1,
    KwWhile,
    KwWildcard,
    KwWire,
    KwWith,
    KwWithin,
    KwWor,
    KwXnor,
    KwXor,
    // Bluespec 3.8 keywords
    KwAction,
    KwEndaction,
    KwActionvalue,
    KwEndactionvalue,
    KwDeriving,
    KwEndinstance,
    KwLet,
    KwMethod,
    KwEndmethod,
    KwPar,
    KwEndpar,
    KwAbortif,
    KwProvisos,
    KwRule,
    KwEndrule,
    KwRules,
    KwEndrules,
    KwSeq,
    KwEndseq,
    KwGoto,
    KwTypeclass,
    KwEndtypeclass,
    KwValueof,
    KwValueOf,
    KwStringof,
    KwStringOf,
    KwClockedBy,
    KwResetBy,
    KwPoweredBy,
    KwActionType,       // "Action"
    KwActionValueType,  // "ActionValue"

    // Symbols (from SystemVerilogKeywords.lhs svSymbolTable)
    SymPlus,            // +
    SymMinus,           // -
    SymBang,            // !
    SymTilde,           // ~
    SymAnd,             // &
    SymTildeAnd,        // ~&
    SymPipe,            // |
    SymTildePipe,       // ~|
    SymCaret,           // ^
    SymTildeCaret,      // ~^
    SymCaretTilde,      // ^~
    SymStar,            // *
    SymSlash,           // /
    SymPercent,         // %
    SymEqEq,            // ==
    SymBangEq,          // !=
    SymEqEqEq,          // ===
    SymBangEqEq,        // !==
    SymEqQuestionEq,    // =?=
    SymBangQuestionEq,  // !?=
    SymAndAnd,          // &&
    SymPipePipe,        // ||
    SymStarStar,        // **
    SymLt,              // <
    SymLtEq,            // <=
    SymGt,              // >
    SymGtEq,            // >=
    SymGtGt,            // >>
    SymLtLt,            // <<
    SymGtGtGt,          // >>>
    SymLtLtLt,          // <<<
    SymPlusPlus,        // ++
    SymMinusMinus,      // --
    SymTick,            // '
    SymBacktick,        // `
    SymColonColon,      // ::
    SymColon,           // :
    SymDot,             // .
    SymEq,              // =
    SymPlusEq,          // +=
    SymMinusEq,         // -=
    SymComma,           // ,
    SymSemi,            // ;
    SymLParen,          // (
    SymRParen,          // )
    SymLParenStar,      // (*
    SymStarRParen,      // *)
    SymLBracket,        // [
    SymRBracket,        // ]
    SymLBrace,          // {
    SymRBrace,          // }
    SymQuestion,        // ?
    SymHash,            // #
    SymHashHash,        // ##
    SymDollar,          // $
    SymPipeFatArrow,    // |=>
    SymPipeArrow,       // |->
    SymArrow,           // ->
    SymLBracketStar,    // [*
    SymLBracketArrow,   // [->
    SymLBracketEq,      // [=
    // Assignment shortcuts
    SymPipeEq,          // |=
    SymCaretEq,         // ^=
    SymPercentEq,       // %=
    SymAndEq,           // &=
    SymSlashEq,         // /=
    SymLtLtEq,          // <<=
    SymGtGtEq,          // >>=
    SymLtLtLtEq,        // <<<=
    SymGtGtGtEq,        // >>>=
    // Bluespec symbols
    SymDotStar,         // .*
    SymLArrow,          // <-
    SymLtGt,            // <>
    SymDotDot,          // ..
    SymAndAndAnd,       // &&&

    Eof,
}

impl TokenKind {
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            TokenKind::Id(_) => "identifier",
            TokenKind::SystemId(_) => "system identifier",

            TokenKind::Number { .. } => "number",
            TokenKind::Integer { .. } => "integer",
            TokenKind::Float(_) => "float",
            TokenKind::String(_) => "string",
            TokenKind::Directive(_) => "directive",

            TokenKind::KwAlias => "alias",
            TokenKind::KwAlways => "always",
            TokenKind::KwAlwaysComb => "always_comb",
            TokenKind::KwAlwaysFf => "always_ff",
            TokenKind::KwAlwaysLatch => "always_latch",
            TokenKind::KwAnd => "and",
            TokenKind::KwAssert => "assert",
            TokenKind::KwAssertStrobe => "assert_strobe",
            TokenKind::KwAssign => "assign",
            TokenKind::KwAssume => "assume",
            TokenKind::KwAutomatic => "automatic",
            TokenKind::KwBefore => "before",
            TokenKind::KwBegin => "begin",
            TokenKind::KwBind => "bind",
            TokenKind::KwBins => "bins",
            TokenKind::KwBinsof => "binsof",
            TokenKind::KwBit => "bit",
            TokenKind::KwBreak => "break",
            TokenKind::KwBuf => "buf",
            TokenKind::KwBufif0 => "bufif0",
            TokenKind::KwBufif1 => "bufif1",
            TokenKind::KwByte => "byte",
            TokenKind::KwCase => "case",
            TokenKind::KwCasex => "casex",
            TokenKind::KwCasez => "casez",
            TokenKind::KwCell => "cell",
            TokenKind::KwChandle => "chandle",
            TokenKind::KwClass => "class",
            TokenKind::KwClocking => "clocking",
            TokenKind::KwCmos => "cmos",
            TokenKind::KwConfig => "config",
            TokenKind::KwConst => "const",
            TokenKind::KwConstraint => "constraint",
            TokenKind::KwContext => "context",
            TokenKind::KwContinue => "continue",
            TokenKind::KwCover => "cover",
            TokenKind::KwCovergroup => "covergroup",
            TokenKind::KwCoverpoint => "coverpoint",
            TokenKind::KwCross => "cross",
            TokenKind::KwDeassign => "deassign",
            TokenKind::KwDefault => "default",
            TokenKind::KwDefparam => "defparam",
            TokenKind::KwDesign => "design",
            TokenKind::KwDisable => "disable",
            TokenKind::KwDist => "dist",
            TokenKind::KwDo => "do",
            TokenKind::KwEdge => "edge",
            TokenKind::KwElse => "else",
            TokenKind::KwEnd => "end",
            TokenKind::KwEndcase => "endcase",
            TokenKind::KwEndclass => "endclass",
            TokenKind::KwEndclocking => "endclocking",
            TokenKind::KwEndconfig => "endconfig",
            TokenKind::KwEndfunction => "endfunction",
            TokenKind::KwEndgenerate => "endgenerate",
            TokenKind::KwEndgroup => "endgroup",
            TokenKind::KwEndinterface => "endinterface",
            TokenKind::KwEndmodule => "endmodule",
            TokenKind::KwEndpackage => "endpackage",
            TokenKind::KwEndprimitive => "endprimitive",
            TokenKind::KwEndprogram => "endprogram",
            TokenKind::KwEndproperty => "endproperty",
            TokenKind::KwEndspecify => "endspecify",
            TokenKind::KwEndsequence => "endsequence",
            TokenKind::KwEndtable => "endtable",
            TokenKind::KwEndtask => "endtask",
            TokenKind::KwEnum => "enum",
            TokenKind::KwEvent => "event",
            TokenKind::KwExpect => "expect",
            TokenKind::KwExport => "export",
            TokenKind::KwExtends => "extends",
            TokenKind::KwExtern => "extern",
            TokenKind::KwFinal => "final",
            TokenKind::KwFirstMatch => "first_match",
            TokenKind::KwFor => "for",
            TokenKind::KwForce => "force",
            TokenKind::KwForeach => "foreach",
            TokenKind::KwForever => "forever",
            TokenKind::KwFork => "fork",
            TokenKind::KwForkjoin => "forkjoin",
            TokenKind::KwFunction => "function",
            TokenKind::KwGenerate => "generate",
            TokenKind::KwGenvar => "genvar",
            TokenKind::KwHighz0 => "highz0",
            TokenKind::KwHighz1 => "highz1",
            TokenKind::KwIf => "if",
            TokenKind::KwIff => "iff",
            TokenKind::KwIfnone => "ifnone",
            TokenKind::KwIgnoreBins => "ignore_bins",
            TokenKind::KwIllegalBins => "illegal_bins",
            TokenKind::KwImport => "import",
            TokenKind::KwIncdir => "incdir",
            TokenKind::KwInclude => "include",
            TokenKind::KwInitial => "initial",
            TokenKind::KwInout => "inout",
            TokenKind::KwInput => "input",
            TokenKind::KwInside => "inside",
            TokenKind::KwInstance => "instance",
            TokenKind::KwInt => "int",
            TokenKind::KwInteger => "integer",
            TokenKind::KwInterface => "interface",
            TokenKind::KwIntersect => "intersect",
            TokenKind::KwJoin => "join",
            TokenKind::KwJoinAny => "join_any",
            TokenKind::KwJoinNone => "join_none",
            TokenKind::KwLarge => "large",
            TokenKind::KwLiblist => "liblist",
            TokenKind::KwLibrary => "library",
            TokenKind::KwLocal => "local",
            TokenKind::KwLocalparam => "localparam",
            TokenKind::KwLogic => "logic",
            TokenKind::KwLongint => "longint",
            TokenKind::KwMacromodule => "macromodule",
            TokenKind::KwMatch => "match",
            TokenKind::KwMatches => "matches",
            TokenKind::KwMedium => "medium",
            TokenKind::KwModport => "modport",
            TokenKind::KwModule => "module",
            TokenKind::KwNand => "nand",
            TokenKind::KwNegedge => "negedge",
            TokenKind::KwNew => "new",
            TokenKind::KwNmos => "nmos",
            TokenKind::KwNor => "nor",
            TokenKind::KwNoshowcancelled => "noshowcancelled",
            TokenKind::KwNot => "not",
            TokenKind::KwNotif0 => "notif0",
            TokenKind::KwNotif1 => "notif1",
            TokenKind::KwNull => "null",
            TokenKind::KwOr => "or",
            TokenKind::KwOutput => "output",
            TokenKind::KwPackage => "package",
            TokenKind::KwPacked => "packed",
            TokenKind::KwParameter => "parameter",
            TokenKind::KwPmos => "pmos",
            TokenKind::KwPosedge => "posedge",
            TokenKind::KwPrimitive => "primitive",
            TokenKind::KwPriority => "priority",
            TokenKind::KwProgram => "program",
            TokenKind::KwProperty => "property",
            TokenKind::KwProtected => "protected",
            TokenKind::KwPull0 => "pull0",
            TokenKind::KwPull1 => "pull1",
            TokenKind::KwPulldown => "pulldown",
            TokenKind::KwPullup => "pullup",
            TokenKind::KwPulsestyleOnevent => "pulsestyle_onevent",
            TokenKind::KwPulsestyleOndetect => "pulsestyle_ondetect",
            TokenKind::KwPure => "pure",
            TokenKind::KwRand => "rand",
            TokenKind::KwRandc => "randc",
            TokenKind::KwRandcase => "randcase",
            TokenKind::KwRandsequence => "randsequence",
            TokenKind::KwRcmos => "rcmos",
            TokenKind::KwReal => "real",
            TokenKind::KwRealtime => "realtime",
            TokenKind::KwRef => "ref",
            TokenKind::KwReg => "reg",
            TokenKind::KwRelease => "release",
            TokenKind::KwRepeat => "repeat",
            TokenKind::KwReturn => "return",
            TokenKind::KwRnmos => "rnmos",
            TokenKind::KwRpmos => "rpmos",
            TokenKind::KwRtran => "rtran",
            TokenKind::KwRtranif0 => "rtranif0",
            TokenKind::KwRtranif1 => "rtranif1",
            TokenKind::KwScalared => "scalared",
            TokenKind::KwSequence => "sequence",
            TokenKind::KwShortint => "shortint",
            TokenKind::KwShortreal => "shortreal",
            TokenKind::KwShowcancelled => "showcancelled",
            TokenKind::KwSigned => "signed",
            TokenKind::KwSmall => "small",
            TokenKind::KwSolve => "solve",
            TokenKind::KwSpecify => "specify",
            TokenKind::KwSpecparam => "specparam",
            TokenKind::KwStatic => "static",
            TokenKind::KwString => "string",
            TokenKind::KwStrong0 => "strong0",
            TokenKind::KwStrong1 => "strong1",
            TokenKind::KwStruct => "struct",
            TokenKind::KwSuper => "super",
            TokenKind::KwSupply0 => "supply0",
            TokenKind::KwSupply1 => "supply1",
            TokenKind::KwTable => "table",
            TokenKind::KwTagged => "tagged",
            TokenKind::KwTask => "task",
            TokenKind::KwThis => "this",
            TokenKind::KwThroughout => "throughout",
            TokenKind::KwTime => "time",
            TokenKind::KwTimeprecision => "timeprecision",
            TokenKind::KwTimeunit => "timeunit",
            TokenKind::KwTran => "tran",
            TokenKind::KwTranif0 => "tranif0",
            TokenKind::KwTranif1 => "tranif1",
            TokenKind::KwTri => "tri",
            TokenKind::KwTri0 => "tri0",
            TokenKind::KwTri1 => "tri1",
            TokenKind::KwTriand => "triand",
            TokenKind::KwTrior => "trior",
            TokenKind::KwTrireg => "trireg",
            TokenKind::KwType => "type",
            TokenKind::KwTypedef => "typedef",
            TokenKind::KwUnion => "union",
            TokenKind::KwUnique => "unique",
            TokenKind::KwUnsigned => "unsigned",
            TokenKind::KwUse => "use",
            TokenKind::KwVar => "var",
            TokenKind::KwVectored => "vectored",
            TokenKind::KwVirtual => "virtual",
            TokenKind::KwVoid => "void",
            TokenKind::KwWait => "wait",
            TokenKind::KwWaitOrder => "wait_order",
            TokenKind::KwWand => "wand",
            TokenKind::KwWeak0 => "weak0",
            TokenKind::KwWeak1 => "weak1",
            TokenKind::KwWhile => "while",
            TokenKind::KwWildcard => "wildcard",
            TokenKind::KwWire => "wire",
            TokenKind::KwWith => "with",
            TokenKind::KwWithin => "within",
            TokenKind::KwWor => "wor",
            TokenKind::KwXnor => "xnor",
            TokenKind::KwXor => "xor",
            // Bluespec keywords
            TokenKind::KwAction => "action",
            TokenKind::KwEndaction => "endaction",
            TokenKind::KwActionvalue => "actionvalue",
            TokenKind::KwEndactionvalue => "endactionvalue",
            TokenKind::KwDeriving => "deriving",
            TokenKind::KwEndinstance => "endinstance",
            TokenKind::KwLet => "let",
            TokenKind::KwMethod => "method",
            TokenKind::KwEndmethod => "endmethod",
            TokenKind::KwPar => "par",
            TokenKind::KwEndpar => "endpar",
            TokenKind::KwAbortif => "abortif",
            TokenKind::KwProvisos => "provisos",
            TokenKind::KwRule => "rule",
            TokenKind::KwEndrule => "endrule",
            TokenKind::KwRules => "rules",
            TokenKind::KwEndrules => "endrules",
            TokenKind::KwSeq => "seq",
            TokenKind::KwEndseq => "endseq",
            TokenKind::KwGoto => "goto",
            TokenKind::KwTypeclass => "typeclass",
            TokenKind::KwEndtypeclass => "endtypeclass",
            TokenKind::KwValueof => "valueof",
            TokenKind::KwValueOf => "valueOf",
            TokenKind::KwStringof => "stringof",
            TokenKind::KwStringOf => "stringOf",
            TokenKind::KwClockedBy => "clocked_by",
            TokenKind::KwResetBy => "reset_by",
            TokenKind::KwPoweredBy => "powered_by",
            TokenKind::KwActionType => "Action",
            TokenKind::KwActionValueType => "ActionValue",

            TokenKind::SymPlus => "+",
            TokenKind::SymMinus => "-",
            TokenKind::SymBang => "!",
            TokenKind::SymTilde => "~",
            TokenKind::SymAnd => "&",
            TokenKind::SymTildeAnd => "~&",
            TokenKind::SymPipe => "|",
            TokenKind::SymTildePipe => "~|",
            TokenKind::SymCaret => "^",
            TokenKind::SymTildeCaret => "~^",
            TokenKind::SymCaretTilde => "^~",
            TokenKind::SymStar => "*",
            TokenKind::SymSlash => "/",
            TokenKind::SymPercent => "%",
            TokenKind::SymEqEq => "==",
            TokenKind::SymBangEq => "!=",
            TokenKind::SymEqEqEq => "===",
            TokenKind::SymBangEqEq => "!==",
            TokenKind::SymEqQuestionEq => "=?=",
            TokenKind::SymBangQuestionEq => "!?=",
            TokenKind::SymAndAnd => "&&",
            TokenKind::SymPipePipe => "||",
            TokenKind::SymStarStar => "**",
            TokenKind::SymLt => "<",
            TokenKind::SymLtEq => "<=",
            TokenKind::SymGt => ">",
            TokenKind::SymGtEq => ">=",
            TokenKind::SymGtGt => ">>",
            TokenKind::SymLtLt => "<<",
            TokenKind::SymGtGtGt => ">>>",
            TokenKind::SymLtLtLt => "<<<",
            TokenKind::SymPlusPlus => "++",
            TokenKind::SymMinusMinus => "--",
            TokenKind::SymTick => "'",
            TokenKind::SymBacktick => "`",
            TokenKind::SymColonColon => "::",
            TokenKind::SymColon => ":",
            TokenKind::SymDot => ".",
            TokenKind::SymEq => "=",
            TokenKind::SymPlusEq => "+=",
            TokenKind::SymMinusEq => "-=",
            TokenKind::SymComma => ",",
            TokenKind::SymSemi => ";",
            TokenKind::SymLParen => "(",
            TokenKind::SymRParen => ")",
            TokenKind::SymLParenStar => "(*",
            TokenKind::SymStarRParen => "*)",
            TokenKind::SymLBracket => "[",
            TokenKind::SymRBracket => "]",
            TokenKind::SymLBrace => "{",
            TokenKind::SymRBrace => "}",
            TokenKind::SymQuestion => "?",
            TokenKind::SymHash => "#",
            TokenKind::SymHashHash => "##",
            TokenKind::SymDollar => "$",
            TokenKind::SymPipeFatArrow => "|=>",
            TokenKind::SymPipeArrow => "|->",
            TokenKind::SymArrow => "->",
            TokenKind::SymLBracketStar => "[*",
            TokenKind::SymLBracketArrow => "[->",
            TokenKind::SymLBracketEq => "[=",
            TokenKind::SymPipeEq => "|=",
            TokenKind::SymCaretEq => "^=",
            TokenKind::SymPercentEq => "%=",
            TokenKind::SymAndEq => "&=",
            TokenKind::SymSlashEq => "/=",
            TokenKind::SymLtLtEq => "<<=",
            TokenKind::SymGtGtEq => ">>=",
            TokenKind::SymLtLtLtEq => "<<<=",
            TokenKind::SymGtGtGtEq => ">>>=",
            TokenKind::SymDotStar => ".*",
            TokenKind::SymLArrow => "<-",
            TokenKind::SymLtGt => "<>",
            TokenKind::SymDotDot => "..",
            TokenKind::SymAndAndAnd => "&&&",

            TokenKind::Eof => "end of file",
        }
    }

    #[must_use]
    pub fn is_keyword(&self) -> bool {
        !matches!(
            self,
            TokenKind::Id(_)
                | TokenKind::SystemId(_)
                | TokenKind::Integer { .. }
                | TokenKind::Float(_)
                | TokenKind::String(_)
                | TokenKind::Directive(_)
                | TokenKind::SymPlus
                | TokenKind::SymMinus
                | TokenKind::SymBang
                | TokenKind::SymTilde
                | TokenKind::SymAnd
                | TokenKind::SymTildeAnd
                | TokenKind::SymPipe
                | TokenKind::SymTildePipe
                | TokenKind::SymCaret
                | TokenKind::SymTildeCaret
                | TokenKind::SymCaretTilde
                | TokenKind::SymStar
                | TokenKind::SymSlash
                | TokenKind::SymPercent
                | TokenKind::SymEqEq
                | TokenKind::SymBangEq
                | TokenKind::SymEqEqEq
                | TokenKind::SymBangEqEq
                | TokenKind::SymEqQuestionEq
                | TokenKind::SymBangQuestionEq
                | TokenKind::SymAndAnd
                | TokenKind::SymPipePipe
                | TokenKind::SymStarStar
                | TokenKind::SymLt
                | TokenKind::SymLtEq
                | TokenKind::SymGt
                | TokenKind::SymGtEq
                | TokenKind::SymGtGt
                | TokenKind::SymLtLt
                | TokenKind::SymGtGtGt
                | TokenKind::SymLtLtLt
                | TokenKind::SymPlusPlus
                | TokenKind::SymMinusMinus
                | TokenKind::SymTick
                | TokenKind::SymBacktick
                | TokenKind::SymColonColon
                | TokenKind::SymColon
                | TokenKind::SymDot
                | TokenKind::SymEq
                | TokenKind::SymPlusEq
                | TokenKind::SymMinusEq
                | TokenKind::SymComma
                | TokenKind::SymSemi
                | TokenKind::SymLParen
                | TokenKind::SymRParen
                | TokenKind::SymLParenStar
                | TokenKind::SymStarRParen
                | TokenKind::SymLBracket
                | TokenKind::SymRBracket
                | TokenKind::SymLBrace
                | TokenKind::SymRBrace
                | TokenKind::SymQuestion
                | TokenKind::SymHash
                | TokenKind::SymHashHash
                | TokenKind::SymDollar
                | TokenKind::SymPipeFatArrow
                | TokenKind::SymPipeArrow
                | TokenKind::SymArrow
                | TokenKind::SymLBracketStar
                | TokenKind::SymLBracketArrow
                | TokenKind::SymLBracketEq
                | TokenKind::SymPipeEq
                | TokenKind::SymCaretEq
                | TokenKind::SymPercentEq
                | TokenKind::SymAndEq
                | TokenKind::SymSlashEq
                | TokenKind::SymLtLtEq
                | TokenKind::SymGtGtEq
                | TokenKind::SymLtLtLtEq
                | TokenKind::SymGtGtGtEq
                | TokenKind::SymDotStar
                | TokenKind::SymLArrow
                | TokenKind::SymLtGt
                | TokenKind::SymDotDot
                | TokenKind::SymAndAndAnd
                | TokenKind::Eof
        )
    }
}

impl std::hash::Hash for TokenKind {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);

        match self {
            TokenKind::Id(s) => s.hash(state),
            TokenKind::SystemId(s) => s.hash(state),
            TokenKind::Number { value, bitwidth, base, signed } => {
                std::mem::discriminant(value).hash(state);
                if let Some(bw) = bitwidth {
                    true.hash(state);
                    bw.to_signed_bytes_le().hash(state);
                } else {
                    false.hash(state);
                }
                base.hash(state);
                signed.hash(state);
            }
            TokenKind::Integer { size, base, value } => {
                if let Some(sz) = size {
                    true.hash(state);
                    sz.to_signed_bytes_le().hash(state);
                } else {
                    false.hash(state);
                }
                base.hash(state);
                value.to_signed_bytes_le().hash(state);
            }
            TokenKind::Directive(s) => s.hash(state),
            TokenKind::Float(f) => f.hash(state),
            TokenKind::String(s) => s.hash(state),
            _ => {}
        }
    }
}
