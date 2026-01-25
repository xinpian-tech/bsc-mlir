# Rust Bluespec Compiler Frontend Implementation Plan

## Development Environment (MANDATORY)

**CRITICAL: You MUST use the Nix development environment for ALL Operations.**

### Rules for Building Rust Code

1. **ALWAYS use `nix develop .#bsc-rust`** - This is the dedicated Rust development shell:
   ```bash
   nix develop .#bsc-rust -c cargo build
   nix develop .#bsc-rust -c cargo test
   nix develop .#bsc-rust -c cargo check
   ```

2. **NEVER use `nix-shell -p cargo rustc`** - This downloads stable Rust which does NOT support edition 2024.

3. **NEVER use `nix run nixpkgs#cargo`** - Same problem, wrong Rust version.

4. **The project requires Rust NIGHTLY** - Edition 2024 features are used. Only nightly Rust works.

5. **The flake.nix provides the correct toolchain** - It uses `rust-overlay` with nightly Rust.

### Correct Commands

```bash
# Build the project (from bsc-rust directory)
cd bsc-rust && nix develop ..#bsc-rust -c cargo build

# Or from project root
nix develop .#bsc-rust -c bash -c "cd bsc-rust && cargo build"
```

### Building Haskell BSC

To build the original Haskell BSC compiler for reference/comparison:

```bash
nix build .#bsc-original
```
### Build Performance Notes

- **Rust builds are slow** - First builds can take 10+ minutes
- **Run builds in foreground** - Watch the output to detect errors early, don't run in background
- **Filter output for errors** - Use `cargo build 2>&1 | grep -E "^(error|Compiling|Finished)"` for concise output
- **Incremental builds are faster** - Only modified crates are recompiled
---

## MANDATORY: Testing Policy

### NO UNIT TESTS - Differential Testing Only

**CRITICAL: DO NOT write unit tests. The ONLY valid tests are differential tests that compare Rust output against Haskell BSC output file-by-file.**

- **NEVER write unit tests** for individual functions, parsers, lexers, types, etc.
- **NEVER write tests** that don't compare against Haskell BSC output
- **The only valid test** is comparing the entire output of Rust vs Haskell BSC on real source files
- **This ensures 1:1 behavioral compatibility** - unit tests can pass while the overall output differs

### Required Differential Tests

Run these tests after every code change:

```bash
# Run differential tests (compares Rust output to Haskell BSC)
nix develop .#bsc-rust -c bash -c "cd bsc-rust && cargo test"
```

### What the Differential Tests Do

1. **`test_differential_all_libraries`** (bsc-parser-classic) - Compares Rust and Haskell CSyntax output for ALL `src/Libraries/*.bs` files
2. **`test_differential_bsv_testsuite`** (bsc-parser-bsv) - Compares Rust and Haskell CSyntax output for BSV test files

### Test Environment

The nix development shell automatically sets:
- `BSC_PATH` - Path to Haskell BSC binary for comparison
- `BSC_LIBRARIES_DIR` - Path to `src/Libraries/` for test files

### Acceptance Criteria

- **ALL differential tests must pass** before considering a change complete
- **Zero parse failures** on `src/Libraries/*.bs` files
- **Exact CSyntax match** between Rust and Haskell BSC output (string diff)
- If tests fail, fix the issue before proceeding

---

## Chumsky Parser Guidelines (CRITICAL)

The parser uses chumsky 0.12 which has specific patterns that must be followed to avoid issues.

### Avoiding Stack Overflow During Parser Construction

**Problem**: Chumsky parser combinators are eagerly evaluated when function calls are made. If parser functions call each other in a cycle, this causes infinite recursion during parser **construction** (not parsing).

**Example of BROKEN code**:
```rust
// BAD: p_expr() calls p_rule_block() which calls p_rule() which calls p_expr() directly
fn p_expr<'a>() -> impl Parser<...> {
    recursive(|expr| {
        // ...
        let rules = kw_rules().ignore_then(p_rule_block()); // p_rule_block calls p_rule which calls p_expr!
        // ...
    })
}

fn p_rule_block<'a>() -> impl Parser<...> {
    p_rule().separated_by(dsm()).collect()  // calls p_rule
}

fn p_rule<'a>() -> impl Parser<...> {
    recursive(|rule| {
        let body = darrow().ignore_then(p_expr());  // CALLS p_expr() DIRECTLY - STACK OVERFLOW!
        // ...
    })
}
```

**Solution**: Pass the recursive `expr` handle as a parameter to break the cycle:
```rust
// GOOD: Thread the expr handle through to avoid mutual recursion
fn p_expr<'a>() -> impl Parser<...> {
    recursive(|expr| {
        // ...
        let rules = kw_rules().ignore_then(p_rule_block(expr.clone())); // Pass expr handle!
        // ...
    })
}

fn p_rule_block<'a>(
    expr: impl Parser<...> + Clone + 'a,
) -> impl Parser<...> {
    p_rule(expr).separated_by(dsm()).collect()  // Pass expr to p_rule
}

fn p_rule<'a>(
    expr: impl Parser<...> + Clone + 'a,
) -> impl Parser<...> {
    recursive(move |rule| {
        let body = darrow().ignore_then(expr.clone());  // Use the passed handle, not p_expr()!
        // ...
    })
}
```

**Key Rule**: Any parser function that needs to use the expression parser and is called from within `p_expr()` must:
1. Take the `expr` parser as a parameter
2. Use that parameter instead of calling `p_expr()` directly
3. Include `+ 'a` in the parameter bounds for lifetime correctness

### Chumsky 0.12 API Notes

- Use `MappedInput` instead of `SpannedInput` (doesn't exist in 0.12)
- Use `SimpleSpan<u32>` for spans (matches our Span type which uses u32)
- `SimpleSpan::new(context, range)` - takes context first, then range: `SimpleSpan::new((), start..end)`
- Use `.map(eoi_span, |(t, s)| (t, s))` instead of `.spanned()` for token streams
- Error type: `Rich<'a, Token, SimpleSpan<u32>>`

---

## Overview

Rewrite the Bluespec compiler frontend (parsing + typing + expansion) in Rust with 1-to-1 behavioral compatibility, then generate MLIR for hardware synthesis backends.

**Pipeline**: `Source → CSyntax → ISyntax → IExpand → BSV MLIR Dialect`

The Rust implementation mirrors Haskell BSC through IExpand, producing a **lambda-free, fully flattened AST** suitable for direct mapping to MLIR operations.

## Design Requirements (User-Specified)

- **Output Format**: Generate BSV MLIR Dialect from expanded ISyntax (lambda-free, flattened)
- **Language Support**: Both Bluespec Classic and BSV (SystemVerilog syntax)
- **IDE Integration**: LSP Server for VS Code, Neovim, etc.
- **Standard Library**: Re-parse stdlib `.bs` source files directly with Rust parser
- **Backend Target**: BSV MLIR Dialect for integration with CIRCT and other MLIR-based hardware tools

## Critical Source Files to Mirror

| Haskell File | Purpose | Rust Equivalent |
|-------------|---------|-----------------|
| `src/comp/CSyntax.hs` | Concrete syntax AST | `bsc-syntax/src/csyntax.rs` |
| `src/comp/ISyntax.hs` | Internal syntax AST | `bsc-syntax/src/isyntax.rs` |
| `src/comp/CType.hs` | Type/Kind representation | `bsc-types/src/ty.rs` |
| `src/comp/Lex.hs` | Hand-written lexer | `bsc-lexer/src/lexer.rs` |
| `src/comp/Parser/Classic/CParser.hs` | Classic parser | `bsc-parser-classic/` |
| `src/comp/Parser/BSV/CVParser.lhs` | BSV parser | `bsc-parser-bsv/` |
| `src/comp/TypeCheck.hs` | Type checking entry | `bsc-typecheck/src/lib.rs` |
| `src/comp/TIMonad.hs` | Type inference monad | `bsc-typecheck/src/context.rs` |
| `src/comp/TCheck.hs` | Expression type checking | `bsc-typecheck/src/infer.rs` |
| `src/comp/Subst.hs` | Type substitution | `bsc-types/src/subst.rs` |
| `src/comp/Unify.hs` | Unification | `bsc-types/src/unify.rs` |
| `src/comp/SymTab.hs` | Symbol table | `bsc-symtab/src/symtab.rs` |
| `src/comp/IConv.hs` | CSyntax to ISyntax | `bsc-iconv/src/lib.rs` |
| `src/comp/IExpand.hs` | ISyntax expansion (lambda elimination) | `bsc-iexpand/src/lib.rs` |

---

## Phase 3: Parsers

### 3.1 Precise Parsers (for compilation)

**Classic Parser** - Mirror `src/comp/Parser/Classic/CParser.hs`:
- Hand-written recursive descent with parser combinators
- Entry: `pPackage :: CParser CPackage`

**BSV Parser** - Mirror `src/comp/Parser/BSV/CVParser.lhs`:
- Main parser + `CVParserImperative.lhs` + `CVParserAssertion.lhs`
- Handle BSV-specific syntax (module/endmodule, interface/endinterface)

### 3.2 Tree-sitter Grammar (for IDE)

Create `tree-sitter-bluespec` for incremental, error-tolerant parsing:
- Separate grammars for Classic and BSV
- Supports partial/incomplete code
- Used for syntax highlighting, bracket matching, code folding

---

## Phase 5: Type System

### 5.1 Substitution (mirror `src/comp/Subst.hs`)

```rust
pub struct Substitution<'db> {
    mapping: HashMap<TyVar<'db>, Type<'db>>,
}

impl Substitution {
    fn null() -> Self;
    fn singleton(v: TyVar, t: Type) -> Self;
    fn compose(&self, other: &Substitution) -> Substitution;  // @@ operator
    fn lookup(&self, v: &TyVar) -> Option<&Type>;
}

pub trait Types<'db> {
    fn apply_subst(&self, subst: &Substitution<'db>) -> Self;
    fn free_type_vars(&self) -> HashSet<TyVar<'db>>;
}
```

### 5.2 Unification (mirror `src/comp/Unify.hs`)

```rust
pub fn unify_types<'db>(
    bound_tyvars: &HashSet<TyVar<'db>>,
    t1: &Type<'db>,
    t2: &Type<'db>,
    subst: &mut Substitution<'db>,
) -> Result<Vec<(Type<'db>, Type<'db>)>, UnifyError>;

fn var_bind(u: &TyVar, t: &Type, subst: &mut Substitution) -> Result<...>;
fn unify_num(...);  // Special handling for KNum types
```

### 5.3 Type Checking (mirror `src/comp/TCheck.hs`, `TIMonad.hs`)

```rust
pub struct TypeCheckContext<'db> {
    db: &'db dyn CompilerDatabase,
    subst: Substitution<'db>,
    bound_tyvars: Vec<Vec<TyVar<'db>>>,
    explicit_preds: Vec<Vec<EPred<'db>>>,
    next_tyvar: Cell<i32>,
    errors: RefCell<Vec<Diagnostic>>,
}

impl TypeCheckContext {
    fn new_tvar(&self, kind: Kind, pos: Position) -> Type;
    fn unify(&mut self, t1: &Type, t2: &Type) -> Result<...>;
    fn apply_subst<T: Types>(&self, t: T) -> T;
}

pub fn infer_expr(ctx: &mut TypeCheckContext, env: &TypeEnv, expected: &Type, expr: &CExpr)
    -> Result<(Vec<VPred>, CExpr), TypeError>;
```

---

## Phase 6: Symbol Table (mirror `src/comp/SymTab.hs`)

```rust
pub struct SymTab<'db> {
    vars: HashMap<Id<'db>, VarInfo<'db>>,
    cons: HashMap<Id<'db>, Vec<ConInfo<'db>>>,
    types: HashMap<Id<'db>, TypeInfo<'db>>,
    fields: HashMap<Id<'db>, Vec<FieldInfo<'db>>>,
    classes: HashMap<Id<'db>, Class<'db>>,
}

pub struct VarInfo { kind: VarKind, assump: Assump, deprecated: Option<String> }
pub struct TypeInfo { qualified_id: Option<Id>, kind: Kind, type_vars: Vec<Id>, sort: TISort }
pub struct ConInfo { type_id: Id, visible: bool, assump: Assump, tag_info: ConTagInfo }
pub struct FieldInfo { name: Id, type_id: Id, visible: bool, arity: i32, assump: Assump }
```

---

## Phase 8: Verification Strategy (Differential Testing)

The key verification approach is **differential comparison** between the Rust and Haskell frontends.
### 8.6 Existing BSC Flags for Verification

The Haskell BSC already provides flags for dumping internal representations:

| Flag | Output |
|------|--------|
| `-show-csyntax` | CSyntax after parsing |
| `-show-csyntax-typed` | CSyntax after type checking |
| `-show-types` | Type signatures for definitions |
| `-show-isyntax` | ISyntax after conversion |

The Rust implementation must produce **identical output** to these flags for verification. No modifications to Haskell BSC are required.

### 8.7 Additional Testing

1. **Error Message Comparison**: Ensure error messages are equivalent
2. **Performance Testing**: Compare parsing/type checking speed

**NOTE**: No unit tests - all testing is done via differential comparison against Haskell BSC.

---

## STRICT RULES

**These rules are non-negotiable and must be followed at all times:**

### ⚠️⚠️⚠️ CRITICAL: READ HASKELL SOURCE FIRST ⚠️⚠️⚠️

**BEFORE making ANY code change (parsing, Display/Show, data structures), you MUST:**

1. **READ THE COMPLETE HASKELL SOURCE CODE** for the feature you're implementing:
   - For parsing changes: Read `src/comp/Parser/BSV/CVParser.lhs`, `CVParserImperative.lhs`, `CVParserCommon.lhs`
   - For Classic parsing: Read `src/comp/Parser/Classic/CParser.hs`
   - For data types: Read `src/comp/CSyntax.hs`, `src/comp/CType.hs`
   - **UNDERSTAND the exact grammar rules, data transformations, and edge cases**

2. **For parsing changes specifically:**
   - Find the EXACT grammar rule in the Haskell parser (e.g., `pVarDeclParen`, `pModuleBodyStmt`)
   - Understand what AST nodes it produces and how they are converted
   - Trace the full pipeline: parsing → ImperativeStatement → CSyntax conversion
   - Check how the Haskell code handles edge cases and error conditions

3. **UNDERSTAND how Haskell's `deriving Show` works** for that specific type:
   - Record syntax types: `TypeName {field1 = value1, field2 = value2}`
   - Positional types: `ConstructorName arg1 arg2`
   - Nested values in positional contexts get parentheses: `Outer (Inner x y) z`
   - Nested values in record contexts do NOT get extra parentheses: `{field = Inner x y}`

4. **COMPARE the exact Haskell Show output** with the Rust Display output character-by-character

5. **NEVER GUESS** - if unsure, run `bsc -show-csyntax` on a test file and examine the output

**NEVER take shortcuts. NEVER make assumptions. ALWAYS verify against the Haskell source.**

The Haskell files to reference:
- `src/comp/CSyntax.hs` - CPackage, CDefn, CExpr, CPat, CStmt, etc.
- `src/comp/CType.hs` - Type, TyVar, TyCon, Kind, CQType, CPred, etc.
- `src/comp/Pragma.hs` - PProp, RulePragma, IfcPragma, etc.
- `src/comp/VModInfo.hs` - VModInfo, VFieldInfo, etc.
- `src/comp/Parser/BSV/CVParser.lhs` - Main BSV parser
- `src/comp/Parser/BSV/CVParserImperative.lhs` - Imperative statement parsing and conversion
- `src/comp/Parser/BSV/CVParserCommon.lhs` - Common parsing utilities and ImperativeStatement type
- `src/comp/Parser/Classic/CParser.hs` - Classic parser

---

1. **EXACT STRUCTURAL MATCH** - The CSyntax and ISyntax data structures in Rust must be **structurally identical** to their Haskell counterparts. Verification is done by **string diff after serialization**:
   - Rust `--show-csyntax` output must be identical to `bsc -show-csyntax`
   - Rust `--show-isyntax` output must be identical to `bsc -show-isyntax`
   - Any difference in the serialized output indicates a bug that must be fixed
   - This means field names, ordering, and representation must all match exactly

2. **EXACT SEMANTIC MATCH** - The Rust implementation must EXACTLY match the original Haskell BSC semantics. Never simplify, never approximate, never take shortcuts.
   - Every token type must match Lex.hs exactly
   - Every grammar rule must match CParser.hs/CVParser.lhs exactly
   - Every type checking rule must match TCheck.hs exactly
   - When in doubt, read the Haskell source and replicate its behavior precisely

3. **NO FALLBACKS, SIMPLIFICATIONS, OR WORKAROUNDS** - Never implement fallback behavior that differs from BSC
   - If something is unclear, investigate the Haskell source until it's clear
   - If a feature is complex, implement it completely or not at all
   - No "TODO" placeholders in production code paths
   - **NEVER SIMPLIFY** - The code must do exactly what it should do, not a simplified version
   - **NEVER USE WORKAROUNDS** - Fix the root cause, not symptoms
   - **NEVER SKIP FEATURES** - Every feature must be fully implemented

4. **COMPLETE IMPLEMENTATION** - Implement ALL features, not a subset
   - All 69 token types from Lex.hs
   - All grammar rules from CParser.hs
   - All type checking rules from TCheck.hs
   - All error messages must match BSC's error reporting style

5. **src/Libraries/ MUST PARSE WITH ZERO ERRORS** - The Rust Classic parser must successfully parse ALL `.bs` files in `src/Libraries/` without any parsing errors.
   - This includes Base1, Base2, Base3-Contexts, Base3-Math, Base3-Misc
   - Zero tolerance for parse failures on these files
   - This is the primary acceptance test for the Classic parser
   - If any library file fails to parse, the parser is incomplete and must be fixed before proceeding

6. **NO NORMALIZATION IN DISPLAY** - The Display trait implementations must be a direct serialization of the AST structure:
   - **NEVER transform or normalize** the AST during Display
   - If the Rust AST structure differs from Haskell's output, **fix the parser/AST**, not the Display
   - Display must be a 1:1 mapping from AST to string - no post-processing, no rewriting
   - This is a **first principle**: if Display does normalization, debugging becomes impossible
   - Example of WRONG approach: Converting `CExpr::Apply(CExpr::Con(id, []), args)` to `CCon id args` in Display
   - Example of CORRECT approach: Parser produces `CExpr::Con(id, args)` directly, Display just serializes it

7. **DEBUGGING METHODOLOGY** - When fixing structural mismatches:
   - **ALWAYS read the Haskell BSC source code FIRST** to understand the exact data structure
   - Find the structural mismatch between Rust and Haskell by examining the Haskell types and Show instances
   - Fix the Rust code (parser, AST, or Display) to match Haskell exactly
   - **NEVER guess** - always verify against the Haskell source
   - Key files to reference:
     - `src/comp/CSyntax.hs` - CExpr, CDefn, CPackage, etc.
     - `src/comp/CType.hs` - Type, TyVar, TyCon, CQType, etc.
     - `src/comp/Parser/Classic/CParser.hs` - How expressions are constructed
   - Check Haskell's `deriving (Show)` to understand how types are serialized

8. **FOLLOW HASKELL'S DATA STRUCTURES EXACTLY** - When multiple implementation options exist:
   - **ALWAYS follow the original Haskell BSC code structure** to minimize future maintenance burden
   - If Haskell stores a field directly (e.g., `pos_file :: !FString`), Rust must store it directly too
   - If Haskell uses a particular representation, Rust must use the equivalent representation
   - **NEVER simplify or use workarounds** - copy Haskell's approach exactly
   - This ensures the Rust code mirrors Haskell 1:1, making differential testing and maintenance easier
   - Example: Haskell's `Position` stores filename as `FString` directly, so Rust's `Position` must store filename as `Arc<str>` or `SmolStr` directly (NOT use `FileId` lookup)

9. **NO BACKWARD COMPATIBILITY** - Always break APIs to keep code simple:
   - **NEVER add compatibility shims** - just change the API directly
   - **NEVER add wrapper functions** for backward compatibility
   - **NEVER keep old function signatures** alongside new ones
   - When changing a type or function, update ALL call sites immediately
   - Simpler code is more important than API stability
   - This is an internal project - there are no external users to maintain compatibility for

10. **NEVER CREATE SIMPLIFIED VERSIONS** - Always implement the full, correct solution:
    - **NEVER create "simplified versions that compile first"** - this wastes time and leads to wrong designs
    - **NEVER use placeholder implementations** that skip real logic
    - **NEVER implement partial features** with the intent to "fill in later"
    - Always read and understand the Haskell source code FIRST, then implement correctly
    - If you encounter compilation errors, fix them properly instead of simplifying
    - The correct approach: study existing working code (like Classic parser), understand the patterns, then apply them correctly to new code (like BSV parser)

---

## Rust Code Guidelines

The Rust implementation must follow these strict principles:

### Strictness

1. **No silent failures** - Every failure must be explicit with a clear reason
   - Use `Result<T, E>` with descriptive error types, never silently return defaults
   - Avoid `.unwrap()` and `.expect()` in library code; propagate errors properly
   - All error paths must include context about what went wrong and why
   - Use `thiserror` or similar for structured, informative error types

2. **Explicit over implicit** - Avoid hidden behavior
   - No silent type coercions or lossy conversions
   - Use `TryFrom`/`TryInto` instead of `From`/`Into` where conversion can fail
   - Make all assumptions explicit in types and documentation

### Lifetimes

3. **Minimal lifetime scope** - Keep lifetimes as short as possible
   - Prefer owned data over references when the lifetime would be complex
   - Avoid `'static` unless truly necessary
   - Don't expand lifetimes to satisfy the borrow checker; restructure code instead
   - Use scoped arenas or indices rather than long-lived references

4. **Avoid lifetime proliferation** - Don't let lifetimes infect the entire codebase
   - Consider arena allocation with indices for AST nodes
   - Use `Rc`/`Arc` sparingly and only when shared ownership is semantically correct
   - Prefer copying small data over sharing references with complex lifetimes

### Error Handling

5. **Rich error context** - Errors must be actionable
   ```rust
   // BAD: Silent failure
   fn parse_int(s: &str) -> i32 {
       s.parse().unwrap_or(0)
   }

   // GOOD: Explicit failure with context
   fn parse_int(s: &str, context: &str) -> Result<i32, ParseError> {
       s.parse().map_err(|e| ParseError::InvalidInt {
           input: s.to_string(),
           context: context.to_string(),
           source: e,
       })
   }
   ```

6. **Fail fast** - Detect and report errors at the earliest point
   - Validate inputs at API boundaries
   - Use `debug_assert!` for internal invariants during development
   - Make illegal states unrepresentable through the type system
