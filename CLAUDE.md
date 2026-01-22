# Rust Bluespec Compiler Frontend Implementation Plan

## Development Environment (MANDATORY)

**CRITICAL: You MUST use the Nix development environment for ALL Rust operations.**

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

# Run tests
nix develop .#bsc-rust -c bash -c "cd bsc-rust && cargo test"

# Check for errors
nix develop .#bsc-rust -c bash -c "cd bsc-rust && cargo check"

# Run clippy
nix develop .#bsc-rust -c bash -c "cd bsc-rust && cargo clippy"
```

### Building Haskell BSC

To build the original Haskell BSC compiler for reference/comparison:

```bash
# Build the original Haskell BSC
nix build .#bsc-original

# The binary will be available at result/bin/bsc
./result/bin/bsc --help
```

### Why This Matters

- The workspace uses `edition = "2024"` which requires Rust nightly
- Dependencies like `smol_str` also use edition 2024
- Stable Rust (1.83) will fail with: `feature 'edition2024' is required`
- The nix flake provides the correct nightly toolchain via `rust-overlay`
- Use `.#bsc-rust` devshell specifically, NOT `.#default` (which requires other dependencies)

### Build Performance Notes

- **Rust builds are slow** - First builds can take 10+ minutes
- **Run builds in foreground** - Watch the output to detect errors early, don't run in background
- **Filter output for errors** - Use `cargo build 2>&1 | grep -E "^(error|Compiling|Finished)"` for concise output
- **Incremental builds are faster** - Only modified crates are recompiled

---

## MANDATORY: Testing After Code Changes

**CRITICAL: After ANY code change, you MUST run the differential tests to ensure the Rust implementation matches the Haskell BSC.**

### Required Tests

Run these tests after every code change:

```bash
# 1. Build and run all tests (includes differential tests)
nix develop .#bsc-rust -c bash -c "cd bsc-rust && cargo test"

# 2. Run differential tests specifically (compares Rust output to Haskell BSC)
nix develop .#bsc-rust -c bash -c "cd bsc-rust && cargo test --package bsc-parser-classic test_differential -- --nocapture"

# 3. Run library parsing test (ALL src/Libraries/*.bs files must parse)
nix develop .#bsc-rust -c bash -c "cd bsc-rust && cargo test --package bsc-parser-classic test_parse_all_libraries -- --nocapture"
```

### What the Differential Tests Do

1. **`test_differential_csyntax_simple`** - Parses a simple package and compares Rust output to `bsc -show-csyntax`
2. **`test_differential_csyntax_data`** - Tests data type declarations against Haskell BSC
3. **`test_differential_all_libraries`** - Compares Rust and Haskell CSyntax output for ALL library files

### Test Environment

The nix development shell automatically sets:
- `BSC_PATH` - Path to Haskell BSC binary for comparison
- `BSC_LIBRARIES_DIR` - Path to `src/Libraries/` for test files

### Acceptance Criteria

- **ALL tests must pass** before considering a change complete
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

## Phase 2: Lexer

Mirror `src/comp/Lex.hs` hand-written lexer:

**Token Types** (LexItem enum):
- Identifiers: `L_varid`, `L_conid`, `L_varsym`, `L_consym`
- Literals: `L_integer(size, base, value)`, `L_float`, `L_char`, `L_string`
- ~30 reserved words: `action`, `case`, `class`, `data`, `deriving`, `do`, `else`, `if`, `import`, `in`, `infix`, `infixl`, `infixr`, `interface`, `instance`, `let`, `letseq`, `module`, `of`, `package`, `primitive`, `qualified`, `rules`, `signature`, `struct`, `then`, `type`, `valueOf`, `stringOf`, `verilog`, `synthesize`, `when`, `where`
- Layout tokens: `L_lcurl_o`, `L_rcurl_o`, `L_semi_o`
- Operators, punctuation, pragmas

**Lexer Features**:
- Haskell-style layout rules (indentation-sensitive)
- CPP line directive handling
- Sized bit literals (`8'hFF`, `4'b1010`)
- String/char escape sequences
- Block and line comments

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

## Phase 4: Incremental Computation (Salsa)

```rust
#[salsa::db]
pub trait CompilerDatabase: salsa::Database {
    // Inputs
    fn source_text(&self, file: FileId) -> Arc<str>;
    fn compiler_flags(&self) -> Arc<Flags>;

    // Derived queries (cached/incremental)
    fn lex(&self, file: FileId) -> Arc<Vec<Token>>;
    fn parse(&self, file: FileId) -> Result<Arc<CPackage>, Vec<Diagnostic>>;
    fn symbol_table(&self, file: FileId) -> Arc<SymTab>;
    fn type_check(&self, file: FileId) -> Result<TypedPackage, Vec<Diagnostic>>;

    // IDE queries
    fn completions_at(&self, file: FileId, pos: Position) -> Vec<CompletionItem>;
    fn hover_at(&self, file: FileId, pos: Position) -> Option<HoverInfo>;
    fn definition_at(&self, file: FileId, pos: Position) -> Option<Location>;
    fn diagnostics(&self, file: FileId) -> Vec<Diagnostic>;
}
```

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

## Phase 7: LSP Server

Use `tower-lsp` crate:

**Capabilities**:
- `textDocument/hover` - Type information on hover
- `textDocument/completion` - Context-aware completions
- `textDocument/definition` - Go-to-definition
- `textDocument/references` - Find all references
- `textDocument/documentSymbol` - Document outline
- `textDocument/semanticTokens` - Semantic highlighting
- Real-time diagnostics (errors/warnings)

**Incremental Updates**:
- On file change: invalidate Salsa queries for that file
- Re-run affected queries (parsing, type checking)
- Push diagnostics to client

---

## Phase 8: Verification Strategy (Differential Testing)

The key verification approach is **differential comparison** between the Rust and Haskell frontends.

### 8.1 CSyntax Differential Comparison

**Approach**: The Haskell BSC already has `-show-csyntax` flag that outputs the CSyntax AST. The Rust implementation must produce **exactly matching output** for verification.

**Key Requirement**: Implement CSyntax serialization in Rust that produces output identical to `bsc -show-csyntax`. This means:
- Same formatting and indentation
- Same order of fields
- Same representation of all AST node types
- Position information may differ but structure must match

**Test Pipeline**:
```bash
# 1. Parse with Haskell BSC, show CSyntax
./result/bin/bsc -show-csyntax test.bs > haskell_csyntax.txt

# 2. Parse with Rust frontend, show CSyntax (same format)
bsc-rust --show-csyntax test.bs > rust_csyntax.txt

# 3. Compare outputs (should be identical except for positions)
diff haskell_csyntax.txt rust_csyntax.txt
```

**Implementation Note**: Study the output format of `bsc -show-csyntax` carefully and implement a matching `Display` or serialization for all CSyntax types in Rust.

### 8.2 Type Comparison

After type checking, compare inferred types using BSC's existing dump flags:

```bash
# Compare types for all top-level definitions
./result/bin/bsc -show-types test.bs > haskell_types.txt
bsc-rust --show-types test.bs > rust_types.txt
diff haskell_types.txt rust_types.txt
```

**Comparison ignores**:
- Source positions (may differ due to implementation)
- Type variable names (only structure matters)
- Order of type class constraints (semantically equivalent)

### 8.3 ISyntax Comparison

After CSyntax->ISyntax conversion, use BSC's existing flags:

```bash
./result/bin/bsc -show-isyntax test.bs > haskell_isyntax.txt
bsc-rust --show-isyntax test.bs > rust_isyntax.txt
diff haskell_isyntax.txt rust_isyntax.txt
```

### 8.4 Test Corpus

1. **BSC Standard Libraries** (MANDATORY - Zero Errors):
   - `src/Libraries/Base1/*.bs` - Core base libraries (includes Prelude.bs)
   - `src/Libraries/Base2/*.bs` - Extended base libraries
   - `src/Libraries/Base3-Contexts/*.bs` - Context libraries
   - `src/Libraries/Base3-Math/*.bs` - Math libraries
   - `src/Libraries/Base3-Misc/*.bs` - Miscellaneous libraries
   - **ALL files in `src/Libraries/` must parse with zero errors**
   - This is the primary validation gate for the Classic parser
2. **BSC Test Suite**: `testsuite/bsc.typechecker/**/*.bsv` (~hundreds of files)
3. **Real Projects**: Open-source BSV projects from GitHub
4. **Edge Cases**: Manually crafted tests for tricky type inference

### 8.5 CI Pipeline

```yaml
# .github/workflows/differential-test.yml
test:
  - name: Build Rust frontend
    run: cargo build --release

  - name: Parse src/Libraries/ (MANDATORY - must pass)
    run: |
      # This is the primary acceptance gate - ALL library files must parse
      for f in src/Libraries/**/*.bs; do
        echo "Parsing: $f"
        bsc-rust --parse-only "$f" || { echo "FAILED: $f"; exit 1; }
      done
      echo "All src/Libraries/ files parsed successfully"

  - name: Run differential tests
    run: |
      for f in testsuite/bsc.typechecker/**/*.bsv; do
        ./result/bin/bsc -show-csyntax "$f" > /tmp/haskell.txt
        bsc-rust --show-csyntax "$f" > /tmp/rust.txt
        diff /tmp/haskell.txt /tmp/rust.txt || exit 1
      done
```

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

1. **Unit Tests**: Test each module independently
2. **Fuzzing**: Property-based testing with `proptest` crate
3. **Error Message Comparison**: Ensure error messages are equivalent
4. **Performance Testing**: Compare parsing/type checking speed

---

## Implementation Order

### Phase A: Setup and Verification Infrastructure

Before starting Rust implementation, set up the verification environment:

1. **Build Haskell BSC** - `nix build .#bsc-original` to get reference implementation
2. **Test existing flags** - Verify `-show-csyntax`, `-show-types`, `-show-isyntax` work as expected
3. **Document output formats** - Study and document the exact output format of each flag
4. **Create test harness** - Script to compare Rust and Haskell output for any source file

### Phase B: Rust Core (with continuous differential testing)

1. **bsc-syntax** - Core AST types (CSyntax, ISyntax, CType)
   - Test: Implement `Display` that matches `bsc -show-csyntax` output exactly

2. **bsc-lexer** - Tokenizer
   - Test: Token stream comparison

3. **bsc-parser-classic** - Classic syntax parser
   - Test: Parse ALL files in `src/Libraries/` with zero errors (MANDATORY)
   - Test: `--show-csyntax` output matches `bsc -show-csyntax` for Classic test files

4. **bsc-parser-bsv** - BSV parser
   - Test: `--show-csyntax` output matches `bsc -show-csyntax` for BSV test files

5. **bsc-types** - Substitution, Unification
   - Test: Unit tests + type comparison on simple files

6. **bsc-symtab** - Symbol table
   - Test: Symbol lookup comparison

7. **bsc-typecheck** - Type inference/checking
   - Test: `--show-types` output matches `bsc -show-types` on testsuite/bsc.typechecker

8. **bsc-iconv** - CSyntax to ISyntax
   - Test: `--show-isyntax` output matches `bsc -show-isyntax`

9. **bsc-iexpand** - ISyntax expansion (lambda elimination, flattening)
   - Mirror `src/comp/IExpand.hs` - the evaluator that expands ISyntax
   - Produces lambda-free, fully flattened AST
   - All function applications are fully applied (no partial application)
   - All let bindings are inlined or lifted to top level
   - Test: Expanded output matches `bsc -show-isyntax-after-iexpand` (or equivalent)

### Phase C: MLIR Backend

10. **bsc-mlir** - BSV MLIR Dialect generation
    - Maps expanded ISyntax to MLIR operations
    - Defines BSV-specific MLIR dialect operations:
      - Module definitions (`bsv.module`)
      - Interface definitions (`bsv.interface`)
      - Rule definitions (`bsv.rule`)
      - Method definitions (`bsv.method`)
      - Register operations (`bsv.reg`, `bsv.reg_read`, `bsv.reg_write`)
      - Wire operations (`bsv.wire`, `bsv.wire_read`, `bsv.wire_write`)
      - FIFO operations (`bsv.fifo_enq`, `bsv.fifo_deq`, etc.)
      - Action composition (`bsv.action_seq`, `bsv.action_par`)
      - Conditional actions (`bsv.action_if`)
    - Integrates with CIRCT dialects (hw, comb, seq, sv)
    - Enables MLIR-based optimizations and transformations

### Phase D: IDE and Integration

11. **bsc-incremental** - Salsa database
12. **bsc-stdlib** - Parse stdlib .bs files
13. **bsc-lsp** - Language server
14. **bsc-parser-treesitter** - Error-tolerant parsing

---

## STRICT RULES

**These rules are non-negotiable and must be followed at all times:**

### ⚠️⚠️⚠️ CRITICAL: READ HASKELL SOURCE FIRST ⚠️⚠️⚠️

**BEFORE making ANY code change to fix Display/Show mismatches, you MUST:**

1. **READ THE COMPLETE HASKELL DATA TYPE DEFINITION** in `src/comp/CSyntax.hs` or `src/comp/CType.hs`
2. **UNDERSTAND how Haskell's `deriving Show` works** for that specific type:
   - Record syntax types: `TypeName {field1 = value1, field2 = value2}`
   - Positional types: `ConstructorName arg1 arg2`
   - Nested values in positional contexts get parentheses: `Outer (Inner x y) z`
   - Nested values in record contexts do NOT get extra parentheses: `{field = Inner x y}`
3. **COMPARE the exact Haskell Show output** with the Rust Display output character-by-character
4. **NEVER GUESS** - if unsure, run `bsc -show-csyntax` on a test file and examine the output

**NEVER take shortcuts. NEVER make assumptions. ALWAYS verify against the Haskell source.**

The Haskell files to reference:
- `src/comp/CSyntax.hs` - CPackage, CDefn, CExpr, CPat, CStmt, etc.
- `src/comp/CType.hs` - Type, TyVar, TyCon, Kind, CQType, CPred, etc.
- `src/comp/Pragma.hs` - PProp, RulePragma, IfcPragma, etc.
- `src/comp/VModInfo.hs` - VModInfo, VFieldInfo, etc.

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

---

## Key Design Decisions

1. **Salsa 2022** for incremental computation (not salsa 0.x)
2. **Hand-written lexer** (matching Haskell performance characteristics)
3. **Hand-written recursive descent parser** for precise parsing
4. **Tree-sitter** for IDE error-recovery and syntax highlighting
5. **String interning** via Salsa's `#[salsa::interned]` for identifiers
6. **Arena allocation** for AST nodes where beneficial

---

## ISyntax Export and IExpand

The frontend mirrors Haskell BSC through IExpand, producing expanded ISyntax for MLIR generation.

### ISyntax (Pre-Expansion)

```rust
// Display implementations matching Haskell output
impl Display for IPackage { ... }
impl Display for IModule { ... }
impl Display for IDef { ... }
impl Display for IExpr { ... }
```

**ISyntax contains**:
- `IPackage`: name, depends, pragmas, definitions
- `IDef`: identifier, type, expression, properties
- `IExpr`: all expression variants (ILam, IAps, IVar, ILAM, ICon)
- `IType`, `IKind`: full type information

**Verification**: Output must match `bsc -show-isyntax` (except for source positions).

### IExpand (Static Elaboration - The Key Transformation)

Mirror `src/comp/IExpand.hs` - the BSC **static elaboration** engine that evaluates ISyntax at compile time.

#### Why IExpand is Critical for MLIR

IExpand transforms functional Bluespec code into **hardware-ready structures**. After IExpand:
- All functional programming abstractions are eliminated
- What remains represents actual hardware: registers, wires, rules, methods, submodule instances
- The output is ideal for direct mapping to MLIR hardware dialects

#### What IExpand Does

**1. Module Instantiation & Elaboration**
- Evaluates the top-level module definition
- Processes module arguments (clocks, resets, ports, parameters)
- Recursively elaborates submodule instantiations
- Creates `IStateVar` structures for each hardware instance

**2. Lambda Elimination (Partial Evaluation)**
- Beta reduction: `(\x -> body) arg` → `body[x/arg]`
- Type lambda instantiation: `ILAM` type applications are resolved
- Uses a **heap** to store intermediate values and avoid recomputation
- Batches substitutions for efficiency

**3. Primitive Evaluation**
- Evaluates compile-time primitives (`PrimIf`, `PrimCase`, arithmetic, etc.)
- File I/O primitives for compile-time scripting
- String/Integer evaluation for module names, rule names

**4. Rule Elaboration**
- Evaluates rule conditions (guards)
- Evaluates rule bodies (actions)
- Extracts implicit conditions from method calls
- Handles rule pragmas (scheduling attributes)

**5. Interface Elaboration**
- Evaluates interface methods
- Generates ready signals for methods
- Associates methods with clocks/resets

**6. Clock/Reset Domain Tracking**
- Tracks which expressions use which clocks/resets
- Validates clock domain crossings
- Creates clock maps for submodule instantiations

#### Key Data Structures in IExpand

- **Heap**: Mutable storage for evaluated expressions (`HUnev`, `HWHNF`, `HNF`)
- **PExpr**: Predicated expressions `P pred expr` - tracks implicit conditions
- **HWireSet**: Wire set tracking clocks/resets used by expressions
- **G monad**: State monad holding evaluation context (heap, flags, symbols)

#### Evaluation Modes

- **eval1/evalAp**: Evaluate to Weak Head Normal Form (WHNF)
- **evalUH**: Evaluate and unheap (follow heap references)
- **walkNF**: Evaluate to Normal Form (no reducible expressions)
- **evalNF**: Full NF evaluation with wire tracking

#### IExpand Output: IModule

IExpand produces an `IModule` containing:
- **State variables** (`IStateVar`): Submodule instances with their connections
- **Rules** (`IRule`): Guards and actions fully evaluated
- **Interface methods** (`IEFace`): Method bodies and ready signals
- **Definitions** (`IDef`): Heap cells turned into local defs (named `__h*`)
- **Clock/reset info**: Domain information for all signals

#### Post-IExpand Characteristics (Guaranteed by BSC)

From `ISyntax.hs`, the `IExpr` type has explicit comments showing what vanishes:

```haskell
data IExpr a
    = ILam Id IType (IExpr a)     -- vanishes after IExpand
    | IAps (IExpr a) [IType] [IExpr a]
    | IVar Id                      -- vanishes after IExpand
    | ILAM Id IKind (IExpr a)     -- vanishes after IExpand
    | ICon Id (IConInfo a)
    | IRefT IType !Int a          -- vanishes after IExpand (heap reference)
```

**After IExpand, only `IAps` and `ICon` remain:**
- **No ILam** - All lambdas have been beta-reduced
- **No ILAM** - All type lambdas have been instantiated
- **No IVar** - All variables have been substituted
- **No IRefT** - All heap references have been resolved
- **No ICDef references** - All function calls have been inlined/evaluated

**AConv (the next stage) enforces this:** If any `ILam`/`ILAM`/`IVar` reaches `AConv.aExpr`, it triggers `internalError` - these cases are simply not handled because they should never occur.

**Hardware structure exposed** - What remains:
- `ICon` with `ICStateVar` - submodule instances
- `ICon` with `ICModPort` - port references
- `ICon` with `ICPrim` - primitive operations (arithmetic, muxes, etc.)
- `ICon` with `ICSel` - method calls on state variables
- `IAps` - applications of primitives and method calls (fully applied)

#### Example Transformation

```haskell
-- Before IExpand (ISyntax with functional abstractions)
module mkCounter;
  let incr = \x -> x + 1
  Reg#(Int#(32)) count <- mkReg(0);
  rule increment;
    count <= incr(count);
  endrule
endmodule

-- After IExpand (IModule with hardware structures)
IModule {
  state_vars: [
    IStateVar { name: "count", vmod: mkReg, args: [0] }
  ],
  rules: [
    IRule {
      name: "increment",
      pred: True,
      body: count._write(count._read + 1)  -- lambda eliminated, inlined
    }
  ]
}
```

**Verification**: Expanded output must match Haskell BSC's post-IExpand representation.

### BSV MLIR Dialect

The expanded ISyntax maps directly to BSV MLIR operations:

```mlir
// Example: A simple register increment module
bsv.module @Counter {
  %r = bsv.reg "count" : !bsv.reg<i32>

  bsv.rule @increment {
    %v = bsv.reg_read %r : i32
    %one = hw.constant 1 : i32
    %next = comb.add %v, %one : i32
    bsv.reg_write %r, %next : i32
  }

  bsv.method @read -> i32 {
    %v = bsv.reg_read %r : i32
    return %v : i32
  }
}
```

**Dialect operations**:
- `bsv.module` - Hardware module definition
- `bsv.interface` - Interface type definition
- `bsv.rule` - Atomic rule (guarded action)
- `bsv.method` - Interface method implementation
- `bsv.reg`, `bsv.reg_read`, `bsv.reg_write` - Register operations
- `bsv.wire` - Combinational wire
- `bsv.action_if` - Conditional action
- `bsv.action_seq`, `bsv.action_par` - Action composition

**Integration with CIRCT**:
- Uses `hw` dialect for hardware structure
- Uses `comb` dialect for combinational logic
- Uses `seq` dialect for sequential elements
- Uses `sv` dialect for SystemVerilog-specific constructs

---

## Standard Library Handling

Parse stdlib `.bs` source files directly from `src/Libraries/`:

```rust
// bsc-stdlib crate
pub struct StdlibLoader {
    libraries_dir: PathBuf,  // src/Libraries
}

impl StdlibLoader {
    /// Parse and type-check all stdlib packages
    pub fn load_prelude(&self) -> Result<SymTab, StdlibError>;

    /// Get stdlib search paths
    pub fn search_paths(&self) -> Vec<PathBuf>;
}
```

**Stdlib files to parse** (located in `src/Libraries/`):
- `Base1/Prelude.bs` - Core types and functions
- `Base1/List.bs`, `Base2/Vector.bs`, `Base2/FIFO.bs`, etc.

This approach:
- Uses the same parser for user code and stdlib
- Parses source files directly from the BSC source tree
- No dependency on original Bluespec installation
- Simplifies the architecture (no .bo format parsing)
