# BSC-Rust TODO Audit

This document catalogs all `TODO`, `FIXME`, `todo!()`, placeholders, and incomplete implementations in the bsc-rust codebase.

**Audit Date**: 2026-01-17

---

## Summary

| Category | Count | Severity |
|----------|-------|----------|
| `todo!()` macros (will panic) | 6 | CRITICAL |
| TODO comments in type checking | 23 | HIGH |
| TODO comments in parsers | 10 | HIGH |
| TODO comments in IConv | 10 | MEDIUM |
| Placeholder implementations | 15+ | HIGH |
| `.unwrap()` / `.expect()` in lib code | ~20 | MEDIUM |
| "Simplified" type comments | 3 | LOW |

---

## 1. CRITICAL: `todo!()` Macros (Will Panic at Runtime)

These will cause immediate panics when executed:

### `bsc-cli/src/main.rs`

| Line | Code | Fix Required |
|------|------|--------------|
| 60 | `todo!("Parse command not yet implemented")` | Implement parse command |
| 64 | `todo!("Check command not yet implemented")` | Implement check command |
| 72 | `todo!("Export command not yet implemented")` | Implement export command |
| 76 | `todo!("LSP command not yet implemented")` | Implement LSP command |

### `bsc-parser-treesitter/src/lib.rs`

| Line | Code | Fix Required |
|------|------|--------------|
| 12 | `todo!("Implement tree-sitter grammar first")` | Implement grammar |

---

## 2. HIGH: Type Checking TODOs (`bsc-typecheck/src/infer.rs`)

| Line | TODO | Description |
|------|------|-------------|
| 375 | `TODO: Proper IType -> Type conversion and instantiation` | Missing type conversion |
| 390 | `TODO: Proper IType -> Type conversion and instantiation` | Duplicate |
| 815 | `TODO: Check against declared type` | Missing declared type check |
| 861 | `TODO: Unify with expected field type from struct definition` | Missing struct field unification |
| 865 | `TODO: Return actual struct type` | Returns fresh var instead |
| 882 | `TODO: Verify field exists and type matches` | Missing field verification |
| 899 | `TODO: Proper field lookup` | Incomplete field lookup |
| 914 | `TODO: Proper CQType -> Type conversion` | Missing conversion |
| 982 | `TODO: Full module type inference` | Incomplete module inference |
| 995 | `TODO: Full interface type inference` | Incomplete interface inference |
| 1088 | `TODO: Convert Type to IType and add to env` | No-op placeholder |
| 1117 | `TODO: Handle multiple clauses properly` | Only handles first clause |
| 1239 | `TODO: Convert CType to Type and unify` | Missing conversion |
| 1269 | `TODO: Unify struct type with ty and bind field patterns` | Missing struct pattern |
| 1287 | `TODO: Implement proper Bit type handling` | Incomplete Bit handling |
| 1321 | `TODO: Implement kind checking` | Returns Ok(()) placeholder |
| 1331 | `TODO: Implement data type checking` | Returns Ok(()) placeholder |
| 1341 | `TODO: Implement struct checking` | Returns Ok(()) placeholder |
| 1351 | `TODO: Implement class checking` | Returns Ok(()) placeholder |
| 1361 | `TODO: Implement instance checking` | Returns Ok(()) placeholder |
| 1380 | `TODO: Validate the type is well-formed` | Returns Ok(()) placeholder |
| 1390 | `TODO: Validate the type` | Returns Ok(()) placeholder |

---

## 3. HIGH: Parser TODOs

### `bsc-parser-classic/src/lib.rs`

| Line | TODO | Returns |
|------|------|---------|
| 174 | `TODO: Implement full package parsing` | Error placeholder |
| 202 | `TODO: Implement definition parsing` | Error placeholder |
| 226 | `TODO: Implement expression parsing` | Error placeholder |
| 252 | `TODO: Implement pattern parsing` | Error placeholder |
| 273 | `TODO: Implement type parsing` | Error placeholder |

### `bsc-parser-bsv/src/lib.rs`

| Line | TODO | Returns |
|------|------|---------|
| 86 | `TODO: Implement full package parsing` | Error placeholder |
| 107 | `TODO: Implement definition parsing` | Error placeholder |
| 120 | `TODO: Implement expression parsing` | Error placeholder |
| 133 | `TODO: Implement pattern parsing` | Error placeholder |
| 146 | `TODO: Implement type parsing` | Error placeholder |

---

## 4. MEDIUM: IConv TODOs (`bsc-iconv/src/lib.rs`)

| Line | TODO | Description |
|------|------|-------------|
| 591 | `TODO: Handle list comprehension-style generators` | Passes through without handling |
| 672 | `TODO: Add pattern matching` | Missing pattern match |
| 730 | `TODO: Handle more complex patterns` | Limited pattern support |
| 787 | `TODO: Implement proper struct update` | Just evaluates object |
| 919 | `TODO: Implement proper forall handling` | Returns body type only |
| 1060 | `TODO: Implement proper function type splitting` | Returns empty args |
| 1077 | `TODO: Implement proper tuple type extraction` | Incomplete |
| 1083 | `TODO: Implement proper constructor field type extraction` | Incomplete |

---

## 5. MEDIUM: Incremental System TODOs (`bsc-incremental/src/lib.rs`)

| Line | TODO | Description |
|------|------|-------------|
| 118 | `TODO: Add typed definitions, type environment, etc.` | Incomplete TypedPackage |
| 195 | `TODO: Implement actual parsing` | Returns error |
| 214 | `TODO: Implement actual type checking` | Returns error |
| 236 | `TODO: Implement hover` | Returns None |
| 249 | `TODO: Implement completions` | Returns empty vec |

---

## 6. MEDIUM: Stdlib TODOs (`bsc-stdlib/src/lib.rs`)

| Line | TODO | Description |
|------|------|-------------|
| 159 | `TODO: Use bsc_parser_classic to parse the source` | Returns empty SymTab |

---

## 7. LOW: Substitution TODO (`bsc-types/src/subst.rs`)

| Line | TODO | Description |
|------|------|-------------|
| 332 | `TODO: Implement numeric type function evaluation` | Just constructs app |

---

## 8. Placeholder Implementations

These return placeholder values instead of real implementations:

### Type Inference Placeholders

```rust
// bsc-typecheck/src/infer.rs:374
// For now, return a fresh type variable as a placeholder

// bsc-typecheck/src/infer.rs:422
// Return a unit type as a placeholder

// bsc-typecheck/src/infer.rs:864
// Return fresh type variable for now

// bsc-typecheck/src/infer.rs:1089
// For now, this is a no-op placeholder
```

### Parser Placeholders

```rust
// bsc-parser-classic/src/lib.rs:175
// For now, return a placeholder error

// bsc-parser-bsv/src/lib.rs:87
// For now, return a placeholder error indicating this is a skeleton
```

### IConv Placeholders

```rust
// bsc-iconv/src/lib.rs:1300
// For now, use a placeholder PrimOp - the actual op should be determined
op: bsc_syntax::PrimOp::Error, // Placeholder
```

---

## 9. `.unwrap()` / `.expect()` in Library Code

These are acceptable in test code but should be reviewed in library code:

### `bsc-typecheck/src/context.rs`

| Line | Code | Risk |
|------|------|------|
| 207 | `.expect("exit_scope called without matching enter_scope")` | Medium - should return Result |
| 382 | `.expect("checked length")` | Low - guarded by check |
| 529 | `.expect("checked some")` | Low - guarded by check |

### `bsc-iconv/src/lib.rs`

| Line | Code | Risk |
|------|------|------|
| 1179 | `.expect("non-empty")` | Low - guarded by check |

### `bsc-parser-bsv/src/lib.rs`

| Line | Code | Risk |
|------|------|------|
| 162 | `.expect("token stream should contain at least EOF")` | Medium |

---

## 10. "Simplified" Type Comments

These indicate intentional simplifications that may need to be revisited:

| File | Line | Comment |
|------|------|---------|
| `bsc-types/src/ty.rs` | 294 | `Interface pragmas (simplified for now)` |
| `bsc-symtab/src/lib.rs` | 224 | `Interface pragmas (simplified from Pragma.hs)` |

---

## 11. "Not Yet Supported" Errors

These return explicit errors for unimplemented features:

### `bsc-iconv/src/lib.rs`

| Line | Message |
|------|---------|
| 487 | `"list patterns not yet supported"` |
| 501 | `"mixed literal patterns not yet supported"` |

### `bsc-incremental/src/lib.rs`

| Line | Message |
|------|---------|
| 199 | `"Parsing not yet implemented"` |
| 217 | `"Type checking not yet implemented"` |

### Parsers

| File | Message |
|------|---------|
| `bsc-parser-classic` | `"Package parsing not yet implemented"` |
| `bsc-parser-classic` | `"Definition parsing not yet implemented"` |
| `bsc-parser-classic` | `"Expression parsing not yet implemented"` |
| `bsc-parser-classic` | `"Pattern parsing not yet implemented"` |
| `bsc-parser-classic` | `"Type parsing not yet implemented"` |
| `bsc-parser-bsv` | `"BSV package parsing not yet implemented"` |
| `bsc-parser-bsv` | `"BSV definition parsing not yet implemented"` |
| `bsc-parser-bsv` | `"BSV expression parsing not yet implemented"` |
| `bsc-parser-bsv` | `"BSV pattern parsing not yet implemented"` |
| `bsc-parser-bsv` | `"BSV type parsing not yet implemented"` |

---

## 12. Priority Action Items

### P0 - CRITICAL (Blocks Any Execution)

1. **Remove `todo!()` from CLI** - Replace with proper error messages or stub implementations
2. **Remove `todo!()` from tree-sitter** - Return error or stub

### P1 - HIGH (Blocks Type Checking)

1. **Implement type inference core**:
   - `IType -> Type` conversion
   - `CQType -> Type` conversion
   - Kind checking for definitions
   - Struct field unification
   - Module/interface inference

2. **Implement definition checking**:
   - `check_type_defn`
   - `check_data_defn`
   - `check_struct_defn`
   - `check_class_defn`
   - `check_instance_defn`

### P2 - HIGH (Blocks Parsing)

1. **Implement Classic parser**:
   - Package parsing
   - Definition parsing
   - Expression parsing
   - Pattern parsing
   - Type parsing

2. **Implement BSV parser**:
   - Same as Classic parser

### P3 - MEDIUM (Blocks Full Compilation)

1. **Implement IConv**:
   - List comprehension generators
   - Complex patterns
   - Struct updates
   - Forall handling
   - Function type splitting

2. **Implement incremental queries**:
   - Actual parsing
   - Actual type checking
   - Hover info
   - Completions

### P4 - LOW (Polish)

1. **Replace `.expect()` with proper error handling**
2. **Implement numeric type function evaluation in subst.rs**
3. **Complete simplified pragma handling**

---

## 13. Verification Commands

```bash
# Find all todo!() macros
rg 'todo!\(' bsc-rust/crates --type rust

# Find all TODO comments
rg 'TODO' bsc-rust/crates --type rust

# Find all placeholders
rg -i 'placeholder|for now|not yet' bsc-rust/crates --type rust

# Find all .unwrap() / .expect() in non-test code
rg '\.unwrap\(\)|\.expect\(' bsc-rust/crates --type rust | grep -v '#\[test\]' | grep -v 'mod tests'
```
