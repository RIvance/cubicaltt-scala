# Testing Plan for cubicaltt-scala

## Goal
Test the cubical type theory implementation using Mortberg's examples.

## Progress

### ✅ Done
1. Copied 78 `.ctt` files from Mortberg's repository:
   - `examples/` (core examples)
   - `lectures/` (tutorial files)
   - `experiments/` (advanced examples)

2. Created basic type checker tests (4 passing):
   - Universe inference
   - Pi type inference
   - Sigma type inference
   - Universe checking

### 🚧 Next Steps

1. **Complete the parser** to handle `.ctt` syntax:
   - Module declarations
   - Top-level definitions: `name : Type = term`
   - Data types: `data bool = true | false`
   - Split expressions
   - Path types and path literals
   - Import statements

2. **Create integration tests** that:
   - Parse each `.ctt` file
   - Type-check all definitions
   - Verify no type errors

3. **Add specific feature tests**:
   - Path types and composition
   - Transport and Kan filling
   - Glue types and univalence
   - Higher inductive types

## Test Strategy

Start with simple files like `lectures/lecture1.ctt` and gradually work up to complex examples.
