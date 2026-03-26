# Agda Core

This directory contains the formalisation for our tool.

It defines the syntax, well-formedness rules, and refinement logic used to check backward compatibility between API specifications.

## Structure

- `Everything.agda`: Root module importing all definitions.
- `Prelude.lagda.md`: Standard library imports and base definitions.
- `Syntax/`: The internal DSL for schemas, endpoints, and paths.
- `WellFormed/`: Decidable well-formedness checks (e.g., no duplicate keys).
- `Semantics/`: The definition of API drift and the core `API⊑?` decision procedure.

## Typechecking

To type-check the code manually:

```bash
agda Everything.agda
```

## Execution Flow

The Python pipeline in `parser/` automates the proofs by:
1. Generating Agda modules for the OpenAPI inputs.
2. Compiling the checks using `agda --compile`.
3. Running the output binary to collect the results.
