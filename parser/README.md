# Parser Pipeline Overview

This folder contains the Python orchestration layer for:

- loading a constrained OpenAPI subset from YAML
- translating it into the internal DSL
- generating Agda modules
- executing well-formedness and compatibility checks
- formatting stable CLI diagnostics

Python is the orchestration layer. Agda is the decision layer for WF and compatibility.

## High-Level Flow

Input:
- OpenAPI YAML

Shared pipeline:
1. Load YAML and run basic top-level sanity checks.
2. Translate the supported OpenAPI subset into internal DSL dataclasses.
3. Generate Agda API modules from the translated DSL.
4. Generate an Agda runner module for the requested check.
5. Compile the runner with `agda --compile`.
6. Execute the compiled binary.
7. Parse the runner output.
8. Print a stable CLI result with optional detail/context lines.

Decision authority:
- Agda decides WF and compatibility.
- Python handles IO, translation, code generation, process execution, and user-facing reporting.

## Modules

- `loader.py`
  - YAML loading and minimal OpenAPI sanity checks.

- `translate.py`
  - OpenAPI subset -> DSL AST translation.
  - Raises `TranslationError` for out-of-subset or unrepresentable inputs.

- `dsl_ast.py`
  - Internal DSL dataclasses (`Schema`, `Endpoint`, `API`, etc.).

- `printer.py`
  - Renders translated DSL into generated Agda API source.

- `wf_runner_printer.py`
  - Renders the generated Agda WF runner.
  - Maps Agda WF witnesses to stable `WF_ERR:*` tags and context fields.

- `compat_runner_printer.py`
  - Renders the generated Agda compatibility runner.
  - Maps Agda drift witnesses to stable `COMPAT_ERR:*` tags and context fields.

- `error_reporting.py`
  - Human-readable message catalogs and context formatting helpers.

- `cli.py`
  - Main entrypoint and orchestration for generation, WF, and compatibility.

- `test_wf.py`
  - WF regression suite for fixtures in `../specs/tests/wf`.

- `test_compat.py`
  - Compatibility regression suite for fixtures in `../specs/tests/compat`.


## Test Layout

- `../specs/tests/wf`
  - WF fixtures

- `../specs/tests/compat`
  - Compatibility fixture pairs

## Backend Behavior

When a check runs:
1. Python writes generated modules to `../agda/Generated`.
2. Python invokes `agda --compile` on the generated runner.
3. Agda compiles through the GHC backend.
4. Python executes the produced binary.
5. Python parses the binary output and formats the final CLI result.

This means correctness comes from the Agda model, while user-facing ergonomics come from the Python layer.
