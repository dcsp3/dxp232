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

## Well-Formedness (WF)

### WF Commands

From this `parser` directory:

- `python cli.py <path-to-openapi.yaml>`
  - Generate Agda files only.

- `python cli.py check-wf <path-to-openapi.yaml>`
  - Run the full WF pipeline.

- `python test_wf.py`
  - Run the WF regression suite.

### WF Output Contract

- `WF_OK`
  - Exit `0`

- `WF_ERR:*`
  - Representable input that Agda classifies as ill-formed.
  - Exit `1`

- `TRANSLATION_ERR:*`
  - Out-of-subset or unrepresentable input rejected before Agda WF.
  - Exit `2`

- `WF_CHECK_ERROR:*`
  - Infrastructure/runtime issue such as load failure, compile failure, runner failure, or unexpected output.
  - Exit `3`

### WF Design Rule

- Python translation rejects only what cannot be represented in the DSL subset.
- Agda WF classifies representable malformed structures.

This keeps formal WF judgments centralized in the Agda checker.

## Compatibility

Compatibility is directional: `old -> new` asks whether the new API refines the old API.

That means compatibility is not symmetric:
- `A -> B` can fail
- `B -> A` can pass

### Compatibility Commands

From this `parser` directory:

- `python cli.py check-compat <old-openapi.yaml> <new-openapi.yaml>`
  - Run WF on both specs and then run the compatibility check.

- `python test_compat.py`
  - Run the compatibility regression suite.

### Compatibility Output Contract

- `COMPAT_OK`
  - Exit `0`

- `COMPAT_ERR:*`
  - The new API does not refine the old API.
  - Exit `1`

- `COMPAT_CHECK_ERROR:*`
  - Infrastructure/runtime issue, or one side failed prerequisite WF checking.
  - Exit `3`

Compatibility output may also include:
- `DETAIL: ...`
- `CONTEXT: key=value [key=value]`

Current context fields are intentionally atomic values such as component names, HTTP methods, parameter names, response statuses, and drift kinds.

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
