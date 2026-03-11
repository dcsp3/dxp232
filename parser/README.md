# Parser Pipeline Overview

This folder contains the Python orchestration layer for parsing OpenAPI input, generating Agda code, and executing formal checks.

## Well-Formedness (WF)

Everything currently implemented in this folder is centered on WF checking.

### High-Level Flow

Input:
- OpenAPI YAML

WF pipeline:
1. Load YAML and run basic top-level sanity checks.
2. Translate OpenAPI subset into internal DSL dataclasses.
3. Generate Agda API module from the translated DSL.
4. Generate Agda WF runner module that calls `WFAPI? GeneratedAPI`.
5. Compile the runner with `agda --compile`.
6. Execute the compiled binary.
7. Parse runner output (tag + context fields).
8. Print stable CLI result with details/context.

Decision authority:
- Agda (`WFAPI?`) decides WF.
- Python orchestrates IO, code generation, process execution, and formatting.

### WF Modules

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
  - Renders generated Agda WF runner source.
  - Encodes mapping from Agda ill-formed witnesses to stable `WF_ERR:*` tags and context keys/values.

- `error_reporting.py`
  - Human-readable message catalogs for `WF_ERR:*` and `TRANSLATION_ERR:*`.

- `cli.py`
  - Main entrypoint and orchestrator (`check-wf`).

- `test_wf.py`
  - Regression suite for fixtures in `../specs/tests`.
  - Asserts expected tag and expected exit code.

### Agda Backend Behavior (WF)

When `check-wf` runs:
1. Generated modules are written to `../agda/Generated`.
2. Python runs `agda --compile` on the generated WF runner.
3. Agda compiles through the GHC backend (MAlonzo artifacts under `../agda/MAlonzo`).
4. Python executes the produced binary.
5. Python parses the binary output and formats final CLI diagnostics.

### WF CLI Commands

From this `parser` directory:

- `python cli.py <path-to-openapi.yaml>`
  - Generate Agda files only.

- `python cli.py check-wf <path-to-openapi.yaml>`
  - Run full WF pipeline.

- `python test_wf.py`
  - Run WF regression suite.

### WF Output Contract and Exit Codes

- `WF_OK`
  - Exit `0`

- `WF_ERR:*`
  - Representable input that Agda classifies as ill-formed.
  - Exit `1`

- `TRANSLATION_ERR:*`
  - Out-of-subset or unrepresentable input rejected before Agda WF.
  - Exit `2`

- `WF_CHECK_ERROR:*`
  - Infrastructure/runtime issue (parse failure, compile failure, runner failure, unexpected output).
  - Exit `3`

### WF Design Rule

- Python translation rejects only what cannot be represented in the DSL subset.
- Agda WF classifies representable malformed structures.

This keeps formal WF judgments in one place: the Agda checker.

## Compatibility (Planned)

This README is structured so compatibility can be added as a sibling section to WF.

Planned shape:
1. Run WF precheck on both old/new specs.
2. Generate compatibility runner module(s).
3. Execute Agda compatibility decision.
4. Return stable `COMPAT_OK` / `COMPAT_ERR:*` outputs with context.
