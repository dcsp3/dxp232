"""
WF check regression test suite.

Run from the parser/ directory:
    python test_wf.py

Each entry in TESTS is:
    (filename, expected_tag, expected_exit_code, description)

PASS requires both the expected tag to appear in stdout AND the exit code to match.
"""

import subprocess
import sys
from pathlib import Path

ROOT_TESTS_DIR = Path(__file__).parent.parent / "specs" / "tests"
WF_TESTS_DIR = ROOT_TESTS_DIR / "wf"
CLI = Path(__file__).parent / "cli.py"

TESTS = [
    # --- translation-layer rejections (exit 2): unrepresentable inputs ---
    (
        "wf_bad_path_param_not_required.yaml",
        "TRANSLATION_ERR:PATH_PARAMETER_NOT_REQUIRED",
        2,
        "path parameter not marked required:true",
    ),
    (
        "wf_bad_schema_unknown_field.yaml",
        "TRANSLATION_ERR:SCHEMA_UNKNOWN_FIELD",
        2,
        "schema uses unsupported keyword 'format'",
    ),
    (
        "wf_bad_path_level_parameters.yaml",
        "TRANSLATION_ERR:PATH_LEVEL_PARAMETERS_UNSUPPORTED",
        2,
        "path-level parameters are out of subset",
    ),
    # --- Agda WF rejections (representable but ill-formed) ---
    (
        "wf_bad_component_primitive_properties.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_PRIM_HAS_PROPERTIES",
        1,
        "component primitive schema incorrectly has properties",
    ),
    (
        "wf_bad_component_prim_items.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_PRIM_HAS_ITEMS",
        1,
        "component primitive schema incorrectly has items",
    ),
    (
        "wf_bad_component_prim_required.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_PRIM_HAS_REQUIRED",
        1,
        "component primitive schema incorrectly has required",
    ),
    (
        "wf_bad_component_array_missing_items.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_ARRAY_MISSING_ITEMS",
        1,
        "component array schema missing items",
    ),
    (
        "wf_bad_component_array_has_properties.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_ARRAY_HAS_PROPERTIES",
        1,
        "component array schema incorrectly has properties",
    ),
    (
        "wf_bad_component_array_has_required.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_ARRAY_HAS_REQUIRED",
        1,
        "component array schema incorrectly has required",
    ),
    (
        "wf_bad_component_object_has_items.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_OBJECT_HAS_ITEMS",
        1,
        "component object schema incorrectly has items",
    ),
    (
        "wf_bad_component_object_property_ill_formed.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_OBJECT_PROPERTY_ILL_FORMED",
        1,
        "component object property schema is ill-formed",
    ),
    (
        "wf_bad_required.yaml",
        "WF_ERR:API_ENDPOINT_RESPONSE_SCHEMA_OBJECT_MISSING_REQUIRED",
        1,
        "response object requires a field not in properties",
    ),
    (
        "wf_bad_body_missing_required.yaml",
        "WF_ERR:API_ENDPOINT_BODY_SCHEMA_OBJECT_MISSING_REQUIRED",
        1,
        "request body object requires a field not in properties",
    ),
    (
        "wf_bad_component_missing_required.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_OBJECT_MISSING_REQUIRED",
        1,
        "component schema object requires a field not in properties",
    ),
    (
        "wf_bad_component_object_duplicate_required.yaml",
        "WF_ERR:API_COMPONENT_SCHEMA_OBJECT_DUPLICATE_REQUIRED",
        1,
        "component object has duplicate required entries",
    ),
    (
        "wf_bad_placeholder_not_declared.yaml",
        "WF_ERR:API_ENDPOINT_PATH_ILL_FORMED",
        1,
        "path placeholder {id} with no matching parameter declared",
    ),
    (
        "wf_bad_orphan_path_parameter.yaml",
        "WF_ERR:API_ENDPOINT_PATH_ILL_FORMED",
        1,
        "path parameter declared but not present in path placeholders",
    ),
    (
        "wf_bad_duplicate_placeholder.yaml",
        "WF_ERR:API_ENDPOINT_PATH_ILL_FORMED",
        1,
        "duplicate placeholder names in path",
    ),
    (
        "wf_bad_duplicate_parameters.yaml",
        "WF_ERR:API_ENDPOINT_DUPLICATE_PARAMETERS",
        1,
        "endpoint has duplicate parameter keys",
    ),
    (
        "wf_bad_body_prim_required.yaml",
        "WF_ERR:API_ENDPOINT_BODY_SCHEMA_PRIM_HAS_REQUIRED",
        1,
        "endpoint body primitive schema incorrectly has required",
    ),
    (
        "wf_bad_response_array_missing_items.yaml",
        "WF_ERR:API_ENDPOINT_RESPONSE_SCHEMA_ARRAY_MISSING_ITEMS",
        1,
        "endpoint response array schema missing items",
    ),
    # --- well-formed specs (should all pass WF) ---
    (
        "wf_ok_simple_get.yaml",
        "WF_OK",
        0,
        "minimal valid GET endpoint",
    ),
    (
        "wf_ok_path_param.yaml",
        "WF_OK",
        0,
        "valid GET with required path parameter",
    ),
    (
        "wf_ok_post_body.yaml",
        "WF_OK",
        0,
        "valid POST with request body and response object",
    ),
]

# These WF tags are part of the Agda model but are not reliably triggerable from
# standard OpenAPI YAML parsing in this pipeline. YAML object keys are unique, so
# duplicate map keys are typically overwritten before translation can observe them.
UNREACHABLE_VIA_YAML = [
    "WF_ERR:API_DUPLICATE_COMPONENTS",
    "WF_ERR:API_DUPLICATE_ENDPOINTS",
    "WF_ERR:API_ENDPOINT_DUPLICATE_STATUSES",
    "WF_ERR:API_COMPONENT_SCHEMA_OBJECT_DUPLICATE_PROPERTIES",
    "WF_ERR:API_ENDPOINT_BODY_SCHEMA_OBJECT_DUPLICATE_PROPERTIES",
    "WF_ERR:API_ENDPOINT_RESPONSE_SCHEMA_OBJECT_DUPLICATE_PROPERTIES",
]


def run_test(filename: str, expected_tag: str, expected_exit: int, description: str) -> bool:
    spec_path = WF_TESTS_DIR / filename
    result = subprocess.run(
        [sys.executable, str(CLI), "check-wf", str(spec_path)],
        capture_output=True,
        text=True,
    )

    output = result.stdout.strip()
    first_line = output.split("\n")[0] if output else "(no output)"

    tag_ok = expected_tag in output
    exit_ok = result.returncode == expected_exit
    passed = tag_ok and exit_ok

    label = "PASS" if passed else "FAIL"
    print(f"[{label}] {filename}")
    print(f"       {description}")
    if not passed:
        if not tag_ok:
            print(f"       Expected tag  : {expected_tag}")
            print(f"       Got (1st line) : {first_line}")
        if not exit_ok:
            print(f"       Expected exit : {expected_exit}   Got exit: {result.returncode}")
    print()

    return passed


def main() -> None:
    print(f"Running {len(TESTS)} WF check tests...\n")
    results = [run_test(*t) for t in TESTS]

    passed = sum(results)
    failed = len(results) - passed
    print(f"Results: {passed} passed, {failed} failed")
    print("\nCoverage note: the following tags are modeled but unreachable via normal YAML key semantics:")
    for tag in UNREACHABLE_VIA_YAML:
        print(f"  - {tag}")

    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
