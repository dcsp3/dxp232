"""
Compatibility check regression test suite.

Run from the parser/ directory:
    python test_compat.py

Each entry in TESTS is:
    (old_filename, new_filename, expected_tag, expected_exit_code, description, expected_context_substring)

PASS requires expected tag in stdout and matching exit code.
If expected_context_substring is non-empty, it must also appear in stdout.
"""

import subprocess
import sys
from pathlib import Path

ROOT_TESTS_DIR = Path(__file__).parent.parent / "specs" / "tests"
WF_TESTS_DIR = ROOT_TESTS_DIR / "wf"
COMPAT_TESTS_DIR = ROOT_TESTS_DIR / "compat"
CLI = Path(__file__).parent / "cli.py"

TESTS = [
    (
        "wf_ok_simple_get.yaml",
        "wf_ok_simple_get.yaml",
        "COMPAT_OK",
        0,
        "identical APIs are compatible",
        "",
    ),
    (
        "compat_ok_new_endpoint_old.yaml",
        "compat_ok_new_endpoint_new.yaml",
        "COMPAT_OK",
        0,
        "adding a new endpoint is compatible when old endpoints are preserved",
        "",
    ),
    (
        "compat_ok_optional_parameter_added_old.yaml",
        "compat_ok_optional_parameter_added_new.yaml",
        "COMPAT_OK",
        0,
        "adding a new optional parameter is compatible",
        "",
    ),
    (
        "compat_ok_required_parameter_weakened_old.yaml",
        "compat_ok_required_parameter_weakened_new.yaml",
        "COMPAT_OK",
        0,
        "weakening a required parameter to optional is compatible",
        "",
    ),
    (
        "compat_ok_response_added_old.yaml",
        "compat_ok_response_added_new.yaml",
        "COMPAT_OK",
        0,
        "adding an extra response status is compatible",
        "",
    ),
    (
        "compat_ok_component_added_old.yaml",
        "compat_ok_component_added_new.yaml",
        "COMPAT_OK",
        0,
        "adding a new component is compatible when existing components are preserved",
        "",
    ),
    (
        "compat_ok_component_optional_property_added_old.yaml",
        "compat_ok_component_optional_property_added_new.yaml",
        "COMPAT_OK",
        0,
        "adding an optional component property is compatible",
        "",
    ),
    (
        "wf_ok_simple_get.yaml",
        "wf_ok_post_body.yaml",
        "COMPAT_ERR:ENDPOINT_REMOVED",
        1,
        "removing old endpoint is incompatible",
        "CONTEXT: method=GET",
    ),
    (
        "component_removed_old.yaml",
        "component_removed_new.yaml",
        "COMPAT_ERR:COMPONENT_REMOVED",
        1,
        "removing a shared component is incompatible",
        "CONTEXT: component=User",
    ),
    (
        "component_primitive_changed_old.yaml",
        "component_primitive_changed_new.yaml",
        "COMPAT_ERR:COMPONENT_SCHEMA_PRIMITIVE_CHANGED",
        1,
        "changing a shared component primitive type is incompatible",
        "CONTEXT: component=User type_change=primitive_changed",
    ),
    (
        "component_array_item_drift_old.yaml",
        "component_array_item_drift_new.yaml",
        "COMPAT_ERR:COMPONENT_SCHEMA_ARRAY_ITEM_DRIFT",
        1,
        "changing a shared component array item schema is incompatible",
        "CONTEXT: component=User type_change=primitive_changed",
    ),
    (
        "component_property_removed_old.yaml",
        "component_required_field_removed_new.yaml",
        "COMPAT_ERR:COMPONENT_SCHEMA_REQUIRED_FIELD_REMOVED",
        1,
        "removing a shared component required field is incompatible",
        "CONTEXT: component=User required_field=name",
    ),
    (
        "component_property_removed_old.yaml",
        "component_property_removed_new.yaml",
        "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_REMOVED",
        1,
        "removing a shared component property is incompatible",
        "CONTEXT: component=User property=name",
    ),
    (
        "component_property_removed_old.yaml",
        "component_property_drift_new.yaml",
        "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_DRIFT",
        1,
        "changing a shared component property schema is incompatible",
        "CONTEXT: component=User property=name",
    ),
    (
        "component_primitive_changed_old.yaml",
        "component_shape_mismatch_new.yaml",
        "COMPAT_ERR:COMPONENT_SCHEMA_SHAPE_MISMATCH",
        1,
        "changing a shared component shape is incompatible",
        "CONTEXT: component=User type_change=shape_mismatch",
    ),
    (
        "endpoint_parameter_schema_changed_old.yaml",
        "endpoint_parameter_removed_new.yaml",
        "COMPAT_ERR:ENDPOINT_PARAMETER_REMOVED",
        1,
        "removing a shared parameter is incompatible",
        "CONTEXT: method=GET parameter=q",
    ),
    (
        "endpoint_parameter_schema_changed_old.yaml",
        "endpoint_required_parameter_added_new.yaml",
        "COMPAT_ERR:ENDPOINT_REQUIRED_PARAMETER_ADDED",
        1,
        "strengthening a shared parameter from optional to required is incompatible",
        "CONTEXT: method=GET parameter=q",
    ),
    (
        "endpoint_parameter_schema_changed_old.yaml",
        "endpoint_new_required_parameter_new.yaml",
        "COMPAT_ERR:ENDPOINT_NEW_REQUIRED_PARAMETER",
        1,
        "adding a new required parameter is incompatible",
        "CONTEXT: method=GET parameter=page",
    ),
    (
        "endpoint_response_removed_old.yaml",
        "endpoint_response_removed_new.yaml",
        "COMPAT_ERR:ENDPOINT_RESPONSE_REMOVED",
        1,
        "removing an old response status is incompatible",
        "CONTEXT: method=GET response_status=NotFound",
    ),
    (
        "endpoint_parameter_schema_changed_old.yaml",
        "endpoint_parameter_schema_changed_new.yaml",
        "COMPAT_ERR:ENDPOINT_PARAMETER_SCHEMA_CHANGED",
        1,
        "changing shared parameter schema is incompatible",
        "CONTEXT: method=GET parameter=q",
    ),
    (
        "endpoint_body_primitive_changed_old.yaml",
        "endpoint_body_primitive_changed_new.yaml",
        "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PRIMITIVE_CHANGED",
        1,
        "changing a shared request body primitive type is incompatible",
        "CONTEXT: method=POST type_change=primitive_changed",
    ),
    (
        "endpoint_body_array_item_drift_old.yaml",
        "endpoint_body_array_item_drift_new.yaml",
        "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_ARRAY_ITEM_DRIFT",
        1,
        "changing a shared request body array item schema is incompatible",
        "CONTEXT: method=POST type_change=primitive_changed",
    ),
    (
        "endpoint_body_required_field_removed_old.yaml",
        "endpoint_body_required_field_removed_new.yaml",
        "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_REQUIRED_FIELD_REMOVED",
        1,
        "strengthening a shared request body required field set is incompatible",
        "CONTEXT: method=POST required_field=name",
    ),
    (
        "endpoint_body_property_removed_old.yaml",
        "endpoint_body_property_removed_new.yaml",
        "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PROPERTY_REMOVED",
        1,
        "adding a shared request body property incompatibly is reported",
        "CONTEXT: method=POST property=name",
    ),
    (
        "endpoint_body_property_drift_old.yaml",
        "endpoint_body_property_drift_new.yaml",
        "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_PROPERTY_DRIFT",
        1,
        "changing a shared request body property schema is incompatible",
        "CONTEXT: method=POST property=name",
    ),
    (
        "endpoint_body_primitive_changed_old.yaml",
        "endpoint_body_shape_mismatch_new.yaml",
        "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_SHAPE_MISMATCH",
        1,
        "changing a shared request body shape is incompatible",
        "CONTEXT: method=POST type_change=shape_mismatch",
    ),
    (
        "endpoint_response_primitive_changed_old.yaml",
        "endpoint_response_primitive_changed_new.yaml",
        "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PRIMITIVE_CHANGED",
        1,
        "changing a shared response primitive type is incompatible",
        "CONTEXT: method=GET type_change=primitive_changed",
    ),
    (
        "endpoint_response_array_item_drift_old.yaml",
        "endpoint_response_array_item_drift_new.yaml",
        "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_ARRAY_ITEM_DRIFT",
        1,
        "changing a shared response array item schema is incompatible",
        "CONTEXT: method=GET type_change=primitive_changed",
    ),
    (
        "endpoint_response_object_old.yaml",
        "endpoint_response_required_field_removed_new.yaml",
        "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_REQUIRED_FIELD_REMOVED",
        1,
        "removing a shared response required field is incompatible",
        "CONTEXT: method=GET required_field=name",
    ),
    (
        "endpoint_response_object_old.yaml",
        "endpoint_response_property_removed_new.yaml",
        "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PROPERTY_REMOVED",
        1,
        "removing a shared response property is incompatible",
        "CONTEXT: method=GET property=name",
    ),
    (
        "endpoint_response_object_old.yaml",
        "endpoint_response_property_drift_new.yaml",
        "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_PROPERTY_DRIFT",
        1,
        "changing a shared response property schema is incompatible",
        "CONTEXT: method=GET property=name",
    ),
    (
        "endpoint_response_primitive_changed_old.yaml",
        "endpoint_response_shape_mismatch_new.yaml",
        "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_SHAPE_MISMATCH",
        1,
        "changing a shared response shape is incompatible",
        "CONTEXT: method=GET type_change=shape_mismatch",
    ),
]


UNREACHABLE_VIA_CHECK_COMPAT = [
    "COMPAT_ERR:COMPONENT_DRIFT",
    "COMPAT_ERR:ENDPOINT_DRIFT",
    "COMPAT_ERR:ENDPOINT_ROUTE_CHANGED",
    "COMPAT_ERR:ENDPOINT_METHOD_CHANGED",
    "COMPAT_ERR:ENDPOINT_BODY_SCHEMA_DRIFT",
    "COMPAT_ERR:ENDPOINT_RESPONSE_SCHEMA_DRIFT",
]


def resolve_test_path(filename: str) -> Path:
    wf_candidate = WF_TESTS_DIR / filename
    if wf_candidate.exists():
        return wf_candidate
    return COMPAT_TESTS_DIR / filename


def run_test(
    old_filename: str,
    new_filename: str,
    expected_tag: str,
    expected_exit: int,
    description: str,
    expected_context_substring: str,
) -> bool:
    old_path = resolve_test_path(old_filename)
    new_path = resolve_test_path(new_filename)

    result = subprocess.run(
        [sys.executable, str(CLI), "check-compat", str(old_path), str(new_path)],
        capture_output=True,
        text=True,
    )

    output = result.stdout.strip()
    first_line = output.split("\n")[0] if output else "(no output)"

    tag_ok = expected_tag in output
    exit_ok = result.returncode == expected_exit
    context_ok = True
    if expected_context_substring:
        context_ok = expected_context_substring in output

    passed = tag_ok and exit_ok and context_ok

    label = "PASS" if passed else "FAIL"
    print(f"[{label}] {old_filename} -> {new_filename}")
    print(f"       {description}")
    if not passed:
        if not tag_ok:
            print(f"       Expected tag    : {expected_tag}")
            print(f"       Got (1st line)  : {first_line}")
        if not exit_ok:
            print(f"       Expected exit   : {expected_exit}   Got exit: {result.returncode}")
        if expected_context_substring and not context_ok:
            print(f"       Missing context : {expected_context_substring}")
    print()

    return passed


def main() -> None:
    print(f"Running {len(TESTS)} compatibility check tests...\n")
    results = [run_test(*t) for t in TESTS]

    passed = sum(results)
    failed = len(results) - passed
    print(f"Results: {passed} passed, {failed} failed")
    print("\nCoverage note: the following compat tags are modeled but not observable via check-compat alignment or are internal fallbacks:")
    for tag in UNREACHABLE_VIA_CHECK_COMPAT:
        print(f"  - {tag}")

    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
