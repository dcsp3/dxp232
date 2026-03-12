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
        "component_property_removed_old.yaml",
        "component_property_removed_new.yaml",
        "COMPAT_ERR:COMPONENT_SCHEMA_PROPERTY_REMOVED",
        1,
        "removing a shared component property is incompatible",
        "CONTEXT: component=User schema_drift=property_removed",
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

    if failed:
        sys.exit(1)


if __name__ == "__main__":
    main()
