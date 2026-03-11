import re
import subprocess
import sys
from pathlib import Path

from error_reporting import (
    TRANSLATION_ERROR_MESSAGES,
    WF_ERROR_MESSAGES,
    format_context_parts,
)
from loader import OpenAPILoadError, basic_openapi_sanity_check, load_spec
from printer import print_api_module, print_wf_runner_module
from translate import TranslationError, translate_api


def print_usage() -> None:
    print("Usage:")
    print("  python cli.py <openapi.yaml>")
    print("  python cli.py check-wf <openapi.yaml>")


def to_agda_identifier(raw: str) -> str:
    parts = re.split(r"[^A-Za-z0-9]+", raw)
    parts = [part for part in parts if part]
    if not parts:
        return "Spec"

    head = parts[0]
    if not head[0].isalpha():
        head = f"Spec{head}"

    pascal_parts = [head[:1].upper() + head[1:]]
    for part in parts[1:]:
        pascal_parts.append(part[:1].upper() + part[1:])

    return "".join(pascal_parts)


def generate_agda_files(spec_path: str, repo_root: Path) -> tuple[Path, Path]:
    candidate = Path(spec_path)
    if not candidate.is_absolute() and not candidate.exists():
        candidate = repo_root / candidate

    spec = load_spec(str(candidate))
    basic_openapi_sanity_check(spec)

    api = translate_api(spec)

    spec_base = to_agda_identifier(candidate.stem)
    api_module_name = f"Generated.{spec_base}API"
    runner_module_name = f"Generated.{spec_base}RunWFCheck"

    generated_api_code = print_api_module(api, api_module_name)
    wf_runner_code = print_wf_runner_module(runner_module_name, api_module_name)

    generated_dir = repo_root / "agda" / "Generated"
    generated_dir.mkdir(parents=True, exist_ok=True)

    api_path = generated_dir / f"{spec_base}API.agda"
    runner_path = generated_dir / f"{spec_base}RunWFCheck.agda"

    api_path.write_text(generated_api_code, encoding="utf-8")
    runner_path.write_text(wf_runner_code, encoding="utf-8")

    return api_path, runner_path


def run_agda_typecheck(agda_dir: Path, module_path: Path) -> tuple[bool, str]:
    module_rel = module_path.relative_to(agda_dir)

    cmd = [
        "agda",
        str(module_rel).replace("/", "\\"),
        "--transliterate",
    ]

    result = subprocess.run(
        cmd,
        cwd=agda_dir,
        text=True,
        capture_output=True,
    )

    if result.returncode == 0:
        return True, ""

    stderr = (result.stderr or "").strip()
    stdout = (result.stdout or "").strip()
    details = stderr if stderr else stdout
    return False, details


def run_agda_compile_and_execute(agda_dir: Path, module_path: Path) -> tuple[bool, str, str]:
    module_rel = module_path.relative_to(agda_dir)

    compile_cmd = [
        "agda",
        "--compile",
        str(module_rel).replace("/", "\\"),
        "--transliterate",
    ]

    compile_result = subprocess.run(
        compile_cmd,
        cwd=agda_dir,
        text=True,
        capture_output=True,
    )

    if compile_result.returncode != 0:
        stderr = (compile_result.stderr or "").strip()
        stdout = (compile_result.stdout or "").strip()
        details = stderr if stderr else stdout
        return False, "COMPILE_FAILED", details

    exe_name = f"{module_path.stem}.exe"
    exe_path = agda_dir / exe_name
    if not exe_path.exists():
        fallback = agda_dir / module_path.stem
        if fallback.exists():
            exe_path = fallback

    run_result = subprocess.run(
        [str(exe_path)],
        cwd=agda_dir,
        text=True,
        capture_output=True,
    )

    if run_result.returncode != 0:
        stderr = (run_result.stderr or "").strip()
        stdout = (run_result.stdout or "").strip()
        details = stderr if stderr else stdout
        return False, "RUN_FAILED", details

    output = (run_result.stdout or "").strip()
    return True, "", output


def parse_runner_output(output: str) -> tuple[str, str, str, str, str]:
    lines = [line.strip() for line in output.splitlines()]
    if not lines:
        return "", "", "", "", ""

    tag = lines[0]
    key1 = lines[1] if len(lines) > 1 else ""
    value1 = lines[2] if len(lines) > 2 else ""
    key2 = lines[3] if len(lines) > 3 else ""
    value2 = lines[4] if len(lines) > 4 else ""
    return tag, key1, value1, key2, value2


def main():
    if len(sys.argv) not in {2, 3}:
        print_usage()
        sys.exit(1)

    mode = "generate"
    path = ""

    if len(sys.argv) == 2:
        path = sys.argv[1]
    elif len(sys.argv) == 3 and sys.argv[1] == "check-wf":
        mode = "check-wf"
        path = sys.argv[2]
    else:
        print_usage()
        sys.exit(1)

    try:
        repo_root = Path(__file__).resolve().parent.parent
        output_path, wf_runner_path = generate_agda_files(path, repo_root)

        try:
            rel_output = output_path.relative_to(repo_root)
            print(f"Generated {rel_output.as_posix()}")
        except ValueError:
            print(f"Generated {output_path}")

        if mode == "check-wf":
            agda_dir = repo_root / "agda"
            ok, stage, output = run_agda_compile_and_execute(agda_dir, wf_runner_path)

            if not ok:
                print(f"WF_CHECK_ERROR:AGDA_{stage}")
                if output:
                    print("DETAILS_START")
                    print(output)
                    print("DETAILS_END")
                sys.exit(3)

            tag, key1, value1, key2, value2 = parse_runner_output(output)

            if tag == "WF_OK":
                print("WF_OK")
            elif tag.startswith("WF_ERR:"):
                key = tag.split(":", 1)[1].strip()
                print(tag)
                message = WF_ERROR_MESSAGES.get(key)
                if message:
                    print(f"DETAIL: {message}")
                context_line = format_context_parts((key1, value1), (key2, value2))
                if context_line:
                    print(f"CONTEXT: {context_line}")
                sys.exit(1)
            else:
                print("WF_CHECK_ERROR:UNEXPECTED_RUNNER_OUTPUT")
                if output:
                    print(f"DETAIL: {output}")
                sys.exit(3)

    except OpenAPILoadError as error:
        print("WF_CHECK_ERROR:PARSE_OR_TRANSLATION_FAILED")
        print(f"DETAIL: {error}")
        sys.exit(2)
    except TranslationError as error:
        print(f"TRANSLATION_ERR:{error.code}")
        message = TRANSLATION_ERROR_MESSAGES.get(error.code)
        if message:
            print(f"DETAIL: {message}")
        print(f"CAUSE: {error.detail}")
        context_items = list(error.context.items())
        first = context_items[0] if len(context_items) > 0 else ("", "")
        second = context_items[1] if len(context_items) > 1 else ("", "")
        context_line = format_context_parts(first, second)
        if context_line:
            print(f"CONTEXT: {context_line}")
        sys.exit(2)


if __name__ == "__main__":
    main()
