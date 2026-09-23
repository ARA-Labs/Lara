#!/usr/bin/env python3
"""Build and audit every repository Lean module, including unimported sources.

--module restricts the audit to named discovered modules for focused regression
checks. The default discovers the complete tree; it never filters *Main modules.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
EXCLUDED = {".git", ".lake", ".claude", ".codex", ".agents", ".superpowers",
            "__pycache__", "node_modules"}


def run(command: list[str], *, env: dict[str, str] | None = None) -> str:
    result = subprocess.run(command, cwd=LEAN, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{' '.join(command)} failed:\n{result.stdout}")
    return result.stdout


def discover() -> dict[str, Path]:
    modules = {}
    for directory, dirs, files in os.walk(ROOT):
        dirs[:] = sorted(d for d in dirs if d not in EXCLUDED)
        for filename in sorted(files):
            if not filename.endswith(".lean"):
                continue
            path = Path(directory) / filename
            if not path.is_relative_to(LEAN):
                raise RuntimeError(f"Lean source outside configured lean/ source root: {path}")
            name = ".".join(path.relative_to(LEAN).with_suffix("").parts)
            modules[name] = path
    return modules


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", dest="modules",
                        help="audit a discovered module (repeatable; default: all)")
    args = parser.parse_args()
    modules = discover()
    selected = sorted(set(args.modules or modules))
    unknown = set(selected) - modules.keys()
    if unknown:
        raise RuntimeError(f"unknown repository modules: {', '.join(sorted(unknown))}")

    # Lake owns Lara and every descendant, even when Lara.lean never imports it.
    # Standalone scripts use temporary oleans so their separate main definitions
    # can be imported one at a time without changing the package's library roots.
    library = [name for name in selected if name == "Lara" or name.startswith("Lara.")]
    targets = sorted(set(library + ["Lara.Semantics.Registry"]))
    run(["lake", "build", *[f"+{name}:olean" for name in targets]])
    with tempfile.TemporaryDirectory(prefix="lara-semantics-audit-") as scratch:
        env = dict(os.environ)
        base_path = run(["lake", "env", "printenv", "LEAN_PATH"]).strip()
        env["LEAN_PATH"] = scratch + os.pathsep + base_path
        lean = run(["lake", "env", "which", "lean"]).strip()
        built: set[str] = set()
        active: set[str] = set()
        by_path = {path.resolve(): name for name, path in modules.items()}

        def build_extra(name: str) -> None:
            if name in built:
                return
            if name in active:
                raise RuntimeError(f"cyclic standalone module imports: {name}")
            active.add(name)
            source = modules[name]
            # Lean's own header parser handles comments, multiline imports and
            # module syntax. Source dependencies do not require existing oleans.
            deps = run(["lake", "env", "lean", "--src-deps", str(source)])
            library_deps = []
            for dep in deps.splitlines():
                local = by_path.get(Path(dep).resolve())
                if local is None:
                    continue
                if local == "Lara" or local.startswith("Lara."):
                    library_deps.append(local)
                else:
                    build_extra(local)
            if library_deps:
                run(["lake", "build", *[f"+{dep}:olean" for dep in sorted(set(library_deps))]])
            output = Path(scratch).joinpath(*name.split(".")).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            run([lean, "-R", str(LEAN), "-o", str(output), str(source)], env=env)
            active.remove(name)
            built.add(name)

        for name in selected:
            if name not in library:
                build_extra(name)
        output = run([lean, "--run", str(LEAN / "SemanticsRegistryAudit.lean"), *selected], env=env)
        print(output, end="")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, OSError) as error:
        print(f"semantics registry: {error}", file=sys.stderr)
        sys.exit(1)
