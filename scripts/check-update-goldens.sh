#!/usr/bin/env bash
set -euo pipefail

# Rebuild the Lean oracle, emit the theorem-backed update matrices, and compare
# them byte for byte with the committed publication/supplement source.
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

golden="$repo_root/test/update-matrices.golden"
doc="$repo_root/docs/theory-m3-source-updates.md"
doc_matrix="$tmp_dir/doc-matrix.txt"
mode="${1:-check}"
case "$mode" in
  check) ;;
  update|--update) mode="update" ;;
  *)
    echo "usage: $0 [check|--update]" >&2
    exit 2
    ;;
esac

cd "$repo_root"

if ! (cd lean && lake build Lara.Examples.Update) > "$tmp_dir/lake-build.log" 2>&1; then
  echo "update goldens: FAIL: lake build Lara.Examples.Update" >&2
  cat "$tmp_dir/lake-build.log" >&2
  exit 1
fi

if ! (cd lean && lake env lean --run UpdateMatrices.lean) > "$tmp_dir/lean.txt" 2> "$tmp_dir/lean.log"; then
  echo "update goldens: FAIL: Lean emitter" >&2
  cat "$tmp_dir/lean.log" >&2
  exit 1
fi

test -s "$tmp_dir/lean.txt" || {
  echo "update goldens: FAIL: Lean emitter produced empty output" >&2
  exit 1
}

if [[ "$mode" == "check" ]]; then
  if [[ ! -f "$golden" ]]; then
    echo "update goldens: FAIL: missing ${golden#"$repo_root/"}" >&2
    echo "  Regenerate with: scripts/check-update-goldens.sh --update" >&2
    exit 1
  fi
  if [[ ! -s "$golden" ]]; then
    echo "update goldens: FAIL: empty ${golden#"$repo_root/"}" >&2
    echo "  Regenerate with: scripts/check-update-goldens.sh --update" >&2
    exit 1
  fi
  if [[ ! -f "$doc" ]]; then
    echo "update goldens: FAIL: missing ${doc#"$repo_root/"}" >&2
    exit 1
  fi
  if [[ ! -s "$doc" ]]; then
    echo "update goldens: FAIL: empty ${doc#"$repo_root/"}" >&2
    exit 1
  fi
fi

if ! python3 - "$mode" "$tmp_dir/lean.txt" "$golden" "$doc" "$doc_matrix" <<'PY'
import os
import signal
import re
import stat
import sys
import tempfile
from pathlib import Path

BEGIN = b"<!-- BEGIN GENERATED UPDATE MATRICES -->"
END = b"<!-- END GENERATED UPDATE MATRICES -->"
FENCE_OPEN = b"```text\n"
FENCE_CLOSE = b"```\n"
SUMMARY_BEGIN = b"<!-- BEGIN GENERATED UPDATE SUMMARY -->"
SUMMARY_END = b"<!-- END GENERATED UPDATE SUMMARY -->"


def generated_block(document: bytes, *, require_content: bool):
    if document.count(BEGIN) != 1 or document.count(END) != 1:
        raise ValueError(
            "documentation must contain exactly one generated update-matrix "
            "BEGIN/END sentinel pair"
        )

    begin = document.index(BEGIN)
    if begin != 0 and document[begin - 1 : begin] != b"\n":
        raise ValueError("generated update-matrix BEGIN sentinel must occupy its own line")

    block_start = begin + len(BEGIN)
    if document[block_start : block_start + 1] != b"\n":
        raise ValueError("generated update-matrix BEGIN sentinel must occupy its own line")
    block_start += 1

    end = document.index(END, block_start)
    if end == 0 or document[end - 1 : end] != b"\n":
        raise ValueError("generated update-matrix END sentinel must occupy its own line")
    end_after = end + len(END)
    if end_after < len(document) and document[end_after : end_after + 1] != b"\n":
        raise ValueError("generated update-matrix END sentinel must occupy its own line")

    fenced = document[block_start:end]
    if not fenced.startswith(FENCE_OPEN) or not fenced.endswith(FENCE_CLOSE):
        raise ValueError(
            "generated update-matrix sentinels must wrap one ```text code block"
        )

    content = fenced[len(FENCE_OPEN) : -len(FENCE_CLOSE)]
    if require_content and not content:
        raise ValueError("documentation update-matrix block is empty")
    return block_start, end, content

def summary_block(document: bytes, *, require_content: bool):
    if document.count(SUMMARY_BEGIN) != 1 or document.count(SUMMARY_END) != 1:
        raise ValueError(
            "documentation must contain exactly one generated update-summary "
            "BEGIN/END sentinel pair"
        )

    begin = document.index(SUMMARY_BEGIN)
    if begin != 0 and document[begin - 1 : begin] != b"\n":
        raise ValueError("generated update-summary BEGIN sentinel must occupy its own line")
    block_start = begin + len(SUMMARY_BEGIN)
    if document[block_start : block_start + 1] != b"\n":
        raise ValueError("generated update-summary BEGIN sentinel must occupy its own line")
    block_start += 1

    end = document.index(SUMMARY_END, block_start)
    if end == 0 or document[end - 1 : end] != b"\n":
        raise ValueError("generated update-summary END sentinel must occupy its own line")
    end_after = end + len(SUMMARY_END)
    if end_after < len(document) and document[end_after : end_after + 1] != b"\n":
        raise ValueError("generated update-summary END sentinel must occupy its own line")

    content = document[block_start:end]
    if require_content and not content:
        raise ValueError("documentation update-summary block is empty")
    return block_start, end, content


def expected_summary(emitted: bytes) -> bytes:
    text = emitted.decode("utf-8")
    core = {}
    for constructor in ("addLeaf", "tighten", "addAttack", "addInstance"):
        match = re.search(
            rf"(?m)^{constructor} grounded core matrix\nreachable=([0-9]+)/([0-9]+)$",
            text,
        )
        if match is None:
            raise ValueError(f"Lean output lacks {constructor} grounded-core count")
        core[constructor] = (int(match.group(1)), int(match.group(2)))

    additive = re.search(
        r"(?m)^addLeaf reachable=([0-9]+)/([0-9]+).*;"
        r" addAttack reachable=([0-9]+)/([0-9]+).*;"
        r" addInstance reachable=([0-9]+)/([0-9]+).*$",
        text,
    )
    if additive is None:
        raise ValueError("Lean output lacks additive public counts")
    public = {
        "addLeaf": (int(additive.group(1)), int(additive.group(2))),
        "addAttack": (int(additive.group(3)), int(additive.group(4))),
        "addInstance": (int(additive.group(5)), int(additive.group(6))),
    }

    tighten_public = re.search(
        r"(?m)^tighten five-valued public matrix under CleanBase\n"
        r"reachable=([0-9]+)/([0-9]+); evidenceBlocked=([0-9]+)$",
        text,
    )
    if tighten_public is None:
        raise ValueError("Lean output lacks tighten public count")
    public["tighten"] = (
        int(tighten_public.group(1)),
        int(tighten_public.group(2)),
    )
    evidence_blocked = int(tighten_public.group(3))

    if any(total != 16 for _, total in core.values()):
        raise ValueError("grounded-core matrices must each have 16 cells")
    if any(total != 20 for _, total in public.values()):
        raise ValueError("public matrices must each have 20 cells")
    for constructor in ("addLeaf", "addAttack", "addInstance"):
        if public[constructor][0] != core[constructor][0]:
            raise ValueError(
                f"{constructor} public reachable count differs from grounded core"
            )

    core_total = sum(total for _, total in core.values())
    core_reachable = sum(reachable for reachable, _ in core.values())
    add_instance = core["addInstance"][0]
    return (
        f"The four core products contain {core_total} cells and {core_reachable} "
        f"reachable cells: `addLeaf` {core['addLeaf'][0]},\n"
        f"`tighten` {core['tighten'][0]}, `addAttack` {core['addAttack'][0]}, and "
        f"`addInstance` {add_instance}. Cells marked `U*` are\n"
        "unreachable only under the premise printed below their matrix. Under "
        "`CleanBase`,\n"
        "the public additive products contain 20 cells each and retain the core "
        "reachable\n"
        "counts, with zero reachable `evidenceBlocked` targets. The `addLeaf` "
        "count also\n"
        "uses the admitted-new-key blocker premise. Under `CleanBase`, the public\n"
        f"`tighten` product has {public['tighten'][0]} reachable cells, including "
        f"{evidence_blocked} `evidenceBlocked`\n"
        "targets.\n\n"
        "The mechanization refuted the predicted `addInstance` count of 13. The "
        "actual\n"
        f"count is {add_instance}. A fresh instance is a sink in the old framework: "
        "freshness prevents\n"
        "old raw attacks from naming it, while old-to-old edges and labels are "
        "preserved.\n"
        "`Grounded.SinkExtension`, `SinkExtension.label_old`,\n"
        "`SinkExtension.justified_preserved`, and\n"
        "`SinkExtension.contested_not_defeated` support\n"
        "`addInstance_sink_status_monotone`. This excludes justified-to-refuted,\n"
        "justified-to-both, and both-to-refuted, in addition to the additive no-gap\n"
        f"column. The matrix and `addInstance_reachable_count` record {add_instance}.\n"
    ).encode("utf-8")


def stage(path: Path, content: bytes, mode: int) -> Path:
    descriptor, staged_name = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=path.parent
    )
    staged = Path(staged_name)
    try:
        os.fchmod(descriptor, mode)
        with os.fdopen(descriptor, "wb") as handle:
            descriptor = -1
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
    except BaseException:
        if descriptor >= 0:
            os.close(descriptor)
        staged.unlink(missing_ok=True)
        raise
    return staged


def replace_both(golden: Path, golden_bytes: bytes, doc: Path, doc_bytes: bytes) -> None:
    paths = (golden, doc)
    originals = {
        golden: golden.read_bytes() if golden.exists() else None,
        doc: doc.read_bytes() if doc.exists() else None,
    }
    modes = {
        path: stat.S_IMODE(path.stat().st_mode) if path.exists() else 0o644
        for path in paths
    }
    staged = {}
    rollback = {}
    temporaries = []
    blocked = {signal.SIGINT, signal.SIGTERM, signal.SIGHUP}
    previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, blocked)
    try:
        for path, content in ((golden, golden_bytes), (doc, doc_bytes)):
            staged[path] = stage(path, content, modes[path])
            temporaries.append(staged[path])
        for path in paths:
            original = originals[path]
            rollback[path] = (
                stage(path, original, modes[path]) if original is not None else None
            )
            if rollback[path] is not None:
                temporaries.append(rollback[path])

        replaced = []
        try:
            for path in paths:
                os.replace(staged[path], path)
                replaced.append(path)
        except BaseException as commit_error:
            rollback_errors = []
            for path in reversed(replaced):
                try:
                    backup = rollback[path]
                    if backup is None:
                        path.unlink(missing_ok=True)
                    else:
                        os.replace(backup, path)
                except BaseException as rollback_error:
                    rollback_errors.append(f"{path}: {rollback_error}")
            if rollback_errors:
                raise RuntimeError(
                    f"replacement failed ({commit_error}); rollback also failed: "
                    + "; ".join(rollback_errors)
                ) from commit_error
            raise RuntimeError(
                f"replacement failed and all changed files were restored: {commit_error}"
            ) from commit_error
    finally:
        for temporary in temporaries:
            temporary.unlink(missing_ok=True)
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)


try:
    mode, emitted_name, golden_name, doc_name, extracted_name = sys.argv[1:]
    emitted = Path(emitted_name).read_bytes()
    golden = Path(golden_name)
    doc = Path(doc_name)
    extracted = Path(extracted_name)

    if not doc.is_file():
        raise ValueError(f"missing {doc}")

    document = doc.read_bytes()
    matrix_start, matrix_end, content = generated_block(
        document, require_content=(mode == "check")
    )
    summary_start, summary_end, summary = summary_block(
        document, require_content=(mode == "check")
    )
    expected = expected_summary(emitted)

    if mode == "check":
        extracted.write_bytes(content)
        if summary != expected:
            raise ValueError("generated documentation update summary is stale")
    elif mode == "update":
        matrix_replacement = FENCE_OPEN + emitted + FENCE_CLOSE
        updated_document = (
            document[:matrix_start] + matrix_replacement + document[matrix_end:]
        )
        summary_start, summary_end, _ = summary_block(
            updated_document, require_content=False
        )
        updated_document = (
            updated_document[:summary_start] + expected + updated_document[summary_end:]
        )
        replace_both(golden, emitted, doc, updated_document)
    else:
        raise ValueError(f"unsupported mode: {mode}")
except Exception as error:
    print(f"update goldens: FAIL: {error}", file=sys.stderr)
    raise SystemExit(1)
PY
then
  exit 1
fi

if [[ "$mode" == "update" ]]; then
  printf 'update goldens: UPDATED %s and %s\n' \
    "${golden#"$repo_root/"}" "${doc#"$repo_root/"}"
  exit 0
fi

if ! diff -u --label lean-emitted.txt --label test/update-matrices.golden \
    "$tmp_dir/lean.txt" "$golden"; then
  echo "update goldens: FAIL: test/update-matrices.golden is stale." >&2
  echo "  Regenerate with: scripts/check-update-goldens.sh --update" >&2
  exit 1
fi

if ! diff -u --label test/update-matrices.golden \
    --label docs/theory-m3-source-updates.md:update-matrices \
    "$golden" "$doc_matrix"; then
  echo "update goldens: FAIL: the generated documentation matrix block is stale." >&2
  echo "  Synchronize both files with: scripts/check-update-goldens.sh --update" >&2
  exit 1
fi

printf 'update goldens: PASS\n'
