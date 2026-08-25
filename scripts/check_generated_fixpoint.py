#!/usr/bin/env python3
"""Verify generated artifacts are fresh and reach a one-pass fixpoint."""
from __future__ import annotations

import argparse
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

GENERATORS = [
    ["scripts/gen_stats.py"],
    ["scripts/build_frontier_map.py"],
    ["scripts/gen_result_registry.py"],
    ["scripts/gen_researchos_registry.py"],
    ["scripts/gen_verified_index.py"],
    ["scripts/gen_axiom_audit.py"],
    ["scripts/gen_source_registry.py"],
    [
        "experiments/engine/pkc_smooth_m16_source_faithful_mechanism/generate.py"
    ],
    ["scripts/build_typed_evidence_state.py"],
    ["scripts/research_claims.py"],
    ["scripts/build_research_engine_state.py"],
    ["scripts/build_research_engine_v02_state.py"],
    ["scripts/build_research_shadow_intake.py"],
    ["scripts/build_untrusted_evidence_intake.py"],
    ["scripts/hypothesis_funnel.py"],
    ["scripts/hypothesis_space_funnel.py"],
    ["scripts/hypothesis_space_run_ledger.py"],
    ["scripts/hypothesis_space_campaign.py"],
    ["scripts/hypothesis_ranker.py"],
    ["scripts/build_knowledge_graph.py"],
    ["scripts/coverage_report.py"],
    ["scripts/gen_status.py"],
    ["scripts/build_ecdlp_decision_view.py"],
    ["scripts/export_agent_bundle.py", "--manifest"],
    ["scripts/build_dashboard.py"],
]

PURE_ARTIFACTS = [
    "data/stats.json",
    "badges/theorems.json",
    "data/frontier_map.json",
    "data/result_registry.json",
    "data/researchos_result_registry.json",
    "data/verified_index.json",
    "VERIFIED_INDEX.md",
    "llms.txt",
    "Ecdlp/LedgerAxiomAudit.lean",
    "ResearchOS/LedgerAxiomAudit.lean",
    "data/source_registry.json",
    "experiments/engine/pkc_smooth_m16_source_faithful_mechanism/artifact.json",
    "experiments/engine/pkc_smooth_m16_source_faithful_mechanism/artifact.sha256",
    "data/typed_evidence_state.json",
    "data/research_claim_state.json",
    "data/research_engine_state.json",
    "data/research_engine_v02_state.json",
    "data/research_engine_shadow_intake.json",
    "data/untrusted_evidence_intake/OPUS-ECDLP-SCREEN-ATLAS-2026-07-26.json",
    "data/hypothesis_funnel_state.json",
    "data/hypothesis_space_state.json",
    "data/hypothesis_space_map.json",
    "data/hypothesis_space_run_state.json",
    "data/hypothesis_space_campaign_state.json",
    "data/hypothesis_ranker_state.json",
    "data/knowledge_graph.json",
    "data/knowledge_graph.md",
    "COVERAGE.md",
    "STATUS.md",
    "repo/ECDLP_DECISION_SUBSTRATE.md",
    "bundles/MANIFEST.json",
]

SITE_ARTIFACTS = [
    "dashboard.html",
    "index.html",
    "results.html",
    "explore.html",
    "pilot.html",
    "robots.txt",
    "sitemap.xml",
]
ALL_ARTIFACTS = PURE_ARTIFACTS + SITE_ARTIFACTS


def logical_digest(path: Path) -> str:
    data = path.read_bytes()
    try:
        text = data.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
        data = text.encode("utf-8")
    except UnicodeDecodeError:
        pass
    return hashlib.sha256(data).hexdigest()


def snapshot(root: Path, paths: list[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for rel in paths:
        path = root / rel
        result[rel] = logical_digest(path) if path.exists() else "<missing>"
    return result


def changed(before: dict[str, str], after: dict[str, str]) -> list[str]:
    return sorted(path for path in before if before[path] != after[path])


def run_generators(root: Path) -> None:
    env = dict(os.environ)
    env["PYTHONIOENCODING"] = "utf-8"
    python_paths = [str(root / "scripts")]
    if env.get("PYTHONPATH"):
        python_paths.append(env["PYTHONPATH"])
    env["PYTHONPATH"] = os.pathsep.join(python_paths)
    runner = (
        "import runpy,sys;"
        "path=sys.argv[1];"
        "args=sys.argv[2:];"
        "sys.path.insert(0,'scripts');"
        "sys.argv=[path]+args;"
        "runpy.run_path(path,run_name='__main__')"
    )
    for args in GENERATORS:
        result = subprocess.run(
            [sys.executable, "-c", runner, *args],
            cwd=root,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            encoding="utf-8",
        )
        if result.returncode:
            raise RuntimeError(
                f"generator failed ({' '.join(args)}):\n{result.stdout}"
            )


def ignore_copy(directory: str, names: list[str]) -> set[str]:
    ignored = {"__pycache__", ".lake", "node_modules"}
    return {name for name in names if name in ignored}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true",
                        help="fail when committed pure artifacts are stale")
    args = parser.parse_args()

    with tempfile.TemporaryDirectory(prefix="ecdlp-fixpoint-") as tmp:
        work = Path(tmp) / "repo"
        shutil.copytree(ROOT, work, ignore=ignore_copy)
        initial = snapshot(work, ALL_ARTIFACTS)
        try:
            run_generators(work)
            first = snapshot(work, ALL_ARTIFACTS)
            run_generators(work)
            second = snapshot(work, ALL_ARTIFACTS)
        except RuntimeError as exc:
            print(f"generated-fixpoint check FAILED: {exc}", file=sys.stderr)
            return 1

    stale = changed(initial, first)
    non_idempotent = changed(first, second)
    if (args.check and stale) or non_idempotent:
        print("generated-fixpoint check FAILED:", file=sys.stderr)
        for path in stale if args.check else []:
            print(f"- stale generated artifact: {path}", file=sys.stderr)
        for path in non_idempotent:
            print(f"- changes again on second generator pass: {path}", file=sys.stderr)
        return 1

    print(
        "generated-fixpoint check OK: "
        f"{len(ALL_ARTIFACTS)} generated artifacts fresh and stable after one pass"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
