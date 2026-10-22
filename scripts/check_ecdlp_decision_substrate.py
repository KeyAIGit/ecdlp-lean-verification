#!/usr/bin/env python3
"""Validate the canonical secp256k1 ECDLP decision substrate.

This gate checks cross-registry identity, evidence paths, route/foundation
ownership, and the split between bounded exploration and promotion. It
validates project decisions; it does not validate mathematical claims
independently of their cited Lean or literature evidence.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECISIONS = ROOT / "repo" / "ECDLP_DECISION_SUBSTRATE.json"
ATTACKS = ROOT / "data" / "attack_registry.json"
FORMAL = ROOT / "repo" / "FORMAL_SUBSTRATE.json"
RESULTS = ROOT / "data" / "result_registry.json"
SOURCES = ROOT / "data" / "source_registry.json"
HYPOTHESES = ROOT / "experiments" / "HYPOTHESES.yaml"
TASKS = ROOT / "tasks" / "ECDLP_RESEARCH.md"
NEXT_TASKS = ROOT / "tasks" / "NEXT.md"
ENGINE_POLICY = ROOT / "repo" / "RESEARCH_ENGINE_V0.json"
ENGINE_STATE = ROOT / "data" / "research_engine_state.json"

STRUCTURAL_DECISION_ID = "RS-2026-07-24-001"
STRUCTURAL_SUPERSEDES = "RS-2026-07-22-001"
STRUCTURAL_ITERATION_ID = "GLV-SEMAEV-ITER-001"
STRUCTURAL_ROUTE_ID = "R-GLV-SEMAEV"
STRUCTURAL_HYPOTHESIS_ID = "HYP_GLV_SEMAEV_001"
STRUCTURAL_TASK_ID = "TASK-009"
STRUCTURAL_FOUNDATION_ID = "F-SEMAEV-ELIMINATION"
MAINTENANCE_CYCLE_ID = "RESEARCH-ENGINE-V0.2-SANITATION-001"
MAINTENANCE_TASK_ID = "TASK-010"
MAINTENANCE_ACCEPTANCE_COMMIT = "85f85d4ca0b9dba323bfdd05ce8750d6db4732ac"
CURRENT_PHASE = "post-task026-decision-review"
BOUNDED_AUTHORIZATION_KEY = "bounded_experiment_authorization"
BOUNDED_AUTHORIZATION_ID = (
    "AUTH-HYP-M16-FIXED-TARGET-YIELD-001-20260730-01"
)
BOUNDED_AUTHORIZATION_SOURCE_COMMIT = (
    "0b1b36851aa0f82c3a1bd587d385775923153d9c"
)
BOUNDED_AUTHORIZATION_HYPOTHESIS_ID = (
    "HYP-M16-FIXED-TARGET-YIELD-001"
)
BOUNDED_AUTHORIZATION_TASK_ID = "TASK-026"
BOUNDED_AUTHORIZATION_ROUTE_ID = "R-PETIT-COMPOSED-MAPS"
BOUNDED_AUTHORIZATION_CELL_ID = "CELL-M-PKC-SMOOTH-M16"
BOUNDED_AUTHORIZATION_BINDINGS = {
    "preregistration": (
        "experiments/engine/pkc_smooth_m16_fixed_target_yield/"
        "PREREGISTRATION.md",
        "e41164b1e8950aab60849e567949a230d592652d9b7ae2484eaed5dff7518cc5",
    ),
    "curve_table": (
        "experiments/engine/pkc_smooth_m16_fixed_target_yield/curve_table.json",
        "a59ed1a8b597bc5d512438d09fbb4c970fff74dd704f8f88be4f7224775f5e0d",
    ),
    "experiment_config": (
        "experiments/engine/pkc_smooth_m16_fixed_target_yield/"
        "experiment_config.json",
        "34265beeba540ab03a5c738519eef7acaf1504a96a2f6e73b993c8af773a7c64",
    ),
    "run_py": (
        "experiments/engine/pkc_smooth_m16_fixed_target_yield/run.py",
        "7fe8bc7d4aff18e42fbfbb9c03ae9e5cec4bacc4c39eb00fb718096dd163384a",
    ),
    "validate_py": (
        "experiments/engine/pkc_smooth_m16_fixed_target_yield/validate.py",
        "9f89bd4f1708f94235ff9f3c76de7db4dd7b05d42911e118b21d5f9592639d7c",
    ),
}
BOUNDED_AUTHORIZATION_BUDGET = {
    "max_primary_trials": 3_000_000,
    "max_cpu_hours": 4,
    "max_peak_rss_gib": 4,
    "max_wall_hours": 24,
}
BOUNDED_AUTHORIZATION_SCOPE = {
    "kind": "synthetic_toy_only",
    "curve_family": "E_7",
    "curve_ids": [
        "E7-P262153-N262567",
        "E7-P1048783-N1050337",
        "E7-P16777711-N5591281",
    ],
    "max_field_bits": 25,
    "real_world_targets_forbidden": True,
    "secp256k1_targets_forbidden": True,
}
BOUNDED_TERMINAL_EVENT_ID = "REO-2026-07-31-001"
BOUNDED_TERMINAL_STATUS = "CLASSIFY_AS_KNOWN_LOCAL_SIMPLIFICATION"
BOUNDED_TERMINAL_OUTCOME = "supported"
BOUNDED_TERMINAL_ARTIFACT = (
    "experiments/engine/pkc_smooth_m16_fixed_target_yield/artifact.json"
)
BOUNDED_TERMINAL_ARTIFACT_SHA256 = (
    "21a95ea4ea71c02d0199c331e549ca2e4ec2fbf7c1d8d70fe6651bea292d6413"
)
BOUNDED_TERMINAL_EVENT = (
    "experiments/engine/outcomes/REO-2026-07-31-001.json"
)
COMPLETED_PROPAGATION_TASK_ID = "TASK-025"
COMPLETED_STRATA_TASK_ID = "TASK-024"
COMPLETED_CHART_TASK_ID = "TASK-023"
COMPLETED_GUARDED_TASK_ID = "TASK-022"
COMPLETED_WITNESS_TASK_ID = "TASK-021"
COMPLETED_SPECIALIZATION_TASK_ID = "TASK-020"
COMPLETED_RESULTANT_TASK_ID = "TASK-019"
COMPLETED_DESK_TASK_ID = "TASK-018"
PREVIOUS_PROJECTIVE_TASK_ID = "TASK-017"
PREVIOUS_SEMANTIC_TASK_ID = "TASK-016"
PREVIOUS_DESK_TASK_ID = "TASK-015"
DESK_PRIORITY_CELL_ID = "CELL-M-PKC-SMOOTH-M16"
DESK_PRIORITY_STUB_ID = "RSI-D8BBA6340789"
DESK_PRIORITY_COST_ID = "CQ-SEMAEV-S17-SYSTEM-COST"
M16_PROJECTIVE_ARTIFACT_PATH = (
    "experiments/engine/pkc_smooth_m16_projective_bridge/artifact.json"
)
M16_PROJECTIVE_ARTIFACT_SHA256 = (
    "3164cb89adac7622b4d08d781061ea386dc64e754236e48c838a3dac23040715"
)
M16_RESULTANT_ARTIFACT_PATH = (
    "experiments/engine/"
    "pkc_smooth_m16_projective_resultant_kernel/artifact.json"
)
M16_RESULTANT_ARTIFACT_SHA256 = (
    "0b9d8b48953aae2defa28ade67992084cecca3a01b43490bc338a0fd5ce97c5a"
)
M16_SPECIALIZATION_ARTIFACT_PATH = (
    "experiments/engine/"
    "pkc_smooth_m16_frozen_cr_specialization/artifact.json"
)
M16_SPECIALIZATION_ARTIFACT_SHA256 = (
    "d025053b9f882c88086fd5f04bcbd9627c72987e263e9b55af6024794305acbe"
)
M16_SPECIALIZATION_ARTIFACT_ID = (
    "PKC-SMOOTH-M16-FROZEN-CR-SPECIALIZATION-001"
)
M16_SPECIALIZATION_CLAIM_ID = (
    "SC-PKC-M16-FROZEN-CR-SPECIALIZATION-RESULT"
)
M16_WITNESS_ARTIFACT_PATH = (
    "experiments/engine/"
    "pkc_smooth_m16_frozen_projective_witness/artifact.json"
)
M16_WITNESS_ARTIFACT_SHA256 = (
    "89c645545d89334473d51654a41ff7ec2364857d034c64ce08d505337fa1e2d4"
)
M16_WITNESS_ARTIFACT_ID = (
    "PKC-SMOOTH-M16-FROZEN-PROJECTIVE-WITNESS-001"
)
M16_WITNESS_CLAIM_ID = (
    "SC-PKC-M16-FROZEN-PROJECTIVE-WITNESS-RESULT"
)
M16_GUARDED_ARTIFACT_PATH = (
    "experiments/engine/"
    "pkc_smooth_m16_guarded_projective_system/artifact.json"
)
M16_GUARDED_ARTIFACT_SHA256 = (
    "3445da55b44a71d0f40ee60206c90f2ef1798c28abd125542ce3acbeeb8e1d46"
)
M16_GUARDED_ARTIFACT_ID = (
    "PKC-SMOOTH-M16-GUARDED-PROJECTIVE-SYSTEM-001"
)
M16_GUARDED_CLAIM_ID = (
    "SC-PKC-M16-GUARDED-PROJECTIVE-SYSTEM-RESULT"
)
M16_GUARDED_SOURCE_SHA256 = (
    "37feeef48e77437b44b6ae6dd4750782e19ecd824e3ea2e73b657e2fb8296fb9"
)
M16_CHART_ARTIFACT_PATH = (
    "experiments/engine/"
    "pkc_smooth_m16_exact_chart_cover/artifact.json"
)
M16_CHART_ARTIFACT_SHA256 = (
    "934809fabbb8c98c5ed9356a0a1f3367a23f8fbc1bc86239069942537fd678ed"
)
M16_CHART_ARTIFACT_ID = "PKC-SMOOTH-M16-EXACT-CHART-COVER-001"
M16_CHART_CLAIM_ID = "SC-PKC-M16-EXACT-CHART-COVER-RESULT"
M16_CHART_SOURCE_SHA256 = (
    "4f7b95453d8fafba3ec9cae0a9bbad5d8f782c6c0202f6e7cf37e17981b63019"
)
M16_STRATA_ARTIFACT_PATH = (
    "experiments/engine/"
    "pkc_smooth_m16_infinity_strata/artifact.json"
)
M16_STRATA_ARTIFACT_SHA256 = (
    "54b0f3c5f2f1880b1f805911df21b72e5427b18871f14907ac17a1d8b48bdd39"
)
M16_STRATA_ARTIFACT_ID = "PKC-SMOOTH-M16-INFINITY-STRATA-001"
M16_STRATA_CLAIM_ID = "SC-PKC-M16-INFINITY-STRATA-RESULT"
M16_STRATA_SOURCE_SHA256 = (
    "1314477f9821da87d2017837abca4fec957ae9998390a231e93532230129a22c"
)
M16_PROPAGATION_ARTIFACT_PATH = (
    "experiments/engine/"
    "pkc_smooth_m16_infinity_propagation/artifact.json"
)
M16_PROPAGATION_ARTIFACT_SHA256 = (
    "9330603ba1f0af9ee4902c263200709e2ec6f8c50d8d7eaab3b55bcba78e388f"
)
M16_PROPAGATION_ARTIFACT_ID = (
    "PKC-SMOOTH-M16-INFINITY-PROPAGATION-001"
)
M16_PROPAGATION_CLAIM_ID = (
    "SC-PKC-M16-INFINITY-PROPAGATION-RESULT"
)
M16_PROPAGATION_SOURCE_SHA256 = (
    "7f868aab5b946a55a213ce26a461477321d6387830eed218c414f1e62853b4b4"
)
M16_EXCEPTIONAL_ARTIFACT_PATH = (
    "experiments/engine/pkc_smooth_m16_exceptional_fibers/artifact.json"
)
M16_EXCEPTIONAL_ARTIFACT_SHA256 = (
    "578db732807a452e26de03dcd338d62c25a7d90490a62bbf427b1f96c3a869cf"
)
M16_SEMANTIC_ARTIFACT_PATH = (
    "experiments/engine/pkc_smooth_m16_semantic_bridge/artifact.json"
)
M16_SEMANTIC_ARTIFACT_SHA256 = (
    "963eea60097807ae0aa66a5d881b0c34bf0497ade53ed4d37d38861a73887c19"
)
M16_SYMBOLIC_ARTIFACT_PATH = (
    "experiments/engine/pkc_smooth_m16_symbolic_desk/artifact.json"
)
M16_SYMBOLIC_ARTIFACT_SHA256 = (
    "59596c3c59f5389c49742ba4a26d500445557ee6398d6aaad63c7995a93242f7"
)

ROUTE_STATUSES = {
    "guardrail",
    "baseline",
    "ruled_out_for_target",
    "constant_factor_only",
    "open_parked",
    "conditional_only",
    "separate_threat_model",
    "monitor",
}
FOUNDATION_DECISIONS = {
    "build_now",
    "build_if_selected",
    "retain_frontier",
    "monitor_only",
}
FOUNDATION_STATUSES = {"complete", "partial", "not_started"}
PRIORITIES = {"P0", "P1", "P2", "P3"}
REQUIRED_ROUTE_FIELDS = {
    "id",
    "title",
    "threat_models",
    "attack_registry_ids",
    "status",
    "priority",
    "applicability",
    "assumptions",
    "known_cost",
    "current_evidence",
    "success_gate",
    "stop_condition",
    "next_action",
    "authorized_experiment",
    "foundation_ids",
    "formal_node_ids",
    "lean_anchors",
    "evidence_files",
    "source_ids",
    "anti_overclaim",
}
REQUIRED_FOUNDATION_FIELDS = {
    "id",
    "title",
    "decision",
    "priority",
    "build_now",
    "implementation_status",
    "needed_by_route_ids",
    "formal_node_ids",
    "mathlib_status",
    "deliverable",
    "resume_condition",
}
REQUIRED_SELECTION_FIELDS = {
    "decision_id",
    "performed_on",
    "completed_on",
    "supersedes",
    "decision",
    "selection_scope",
    "iteration_id",
    "selected_route_ids",
    "promoted_route_ids",
    "hypothesis_id",
    "task_id",
    "foundation_ids",
    "outcome",
    "kernel_acceptance",
    "ledger_acceptance",
    "evaluated_route_ids",
    "gate_result",
    "rationale",
    "reconsideration_triggers",
    "operational_effects",
}
FOUNDATION_BUILD_DECISIONS_KEY = "foundation_build_decisions"
FOUNDATION_BUILD_DECISION_ID = "FD-2026-10-22-001"
AUTHORIZED_BUILD_RULING = "register_and_authorize_bounded_build"
UNCHANGED_PARKED_RULING = "unchanged_build_if_selected"
FOUNDATION_BUILD_DECISION_RULINGS = {
    "F-PARITY-BIT-SECURITY": AUTHORIZED_BUILD_RULING,
    "F-PRIME-ORDER-POINT-COUNT": AUTHORIZED_BUILD_RULING,
    STRUCTURAL_FOUNDATION_ID: UNCHANGED_PARKED_RULING,
}
RELEASE_EXCLUDED_NODE_IDS = ("p256-exact-cardinality",)
REQUIRED_FOUNDATION_BUILD_DECISION_FIELDS = {
    "decision_id",
    "decided_on",
    "decided_by",
    "source",
    "kind",
    "selected_route_ids",
    "promoted_route_ids",
    "authorizes_experiment",
    "promotes_route",
    "changes_release_required_nodes",
    "rationale",
    "rulings",
}
REQUIRED_RULING_FIELDS = {
    AUTHORIZED_BUILD_RULING: {
        "foundation_id",
        "ruling",
        "authorized_build",
        "exact_uncertainty",
        "success_condition",
        "stop_condition",
    },
    UNCHANGED_PARKED_RULING: {"foundation_id", "ruling", "scope"},
}
OPTIONAL_RULING_FIELDS = {
    AUTHORIZED_BUILD_RULING: {"status_basis"},
    UNCHANGED_PARKED_RULING: set(),
}
STALE_ACTIVE_PHRASES = (
    "Hypothesis remains ACTIVE",
    "hypothesis remains ACTIVE",
    "HYP_GLV_SEMAEV_001 ACTIVE",
)
STALE_STATUS_FILES = (
    "BARRIERS.md",
    "experiments/README.md",
    "experiments/p0_glv_semaev/README.md",
    "experiments/p0_glv_semaev/RESULTS.md",
    "experiments/p1_petit/README.md",
    "experiments/p1_petit/RESULTS.md",
    "experiments/p1_petit_m3/README.md",
    "experiments/p1_petit_m3/RESULTS.md",
    "experiments/p3_sm_system/README.md",
    "experiments/p3_sm_system/RESULTS.md",
    "experiments/p4_petit/README.md",
    "experiments/p4_petit/RESULTS.md",
    "notes/RESEARCH_MAP.md",
)


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def portable_text_sha256(payload: bytes) -> str:
    text = payload.decode("utf-8")
    canonical = text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")
    return sha256_bytes(canonical)


def git_file_bytes(commit: str, relative: str) -> bytes | None:
    """Read one readiness-bound file without trusting the working tree."""

    completed = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return completed.stdout if completed.returncode == 0 else None


def validate_bounded_authorization(
    data: dict, problems: list[str]
) -> dict:
    """Validate the sole decision-level exception to the closed run gates.

    This is intentionally a singleton with an exact field set.  It does not
    mutate the Research Engine, route, lifecycle, claim, or promotion gates.
    The experiment producer independently repeats these checks before it can
    execute.
    """

    authorization = data.get(BOUNDED_AUTHORIZATION_KEY)
    if not isinstance(authorization, dict):
        problems.append(
            f"{BOUNDED_AUTHORIZATION_KEY} must be the exact approved object"
        )
        return {}

    expected_fields = {
        "status",
        "hypothesis_id",
        "task_id",
        "route_id",
        "cell_id",
        "promotion_authorized",
        "authorization_id",
        "source_commit",
        "authorized_utc",
        "completed_utc",
        "terminal_event_id",
        "terminal_status",
        "normalized_outcome",
        "validated_artifact_sha256",
        "rerun_authorized",
        "sha256_bindings",
        "resource_budget",
        "scope",
    }
    if set(authorization) != expected_fields:
        problems.append(
            f"{BOUNDED_AUTHORIZATION_KEY} field set must be exactly "
            f"{sorted(expected_fields)}"
        )

    expected_identity = {
        "status": "consumed",
        "hypothesis_id": BOUNDED_AUTHORIZATION_HYPOTHESIS_ID,
        "task_id": BOUNDED_AUTHORIZATION_TASK_ID,
        "route_id": BOUNDED_AUTHORIZATION_ROUTE_ID,
        "cell_id": BOUNDED_AUTHORIZATION_CELL_ID,
        "promotion_authorized": False,
        "authorization_id": BOUNDED_AUTHORIZATION_ID,
        "source_commit": BOUNDED_AUTHORIZATION_SOURCE_COMMIT,
        "terminal_event_id": BOUNDED_TERMINAL_EVENT_ID,
        "terminal_status": BOUNDED_TERMINAL_STATUS,
        "normalized_outcome": BOUNDED_TERMINAL_OUTCOME,
        "validated_artifact_sha256": BOUNDED_TERMINAL_ARTIFACT_SHA256,
        "rerun_authorized": False,
        "resource_budget": BOUNDED_AUTHORIZATION_BUDGET,
        "scope": BOUNDED_AUTHORIZATION_SCOPE,
    }
    for field, expected in expected_identity.items():
        if authorization.get(field) != expected:
            problems.append(
                f"{BOUNDED_AUTHORIZATION_KEY}.{field} must be {expected!r}"
            )

    parsed_timestamps: dict[str, datetime] = {}
    for timestamp_field in ("authorized_utc", "completed_utc"):
        timestamp = authorization.get(timestamp_field)
        if not isinstance(timestamp, str) or not re.fullmatch(
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", timestamp
        ):
            problems.append(
                f"{BOUNDED_AUTHORIZATION_KEY}.{timestamp_field} must be "
                "canonical UTC"
            )
            continue
        try:
            parsed = datetime.strptime(
                timestamp, "%Y-%m-%dT%H:%M:%SZ"
            ).replace(tzinfo=timezone.utc)
        except ValueError:
            problems.append(
                f"{BOUNDED_AUTHORIZATION_KEY}.{timestamp_field} is invalid"
            )
        else:
            parsed_timestamps[timestamp_field] = parsed
            if parsed > datetime.now(timezone.utc):
                problems.append(
                    f"{BOUNDED_AUTHORIZATION_KEY}.{timestamp_field} is in the "
                    "future"
                )
    if (
        parsed_timestamps.get("authorized_utc")
        and parsed_timestamps.get("completed_utc")
        and parsed_timestamps["completed_utc"]
        < parsed_timestamps["authorized_utc"]
    ):
        problems.append("bounded authorization completion precedes approval")

    bindings = authorization.get("sha256_bindings")
    expected_hashes = {
        key: digest
        for key, (_, digest) in BOUNDED_AUTHORIZATION_BINDINGS.items()
    }
    if bindings != expected_hashes:
        problems.append(
            f"{BOUNDED_AUTHORIZATION_KEY}.sha256_bindings must match the "
            "five frozen readiness files"
        )

    for key, (relative, digest) in BOUNDED_AUTHORIZATION_BINDINGS.items():
        path = ROOT / relative
        if not path.is_file():
            problems.append(f"authorization-bound file is absent: {relative}")
            continue
        if portable_text_sha256(path.read_bytes()) != digest:
            problems.append(
                f"authorization-bound working-tree hash drifted: {key}"
            )
        source_payload = git_file_bytes(
            BOUNDED_AUTHORIZATION_SOURCE_COMMIT, relative
        )
        if source_payload is None:
            problems.append(
                f"authorization source commit lacks bound file: {relative}"
            )
        elif sha256_bytes(source_payload) != digest:
            problems.append(
                f"authorization source-commit hash drifted: {key}"
            )

    terminal_artifact = ROOT / BOUNDED_TERMINAL_ARTIFACT
    if not terminal_artifact.is_file():
        problems.append("bounded terminal artifact is absent")
    elif portable_text_sha256(terminal_artifact.read_bytes()) != (
        BOUNDED_TERMINAL_ARTIFACT_SHA256
    ):
        problems.append("bounded terminal artifact hash drifted")
    terminal_event_path = ROOT / BOUNDED_TERMINAL_EVENT
    if not terminal_event_path.is_file():
        problems.append("bounded terminal event is absent")
    else:
        terminal_event = load_json(terminal_event_path)
        expected_terminal = {
            "event_id": BOUNDED_TERMINAL_EVENT_ID,
            "candidate_id": BOUNDED_AUTHORIZATION_ID,
            "hypothesis_id": BOUNDED_AUTHORIZATION_HYPOTHESIS_ID,
            "route_id": BOUNDED_AUTHORIZATION_ROUTE_ID,
            "outcome": BOUNDED_TERMINAL_OUTCOME,
        }
        for field, expected in expected_terminal.items():
            if terminal_event.get(field) != expected:
                problems.append(
                    f"bounded terminal event {field} must be {expected!r}"
                )
        if terminal_event.get("stop_condition", {}).get("triggered") is not True:
            problems.append("bounded terminal event must trigger its stop condition")

    source_substrate_payload = git_file_bytes(
        BOUNDED_AUTHORIZATION_SOURCE_COMMIT,
        DECISIONS.relative_to(ROOT).as_posix(),
    )
    if source_substrate_payload is None:
        problems.append("authorization source commit is not inspectable")
    else:
        try:
            source_substrate = json.loads(source_substrate_payload)
        except json.JSONDecodeError:
            problems.append("authorization source substrate is malformed")
        else:
            source_authorization = source_substrate.get(
                BOUNDED_AUTHORIZATION_KEY
            )
            if (
                isinstance(source_authorization, dict)
                and source_authorization.get("status") == "approved"
            ):
                problems.append(
                    "authorization source commit already contained an approved "
                    "singleton"
                )
    return authorization


def validate_foundation_build_decisions(
    data: dict,
    foundations: list[dict],
    release_required_nodes: list[str],
    problems: list[str],
) -> None:
    """Validate dated owner decisions that bound formal-foundation builds.

    Such a decision may authorize exactly one named formal build for a
    foundation that stays ``retain_frontier`` with ``build_now`` false, or
    record that a ``build_if_selected`` foundation stays parked. It never
    selects or promotes a route, authorizes an experiment, or changes the
    formal release's required nodes.
    """

    records = data.get(FOUNDATION_BUILD_DECISIONS_KEY)
    if not isinstance(records, list) or not records:
        problems.append(
            f"{FOUNDATION_BUILD_DECISIONS_KEY} must be a non-empty list of "
            "dated decisions"
        )
        return
    by_id = {
        foundation["id"]: foundation
        for foundation in foundations
        if isinstance(foundation.get("id"), str)
    }
    authorized_by: dict[str, str] = {}
    seen_decisions: set[str] = set()
    for record in records:
        decision_id = record.get("decision_id", "?")
        missing = REQUIRED_FOUNDATION_BUILD_DECISION_FIELDS - set(record)
        extra = set(record) - REQUIRED_FOUNDATION_BUILD_DECISION_FIELDS
        if missing or extra:
            problems.append(
                f"{decision_id}: foundation build decision fields differ; "
                f"missing={sorted(missing)}, extra={sorted(extra)}"
            )
            continue
        if decision_id in seen_decisions:
            problems.append(f"{decision_id}: duplicate foundation build decision")
        seen_decisions.add(decision_id)
        match = re.fullmatch(r"FD-(\d{4}-\d{2}-\d{2})-\d{3}", decision_id)
        if not match or match.group(1) != record["decided_on"]:
            problems.append(
                f"{decision_id}: decision id must be FD-<decided_on>-NNN"
            )
        if record["decided_by"] != "owner":
            problems.append(f"{decision_id}: only the owner records this decision")
        if record["selected_route_ids"] != [] or record["promoted_route_ids"] != []:
            problems.append(f"{decision_id}: must select and promote no route")
        if record["authorizes_experiment"] is not False:
            problems.append(f"{decision_id}: must not authorize an experiment")
        if record["promotes_route"] is not False:
            problems.append(f"{decision_id}: must not promote a route")
        if record["changes_release_required_nodes"] is not False:
            problems.append(
                f"{decision_id}: must not change release.required_nodes"
            )
        rulings = record["rulings"]
        if not isinstance(rulings, list) or not rulings:
            problems.append(f"{decision_id}: rulings must be a non-empty list")
            continue
        ruled: dict[str, str] = {}
        for ruling in rulings:
            foundation_id = ruling.get("foundation_id", "?")
            kind = ruling.get("ruling")
            required = REQUIRED_RULING_FIELDS.get(kind)
            if required is None:
                problems.append(
                    f"{decision_id}/{foundation_id}: invalid ruling {kind!r}"
                )
                continue
            if not required <= set(ruling) <= (
                required | OPTIONAL_RULING_FIELDS[kind]
            ):
                problems.append(
                    f"{decision_id}/{foundation_id}: ruling fields differ from "
                    f"{sorted(required)}"
                )
            foundation = by_id.get(foundation_id)
            if foundation is None:
                problems.append(
                    f"{decision_id}: ruling for unknown foundation {foundation_id}"
                )
                continue
            if foundation_id in ruled:
                problems.append(
                    f"{decision_id}: duplicate ruling for {foundation_id}"
                )
            ruled[foundation_id] = kind
            if kind == AUTHORIZED_BUILD_RULING:
                if (
                    foundation["decision"] != "retain_frontier"
                    or foundation["build_now"] is not False
                ):
                    problems.append(
                        f"{foundation_id}: a bounded authorized build must keep "
                        "decision=retain_frontier and build_now=false"
                    )
                if foundation.get("registered_by") != decision_id:
                    problems.append(
                        f"{foundation_id}: registered_by must name {decision_id}"
                    )
                if foundation.get("needed_by_route_ids") != []:
                    problems.append(
                        f"{foundation_id}: a bounded build without a selected "
                        "route must have no dependent routes"
                    )
                authorized_by[foundation_id] = decision_id
            elif (
                foundation["decision"] != "build_if_selected"
                or foundation["build_now"] is not False
            ):
                problems.append(
                    f"{foundation_id}: a parked ruling requires "
                    "decision=build_if_selected and build_now=false"
                )
        if decision_id == FOUNDATION_BUILD_DECISION_ID and (
            ruled != FOUNDATION_BUILD_DECISION_RULINGS
        ):
            problems.append(
                f"{decision_id}: rulings must be exactly "
                f"{FOUNDATION_BUILD_DECISION_RULINGS}"
            )
    if FOUNDATION_BUILD_DECISION_ID not in seen_decisions:
        problems.append(
            f"{FOUNDATION_BUILD_DECISIONS_KEY} is missing "
            f"{FOUNDATION_BUILD_DECISION_ID}"
        )
    for foundation_id, foundation in by_id.items():
        registered_by = foundation.get("registered_by")
        if registered_by is not None and authorized_by.get(foundation_id) != registered_by:
            problems.append(
                f"{foundation_id}: registered_by {registered_by} has no "
                "authorizing ruling"
            )
    for node_id in RELEASE_EXCLUDED_NODE_IDS:
        if node_id in release_required_nodes:
            problems.append(
                f"{node_id} must stay out of release.required_nodes under "
                f"{FOUNDATION_BUILD_DECISION_ID}; changing that needs a new "
                "dated decision"
            )


def ids_are_unique(items: list[dict], label: str, problems: list[str]) -> set[str]:
    ids = [item.get("id") for item in items]
    if None in ids:
        problems.append(f"{label}: item missing id")
    if len(ids) != len(set(ids)):
        problems.append(f"{label}: duplicate ids")
    return {item for item in ids if item is not None}


def parse_hypotheses() -> dict[str, dict[str, str]]:
    text = HYPOTHESES.read_text(encoding="utf-8")
    pattern = re.compile(
        r"^  - id: (?P<id>[A-Z0-9_-]+)\s*$"
        r"(?P<body>.*?)(?=^  - id: [A-Z0-9_-]+\s*$|\Z)",
        flags=re.MULTILINE | re.DOTALL,
    )
    parsed: dict[str, dict[str, str]] = {}
    for match in pattern.finditer(text):
        fields: dict[str, str] = {}
        for name in (
            "direction",
            "status",
            "hypothesis_type",
            "lifecycle_state",
            "task_id",
            "route_id",
            "cell_id",
            "authorization_class",
            "authorization_id",
            "native_engine_candidate",
            "exact_test",
            "resume_after",
            "structural_lane",
            "structural_decision_id",
            "structural_iteration_id",
            "structural_route_id",
            "structural_task_id",
            "structural_foundation_id",
        ):
            field = re.search(
                rf"^    {name}:\s*(?:\"(?P<quoted>[^\"]*)\"|(?P<plain>.+))$",
                match.group("body"),
                flags=re.MULTILINE,
            )
            if field:
                fields[name] = (field.group("quoted") or field.group("plain")).strip()
        parsed[match.group("id")] = fields
    return parsed


def validate() -> list[str]:
    problems: list[str] = []
    data = load_json(DECISIONS)
    attack_data = load_json(ATTACKS)
    formal_data = load_json(FORMAL)
    result_data = load_json(RESULTS)
    source_data = load_json(SOURCES)
    engine_policy = load_json(ENGINE_POLICY)
    engine_state = load_json(ENGINE_STATE)

    routes = data.get("routes", [])
    foundations = data.get("foundations", [])
    route_ids = ids_are_unique(routes, "routes", problems)
    foundation_ids = ids_are_unique(foundations, "foundations", problems)
    attack_ids = {attack["id"] for attack in attack_data["attacks"]}
    formal_ids = {node["id"] for node in formal_data["critical_nodes"]}
    declaration_ids = set(result_data["declarations"])
    source_ids = {source["id"] for source in source_data["sources"]}
    threat_ids = ids_are_unique(data.get("threat_models", []), "threat_models", problems)
    hypotheses = parse_hypotheses()
    authorization = validate_bounded_authorization(data, problems)

    primary_models = [
        model["id"] for model in data["threat_models"] if model.get("primary")
    ]
    if primary_models != ["classical-single-target-plain"]:
        problems.append(
            "exactly classical-single-target-plain must be the primary threat model"
        )
    if data["phase_policy"].get("phase") != CURRENT_PHASE:
        problems.append(f"the current phase must be {CURRENT_PHASE}")
    if data["phase_policy"].get("experiments_authorized") is not False:
        problems.append("completed singleton must leave experiments_authorized=false")
    if (
        data["phase_policy"].get("experiments_authorized")
        is not (authorization.get("status") == "approved")
    ):
        problems.append(
        "decision-level experiments_authorized must equal the exact singleton "
        "approval state"
        )
    if data["phase_policy"].get("bounded_exploration_authorized") is not False:
        problems.append(
            "native bounded_exploration_authorized must remain false"
        )
    if data["phase_policy"].get("promotion_experiments_authorized") is not False:
        problems.append("promotion experiments must remain unauthorized")
    if data["phase_policy"].get("selected_attack_route") is not None:
        problems.append("completed structural selection must keep selected_attack_route=null")
    phase_allowed = "\n".join(data["phase_policy"].get("allowed_work", []))
    for binding in (
        BOUNDED_AUTHORIZATION_ID,
        BOUNDED_AUTHORIZATION_TASK_ID,
        "five source hashes",
        "three frozen E_7 toy subgroup rows",
        "thirty frozen cells",
        "3000000 completed primary trials",
        "independent validator",
        BOUNDED_TERMINAL_EVENT_ID,
        BOUNDED_TERMINAL_ARTIFACT_SHA256,
        "HYP-M16-SOLVER-SLOPE-001",
    ):
        if binding not in phase_allowed:
            problems.append(
                f"phase_policy.allowed_work is missing authorization binding {binding}"
            )
    for binding in (
        COMPLETED_SPECIALIZATION_TASK_ID,
        "actual frozen recursive C_r specialization",
        "predecessor output-degree bound",
        "unconditional one-step resultant/common-projective-root equivalence",
        COMPLETED_WITNESS_TASK_ID,
        "projective homogenization/evaluation",
        "recursive projective witness chain",
        "universal C16-to-C2 extraction",
        COMPLETED_GUARDED_TASK_ID,
        "exact literal finite MvPolynomial family",
        "injective base change",
        "56 scalar variables",
        "29 equation-family members",
        "total degree at most four",
        "chart/gauge redundancy",
        COMPLETED_CHART_TASK_ID,
        "exact affine/infinity chart-polynomial cover",
        "14 - I.card variables",
        "fifteen literal H equations",
        "degree ceilings 2/4/2",
        "production mask enumeration",
        COMPLETED_STRATA_TASK_ID,
        "necessary infinity-stratum pruning",
        "16384 masks",
        "987 separated masks",
        "377 interior masks",
        "sufficiency",
        COMPLETED_PROPAGATION_TASK_ID,
        "explicit infinity propagation",
        "377 to 129 to 69 to 36",
        "independent boundary-only refinement is 129 to 60",
        "BalancedPropagatedRegular",
        "mapped-target regularity",
        "symbolic nonzeroness, nonemptiness, genericity",
    ):
        if binding not in phase_allowed:
            problems.append(f"phase_policy.allowed_work is missing {binding}")
    phase_forbidden = "\n".join(data["phase_policy"].get("forbidden_work", []))
    for binding in (
        "Repeat TASK-026",
        "exact-target secp256k1 work",
        "promotion experiment",
    ):
        if binding not in phase_forbidden:
            problems.append(
                f"phase_policy.forbidden_work is missing singleton boundary {binding}"
            )
    for binding in (
        COMPLETED_WITNESS_TASK_ID,
        "frozen projective witness chain",
        "direct-S17 equivalence",
        "solving-cost result",
        "execution authorization",
        COMPLETED_GUARDED_TASK_ID,
        "guarded frozen representation",
        "expanded direct-S17 polynomial",
        "independent relation system",
        COMPLETED_CHART_TASK_ID,
        "production mask-selection algorithm",
        "enumeration of all 2^14 masks",
        COMPLETED_STRATA_TASK_ID,
        "necessary infinity-stratum filter",
        "sufficient or unique mask selection",
        COMPLETED_PROPAGATION_TASK_ID,
        "conditional single-affine-chart theorem",
        "symbolically nonzero, nonempty, dense, probable, or generic",
        "automatic mapped-target regularity from source-field computation",
    ):
        if binding not in phase_forbidden:
            problems.append(f"phase_policy.forbidden_work is missing {binding}")
    execution_gates = data.get("execution_gates", {})
    if execution_gates.get("exploration", {}).get("authorized") is not False:
        problems.append(
            "execution_gates.exploration must remain closed; the decision singleton "
            "is not native Engine authorization"
        )
    if execution_gates.get("promotion", {}).get("authorized") is not False:
        problems.append("execution_gates.promotion must remain closed")
    exploration_cannot_do = "\n".join(
        execution_gates.get("exploration", {}).get("cannot_do", [])
    )
    if (
        "TASK-026 singleton is consumed"
        not in exploration_cannot_do
    ):
        problems.append(
            "execution_gates.exploration.cannot_do must preserve the exact singleton "
            "boundary"
        )
    if execution_gates.get("exploration", {}).get("policy_source") != (
        "repo/RESEARCH_ENGINE_V0.json"
    ):
        problems.append("exploration gate must point at RESEARCH_ENGINE_V0.json")
    structural_gate = execution_gates.get("structural")
    if not isinstance(structural_gate, dict):
        problems.append("execution_gates.structural must be an object")
        structural_gate = {}
    expected_structural_gate = {
        "authorized": False,
        "status": "completed",
        "kind": "non_experiment",
        "authorizes_experiment": False,
        "promotes_route": False,
        "decision_id": STRUCTURAL_DECISION_ID,
        "iteration_id": STRUCTURAL_ITERATION_ID,
        "selected_route_ids": [STRUCTURAL_ROUTE_ID],
        "hypothesis_id": STRUCTURAL_HYPOTHESIS_ID,
        "task_id": STRUCTURAL_TASK_ID,
        "foundation_ids": [STRUCTURAL_FOUNDATION_ID],
    }
    for field, expected in expected_structural_gate.items():
        if structural_gate.get(field) != expected:
            problems.append(
                f"execution_gates.structural.{field} must be {expected!r}"
            )
    if engine_policy.get("gates", {}).get("exploration", {}).get(
        "authorized"
    ) is not True:
        problems.append("Research Engine must retain its bounded-exploration capability")
    if engine_policy.get("gates", {}).get("promotion", {}).get(
        "authorized"
    ) is not False:
        problems.append("Research Engine policy must keep promotion closed")
    engine_gate_status = engine_state.get("gate_status", {})
    if engine_gate_status.get("promotion_authorized") is not False:
        problems.append("generated engine state must keep promotion closed")
    selected_count = engine_state.get("counts", {}).get("selected_explorations")
    authorized_count = engine_state.get("counts", {}).get(
        "authorized_exploration_candidates"
    )
    ready_count = engine_state.get("counts", {}).get("ready_explorations")
    max_selected = engine_policy.get("gates", {}).get("exploration", {}).get(
        "max_selected_per_cycle"
    )
    if (
        not isinstance(selected_count, int)
        or not isinstance(max_selected, int)
        or selected_count > max_selected
    ):
        problems.append("generated selected sequence exceeds the exploration gate")
    if selected_count != 0 or authorized_count != 0 or ready_count != 0:
        problems.append(
            "the completed structural decision requires zero selected, authorized, and ready "
            "Research Engine explorations"
        )

    selection = data.get("route_selection")
    if not isinstance(selection, dict):
        problems.append("route_selection must be an object")
        selection = {}
    missing_selection = REQUIRED_SELECTION_FIELDS - set(selection)
    extra_selection = set(selection) - REQUIRED_SELECTION_FIELDS
    if missing_selection:
        problems.append(
            f"route_selection: missing fields {sorted(missing_selection)}"
        )
    if extra_selection:
        problems.append(
            f"route_selection: unknown fields {sorted(extra_selection)}"
        )
    expected_selection = {
        "decision_id": STRUCTURAL_DECISION_ID,
        "performed_on": "2026-07-24",
        "completed_on": "2026-07-24",
        "supersedes": STRUCTURAL_SUPERSEDES,
        "decision": "select_one_bounded_structural",
        "selection_scope": "bounded_structural_non_experiment",
        "iteration_id": STRUCTURAL_ITERATION_ID,
        "selected_route_ids": [STRUCTURAL_ROUTE_ID],
        "promoted_route_ids": [],
        "hypothesis_id": STRUCTURAL_HYPOTHESIS_ID,
        "task_id": STRUCTURAL_TASK_ID,
        "foundation_ids": [STRUCTURAL_FOUNDATION_ID],
        "outcome": "diagonal_only_bounded_negative",
    }
    for field, expected in expected_selection.items():
        if selection.get(field) != expected:
            problems.append(f"route_selection.{field} must be {expected!r}")
    selected_structural = selection.get("selected_route_ids")
    if not isinstance(selected_structural, list) or len(selected_structural) != 1:
        problems.append("exactly one bounded structural route must be selected")
    promoted = selection.get("promoted_route_ids")
    if not isinstance(promoted, list) or promoted:
        problems.append("route_selection.promoted_route_ids must be an empty array")
    evaluated = selection.get("evaluated_route_ids")
    if not isinstance(evaluated, list) or len(evaluated) != len(set(evaluated)):
        problems.append("route_selection.evaluated_route_ids must be a unique array")
    elif set(evaluated) != route_ids:
        problems.append(
            "route_selection.evaluated_route_ids must contain every registered route"
        )
    if not re.fullmatch(
        r"RS-\d{4}-\d{2}-\d{2}-\d{3}", str(selection.get("decision_id", ""))
    ):
        problems.append("route_selection.decision_id has an invalid format")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(selection.get("performed_on", ""))):
        problems.append("route_selection.performed_on must be YYYY-MM-DD")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(selection.get("completed_on", ""))):
        problems.append("route_selection.completed_on must be YYYY-MM-DD")
    kernel_acceptance = selection.get("kernel_acceptance")
    if not isinstance(kernel_acceptance, dict):
        problems.append("route_selection.kernel_acceptance must be an object")
    else:
        expected_kernel_acceptance = {
            "commit": "1bba09ff1d8682187365996d9b190044aea333f9",
            "workflow_run": 30142661986,
            "lean": "v4.31.0",
            "mathlib": "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
        }
        for field, expected in expected_kernel_acceptance.items():
            if kernel_acceptance.get(field) != expected:
                problems.append(
                    f"route_selection.kernel_acceptance.{field} must be {expected!r}"
                )
    ledger_acceptance = selection.get("ledger_acceptance")
    expected_ledger_acceptance = {
        "status": "accepted",
        "commit": "9b77dd109306fa677fed5feab7bef830049e0c55",
        "workflow_run": 30143606761,
        "job": 89641332798,
        "lean": "v4.31.0",
        "mathlib": "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
    }
    if ledger_acceptance != expected_ledger_acceptance:
        problems.append(
            "route_selection.ledger_acceptance must match the accepted closure "
            "commit and expanded ledger axiom-audit run"
        )
    for field in (
        "gate_result",
        "rationale",
        "reconsideration_triggers",
        "operational_effects",
    ):
        value = selection.get(field)
        if field == "gate_result":
            valid = isinstance(value, str) and bool(value)
        else:
            valid = (
                isinstance(value, list)
                and bool(value)
                and all(isinstance(item, str) and item for item in value)
            )
        if not valid:
            problems.append(f"route_selection.{field} must be nonempty")
    next_gate = data.get("next_phase_gate", {})
    if (
        next_gate.get("current_mode")
        != "post_task026_proposal_only_promotion_closed"
    ):
        problems.append(
            "next_phase_gate.current_mode must be "
            "post_task026_proposal_only_promotion_closed"
        )
    reopen = next_gate.get("reopen_requirements")
    if not isinstance(reopen, list) or not reopen:
        problems.append("next_phase_gate.reopen_requirements must be nonempty")
    reopen_text = "\n".join(reopen) if isinstance(reopen, list) else ""
    for binding in (
        BOUNDED_AUTHORIZATION_TASK_ID,
        "independently validate",
        "HYP-M16-SOLVER-SLOPE-001",
        "no TASK-026 terminal promotes a route",
        "authorizes a solver",
        "secp256k1 extrapolation",
    ):
        if binding not in reopen_text:
            problems.append(
                f"next_phase_gate.reopen_requirements is missing {binding}"
            )
    next_gate_decision = next_gate.get("decision", "")
    for binding in (
        COMPLETED_PROPAGATION_TASK_ID,
        "HYP-SELECT-002",
        BOUNDED_AUTHORIZATION_HYPOTHESIS_ID,
        BOUNDED_AUTHORIZATION_ID,
        BOUNDED_AUTHORIZATION_TASK_ID,
        "three frozen synthetic E_7 toy subgroups",
        "thirty frozen cells",
        "3000000 primary trials",
        BOUNDED_AUTHORIZATION_SOURCE_COMMIT,
        "open_parked",
        "selected_attack_route remains null",
        "route-level and native bounded-exploration authorization remain false",
        "promotion authorization remains false",
        "authorizes no solver",
        "direct secp256k1 target work",
        "ECDLP complexity improvement",
    ):
        if binding not in next_gate_decision:
            problems.append(f"next_phase_gate.decision is missing {binding}")

    target_anchors = data["target_problem"].get("formal_anchors", [])
    for anchor in target_anchors:
        if anchor not in declaration_ids:
            problems.append(f"target problem: unknown Lean anchor {anchor}")
    for source_id in data["target_problem"].get("standards_sources", []):
        if source_id not in source_ids:
            problems.append(f"target problem: unknown source {source_id}")

    reverse_foundations = {foundation_id: set() for foundation_id in foundation_ids}
    completed_structural_routes: list[str] = []
    for route in routes:
        route_id = route.get("id", "?")
        missing = REQUIRED_ROUTE_FIELDS - set(route)
        if missing:
            problems.append(f"{route_id}: missing fields {sorted(missing)}")
            continue
        if route["status"] not in ROUTE_STATUSES:
            problems.append(f"{route_id}: invalid status {route['status']}")
        if route["priority"] not in PRIORITIES:
            problems.append(f"{route_id}: invalid priority {route['priority']}")
        if not route["assumptions"]:
            problems.append(f"{route_id}: assumptions must not be empty")
        if route["authorized_experiment"] is not False:
            problems.append(
                f"{route_id}: route-level promotion experiments are not authorized"
            )
        structural_lane = route.get("structural_lane")
        if (
            isinstance(structural_lane, dict)
            and structural_lane.get("status") == "completed"
        ):
            completed_structural_routes.append(route_id)
            expected_route_lane = {
                "decision_id": STRUCTURAL_DECISION_ID,
                "iteration_id": STRUCTURAL_ITERATION_ID,
                "route_id": STRUCTURAL_ROUTE_ID,
                "hypothesis_id": STRUCTURAL_HYPOTHESIS_ID,
                "task_id": STRUCTURAL_TASK_ID,
                "foundation_ids": [STRUCTURAL_FOUNDATION_ID],
                "promotes_route": False,
                "authorizes_experiment": False,
            }
            for field, expected in expected_route_lane.items():
                if structural_lane.get(field) != expected:
                    problems.append(
                        f"{route_id}: structural_lane.{field} must be {expected!r}"
                    )
        if not set(route["threat_models"]) <= threat_ids:
            unknown = set(route["threat_models"]) - threat_ids
            problems.append(f"{route_id}: unknown threat models {sorted(unknown)}")
        if not set(route["attack_registry_ids"]) <= attack_ids:
            unknown = set(route["attack_registry_ids"]) - attack_ids
            problems.append(f"{route_id}: unknown attack registry ids {sorted(unknown)}")
        if not set(route["foundation_ids"]) <= foundation_ids:
            unknown = set(route["foundation_ids"]) - foundation_ids
            problems.append(f"{route_id}: unknown foundations {sorted(unknown)}")
        if not set(route["formal_node_ids"]) <= formal_ids:
            unknown = set(route["formal_node_ids"]) - formal_ids
            problems.append(f"{route_id}: unknown formal nodes {sorted(unknown)}")
        if not set(route["lean_anchors"]) <= declaration_ids:
            unknown = set(route["lean_anchors"]) - declaration_ids
            problems.append(f"{route_id}: unknown Lean anchors {sorted(unknown)}")
        if not set(route["source_ids"]) <= source_ids:
            unknown = set(route["source_ids"]) - source_ids
            problems.append(f"{route_id}: unknown sources {sorted(unknown)}")
        if not (
            route["attack_registry_ids"]
            or route["lean_anchors"]
            or route["source_ids"]
            or route["evidence_files"]
        ):
            problems.append(
                f"{route_id}: no repository, registry, Lean, or literature evidence"
            )
        for evidence_file in route["evidence_files"]:
            path = ROOT / evidence_file
            if not path.is_file():
                problems.append(f"{route_id}: missing evidence file {evidence_file}")
        for foundation_id in route["foundation_ids"]:
            if foundation_id in reverse_foundations:
                reverse_foundations[foundation_id].add(route_id)
        for hypothesis_id in route.get("hypothesis_ids", []):
            if hypothesis_id not in hypotheses:
                problems.append(f"{route_id}: unknown hypothesis {hypothesis_id}")
                continue
            status = hypotheses[hypothesis_id].get("status")
            expected_status = (
                "closed"
                if (
                    hypothesis_id == BOUNDED_AUTHORIZATION_HYPOTHESIS_ID
                    and route_id == BOUNDED_AUTHORIZATION_ROUTE_ID
                )
                else "parked"
            )
            if status != expected_status:
                problems.append(
                    f"{route_id}: {hypothesis_id} must be {expected_status}, "
                    f"found {status!r}"
                )

    if completed_structural_routes != [STRUCTURAL_ROUTE_ID]:
        problems.append(
            "exactly R-GLV-SEMAEV must own the completed structural route lane; "
            f"found {completed_structural_routes}"
        )
    petit_route = next(
        (route for route in routes if route.get("id") == "R-PETIT-COMPOSED-MAPS"),
        {},
    )
    petit_next_action = petit_route.get("next_action", "")
    for binding in (
        COMPLETED_PROPAGATION_TASK_ID,
        BOUNDED_AUTHORIZATION_TASK_ID,
        BOUNDED_TERMINAL_EVENT_ID,
        BOUNDED_TERMINAL_STATUS,
        "HYP-M16-SOLVER-SLOPE-001",
    ):
        if binding not in petit_next_action:
            problems.append(
                f"R-PETIT-COMPOSED-MAPS.next_action is missing {binding}"
            )
    if M16_PROJECTIVE_ARTIFACT_PATH not in petit_route.get(
        "evidence_files", []
    ):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must retain the TASK-018 projective "
            "certificate as evidence"
        )
    if M16_RESULTANT_ARTIFACT_PATH not in petit_route.get(
        "evidence_files", []
    ):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must retain the TASK-019 "
            "projective-resultant kernel certificate as evidence"
        )
    if M16_SPECIALIZATION_ARTIFACT_PATH not in petit_route.get(
        "evidence_files", []
    ):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must retain the TASK-020 frozen-C_r "
            "specialization certificate as evidence"
        )
    if M16_WITNESS_ARTIFACT_PATH not in petit_route.get(
        "evidence_files", []
    ):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must retain the TASK-021 frozen "
            "projective witness certificate as evidence"
        )
    if M16_GUARDED_ARTIFACT_PATH not in petit_route.get(
        "evidence_files", []
    ):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must retain the TASK-022 guarded "
            "projective-system certificate as evidence"
        )
    if M16_CHART_ARTIFACT_PATH not in petit_route.get(
        "evidence_files", []
    ):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must retain the TASK-023 exact "
            "chart-cover certificate as evidence"
        )
    if M16_STRATA_ARTIFACT_PATH not in petit_route.get(
        "evidence_files", []
    ):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must retain the TASK-024 infinity-strata "
            "certificate as evidence"
        )
    if M16_PROPAGATION_ARTIFACT_PATH not in petit_route.get(
        "evidence_files", []
    ):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must retain the TASK-025 infinity-propagation "
            "certificate as evidence"
        )
    petit_current_evidence = petit_route.get("current_evidence", "")
    for binding in (
        "TASK-019 kernel-checks",
        "fixed-degree projective resultant common-root theorem",
        "PKC-SMOOTH-M16-PROJECTIVE-RESULTANT-KERNEL-001",
        M16_RESULTANT_ARTIFACT_SHA256,
        "SC-PKC-M16-PROJECTIVE-RESULTANT-KERNEL-RESULT",
        "coefficient unit 1",
        "zero forms",
        "[1:0]",
        "TASK-020 kernel-checks",
        "actual recursive frozen C_r family",
        "formal degrees (2^(r-2),2)",
        "uniform predecessor output-degree bound",
        "unconditional one-step resultant/common-projective-root equivalence",
        M16_SPECIALIZATION_ARTIFACT_ID,
        M16_SPECIALIZATION_ARTIFACT_SHA256,
        M16_SPECIALIZATION_CLAIM_ID,
        "TASK-021 kernel-checks",
        "universal all-stage frozen witness-chain equivalence",
        "fourteen valid intermediate projective slots",
        M16_WITNESS_ARTIFACT_ID,
        M16_WITNESS_ARTIFACT_SHA256,
        M16_WITNESS_CLAIM_ID,
        "TASK-022 now kernel-checks",
        "exact literal finite MvPolynomial family",
        "injective source-to-target field map",
        "56 variables",
        "29 equation-family members",
        "total degree at most four",
        "[0:0] is excluded",
        "[1:0] is retained",
        M16_GUARDED_ARTIFACT_ID,
        M16_GUARDED_ARTIFACT_SHA256,
        M16_GUARDED_CLAIM_ID,
        M16_GUARDED_SOURCE_SHA256,
        "TASK-023 now kernel-checks",
        "exact affine/infinity chart-polynomial cover",
        "14 - I.card",
        "no guard equations",
        "fifteen literal H equations",
        "degree ceilings 2/4/2",
        "2^14 logical masks are not enumerated or materialized",
        M16_CHART_ARTIFACT_ID,
        M16_CHART_ARTIFACT_SHA256,
        M16_CHART_CLAIM_ID,
        M16_CHART_SOURCE_SHA256,
        "TASK-024 kernel-checks",
        "16384 masks to 987 separated masks",
        "conditionally to 377 interior masks",
        M16_STRATA_ARTIFACT_ID,
        M16_STRATA_ARTIFACT_SHA256,
        M16_STRATA_CLAIM_ID,
        "TASK-025 kernel-checks",
        "377 to 129 to 69 to 36",
        "independent boundary-only refinement is 129 to 60",
        "over any field",
        "BalancedPropagatedRegular",
        "single empty-mask affine chart",
        M16_PROPAGATION_ARTIFACT_ID,
        M16_PROPAGATION_ARTIFACT_SHA256,
        M16_PROPAGATION_CLAIM_ID,
        M16_PROPAGATION_SOURCE_SHA256,
        "source-stage bridge requires injective base change",
        "mapped-target balanced regularity",
        "source-field computation does not automatically establish",
        "Symbolic nonzeroness, nonemptiness, density, probability, genericity",
        "open_non_executable",
        "symbolic nonzeroness and nonemptiness of a usable regular locus",
        "orchestration of its exceptional complement",
        "zero_retention_success",
        "CQ-SEMAEV-S17-SYSTEM-COST remains partial",
        "solving cost remain unpriced",
    ):
        if binding not in petit_current_evidence:
            problems.append(
                "R-PETIT-COMPOSED-MAPS.current_evidence is missing "
                f"{binding}"
            )
    for binding in (
        "3000000 trials",
        "911 exact relations",
        "907 were affine regular",
        "no H_NEW qualifying size",
        "source-faithful PKC relation generation",
        "rank",
        "solver scaling",
        "recovery",
        "total cost",
        "256-bit persistence",
        "TASK-026 rerun",
        "route promotion",
        "exact-target",
    ):
        if binding not in petit_next_action:
            problems.append(
                f"R-PETIT-COMPOSED-MAPS.next_action is missing {binding}"
            )
    if "auxiliary-curve cell parked" not in petit_next_action:
        problems.append(
            "R-PETIT-COMPOSED-MAPS must keep the auxiliary-curve cell parked"
        )
    if petit_route.get("status") != "open_parked":
        problems.append("R-PETIT-COMPOSED-MAPS must remain open_parked")
    if petit_route.get("authorized_experiment") is not False:
        problems.append(
            "R-PETIT-COMPOSED-MAPS authorization must remain false"
        )
    if "No reliable project estimate" not in petit_route.get("known_cost", ""):
        problems.append(
            "R-PETIT-COMPOSED-MAPS must not acquire a TASK-020 cost claim"
        )

    completed_structural_foundations: list[str] = []
    for foundation in foundations:
        foundation_id = foundation.get("id", "?")
        missing = REQUIRED_FOUNDATION_FIELDS - set(foundation)
        if missing:
            problems.append(f"{foundation_id}: missing fields {sorted(missing)}")
            continue
        if foundation["decision"] not in FOUNDATION_DECISIONS:
            problems.append(
                f"{foundation_id}: invalid decision {foundation['decision']}"
            )
        if foundation["priority"] not in PRIORITIES:
            problems.append(
                f"{foundation_id}: invalid priority {foundation['priority']}"
            )
        if foundation["build_now"] != (foundation["decision"] == "build_now"):
            problems.append(
                f"{foundation_id}: build_now must agree with decision=build_now"
            )
        if foundation["build_now"] and foundation["priority"] != "P0":
            problems.append(f"{foundation_id}: build-now work must be P0")
        if foundation["implementation_status"] not in FOUNDATION_STATUSES:
            problems.append(
                f"{foundation_id}: invalid implementation status "
                f"{foundation['implementation_status']}"
            )
        if foundation["build_now"] and foundation["implementation_status"] != "complete":
            problems.append(
                f"{foundation_id}: build-now foundation must be complete before "
                "route selection"
            )
        if not set(foundation["needed_by_route_ids"]) <= route_ids:
            unknown = set(foundation["needed_by_route_ids"]) - route_ids
            problems.append(
                f"{foundation_id}: unknown dependent routes {sorted(unknown)}"
            )
        declared = set(foundation["needed_by_route_ids"])
        observed = reverse_foundations.get(foundation_id, set())
        if declared != observed:
            problems.append(
                f"{foundation_id}: needed_by_route_ids differs from route references; "
                f"declared={sorted(declared)}, observed={sorted(observed)}"
            )
        if not set(foundation["formal_node_ids"]) <= formal_ids:
            unknown = set(foundation["formal_node_ids"]) - formal_ids
            problems.append(
                f"{foundation_id}: unknown formal nodes {sorted(unknown)}"
            )
        structural_lane = foundation.get("structural_lane")
        if (
            isinstance(structural_lane, dict)
            and structural_lane.get("status") == "completed_bounded_slice"
        ):
            completed_structural_foundations.append(foundation_id)
            expected_foundation_lane = {
                "decision_id": STRUCTURAL_DECISION_ID,
                "iteration_id": STRUCTURAL_ITERATION_ID,
                "route_id": STRUCTURAL_ROUTE_ID,
                "hypothesis_id": STRUCTURAL_HYPOTHESIS_ID,
                "task_id": STRUCTURAL_TASK_ID,
                "promotes_foundation": False,
                "build_now": False,
            }
            for field, expected in expected_foundation_lane.items():
                if structural_lane.get(field) != expected:
                    problems.append(
                        f"{foundation_id}: structural_lane.{field} must be "
                        f"{expected!r}"
                    )

    if completed_structural_foundations != [STRUCTURAL_FOUNDATION_ID]:
        problems.append(
            "exactly F-SEMAEV-ELIMINATION must own the completed bounded foundation "
            f"slice; found {completed_structural_foundations}"
        )
    validate_foundation_build_decisions(
        data,
        foundations,
        formal_data["release"]["required_nodes"],
        problems,
    )

    experiment_hypotheses = {
        hypothesis_id: fields
        for hypothesis_id, fields in hypotheses.items()
        if fields.get("direction") == "experiment"
    }
    active_experiments = [
        hypothesis_id
        for hypothesis_id, fields in experiment_hypotheses.items()
        if fields.get("status") == "active"
    ]
    if active_experiments:
        problems.append(
            "the consumed external singleton leaves no active experiment; found: "
            + ", ".join(sorted(active_experiments))
        )
    completed_structural_hypotheses = [
        hypothesis_id
        for hypothesis_id, fields in experiment_hypotheses.items()
        if fields.get("structural_lane") == "completed"
    ]
    if completed_structural_hypotheses != [STRUCTURAL_HYPOTHESIS_ID]:
        problems.append(
            "exactly HYP_GLV_SEMAEV_001 must own the completed structural hypothesis "
            f"lane; found {completed_structural_hypotheses}"
        )
    expected_hypothesis_binding = {
        "status": "parked",
        "structural_lane": "completed",
        "structural_decision_id": STRUCTURAL_DECISION_ID,
        "structural_iteration_id": STRUCTURAL_ITERATION_ID,
        "structural_route_id": STRUCTURAL_ROUTE_ID,
        "structural_task_id": STRUCTURAL_TASK_ID,
        "structural_foundation_id": STRUCTURAL_FOUNDATION_ID,
    }
    structural_hypothesis = hypotheses.get(STRUCTURAL_HYPOTHESIS_ID, {})
    for field, expected in expected_hypothesis_binding.items():
        if structural_hypothesis.get(field) != expected:
            problems.append(
                f"{STRUCTURAL_HYPOTHESIS_ID}.{field} must be {expected!r}"
            )
    for required_parked in ("HYP_GLV_SEMAEV_001", "HYP_WARD_EDS_001"):
        status = hypotheses.get(required_parked, {}).get("status")
        if status != "parked":
            problems.append(f"{required_parked} must remain parked, found {status!r}")
    if hypotheses.get("H7_ECDLP_DECISION_SUBSTRATE", {}).get("status") != "closed":
        problems.append("H7_ECDLP_DECISION_SUBSTRATE must be closed after selection")

    required_foundation_files = (
        "scripts/build_ecdlp_decision_view.py",
        "scripts/check_ecdlp_decision_substrate.py",
        "experiments/framework/candidate_run.schema.json",
        "experiments/framework/candidate_contract.py",
        "experiments/framework/ec_oracle.py",
        "experiments/framework/test_framework.py",
        "experiments/framework/fixtures/valid.json",
        "experiments/framework/fixtures/invalid_hidden_precomputation.json",
        "experiments/framework/fixtures/invalid_self_validation.json",
        "experiments/framework/fixtures/invalid_wrong_output.json",
        "experiments/framework/fixtures/invalid_missing_provenance.json",
        "repo/RESEARCH_ENGINE_V0.json",
        "data/research_engine_state.json",
        "experiments/engine/outcome.schema.json",
        "experiments/engine/run.schema.json",
        "experiments/engine/instance_result.schema.json",
        "experiments/engine/instance_validation.schema.json",
        "experiments/engine/validator_request.schema.json",
        "experiments/engine/validator_output.schema.json",
        "experiments/engine/runs/README.md",
        "scripts/build_research_engine_state.py",
        "scripts/check_research_engine.py",
        "scripts/test_research_engine.py",
    )
    for relative in required_foundation_files:
        if not (ROOT / relative).is_file():
            problems.append(f"completed build-now foundation is missing {relative}")

    tasks_text = TASKS.read_text(encoding="utf-8")
    for required_task in (
        "TASK-008",
        "TASK-009",
        "TASK-010",
        "TASK-013",
        PREVIOUS_DESK_TASK_ID,
        PREVIOUS_SEMANTIC_TASK_ID,
        PREVIOUS_PROJECTIVE_TASK_ID,
        COMPLETED_DESK_TASK_ID,
        COMPLETED_RESULTANT_TASK_ID,
        COMPLETED_SPECIALIZATION_TASK_ID,
        COMPLETED_WITNESS_TASK_ID,
        COMPLETED_GUARDED_TASK_ID,
        COMPLETED_CHART_TASK_ID,
        COMPLETED_STRATA_TASK_ID,
        COMPLETED_PROPAGATION_TASK_ID,
        BOUNDED_AUTHORIZATION_TASK_ID,
    ):
        if required_task not in tasks_text:
            problems.append(f"tasks/ECDLP_RESEARCH.md must contain {required_task}")
    for completed_task in ("TASK-005", "TASK-006", "TASK-007"):
        if re.search(rf"^### {completed_task}\b", tasks_text, flags=re.MULTILINE):
            problems.append(
                f"tasks/ECDLP_RESEARCH.md must not retain completed {completed_task}"
            )
    task_sections = {
        match.group("id"): match.group("body")
        for match in re.finditer(
            r"^### (?P<id>TASK-\d{3})\b(?P<body>.*?)(?=^### TASK-\d{3}\b|\Z)",
            tasks_text,
            flags=re.MULTILINE | re.DOTALL,
        )
    }
    task_009 = task_sections.get(STRUCTURAL_TASK_ID, "")
    expected_task_lines = (
        "Status: completed_bounded_structural",
        "Structural lane: completed",
        f"Decision: {STRUCTURAL_DECISION_ID}",
        f"Iteration: {STRUCTURAL_ITERATION_ID}",
        f"Route: {STRUCTURAL_ROUTE_ID}",
        f"Hypothesis: {STRUCTURAL_HYPOTHESIS_ID}",
        f"Foundation: {STRUCTURAL_FOUNDATION_ID}",
    )
    for line in expected_task_lines:
        if not re.search(rf"^{re.escape(line)}$", task_009, flags=re.MULTILINE):
            problems.append(f"{STRUCTURAL_TASK_ID} must contain {line!r}")
    structural_task_ids = [
        task_id
        for task_id, body in task_sections.items()
        if re.search(r"^Structural lane: completed$", body, flags=re.MULTILINE)
    ]
    if structural_task_ids != [STRUCTURAL_TASK_ID]:
        problems.append(
            "exactly TASK-009 must be the completed bounded structural task; "
            f"found {structural_task_ids}"
        )
    task_010 = task_sections.get(MAINTENANCE_TASK_ID, "")
    if not re.search(
        r"^Status: completed_accepted$", task_010, flags=re.MULTILINE
    ):
        problems.append("TASK-010 must be completed_accepted")
    task_026 = task_sections.get(BOUNDED_AUTHORIZATION_TASK_ID, "")
    for binding in (
        "Status: completed_independently_validated_terminal",
        f"Hypothesis: `{BOUNDED_AUTHORIZATION_HYPOTHESIS_ID}`",
        f"`{BOUNDED_AUTHORIZATION_ID}`",
        f"`{BOUNDED_AUTHORIZATION_SOURCE_COMMIT}`",
        "Model: classical representation-aware, synthetic toy data only",
        f"Route state: `{BOUNDED_AUTHORIZATION_ROUTE_ID}` remains `open_parked`",
        "Promotion: false",
        f"Outcome event: `{BOUNDED_TERMINAL_EVENT_ID}`",
        f"Terminal: `{BOUNDED_TERMINAL_STATUS}`",
        "Authorization state: consumed; rerun authorized: false",
        BOUNDED_TERMINAL_ARTIFACT_SHA256,
        "three frozen `E_7` toy subgroup rows",
        "3,000,000 primary trials",
        "four CPU-hours",
        "4 GiB peak RSS",
        "24 wall-clock hours",
        "self-generated public toy targets",
        "faithful PKC factor base",
        "secp256k1",
        "independent validator",
        "PAUSE_INCONCLUSIVE",
        "REJECT_AS_ARTIFACT",
        "HYP-M16-SOLVER-SLOPE-001",
    ):
        if binding not in task_026:
            problems.append(
                f"{BOUNDED_AUTHORIZATION_TASK_ID} is missing binding {binding}"
            )
    completed_desk_task = task_sections.get(COMPLETED_DESK_TASK_ID, "")
    expected_completed_desk_lines = (
        "Status: completed_non_executable_scoped_blocker",
        "Authorization: none",
        "Outcome: `scoped_blocker`",
        "Retention: `zero_retention_success`",
    )
    for line in expected_completed_desk_lines:
        if not re.search(
            rf"^{re.escape(line)}$",
            completed_desk_task,
            flags=re.MULTILINE,
        ):
            problems.append(
                f"{COMPLETED_DESK_TASK_ID} must contain {line!r}"
            )
    for binding in (
        M16_PROJECTIVE_ARTIFACT_PATH,
        M16_PROJECTIVE_ARTIFACT_SHA256,
        "PKC-SMOOTH-M16-PROJECTIVE-S17-BRIDGE-001",
        "SC-PKC-M16-PROJECTIVE-S17-BRIDGE-RESULT",
        DESK_PRIORITY_CELL_ID,
        DESK_PRIORITY_STUB_ID,
        DESK_PRIORITY_COST_ID,
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "`{2,3,7}`",
        "`certificate_replayed`",
        "`not_established`",
        "`excluded_nonexperimental`",
        "`unpriced`",
        "fixed-degree",
        "reverse projection",
    ):
        if binding not in completed_desk_task:
            problems.append(
                f"{COMPLETED_DESK_TASK_ID} is missing closure binding {binding}"
            )
    completed_resultant_task = task_sections.get(
        COMPLETED_RESULTANT_TASK_ID, ""
    )
    expected_completed_resultant_lines = (
        "Status: completed_non_executable_scoped_blocker",
        "Authorization: none",
        "Outcome: `scoped_blocker`",
        "Retention: `zero_retention_success`",
    )
    for line in expected_completed_resultant_lines:
        if not re.search(
            rf"^{re.escape(line)}$",
            completed_resultant_task,
            flags=re.MULTILINE,
        ):
            problems.append(
                f"{COMPLETED_RESULTANT_TASK_ID} must contain {line!r}"
            )
    for binding in (
        M16_RESULTANT_ARTIFACT_PATH,
        M16_RESULTANT_ARTIFACT_SHA256,
        "PKC-SMOOTH-M16-PROJECTIVE-RESULTANT-KERNEL-001",
        "SC-PKC-M16-PROJECTIVE-RESULTANT-KERNEL-RESULT",
        DESK_PRIORITY_CELL_ID,
        DESK_PRIORITY_STUB_ID,
        DESK_PRIORITY_COST_ID,
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "`kernel_bound_non_run_certificate`",
        "`not_established`",
        "`excluded_nonexperimental`",
        "`unpriced`",
        "fixed-degree",
        "zero forms",
        "[1:0]",
        "recursive",
        "C16",
        "C2",
    ):
        if binding.casefold() not in completed_resultant_task.casefold():
            problems.append(
                f"{COMPLETED_RESULTANT_TASK_ID} is missing closure binding "
                f"{binding}"
            )
    completed_specialization_task = task_sections.get(
        COMPLETED_SPECIALIZATION_TASK_ID, ""
    )
    expected_completed_specialization_lines = (
        "Status: completed_non_executable_scoped_blocker",
        "Authorization: none",
        "Outcome: `scoped_blocker`",
        "Retention: `zero_retention_success`",
    )
    for line in expected_completed_specialization_lines:
        if not re.search(
            rf"^{re.escape(line)}$",
            completed_specialization_task,
            flags=re.MULTILINE,
        ):
            problems.append(
                f"{COMPLETED_SPECIALIZATION_TASK_ID} must contain {line!r}"
            )
    for binding in (
        M16_SPECIALIZATION_ARTIFACT_PATH,
        M16_SPECIALIZATION_ARTIFACT_SHA256,
        M16_SPECIALIZATION_ARTIFACT_ID,
        M16_SPECIALIZATION_CLAIM_ID,
        DESK_PRIORITY_CELL_ID,
        DESK_PRIORITY_STUB_ID,
        DESK_PRIORITY_COST_ID,
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "`unpriced`",
        "actual frozen",
        "formal degrees",
        "coefficient unit exactly `1`",
        "affine `[y:1]`",
        "infinity `[1:0]`",
        "uniform",
        "unconditionally",
        "projective evaluation",
        "witness-chain",
        "C16",
        "C2",
        "open_parked",
        "authorization",
        "cost claim",
    ):
        if binding.casefold() not in completed_specialization_task.casefold():
            problems.append(
                f"{COMPLETED_SPECIALIZATION_TASK_ID} is missing closure binding "
                f"{binding}"
            )
    completed_witness_task = task_sections.get(COMPLETED_WITNESS_TASK_ID, "")
    expected_completed_witness_lines = (
        "Status: completed_non_executable_kernel_result",
        f"Desk priority: `{DESK_PRIORITY_CELL_ID}` / `{DESK_PRIORITY_STUB_ID}`",
        "Authorization: none",
        "Outcome: `closed_exact_theorem`",
        "Retention: `zero_retention_success`",
    )
    for line in expected_completed_witness_lines:
        if not re.search(
            rf"^{re.escape(line)}$",
            completed_witness_task,
            flags=re.MULTILINE,
        ):
            problems.append(
                f"{COMPLETED_WITNESS_TASK_ID} must contain {line!r}"
            )
    for binding in (
        DESK_PRIORITY_CELL_ID,
        DESK_PRIORITY_STUB_ID,
        DESK_PRIORITY_COST_ID,
        M16_SPECIALIZATION_ARTIFACT_PATH,
        M16_WITNESS_ARTIFACT_PATH,
        M16_WITNESS_ARTIFACT_SHA256,
        M16_WITNESS_ARTIFACT_ID,
        M16_WITNESS_CLAIM_ID,
        "projectiveOutputAtOver_frozenC_isHomogeneous",
        "projective homogenization",
        "FrozenProjectiveChain",
        "specializeOver",
        "fourteen",
        "q 0",
        "q 15",
        "[0:0]",
        "[1:0]",
        "C16",
        "C2",
        "partial",
        "open_parked",
        "no injectivity",
        "base-field descent",
        "cost claim",
    ):
        if binding.casefold() not in completed_witness_task.casefold():
            problems.append(
                f"{COMPLETED_WITNESS_TASK_ID} is missing binding {binding}"
            )
    completed_guarded_task = task_sections.get(COMPLETED_GUARDED_TASK_ID, "")
    normalized_completed_guarded_task = " ".join(
        completed_guarded_task.split()
    )
    expected_completed_guarded_lines = (
        "Status: completed_non_executable_kernel_result",
        "Kind: theorem | research | review",
        f"Desk priority: `{DESK_PRIORITY_CELL_ID}` / `{DESK_PRIORITY_STUB_ID}`",
        "Authorization: none",
        "Outcome: `closed_exact_theorem`",
        "Retention: `zero_retention_success`",
        "Completed on: 2026-07-29",
    )
    for line in expected_completed_guarded_lines:
        if not re.search(
            rf"^{re.escape(line)}$",
            completed_guarded_task,
            flags=re.MULTILINE,
        ):
            problems.append(
                f"{COMPLETED_GUARDED_TASK_ID} must contain {line!r}"
            )
    for binding in (
        DESK_PRIORITY_CELL_ID,
        DESK_PRIORITY_STUB_ID,
        DESK_PRIORITY_COST_ID,
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        M16_WITNESS_ARTIFACT_PATH,
        M16_GUARDED_ARTIFACT_PATH,
        M16_GUARDED_ARTIFACT_SHA256,
        M16_GUARDED_ARTIFACT_ID,
        M16_GUARDED_CLAIM_ID,
        M16_GUARDED_SOURCE_SHA256,
        "Ecdlp/Proved/FrozenProjectiveGuardSystem.lean",
        "literal finite",
        "∃ assignment : GuardVar → K",
        "∀ e : GuardedEquation",
        "MvPolynomial.eval assignment",
        "not a parallel recursive syntax",
        "Field k",
        "injective",
        "algebraically closed target field `K`",
        "fourteen",
        "56 raw variables",
        "fifteen `H` equations",
        "fourteen guards",
        "total degree at most four",
        "native_decide",
        "Lean.ofReduceBool",
        "[0:0]",
        "[1:0]",
        "base-field descent",
        "chart/gauge",
        "independent relations",
        "open_non_executable",
        "partial",
        "open_parked",
        "solver",
        "experiment authorization",
        "cost claim",
        "route promotion",
    ):
        if (
            " ".join(binding.split()).casefold()
            not in normalized_completed_guarded_task.casefold()
        ):
            problems.append(
                f"{COMPLETED_GUARDED_TASK_ID} is missing binding {binding}"
            )
    completed_chart_task = task_sections.get(COMPLETED_CHART_TASK_ID, "")
    normalized_completed_chart_task = " ".join(completed_chart_task.split())
    expected_completed_chart_lines = (
        "Status: completed_non_executable_kernel_result",
        "Kind: theorem | research | review",
        f"Desk priority: `{DESK_PRIORITY_CELL_ID}` / `{DESK_PRIORITY_STUB_ID}`",
        "Authorization: none",
        "Outcome: `closed_exact_theorem`",
        "Retention: `zero_retention_success`",
        "Completed on: 2026-07-29",
    )
    for line in expected_completed_chart_lines:
        if not re.search(
            rf"^{re.escape(line)}$",
            completed_chart_task,
            flags=re.MULTILINE,
        ):
            problems.append(
                f"{COMPLETED_CHART_TASK_ID} must contain {line!r}"
            )
    for binding in (
        DESK_PRIORITY_CELL_ID,
        DESK_PRIORITY_STUB_ID,
        DESK_PRIORITY_COST_ID,
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        M16_GUARDED_ARTIFACT_PATH,
        M16_CHART_ARTIFACT_PATH,
        M16_CHART_ARTIFACT_SHA256,
        M16_CHART_ARTIFACT_ID,
        M16_CHART_CLAIM_ID,
        M16_CHART_SOURCE_SHA256,
        "Ecdlp/Proved/FrozenProjectiveChartSystem.lean",
        "InfinityMask := Finset (Fin 14)",
        "[1:0]",
        "[X_i:1]",
        "14 - I.card",
        "fifteen",
        "degree",
        "2/4/2",
        "FrozenChartPolynomialSystem",
        "frozenProjectiveChain_iff_chartPolynomialCover",
        "frozenGuardedProjectiveSystem_iff_chartPolynomialCover",
        "frozenRecS17_iff_chartPolynomialCover_over",
        "native_decide",
        "2^14",
        "neither Lean",
        "open_non_executable",
        "partial",
        "open_parked",
        "solver",
        "experiment authorization",
        "cost claim",
        "route promotion",
        "60 semantic mutations",
    ):
        if (
            " ".join(binding.split()).casefold()
            not in normalized_completed_chart_task.casefold()
        ):
            problems.append(
                f"{COMPLETED_CHART_TASK_ID} is missing binding {binding}"
            )
    active_hypotheses = [
        hypothesis_id
        for hypothesis_id, fields in hypotheses.items()
        if fields.get("status") == "active"
    ]
    bounded_hypothesis = hypotheses.get(
        BOUNDED_AUTHORIZATION_HYPOTHESIS_ID, {}
    )
    expected_bounded_hypothesis = {
        "direction": "experiment",
        "status": "closed",
        "hypothesis_type": "ENABLING",
        "lifecycle_state": "PROMOTED",
        "task_id": BOUNDED_AUTHORIZATION_TASK_ID,
        "route_id": BOUNDED_AUTHORIZATION_ROUTE_ID,
        "cell_id": BOUNDED_AUTHORIZATION_CELL_ID,
        "authorization_class": "external_bounded_singleton",
        "authorization_id": BOUNDED_AUTHORIZATION_ID,
        "native_engine_candidate": "false",
        "exact_test": (
            "experiments/engine/pkc_smooth_m16_fixed_target_yield/"
            "PREREGISTRATION.md"
        ),
    }
    for field, expected in expected_bounded_hypothesis.items():
        if bounded_hypothesis.get(field) != expected:
            problems.append(
                f"{BOUNDED_AUTHORIZATION_HYPOTHESIS_ID}.{field} must be "
                f"{expected!r}"
            )
    if active_hypotheses:
        problems.append(
            "the consumed singleton must leave no active hypothesis; "
            f"found {active_hypotheses}"
        )
    for hypothesis_id in active_hypotheses:
        if hypothesis_id not in tasks_text:
            problems.append(
                f"active hypothesis {hypothesis_id} is not referenced by "
                "tasks/ECDLP_RESEARCH.md"
            )
    if "Promotion and exact-target work remain disabled." not in tasks_text:
        problems.append(
            "tasks/ECDLP_RESEARCH.md must preserve the promotion boundary"
        )
    next_tasks_text = NEXT_TASKS.read_text(encoding="utf-8")
    maintenance = data.get("maintenance_cycle", {})
    if maintenance.get("cycle_id") != MAINTENANCE_CYCLE_ID:
        problems.append("decision substrate has the wrong maintenance cycle")
    if maintenance.get("task_id") != MAINTENANCE_TASK_ID:
        problems.append("maintenance cycle must bind TASK-010")
    if maintenance.get("status") != "completed_accepted":
        problems.append("maintenance cycle must be completed_accepted")
    if maintenance.get("completed_on") != "2026-07-27":
        problems.append("maintenance cycle completed_on must be 2026-07-27")
    if maintenance.get("acceptance_commit") != MAINTENANCE_ACCEPTANCE_COMMIT:
        problems.append("maintenance cycle acceptance commit drifted")
    if maintenance.get("authorizes_experiment") is not False:
        problems.append("maintenance cycle must not authorize an experiment")
    if maintenance.get("promotes_route") is not False:
        problems.append("maintenance cycle must not promote a route")
    if maintenance.get("historical_outcomes_mutable") is not False:
        problems.append("maintenance cycle must preserve historical outcomes")
    if not all(
        binding in next_tasks_text
        for binding in (
            "Current ECDLP decision: `TASK-029` is terminal.",
            "The operational queue returns to non-executable `TASK-008`",
            "no new scientific execution is selected",
        )
    ):
        problems.append(
            "tasks/NEXT.md must expose the terminal proposal review and "
            "non-executable maintenance intake"
        )
    for binding in (
        BOUNDED_AUTHORIZATION_ID,
        BOUNDED_AUTHORIZATION_HYPOTHESIS_ID,
        BOUNDED_TERMINAL_EVENT_ID,
        BOUNDED_TERMINAL_STATUS,
        f"`{BOUNDED_AUTHORIZATION_ROUTE_ID}` remains",
        "`R-GLV-SEMAEV` is also",
        "selected attack route remains null",
        "native bounded",
        "promotion",
    ):
        if binding not in next_tasks_text:
            problems.append(
                f"tasks/NEXT.md is missing bounded authorization binding {binding}"
            )
    for binding in (
        DESK_PRIORITY_CELL_ID,
        DESK_PRIORITY_STUB_ID,
        COMPLETED_GUARDED_TASK_ID,
        COMPLETED_CHART_TASK_ID,
        COMPLETED_STRATA_TASK_ID,
        COMPLETED_PROPAGATION_TASK_ID,
    ):
        if binding not in next_tasks_text:
            problems.append(f"tasks/NEXT.md is missing desk-priority binding {binding}")
    for binding_id in (
        STRUCTURAL_DECISION_ID,
        STRUCTURAL_ITERATION_ID,
        STRUCTURAL_ROUTE_ID,
        STRUCTURAL_HYPOTHESIS_ID,
        STRUCTURAL_TASK_ID,
    ):
        if binding_id not in next_tasks_text:
            problems.append(f"tasks/NEXT.md is missing structural binding {binding_id}")

    for relative in STALE_STATUS_FILES:
        path = ROOT / relative
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        for phrase in STALE_ACTIVE_PHRASES:
            if phrase in text:
                problems.append(f"{relative}: stale active phrase {phrase!r}")

    decisions_log = (ROOT / "data" / "research_decisions.md").read_text(
        encoding="utf-8"
    )
    if selection.get("decision_id") not in decisions_log:
        problems.append("route-selection decision is missing from research_decisions.md")
    if FOUNDATION_BUILD_DECISION_ID not in decisions_log:
        problems.append(
            f"{FOUNDATION_BUILD_DECISION_ID} is missing from research_decisions.md"
        )
    symbolic_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 25 |")
        ),
        "",
    )
    for binding in (
        PREVIOUS_DESK_TASK_ID,
        PREVIOUS_SEMANTIC_TASK_ID,
        "scoped_blocker",
        "zero_retention_success",
        M16_SYMBOLIC_ARTIFACT_PATH,
        M16_SYMBOLIC_ARTIFACT_SHA256,
        "SC-PKC-M16-SYMBOLIC-DESK-RESULT",
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
    ):
        if binding not in symbolic_closure_row:
            problems.append(
                "TASK-015 closure row is missing binding "
                f"{binding}"
            )
    semantic_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 26 |")
        ),
        "",
    )
    for binding in (
        PREVIOUS_SEMANTIC_TASK_ID,
        PREVIOUS_PROJECTIVE_TASK_ID,
        "scoped_blocker",
        "zero_retention_success",
        M16_SEMANTIC_ARTIFACT_PATH,
        M16_SEMANTIC_ARTIFACT_SHA256,
        "SC-PKC-M16-SEMANTIC-BRIDGE-RESULT",
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
    ):
        if binding not in semantic_closure_row:
            problems.append(
                "TASK-016 closure row is missing binding "
                f"{binding}"
            )
    exceptional_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 27 |")
        ),
        "",
    )
    for binding in (
        PREVIOUS_PROJECTIVE_TASK_ID,
        COMPLETED_DESK_TASK_ID,
        "scoped_blocker",
        "zero_retention_success",
        M16_EXCEPTIONAL_ARTIFACT_PATH,
        M16_EXCEPTIONAL_ARTIFACT_SHA256,
        "PKC-SMOOTH-M16-EXCEPTIONAL-FIBERS-001",
        "SC-PKC-M16-EXCEPTIONAL-FIBER-RESULT",
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "certificate_replayed",
        "not_established",
        "excluded_nonexperimental",
        "unpriced",
        "{2,3,7}",
    ):
        if binding not in exceptional_closure_row:
            problems.append(
                "TASK-017 closure row is missing binding "
                f"{binding}"
            )
    projective_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 28 |")
        ),
        "",
    )
    for binding in (
        COMPLETED_DESK_TASK_ID,
        COMPLETED_RESULTANT_TASK_ID,
        "scoped_blocker",
        "zero_retention_success",
        M16_PROJECTIVE_ARTIFACT_PATH,
        M16_PROJECTIVE_ARTIFACT_SHA256,
        "PKC-SMOOTH-M16-PROJECTIVE-S17-BRIDGE-001",
        "SC-PKC-M16-PROJECTIVE-S17-BRIDGE-RESULT",
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "certificate_replayed",
        "not_established",
        "excluded_nonexperimental",
        "unpriced",
        "fixed-degree",
        "reverse projection",
        "{2,3,7}",
    ):
        if binding not in projective_closure_row:
            problems.append(
                "TASK-018 closure row is missing binding "
                f"{binding}"
            )
    resultant_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 29 |")
        ),
        "",
    )
    for binding in (
        COMPLETED_RESULTANT_TASK_ID,
        COMPLETED_SPECIALIZATION_TASK_ID,
        "scoped_blocker",
        "zero_retention_success",
        M16_RESULTANT_ARTIFACT_PATH,
        M16_RESULTANT_ARTIFACT_SHA256,
        "PKC-SMOOTH-M16-PROJECTIVE-RESULTANT-KERNEL-001",
        "SC-PKC-M16-PROJECTIVE-RESULTANT-KERNEL-RESULT",
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "kernel_bound_non_run_certificate",
        "not_established",
        "excluded_nonexperimental",
        "unpriced",
        "resultant/common-projective-root",
        "zero forms",
        "[1:0]",
        "recursive",
        "C16",
        "C2",
    ):
        if binding not in resultant_closure_row:
            problems.append(
                "TASK-019 closure row is missing binding "
                f"{binding}"
            )
    specialization_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 30 |")
        ),
        "",
    )
    for binding in (
        COMPLETED_SPECIALIZATION_TASK_ID,
        COMPLETED_WITNESS_TASK_ID,
        "scoped_blocker",
        "zero_retention_success",
        M16_SPECIALIZATION_ARTIFACT_PATH,
        M16_SPECIALIZATION_ARTIFACT_SHA256,
        M16_SPECIALIZATION_ARTIFACT_ID,
        M16_SPECIALIZATION_CLAIM_ID,
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "kernel_bound_non_run_certificate",
        "not_established",
        "excluded_nonexperimental",
        "partial",
        "unpriced",
        "predecessor output-degree bound",
        "unconditional one-step resultant/common-projective-root equivalence",
        "projective evaluation",
        "witness-chain",
        "C16",
        "C2",
        "[1:0]",
        "open_parked",
        "experiment authorization",
        "cost claim",
    ):
        if binding not in specialization_closure_row:
            problems.append(
                "TASK-020 closure row is missing binding "
                f"{binding}"
            )
    witness_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 31 |")
        ),
        "",
    )
    for binding in (
        COMPLETED_WITNESS_TASK_ID,
        "closed_exact_theorem",
        "zero_retention_success",
        M16_WITNESS_ARTIFACT_PATH,
        M16_WITNESS_ARTIFACT_SHA256,
        M16_WITNESS_ARTIFACT_ID,
        M16_WITNESS_CLAIM_ID,
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "kernel_bound_non_run_certificate",
        "not_established",
        "excluded_nonexperimental",
        "partial",
        "unpriced",
        "declared-degree homogeneity",
        "FrozenProjectiveChain",
        "fourteen valid intermediate projective slots",
        "[1:0]",
        "[0:0]",
        "base-field",
        "open_parked",
        "experiment authorization",
        "cost claim",
    ):
        if binding.casefold() not in witness_closure_row.casefold():
            problems.append(
                "TASK-021 closure row is missing binding "
                f"{binding}"
            )
    guarded_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 32 |")
        ),
        "",
    )
    for binding in (
        COMPLETED_GUARDED_TASK_ID,
        "closed_exact_theorem",
        "zero_retention_success",
        M16_GUARDED_ARTIFACT_PATH,
        M16_GUARDED_ARTIFACT_SHA256,
        M16_GUARDED_ARTIFACT_ID,
        M16_GUARDED_CLAIM_ID,
        M16_GUARDED_SOURCE_SHA256,
        "Ecdlp/Proved/FrozenProjectiveGuardSystem.lean",
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "kernel-checks",
        "literal finite guarded `MvPolynomial` family",
        "∃ assignment : GuardVar → K",
        "∀ e : GuardedEquation",
        "not a parallel recursive syntax",
        "injective field map",
        "algebraically closed target",
        "fourteen projective witness slots",
        "56 raw scalar variables",
        "fifteen literal `H` equations",
        "fourteen guards",
        "29 equation-family members",
        "total degree at most four",
        "native_decide",
        "not_established",
        "excluded_nonexperimental",
        "open_non_executable",
        "partial",
        "unpriced",
        "[0:0]",
        "[1:0]",
        "source field",
        "independent relations",
        "open_parked",
        "solver input",
        "experiment authorization",
        "cost claim",
        "route promotion",
        "26 semantic mutations",
    ):
        if binding.casefold() not in guarded_closure_row.casefold():
            problems.append(
                "TASK-022 closure row is missing binding "
                f"{binding}"
            )
    chart_closure_row = next(
        (
            line
            for line in decisions_log.splitlines()
            if line.startswith("| 33 |")
        ),
        "",
    )
    for binding in (
        COMPLETED_CHART_TASK_ID,
        "closed_exact_theorem",
        "zero_retention_success",
        M16_CHART_ARTIFACT_PATH,
        M16_CHART_ARTIFACT_SHA256,
        M16_CHART_ARTIFACT_ID,
        M16_CHART_CLAIM_ID,
        M16_CHART_SOURCE_SHA256,
        "Ecdlp/Proved/FrozenProjectiveChartSystem.lean",
        "B-PKC-M16-COMPLETE-COST-BRIDGE",
        "kernel-checks",
        "affine/infinity chart-polynomial cover",
        "InfinityMask",
        "[1:0]",
        "[X_i:1]",
        "14 - I.card",
        "fifteen `H` equations",
        "degree",
        "2^14",
        "neither enumerated nor materialized",
        "native_decide",
        "Lean.ofReduceBool",
        "not_established",
        "excluded_nonexperimental",
        "open_non_executable",
        "partial",
        "unpriced",
        "base-field descent",
        "independent relations",
        "open_parked",
        "solver input",
        "experiment authorization",
        "cost claim",
        "route promotion",
        "60 semantic mutations",
    ):
        if binding.casefold() not in chart_closure_row.casefold():
            problems.append(
                "TASK-023 closure row is missing binding "
                f"{binding}"
            )

    return problems


def main() -> int:
    try:
        problems = validate()
    except (KeyError, TypeError, json.JSONDecodeError) as error:
        print(f"decision-substrate check FAILED: malformed source: {error}", file=sys.stderr)
        return 1

    if problems:
        print("decision-substrate check FAILED:")
        for problem in problems:
            print(f"  - {problem}")
        return 1

    data = load_json(DECISIONS)
    print(
        "decision-substrate check OK: "
        f"{len(data['routes'])} routes, {len(data['foundations'])} foundations, "
        "1 completed bounded structural route, 1 consumed decision-level "
        "synthetic-toy experiment record, 0 current experiment authorizations, "
        "0 native/route authorizations, 0 promoted routes."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
