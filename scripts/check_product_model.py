#!/usr/bin/env python3
"""Validate KeyAI's canonical product model and public-claim boundary."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from pilot_evidence import (
    expected_pilot_status,
    expected_primary_status,
    latest_primary_disposition,
    parse_iso_date,
    primary_dispositions,
    record_sequence,
    valid_returns,
    valid_second_projects,
)

ROOT = Path(__file__).resolve().parent.parent
MODEL_PATH = ROOT / "repo" / "PRODUCT_MODEL.json"
PILOT_PATH = ROOT / "repo" / "PILOT_PROTOCOL.json"


def main() -> int:
    errors: list[str] = []

    def check(condition: bool, message: str) -> None:
        if not condition:
            errors.append(message)

    try:
        model = json.loads(MODEL_PATH.read_text(encoding="utf-8"))
        pilot = json.loads(PILOT_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"product model check failed: {exc}", file=sys.stderr)
        return 1

    check(model.get("schema_version") == "1.0", "schema_version must be 1.0")
    check(model.get("name") == "KeyAI", "name must be KeyAI")
    check(
        isinstance(model.get("repository_url"), str)
        and model["repository_url"].startswith("https://github.com/")
        and not model["repository_url"].endswith("/"),
        "repository_url must be a canonical GitHub repository URL without a trailing slash",
    )
    check(
        model.get("category") == "verification workspace for AI research",
        "category must remain the canonical product category",
    )

    workflow = model.get("workflow", [])
    workflow_ids = [step.get("id") for step in workflow if isinstance(step, dict)]
    check(
        workflow_ids == ["ingest", "structure", "decide", "execute", "verify", "retain"],
        "workflow must preserve the six-stage product loop",
    )
    check(
        all(step.get("label") and step.get("outcome") for step in workflow),
        "every workflow step needs a label and outcome",
    )
    queues = model.get("work_queues", {})
    check(
        queues.get("router") == "tasks/NEXT.md"
        and queues.get("product") == "tasks/KEYAI_PRODUCT.md"
        and queues.get("ecdlp_reference_research") == "tasks/ECDLP_RESEARCH.md",
        "product and ECDLP work must use separate canonical queues",
    )
    for key in ("router", "product", "ecdlp_reference_research"):
        path = queues.get(key)
        check(
            isinstance(path, str) and (ROOT / path).is_file(),
            f"work_queues.{key} must point at an existing file",
        )
    check(
        "never count as ECDLP progress" in queues.get("boundary", "")
        and "never counts as external product validation" in queues.get("boundary", ""),
        "work queue boundary must prevent product/research KPI conflation",
    )

    hypotheses = model.get("customer_hypotheses", [])
    check(len(hypotheses) >= 2, "at least two customer hypotheses are required")
    hypothesis_ids = [item.get("id") for item in hypotheses]
    hypotheses_by_id = {
        item.get("id"): item for item in hypotheses if isinstance(item, dict)
    }
    check(len(hypothesis_ids) == len(set(hypothesis_ids)), "customer hypothesis ids must be unique")
    hypothesis_statuses = {"unvalidated", "testing", "supported", "rejected"}
    for hypothesis in hypotheses:
        hypothesis_id = hypothesis.get("id", "<missing>")
        status_value = hypothesis.get("status")
        evidence = hypothesis.get("evidence")
        check(status_value in hypothesis_statuses,
              f"customer hypothesis has an invalid status: {hypothesis_id}")
        check(isinstance(evidence, list),
              f"customer hypothesis evidence must be a list: {hypothesis_id}")
        if status_value in {"testing", "supported", "rejected"}:
            check(bool(evidence),
                  f"customer hypothesis status requires dated evidence: {hypothesis_id}")
        for record in evidence if isinstance(evidence, list) else []:
            check(
                isinstance(record, dict)
                and re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(record.get("performed_on", "")))
                and bool(record.get("source")),
                f"customer hypothesis evidence needs performed_on and source: {hypothesis_id}",
            )

    reference = model.get("reference_environment", {})
    for key in (
        "decision_source",
        "formal_source",
        "stats_source",
        "frontier_source",
        "result_source",
        "verified_index_source",
        "task_source",
    ):
        path = reference.get(key)
        check(isinstance(path, str) and bool(path), f"reference_environment.{key} is required")
        if isinstance(path, str) and path:
            check((ROOT / path).exists(), f"reference_environment.{key} does not exist: {path}")
    check(
        "does not solve" in reference.get("boundary", "").lower(),
        "reference boundary must state that the environment does not solve ECDLP",
    )

    stage = model.get("current_stage", {})
    check(stage.get("id") == "reference-deployment", "current stage must be reference-deployment")
    check(
        len(stage.get("capabilities_now", [])) >= 4,
        "current stage must expose at least four evidenced capabilities",
    )
    for capability in stage.get("capabilities_now", []):
        for evidence in capability.get("evidence", []):
            check((ROOT / evidence).exists(), f"capability evidence does not exist: {evidence}")
    check(
        len(stage.get("not_yet", [])) >= 5,
        "current stage must retain an explicit not-yet boundary",
    )

    mvp = model.get("mvp", {})
    check("non-owner" in mvp.get("definition", ""), "MVP must require a non-owner user")
    check(
        any(metric.get("id") == "external-pilot" for metric in mvp.get("exit_metrics", [])),
        "MVP exit metrics must include an external pilot",
    )
    check(
        mvp.get("yc_readiness", "").startswith("Not ready today."),
        "YC readiness must remain evidence-gated until a pilot exists",
    )

    pilot_model = model.get("pilot", {})
    check(pilot.get("schema_version") == "1.0", "pilot schema_version must be 1.0")
    check(pilot.get("id") == pilot_model.get("id"), "pilot id must match the product model")
    check(pilot.get("task_id") == "TASK-011", "pilot must remain bound to TASK-011")
    check(
        pilot.get("status") == pilot_model.get("status"),
        "pilot status must match the product model",
    )
    check(
        pilot_model.get("protocol_source") == "repo/PILOT_PROTOCOL.json",
        "product model must point to the canonical pilot protocol",
    )
    check(
        pilot_model.get("task_source") == "tasks/KEYAI_PRODUCT.md",
        "the external pilot must use the product queue",
    )
    check(
        pilot_model.get("evidence_summary") == pilot.get("evidence_state"),
        "pilot evidence summary must match the canonical protocol",
    )
    check(
        pilot.get("primary_hypothesis_id") == pilot_model.get("primary_hypothesis_id")
        == "CH-001",
        "pilot must keep CH-001 as the primary discovery hypothesis",
    )
    check(
        set(pilot.get("secondary_hypothesis_ids", []))
        == set(pilot_model.get("secondary_hypothesis_ids", []))
        and set(pilot.get("secondary_hypothesis_ids", [])).issubset(set(hypothesis_ids)),
        "pilot secondary hypotheses must match the product model",
    )
    check(
        len(pilot.get("session_plan", [])) == 4,
        "pilot must define the four-stage observed session",
    )
    measurement_ids = {
        item.get("id") for item in pilot.get("measurements", []) if isinstance(item, dict)
    }
    check(
        {
            "orientation-time",
            "repeated-pain",
            "workflow-fit",
            "discovery-disposition",
            "second-session",
            "provenance-completeness",
            "generator-edits",
            "public-data-safety",
        }.issubset(measurement_ids),
        "pilot measurements must preserve primary, diagnostic, and guardrail metrics",
    )
    for outcome in ("build", "change", "stop", "pending"):
        check(
            bool(pilot.get("decision_rules", {}).get(outcome)),
            f"pilot decision rule is missing: {outcome}",
        )
    check(
        pilot.get("status")
        in {"inactive", "recruiting", "discovery_active", "discovery_complete", "stopped", "mvp_validated"},
        "pilot status is not recognized",
    )
    check(
        isinstance(pilot.get("evidence_log"), list),
        "pilot evidence_log must be a list",
    )
    safety = pilot.get("privacy_and_safety", {})
    for key in (
        "authorization_attestation",
        "collection_policy",
        "retention_policy",
        "incident_response",
        "task_authority",
        "experiment_gate",
    ):
        check(bool(safety.get(key)), f"pilot privacy_and_safety.{key} is required")
    check(
        "does not authorize executing" in safety.get("task_authority", ""),
        "TASK-011 must explicitly authorize no candidate execution",
    )
    check(
        "superseding route-selection decision" in safety.get("experiment_gate", ""),
        "ECDLP experiments must require a superseding route-selection decision",
    )
    evidence_schema = pilot.get("evidence_log_schema", {})
    required_record_fields = set(evidence_schema.get("required_fields", []))
    allowed_stages = set(evidence_schema.get("stages", []))
    allowed_record_statuses = set(evidence_schema.get("statuses", []))
    allowed_dispositions = {"build", "change", "stop", "pending"}
    check(
        "external CH-001 record" in evidence_schema.get("completed_discovery_definition", "")
        and "latest completed external CH-001 discovery" in evidence_schema.get(
            "task_012_unlock_definition", ""
        )
        and "relocks TASK-012" in evidence_schema.get("task_012_unlock_definition", ""),
        "pilot evidence schema must bind discovery completion and TASK-012 unlock to CH-001",
    )
    check(
        set(evidence_schema.get("primary_hypothesis_lifecycle", {}))
        == {"unvalidated", "testing", "supported", "rejected"},
        "pilot evidence schema must define the complete CH-001 lifecycle",
    )
    records = pilot.get("evidence_log", [])
    record_ids: list[str] = []
    record_sequences: list[int] = []
    record_dates = []
    expected_task_by_stage = {
        "qualification": "TASK-011",
        "discovery": "TASK-011",
        "second_project": "TASK-012",
        "return": "TASK-012",
    }
    for record in records if isinstance(records, list) else []:
        if not isinstance(record, dict):
            check(False, "pilot evidence records must be objects")
            continue
        record_id = record.get("id", "<missing>")
        record_ids.append(str(record_id))
        sequence = record_sequence(record)
        if sequence is not None:
            record_sequences.append(sequence)
        performed_on = parse_iso_date(record.get("performed_on"))
        if performed_on is not None:
            record_dates.append(performed_on)
        check(required_record_fields.issubset(record),
              f"pilot evidence record is missing required fields: {record_id}")
        check(sequence is not None,
              f"pilot evidence record needs a positive integer sequence: {record_id}")
        check(
            isinstance(record.get("case_id"), str)
            and re.fullmatch(r"CASE-[A-Z0-9-]{3,40}", record.get("case_id", "")) is not None,
            f"pilot evidence record needs an opaque CASE-* case_id: {record_id}",
        )
        check(record.get("hypothesis_id") in hypothesis_ids,
              f"pilot evidence record has unknown hypothesis: {record_id}")
        check(isinstance(record.get("external"), bool),
              f"pilot evidence record external must be boolean: {record_id}")
        check(record.get("stage") in allowed_stages,
              f"pilot evidence record has invalid stage: {record_id}")
        check(record.get("status") in allowed_record_statuses,
              f"pilot evidence record has invalid status: {record_id}")
        check(performed_on is not None,
              f"pilot evidence record needs a real ISO date: {record_id}")
        check(
            record.get("task_id") == expected_task_by_stage.get(record.get("stage")),
            f"pilot evidence record has the wrong owning task: {record_id}",
        )
        check(
            record.get("disposition") in allowed_dispositions | {None},
            f"pilot evidence record has invalid disposition: {record_id}",
        )
        check(
            isinstance(record.get("public_summary"), str)
            and bool(record.get("public_summary", "").strip()),
            f"pilot evidence record needs a non-empty public_summary: {record_id}",
        )
        evidence_files = record.get("evidence_files", [])
        check(
            isinstance(evidence_files, list),
            f"pilot evidence_files must be a list: {record_id}",
        )
        if record.get("status") == "completed":
            check(
                bool(evidence_files),
                f"completed pilot evidence needs at least one evidence file: {record_id}",
            )
        for evidence_path in evidence_files if isinstance(evidence_files, list) else []:
            if not isinstance(evidence_path, str) or not evidence_path or "\\" in evidence_path:
                check(False, f"pilot evidence path must be a repository-relative file: {record_id}")
                continue
            candidate = (ROOT / evidence_path).resolve()
            check(
                candidate.is_relative_to(ROOT.resolve()) and candidate.is_file(),
                f"pilot evidence path must resolve to a regular file inside the repository: "
                f"{evidence_path}",
            )
    check(
        len(record_ids) == len(set(record_ids)),
        "pilot evidence record ids must be unique",
    )
    check(
        len(record_sequences) == len(set(record_sequences))
        and record_sequences == sorted(record_sequences),
        "pilot evidence sequences must be unique and stored in increasing order",
    )
    check(
        record_dates == sorted(record_dates),
        "pilot evidence performed_on dates must not move backward",
    )
    completed_discovery = [
        record
        for record in primary_dispositions(pilot)
        if record.get("disposition") in {"build", "change", "stop"}
    ]
    second_projects = valid_second_projects(pilot)
    completed_returns = valid_returns(pilot)
    raw_primary_second_projects = [
        record
        for record in records
        if isinstance(record, dict)
        and record.get("hypothesis_id") == pilot.get("primary_hypothesis_id")
        and record.get("external") is True
        and record.get("stage") == "second_project"
        and record.get("status") == "completed"
    ]
    raw_primary_returns = [
        record
        for record in records
        if isinstance(record, dict)
        and record.get("hypothesis_id") == pilot.get("primary_hypothesis_id")
        and record.get("external") is True
        and record.get("stage") == "return"
        and record.get("status") == "completed"
    ]
    check(
        len(second_projects) == len(raw_primary_second_projects),
        "every completed CH-001 second_project requires the latest build disposition, "
        "TASK-012 ownership, matching case_id, and forward chronology",
    )
    check(
        len(completed_returns) == len(raw_primary_returns),
        "every completed CH-001 return requires an ordered same-case TASK-012 second_project",
    )
    completed_external_records = [
        record for record in records
        if isinstance(record, dict)
        and record.get("external") is True
        and record.get("status") == "completed"
        and parse_iso_date(record.get("performed_on")) is not None
        and record_sequence(record) is not None
        and bool(record.get("public_summary", "").strip())
        and bool(record.get("evidence_files"))
    ]
    evidence_state = pilot.get("evidence_state", "")
    no_evidence_state = "No external pilot session has been completed or recorded."
    if completed_external_records:
        latest_external = max(
            completed_external_records,
            key=lambda record: record_sequence(record) or 0,
        )
        required_summary_tokens = [
            str(latest_external.get("id", "")),
            f"sequence {latest_external.get('sequence', '')}",
            str(latest_external.get("performed_on", "")),
            str(latest_external.get("stage", "")),
            str(latest_external.get("hypothesis_id", "")),
            str(latest_external.get("case_id", "")),
            str(latest_external.get("task_id", "")),
        ]
        if latest_external.get("disposition"):
            required_summary_tokens.append(str(latest_external["disposition"]))
        check(
            all(token and token in evidence_state for token in required_summary_tokens),
            "pilot evidence_state must summarize the latest completed external record",
        )
        check(
            no_evidence_state.lower() not in evidence_state.lower(),
            "pilot evidence_state must not claim that no session exists after completed evidence",
        )
    else:
        check(
            evidence_state == no_evidence_state,
            "pilot evidence_state must use the exact no-session state without completed evidence",
        )
    latest_discovery = latest_primary_disposition(pilot)
    required_primary_status = expected_primary_status(pilot)
    primary_hypothesis = hypotheses_by_id.get(pilot.get("primary_hypothesis_id"), {})
    check(
        primary_hypothesis.get("status") == required_primary_status,
        "CH-001 status must follow the canonical pilot evidence lifecycle",
    )
    if required_primary_status != "unvalidated":
        hypothesis_sources = {
            item.get("source")
            for item in primary_hypothesis.get("evidence", [])
            if isinstance(item, dict)
        }
        pilot_evidence_files = {
            path
            for record in primary_dispositions(pilot) + second_projects + completed_returns
            for path in record.get("evidence_files", [])
        }
        check(
            bool(hypothesis_sources & pilot_evidence_files),
            "CH-001 status evidence must link a canonical pilot evidence file",
        )
    if pilot.get("status") in {"discovery_complete", "stopped", "mvp_validated"}:
        check(bool(completed_discovery),
              "a closed discovery status requires completed external discovery evidence")
    required_pilot_status = expected_pilot_status(pilot)
    if required_pilot_status:
        check(
            pilot.get("status") == required_pilot_status,
            "pilot status must match the ordered CH-001 evidence lifecycle",
        )
    else:
        check(
            pilot.get("status") in {"inactive", "recruiting", "discovery_active"},
            "pilot cannot be closed without completed CH-001 discovery evidence",
        )
    for key in ("protocol_source", "intake_surface"):
        path = pilot_model.get(key)
        check(isinstance(path, str) and bool(path), f"pilot.{key} is required")
        if isinstance(path, str) and path:
            check((ROOT / path).exists(), f"pilot.{key} does not exist: {path}")
    intake_path = ROOT / str(pilot_model.get("intake_surface", ""))
    if intake_path.exists():
        intake_text = intake_path.read_text(encoding="utf-8")
        for required_intake_text in (
            "qualification signals only",
            "live funds",
            "explicitly authorized by me",
            "build/change/stop/pending",
        ):
            check(
                required_intake_text in intake_text,
                f"pilot intake is missing safety text: {required_intake_text}",
            )

    position = model.get("competitive_position", {})
    check(
        "general autonomous mathematician" in position.get("not_a", []),
        "competitive boundary must reject the autonomous-mathematician claim",
    )
    check(
        "Lean kernel checks declared formal statements" in position.get("verifier_policy", "")
        and "does not establish semantic faithfulness" in position.get("verifier_policy", ""),
        "verifier policy must state the Lean scope and semantic limitation",
    )

    policy = model.get("public_claim_policy", {})
    check(len(policy.get("required", [])) >= 5, "public claim policy needs required claims")
    check(len(policy.get("forbidden", [])) >= 5, "public claim policy needs forbidden claims")
    check(
        any("finished autonomous research engine" in item for item in policy.get("forbidden", [])),
        "public claim policy must forbid the finished autonomous-engine claim",
    )

    surfaces = {item.get("path"): item for item in model.get("site_surfaces", [])}
    for path in ("index.html", "results.html", "dashboard.html", "explore.html", "pilot.html"):
        check(path in surfaces, f"site surface is missing: {path}")

    if errors:
        print("product model check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(
        "product model check OK: "
        f"{len(workflow)} workflow stages, "
        f"{len(stage['capabilities_now'])} evidenced capabilities, "
        f"{sum(item.get('status') == 'unvalidated' for item in hypotheses)} unvalidated customer hypotheses, "
        f"pilot {pilot['status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
