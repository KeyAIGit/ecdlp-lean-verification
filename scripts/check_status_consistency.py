#!/usr/bin/env python3
"""Check Research OS truth-layer consistency.

This is a cheap, dependency-free gate for the non-Lean operating layer. It does
not prove mathematical claims; it catches drift between generated machine views,
the canonical status page, the public HTML counters, and the active work files.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from pilot_evidence import task_012_unlocked

ROOT = Path(__file__).resolve().parent.parent


def read_text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def read_json(path: str) -> dict:
    return json.loads(read_text(path))


def relative_luminance(hex_color: str) -> float:
    channels = [int(hex_color[index:index + 2], 16) / 255 for index in (1, 3, 5)]
    linear = [
        value / 12.92 if value <= 0.04045 else ((value + 0.055) / 1.055) ** 2.4
        for value in channels
    ]
    return 0.2126 * linear[0] + 0.7152 * linear[1] + 0.0722 * linear[2]


def contrast_ratio(foreground: str, background: str) -> float:
    lighter, darker = sorted(
        (relative_luminance(foreground), relative_luminance(background)),
        reverse=True,
    )
    return (lighter + 0.05) / (darker + 0.05)


def css_hex_variable(stylesheet: str, name: str) -> str | None:
    match = re.search(rf"{re.escape(name)}:\s*(#[0-9a-fA-F]{{6}})\s*;", stylesheet)
    return match.group(1) if match else None


def main() -> int:
    errors: list[str] = []

    def check(condition: bool, message: str) -> None:
        if not condition:
            errors.append(message)

    stats = read_json("data/stats.json")
    verified_index = read_json("data/verified_index.json")
    frontier = read_json("data/frontier_map.json")
    graph = read_json("data/knowledge_graph.json")
    decisions = read_json("repo/ECDLP_DECISION_SUBSTRATE.json")
    typed_evidence = read_json("data/typed_evidence_state.json")
    engine = read_json("data/research_engine_state.json")
    hypothesis_space_runs = read_json("data/hypothesis_space_run_state.json")
    product = read_json("repo/PRODUCT_MODEL.json")
    pilot_protocol = read_json("repo/PILOT_PROTOCOL.json")
    status = read_text("STATUS.md")
    knowledge_graph_md = read_text("data/knowledge_graph.md")
    decision_view = read_text("repo/ECDLP_DECISION_SUBSTRATE.md")
    index = read_text("index.html")
    results = read_text("results.html")
    dashboard = read_text("dashboard.html")
    explore = read_text("explore.html")
    pilot = read_text("pilot.html")
    tasks = read_text("tasks/NEXT.md")
    research_tasks = read_text("tasks/ECDLP_RESEARCH.md")
    rh_tasks = read_text("tasks/RIEMANN_HYPOTHESIS.md")
    product_tasks = read_text("tasks/KEYAI_PRODUCT.md")
    hypotheses = read_text("experiments/HYPOTHESES.yaml")
    autonomy = read_text("AUTONOMY.md")
    agents = read_text("AGENTS.md")
    architecture = read_text("REPOSITORY_ARCHITECTURE.md")
    site_css = read_text("assets/site.css")
    autonomous_workflow = read_text(".github/workflows/autonomous-engine.yml")
    ci_workflow = read_text(".github/workflows/ci.yml")

    ledger_rows = stats.get("ledger_rows")
    distinct = stats.get("distinct_results")
    proved_modules = stats.get("proved_modules")
    sorry_count = stats.get("sorry_count")
    custom_axioms = stats.get("custom_axioms")
    corpus_claims = frontier.get("meta", {}).get("corpus_claims")
    frontier_rows = frontier.get("meta", {}).get("verified_ledger_rows")
    status_summary = frontier.get("status_summary", {})
    route_selection = decisions.get("route_selection", {})
    authorization = decisions.get("bounded_experiment_authorization", {})
    authorization_id = authorization.get("authorization_id")

    check(isinstance(ledger_rows, int) and ledger_rows > 0,
          "data/stats.json must expose a positive integer ledger_rows")
    check(isinstance(distinct, int) and distinct > 0,
          "data/stats.json must expose a positive integer distinct_results")
    check(frontier_rows == ledger_rows,
          "frontier_map.meta.verified_ledger_rows must match stats.ledger_rows")
    check(sum(int(v) for v in status_summary.values()) == corpus_claims,
          "frontier_map.status_summary must sum to meta.corpus_claims")

    check(f"| ledger rows | **{ledger_rows}**" in status,
          "STATUS.md ledger row does not match data/stats.json")
    check(f"| distinct results | **~{distinct}**" in status,
          "STATUS.md distinct-results row does not match data/stats.json")
    check(f"| proved modules | **{proved_modules}**" in status,
          "STATUS.md proved-modules row does not match data/stats.json")
    check(f"| `sorry` | **{sorry_count}**" in status,
          "STATUS.md sorry row does not match data/stats.json")
    check(f"| custom axioms | **{custom_axioms}**" in status,
          "STATUS.md custom-axioms row does not match data/stats.json")

    for name, value in status_summary.items():
        check(f"| {name} | **{value}**" in status,
              f"STATUS.md corpus row for {name!r} does not match frontier_map")

    check(
        f"**Category:** {product.get('category')}." in status,
        "STATUS.md must expose the canonical product category",
    )
    check(
        f"**Current stage:** {product.get('current_stage', {}).get('label')}." in status,
        "STATUS.md must expose the canonical product stage",
    )
    check(
        product.get("mvp", {}).get("definition") in status,
        "STATUS.md must expose the canonical MVP boundary",
    )
    check(
        pilot_protocol.get("id") in status
        and pilot_protocol.get("status") in status
        and pilot_protocol.get("evidence_state") in status,
        "STATUS.md must expose the canonical pilot state",
    )

    check(
        f'data-metric="ledger-rows">{ledger_rows}</strong>' in index,
        "index.html ledger counter does not match data/stats.json",
    )
    check(
        f'data-metric="distinct-results">~{distinct}</strong>' in index,
        "index.html distinct-results counter does not match data/stats.json",
    )
    verified_counts = verified_index.get("counts", {})
    check(
        verified_counts.get("ecdlp_rows") == ledger_rows,
        "verified_index ECDLP rows must match data/stats.json",
    )
    check(
        verified_counts.get("researchos_rows")
        == read_json("data/researchos_result_registry.json").get("ledger_rows"),
        "verified_index ResearchOS rows must match its isolated registry",
    )
    check(
        verified_counts.get("navigation_rows_total")
        == verified_counts.get("ecdlp_rows", 0) + verified_counts.get("researchos_rows", 0),
        "verified_index navigation total must be the sum of the two isolated lanes",
    )
    check(
        f'{verified_counts.get("navigation_rows_total")} results' in results
        and 'data-result-list' in results
        and 'data-result-count aria-live="polite"' in results,
        "results.html must expose the complete static result list and accessible filters",
    )
    check(
        "One browser, two isolated ledgers" in results
        and "not an ECDLP security metric" in results,
        "results.html must expose the cross-lane accounting boundary",
    )
    rh_rows = verified_counts.get("domains", {}).get("riemann-hypothesis", 0)
    check(
        f"The {rh_rows} ResearchOS rows in this domain" in results
        and "no proof candidate, and no progress on RH itself" in results
        and "Ledger scope" in results
        and "proves neither side" in results,
        "results.html must retain the canonical RH no-progress boundary and per-row scope",
    )
    check(f"snapshot {ledger_rows} ledger rows / ~{distinct} distinct" in dashboard,
          "dashboard.html snapshot stamp does not match data/stats.json")
    check(
        f'data-metric="ledger-rows">{ledger_rows}</span>' in explore,
        "explore.html ledger counter does not match data/stats.json",
    )
    check("Sync Health" in dashboard,
          "dashboard.html must expose a Sync Health section")
    check(
        "Work queues" in dashboard
        and "tasks/NEXT.md" in dashboard
        and "tasks/ECDLP_RESEARCH.md" in dashboard
        and "tasks/KEYAI_PRODUCT.md" in dashboard,
        "dashboard must expose the queue router and both owning queues",
    )
    check("repo/ARTIFACTS.yaml" in dashboard and "scripts/check_repo_artifacts.py" in dashboard,
          "dashboard.html Sync Health must link the artifact manifest to its gate")
    check(
        product.get("category") in index
        and product.get("category") in results
        and product.get("category") in dashboard
        and product.get("category") in explore
        and product.get("category") in pilot,
        "all public surfaces must expose the canonical product category",
    )
    check(
        product.get("current_stage", {}).get("label") in index
        and product.get("current_stage", {}).get("label") in dashboard,
        "index and dashboard must expose the canonical product stage",
    )
    check(
        "repo/PRODUCT_MODEL.json" in index
        and "repo/PRODUCT_MODEL.json" in results
        and "repo/PRODUCT_MODEL.json" in dashboard
        and "repo/PRODUCT_MODEL.json" in explore
        and "repo/PRODUCT_MODEL.json" in pilot,
        "all public surfaces must link the canonical product model",
    )
    check(
        all("assets/site.css" in page and "assets/site.js" in page
            for page in (index, results, dashboard, explore, pilot)),
        "all public surfaces must use the shared site assets",
    )
    check(
        all(
            "The Lean kernel checks declared statements and proof terms" in page
            for page in (index, results, dashboard, explore, pilot)
        ),
        "all public surfaces must expose the verifier-scope caveat",
    )
    check(
        pilot_protocol.get("task_id") in pilot
        and pilot_protocol.get("status", "").title() in pilot
        and pilot_protocol.get("evidence_state") in pilot,
        "pilot.html must expose the canonical task, status, and evidence state",
    )
    intake_template = Path(product.get("pilot", {}).get("intake_surface", "")).name
    intake_url = (
        f"{product.get('repository_url', '').rstrip('/')}/issues/new?template={intake_template}"
    )
    check(
        bool(intake_template)
        and intake_url in index
        and intake_url in pilot,
        "product and pilot pages must derive the public intake URL from PRODUCT_MODEL.json",
    )
    check(
        'data-route-count aria-live="polite"' in explore
        and 'data-route-empty role="status" aria-live="polite"' in explore,
        "route result changes must be announced to assistive technology",
    )
    public_site = (index + results + dashboard + explore + pilot).lower()
    for retired_claim in (
        "autonomous engine",
        "verified environment for a strong ai",
        "turn ai research into verified, reusable state",
        "source material to verified asset",
    ):
        check(
            retired_claim not in public_site,
            f"public site contains retired product claim: {retired_claim!r}",
        )
    route_count = len(decisions.get("routes", []))
    selected_structural = route_selection.get("selected_route_ids", [])
    promoted_routes = route_selection.get("promoted_route_ids", [])
    selected_explorations = engine.get("counts", {}).get("selected_explorations")
    generated_hypothesis_seeds = engine.get("counts", {}).get(
        "generated_hypothesis_seeds"
    )
    typed_evidence_cells = engine.get("counts", {}).get("typed_evidence_cells")
    typed_decided_cells = engine.get("counts", {}).get("typed_decided_cells")
    typed_seed_eligible_cells = engine.get("counts", {}).get(
        "typed_seed_eligible_cells"
    )
    typed_desk_decisions = engine.get("counts", {}).get("typed_desk_decisions")
    check(
        f"{route_count} canonical routes" in dashboard,
        "dashboard route count must match the decision substrate",
    )
    check(
        f'data-route-count aria-live="polite">{route_count} routes' in explore,
        "explore route count must match the decision substrate",
    )
    check(
        route_selection.get("decision_id") in dashboard
        and route_selection.get("decision_id") in explore
        and "Structural selection" in dashboard
        and "Structural selection" in explore,
        "dashboard and explore must expose the canonical structural decision",
    )
    check(
        f'data-metric="native-experiments">{selected_explorations}</strong> native experiments selected' in index
        and f"{selected_explorations} selected;" in dashboard
        and f"{len(selected_structural)} structural route completed" in explore
        and f"{len(promoted_routes)} promoted" in explore
        and "1 exact synthetic-toy run completed" in explore
        and "0 native experiments selected" in explore,
        "public reference views must distinguish the exact singleton from the "
        "empty native exploration queue",
    )
    check(
        "One hash-bound synthetic-toy diagnostic completed." in dashboard
        and "Native queue closed" in dashboard
        and authorization_id in dashboard
        and "repo/RESEARCH_ENGINE_V0.json" in dashboard
        and "repo/HYPOTHESIS_GENERATION_V0.json" in dashboard
        and "Native decision exploration" in dashboard
        and "Promotion experiments" in dashboard,
        "dashboard must distinguish the exact singleton, native exploration, "
        "and promotion gates",
    )
    check(
        f"**{generated_hypothesis_seeds} source-grounded seeds**" in status
        and f"{generated_hypothesis_seeds} seed-eligible questions;" in dashboard,
        "status and dashboard must expose the generated hypothesis-seed count",
    )
    check(
        f"**{typed_evidence_cells} mechanism/property cells**" in status
        and f"**{typed_decided_cells} decided at desk**" in status
        and f"**{typed_seed_eligible_cells} eligible to emit a bounded research question**"
        in status
        and f"**{typed_desk_decisions} desk decisions**" in status,
        "STATUS.md must expose typed evidence and zero-cost desk-decision counts",
    )
    check(
        f"{typed_evidence_cells} mechanism/property cells;" in dashboard
        and f"{typed_decided_cells} decided at desk;" in dashboard,
        "dashboard must expose typed evidence and desk-decision counts",
    )

    graph_counts = graph.get("counts", {})
    check(isinstance(graph_counts.get("theorems"), int) and graph_counts["theorems"] > 0,
          "data/knowledge_graph.json must expose counts.theorems")
    check(graph_counts.get("ledger_rows") == ledger_rows,
          "data/knowledge_graph.json counts.ledger_rows must match data/stats.json")
    check(graph_counts.get("families") == 8,
          "data/knowledge_graph.json must expose the exhaustive eight-family partition")
    check(graph_counts.get("critical_nodes", 0) > 0,
          "data/knowledge_graph.json must expose formal critical-path nodes")
    check(graph_counts.get("attack_routes") == 17,
          "data/knowledge_graph.json must expose all 17 decision routes")
    check(
        graph_counts.get("decision_foundations")
        == len(decisions.get("foundations", [])),
        "data/knowledge_graph.json foundation count must match the decision substrate",
    )
    check(
        graph_counts.get("selected_structural_routes") == len(selected_structural)
        and graph_counts.get("promoted_routes") == len(promoted_routes),
        "knowledge graph structural and promotion counts must match route selection",
    )
    check(
        graph_counts.get("research_engine_candidates")
        == engine.get("counts", {}).get("candidate_proposals"),
        "knowledge graph candidate count must match research_engine_state.json",
    )
    check(
        graph_counts.get("generated_hypothesis_seeds")
        == generated_hypothesis_seeds,
        "knowledge graph generated-seed count must match research_engine_state.json",
    )
    check(
        graph_counts.get("typed_evidence_cells") == typed_evidence_cells
        and graph_counts.get("typed_decided_cells") == typed_decided_cells
        and graph_counts.get("typed_seed_eligible_cells")
        == typed_seed_eligible_cells
        and graph_counts.get("typed_desk_decisions") == typed_desk_decisions,
        "knowledge graph typed-evidence counts must match research_engine_state.json",
    )
    check(
        graph_counts.get("research_engine_outcomes")
        == engine.get("counts", {}).get("outcome_events"),
        "knowledge graph outcome count must match research_engine_state.json",
    )
    check(
        graph_counts.get("hypothesis_space_run_records")
        == hypothesis_space_runs.get("counts", {}).get("runs")
        and graph_counts.get("hypothesis_space_distinct_roots")
        == hypothesis_space_runs.get("counts", {}).get("distinct_instance_roots")
        and graph_counts.get("hypothesis_space_operational_errors")
        == hypothesis_space_runs.get("counts", {}).get("pipeline_errors", 0)
        + hypothesis_space_runs.get("counts", {}).get("invariant_violations", 0),
        "knowledge graph hypothesis-space run memory must match its generated state",
    )
    check(
        graph_counts.get("selected_explorations")
        == engine.get("counts", {}).get("selected_explorations"),
        "knowledge graph selected exploration count must match research_engine_state.json",
    )
    check(
        graph_counts.get("decision_level_bounded_authorizations") == 1,
        "knowledge graph must expose exactly one decision-level authorization",
    )
    check(graph.get("schema_version") == "4.0",
          "data/knowledge_graph.json must use Research Engine-aware schema 4.0")
    check(
        graph.get("decision_substrate", {}).get("route_selection") == route_selection,
        "knowledge graph route selection must match ECDLP_DECISION_SUBSTRATE.json",
    )
    check(
        graph.get("decision_substrate", {}).get(
            "bounded_experiment_authorization"
        )
        == authorization,
        "knowledge graph bounded authorization must match the decision substrate",
    )
    graph_engine = graph.get("research_engine", {})
    check(
        graph_engine.get("gate_status") == engine.get("gate_status")
        and graph_engine.get("selected_sequence") == engine.get("selected_sequence")
        and graph_engine.get("execution_queue") == engine.get("execution_queue")
        and graph_engine.get("outcome_events") == engine.get("outcome_events"),
        "knowledge graph Research Engine view must match generated engine state",
    )
    check(
        graph_engine.get("hypothesis_generation")
        == engine.get("hypothesis_generation"),
        "knowledge graph hypothesis-generation view must match engine state",
    )
    check(
        graph.get("hypothesis_space", {}).get("run_memory", {}).get("counts")
        == hypothesis_space_runs.get("counts"),
        "knowledge graph run-memory view must match hypothesis_space_run_state.json",
    )
    check(
        f"{hypothesis_space_runs.get('counts', {}).get('runs', 0)} immutable"
        in status,
        "STATUS.md must expose the immutable hypothesis-space run count",
    )
    graph_typed = graph.get("typed_evidence", {})
    expected_cell_index = [
        {
            "cell_id": cell["cell_id"],
            "mechanism_id": cell["mechanism_id"],
            "route_id": cell["route_id"],
            "status": cell["status"],
            "cost_quantity_id": cell["cost_quantity_id"],
            "requirement_results": cell["requirement_results"],
            "seed_eligible": cell["seed_eligible"],
            "evidence_digest": cell["evidence_digest"],
            "authorization": cell["authorization"],
        }
        for cell in typed_evidence.get("cells", [])
    ]
    check(
        graph_typed.get("counts") == typed_evidence.get("counts")
        and graph_typed.get("cell_index") == expected_cell_index,
        "knowledge graph typed-evidence view must match typed evidence state",
    )
    check(
        engine.get("gate_status", {}).get("exploration_authorized")
        == True
        and engine.get("gate_status", {}).get(
            "current_decision_experiment_authorized"
        )
        == False
        and decisions.get("phase_policy", {}).get(
            "experiments_authorized"
        )
        == False
        and decisions.get("phase_policy", {}).get(
            "bounded_exploration_authorized"
        )
        == False
        and engine.get("gate_status", {}).get("promotion_authorized")
        == decisions.get("phase_policy", {}).get(
            "promotion_experiments_authorized"
        )
        == False,
        "the Engine capability, exact decision singleton, closed native "
        "decision queue, and closed promotion gate must remain distinct",
    )
    check(
        route_selection.get("decision_id") in status,
        "STATUS.md must expose the current route-selection decision",
    )
    check(
        isinstance(authorization_id, str)
        and authorization_id in status
        and authorization_id in decision_view
        and authorization_id in knowledge_graph_md
        and authorization_id in index
        and authorization_id in dashboard
        and authorization_id in explore,
        "all generated decision surfaces must expose the exact singleton id",
    )
    check(
        authorization.get("hypothesis_id") in status
        and authorization.get("task_id") in status
        and authorization.get("source_commit") in status
        and str(
            authorization.get("resource_budget", {}).get(
                "max_primary_trials"
            )
        )
        in status
        and "Real-world and secp256k1" in status,
        "STATUS.md must expose singleton identity, source, budget, and safety scope",
    )
    check(
        "Exact decision experiment authorized: **false**" in decision_view
        and "Native bounded exploration authorized: **false**"
        in decision_view
        and "Promotion experiments authorized: **false**" in decision_view
        and "**Promotion authorized:** **false**" in decision_view,
        "decision view must separate singleton, native, and promotion gates",
    )
    edge_types = graph_counts.get("by_edge_type", {})
    for edge_type in (
        "imports",
        "member_of",
        "supports",
        "depends_on",
        "blocked_by",
        "evaluated_under",
        "detailed_by",
        "requires_foundation",
        "decision_grounded_in",
        "governs_hypothesis",
        "extends_frontier",
        "tests_hypothesis",
        "explores_route",
        "depends_on_candidate",
        "records_outcome_for",
        "updates_hypothesis",
        "records_route_evidence",
        "binds_target_feature",
        "binds_mechanism_primitive",
        "binds_unresolved_question",
        "generated_from_cell",
        "follows_up_cell",
        "follows_up_source",
    ):
        check(edge_types.get(edge_type, 0) > 0,
              f"knowledge graph is missing semantic edge type {edge_type!r}")
    cells = {
        item["cell_id"]
        for item in graph.get("typed_evidence", {}).get("cell_index", [])
    }
    seeds = {
        item["seed_id"]
        for item in graph.get("research_engine", {})
        .get("hypothesis_generation", {})
        .get("generated_seeds", [])
    }
    stubs = {
        item["stub_id"]
        for item in graph.get("research_shadow_intake", {}).get(
            "proposal_stubs", []
        )
    }
    source_ids = {
        item["id"]
        for item in graph.get("source_index", {}).get("sources", [])
    }
    axis_index = graph.get("hypothesis_axis_index", {})
    axis_targets = {
        "binds_target_feature": {
            item["id"] for item in axis_index.get("target_features", [])
        },
        "binds_mechanism_primitive": {
            item["id"] for item in axis_index.get("mechanism_primitives", [])
        },
        "binds_unresolved_question": {
            item["id"] for item in axis_index.get("unresolved_questions", [])
        },
    }
    endpoint_contracts = {
        "binds_target_feature": (cells, axis_targets["binds_target_feature"]),
        "binds_mechanism_primitive": (
            cells,
            axis_targets["binds_mechanism_primitive"],
        ),
        "binds_unresolved_question": (
            cells,
            axis_targets["binds_unresolved_question"],
        ),
        "generated_from_cell": (seeds, cells),
        "follows_up_cell": (stubs, cells),
        "follows_up_source": (stubs, source_ids),
    }
    for edge in graph.get("edges", []):
        edge_type = edge.get("type")
        if edge_type not in endpoint_contracts:
            continue
        valid_sources, valid_targets = endpoint_contracts[edge_type]
        check(
            edge.get("from") in valid_sources,
            f"{edge_type} edge has unresolved source {edge.get('from')!r}",
        )
        check(
            edge.get("to") in valid_targets,
            f"{edge_type} edge has unresolved target {edge.get('to')!r}",
        )
    check(graph.get("invariant", "").lower().find("lean kernel") >= 0,
          "data/knowledge_graph.json invariant should mention the Lean kernel")
    check(
        "## Finite hypothesis-space projection" in knowledge_graph_md
        and "not a claim that every possible ECDLP idea has been enumerated"
        in knowledge_graph_md,
        "rendered knowledge graph must expose the bounded hypothesis-space projection",
    )

    check("Task contract template" in tasks,
          "tasks/NEXT.md must include the task contract template")
    queue_specs = (
        ("ECDLP", research_tasks, r"^### TASK-\d+\b"),
        ("RH", rh_tasks, r"^## RH-\d+\b"),
        ("product", product_tasks, r"^### TASK-\d+\b"),
    )
    active_task_count = 0
    active_rh_contracts: list[tuple[str, str]] = []
    for queue_name, queue_text, heading_pattern in queue_specs:
        sections = re.findall(
            rf"{heading_pattern}.*?(?={heading_pattern}|\Z)",
            queue_text,
            flags=re.MULTILINE | re.DOTALL,
        )
        check(bool(sections), f"{queue_name} queue must contain task contracts")
        for section in sections:
            heading = section.splitlines()[0]
            status_lines = re.findall(
                r"^Status:\s*(.+?)\s*$", section, flags=re.MULTILINE
            )
            check(
                len(status_lines) == 1,
                f"{heading} must contain exactly one Status line",
            )
            if len(status_lines) != 1:
                continue
            task_status = re.sub(r"[*`]", "", status_lines[0]).strip()
            if task_status.lower().startswith(("active", "maintenance")):
                active_task_count += 1
            if queue_name == "RH" and task_status.upper().startswith("ACTIVE"):
                task_match = re.match(r"^## (RH-\d+)(?::\s*(.*))?$", heading)
                if task_match is not None:
                    active_rh_contracts.append(
                        (task_match.group(1), (task_match.group(2) or "").strip())
                    )
    check(3 <= active_task_count <= 7,
          "the three owning queues must keep 3-7 actionable task contracts in total")
    check(
        len(active_rh_contracts) == 1,
        "the RH queue must contain exactly one ACTIVE contract",
    )
    check(
        "tasks/ECDLP_RESEARCH.md" in tasks
        and "tasks/RIEMANN_HYPOTHESIS.md" in tasks
        and "tasks/KEYAI_PRODUCT.md" in tasks
        and "Product work never counts as ECDLP progress" in tasks,
        "tasks/NEXT.md must route to separate RH, ECDLP, and product queues",
    )
    check(
        "Current ECDLP decision:" in tasks
        and "Current central decision:" not in tasks,
        "tasks/NEXT.md must scope the legacy M16 decision to ECDLP",
    )
    if len(active_rh_contracts) == 1:
        active_rh_id, active_rh_title = active_rh_contracts[0]
        check(
            f"`{active_rh_id}`**: {active_rh_title}" in status
            and "tasks/RIEMANN_HYPOTHESIS.md" in status,
            "STATUS.md must derive its RH priority from the active queue contract",
        )
    startup_block = agents.split("## What this project actually is", 1)[0]
    check(
        "For a small-context start" in startup_block
        and "domains/riemann-hypothesis/README.md" in startup_block
        and "domains/riemann-hypothesis/corpus.md" in startup_block
        and "tasks/RIEMANN_HYPOTHESIS.md" in startup_block
        and "choose exactly one" in startup_block
        and "tasks/RIEMANN_HYPOTHESIS.md" in autonomy
        and "three owning queues" in autonomy,
        "agent control documents must route RH work through its isolated queue",
    )
    check("canonical_source: STATUS.md" in hypotheses,
          "experiments/HYPOTHESES.yaml must point at STATUS.md")
    check("task_queue: tasks/ECDLP_RESEARCH.md" in hypotheses,
          "experiments/HYPOTHESES.yaml must point at the ECDLP research queue")
    check(len(re.findall(r"^  - id: H", hypotheses, flags=re.MULTILINE)) >= 3,
          "experiments/HYPOTHESES.yaml must define at least three hypotheses")
    check('status: "parked"' in hypotheses and "resume_after:" in hypotheses,
          "deferred experiments must be parked with an explicit resume condition")
    check("Never use `git reset --hard`" in autonomy,
          "AUTONOMY.md must explicitly forbid destructive branch resets")
    check("Reset branch to `main`" not in agents,
          "AGENTS.md must not prescribe ambiguous branch resets")
    check(
        "repo/PILOT_PROTOCOL.json" in agents
        and "`build/change/stop/pending`" in agents
        and re.search(r"does not validate\s+the\s+adapter", agents) is not None,
        "AGENTS.md must expose the canonical TASK-011 discovery boundary",
    )
    check(
        "on-demand autonomous cycle" in autonomy
        and "repository itself has no recurring scheduler" in autonomy
        and "workflow_dispatch:" in autonomous_workflow
        and "\n  schedule:" not in autonomous_workflow,
        "autonomy documentation must match the dispatch-only autonomous workflow",
    )
    check(
        "${{ secrets." not in ci_workflow,
        "ordinary push/PR verification CI must not receive repository secrets",
    )
    secret_auto_triggers: list[str] = []
    for workflow_path in sorted((ROOT / ".github" / "workflows").glob("*.yml")):
        workflow_text = workflow_path.read_text(encoding="utf-8")
        if "${{ secrets." not in workflow_text:
            continue
        if re.search(
            r"^  (?:push|pull_request|pull_request_target|schedule):",
            workflow_text,
            flags=re.MULTILINE,
        ):
            secret_auto_triggers.append(workflow_path.name)
    check(
        not secret_auto_triggers,
        "secret-bearing workflows must remain manual-only: "
        + ", ".join(secret_auto_triggers),
    )
    check(
        "only open PRs in this repository" in autonomy
        and "Never act on another repository" in autonomy,
        "autonomous PR reconciliation must remain scoped to this repository",
    )
    check(
        "repo/PILOT_PROTOCOL.json" in architecture
        and "pilot.html" in architecture
        and "results.html" in architecture
        and "Generate all five pages" in architecture,
        "repository architecture must map the pilot protocol and all five public surfaces",
    )
    task_012_match = re.search(
        r"^### TASK-012\b.*?^Status:\s*([^\n]+)",
        product_tasks,
        flags=re.MULTILINE | re.DOTALL,
    )
    task_012_status = task_012_match.group(1).strip() if task_012_match else None
    check(
        task_012_match is not None,
        "tasks/KEYAI_PRODUCT.md must retain a TASK-012 contract",
    )
    if task_012_unlocked(pilot_protocol):
        check(
            task_012_status in {"active", "done", "completed"},
            "TASK-012 must have an explicit actionable or completed status after the "
            "latest primary build disposition",
        )
    else:
        check(
            task_012_status == "blocked_on_task_011_build_disposition"
            and "completed `TASK-011` discovery record with a `build` disposition"
            in product_tasks,
            "TASK-012 must remain explicitly blocked unless the latest primary "
            "discovery disposition is build",
        )
    blue = css_hex_variable(site_css, "--blue")
    quiet = css_hex_variable(site_css, "--quiet")
    check(
        blue is not None and contrast_ratio(blue, "#ffffff") >= 4.5,
        "primary blue must meet WCAG AA contrast against white text",
    )
    check(
        quiet is not None and contrast_ratio(quiet, "#e9eef1") >= 4.5,
        "quiet text must meet WCAG AA contrast on muted surfaces",
    )

    if errors:
        print("Research OS consistency check failed:")
        for error in errors:
            print(f"- {error}")
        return 1

    print(
        "Research OS consistency OK: "
        f"{ledger_rows} ledger rows / ~{distinct} distinct; "
        f"{corpus_claims} corpus claims; "
        f"{graph_counts['ledger_rows']} graph ledger-row nodes"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
