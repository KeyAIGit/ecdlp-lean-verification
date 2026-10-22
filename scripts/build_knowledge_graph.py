#!/usr/bin/env python3
"""Build the machine-readable ECDLP knowledge graph.

Emits `data/knowledge_graph.json`: a navigable, structured index that links every
verified ledger row to (a) the knowledge-graph claim it supports, (b) the Lean
files and import dependencies it rests on, and (c) the formalization barriers that
bound what is provable. The intent (see the project north star) is a verified,
navigable substrate a future automated reasoner can load to understand the *known
and machine-checked* structure of the ECDLP landscape — proofs, dependencies, and
the precise foundations still missing — without re-deriving any of it.

This script READS the human-maintained sources of truth and DERIVES the graph; it
never asserts a proof. The Lean kernel remains the only judge of correctness.

Sources of truth (read-only):
  - VERIFIED.md                      — ledger of verified results (the nodes)
  - Ecdlp/*.lean, Ecdlp/Proved/*.lean — Lean sources (import dependency edges)
  - Ecdlp.lean                       — the built import surface (what is gated)
  - BARRIERS.md                      — the no-go / missing-foundation map
  - data/KG_CLAIM_FORMALIZATION_v1.csv — the 486-claim corpus (claim metadata)

Usage:  python3 scripts/build_knowledge_graph.py [--check]
  --check : build in memory and fail (nonzero exit) if it diverges from the
            committed data/knowledge_graph.json (for CI drift detection).
"""
from __future__ import annotations

import csv
import json
import re
import sys
from collections import Counter
from pathlib import Path

from ledger_utils import parse_ledger as parse_verified_ledger

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "data" / "knowledge_graph.json"
SUBSTRATE = ROOT / "repo" / "FORMAL_SUBSTRATE.json"
DECISION_SUBSTRATE = ROOT / "repo" / "ECDLP_DECISION_SUBSTRATE.json"
ATTACK_REGISTRY = ROOT / "data" / "attack_registry.json"
RESEARCH_ENGINE_POLICY = ROOT / "repo" / "RESEARCH_ENGINE_V0.json"
RESEARCH_ENGINE_STATE = ROOT / "data" / "research_engine_state.json"
RESEARCH_ENGINE_V02_STATE = ROOT / "data" / "research_engine_v02_state.json"
RESEARCH_SHADOW_INTAKE = ROOT / "data" / "research_engine_shadow_intake.json"
TYPED_EVIDENCE_STATE = ROOT / "data" / "typed_evidence_state.json"
HYPOTHESIS_GENERATION_POLICY = ROOT / "repo" / "HYPOTHESIS_GENERATION_V0.json"
HYPOTHESIS_SPACE_STATE = ROOT / "data" / "hypothesis_space_state.json"
HYPOTHESIS_SPACE_MAP = ROOT / "data" / "hypothesis_space_map.json"
HYPOTHESIS_SPACE_RUN_STATE = ROOT / "data" / "hypothesis_space_run_state.json"
SOURCE_REGISTRY = ROOT / "data" / "source_registry.json"


def parse_ledger() -> list[dict]:
    """Compatibility view over the shared canonical-ledger parser."""
    rows: list[dict] = []
    for row in parse_verified_ledger(ROOT):
        files = row["files"] or [row["file_cell"].strip().strip("`")]
        rows.append(
            {
                "claim": row["claim"],
                "name": row["name"],
                "file": files[0],
                "files": files,
                "method": row["method"],
                "status": row["status"],
            }
        )
    return rows


# --- parse Lean imports: file-level dependency edges ----------------------------

_IMPORT = re.compile(r"^\s*import\s+(Ecdlp[\w.]*)")


def lean_path(module: str) -> Path | None:
    rel = module.replace(".", "/") + ".lean"
    p = ROOT / rel
    return p if p.exists() else None


def stable_repo_path(path: Path, root: Path = ROOT) -> str:
    """Return a case-sensitive, platform-independent repository path key."""
    return path.relative_to(root).as_posix()


def parse_imports() -> dict[str, list[str]]:
    """module -> list of Ecdlp.* modules it imports (intra-project edges only)."""
    edges: dict[str, list[str]] = {}
    # Path ordering follows the host path flavor. WindowsPath compares names
    # case-insensitively, while PosixPath does not, so sort by a normalized string.
    lean_files = sorted(
        (
            path
            for path in ROOT.glob("Ecdlp/**/*.lean")
            if "Targets" not in path.parts
            and not path.name.endswith("AxiomAudit.lean")
        ),
        key=stable_repo_path,
    ) + [ROOT / "Ecdlp.lean"]
    for f in lean_files:
        if not f.exists():
            continue
        module = (
            f.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
        )
        deps = []
        for line in f.read_text(encoding="utf-8").splitlines():
            m = _IMPORT.match(line)
            if m and m.group(1) != module:
                deps.append(m.group(1))
        edges[module] = deps
    return edges


def file_to_module(file_field: str) -> str:
    return file_field.replace("/", ".").removesuffix(".lean")


# --- the barrier map (curated mirror of BARRIERS.md, machine-readable) ----------
# These are the foundations Mathlib lacks to formalize ECDLP cryptanalysis. Each
# is a first-class node: a precise statement of *what is missing and why*, which is
# itself the research contribution. Counts are indicative (see BARRIERS.md).

BARRIERS = [
    {
        "id": "B1-cost-model",
        "title": "No oracle / group-operation cost model in Lean",
        "missing_foundation": "a general cost / oracle-query model in Mathlib",
        "blocks": "exact Theta running times, index-calculus subexponential bounds, "
        "distinguished-point parallel speedups",
        "affected_claims_estimate": 54,
        "mathlib_area": "(not in Mathlib) complexity/cost model",
        "partial_progress": "generic-group Omega(sqrt p) lower bound and O(sqrt n) "
        "upper bounds are formalized: their information-theoretic core sidesteps a "
        "general cost model (collision count over affine forms a + b*X).",
    },
    {
        "id": "B2-lattice",
        "title": "No lattice-reduction theory in Mathlib",
        "missing_foundation": "LLL/BKZ basis reduction, CVP/SVP",
        "blocks": "hidden-number-problem / biased-nonce ECDSA attacks",
        "affected_claims_estimate": 24,
        "mathlib_area": "(not in Mathlib) lattice reduction",
        "partial_progress": None,
    },
    {
        "id": "B2-quantum",
        "title": "No quantum-circuit cost model in Mathlib",
        "missing_foundation": "quantum circuit resource model",
        "blocks": "Shor-style ECDLP resource estimates",
        "affected_claims_estimate": 38,
        "mathlib_area": "(not in Mathlib) quantum circuits",
        "partial_progress": None,
    },
    {
        "id": "B3-semaev",
        "title": "Summation / Semaev polynomials not in Mathlib",
        "missing_foundation": "elliptic summation polynomials S_n over MvPolynomial",
        "blocks": "index calculus on elliptic curves over extension fields",
        "affected_claims_estimate": 12,
        "mathlib_area": "MvPolynomial (partial)",
        "partial_progress": "Mathlib has multivariate polynomials but not the S_n.",
    },
    {
        "id": "B3-weil-pairing",
        "title": "Weil/Tate pairing and isogeny depth missing",
        "missing_foundation": "Weil pairing on EllipticCurve, isogeny machinery",
        "blocks": "MOV/FR transfer reductions to finite-field DLP",
        "affected_claims_estimate": 15,
        "mathlib_area": "EllipticCurve and DivisionPolynomial (partial prerequisites)",
        "partial_progress": "Mathlib has curve and division-polynomial prerequisites; "
        "the audited pinned/current trees have no elliptic-isogeny or pairing module.",
    },
    {
        "id": "B3-point-counting",
        "title": "Concrete point count #E(F_p) = n not kernel-computable",
        "missing_foundation": "Schoof / efficient point counting in Mathlib",
        "blocks": "deriving #E = n abstractly for the concrete curve",
        "affected_claims_estimate": 6,
        "mathlib_area": "EllipticCurve (partial)",
        "partial_progress": "the concrete order is instead pinned via native_decide / "
        "the published value; primality of n is machine-checked (Pratt).",
    },
]

# Map a ledger row to the barrier(s) it is adjacent to (verified node that lives at
# the frontier of a barrier — either a partial step into it, or its boundary).
FRONTIER = {
    "B1-cost-model": [
        "generic_dlog_query_bound",
        "generic_dlog_sqrt_bound",
        "generic_success_le",
        "bsgs_decomp",
        "pollard_rho_collision",
        "secp256k1_generic_security",
    ],
    "B3-weil-pairing": [
        "secp256k1_j_eq_zero",
        "secp256k1_embedding_degree_gt_100",
        "secp256k1_trace_ordinary_nonanomalous",
        "secp256k1_Ψ₂Sq",
        "secp256k1_Ψ₂Sq_root_of_two_torsion",
    ],
    "B3-point-counting": ["secp256k1_n_prime", "secp256k1_p_prime"],
}


# --- corpus summary -------------------------------------------------------------

def parse_corpus() -> dict:
    path = ROOT / "data" / "KG_CLAIM_FORMALIZATION_v1.csv"
    with path.open() as f:
        rows = list(csv.DictReader(f))
    status = Counter(r.get("formal_status", "") for r in rows)
    return {
        "total_claims": len(rows),
        "by_formal_status": dict(status.most_common()),
        "columns": list(rows[0].keys()) if rows else [],
        "note": "486 atomic claims. formalizable + formalizable_hard are the "
        "candidate frontier; informal_only / scope_meta are out of scope by nature.",
    }


# --- assemble -------------------------------------------------------------------

def short_name(full: str) -> str:
    """Last dotted component, for frontier matching (e.g. ...secp256k1_n_prime)."""
    return full.split()[0].split(".")[-1] if full else full


# Coarse research areas, matched by keyword against (claim + module). First hit
# wins; order matters (most specific first). Gives a future reasoner a stable
# faceting of the corpus without re-reading every statement.
AREA_RULES = [
    # Checked before "primality": the parity / Fourier rows state their
    # hypotheses with "prime n", which would otherwise file them as primality.
    ("bit-security", ["parity", "fourier", "σ̂", "halving", "ordered-sector",
                      "twisted sum"]),
    ("primality", ["prime", "pratt", "primality"]),
    ("attack-resistance", ["embedding degree", "anomalous", "trace of frobenius",
                           "supersingular", "mov", "smart"]),
    ("generic-hardness", ["generic", "shoup", "nechaev", "bsgs", "baby-step",
                          "pollard", "query bound", "sqrt", "√"]),
    ("reduction", ["pohlig", "crt", "reconstruct", "projection", "component"]),
    ("protocol-soundness", ["schnorr", "pedersen", "okamoto", "chaum", "dleq",
                            "elgamal", "diffie", "musig", "feldman", "adaptor",
                            "blind", "threshold", "vss", "eddsa"]),
    ("curve-torsion", ["division polynomial", "ψ", "torsion", "j-invariant",
                       "j =", "discriminant", "δ", "c₄", "weierstrass", "b₂",
                       "b₄", "b₆", "b₈", "elliptic", "nonsingular", "generator",
                       "eigenvalue", "cube root", "order exactly 3", "β", "λ",
                       "glv", "cofactor", "lagrange", "secp256k1verified",
                       "lambda", "beta", "lam ", "base point", "on the curve"]),
    ("params", ["p ≡", "special form", "mod four", "3 ∣", "divides"]),
]


def classify_area(claim: str, module: str) -> str:
    hay = (claim + " " + module).lower()
    for area, kws in AREA_RULES:
        if any(k in hay for k in kws):
            return area
    return "other"


def module_depth(module: str, imports: dict[str, list[str]],
                 _cache: dict[str, int] | None = None) -> int:
    """Longest intra-project import chain under `module` (0 = no project deps)."""
    if _cache is None:
        _cache = {}
    if module in _cache:
        return _cache[module]
    _cache[module] = 0  # guard against cycles
    deps = imports.get(module, [])
    depth = 0 if not deps else 1 + max(
        (module_depth(d, imports, _cache) for d in deps), default=0
    )
    _cache[module] = depth
    return depth


def build() -> dict:
    ledger = parse_ledger()
    imports = parse_imports()
    substrate = json.loads(SUBSTRATE.read_text(encoding="utf-8"))
    decisions = json.loads(DECISION_SUBSTRATE.read_text(encoding="utf-8"))
    attack_registry = json.loads(ATTACK_REGISTRY.read_text(encoding="utf-8"))
    engine_policy = json.loads(RESEARCH_ENGINE_POLICY.read_text(encoding="utf-8"))
    engine = json.loads(RESEARCH_ENGINE_STATE.read_text(encoding="utf-8"))
    engine_v02 = json.loads(
        RESEARCH_ENGINE_V02_STATE.read_text(encoding="utf-8")
    )
    shadow_intake = json.loads(
        RESEARCH_SHADOW_INTAKE.read_text(encoding="utf-8")
    )
    typed_evidence = json.loads(TYPED_EVIDENCE_STATE.read_text(encoding="utf-8"))
    generation_policy = json.loads(
        HYPOTHESIS_GENERATION_POLICY.read_text(encoding="utf-8")
    )
    hypothesis_space = json.loads(
        HYPOTHESIS_SPACE_STATE.read_text(encoding="utf-8")
    )
    hypothesis_map = json.loads(HYPOTHESIS_SPACE_MAP.read_text(encoding="utf-8"))
    hypothesis_space_runs = json.loads(
        HYPOTHESIS_SPACE_RUN_STATE.read_text(encoding="utf-8")
    )
    leading_warm_regions = sorted(
        hypothesis_map["regions"],
        key=lambda item: (-item["warm"], item["family"]),
    )[:12]
    source_registry = json.loads(SOURCE_REGISTRY.read_text(encoding="utf-8"))
    family_by_area = {family["area"]: family["id"] for family in substrate["families"]}
    built_modules = set(imports.get("Ecdlp", []))  # what Ecdlp.lean gates
    depth_cache: dict[str, int] = {}

    theorems = []
    for i, r in enumerate(ledger):
        modules = [file_to_module(file) for file in r["files"]]
        module = modules[0]
        area = classify_area(r["claim"], " ".join(modules))
        sn = short_name(r["name"])
        theorems.append(
            {
                "id": f"thm-{i:03d}",
                "name": r["name"],
                "short_name": sn,
                "module": module,
                "modules": modules,
                "file": r["file"],
                "files": r["files"],
                "claim": r["claim"],
                "method": r["method"],
                "status": r["status"],
                "area": area,
                "family_id": family_by_area[area],
                "dependency_depth": max(
                    (module_depth(item, imports, depth_cache) for item in modules),
                    default=0,
                ),
                "gated": all(
                    item in built_modules
                    or item in {
                        "Ecdlp.Secp256k1Verified",
                        "Ecdlp.Lagrange",
                        "Ecdlp.Statements",
                    }
                    for item in modules
                ),
            }
        )

    name_to_id = {t["short_name"]: t["id"] for t in theorems}

    edges = []
    # file-level import dependency edges between project modules
    for module, deps in imports.items():
        for d in deps:
            edges.append({"from": module, "to": d, "type": "imports"})
    # theorem -> barrier frontier edges
    for bid, names in FRONTIER.items():
        for nm in names:
            if nm in name_to_id:
                edges.append(
                    {"from": name_to_id[nm], "to": bid, "type": "frontier_of"}
                )

    # Semantic architecture edges. Import edges explain compilation; these explain
    # research meaning and release dependencies.
    for theorem in theorems:
        edges.append(
            {"from": theorem["id"], "to": theorem["family_id"], "type": "member_of"}
        )
    for node in substrate["critical_nodes"]:
        node_id = node["id"]
        for anchor in node.get("anchors", []):
            for theorem in theorems:
                if anchor in theorem["name"]:
                    edges.append(
                        {
                            "from": theorem["id"],
                            "to": node_id,
                            "type": "supports",
                            "anchor": anchor,
                        }
                    )
        for dependency in node.get("depends_on", []):
            edges.append(
                {"from": node_id, "to": dependency, "type": "depends_on"}
            )
        for blocker in node.get("blocker_ids", []):
            edges.append(
                {"from": node_id, "to": blocker, "type": "blocked_by"}
            )

    # The decision layer answers which routes apply to the exact target and what
    # work they require. It is intentionally separate from formal release edges.
    for route in decisions["routes"]:
        route_id = route["id"]
        for threat_model in route["threat_models"]:
            edges.append(
                {
                    "from": route_id,
                    "to": threat_model,
                    "type": "evaluated_under",
                }
            )
        for attack_id in route["attack_registry_ids"]:
            edges.append(
                {"from": route_id, "to": attack_id, "type": "detailed_by"}
            )
        for foundation_id in route["foundation_ids"]:
            edges.append(
                {
                    "from": route_id,
                    "to": foundation_id,
                    "type": "requires_foundation",
                }
            )
        for formal_node_id in route["formal_node_ids"]:
            edges.append(
                {
                    "from": route_id,
                    "to": formal_node_id,
                    "type": "decision_grounded_in",
                }
            )
        for hypothesis_id in route.get("hypothesis_ids", []):
            edges.append(
                {
                    "from": route_id,
                    "to": hypothesis_id,
                    "type": "governs_hypothesis",
                }
            )
    for foundation in decisions["foundations"]:
        for formal_node_id in foundation["formal_node_ids"]:
            edges.append(
                {
                    "from": foundation["id"],
                    "to": formal_node_id,
                    "type": "extends_frontier",
                }
            )

    # Typed evidence cells are the deterministic left half of hypothesis
    # generation. They join mechanisms to target facts, source claims, barriers,
    # and the cost quantity a useful mechanism would have to change.
    for cell in typed_evidence["cells"]:
        cell_id = cell["cell_id"]
        edges.append(
            {
                "from": cell_id,
                "to": cell["mechanism_id"],
                "type": "instantiates_mechanism",
            }
        )
        edges.append(
            {
                "from": cell_id,
                "to": cell["route_id"],
                "type": "evaluates_route",
            }
        )
        edges.append(
            {
                "from": cell_id,
                "to": cell["cost_quantity_id"],
                "type": "must_change_cost_quantity",
            }
        )
        for requirement in cell["requirement_results"]:
            edges.append(
                {
                    "from": cell_id,
                    "to": requirement["property_id"],
                    "type": "requires_target_property",
                    "verdict": requirement["verdict"],
                }
            )
        for claim_id in cell["source_claim_ids"]:
            edges.append(
                {
                    "from": cell_id,
                    "to": claim_id,
                    "type": "grounded_in_source_claim",
                }
            )
        for barrier_id in cell["barrier_ids"]:
            edges.append(
                {
                    "from": cell_id,
                    "to": barrier_id,
                    "type": "bounded_by_research_barrier",
                }
            )
        seed_axes = cell["seed_axes"]
        edges.extend(
            [
                {
                    "from": cell_id,
                    "to": seed_axes["target_feature_id"],
                    "type": "binds_target_feature",
                },
                {
                    "from": cell_id,
                    "to": seed_axes["mechanism_primitive_id"],
                    "type": "binds_mechanism_primitive",
                },
                {
                    "from": cell_id,
                    "to": seed_axes["uncertainty_id"],
                    "type": "binds_unresolved_question",
                },
            ]
        )

    for seed in engine["hypothesis_generation"]["generated_seeds"]:
        edges.append(
            {
                "from": seed["seed_id"],
                "to": seed["cell_id"],
                "type": "generated_from_cell",
            }
        )

    for stub in shadow_intake["proposal_stubs"]:
        anchor_id = stub["anchor_id"]
        edges.append(
            {
                "from": stub["stub_id"],
                "to": anchor_id,
                "type": (
                    "follows_up_cell"
                    if anchor_id.startswith("CELL-")
                    else "follows_up_source"
                ),
            }
        )

    # Research Engine nodes connect candidate selection and retained outcomes to the
    # already classified route and hypothesis layers. The engine state remains
    # generated from the policy and append-only outcome events.
    for candidate in engine_policy["candidate_proposals"]:
        candidate_id = candidate["id"]
        edges.append(
            {
                "from": candidate_id,
                "to": candidate["hypothesis_id"],
                "type": "tests_hypothesis",
            }
        )
        edges.append(
            {
                "from": candidate_id,
                "to": candidate["route_id"],
                "type": "explores_route",
            }
        )
        for dependency in candidate["dependencies"]:
            edges.append(
                {
                    "from": candidate_id,
                    "to": dependency,
                    "type": "depends_on_candidate",
                }
            )
    for outcome in engine["outcome_events"]:
        event_id = outcome["event_id"]
        edges.append(
            {
                "from": event_id,
                "to": outcome["candidate_id"],
                "type": "records_outcome_for",
            }
        )
        edges.append(
            {
                "from": event_id,
                "to": outcome["hypothesis_id"],
                "type": "updates_hypothesis",
            }
        )
        edges.append(
            {
                "from": event_id,
                "to": outcome["route_id"],
                "type": "records_route_evidence",
            }
        )

    method_hist = Counter(t["method"] for t in theorems)
    edge_hist = Counter(edge["type"] for edge in edges)

    return {
        "schema_version": "4.0",
        "name": "ECDLP verified knowledge graph",
        "purpose": "A machine-readable, navigable index of the machine-checked "
        "(Lean 4 + Mathlib, no sorry or project-defined axioms) structure of the "
        "ECDLP landscape for secp256k1: verified ledger rows, their declaration "
        "and import dependencies, the corpus "
        "claims they verify, the formalization barriers that bound them, and "
        "the target-specific route/foundation decisions. It also carries the "
        "generated Research Engine v0 selection and retained outcome state, while "
        "keeping bounded exploration distinct from route promotion. "
        "Built for a future automated reasoner to load the known-and-verified "
        "frontier without re-deriving it.",
        "invariant": "Every ledger row resolves to declarations accepted by the Lean "
        "kernel with no sorry or project-defined axioms; compiler-trusted native_decide "
        "use is disclosed separately. This graph is derived evidence, not a proof.",
        "counts": {
            "theorems": len(theorems),
            "ledger_rows": len(theorems),
            "barriers": len(BARRIERS),
            "families": len(substrate["families"]),
            "critical_nodes": len(substrate["critical_nodes"]),
            "attack_routes": len(decisions["routes"]),
            "decision_foundations": len(decisions["foundations"]),
            "attack_registry_objects": len(attack_registry["attacks"]),
            "research_engine_candidates": engine["counts"]["candidate_proposals"],
            "generated_hypothesis_seeds": engine["counts"][
                "generated_hypothesis_seeds"
            ],
            "quality_cleared_hypothesis_proposals": engine["counts"][
                "quality_cleared_hypothesis_proposals"
            ],
            "typed_evidence_cells": typed_evidence["counts"]["cells"],
            "typed_decided_cells": (
                typed_evidence["counts"]["decided_inapplicable_cells"]
                + typed_evidence["counts"]["decided_closed_cells"]
            ),
            "typed_seed_eligible_cells": typed_evidence["counts"][
                "seed_eligible_cells"
            ],
            "typed_desk_decisions": typed_evidence["counts"]["desk_decisions"],
            "hypothesis_axis_nodes": sum(
                len(generation_policy["axes"][axis_name])
                for axis_name in (
                    "target_features",
                    "mechanism_primitives",
                    "unresolved_questions",
                )
            ),
            "source_index_nodes": len(source_registry["sources"]),
            "research_engine_intake_candidates": engine["counts"][
                "intake_candidates"
            ],
            "research_engine_outcomes": engine["counts"]["outcome_events"],
            "research_engine_v02_candidates": engine_v02["engine"][
                "input_candidate_count"
            ],
            "shadow_proposal_stubs": shadow_intake["counts"][
                "proposal_stubs"
            ],
            "shadow_parked_ideas": shadow_intake["counts"]["parked_ideas"],
            "typed_screening_cells": hypothesis_space["counts"]["typed_cells"],
            "typed_screening_cold": hypothesis_space["counts"]["cold"],
            "typed_screening_warm": hypothesis_space["counts"]["warm"],
            "typed_screening_hot": hypothesis_space["counts"]["hot"],
            "hypothesis_space_run_records": hypothesis_space_runs["counts"]["runs"],
            "hypothesis_space_distinct_roots": hypothesis_space_runs["counts"]["distinct_instance_roots"],
            "hypothesis_space_operational_errors": (
                hypothesis_space_runs["counts"]["pipeline_errors"]
                + hypothesis_space_runs["counts"]["invariant_violations"]
            ),
            "selected_explorations": engine["counts"]["selected_explorations"],
            "decision_level_bounded_authorizations": int(
                isinstance(
                    decisions.get("bounded_experiment_authorization"), dict
                )
                and decisions["bounded_experiment_authorization"].get("status")
                in {"approved", "consumed"}
            ),
            "selected_structural_routes": len(
                decisions["route_selection"].get("selected_route_ids", [])
            ),
            "promoted_routes": len(
                decisions["route_selection"].get("promoted_route_ids", [])
            ),
            "edges": len(edges),
            "by_edge_type": dict(edge_hist.most_common()),
            "by_method": dict(method_hist.most_common()),
            "by_area": dict(Counter(t["area"] for t in theorems).most_common()),
        },
        "theorems": theorems,
        "barriers": BARRIERS,
        "formal_substrate": {
            "source": "repo/FORMAL_SUBSTRATE.json",
            "release": substrate["release"],
            "families": substrate["families"],
            "blockers": substrate["blockers"],
            "critical_nodes": substrate["critical_nodes"],
            "open_targets": substrate["open_targets"],
        },
        "decision_substrate": {
            "source": "repo/ECDLP_DECISION_SUBSTRATE.json",
            "attack_evidence_source": "data/attack_registry.json",
            "target_problem": decisions["target_problem"],
            "threat_models": decisions["threat_models"],
            "phase_policy": decisions["phase_policy"],
            "bounded_experiment_authorization": decisions.get(
                "bounded_experiment_authorization"
            ),
            "route_selection": decisions["route_selection"],
            "routes": decisions["routes"],
            "foundations": decisions["foundations"],
            "attack_registry_index": [
                {
                    "id": attack["id"],
                    "family": attack["family"],
                    "verdict_class": attack["verdict_class"],
                }
                for attack in attack_registry["attacks"]
            ],
        },
        "research_engine": {
            "policy_source": "repo/RESEARCH_ENGINE_V0.json",
            "state_source": "data/research_engine_state.json",
            "outcome_event_source": "experiments/engine/outcomes/",
            "gate_status": engine["gate_status"],
            "queue_separation": engine["queue_separation"],
            "counts": engine["counts"],
            "selected_sequence": engine["selected_sequence"],
            "execution_queue": engine["execution_queue"],
            "hard_rejected_candidates": engine["hard_rejected_candidates"],
            "retrospective_validation": engine["retrospective_validation"],
            "calibration": engine["calibration"],
            "normalized_hypotheses": engine["normalized_hypotheses"],
            "outcome_events": engine["outcome_events"],
            "historical_outcomes": engine["historical_outcomes"],
            "native_outcomes": engine["native_outcomes"],
            "route_evidence_state": engine["route_evidence_state"],
            "hypothesis_generation": engine["hypothesis_generation"],
            "feedback_contract": engine["feedback_contract"],
        },
        "research_engine_v02": {
            "policy_source": "repo/RESEARCH_ENGINE_LIFECYCLE_V0.json",
            "state_source": "data/research_engine_v02_state.json",
            "status": engine_v02["status"],
            "historical_outcome_boundary": engine_v02[
                "historical_outcome_boundary"
            ],
            "engine": engine_v02["engine"],
            "authorization": engine_v02["authorization"],
        },
        "research_shadow_intake": {
            "state_source": "data/research_engine_shadow_intake.json",
            "status": shadow_intake["status"],
            "counts": shadow_intake["counts"],
            "proposal_stubs": shadow_intake["proposal_stubs"],
            "parked_ideas": shadow_intake["parked_ideas"],
            "generation_contract": shadow_intake["generation_contract"],
        },
        "hypothesis_axis_index": {
            "policy_source": "repo/HYPOTHESIS_GENERATION_V0.json",
            "target_features": generation_policy["axes"]["target_features"],
            "mechanism_primitives": generation_policy["axes"][
                "mechanism_primitives"
            ],
            "unresolved_questions": generation_policy["axes"][
                "unresolved_questions"
            ],
        },
        "hypothesis_space": {
            "policy_source": "repo/HYPOTHESIS_SPACE_V2.json",
            "state_source": "data/hypothesis_space_state.json",
            "map_source": "data/hypothesis_space_map.json",
            "space_id": hypothesis_space["space_id"],
            "status": hypothesis_space["status"],
            "counts": hypothesis_space["counts"],
            "bulk_contract": hypothesis_space["bulk_contract"],
            "coverage_boundary": hypothesis_map["coverage_boundary"],
            "temperature_legend": hypothesis_map["temperature_legend"],
            "region_count": len(hypothesis_map["regions"]),
            "leading_warm_regions": leading_warm_regions,
            "run_memory": {
                "policy_source": "repo/HYPOTHESIS_SPACE_RUN_LEDGER_V1.json",
                "state_source": "data/hypothesis_space_run_state.json",
                "counts": hypothesis_space_runs["counts"],
                "latest_completed_run": hypothesis_space_runs["latest_completed_run"],
                "map_revisions": hypothesis_space_runs["map_revisions"],
                "scientific_memory_boundary": hypothesis_space_runs[
                    "scientific_memory_boundary"
                ],
            },
        },
        "source_index": {
            "registry_source": "data/source_registry.json",
            "sources": [
                {
                    "id": source["id"],
                    "title": source["title"],
                    "full_text_status": source["full_text_status"],
                }
                for source in source_registry["sources"]
            ],
        },
        "typed_evidence": {
            "state_source": "data/typed_evidence_state.json",
            "policy_source": "repo/ECDLP_TYPED_EVIDENCE_V0.json",
            "counts": typed_evidence["counts"],
            "source_hashes": typed_evidence["source_hashes"],
            "trust_boundary": typed_evidence["trust_boundary"],
            "cell_index": [
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
                for cell in typed_evidence["cells"]
            ],
            "desk_decision_index": [
                {
                    "decision_id": decision["decision_id"],
                    "cell_id": decision["cell_id"],
                    "classification": decision["classification"],
                    "authorization": decision["authorization"],
                }
                for decision in typed_evidence["desk_decisions"]
            ],
            "authorization_boundary": typed_evidence["authorization_boundary"],
        },
        "corpus": parse_corpus(),
        "edges": edges,
    }


OUT_MD = ROOT / "data" / "knowledge_graph.md"


def render_markdown(graph: dict) -> str:
    """A human/AI-readable rendering of the graph: the verified frontier grouped by
    research area, then the barriers. Generated — edit the script, not this file."""
    c = graph["counts"]
    lines: list[str] = []
    lines.append("# ECDLP verified knowledge graph (rendered view)")
    lines.append("")
    lines.append(
        "> Auto-generated from `VERIFIED.md` + the Lean import surface by "
        "`scripts/build_knowledge_graph.py`. Machine source of truth: "
        "`data/knowledge_graph.json`. Every ledger row below cites kernel-checked "
        "declarations (no `sorry`, no custom axioms)."
    )
    lines.append("")
    lines.append(
        f"**{c['ledger_rows']} ledger-row nodes** · **{c['families']} result families** · "
        f"**{c['critical_nodes']} critical nodes** · "
        f"**{c['attack_routes']} attack routes** · "
        f"**{c['decision_foundations']} decision foundations** · "
        f"**{c['selected_structural_routes']} bounded structural route recorded** · "
        f"**{c['promoted_routes']} routes promoted** · "
        f"**{c['typed_evidence_cells']} typed evidence cells** · "
        f"**{c['typed_decided_cells']} desk-decided cells** · "
        f"**{c['generated_hypothesis_seeds']} research-question seeds** · "
        f"**{c['shadow_proposal_stubs']} shadow proposal stubs** · "
        f"**{c['selected_explorations']} bounded explorations selected** · "
        f"**{c['decision_level_bounded_authorizations']} exact decision-level "
        "toy authorization** · "
        f"**{c['research_engine_outcomes']} retained outcomes** · "
        f"**{c['edges']} edges**"
    )
    lines.append("")
    lines.append(
        "> A ledger-row node may cite several Lean declarations. `STATUS.md` owns headline "
        "counts; `data/result_registry.json` owns declaration-level resolution."
    )
    lines.append("")
    lines.append("By proof method: "
                 + ", ".join(f"{k} ({v})" for k, v in c["by_method"].items()))
    lines.append("")
    lines.append("By research area: "
                 + ", ".join(f"{k} ({v})" for k, v in c["by_area"].items()))
    lines.append("")
    lines.append("By edge type: "
                 + ", ".join(f"{k} ({v})" for k, v in c["by_edge_type"].items()))
    lines.append("")

    decisions = graph["decision_substrate"]
    phase = decisions["phase_policy"]
    authorization = decisions["bounded_experiment_authorization"]
    selection = decisions["route_selection"]
    lines.append("## secp256k1 route decisions")
    lines.append("")
    lines.append(
        "This target-specific layer is generated from "
        "`repo/ECDLP_DECISION_SUBSTRATE.json`. It does not replace the attack "
        "evidence registry or the formal release map."
    )
    lines.append("")
    lines.append(
        f"Phase: **{phase['phase']}**. Exact decision experiment authorized: "
        f"**{str(phase['experiments_authorized']).lower()}**. "
        f"Native bounded exploration authorized: "
        f"**{str(phase['bounded_exploration_authorized']).lower()}**. "
        f"Promotion experiments authorized: "
        f"**{str(phase['promotion_experiments_authorized']).lower()}**. "
        f"Structural routes: "
        f"**{', '.join(selection.get('selected_route_ids', [])) or 'none'}**. "
        f"Promoted routes: "
        f"**{', '.join(selection.get('promoted_route_ids', [])) or 'none'}**. "
        f"Selected attack route: **{phase['selected_attack_route'] or 'none'}**."
    )
    lines.append("")
    lines.append("### Exact bounded experiment record")
    lines.append("")
    lines.append(
        f"**{authorization['authorization_id']}** is "
        f"`{authorization['status']}` for "
        f"`{authorization['hypothesis_id']}` / "
        f"`{authorization['task_id']}` / "
        f"`{authorization['route_id']}` / "
        f"`{authorization['cell_id']}`. It binds readiness commit "
        f"`{authorization['source_commit']}` and "
        f"**{len(authorization['sha256_bindings'])} source hashes**. "
        f"Terminal: `{authorization['terminal_status']}` in "
        f"`{authorization['terminal_event_id']}`; rerun authorized: "
        f"**{str(authorization['rerun_authorized']).lower()}**."
    )
    lines.append("")
    lines.append(
        f"Scope: `{authorization['scope']['kind']}`, "
        f"`{authorization['scope']['curve_family']}`, "
        f"{len(authorization['scope']['curve_ids'])} frozen toy subgroups, "
        f"maximum **{authorization['scope']['max_field_bits']} field bits**. "
        f"Budget: **{authorization['resource_budget']['max_primary_trials']} "
        "primary trials**, "
        f"**{authorization['resource_budget']['max_cpu_hours']} CPU-hours**, "
        f"**{authorization['resource_budget']['max_peak_rss_gib']} GiB**, "
        f"**{authorization['resource_budget']['max_wall_hours']} wall-hours**."
    )
    lines.append("")
    lines.append(
        "This external singleton is not a native Engine candidate or route "
        "authorization. Real-world and secp256k1 targets are forbidden; "
        f"promotion authorized: "
        f"**{str(authorization['promotion_authorized']).lower()}**."
    )
    lines.append("")
    lines.append(
        f"Selection **{selection['decision_id']}** "
        f"(`{selection['performed_on']}`): **{selection['decision']}**. "
        f"{selection['gate_result']}"
    )
    lines.append("")
    lines.append("| priority | route | status | threat models | foundations |")
    lines.append("|---:|---|---|---|---|")
    for route in sorted(
        decisions["routes"], key=lambda item: (item["priority"], item["id"])
    ):
        threat_models = ", ".join(f"`{item}`" for item in route["threat_models"])
        foundations = ", ".join(f"`{item}`" for item in route["foundation_ids"])
        lines.append(
            f"| {route['priority']} | **{route['id']}**: {route['title']} | "
            f"`{route['status']}` | {threat_models} | {foundations} |"
        )
    lines.append("")
    lines.append("### Foundation portfolio")
    lines.append("")
    lines.append("| priority | foundation | decision | status | build now |")
    lines.append("|---:|---|---|---|---:|")
    for foundation in sorted(
        decisions["foundations"], key=lambda item: (item["priority"], item["id"])
    ):
        lines.append(
            f"| {foundation['priority']} | **{foundation['id']}**: "
            f"{foundation['title']} | `{foundation['decision']}` | "
            f"`{foundation['implementation_status']}` | "
            f"{str(foundation['build_now']).lower()} |"
        )
    lines.append("")

    typed = graph["typed_evidence"]
    lines.append("## Typed evidence and hypothesis cells")
    lines.append("")
    lines.append(
        "Cells are regenerated joins over mechanisms, target properties, source "
        "claims, scoped barriers, and cost quantities. A decided cell cannot emit "
        "a non-executable proposal seed, and no cell authorizes an experiment."
    )
    lines.append("")
    lines.append(
        "| cell | route | status | required property verdicts | cost quantity | seed eligible |"
    )
    lines.append("|---|---|---|---|---|---:|")
    for cell in typed["cell_index"]:
        verdicts = ", ".join(
            f"`{item['property_id']}`={item['verdict']}"
            for item in cell["requirement_results"]
        )
        lines.append(
            f"| **{cell['cell_id']}** | `{cell['route_id']}` | "
            f"`{cell['status']}` | {verdicts} | "
            f"`{cell['cost_quantity_id']}` | "
            f"{str(cell['seed_eligible']).lower()} |"
        )
    lines.append("")

    engine = graph["research_engine"]
    shadow = graph["research_shadow_intake"]
    generation = engine["hypothesis_generation"]
    axis_index = graph["hypothesis_axis_index"]
    lines.append("## Finite hypothesis-space projection")
    lines.append("")
    lines.append(
        "The mathematical hypothesis space is open-ended. This section is the "
        "finite, versioned projection induced by the current typed evidence, "
        "mechanism identity grammar, route model, and evidence digests. It is "
        "not a claim that every possible ECDLP idea has been enumerated."
    )
    lines.append("")
    lines.append(
        "The typed mechanism and cell are part of scientific identity. The three "
        "synthesis axes alone are not a Cartesian-product hypothesis identifier."
    )
    lines.append("")
    lines.append(
        "| axis kind | axis | definition boundary |"
    )
    lines.append("|---|---|---|")
    axis_groups = (
        ("target feature", axis_index["target_features"]),
        ("mechanism primitive", axis_index["mechanism_primitives"]),
        ("unresolved question", axis_index["unresolved_questions"]),
    )
    for axis_kind, axes in axis_groups:
        for axis in axes:
            lines.append(
                f"| {axis_kind} | **{axis['id']}**: {axis['label']} | "
                f"{axis['boundary']} |"
            )
    lines.append("")
    lines.append(
        "| seed | typed mechanism and cell | target feature | mechanism primitive | "
        "unresolved question | status |"
    )
    lines.append("|---|---|---|---|---|---|")
    for seed in generation["generated_seeds"]:
        lines.append(
            f"| **{seed['seed_id']}** | `{seed['typed_cell']['mechanism_id']}` / "
            f"`{seed['cell_id']}` | `{seed['target_feature']['id']}` | "
            f"`{seed['mechanism_primitive']['id']}` | "
            f"`{seed['unresolved_question']['id']}` | "
            f"`{seed['status']}`, authorization `{seed['authorization']}` |"
        )
    if not generation["generated_seeds"]:
        lines.append("| **none** | - | - | - | - | no eligible typed cells |")
    lines.append("")
    lines.append("| shadow stub | anchor | kind | executable | authorized |")
    lines.append("|---|---|---|---:|---:|")
    for stub in shadow["proposal_stubs"]:
        lines.append(
            f"| **{stub['stub_id']}** | `{stub['anchor_id']}` | "
            f"`{stub['stub_kind']}` | {str(stub['executable']).lower()} | "
            f"{str(stub['authorized']).lower()} |"
        )
    lines.append("")
    lines.append(
        "> These rows are research questions. They are not quality-cleared "
        "hypotheses, candidates, route promotions, or permission to execute."
    )
    lines.append("")
    lines.append(
        "> Current desk priority: `CELL-M-PKC-SMOOTH-M16` / "
        "`RSI-D8BBA6340789`. The auxiliary-curve cell remains parked pending "
        "a finite source-defined search domain. Authorization remains `none`."
    )
    lines.append("")

    space = graph["hypothesis_space"]
    counts = space["counts"]
    lines.append("### Million-cell adversarial projection")
    lines.append("")
    lines.append(space["coverage_boundary"])
    lines.append("")
    lines.append(
        f"The frozen projection contains **{counts['typed_cells']:,}** typed "
        f"challenge cells: **{counts['cold']:,} cold**, "
        f"**{counts['warm']:,} warm**, and **{counts['hot']:,} hot**. "
        f"Only **{counts['review_queue']}** bounded records reach the review queue; "
        "authorization remains `none`."
    )
    lines.append("")
    lines.append("| region temperature | meaning |")
    lines.append("|---|---|")
    for temperature in ("cold", "warm", "hot"):
        lines.append(
            f"| **{temperature}** | {space['temperature_legend'][temperature]} |"
        )
    lines.append("")
    lines.append("| leading warm family | kind | warm cells | cold cells |")
    lines.append("|---|---|---:|---:|")
    for region in space["leading_warm_regions"]:
        lines.append(
            f"| `{region['family']}` | `{region['type']}` | "
            f"{region['warm']} | {region['cold']} |"
        )
    lines.append("")
    run_memory = space["run_memory"]
    latest_run = run_memory["latest_completed_run"]
    latest_rate = (
        f"{latest_run['median_signatures_per_minute']:,} typed cells/minute"
        if latest_run
        else "not yet measured"
    )
    lines.append(
        f"Operational memory retains **{run_memory['counts']['runs']}** immutable "
        f"run record(s) over **{run_memory['counts']['distinct_instance_roots']}** "
        f"distinct map root(s); latest median throughput is **{latest_rate}**. "
        "These records preserve engineering performance and failures only. "
        "Structural rejects are not falsified hypotheses, and the run ledger "
        "cannot supply scientific labels, calibration, or authorization."
    )
    lines.append("")

    gates = engine["gate_status"]
    lines.append("## Research Engine v0")
    lines.append("")
    lines.append(
        "The engine may schedule cheap, preregistered toy-curve exploration within "
        "the declared budget. It cannot promote a route, authorize exact-target "
        "work, or support a secp256k1 complexity claim."
    )
    lines.append("")
    lines.append(
        f"Exploration gate: **{str(gates['exploration_authorized']).lower()}**. "
        f"Promotion gate: **{str(gates['promotion_authorized']).lower()}**. "
        "Historical no-reopen guard: "
        f"**{str(engine['retrospective_validation']['passed']).lower()}**. "
        "Predictive EIG calibration outcomes: "
        f"**{engine['calibration']['scored_native_outcomes']}**."
    )
    lines.append("")
    lines.append(
        "| order | candidate | kind | EIG (bits) | bits / budget cost | execution state |"
    )
    lines.append("|---:|---|---|---:|---:|---|")
    for candidate in engine["selected_sequence"]:
        lines.append(
            f"| {candidate['position']} | **{candidate['candidate_id']}**: "
            f"{candidate['title']} | `{candidate['kind']}` | "
            f"{candidate['expected_information_gain_bits']:.6g} | "
            f"{candidate['priority_bits_per_cost']:.6g} | "
            f"`{candidate['execution_state']}` |"
        )
    if not engine["selected_sequence"]:
        lines.append(
            "| - | **none** | - | - | - | "
            "`no candidate cleared mechanism and validator gates` |"
        )
    lines.append("")
    lines.append(
        f"Blocked intake candidates: **{engine['counts']['intake_candidates']}**. "
        "Intake is retained research memory, not permission to execute."
    )
    lines.append("")
    outcomes = engine["counts"]["outcomes_by_taxonomy"]
    lines.append(
        "Retained outcomes: "
        + ", ".join(f"`{name}`={count}" for name, count in outcomes.items())
        + "."
    )
    lines.append("")
    lines.append(
        f"> Promotion boundary: {engine['feedback_contract']['promotion_boundary']}"
    )
    lines.append("")

    lifecycle = graph["research_engine_v02"]
    lines.append("## Research Engine v0.2 shadow lifecycle")
    lines.append("")
    lines.append(
        "v0.2 separates immutable candidate snapshots, mutable lifecycle state, "
        "portfolio recommendation, and owner authorization. The current state is "
        "non-executing."
    )
    lines.append("")
    lines.append(
        f"Lifecycle candidates: **{lifecycle['engine']['input_candidate_count']}**. "
        f"Admissible: **{len(lifecycle['engine']['admissible'])}**. "
        f"Recommended: **{len(lifecycle['engine']['recommended'])}**. "
        f"Authorized: **{lifecycle['authorization']['experiments']}**. "
        f"Shadow proposal stubs: **{shadow['counts']['proposal_stubs']}**. "
        f"Parked desired-property ideas: **{shadow['counts']['parked_ideas']}**."
    )
    lines.append("")
    lines.append(
        "> Every shadow row is a research-question seed. It is not a hypothesis, "
        "candidate, route promotion, or permission to execute."
    )
    lines.append("")

    substrate = graph["formal_substrate"]
    lines.append("## Formal substrate critical path")
    lines.append("")
    lines.append(
        "This is the release-facing dependency map from `repo/FORMAL_SUBSTRATE.json`. "
        "`closed` means the declared scope is landed; `blocked` is an explicit frontier, "
        "not a proved result."
    )
    lines.append("")
    lines.append("| node | status | release | depends on | blockers |")
    lines.append("|---|---|---|---|---|")
    for node in substrate["critical_nodes"]:
        deps = ", ".join(f"`{item}`" for item in node.get("depends_on", [])) or "—"
        blockers = ", ".join(f"`{item}`" for item in node.get("blocker_ids", [])) or "—"
        lines.append(
            f"| **{node['id']}** — {node['title']} | {node['status']} | "
            f"{node['release_disposition']} | {deps} | {blockers} |"
        )
    lines.append("")

    lines.append("### Declared blockers")
    lines.append("")
    for blocker in substrate["blockers"]:
        lines.append(
            f"- **{blocker['id']} — {blocker['title']}.** "
            f"{blocker['description']} Resume: {blocker['resume_condition']}"
        )
    lines.append("")

    lines.append("### Exhaustive result families")
    lines.append("")
    area_counts = c["by_area"]
    for family in substrate["families"]:
        lines.append(
            f"- **{family['id']}** (`{family['area']}`, "
            f"{area_counts.get(family['area'], 0)} rows in this family): {family['title']}."
        )
    lines.append("")

    # Group compatibility-key `theorems` (ledger-row nodes) by area.
    by_area: dict[str, list[dict]] = {}
    for t in graph["theorems"]:
        by_area.setdefault(t["area"], []).append(t)
    lines.append("## Verified ledger rows by area")
    lines.append("")
    for area in sorted(by_area, key=lambda a: -len(by_area[a])):
        lines.append(f"### {area} ({len(by_area[area])})")
        lines.append("")
        lines.append("| theorem | claim | method | file |")
        lines.append("|---|---|---|---|")
        for t in by_area[area]:
            lines.append(
                f"| `{t['short_name']}` | {t['claim']} | {t['method']} | "
                f"`{t['file'].split('/')[-1]}` |"
            )
        lines.append("")

    # Frontier: ledger-row nodes sitting at a barrier boundary.
    frontier = [e for e in graph["edges"] if e["type"] == "frontier_of"]
    id_to_thm = {t["id"]: t for t in graph["theorems"]}
    lines.append("## Barriers and their verified frontier")
    lines.append("")
    lines.append(
        "Each barrier is a foundation Mathlib lacks. The *frontier* lists verified "
        "ledger rows sitting at that boundary — the realised edge of the missing work."
    )
    lines.append("")
    for b in graph["barriers"]:
        lines.append(f"### {b['id']} — {b['title']}")
        lines.append("")
        lines.append(f"- **Missing:** {b['missing_foundation']}")
        lines.append(f"- **Blocks:** {b['blocks']}")
        if b.get("partial_progress"):
            lines.append(f"- **Partial progress:** {b['partial_progress']}")
        fnodes = [id_to_thm[e["from"]] for e in frontier
                  if e["to"] == b["id"] and e["from"] in id_to_thm]
        if fnodes:
            lines.append("- **Verified frontier:** "
                         + ", ".join(f"`{t['short_name']}`" for t in fnodes))
        lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    graph = build()
    text = json.dumps(graph, indent=2, ensure_ascii=False) + "\n"
    md = render_markdown(graph)
    if "--check" in sys.argv:
        stale = []
        if not OUT.exists() or OUT.read_text(encoding="utf-8") != text:
            stale.append(str(OUT))
        if not OUT_MD.exists() or OUT_MD.read_text(encoding="utf-8") != md:
            stale.append(str(OUT_MD))
        if stale:
            print(
                "stale; run: python3 scripts/build_knowledge_graph.py -> "
                + ", ".join(stale),
                file=sys.stderr,
            )
            return 1
        print(f"up to date ({graph['counts']['ledger_rows']} ledger rows).")
        return 0
    OUT.write_text(text, encoding="utf-8")
    OUT_MD.write_text(md, encoding="utf-8")
    print(
        f"wrote {OUT} and {OUT_MD}: {graph['counts']['ledger_rows']} ledger rows, "
        f"{graph['counts']['barriers']} barriers, {graph['counts']['edges']} edges."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
