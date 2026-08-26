#!/usr/bin/env python3
"""Generate KeyAI's product site from canonical repository state."""
from __future__ import annotations

import html
import json
import re
from collections import Counter
from pathlib import Path

from ledger_utils import parse_researchos_ledger, strip_md
from pilot_evidence import primary_dispositions, valid_second_projects

ROOT = Path(__file__).resolve().parent.parent
ASSET_VERSION = "20260825-1"

PRODUCT_PATH = ROOT / "repo" / "PRODUCT_MODEL.json"
PILOT_PATH = ROOT / "repo" / "PILOT_PROTOCOL.json"
DECISION_PATH = ROOT / "repo" / "ECDLP_DECISION_SUBSTRATE.json"
FORMAL_PATH = ROOT / "repo" / "FORMAL_SUBSTRATE.json"
STATS_PATH = ROOT / "data" / "stats.json"
FRONTIER_PATH = ROOT / "data" / "frontier_map.json"
GRAPH_PATH = ROOT / "data" / "knowledge_graph.json"
ENGINE_PATH = ROOT / "data" / "research_engine_state.json"
VERIFIED_INDEX_PATH = ROOT / "data" / "verified_index.json"
RESEARCH_TASKS_PATH = ROOT / "tasks" / "ECDLP_RESEARCH.md"
PRODUCT_TASKS_PATH = ROOT / "tasks" / "KEYAI_PRODUCT.md"

INDEX_PATH = ROOT / "index.html"
DASHBOARD_PATH = ROOT / "dashboard.html"
EXPLORE_PATH = ROOT / "explore.html"
PILOT_OUTPUT_PATH = ROOT / "pilot.html"
RESULTS_PATH = ROOT / "results.html"
ROBOTS_PATH = ROOT / "robots.txt"
SITEMAP_PATH = ROOT / "sitemap.xml"
CNAME_PATH = ROOT / "CNAME"

PUBLIC_PAGES = (
    ("", "Home"),
    ("results.html", "Verified results"),
    ("explore.html", "ECDLP route map"),
    ("dashboard.html", "Technical workspace"),
    ("pilot.html", "Collaboration"),
)

ROUTE_STATUS = {
    "guardrail": ("Guardrail", "guardrail"),
    "baseline": ("Baseline", "baseline"),
    "constant_factor_only": ("Constant factor", "constant_factor_only"),
    "ruled_out_for_target": ("Ruled out for target", "ruled_out_for_target"),
    "open_parked": ("Open, parked", "open_parked"),
    "monitor": ("Monitor", "monitor"),
    "conditional_only": ("Conditional inputs", "conditional_only"),
    "separate_threat_model": ("Separate threat model", "separate_threat_model"),
}

ROUTE_STATUS_ORDER = [
    "guardrail",
    "baseline",
    "constant_factor_only",
    "ruled_out_for_target",
    "open_parked",
    "monitor",
    "conditional_only",
    "separate_threat_model",
]

FORMAL_STATUS = {
    "closed": ("Closed", "closed"),
    "blocked": ("Blocked", "blocked"),
    "parked": ("Parked", "parked"),
    "out_of_release": ("Outside release", "out_of_release"),
}


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def write_text(path: Path, text: str) -> None:
    path.write_text(text.rstrip() + "\n", encoding="utf-8", newline="\n")


def repo_url(product: dict, path: str) -> str:
    repository = product["repository_url"].rstrip("/")
    if path.endswith("/"):
        return f"{repository}/tree/main/{path.rstrip('/')}"
    return f"{repository}/blob/main/{path}"


def pilot_intake_url(product: dict) -> str:
    template = Path(product["pilot"]["intake_surface"]).name
    return f"{product['repository_url'].rstrip('/')}/issues/new?template={template}"


def researchos_claim_scopes() -> dict[str, str]:
    """Read public claim scopes from the canonical ResearchOS ledger."""
    return {
        row["claim_id"]: re.sub(r"\s+", " ", strip_md(row["claim_scope"])).strip()
        for row in parse_researchos_ledger(ROOT)
    }


def evidence_links(product: dict, paths: list[str], limit: int | None = None) -> str:
    selected = paths if limit is None else paths[:limit]
    return "".join(
        f'<a class="source-link" href="{esc(repo_url(product, path))}">{esc(path)}</a>'
        for path in selected
    )


def status_badge(status: str, label: str | None = None) -> str:
    route_meta = ROUTE_STATUS.get(status)
    formal_meta = FORMAL_STATUS.get(status)
    direct_status = status if status in {"blue", "green", "amber", "red", "violet", "gray"} else None
    default_label = route_meta[0] if route_meta else formal_meta[0] if formal_meta else status
    css_status = (
        route_meta[1]
        if route_meta
        else formal_meta[1]
        if formal_meta
        else direct_status or "gray"
    )
    return f'<span class="status status--{esc(css_status)}">{esc(label or default_label)}</span>'


def engine_execution_badge(state: str) -> str:
    style, label = {
        "ready": ("blue", "Ready"),
        "conditional_on_prior_selected_outcomes": ("gray", "Dependency-gated"),
        "awaiting_dependency_outcome": ("gray", "Dependency-gated"),
        "awaiting_validator_implementation": ("amber", "Validator pending"),
        "blocked_by_dependency_outcome": ("red", "Blocked"),
        "terminal": ("green", "Terminal"),
    }.get(state, ("gray", state))
    return status_badge(style, label)


TASK_BLOCK_RE = re.compile(
    r"^### (TASK-\d+) - ([^\n]+)\n(?P<body>.*?)(?=^### TASK-\d+ - |\Z)",
    re.MULTILINE | re.DOTALL,
)
TASK_FIELD_BOUNDARY_RE = r"(?=^[A-Z][A-Za-z0-9 _/-]*:\s|\Z)"


def task_field(
    body: str,
    field: str,
    *,
    source: str,
    task_id: str,
    single_line: bool = False,
) -> str:
    value_pattern = r"([^\n]+)" if single_line else rf"(.*?){TASK_FIELD_BOUNDARY_RE}"
    match = re.search(
        rf"^{re.escape(field)}:\s*{value_pattern}",
        body,
        re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise ValueError(f"{source}: {task_id} is missing required field {field!r}")
    return re.sub(r"\s+", " ", match.group(1)).strip()


def parse_task_text(
    text: str,
    *,
    source: str,
    queue_label: str,
    queue_id: str,
) -> list[dict[str, str]]:
    tasks: list[dict[str, str]] = []
    for match in TASK_BLOCK_RE.finditer(text):
        task_id = match.group(1)
        body = match.group("body")
        tasks.append(
            {
                "id": task_id,
                "title": match.group(2).strip(),
                "status": task_field(
                    body,
                    "Status",
                    source=source,
                    task_id=task_id,
                    single_line=True,
                ),
                "kind": task_field(
                    body,
                    "Kind",
                    source=source,
                    task_id=task_id,
                    single_line=True,
                ),
                "hypothesis": task_field(
                    body,
                    "Hypothesis",
                    source=source,
                    task_id=task_id,
                ),
                "why": task_field(
                    body,
                    "Why it matters",
                    source=source,
                    task_id=task_id,
                ),
                "queue": queue_id,
                "queue_label": queue_label,
                "source": source,
            }
        )
    return tasks


def parse_tasks() -> list[dict[str, str]]:
    tasks: list[dict[str, str]] = []
    queues = (
        ("ECDLP research", "research", RESEARCH_TASKS_PATH),
        ("KeyAI product", "product", PRODUCT_TASKS_PATH),
    )
    for queue_label, queue_id, path in queues:
        source = path.relative_to(ROOT).as_posix()
        tasks.extend(
            parse_task_text(
                path.read_text(encoding="utf-8"),
                source=source,
                queue_label=queue_label,
                queue_id=queue_id,
            )
        )
    return tasks


def task_status_badge(status: str) -> str:
    if status.startswith("active"):
        return status_badge("blue", "Active")
    if status.startswith("blocked"):
        return status_badge("blocked", "Blocked")
    if status.startswith("parked"):
        return status_badge("parked", "Parked")
    return status_badge("gray", status.replace("_", " ").title())


def site_origin() -> str:
    hostname = CNAME_PATH.read_text(encoding="utf-8").strip()
    if not hostname or any(character.isspace() for character in hostname):
        raise ValueError("CNAME must contain exactly one public hostname")
    return f"https://{hostname}"


def page_head(title: str, description: str, path: str = "") -> str:
    origin = site_origin()
    canonical = f"{origin}/{path}" if path else f"{origin}/"
    social_image = f"{origin}/assets/logo-wordmark.png"
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{esc(title)}</title>
  <meta name="description" content="{esc(description)}">
  <meta name="robots" content="index,follow">
  <link rel="canonical" href="{esc(canonical)}">
  <meta property="og:type" content="website">
  <meta property="og:title" content="{esc(title)}">
  <meta property="og:description" content="{esc(description)}">
  <meta property="og:url" content="{esc(canonical)}">
  <meta property="og:image" content="{esc(social_image)}">
  <meta property="og:image:alt" content="KeyAI">
  <meta name="twitter:card" content="summary">
  <meta name="twitter:title" content="{esc(title)}">
  <meta name="twitter:description" content="{esc(description)}">
  <meta name="twitter:image" content="{esc(social_image)}">
  <meta name="theme-color" content="#07182d">
  <link rel="icon" type="image/png" sizes="32x32" href="assets/favicon-32.png">
  <link rel="icon" type="image/png" sizes="16x16" href="assets/favicon-16.png">
  <link rel="apple-touch-icon" href="assets/apple-touch-icon.png">
  <link rel="stylesheet" href="assets/site.css?v={ASSET_VERSION}">
</head>"""


def site_header(product: dict) -> str:
    repository = product["repository_url"].rstrip("/")
    return f"""<a class="skip-link" href="#main">Skip to content</a>
<header class="site-header">
  <div class="shell site-header__inner">
    <a class="brand-link" href="index.html" aria-label="KeyAI home">
      <img src="assets/logo-wordmark.png" alt="KeyAI" width="116" height="59">
    </a>
    <nav class="primary-nav" aria-label="Primary navigation">
      <a data-nav-page="product" href="index.html#research-system">Research system</a>
      <a data-nav-page="results" href="results.html">Verified results</a>
      <a data-nav-page="routes" href="explore.html">ECDLP deployment</a>
      <a data-nav-page="pilot" href="pilot.html">Collaborate</a>
      <a class="nav-cta" href="{esc(repository)}">GitHub</a>
    </nav>
  </div>
</header>"""


def site_footer(product: dict) -> str:
    repository = product["repository_url"].rstrip("/")
    return f"""<footer class="site-footer">
  <div class="shell site-footer__inner">
    <img src="assets/logo-wordmark.png" alt="KeyAI" width="100" height="51">
    <p>{esc(product["category"])}. Current stage: {esc(product["current_stage"]["label"])}.
      The Lean kernel checks declared statements and proof terms; semantic, empirical,
      security, and product claims remain separately evidence-gated.</p>
    <nav class="footer-links" aria-label="Footer navigation">
      <a href="index.html#research-system">Research system</a>
      <a href="results.html">Verified results</a>
      <a href="index.html#reference">ECDLP deployment</a>
      <a href="explore.html">Detailed route map</a>
      <a href="dashboard.html">Technical workspace</a>
      <a href="pilot.html">Collaborate</a>
      <a href="{esc(f'{repository}/blob/main/repo/PRODUCT_MODEL.json')}">Product model</a>
      <a href="{esc(repository)}">Repository</a>
    </nav>
  </div>
</footer>
<script src="assets/site.js?v={ASSET_VERSION}"></script>
</body>
</html>"""


def build_index(
    product: dict,
    pilot: dict,
    stats: dict,
    frontier: dict,
    decisions: dict,
    formal: dict,
    engine: dict,
    verified_index: dict,
) -> str:
    selection = decisions["route_selection"]
    promoted_routes = selection.get("promoted_route_ids", [])
    routes = decisions["routes"]
    current_stage = product["current_stage"]
    mvp = product["mvp"]
    verified_counts = verified_index["counts"]
    pilot_model = product["pilot"]
    route_counts = Counter(route["status"] for route in routes)
    completed_discovery = sum(
        record.get("disposition") in {"build", "change", "stop"}
        for record in primary_dispositions(pilot)
    )
    workflow_context = {
        "ingest": "Pinned question + sources",
        "structure": "Hypotheses + dependencies",
        "decide": "Prior evidence + barriers",
        "execute": "Bounded experiment / proof",
        "verify": "Verifier / scoped outcome",
        "retain": "Updated frontier + next hypothesis",
    }
    workflow_html = "".join(
        f"""<li class="research-loop__item">
  <details class="research-loop__step" data-loop-step {"open" if index == 1 else ""}>
    <summary>
      <span class="research-loop__index">{index:02d}</span>
      <span class="research-loop__label"><strong>{esc(step["label"])}</strong>
        <small>{esc(workflow_context[step["id"]])}</small></span>
    </summary>
    <div class="research-loop__detail"><p>{esc(step["outcome"])}</p></div>
  </details>
</li>"""
        for index, step in enumerate(product["workflow"], start=1)
    )
    memory_html = "".join(
        f"<li>{esc(item)}</li>" for item in product["product"]["system_of_record"]
    )
    failure_html = "".join(
        f"<li>{esc(item)}</li>" for item in product["problem"]["failure_modes"]
    )
    capability_copy = {
        "verified-ledger": "Exact declarations, source anchors, proof methods, and disclosed trust labels.",
        "decision-substrate": "Routes retain their scope, evidence, stop conditions, and reasons to reopen.",
        "candidate-contract": "Selected outputs bind pinned inputs to a separate validation path.",
        "research-memory": "Tasks, hypotheses, outcomes, provenance, and generated views persist across sessions.",
    }
    capabilities_html = "".join(
        f"""<article class="capability-card">
  <span class="capability-card__state">Available in the reference deployment</span>
  <h3>{esc(capability["label"])}</h3>
  <p>{esc(capability_copy[capability["id"]])}</p>
  {evidence_links(product, capability["evidence"], limit=1)}
</article>"""
        for capability in current_stage["capabilities_now"]
    )
    current_html = "".join(
        f"<li>{esc(item['label'])}</li>" for item in current_stage["capabilities_now"]
    )
    not_yet_html = "".join(f"<li>{esc(item)}</li>" for item in current_stage["not_yet"])
    metric_html = "".join(
        f"""<li><span>{esc(metric["id"])}</span><p>{esc(metric["target"])}</p></li>"""
        for metric in mvp["exit_metrics"]
    )
    proof_closed = sum(1 for node in formal["critical_nodes"] if node["status"] == "closed")
    description = (
        "KeyAI is a public reference deployment for long-running AI research, preserving "
        "hypotheses, evidence, bounded experiments, counterexamples, replay, and formal results."
    )
    return f"""{page_head("KeyAI | Research infrastructure that remembers", description)}
<body data-page="product">
{site_header(product)}
<main id="main">
  <section class="hero" aria-labelledby="hero-title">
    <div class="shell hero__inner">
      <div class="hero__copy">
        <p class="eyebrow">KeyAI · {esc(product["category"])}</p>
        <h1 id="hero-title">An operating system for long-running AI research.</h1>
        <p class="hero__lede">Today, KeyAI is a public reference deployment—not a
          self-serve or hosted multi-project product. It preserves hypotheses, evidence, bounded experiments,
          counterexamples, formal results, barriers, and provenance in one inspectable state—so
          the next researcher or agent can continue from the last known boundary.</p>
        <div class="actions">
          <a class="button button--primary" href="#research-system">Explore the Research System</a>
          <a class="button button--on-dark" href="results.html">View Verified Results</a>
        </div>
        <nav class="hero__links" aria-label="More ways to explore">
          <a href="#reference">See the ECDLP Reference Deployment</a>
          <a href="{esc(product['repository_url'])}">GitHub</a>
        </nav>
      </div>
      <aside class="hero-state" aria-labelledby="hero-state-title">
        <div class="hero-state__head">
          <span>What exists today</span>
          {status_badge("blue", current_stage["label"])}
        </div>
        <h2 id="hero-state-title">A public reference deployment, not a product promise.</h2>
        <ol class="hero-state__list">
          <li><span>01</span><div><strong>One inspectable research state</strong>
            <small>Claims, evidence, tasks, decisions, outcomes, and provenance.</small></div></li>
          <li><span>02</span><div><strong>One difficult reference environment</strong>
            <small>secp256k1 ECDLP demonstrates the workflow; no break is claimed.</small></div></li>
          <li><span>03</span><div><strong>One evidence-gated next milestone</strong>
            <small>An external team must complete the loop before the MVP claim advances.</small></div></li>
        </ol>
        <p>{esc(current_stage["summary"])}</p>
      </aside>
    </div>
  </section>

  <section class="evidence-rail" aria-labelledby="evidence-rail-title">
    <div class="shell evidence-rail__inner">
      <div class="evidence-rail__intro">
        <p class="eyebrow">Demonstrated, not implied</p>
        <h2 id="evidence-rail-title">Evidence is inspectable from the first click.</h2>
      </div>
      <dl class="evidence-rail__metrics">
        <div><dt>Proof navigation</dt><dd><strong>{verified_counts["navigation_rows_total"]}</strong>
          entries across two isolated ledgers</dd></div>
        <div><dt>ECDLP route memory</dt><dd><strong>{len(routes)}</strong>
          routes with recorded dispositions</dd></div>
        <div><dt>Built proof surface</dt><dd><strong>{stats["sorry_count"]} / {stats["custom_axioms"]}</strong>
          <code>sorry</code> / custom axioms</dd></div>
      </dl>
    </div>
  </section>

  <section class="band band--white" id="what-keyai-is" aria-labelledby="what-keyai-title">
    <div class="shell problem-layout">
      <div class="section-heading section-heading--sticky">
        <p class="eyebrow">What KeyAI is</p>
        <h2 id="what-keyai-title">The missing infrastructure between a research question and the next agent.</h2>
        <p>{esc(product["problem"]["statement"])}</p>
        <p class="section-note">{esc(product["product"]["promise"])}</p>
      </div>
      <div class="problem-cards">
        <article class="problem-card problem-card--risk">
          <span>Without durable memory</span>
          <h3>Research restarts in fragments.</h3>
          <ul>{failure_html}</ul>
        </article>
        <article class="problem-card problem-card--system">
          <span>With an inspectable state</span>
          <h3>Each recorded handoff has evidence and a boundary.</h3>
          <p>Models can propose proofs, experiments, and code. KeyAI preserves the research program
            around those attempts: what was asked, what was tried, what a verifier accepted, what
            failed in scope, and what should happen next.</p>
          <a href="#research-system">See the research loop</a>
        </article>
      </div>
    </div>
  </section>

  <section class="band research-system" id="research-system" aria-labelledby="research-system-title">
    <div class="shell">
      <div class="section-heading section-heading--wide">
        <p class="eyebrow">How Research OS works</p>
        <h2 id="research-system-title">A research loop that remembers what happened.</h2>
        <p>The canonical workflow moves from pinned inputs to a retained outcome. Open each stage to see
          what it contributes; the full explanation remains available without JavaScript.</p>
      </div>
      <div class="research-loop" data-research-loop>
        <ol class="research-loop__steps">{workflow_html}</ol>
        <aside class="research-loop__memory" aria-labelledby="research-memory-title">
          <p class="eyebrow">Durable research memory</p>
          <h3 id="research-memory-title">The state survives every loop.</h3>
          <ul>{memory_html}</ul>
          <p class="research-loop__foot">Retaining failed approaches and counterexamples is part of
            the output—not an afterthought.</p>
        </aside>
      </div>
    </div>
  </section>

  <section class="band band--white" id="research-map" aria-labelledby="research-map-title">
    <div class="shell">
      <div class="section-heading section-heading--wide">
        <p class="eyebrow">Research map · generated projection</p>
        <h2 id="research-map-title">One starting question. A frontier that records what changed.</h2>
        <p>This small public map is generated from the same decision, formal, result, and engine state
          that drive the technical workspace. It intentionally leaves the full internal graph in the repository.</p>
      </div>
      <ol class="research-map" data-research-map aria-label="ECDLP reference research map">
        <li class="research-map__node research-map__node--question" data-map-kind="question">
          <span class="research-map__kind">Starting question</span>
          <h3>Recover the discrete logarithm in the prime-order secp256k1 group.</h3>
          <p>The target, inputs, output, threat models, and promotion gates are pinned before work begins.</p>
        </li>
        <li class="research-map__node" data-map-kind="branches">
          <span class="research-map__kind">Major branches</span>
          <h3>{len(routes)} named routes are retained.</h3>
          <p>{route_counts.get("ruled_out_for_target", 0)} are ruled out for the exact target;
            {route_counts.get("open_parked", 0)} remain open and parked. Every status is scoped.</p>
          <a href="explore.html">Inspect every route and stop condition</a>
        </li>
        <li class="research-map__node" data-map-kind="formal">
          <span class="research-map__kind">Verified substrate</span>
          <h3>{proof_closed} of {len(formal["critical_nodes"])} critical formal nodes are closed.</h3>
          <p>Formal results establish their encoded statements and assumptions; they do not automatically
            establish an attack or a product claim.</p>
          <a href="results.html">Browse source-linked formal results</a>
        </li>
        <li class="research-map__node research-map__node--empirical" data-map-kind="replayed">
          <span class="research-map__kind">Independently replayed evidence</span>
          <h3>1 exact synthetic-toy run completed.</h3>
          <p>The consumed bounded run was independently validated on frozen toy instances. It is empirical
            evidence, not a secp256k1 result, route promotion, or rerun authorization.</p>
          <a href="dashboard.html#overview">Inspect the retained outcome</a>
        </li>
        <li class="research-map__node research-map__node--barrier" data-map-kind="frontier">
          <span class="research-map__kind">Updated frontier</span>
          <h3>{len(promoted_routes)} attack routes are promoted.</h3>
          <p>Scoped negatives and unresolved cost, recovery, and validation obligations remain visible so
            the next attempt does not quietly repeat them.</p>
        </li>
        <li class="research-map__node research-map__node--frontier" data-map-kind="next-gap">
          <span class="research-map__kind">Next unresolved gap</span>
          <h3>New execution needs new evidence and a dated decision.</h3>
          <p>{len(decisions["acceptance_gate"]["required_for_route_promotion"])} common promotion requirements
            preserve the boundary between a plausible idea and an authorized research route.</p>
          <a href="{esc(repo_url(product, 'repo/ECDLP_DECISION_SUBSTRATE.json'))}">Open the canonical decision contract</a>
        </li>
      </ol>
    </div>
  </section>

  <section class="band reference-deployment" id="reference" aria-labelledby="reference-title">
    <div class="shell">
      <div class="reference-deployment__intro">
        <div class="section-heading">
          <p class="eyebrow">ECDLP reference deployment</p>
          <h2 id="reference-title">A hard testbed for durable research memory.</h2>
          <p>secp256k1 is precise, technically demanding, and rich in formal proofs, experiments,
            threat-model boundaries, failed routes, and unresolved gaps. That makes it a useful test of
            whether research state can remain inspectable over a long-running program.</p>
          <p><strong>The boundary is explicit:</strong> no secp256k1 break, shortcut, or validated
            subgeneric route is claimed.</p>
          <div class="actions">
            <a class="button button--primary" href="explore.html">Explore the ECDLP route map</a>
            <a class="button" href="dashboard.html">Open the technical workspace</a>
          </div>
        </div>
        <aside class="reference-snapshot" aria-labelledby="reference-snapshot-title">
          <span class="reference-snapshot__label">Current generated state</span>
          <h3 id="reference-snapshot-title">What the reference deployment demonstrates</h3>
          <dl>
            <div><dt>ECDLP proof ledger</dt><dd><strong data-metric="ledger-rows">{stats["ledger_rows"]}</strong> rows</dd></div>
            <div><dt>Distinct ECDLP results</dt><dd><strong data-metric="distinct-results">~{stats["distinct_results"]}</strong> results</dd></div>
            <div><dt>Route memory</dt><dd><strong>{len(routes)}</strong> named routes evaluated</dd></div>
            <div><dt>Current route decision</dt><dd><strong>{len(promoted_routes)}</strong> promoted routes</dd></div>
            <div><dt>Current experiment state</dt><dd><strong data-metric="native-experiments">{engine["counts"]["selected_explorations"]}</strong> native experiments selected</dd></div>
            <div><dt>Consumed bounded run</dt><dd><code>{esc(decisions["bounded_experiment_authorization"]["authorization_id"])}</code></dd></div>
          </dl>
          <p>Negative and barrier results are retained because they narrow what should be tried next;
            they are not claims that every wider approach is impossible.</p>
        </aside>
      </div>
      <div class="capability-grid">
        {capabilities_html}
      </div>
    </div>
  </section>

  <section class="band band--white" aria-labelledby="stage-title">
    <div class="shell">
      <div class="section-heading section-heading--wide">
        <p class="eyebrow">Current stage</p>
        <h2 id="stage-title">Built today and still being developed are deliberately separate.</h2>
      </div>
      <div class="stage-grid">
        <article class="stage-card stage-card--now">
          <span>{status_badge("green", "Exists today")}</span>
          <h3>Public reference system</h3>
          <ul class="check-list">{current_html}</ul>
        </article>
        <article class="stage-card stage-card--next">
          <span>{status_badge("amber", "Not yet")}</span>
          <h3>Hosted, configurable product</h3>
          <ul class="check-list check-list--not">{not_yet_html}</ul>
        </article>
      </div>
    </div>
  </section>

  <section class="band collaboration" id="collaboration" aria-labelledby="collaboration-title">
    <div class="shell collaboration__grid">
      <div>
        <p class="eyebrow">For researchers and AI labs</p>
        <h2 id="collaboration-title">Inspect the evidence—or help test the workflow.</h2>
        <p>KeyAI is recruiting one formal-research team to test orientation in the current workspace,
          map one repeated research-state problem, and reach an explicit build, change, stop, or pending decision.</p>
        <p class="collaboration__boundary">No external pilot session has been completed or recorded.
          Interest is not counted as adoption, retention, or product validation.</p>
        <div class="actions">
          <a class="button button--light" href="pilot.html">Read the collaboration protocol</a>
          <a class="text-link text-link--light" href="{esc(pilot_intake_url(product))}">Open the public GitHub intake</a>
        </div>
      </div>
      <dl class="collaboration__facts">
        <div><dt>Pilot status</dt><dd>{esc(pilot_model["status"].title())}</dd></div>
        <div><dt>Planned session</dt><dd>{sum(item["minutes"] for item in pilot["session_plan"])} minutes</dd></div>
        <div><dt>Completed discovery</dt><dd>{completed_discovery}</dd></div>
      </dl>
    </div>
  </section>

  <section class="band band--muted mvp-band" id="mvp" aria-labelledby="mvp-title">
    <div class="shell mvp-layout">
      <div class="section-heading">
        <p class="eyebrow">The next product milestone</p>
        <h2 id="mvp-title">Another team must complete the loop.</h2>
        <p>{esc(mvp["definition"])} A technical MVP still would not establish repeatable demand or willingness to pay.</p>
      </div>
      <ol class="mvp-metrics">{metric_html}</ol>
    </div>
  </section>
</main>
{site_footer(product)}"""


def build_results(
    product: dict,
    verified_index: dict,
    decisions: dict,
    engine: dict,
    researchos_scopes: dict[str, str],
) -> str:
    counts = verified_index["counts"]
    results = verified_index["results"]
    repository = product["repository_url"].rstrip("/")
    authorization = decisions["bounded_experiment_authorization"]

    def reference_link(reference: dict) -> str:
        source_file = reference.get("file", "")
        declaration = reference.get("declaration", "declaration")
        line = reference.get("line")
        if not source_file:
            return f'<code>{esc(declaration)}</code>'
        anchor = f"#L{line}" if line else ""
        url = f"{repository}/blob/main/{source_file}{anchor}"
        line_label = f":{line}" if line else ""
        return (
            f'<a class="result-source" href="{esc(url)}">'
            f'<code>{esc(declaration)}</code>'
            f'<span>{esc(source_file)}{line_label}</span></a>'
        )

    cards: list[str] = []
    for result in results:
        lane = result["lane"]
        trust = result["trust_level"]
        domain = result["domain"]
        lane_label = "ECDLP" if lane == "ecdlp" else "ResearchOS"
        trust_label = {
            "kernel_plus_compiler": "Kernel + compiler",
            "kernel_standard": "Kernel standard",
            "kernel_audited": "Kernel audited",
        }[trust]
        title = result.get("title") or result["claim_id"]
        title = re.sub(r"^\*\(([^)]+)\)\*\s*", r"\1 · ", title).replace("`", "")
        full_claim = result["claim_id"]
        display = (result.get("display") or "Declaration group").replace("`", "")
        ledger_scope = researchos_scopes.get(full_claim, "") if lane == "researchos" else ""
        if lane == "researchos" and not ledger_scope:
            raise ValueError(f"missing ResearchOS ledger scope for {full_claim}")
        claim_details = ""
        if lane == "ecdlp" and full_claim != title:
            claim_details = (
                '\n  <details class="result-card__scope"><summary>Full ledger claim and scope</summary>'
                f'<p>{esc(full_claim)}</p></details>'
            )
        ledger_scope_html = ""
        if ledger_scope:
            ledger_scope_html = (
                '\n  <div class="result-card__ledger-scope"><strong>Ledger scope</strong>'
                f'<p>{esc(ledger_scope)}</p></div>'
            )
        sources = "".join(reference_link(reference) for reference in result["references"])
        if not sources:
            sources = "".join(
                f'<a class="result-source" href="{esc(repo_url(product, source_file))}">'
                f'<code>{esc(source_file)}</code><span>declared source</span></a>'
                for source_file in result["files"]
            )
        cards.append(
            f"""<article class="result-card" id="{esc(result['slug'])}"
  data-result-tags="{esc(f'{lane} {trust} {domain}')}">
  <div class="result-card__top">
    <div class="result-card__badges">
      <span class="lane-badge lane-badge--{esc(lane)}">{lane_label}</span>
      <span class="trust-badge trust-badge--{esc(trust)}">{trust_label}</span>
    </div>
    <a class="result-card__anchor" href="#{esc(result['slug'])}" aria-label="Permanent link to {esc(title)}">#</a>
  </div>
  <h3>{esc(title)}</h3>
  <p class="result-card__display"><code>{esc(display)}</code></p>{ledger_scope_html}{claim_details}
  <dl class="result-card__meta">
    <div><dt>Domain</dt><dd>{esc(domain)}</dd></div>
    <div><dt>Method</dt><dd>{esc(result['method'])}</dd></div>
    <div><dt>Canonical ledger</dt><dd><a href="{esc(repo_url(product, result['source_ledger']))}">{esc(result['source_ledger'])}</a></dd></div>
  </dl>
  <div class="result-card__sources">{sources}</div>
</article>"""
        )

    filter_buttons = "".join(
        f'<button class="filter-button" type="button" data-result-filter="{token}" '
        f'aria-pressed="{str(index == 0).lower()}">{label}</button>'
        for index, (token, label) in enumerate(
            [
                ("all", "All results"),
                ("ecdlp", f"ECDLP {counts['ecdlp_rows']}"),
                ("researchos", f"ResearchOS {counts['researchos_rows']}"),
                ("kernel_standard", f"Kernel standard {counts['kernel_standard_rows']}"),
                ("kernel_audited", f"Kernel audited {counts['kernel_audited_rows']}"),
                (
                    "kernel_plus_compiler",
                    f"Kernel + compiler {counts['kernel_plus_compiler_rows']}",
                ),
            ]
        )
    )
    domain_rows = "".join(
        f"<li><span>{esc(domain)}</span><strong>{count}</strong></li>"
        for domain, count in counts["domains"].items()
    )
    evidence_types = [
        (
            "formal",
            "Formally proved",
            "Lean accepted the exact built declaration. This establishes the encoded statement under its assumptions—not semantic faithfulness, empirical validity, or practical impact.",
            "#result-browser",
            "Browse formal results",
        ),
        (
            "replayed",
            "Independently replayed",
            "A separate validator path recomputed a certificate or result from pinned artifacts. Replay is not automatically a kernel proof, peer review, or external institutional reproduction.",
            "dashboard.html#overview",
            f"Inspect the {esc(authorization['status'])} bounded run",
        ),
        (
            "empirical",
            "Empirical",
            "Observed under named instances, controls, and budgets. It does not establish an asymptotic result or transfer automatically to a real-world target.",
            "dashboard.html#overview",
            "See bounded evidence",
        ),
        (
            "negative",
            "Scoped negative",
            "A specific mechanism or prediction failed, or was inapplicable, inside a declared scope. The wider route may remain open.",
            "explore.html",
            f"Inspect {engine['counts']['outcomes_by_taxonomy']['bounded_negative']} retained bounded negatives",
        ),
        (
            "open",
            "Proposal / open",
            "A research question or mechanism awaits evidence, review, or authorization. It is non-executable and is not a result.",
            "dashboard.html#activity",
            "Open the governed queues",
        ),
    ]
    evidence_type_html = "".join(
        f"""<article class="evidence-type evidence-type--{esc(kind)}">
  <span class="evidence-type__marker" aria-hidden="true"></span>
  <h3>{esc(label)}</h3>
  <p>{esc(explanation)}</p>
  <a href="{esc(href)}">{esc(link_label)}</a>
</article>"""
        for kind, label, explanation, href, link_label in evidence_types
    )
    rh_rows = counts["domains"].get("riemann-hypothesis", 0)

    description = (
        "Browse every ledgered, machine-checked KeyAI result with its source file, "
        "method, trust label, and canonical ledger boundary."
    )
    return f"""{page_head("Verified results | KeyAI", description, "results.html")}
<body data-page="results">
{site_header(product)}
<main id="main">
  <section class="results-mast">
    <div class="shell results-mast__inner">
      <div>
        <p class="eyebrow">Inspectable proof surface</p>
        <h1>Verified results, with the evidence attached.</h1>
        <p>{description}</p>
      </div>
      <dl class="results-summary" aria-label="Verified result counts">
        <div><dt>ECDLP lane</dt><dd>{counts["ecdlp_rows"]}</dd></div>
        <div><dt>ResearchOS lane</dt><dd>{counts["researchos_rows"]}</dd></div>
        <div><dt>Navigation total</dt><dd>{counts["navigation_rows_total"]}</dd></div>
      </dl>
    </div>
  </section>

  <section class="results-boundary" aria-labelledby="results-boundary-title">
    <div class="shell results-boundary__inner">
      <div>
        <p class="eyebrow">Trust boundary</p>
        <h2 id="results-boundary-title">One browser, two isolated ledgers.</h2>
      </div>
      <p><strong>VERIFIED.md</strong> remains the canonical ECDLP ledger and alone feeds
        ECDLP headline statistics. <strong>VERIFIED_RESEARCHOS.md</strong> remains the canonical
        non-ECDLP ledger. The combined count is navigation only and is not an ECDLP security metric.</p>
    </div>
  </section>

  <section class="band evidence-guide" aria-labelledby="evidence-guide-title">
    <div class="shell">
      <div class="section-heading section-heading--wide">
        <p class="eyebrow">What “verified” means here</p>
        <h2 id="evidence-guide-title">Evidence status and trust path answer different questions.</h2>
        <p>Status says what kind of evidence exists. Trust labels say which checker path a formal row
          used. Neither label silently expands the scope of the underlying claim.</p>
      </div>
      <div class="evidence-type-grid">{evidence_type_html}</div>
      <aside class="trust-axis" aria-labelledby="trust-axis-title">
        <h3 id="trust-axis-title">Formal trust labels</h3>
        <dl>
          <div><dt><span class="trust-badge trust-badge--kernel_standard">Kernel standard</span></dt>
            <dd>A ResearchOS row declares the standard kernel trust base.</dd></div>
          <div><dt><span class="trust-badge trust-badge--kernel_audited">Kernel audited</span></dt>
            <dd>An ECDLP declaration passed the allowed-TCB audit; this index does not infer a standard-only base.</dd></div>
          <div><dt><span class="trust-badge trust-badge--kernel_plus_compiler">Kernel + compiler</span></dt>
            <dd>Ledger metadata discloses <code>native_decide</code> or equivalent compiler trust.</dd></div>
        </dl>
      </aside>
      <aside class="domain-boundary" aria-labelledby="rh-boundary-title">
        <div>
          <p class="eyebrow">Exploratory domain boundary</p>
          <h3 id="rh-boundary-title">Riemann Hypothesis rows are foundation interfaces—not a proof candidate.</h3>
          <p>The {rh_rows} ResearchOS rows in this domain are exact built declarations, including
            definitions, reformulations, and symmetry infrastructure. The repository claims no selected
            route, no authorized route execution, no proof candidate, and no progress on RH itself.</p>
        </div>
        <a class="button" href="{esc(repo_url(product, 'domains/riemann-hypothesis/README.md'))}">Read the canonical RH boundary</a>
      </aside>
    </div>
  </section>

  <div class="band band--white results-browser" id="result-browser">
    <div class="shell results-layout">
      <aside class="results-sidebar" aria-label="Result filters">
        <h2 id="result-browser-title">Browse formal results</h2>
        <p>Search exact claims, declarations, files, domains, and proof methods.</p>
        <label class="filter-search">
          <span>Search results</span>
          <input type="search" data-result-search placeholder="Claim, theorem, file, method"
            autocomplete="off" aria-controls="result-list">
        </label>
        <div class="filter-list" role="group" aria-label="Filter verified results">{filter_buttons}</div>
        <p class="filter-count" data-result-count aria-live="polite">{counts["navigation_rows_total"]} results</p>
        <div class="results-domain-summary">
          <h3>Domains</h3>
          <ul>{domain_rows}</ul>
        </div>
        <p class="results-sidebar__note">The complete list remains in the HTML and readable without
          JavaScript. Filters change only the current view.</p>
      </aside>
      <div>
        <noscript><p class="noscript-note">JavaScript is off, so all results are shown. Browser find remains available.</p></noscript>
        <div class="results-list" id="result-list" data-result-list>{''.join(cards)}</div>
        <p class="empty-state" data-result-empty role="status" aria-live="polite" hidden>No verified results match this filter.</p>
      </div>
    </div>
  </div>
</main>
{site_footer(product)}"""


def route_distribution(routes: list[dict]) -> tuple[str, str]:
    counts = Counter(route["status"] for route in routes)
    total = len(routes) or 1
    segments = []
    legend = []
    for status in ROUTE_STATUS_ORDER:
        count = counts.get(status, 0)
        if not count:
            continue
        label, css_status = ROUTE_STATUS[status]
        width = count / total * 100
        segments.append(
            f'<span class="distribution__segment segment--{esc(css_status)}" '
            f'style="width:{width:.3f}%" title="{esc(label)}: {count}"></span>'
        )
        legend.append(
            f'<span class="legend-item"><i class="segment--{esc(css_status)}"></i>'
            f'{esc(label)} <strong>{count}</strong></span>'
        )
    return "".join(segments), "".join(legend)


def build_dashboard(
    product: dict,
    stats: dict,
    frontier: dict,
    decisions: dict,
    formal: dict,
    graph: dict,
    engine: dict,
    tasks: list[dict[str, str]],
) -> str:
    selection = decisions["route_selection"]
    authorization = decisions["bounded_experiment_authorization"]
    selected_structural = selection.get("selected_route_ids", [])
    promoted_routes = selection.get("promoted_route_ids", [])
    routes = decisions["routes"]
    distribution_html, legend_html = route_distribution(routes)
    task_rows = [
        (
            task,
            f"""<article class="task-row">
  <div class="task-row__top"><div><h3>{esc(task["id"])} · {esc(task["title"])}</h3>
    <small>{esc(task["queue_label"])}</small>
    <p>{esc(task["why"])}</p></div>{task_status_badge(task["status"])}</div>
</article>""",
        )
        for task in tasks
    ]
    task_html = "".join(row for _task, row in task_rows)
    active_task_html = "".join(
        row for task, row in task_rows if task["status"].startswith("active")
    ) or '<p class="empty-state">No task contract is currently active.</p>'
    route_rows = "".join(
        f"""<tr>
  <td><strong>{esc(route["title"])}</strong><small>{esc(route["id"])}</small></td>
  <td>{status_badge(route["status"])}</td>
  <td>{esc(", ".join(route.get("threat_models", [])))}</td>
  <td>{esc(route.get("priority", "unassigned"))}</td>
  <td>{esc(route.get("next_action", ""))}</td>
</tr>"""
        for route in routes
    )
    formal_rows = "".join(
        f"""<tr>
  <td><strong>{esc(node["title"])}</strong><small>{esc(node["id"])}</small></td>
  <td>{status_badge(node["status"])}</td>
  <td>{esc(", ".join(node.get("depends_on", [])) or "none")}</td>
  <td>{esc(", ".join(node.get("blocker_ids", [])) or "none")}</td>
  <td>{evidence_links(product, node.get("evidence_files", []), limit=2)}</td>
</tr>"""
        for node in formal["critical_nodes"]
    )
    blocker_rows = "".join(
        f"""<tr>
  <td><strong>{esc(blocker["title"])}</strong><small>{esc(blocker["kind"])}</small></td>
  <td>{esc(blocker["description"])}</td>
  <td>{esc(blocker["resume_condition"])}</td>
</tr>"""
        for blocker in formal["blockers"]
    )
    decision_reasons = "".join(f"<li>{esc(item)}</li>" for item in selection["rationale"])
    triggers = "".join(f"<li>{esc(item)}</li>" for item in selection["reconsideration_triggers"])
    phase_policy = decisions["phase_policy"]
    graph_counts = graph["counts"]
    engine_counts = engine["counts"]
    engine_gates = engine["gate_status"]
    research_task_count = sum(task["queue"] == "research" for task in tasks)
    product_task_count = sum(task["queue"] == "product" for task in tasks)
    closed_count = sum(node["status"] == "closed" for node in formal["critical_nodes"])
    engine_sequence_html = "".join(
        f"""<article class="task-row">
  <div class="task-row__top"><div><h3>{candidate["position"]:02d} · {esc(candidate["title"])}</h3>
    <small>{esc(candidate["candidate_id"])} · {esc(candidate["kind"])}</small>
    <p>{esc(candidate["stop_condition"])}</p></div>
    {engine_execution_badge(candidate["execution_state"])}</div>
</article>"""
        for candidate in engine["selected_sequence"]
    )
    if not engine_sequence_html:
        engine_sequence_html = (
            '<div class="empty-state"><strong>No native Engine candidate clears every '
            "scientific gate.</strong><p>The native queue remains empty; the exact "
            "external TASK-026 singleton is governed by the decision substrate. A future "
            "native candidate still requires both an exact mechanism and an "
            "independent raw-artifact validator.</p></div>"
        )
    intake_candidates = [
        candidate
        for candidate in engine["hard_rejected_candidates"]
        if candidate.get("disposition") == "intake_blocked"
    ]
    engine_intake_html = "".join(
        f"""<article class="task-row">
  <div class="task-row__top"><div><h3>{esc(candidate["title"])}</h3>
    <small>{esc(candidate["candidate_id"])}</small>
    <p>{esc("; ".join(reason.replace("_", " ") for reason in candidate["reasons"]))}</p></div>
    {status_badge("amber", "Intake")}</div>
</article>"""
        for candidate in intake_candidates
    )
    engine_intake_section = (
        f"""<div class="panel-heading"><div><h2>Blocked research intake</h2>
        <p>{len(intake_candidates)} proposals are retained with explicit reopening
        requirements; none is executable.</p></div></div>
      <div class="surface" style="margin-bottom:22px"><div class="surface__body">{engine_intake_html}</div></div>"""
        if intake_candidates
        else ""
    )
    generation = engine["hypothesis_generation"]
    generation_status = {
        "proposal_required": ("blue", "Proposal"),
        "desk_cost_bridge_required": ("amber", "Desk cost"),
        "property_resolution_required": ("amber", "Property resolution"),
    }
    generation_seed_html = "".join(
        f"""<article class="task-row">
  <div class="task-row__top"><div><h3>{esc(seed["research_question"])}</h3>
    <small>{esc(seed["seed_id"])} · {esc(seed["cell_id"])} · {esc(seed["route_id"])}</small>
    <p>{esc(seed["typed_cell"]["boundary"])}</p></div>
    {status_badge(*generation_status[seed["status"]])}</div>
</article>"""
        for seed in generation["generated_seeds"]
    )
    typed_counts = generation["typed_evidence"]["counts"]
    generation_section = f"""
      <div class="panel-heading"><div><h2>Typed research questions</h2>
        <p>{typed_counts["cells"]} mechanism/property cells;
          {typed_counts["decided_inapplicable_cells"] + typed_counts["decided_closed_cells"]} decided at desk;
          {generation["counts"]["generated_seeds"]} seed-eligible questions;
          {generation["counts"]["submitted_proposals"]} submitted;
          {generation["counts"]["quality_cleared_proposals"]} quality-cleared.
          Typed screens, seeds, and drafts authorize nothing.</p></div>
        <a href="{esc(repo_url(product, 'repo/ECDLP_TYPED_EVIDENCE_V0.json'))}">Open evidence</a></div>
      <div class="surface" style="margin-bottom:22px"><div class="surface__body">{generation_seed_html}</div></div>"""

    health_cards = [
        (
            "Canonical counts",
            f'{stats["ledger_rows"]} ledger rows / ~{stats["distinct_results"]} distinct',
            ["data/stats.json", "scripts/check_status_consistency.py"],
            "closed",
        ),
        (
            "Decision state",
            f"{len(selected_structural)} structural route completed / "
            f"{len(promoted_routes)} promoted / 1 exact toy run completed",
            ["repo/ECDLP_DECISION_SUBSTRATE.json", "scripts/check_ecdlp_decision_substrate.py"],
            "blue",
        ),
        (
            "Research Engine gates",
            (
                f'{engine_counts["typed_evidence_cells"]} typed cells / '
                f'{engine_counts["generated_hypothesis_seeds"]} seeds / '
                f'{engine_counts["selected_explorations"]} bounded experiments'
            ),
            [
                "repo/RESEARCH_ENGINE_V0.json",
                "repo/ECDLP_TYPED_EVIDENCE_V0.json",
                "repo/HYPOTHESIS_GENERATION_V0.json",
                "scripts/check_research_engine.py",
            ],
            "blue",
        ),
        (
            "Generated closure",
            f'{graph_counts["theorems"]} theorem nodes in the knowledge graph',
            ["repo/ARTIFACTS.yaml", "scripts/check_repo_artifacts.py"],
            "closed",
        ),
        (
            "Product boundary",
            product["current_stage"]["label"],
            ["repo/PRODUCT_MODEL.json", "scripts/check_product_model.py"],
            "blue",
        ),
    ]
    health_html = "".join(
        f"""<article class="surface">
  <div class="surface__head"><div><h3>{esc(label)}</h3><p>{esc(value)}</p></div>{status_badge(status, "OK")}</div>
  <div class="surface__body">{evidence_links(product, paths)}</div>
</article>"""
        for label, value, paths, status in health_cards
    )
    description = (
        "The live KeyAI operator workspace for the secp256k1 ECDLP reference environment: "
        "decision routes, formal state, evidence, tasks, and trust boundaries."
    )
    return f"""{page_head("KeyAI Workspace | secp256k1 reference environment", description, "dashboard.html")}
<body data-page="workspace">
{site_header(product)}
<main id="main">
  <section class="workspace-mast">
    <div class="shell">
      <p class="breadcrumb">Reference workspace / secp256k1 ECDLP</p>
      <div class="workspace-title">
        <div><h1>secp256k1 research state</h1>
          <p>One operator view for the current decision, formal substrate, evidence, active work,
            and generated trust checks.</p></div>
        <div class="snapshot">Canonical snapshot
          <code>snapshot {stats["ledger_rows"]} ledger rows / ~{stats["distinct_results"]} distinct</code></div>
      </div>
      <div class="boundary-notice"><strong>Scope boundary.</strong>
        {esc(product["reference_environment"]["boundary"])}
        Monitoring means new evidence can reopen a route; it does not mean impossibility was proved.</div>
      <div class="workspace-metrics">
        <div class="workspace-metric"><div class="workspace-metric__value">{stats["ledger_rows"]}</div><div class="workspace-metric__label">ledger rows</div></div>
        <div class="workspace-metric"><div class="workspace-metric__value">~{stats["distinct_results"]}</div><div class="workspace-metric__label">distinct results</div></div>
        <div class="workspace-metric"><div class="workspace-metric__value">{stats["proved_modules"]}</div><div class="workspace-metric__label">proved modules</div></div>
        <div class="workspace-metric"><div class="workspace-metric__value">{frontier["meta"]["corpus_claims"]}</div><div class="workspace-metric__label">corpus claims</div></div>
        <div class="workspace-metric"><div class="workspace-metric__value">{len(routes)}</div><div class="workspace-metric__label">routes evaluated</div></div>
        <div class="workspace-metric"><div class="workspace-metric__value">{engine_counts["typed_evidence_cells"]}</div><div class="workspace-metric__label">typed cells</div></div>
        <div class="workspace-metric"><div class="workspace-metric__value">{engine_counts["generated_hypothesis_seeds"]}</div><div class="workspace-metric__label">generated seeds</div></div>
        <div class="workspace-metric"><div class="workspace-metric__value">1</div><div class="workspace-metric__label">completed exact toy run</div></div>
      </div>
    </div>
  </section>

  <div class="tabbar-wrap">
    <div class="shell tabbar" role="tablist" aria-label="Workspace views" data-tabs>
      <a role="tab" id="tab-overview" href="#overview" aria-controls="overview" aria-selected="true" data-tab="overview">Overview</a>
      <a role="tab" id="tab-routes" href="#routes" aria-controls="routes" aria-selected="false" data-tab="routes">Routes</a>
      <a role="tab" id="tab-formal" href="#formal" aria-controls="formal" aria-selected="false" data-tab="formal">Formal substrate</a>
      <a role="tab" id="tab-evidence" href="#evidence" aria-controls="evidence" aria-selected="false" data-tab="evidence">Evidence</a>
      <a role="tab" id="tab-activity" href="#activity" aria-controls="activity" aria-selected="false" data-tab="activity">Queue</a>
    </div>
  </div>

  <noscript><div class="shell noscript-note">JavaScript is off, so every workspace panel is shown in sequence.</div></noscript>

  <div class="shell workspace-body">
    <section class="tab-panel" role="tabpanel" id="overview" aria-labelledby="tab-overview" data-tab-panel="overview">
      <div class="panel-heading"><div><h2>Current operating state</h2>
        <p>The decision layer controls what work is justified; proof volume does not select an attack route.</p></div>
        {status_badge("blue", product["current_stage"]["label"])}</div>
      <article class="decision-band">
        <div class="decision-band__state"><span>{esc(authorization["authorization_id"])}</span><strong>Consumed toy run</strong></div>
        <div class="decision-band__copy"><h3>One hash-bound synthetic-toy diagnostic completed.</h3>
          <p>{esc(authorization["hypothesis_id"])} / {esc(authorization["task_id"])} only:
            {authorization["resource_budget"]["max_primary_trials"]} primary trials across
            {len(authorization["scope"]["curve_ids"])} frozen E_7 toy subgroups. Terminal:
            {esc(authorization["terminal_status"])}; rerun authorized:
            {str(authorization["rerun_authorized"]).lower()}. Native Engine selection,
            direct secp256k1 work, solvers, and promotion remain closed.
            Structural selection {esc(selection["decision_id"])} remains unchanged.</p></div>
      </article>
      <div class="panel-heading"><div><h2>Research Engine v0 queue</h2>
        <p>{engine_counts["selected_explorations"]} selected;
          {engine_counts["ready_explorations"]} ready. Positive toy evidence is supported,
          never proved; threat-model scope, route decision, and evidence remain separate.</p></div>
        {status_badge("amber", "Native queue closed")}</div>
      <div class="surface" style="margin-bottom:22px"><div class="surface__body">{engine_sequence_html}</div></div>
{engine_intake_section}
{generation_section}
      <div class="layout-two">
        <article class="surface">
          <div class="surface__head"><div><h3>Why this decision</h3><p>Canonical rationale, not a claim of impossibility</p></div></div>
          <div class="surface__body"><ul class="plain-list">{decision_reasons}</ul></div>
        </article>
        <aside class="surface">
          <div class="surface__head"><div><h3>Split work queues</h3><p>{research_task_count} research / {product_task_count} product contracts</p></div>
            <a href="{esc(repo_url(product, "tasks/NEXT.md"))}">Open source</a></div>
          <div class="surface__body">{active_task_html}</div>
        </aside>
      </div>
    </section>

    <section class="tab-panel" role="tabpanel" id="routes" aria-labelledby="tab-routes" data-tab-panel="routes">
      <div class="panel-heading"><div><h2>Route portfolio</h2>
        <p>All routes are bound to an exact threat model, evidence gate, stop condition, and next action.</p></div>
        <a class="button" href="explore.html">Open detailed route map</a></div>
      <div class="surface" style="margin-bottom:22px">
        <div class="surface__head"><div><h3>Disposition distribution</h3><p>{len(routes)} canonical routes</p></div></div>
        <div class="surface__body"><div class="distribution">{distribution_html}</div><div class="legend-list">{legend_html}</div></div>
      </div>
      <div class="table-wrap" tabindex="0" role="region" aria-label="ECDLP route portfolio table"><table class="data-table">
        <caption class="sr-only">ECDLP route portfolio</caption>
        <thead><tr><th>Route</th><th>Disposition</th><th>Threat model</th><th>Priority</th><th>Next action</th></tr></thead>
        <tbody>{route_rows}</tbody>
      </table></div>
    </section>

    <section class="tab-panel" role="tabpanel" id="formal" aria-labelledby="tab-formal" data-tab-panel="formal">
      <div class="panel-heading"><div><h2>Formal substrate</h2>
        <p>{closed_count} of {len(formal["critical_nodes"])} critical nodes are closed. Blocked nodes retain exact resume conditions.</p></div>
        <a class="button" href="{esc(repo_url(product, "repo/FORMAL_SUBSTRATE.json"))}">Open canonical map</a></div>
      <div class="table-wrap" tabindex="0" role="region" aria-label="Formal substrate table" style="margin-bottom:28px"><table class="data-table">
        <caption class="sr-only">Formal substrate critical nodes</caption>
        <thead><tr><th>Critical node</th><th>Status</th><th>Depends on</th><th>Blocker</th><th>Evidence</th></tr></thead>
        <tbody>{formal_rows}</tbody>
      </table></div>
      <div class="panel-heading"><div><h2>Accepted blockers</h2>
        <p>Missing foundations are recorded, but do not authorize work without a selected route.</p></div></div>
      <div class="table-wrap" tabindex="0" role="region" aria-label="Accepted blockers table"><table class="data-table">
        <caption class="sr-only">Accepted formal blockers and resume conditions</caption>
        <thead><tr><th>Blocker</th><th>What is missing</th><th>Resume condition</th></tr></thead>
        <tbody>{blocker_rows}</tbody>
      </table></div>
    </section>

    <section class="tab-panel" role="tabpanel" id="evidence" aria-labelledby="tab-evidence" data-tab-panel="evidence">
      <div class="panel-heading"><div><h2>Sync Health</h2>
        <p>The public and agent-facing views resolve back to canonical machine sources and their gates.</p></div></div>
      <div class="layout-two" style="margin-bottom:30px">{health_html}</div>
      <div class="layout-two">
        <article class="surface">
          <div class="surface__head"><div><h3>Reconsideration triggers</h3><p>What can legitimately reopen route selection</p></div></div>
          <div class="surface__body"><ul class="plain-list">{triggers}</ul></div>
        </article>
        <article class="surface">
          <div class="surface__head"><div><h3>Operating policy</h3><p>{esc(phase_policy["phase"])}</p></div></div>
          <div class="surface__body">
            <ul class="compact-list">
              <li><strong>Engine exploration capability</strong><span>{str(engine_gates["exploration_authorized"]).lower()}</span></li>
              <li><strong>Exact decision experiment</strong><span>{str(phase_policy["experiments_authorized"]).lower()} · consumed {esc(authorization["authorization_id"])}</span></li>
              <li><strong>Native decision exploration</strong><span>{str(phase_policy["bounded_exploration_authorized"]).lower()}</span></li>
              <li><strong>Structural routes</strong><span>{esc(", ".join(selected_structural) or "none")}</span></li>
              <li><strong>Promotion experiments</strong><span>{str(engine_gates["promotion_authorized"]).lower()}</span></li>
              <li><strong>Promoted route</strong><span>{esc(phase_policy["selected_attack_route"] or "none")}</span></li>
              <li><strong>Merge rule</strong><span>{esc(phase_policy["merge_rule"])}</span></li>
              <li><strong>Product claim policy</strong>{evidence_links(product, ["repo/PRODUCT_MODEL.json", "scripts/check_product_model.py"])}</li>
            </ul>
          </div>
        </article>
      </div>
    </section>

    <section class="tab-panel" role="tabpanel" id="activity" aria-labelledby="tab-activity" data-tab-panel="activity">
      <div class="panel-heading"><div><h2>Work queues</h2>
        <p>Research and product contracts have separate owners and KPIs; neither can count as progress in the other.</p></div>
        <a class="button" href="{esc(repo_url(product, "tasks/NEXT.md"))}">Open queue router</a></div>
      <div class="source-list" style="margin-bottom:18px">
        {evidence_links(product, ["tasks/ECDLP_RESEARCH.md", "tasks/KEYAI_PRODUCT.md"])}
      </div>
      <div class="surface"><div class="surface__body">{task_html}</div></div>
    </section>
  </div>
</main>
{site_footer(product)}"""


def build_explore(product: dict, stats: dict, decisions: dict, engine: dict) -> str:
    routes = decisions["routes"]
    selection = decisions["route_selection"]
    authorization = decisions["bounded_experiment_authorization"]
    selected_structural = selection.get("selected_route_ids", [])
    promoted_routes = selection.get("promoted_route_ids", [])
    counts = Counter(route["status"] for route in routes)
    filter_buttons = [
        f'<li><button class="filter-button" type="button" aria-pressed="true" data-route-filter="all">'
        f'<span>All routes</span><span>{len(routes)}</span></button></li>'
    ]
    for status in ROUTE_STATUS_ORDER:
        count = counts.get(status, 0)
        if not count:
            continue
        label, _css_status = ROUTE_STATUS[status]
        filter_buttons.append(
            f'<li><button class="filter-button" type="button" aria-pressed="false" '
            f'data-route-filter="{esc(status)}"><span>{esc(label)}</span><span>{count}</span></button></li>'
        )

    route_cards = []
    for route in routes:
        evidence = route.get("evidence_files", [])
        assumptions = route.get("assumptions", [])
        assumptions_text = "; ".join(assumptions) if assumptions else "No extra assumptions recorded."
        route_cards.append(
            f"""<details class="route-card" data-route-status="{esc(route["status"])}">
  <summary>
    <span class="route-title"><strong>{esc(route["title"])}</strong><code>{esc(route["id"])}</code></span>
    <span class="route-status">{status_badge(route["status"])}</span>
    <span class="route-meta"><strong>{esc(route.get("priority", "unassigned"))}</strong>
      {esc(", ".join(route.get("threat_models", [])))}</span>
  </summary>
  <div class="route-card__body">
    <section class="route-detail"><h3>Applicability</h3><p>{esc(route.get("applicability", ""))}</p></section>
    <section class="route-detail"><h3>Known cost</h3><p>{esc(route.get("known_cost", ""))}</p></section>
    <section class="route-detail"><h3>Current evidence</h3><p>{esc(route.get("current_evidence", ""))}</p></section>
    <section class="route-detail"><h3>Assumptions</h3><p>{esc(assumptions_text)}</p></section>
    <section class="route-detail"><h3>Success gate</h3><p>{esc(route.get("success_gate", ""))}</p></section>
    <section class="route-detail"><h3>Stop condition</h3><p>{esc(route.get("stop_condition", ""))}</p></section>
    <section class="route-detail route-detail--wide"><h3>Next action</h3><p>{esc(route.get("next_action", ""))}</p></section>
    <section class="route-detail route-detail--wide"><h3>Evidence files</h3>{evidence_links(product, evidence)}</section>
  </div>
</details>"""
        )
    description = (
        "A canonical, searchable map of all recorded routes in the ECDLP portfolio for the plain "
        "single-target secp256k1 objective, including scope, evidence, gates, and stop conditions."
    )
    return f"""{page_head("KeyAI Route Map | secp256k1 ECDLP", description, "explore.html")}
<body data-page="routes">
{site_header(product)}
<main id="main">
  <section class="explorer-mast">
    <div class="shell explorer-mast__title">
      <div><p class="eyebrow">Canonical decision explorer</p>
        <h1>secp256k1 ECDLP route map</h1>
        <p>This is the detailed route memory for KeyAI's public reference deployment. Every route is
          generated from <code>repo/ECDLP_DECISION_SUBSTRATE.json</code>; no status silently closes a wider claim.</p></div>
      <aside class="decision-inline"><strong>{esc(selection["decision_id"])} · Structural selection</strong>
        <span>{len(selected_structural)} structural route completed; {len(promoted_routes)} promoted;
          1 exact synthetic-toy run completed under
          {esc(authorization["authorization_id"])}; 0 native experiments selected.</span></aside>
    </div>
  </section>

  <div class="shell explorer-layout">
    <aside class="explorer-sidebar" aria-label="Route filters">
      <h2>Disposition</h2>
      <ul class="filter-list">{"".join(filter_buttons)}</ul>
      <h2><label for="route-search">Search</label></h2>
      <input class="route-search" id="route-search" type="search" placeholder="GLV, leakage, pairing..."
        autocomplete="off" data-route-search aria-controls="route-list">
      <p style="margin-top:18px"><span data-metric="ledger-rows">{stats["ledger_rows"]}</span> verified ledger rows support the surrounding
        substrate. A formal result is not automatically an attack route.</p>
    </aside>

    <section class="explorer-results" aria-labelledby="route-results-title">
      <div class="explorer-results__head"><h2 id="route-results-title">Evaluated routes</h2>
        <span class="result-count" data-route-count aria-live="polite">{len(routes)} routes</span></div>
      <noscript><p class="noscript-note">JavaScript is off, so all routes are shown. Every route can still be opened.</p></noscript>
      <div class="route-list" id="route-list" data-route-list>{"".join(route_cards)}</div>
      <div class="empty-state" hidden data-route-empty role="status" aria-live="polite">No route matches this filter.</div>
    </section>
  </div>
</main>
{site_footer(product)}"""


def build_pilot(product: dict, pilot: dict) -> str:
    intake_url = pilot_intake_url(product)
    session_total = sum(item["minutes"] for item in pilot["session_plan"])
    completed_external_pilots = len(valid_second_projects(pilot))
    primary_hypothesis = next(
        item
        for item in product["customer_hypotheses"]
        if item["id"] == pilot["primary_hypothesis_id"]
    )
    role_html = "".join(
        f"<li>{esc(item)}</li>" for item in pilot["target_participant"]["roles"]
    )
    signal_html = "".join(
        f"<li>{esc(item)}</li>"
        for item in pilot["target_participant"]["required_signals"]
    )
    out_of_scope_html = "".join(
        f"<li>{esc(item)}</li>"
        for item in pilot["target_participant"]["out_of_scope"]
    )
    session_html = "".join(
        f"""<article class="pilot-step">
  <div class="pilot-step__meta"><span>{index:02d}</span><strong>{phase["minutes"]} min</strong></div>
  <div class="pilot-step__copy">
    <h3>{esc(phase["label"])}</h3>
    <p>{esc(phase["objective"])}</p>
    <p class="pilot-step__gate"><strong>Exit gate</strong>{esc(phase["exit_gate"])}</p>
  </div>
</article>"""
        for index, phase in enumerate(pilot["session_plan"], start=1)
    )
    measurement_rows = "".join(
        f"""<tr>
  <td><code>{esc(metric["id"])}</code><small>{esc(metric["kind"])}</small></td>
  <td>{esc(metric["operational_definition"])}</td>
  <td><strong>{esc(metric["target"])}</strong></td>
  <td>{esc(metric["evidence_source"])}</td>
</tr>"""
        for metric in pilot["measurements"]
    )
    decision_columns = "".join(
        f"""<section class="decision-rule decision-rule--{esc(outcome)}">
  <h3>{esc(outcome.title())}</h3>
  <ul>{''.join(f'<li>{esc(item)}</li>' for item in pilot["decision_rules"][outcome])}</ul>
</section>"""
        for outcome in ("build", "change", "stop", "pending")
    )
    prohibited_html = "".join(
        f"<li>{esc(item)}</li>"
        for item in pilot["privacy_and_safety"]["prohibited_inputs"]
    )
    description = (
        "The evidence-gated KeyAI external pilot for formal-research teams: "
        "qualification, observed orientation, workflow mapping, measures, and decision rules."
    )
    return f"""{page_head("KeyAI External Pilot | Test one research workflow", description, "pilot.html")}
<body data-page="pilot">
{site_header(product)}
<main id="main">
  <section class="pilot-mast" aria-labelledby="pilot-title">
    <div class="shell pilot-mast__inner">
      <div class="pilot-mast__copy">
        <p class="eyebrow">External pilot / {esc(pilot["task_id"])}</p>
        <h1 id="pilot-title">Bring one research workflow that keeps losing its state.</h1>
        <p>We will observe how your team understands the current KeyAI reference environment, map one
          repeated formal-research workflow, and decide whether a bounded TASK-012 adapter test is justified.</p>
        <div class="actions">
          <a class="button button--primary" href="{esc(intake_url)}">Apply on GitHub</a>
          <a class="button button--on-dark" href="{esc(repo_url(product, product["pilot"]["protocol_source"]))}">Inspect the protocol JSON</a>
        </div>
      </div>
      <aside class="pilot-state" aria-label="Pilot evidence state">
        <div><span>Status</span><strong>{esc(pilot["status"].title())}</strong></div>
        <div><span>Planned session</span><strong>{session_total} minutes</strong></div>
        <div><span>Completed external pilots</span><strong>{completed_external_pilots}</strong></div>
        <p>{esc(pilot["evidence_state"])}</p>
      </aside>
    </div>
  </section>

  <section class="pilot-safety" aria-label="Public intake boundary">
    <div class="shell pilot-safety__inner">
      <strong>Public and sanitized inputs only.</strong>
      <span>{esc(pilot["privacy_and_safety"]["public_intake"])}</span>
      <a href="#safety">Read the safety boundary</a>
    </div>
  </section>

  <section class="band band--white">
    <div class="shell split">
      <div class="split__lead">
        <p class="eyebrow">Who this is for</p>
        <h2>A team with a durable coordination problem, not a one-off proof request.</h2>
        <p>{esc(pilot["purpose"])}</p>
        <p class="pilot-primary"><strong>Primary hypothesis {esc(primary_hypothesis["id"])}</strong>
          {esc(primary_hypothesis["user"])}</p>
        <ul class="role-list">{role_html}</ul>
      </div>
      <div class="qualification">
        <section>
          <h3>Signals we need</h3>
          <ul class="check-list">{signal_html}</ul>
        </section>
        <section>
          <h3>Outside this pilot</h3>
          <ul class="check-list check-list--not">{out_of_scope_html}</ul>
        </section>
      </div>
    </div>
  </section>

  <section class="band">
    <div class="shell">
      <div class="section-heading">
        <p class="eyebrow">Session plan</p>
        <h2>A {session_total}-minute path from qualification to an explicit decision.</h2>
        <p>The first session tests orientation and problem fit. It does not count a scheduled follow-up
          or polite interest as product validation.</p>
      </div>
      <div class="pilot-steps">{session_html}</div>
    </div>
  </section>

  <section class="band band--muted">
    <div class="shell">
      <div class="section-heading">
        <p class="eyebrow">Measurement contract</p>
        <h2>Behavior first. Claims only after evidence.</h2>
        <p>Every measure has an operational definition, target, and evidence source. The pilot remains
          recruiting until an external session is actually recorded.</p>
      </div>
      <div class="table-wrap pilot-measures" tabindex="0" role="region" aria-label="Pilot measurement contract"><table class="data-table">
        <caption class="sr-only">Pilot measurements, targets, and evidence sources</caption>
        <thead><tr><th>Measure</th><th>What is observed</th><th>Target</th><th>Evidence</th></tr></thead>
        <tbody>{measurement_rows}</tbody>
      </table></div>
    </div>
  </section>

  <section class="band band--white">
    <div class="shell">
      <div class="section-heading">
        <p class="eyebrow">Decision contract</p>
        <h2>Discovery ends with build, change, stop, or pending.</h2>
        <p>{esc(pilot["decision_rules"]["minimum_evidence"])}</p>
      </div>
      <div class="decision-rules">{decision_columns}</div>
    </div>
  </section>

  <section class="band pilot-boundary" id="safety">
    <div class="shell split">
      <div class="split__lead">
        <p class="eyebrow">Safety and scope</p>
        <h2>No secrets belong in the intake.</h2>
        <p>{esc(pilot["privacy_and_safety"]["reference_boundary"])}</p>
        <dl class="scope-contract">
          <div><dt>TASK-011 authority</dt><dd>{esc(pilot["privacy_and_safety"]["task_authority"])}</dd></div>
          <div><dt>Experiment gate</dt><dd>{esc(pilot["privacy_and_safety"]["experiment_gate"])}</dd></div>
          <div><dt>Evidence retention</dt><dd>{esc(pilot["privacy_and_safety"]["retention_policy"])}</dd></div>
        </dl>
      </div>
      <div>
        <h3>Never submit</h3>
        <ul class="check-list check-list--not">{prohibited_html}</ul>
      </div>
    </div>
  </section>

  <section class="pilot-cta">
    <div class="shell pilot-cta__inner">
      <div><p class="eyebrow">Recruiting now</p>
        <h2>One real workflow is more valuable than another speculative feature.</h2>
        <p>Open the public intake with a repeated failure, current verifier, and a safe project boundary.</p></div>
      <a class="button button--light" href="{esc(intake_url)}">Start the pilot intake</a>
    </div>
  </section>
</main>
{site_footer(product)}"""


def build_robots() -> str:
    return f"""User-agent: *
Allow: /

Sitemap: {site_origin()}/sitemap.xml
"""


def build_sitemap() -> str:
    origin = site_origin()
    urls = "\n".join(
        f"  <url><loc>{esc(f'{origin}/{path}' if path else f'{origin}/')}</loc></url>"
        for path, _label in PUBLIC_PAGES
    )
    return f"""<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
{urls}
</urlset>"""


def main() -> int:
    product = load_json(PRODUCT_PATH)
    pilot = load_json(PILOT_PATH)
    stats = load_json(STATS_PATH)
    frontier = load_json(FRONTIER_PATH)
    decisions = load_json(DECISION_PATH)
    formal = load_json(FORMAL_PATH)
    graph = load_json(GRAPH_PATH)
    engine = load_json(ENGINE_PATH)
    verified_index = load_json(VERIFIED_INDEX_PATH)
    tasks = parse_tasks()

    index = build_index(
        product, pilot, stats, frontier, decisions, formal, engine, verified_index
    )
    results_page = build_results(
        product, verified_index, decisions, engine, researchos_claim_scopes()
    )
    dashboard = build_dashboard(
        product, stats, frontier, decisions, formal, graph, engine, tasks
    )
    explore = build_explore(product, stats, decisions, engine)
    pilot_page = build_pilot(product, pilot)
    write_text(INDEX_PATH, index)
    write_text(RESULTS_PATH, results_page)
    write_text(DASHBOARD_PATH, dashboard)
    write_text(EXPLORE_PATH, explore)
    write_text(PILOT_OUTPUT_PATH, pilot_page)
    write_text(ROBOTS_PATH, build_robots())
    write_text(SITEMAP_PATH, build_sitemap())

    print(
        "wrote KeyAI public site: "
        f"{stats['ledger_rows']} ECDLP ledger rows, "
        f"{verified_index['counts']['researchos_rows']} ResearchOS ledger rows, "
        f"{len(decisions['routes'])} decision routes, "
        f"{len(formal['critical_nodes'])} formal nodes, "
        f"{len(tasks)} task contracts, "
        f"{engine['counts']['selected_explorations']} bounded explorations, "
        f"pilot {pilot['status']}, sitemap {len(PUBLIC_PAGES)} pages"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
