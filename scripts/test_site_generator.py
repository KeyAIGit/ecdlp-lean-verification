#!/usr/bin/env python3
"""Regression tests for canonical task parsing in generated site views."""
from __future__ import annotations

import re
import unittest

import site_generator


class TaskParserTests(unittest.TestCase):
    def test_metadata_between_required_fields_does_not_merge_tasks(self) -> None:
        text = """\
### TASK-009 - Completed structural task

Status: completed_bounded_structural
Structural lane: completed
Decision: RS-TEST-001
Hypothesis: HYP-009
Foundation: F-TEST
Kind: theorem | research
Why it matters: This result is complete.
Inputs:
- input

### TASK-010 - Active audit

Status: active_remediation_draft
Kind: review | ops
Hypothesis: none
Why it matters: This audit is active.
Inputs:
- input
"""
        tasks = site_generator.parse_task_text(
            text,
            source="tasks/test.md",
            queue_label="test",
            queue_id="test",
        )

        self.assertEqual([task["id"] for task in tasks], ["TASK-009", "TASK-010"])
        self.assertEqual(tasks[0]["status"], "completed_bounded_structural")
        self.assertEqual(tasks[0]["kind"], "theorem | research")
        self.assertEqual(tasks[0]["why"], "This result is complete.")
        self.assertEqual(tasks[1]["status"], "active_remediation_draft")

    def test_multiline_hypothesis_is_bound_to_its_task(self) -> None:
        text = """\
### TASK-014 - Activation cycle

Status: queued
Kind: literature | theorem
Hypothesis: RQ-ONE, while the parallel workstream owns
`RQ-TWO`
Why it matters: The two workstreams share one release gate.
Inputs:
- input
"""
        [task] = site_generator.parse_task_text(
            text,
            source="tasks/test.md",
            queue_label="test",
            queue_id="test",
        )

        self.assertEqual(
            task["hypothesis"],
            "RQ-ONE, while the parallel workstream owns `RQ-TWO`",
        )

    def test_live_queues_parse_every_canonical_heading(self) -> None:
        expected_ids: list[str] = []
        for path in (
            site_generator.RESEARCH_TASKS_PATH,
            site_generator.PRODUCT_TASKS_PATH,
        ):
            expected_ids.extend(
                re.findall(r"^### (TASK-\d+) - ", path.read_text(encoding="utf-8"), re.M)
            )

        self.assertEqual(
            [task["id"] for task in site_generator.parse_tasks()],
            expected_ids,
        )

    def test_missing_required_field_fails_closed(self) -> None:
        text = """\
### TASK-999 - Malformed

Status: active
Hypothesis: none
Why it matters: Missing Kind must not disappear from the site silently.
Inputs:
- input
"""
        with self.assertRaisesRegex(ValueError, "missing required field 'Kind'"):
            site_generator.parse_task_text(
                text,
                source="tasks/test.md",
                queue_label="test",
                queue_id="test",
            )

    def test_exact_singleton_is_distinct_from_native_and_promotion_gates(
        self,
    ) -> None:
        product = site_generator.load_json(site_generator.PRODUCT_PATH)
        pilot = site_generator.load_json(site_generator.PILOT_PATH)
        stats = site_generator.load_json(site_generator.STATS_PATH)
        frontier = site_generator.load_json(site_generator.FRONTIER_PATH)
        decisions = site_generator.load_json(site_generator.DECISION_PATH)
        formal = site_generator.load_json(site_generator.FORMAL_PATH)
        graph = site_generator.load_json(site_generator.GRAPH_PATH)
        engine = site_generator.load_json(site_generator.ENGINE_PATH)
        verified_index = site_generator.load_json(site_generator.VERIFIED_INDEX_PATH)
        authorization_id = decisions[
            "bounded_experiment_authorization"
        ]["authorization_id"]

        index = site_generator.build_index(
            product,
            pilot,
            stats,
            frontier,
            decisions,
            formal,
            engine,
            verified_index,
        )
        results_page = site_generator.build_results(
            product,
            verified_index,
            decisions,
            engine,
            site_generator.researchos_claim_scopes(),
        )
        dashboard = site_generator.build_dashboard(
            product,
            stats,
            frontier,
            decisions,
            formal,
            graph,
            engine,
            site_generator.parse_tasks(),
        )
        explore = site_generator.build_explore(
            product, stats, decisions, engine
        )

        self.assertIn("View Verified Results", index)
        self.assertIn("One browser, two isolated ledgers", results_page)
        self.assertIn(str(verified_index["counts"]["navigation_rows_total"]), results_page)
        self.assertIn("data-result-list", results_page)
        self.assertIn("no proof candidate, and no progress on RH itself", results_page)
        self.assertIn("proves neither side", results_page)
        self.assertIn("Ledger scope", results_page)
        self.assertEqual(
            results_page.count('class="result-card__ledger-scope"'),
            verified_index["counts"]["researchos_rows"],
        )
        self.assertIn(authorization_id, dashboard)
        self.assertIn(authorization_id, explore)
        self.assertIn("1 exact synthetic-toy run completed", index)
        self.assertIn("Native decision exploration", dashboard)
        self.assertIn("Promotion experiments", dashboard)
        self.assertNotIn(
            "no experiment is authorized", dashboard.casefold()
        )
        self.assertNotIn("0 experiments authorized", explore.casefold())

    def test_public_research_system_is_progressively_enhanced(self) -> None:
        product = site_generator.load_json(site_generator.PRODUCT_PATH)
        pilot = site_generator.load_json(site_generator.PILOT_PATH)
        stats = site_generator.load_json(site_generator.STATS_PATH)
        frontier = site_generator.load_json(site_generator.FRONTIER_PATH)
        decisions = site_generator.load_json(site_generator.DECISION_PATH)
        formal = site_generator.load_json(site_generator.FORMAL_PATH)
        engine = site_generator.load_json(site_generator.ENGINE_PATH)
        verified_index = site_generator.load_json(site_generator.VERIFIED_INDEX_PATH)

        index = site_generator.build_index(
            product,
            pilot,
            stats,
            frontier,
            decisions,
            formal,
            engine,
            verified_index,
        )

        self.assertIn("data-research-loop", index)
        self.assertEqual(index.count("data-loop-step"), len(product["workflow"]))
        self.assertIn("data-research-map", index)
        self.assertEqual(index.count("data-map-kind="), 6)
        self.assertIn("not a\n          self-serve or hosted multi-project product", index)
        self.assertNotIn("foundations.point_counting.mathlib_gap", index)

    def test_site_discovery_files_follow_cname_and_public_pages(self) -> None:
        origin = site_generator.site_origin()
        robots = site_generator.build_robots()
        sitemap = site_generator.build_sitemap()

        self.assertIn(f"Sitemap: {origin}/sitemap.xml", robots)
        self.assertEqual(sitemap.count("<url>"), len(site_generator.PUBLIC_PAGES))
        for path, _label in site_generator.PUBLIC_PAGES:
            url = f"{origin}/{path}" if path else f"{origin}/"
            self.assertIn(f"<loc>{url}</loc>", sitemap)

    def test_shared_navigation_escapes_repository_url_attributes(self) -> None:
        repository_url = 'https://github.com/example/repo?x=1&next="quoted"'
        product = {
            "repository_url": repository_url,
            "category": "test workspace",
            "current_stage": {"label": "test stage"},
        }

        rendered = site_generator.site_header(product) + site_generator.site_footer(product)

        self.assertNotIn(repository_url, rendered)
        self.assertIn(
            "https://github.com/example/repo?x=1&amp;next=&quot;quoted&quot;",
            rendered,
        )


if __name__ == "__main__":
    unittest.main()
