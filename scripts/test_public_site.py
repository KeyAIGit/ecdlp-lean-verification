#!/usr/bin/env python3
"""Lightweight structural, link, and freshness checks for the public site."""
from __future__ import annotations

import re
import unittest
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

import site_generator


ROOT = Path(__file__).resolve().parent.parent
PAGE_PATHS = tuple(
    ROOT / (path or "index.html") for path, _label in site_generator.PUBLIC_PAGES
)


class DocumentParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.ids: list[str] = []
        self.links: list[str] = []
        self.images: list[dict[str, str]] = []
        self.tags: list[tuple[str, dict[str, str]]] = []
        self.primary_nav_text = ""
        self._primary_nav_depth = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = {name: value or "" for name, value in attrs}
        self.tags.append((tag, values))
        if identifier := values.get("id"):
            self.ids.append(identifier)
        if tag in {"a", "link"} and values.get("href"):
            self.links.append(values["href"])
        if tag in {"img", "script"} and values.get("src"):
            self.links.append(values["src"])
        if tag == "img":
            self.images.append(values)
        if tag == "nav" and "primary-nav" in values.get("class", "").split():
            self._primary_nav_depth = 1
        elif self._primary_nav_depth:
            self._primary_nav_depth += 1

    def handle_endtag(self, tag: str) -> None:
        if self._primary_nav_depth:
            self._primary_nav_depth -= 1

    def handle_data(self, data: str) -> None:
        if self._primary_nav_depth:
            self.primary_nav_text += " " + data


def parse_document(path: Path) -> DocumentParser:
    parser = DocumentParser()
    parser.feed(path.read_text(encoding="utf-8"))
    return parser


class PublicSiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.documents = {path: parse_document(path) for path in PAGE_PATHS}
        cls.ids_by_path = {path: set(document.ids) for path, document in cls.documents.items()}

    def test_generated_pages_are_fresh(self) -> None:
        product = site_generator.load_json(site_generator.PRODUCT_PATH)
        pilot = site_generator.load_json(site_generator.PILOT_PATH)
        stats = site_generator.load_json(site_generator.STATS_PATH)
        frontier = site_generator.load_json(site_generator.FRONTIER_PATH)
        decisions = site_generator.load_json(site_generator.DECISION_PATH)
        formal = site_generator.load_json(site_generator.FORMAL_PATH)
        graph = site_generator.load_json(site_generator.GRAPH_PATH)
        engine = site_generator.load_json(site_generator.ENGINE_PATH)
        verified_index = site_generator.load_json(site_generator.VERIFIED_INDEX_PATH)
        expected = {
            site_generator.INDEX_PATH: site_generator.build_index(
                product, pilot, stats, frontier, decisions, formal, engine, verified_index
            ),
            site_generator.RESULTS_PATH: site_generator.build_results(
                product,
                verified_index,
                decisions,
                engine,
                site_generator.researchos_claim_scopes(),
            ),
            site_generator.DASHBOARD_PATH: site_generator.build_dashboard(
                product,
                stats,
                frontier,
                decisions,
                formal,
                graph,
                engine,
                site_generator.parse_tasks(),
            ),
            site_generator.EXPLORE_PATH: site_generator.build_explore(
                product, stats, decisions, engine
            ),
            site_generator.PILOT_OUTPUT_PATH: site_generator.build_pilot(product, pilot),
            site_generator.ROBOTS_PATH: site_generator.build_robots(),
            site_generator.SITEMAP_PATH: site_generator.build_sitemap(),
        }
        for path, content in expected.items():
            with self.subTest(path=path.name):
                self.assertEqual(path.read_text(encoding="utf-8"), content.rstrip() + "\n")

    def test_landmarks_headings_and_navigation_are_present(self) -> None:
        required_nav = {
            "Research system",
            "Verified results",
            "ECDLP deployment",
            "Collaborate",
            "GitHub",
        }
        for path, document in self.documents.items():
            tags = [tag for tag, _attrs in document.tags]
            with self.subTest(path=path.name):
                self.assertEqual(tags.count("main"), 1)
                self.assertEqual(tags.count("header"), 1)
                self.assertEqual(tags.count("footer"), 1)
                self.assertEqual(tags.count("h1"), 1)
                self.assertIn("nav", tags)
                self.assertEqual(len(document.ids), len(set(document.ids)))
                for label in required_nav:
                    self.assertIn(label, document.primary_nav_text)
                self.assertIn(
                    'data-nav-page="routes" href="explore.html"',
                    path.read_text(encoding="utf-8"),
                )

    def test_internal_links_and_fragments_resolve(self) -> None:
        for source, document in self.documents.items():
            for raw_link in document.links:
                parsed = urlsplit(raw_link)
                if parsed.scheme or parsed.netloc or raw_link.startswith(("mailto:", "data:")):
                    continue
                target = source if not parsed.path else (source.parent / unquote(parsed.path)).resolve()
                with self.subTest(source=source.name, link=raw_link):
                    self.assertTrue(target.exists(), f"missing local target: {raw_link}")
                    if parsed.fragment and target.suffix == ".html":
                        self.assertIn(
                            unquote(parsed.fragment),
                            self.ids_by_path.get(target, set()),
                            f"missing fragment target: {raw_link}",
                        )

    def test_accessibility_sensitive_markup(self) -> None:
        for path, document in self.documents.items():
            source = path.read_text(encoding="utf-8")
            with self.subTest(path=path.name):
                self.assertRegex(source, r'<meta name="viewport" content="width=device-width, initial-scale=1">')
                self.assertIn('class="skip-link" href="#main"', source)
                for image in document.images:
                    self.assertIn("alt", image)
                    self.assertTrue(image.get("width"))
                    self.assertTrue(image.get("height"))
                for table in re.findall(r"<table\b.*?</table>", source, re.DOTALL):
                    self.assertIn("<caption", table)

        dashboard = (ROOT / "dashboard.html").read_text(encoding="utf-8")
        explore = (ROOT / "explore.html").read_text(encoding="utf-8")
        self.assertNotRegex(dashboard, r'<section\b[^>]*role="tabpanel"[^>]*\bhidden\b')
        self.assertNotRegex(dashboard, r'(?s)data-tabs[^>]*>\s*<button\b')
        for target in ("overview", "routes", "formal", "evidence", "activity"):
            self.assertIn(f'href="#{target}"', dashboard)
        for summary in re.findall(r"(?s)<summary\b[^>]*>.*?</summary>", explore):
            self.assertNotIn("<div", summary)
        for label in re.findall(r"(?s)<label\b[^>]*>.*?</label>", explore):
            self.assertNotRegex(label, r"<h[1-6]\b")

    def test_public_map_and_results_keep_generated_boundaries(self) -> None:
        index = (ROOT / "index.html").read_text(encoding="utf-8")
        results = (ROOT / "results.html").read_text(encoding="utf-8")
        kinds = re.findall(r'data-map-kind="([^"]+)"', index)
        self.assertEqual(
            kinds,
            ["question", "branches", "formal", "replayed", "frontier", "next-gap"],
        )
        for label in (
            "Formally proved",
            "Independently replayed",
            "Empirical",
            "Scoped negative",
            "Proposal / open",
            "Formal trust labels",
            "Riemann Hypothesis rows are foundation interfaces—not a proof candidate.",
            "Ledger scope",
        ):
            self.assertIn(label, results)
        self.assertNotIn("data-result-searchable", results)
        self.assertNotIn("data-route-searchable", (ROOT / "explore.html").read_text(encoding="utf-8"))

    def test_responsive_critical_styles_are_retained(self) -> None:
        css = (ROOT / "assets" / "site.css").read_text(encoding="utf-8")
        for breakpoint in ("1100px", "920px", "760px", "560px", "380px"):
            self.assertIn(f"@media (max-width: {breakpoint})", css)
        self.assertRegex(css, r"(?s)\.primary-nav\s*\{[^}]*overflow-x:\s*auto")
        self.assertIn("@media (prefers-reduced-motion: reduce)", css)
        self.assertIn("@media (forced-colors: active)", css)
        self.assertIn("scroll-margin-top: calc(var(--header-height) + 72px)", css)

        docs_sync = (ROOT / ".github" / "workflows" / "docs-sync.yml").read_text(
            encoding="utf-8"
        )
        self.assertEqual(docs_sync.count("- 'CNAME'"), 2)


if __name__ == "__main__":
    unittest.main()
