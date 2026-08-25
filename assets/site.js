(function () {
  "use strict";

  var body = document.body;
  var page = body.getAttribute("data-page");

  document.querySelectorAll("[data-nav-page]").forEach(function (link) {
    if (link.getAttribute("data-nav-page") === page) {
      link.setAttribute("aria-current", "page");
    }
  });

  function setupResearchLoop() {
    var root = document.querySelector("[data-research-loop]");
    if (!root) return;

    var steps = Array.prototype.slice.call(root.querySelectorAll("[data-loop-step]"));
    var summaries = steps.map(function (step) {
      return step.querySelector("summary");
    }).filter(Boolean);
    if (!steps.length || !summaries.length) return;

    root.classList.add("research-loop--enhanced");

    steps.forEach(function (step) {
      step.addEventListener("toggle", function () {
        if (!step.open) return;
        steps.forEach(function (other) {
          if (other !== step) other.open = false;
        });
      });
    });

    summaries.forEach(function (summary, index) {
      summary.addEventListener("keydown", function (event) {
        var next = null;
        if (event.key === "ArrowRight" || event.key === "ArrowDown") {
          next = (index + 1) % summaries.length;
        } else if (event.key === "ArrowLeft" || event.key === "ArrowUp") {
          next = (index - 1 + summaries.length) % summaries.length;
        } else if (event.key === "Home") {
          next = 0;
        } else if (event.key === "End") {
          next = summaries.length - 1;
        }
        if (next === null) return;
        event.preventDefault();
        summaries[next].focus();
      });
    });
  }

  function setupTabs() {
    var tablist = document.querySelector("[data-tabs]");
    if (!tablist) return;

    var buttons = Array.prototype.slice.call(tablist.querySelectorAll("[data-tab]"));
    var panels = Array.prototype.slice.call(document.querySelectorAll("[data-tab-panel]"));
    if (!buttons.length || !panels.length) return;

    body.classList.add("tabs-enhanced");

    function select(id, updateHash, moveFocus) {
      var selectedIndex = buttons.findIndex(function (button) {
        return button.getAttribute("data-tab") === id;
      });
      if (selectedIndex < 0) selectedIndex = 0;
      id = buttons[selectedIndex].getAttribute("data-tab");

      buttons.forEach(function (button, index) {
        var active = index === selectedIndex;
        button.setAttribute("aria-selected", active ? "true" : "false");
        button.setAttribute("tabindex", active ? "0" : "-1");
      });
      panels.forEach(function (panel) {
        panel.hidden = panel.getAttribute("data-tab-panel") !== id;
      });
      if (moveFocus) buttons[selectedIndex].focus();
      if (updateHash && window.history && window.history.replaceState) {
        window.history.replaceState(null, "", "#" + id);
      }
    }

    buttons.forEach(function (button, index) {
      button.addEventListener("click", function (event) {
        event.preventDefault();
        select(button.getAttribute("data-tab"), true, false);
      });
      button.addEventListener("keydown", function (event) {
        var next = null;
        if (event.key === "ArrowRight") {
          next = (index + 1) % buttons.length;
        } else if (event.key === "ArrowLeft") {
          next = (index - 1 + buttons.length) % buttons.length;
        } else if (event.key === "Home") {
          next = 0;
        } else if (event.key === "End") {
          next = buttons.length - 1;
        }
        if (next === null) return;
        event.preventDefault();
        select(buttons[next].getAttribute("data-tab"), true, true);
      });
    });

    var initial = window.location.hash.replace(/^#/, "");
    select(initial, false, false);
    window.addEventListener("hashchange", function () {
      select(window.location.hash.replace(/^#/, ""), false, false);
    });
  }

  function setupFilters(config) {
    var list = document.querySelector(config.list);
    var search = document.querySelector(config.search);
    var buttons = Array.prototype.slice.call(document.querySelectorAll(config.buttons));
    var counter = document.querySelector(config.counter);
    var empty = document.querySelector(config.empty);
    if (!list || !search || !buttons.length) return;

    var rows = Array.prototype.slice.call(list.querySelectorAll(config.rows)).map(function (row) {
      return {
        node: row,
        tags: (row.getAttribute(config.tags) || "").split(/\s+/),
        text: null
      };
    });
    var active = "all";
    var frame = 0;

    function apply() {
      frame = 0;
      var query = search.value.trim().toLowerCase();
      var visible = 0;

      rows.forEach(function (row) {
        var matchesFilter = active === "all" || row.tags.indexOf(active) >= 0;
        if (query && row.text === null) {
          row.text = (row.node.textContent || "").toLowerCase();
        }
        var matchesSearch = !query || row.text.indexOf(query) >= 0;
        var matches = matchesFilter && matchesSearch;
        row.node.hidden = !matches;
        if (matches) visible += 1;
      });

      if (counter) {
        counter.textContent = String(visible) + (visible === 1 ? config.singular : config.plural);
      }
      if (empty) empty.hidden = visible !== 0;
    }

    function schedule() {
      if (frame) cancelAnimationFrame(frame);
      frame = requestAnimationFrame(apply);
    }

    buttons.forEach(function (button) {
      button.addEventListener("click", function () {
        active = button.getAttribute(config.filter) || "all";
        buttons.forEach(function (item) {
          item.setAttribute("aria-pressed", item === button ? "true" : "false");
        });
        schedule();
      });
    });
    search.addEventListener("input", schedule);
    apply();
  }

  setupResearchLoop();
  setupTabs();
  setupFilters({
    list: "[data-route-list]",
    search: "[data-route-search]",
    buttons: "[data-route-filter]",
    counter: "[data-route-count]",
    empty: "[data-route-empty]",
    rows: "[data-route-status]",
    tags: "data-route-status",
    filter: "data-route-filter",
    singular: " route",
    plural: " routes"
  });
  setupFilters({
    list: "[data-result-list]",
    search: "[data-result-search]",
    buttons: "[data-result-filter]",
    counter: "[data-result-count]",
    empty: "[data-result-empty]",
    rows: "[data-result-tags]",
    tags: "data-result-tags",
    filter: "data-result-filter",
    singular: " result",
    plural: " results"
  });
})();
