/* Interactive, clickable, hierarchical dependency graph.
 *
 * Data (graph.json, emitted by tools/auditor/graph.py) is already in
 * Cytoscape.js element shape: nodes carry ntype ∈ {tab, group, entry}, a
 * `parent` (compound nesting: entry → group → tab), a `tab`, and entries
 * also carry a `url`, `kind` and `status`. Edges are entry → entry.
 *
 * Hierarchy is made VISIBLE via compound (parent/child) nodes: every entry
 * sits inside its section box, every section inside its tab box. Tab colour
 * is applied to entry nodes and their containing boxes. Clicking an entry
 * node navigates to its page; clicking a section/tab box navigates to that
 * section/landing page. Scale (~160 entries) is handled by (a) per-tab
 * filtering, (b) a focus mode that dims everything outside the selected
 * node's neighbourhood, and (c) pan/zoom.
 */
(function () {
  "use strict";

  var TAB_COLORS = {
    paper: "#2563eb",
    ppl: "#16a34a",
    examples: "#d97706",
  };

  function tabColor(tab) {
    return TAB_COLORS[tab] || "#6b7280";
  }

  function ready(fn) {
    if (document.readyState !== "loading") fn();
    else document.addEventListener("DOMContentLoaded", fn);
  }

  ready(function () {
    var container = document.getElementById("cy");
    var emptyEl = document.getElementById("cy-empty");
    if (!container) return;

    if (typeof window.cytoscape === "undefined") {
      if (emptyEl) emptyEl.hidden = false;
      container.hidden = true;
      return;
    }
    // Register the dagre layout if both it and the adapter loaded.
    try {
      if (window.cytoscapeDagre) window.cytoscape.use(window.cytoscapeDagre);
    } catch (e) {
      /* already registered or unavailable — fall back to built-in layouts */
    }
    var hasDagre = typeof window.dagre !== "undefined" && !!window.cytoscapeDagre;

    var url = window.GRAPH_DATA_URL || "graph.json";
    fetch(url)
      .then(function (r) {
        if (!r.ok) throw new Error("HTTP " + r.status);
        return r.json();
      })
      .then(function (data) {
        init(data);
      })
      .catch(function (err) {
        if (emptyEl) {
          emptyEl.hidden = false;
          emptyEl.textContent =
            "Graph data could not be loaded (" + err.message + ").";
        }
        container.hidden = true;
      });

    function init(data) {
      var elements = (data.nodes || []).concat(data.edges || []);

      var cy = window.cytoscape({
        container: container,
        elements: elements,
        wheelSensitivity: 0.2,
        minZoom: 0.05,
        maxZoom: 3,
        style: [
          {
            selector: "node",
            style: {
              "font-size": 9,
              "color": "#111",
              "text-wrap": "wrap",
              "text-max-width": 110,
            },
          },
          {
            selector: 'node[ntype = "entry"]',
            style: {
              "label": "data(label)",
              "background-color": function (n) { return tabColor(n.data("tab")); },
              "shape": "round-rectangle",
              "width": "label",
              "height": "label",
              "padding": "5px",
              "text-valign": "center",
              "text-halign": "center",
              "color": "#fff",
              "font-weight": 600,
              "border-width": 0,
            },
          },
          {
            selector: 'node[ntype = "group"]',
            style: {
              "label": "data(label)",
              "background-color": function (n) { return tabColor(n.data("tab")); },
              "background-opacity": 0.06,
              "border-color": function (n) { return tabColor(n.data("tab")); },
              "border-width": 1.5,
              "border-opacity": 0.5,
              "shape": "round-rectangle",
              "text-valign": "top",
              "text-halign": "center",
              "font-size": 11,
              "font-weight": 700,
              "color": function (n) { return tabColor(n.data("tab")); },
              "padding": "12px",
            },
          },
          {
            selector: 'node[ntype = "tab"]',
            style: {
              "label": "data(label)",
              "background-color": function (n) { return tabColor(n.data("tab")); },
              "background-opacity": 0.03,
              "border-color": function (n) { return tabColor(n.data("tab")); },
              "border-width": 2,
              "border-opacity": 0.7,
              "shape": "round-rectangle",
              "text-valign": "top",
              "text-halign": "left",
              "font-size": 15,
              "font-weight": 800,
              "color": function (n) { return tabColor(n.data("tab")); },
              "padding": "18px",
            },
          },
          {
            selector: "edge",
            style: {
              "width": 1,
              "line-color": "#9aa4b2",
              "target-arrow-color": "#9aa4b2",
              "target-arrow-shape": "triangle",
              "arrow-scale": 0.7,
              "curve-style": "bezier",
              "opacity": 0.45,
            },
          },
          // Doc co-reference ("mentions"): lighter, dashed — the weaker
          // relation (A's text names an ident B documents).
          {
            selector: "edge.mentions",
            style: {
              "line-style": "dashed",
              "line-color": "#c0c7d1",
              "target-arrow-color": "#c0c7d1",
              "opacity": 0.35,
            },
          },
          // Real Coq proof dependency ("depends", from .glob): solid,
          // darker, thicker — the load-bearing relation (A's proof USES a
          // lemma B documents).
          {
            selector: "edge.depends",
            style: {
              "line-style": "solid",
              "width": 1.6,
              "line-color": "#4b5563",
              "target-arrow-color": "#4b5563",
              "arrow-scale": 0.85,
              "opacity": 0.65,
            },
          },
          // Cross-tab edges keep their purple hue but the depends/mentions
          // line-style above still distinguishes the two kinds.
          {
            selector: "edge.cross-tab",
            style: {
              "line-color": "#a855f7",
              "target-arrow-color": "#a855f7",
            },
          },
          { selector: ".dimmed", style: { "opacity": 0.08 } },
          {
            selector: "node.highlighted",
            style: { "border-width": 3, "border-color": "#111", "border-opacity": 1 },
          },
          {
            selector: "edge.highlighted",
            style: { "opacity": 0.95, "width": 2, "line-color": "#111", "target-arrow-color": "#111" },
          },
        ],
        layout: { name: "preset" },
      });

      // Tag each edge with its kind (real Coq dependency vs doc mention) and
      // mark cross-tab edges (source tab ≠ target tab) for distinct styling.
      cy.edges().forEach(function (e) {
        var kind = e.data("kind");
        e.addClass(kind === "depends" ? "depends" : "mentions");
        var s = e.source().data("tab");
        var t = e.target().data("tab");
        if (s && t && s !== t) e.addClass("cross-tab");
      });

      // -- focus mode + clickable navigation --------------------------
      // Default: a node tap NAVIGATES to its page. With focus mode on, a
      // tap instead spotlights that node's closed neighbourhood (dimming
      // the rest) so a dense graph stops being a hairball; tapping the
      // background clears the spotlight.
      var focusMode = false;
      var focusEl = document.getElementById("cy-focus-mode");
      if (focusEl) {
        focusEl.addEventListener("change", function () {
          focusMode = focusEl.checked;
          clearFocus();
        });
      }
      function clearFocus() {
        cy.elements().removeClass("dimmed highlighted");
      }
      function spotlight(n) {
        var hood = n.closedNeighborhood();
        cy.elements().addClass("dimmed").removeClass("highlighted");
        hood.removeClass("dimmed").addClass("highlighted");
      }
      cy.on("tap", "node", function (evt) {
        var n = evt.target;
        if (focusMode) {
          spotlight(n);
          return;
        }
        var url = n.data("url");
        if (url) window.location.href = url;
      });
      cy.on("tap", function (evt) {
        if (evt.target === cy && focusMode) clearFocus();
      });
      cy.on("mouseover", "node", function (evt) {
        if (focusMode || evt.target.data("url")) container.style.cursor = "pointer";
      });
      cy.on("mouseout", "node", function () {
        container.style.cursor = "default";
      });

      // -- tab + edge-kind filters ------------------------------------
      // Tabs hide nodes; edge kinds hide edges. Hiding the (weaker, more
      // numerous) `mentions` edges is what turns the hairball into the
      // real proof-dependency skeleton, so it gets its own control.
      var filters = Array.prototype.slice.call(
        document.querySelectorAll(".cy-tab-filter")
      );
      var edgeFilters = Array.prototype.slice.call(
        document.querySelectorAll(".cy-edge-filter")
      );
      function applyFilter() {
        var active = {};
        filters.forEach(function (cb) { active[cb.value] = cb.checked; });
        var kinds = {};
        edgeFilters.forEach(function (cb) { kinds[cb.value] = cb.checked; });
        var filteringEdges = edgeFilters.length > 0;
        cy.batch(function () {
          cy.nodes().forEach(function (n) {
            var tab = n.data("tab");
            if (active[tab]) n.style("display", "element");
            else n.style("display", "none");
          });
          if (filteringEdges) {
            cy.edges().forEach(function (e) {
              var kind = e.data("kind") === "depends" ? "depends" : "mentions";
              e.style("display", kinds[kind] ? "element" : "none");
            });
          }
        });
        runLayout();
        updateStats();
      }
      filters.forEach(function (cb) {
        cb.addEventListener("change", applyFilter);
      });
      edgeFilters.forEach(function (cb) {
        cb.addEventListener("change", applyFilter);
      });

      // -- layout selector --------------------------------------------
      var layoutSel = document.getElementById("cy-layout");
      function layoutConfig() {
        var name = layoutSel ? layoutSel.value : "dagre";
        if (name === "dagre" && !hasDagre) name = "breadthfirst";
        if (name === "dagre") {
          return {
            name: "dagre",
            rankDir: "LR",
            nodeSep: 18,
            rankSep: 60,
            edgeSep: 8,
            animate: false,
            fit: true,
            padding: 20,
          };
        }
        if (name === "cose") {
          return { name: "cose", animate: false, fit: true, padding: 20, nodeRepulsion: 9000 };
        }
        if (name === "breadthfirst") {
          return { name: "breadthfirst", directed: true, fit: true, padding: 20, spacingFactor: 0.9 };
        }
        return { name: "concentric", fit: true, padding: 20, minNodeSpacing: 12 };
      }
      function runLayout() {
        var visible = cy.nodes(':visible[ntype = "entry"]').closedNeighborhood();
        var eles = visible.length ? visible : cy.elements(":visible");
        try {
          eles.layout(layoutConfig()).run();
        } catch (e) {
          cy.elements(":visible").layout({ name: "breadthfirst", fit: true, padding: 20 }).run();
        }
      }
      if (layoutSel) layoutSel.addEventListener("change", runLayout);

      var resetBtn = document.getElementById("cy-reset");
      if (resetBtn) {
        resetBtn.addEventListener("click", function () {
          clearFocus();
          cy.fit(undefined, 20);
        });
      }

      // -- stats ------------------------------------------------------
      var statsEl = document.getElementById("cy-stats");
      function updateStats() {
        if (!statsEl) return;
        var n = cy.nodes(':visible[ntype = "entry"]').length;
        var vis = cy.edges(":visible");
        var dep = vis.filter('[kind = "depends"]').length;
        statsEl.textContent =
          n + " entries · " + vis.length + " edges shown (" + dep +
          " real dependencies)";
      }

      // Initial layout + fit.
      runLayout();
      updateStats();
      cy.fit(undefined, 20);
    }
  });
})();
