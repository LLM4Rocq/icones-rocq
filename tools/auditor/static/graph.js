/* The dependency graph, rebuilt as a READABLE DAG.
 *
 * The data (graph.json, emitted by tools/auditor/graph.py) is the whole
 * three-tab relation: ~170 entry nodes inside ~20 section groups, plus
 * ~800 edges of two kinds (real .glob proof dependencies, and weaker doc
 * co-references).  Drawing all of that at once produces a hairball, so
 * this client never does.  It renders a PROJECTION of the data:
 *
 *   * ONE tab at a time (default: ?tab=… , else "paper");
 *   * "depends" edges only, unless prose co-references are switched on;
 *   * section groups COLLAPSED to a single node (with an entry-count
 *     badge) until clicked, edges aggregating onto the collapsed group;
 *   * dependencies flowing left → right (dagre, rankDir LR);
 *   * edges that leave the visible tab drawn as small stub PORTS on the
 *     node (one per foreign tab, count-badged, click to list) rather
 *     than as edges pointing at nodes that are not on screen.
 *
 * On top of that projection sits the interaction the page exists for:
 * clicking an entry dims everything outside its dependency CONE — the
 * transitive "uses" side, the transitive "used by" side, each toggleable
 * with a depth limit — and shows the entry's card link in a side panel.
 * Double-click (or the panel link) opens the entry page; Esc or a click
 * on the background clears.
 *
 * Everything is client-side over the single graph.json fetch: the page
 * works as a static file with the vendored Cytoscape + dagre bundles.
 */
(function () {
  "use strict";

  var TABS = ["paper", "ppl", "examples"];
  var TAB_LABEL = { paper: "Paper", ppl: "PPL", examples: "Examples" };
  var DEPTH_ALL = 0;          // sentinel: unlimited cone depth
  var MAX_LABEL = 30;         // entry labels are elided past this
  var MAX_RESULTS = 12;       // search suggestions shown at once
  var NODE_BUDGET = 40;       // drawn nodes the landing view aims for

  var REDUCED_MOTION =
    window.matchMedia &&
    window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  function ready(fn) {
    if (document.readyState !== "loading") fn();
    else document.addEventListener("DOMContentLoaded", fn);
  }

  function el(id) {
    return document.getElementById(id);
  }

  function esc(s) {
    return String(s == null ? "" : s).replace(/[&<>"']/g, function (c) {
      return {
        "&": "&amp;",
        "<": "&lt;",
        ">": "&gt;",
        '"': "&quot;",
        "'": "&#39;",
      }[c];
    });
  }

  function elide(s, n) {
    s = String(s || "");
    return s.length > n ? s.slice(0, n - 1) + "…" : s;
  }

  /* Canvas colours live in graph.css (as custom properties) so the graph
   * follows the dashboard's light/dark palette instead of hard-coding a
   * second one here. */
  function palette(root) {
    var cs = getComputedStyle(root);
    function v(name, fallback) {
      var got = cs.getPropertyValue(name);
      got = got && got.trim();
      return got || fallback;
    }
    return {
      paper: v("--g-paper", "#2563eb"),
      ppl: v("--g-ppl", "#16a34a"),
      examples: v("--g-examples", "#d97706"),
      nodeFg: v("--g-node-fg", "#ffffff"),
      groupFg: v("--g-group-fg", "#3d3d38"),
      edge: v("--g-edge", "#6b7280"),
      mention: v("--g-mention", "#b3b9c4"),
      focus: v("--g-focus", "#111111"),
      stub: v("--g-stub", "#8b8f98"),
      surface: v("--g-surface", "#ffffff"),
    };
  }

  ready(function () {
    var container = el("cy");
    var emptyEl = el("cy-empty");
    var appEl = document.querySelector(".graph-app") || document.body;
    if (!container) return;

    function degrade(message) {
      if (emptyEl) {
        emptyEl.hidden = false;
        if (message) emptyEl.textContent = message;
      }
      var stage = document.querySelector(".graph-stage");
      if (stage) stage.hidden = true;
    }

    if (typeof window.cytoscape === "undefined") {
      degrade(
        "Graph could not be initialised (the bundled Cytoscape.js library " +
          "did not load). Each entry page still lists its own cross-references."
      );
      return;
    }
    try {
      if (window.cytoscapeDagre) window.cytoscape.use(window.cytoscapeDagre);
    } catch (e) {
      /* already registered — fall through to the availability check */
    }
    var hasDagre =
      typeof window.dagre !== "undefined" && !!window.cytoscapeDagre;

    fetch(window.GRAPH_DATA_URL || "graph.json")
      .then(function (r) {
        if (!r.ok) throw new Error("HTTP " + r.status);
        return r.json();
      })
      .then(function (data) {
        try {
          init(data);
        } catch (err) {
          degrade("Graph could not be drawn (" + err.message + ").");
          throw err;
        }
      })
      .catch(function (err) {
        degrade("Graph data could not be loaded (" + err.message + ").");
      });

    /* ================================================================
     * 1. Model — index graph.json once, keyed for the projections below
     * ================================================================ */
    function init(data) {
      var meta = data.meta || {};
      var byId = {};                 // node id -> data
      var groupsOfTab = {};          // tab -> [group id] in document order
      var entriesOfGroup = {};       // group id -> [entry id]
      var entryIds = [];             // every entry id, document order
      TABS.forEach(function (t) {
        groupsOfTab[t] = [];
      });

      (data.nodes || []).forEach(function (n) {
        var d = n.data;
        byId[d.id] = d;
        if (d.ntype === "group") {
          if (groupsOfTab[d.tab]) groupsOfTab[d.tab].push(d.id);
          entriesOfGroup[d.id] = [];
        }
      });
      (data.nodes || []).forEach(function (n) {
        var d = n.data;
        if (d.ntype !== "entry") return;
        entryIds.push(d.id);
        if (entriesOfGroup[d.parent]) entriesOfGroup[d.parent].push(d.id);
      });

      var rawEdges = (data.edges || [])
        .map(function (e) {
          return {
            s: e.data.source,
            t: e.data.target,
            kind: e.data.kind === "depends" ? "depends" : "mentions",
          };
        })
        .filter(function (e) {
          return byId[e.s] && byId[e.t];
        });

      // Raw co-reference edges TOUCHING each tab.  This is dataset context
      // for the toggle's tooltip only — it is emphatically NOT what the
      // toggle draws (most of these live inside one collapsed section, or
      // duplicate a dependency already on screen, or leave the tab and
      // become a port entry).  What the toggle draws is measured against
      // the live projection by coReferenceCost() below.
      var tabMentions = {};
      TABS.forEach(function (t) {
        tabMentions[t] = 0;
      });
      rawEdges.forEach(function (e) {
        if (e.kind !== "mentions") return;
        var st = byId[e.s].tab;
        var tt = byId[e.t].tab;
        if (tabMentions[st] !== undefined) tabMentions[st] += 1;
        if (tt !== st && tabMentions[tt] !== undefined) {
          tabMentions[tt] += 1;
        }
      });

      // Search index: entry title + every Rocq identifier it documents.
      var searchIndex = entryIds.map(function (id) {
        var d = byId[id];
        var idents = d.idents || [];
        return {
          id: id,
          label: d.label || id,
          tab: d.tab,
          group: d.group_label || "",
          idents: idents,
          hay: (d.label + " " + idents.join(" ") + " " + (d.group_label || ""))
            .toLowerCase(),
        };
      });

      /* ==============================================================
       * 2. View state (+ its URL round-trip)
       * ============================================================== */
      var params = new URLSearchParams(window.location.search);
      var wantTab = params.get("tab");
      var state = {
        tab: TABS.indexOf(wantTab) >= 0 ? wantTab : "paper",
        mentions: params.get("co") === "1",
        expanded: {},              // group id -> true
        focus: null,               // rendered node id
        up: true,                  // cone: what the node builds on
        down: true,                // cone: what builds on the node
        depth: DEPTH_ALL,
        stub: null,                // id of the cross-tab port being listed
      };

      /* The landing view is a NODE BUDGET, not "everything folded".  A page
       * whose first paint is eight boxes reads as a graph with eight nodes,
       * and gives the reader nothing to click that they can recognise; a
       * page whose first paint is every entry is the hairball this rewrite
       * exists to kill.  So: unfold sections, in document order, while the
       * drawn-node count stays inside the budget — the reader lands on real
       * entries, and learns the affordance by FOLDING a box rather than by
       * hunting for one worth opening.  A section too big for the remaining
       * budget stays folded and later, smaller ones still get their turn. */
      function budgetedExpansion(tab) {
        var open = {};
        var groups = groupsOfTab[tab] || [];
        var drawn = groups.length;          // every group draws one box
        groups.forEach(function (gid) {
          var kids = (entriesOfGroup[gid] || []).length;
          if (kids && drawn + kids <= NODE_BUDGET) {
            open[gid] = true;
            drawn += kids;
          }
        });
        return open;
      }
      state.expanded = budgetedExpansion(state.tab);

      // ?focus= wins over ?tab=: a deep link from an entry page names the
      // node, and the node knows which tab it lives in.
      var wantFocus = params.get("focus");
      if (wantFocus && byId[wantFocus]) {
        var fd = byId[wantFocus];
        if (fd.ntype === "entry") {
          state.tab = fd.tab;
          state.expanded = budgetedExpansion(fd.tab);
          state.expanded[fd.parent] = true;   // the deep link's own section
          state.focus = wantFocus;
        } else if (fd.ntype === "group") {
          state.tab = fd.tab;
          state.expanded = budgetedExpansion(fd.tab);
          state.focus = wantFocus;
        }
      }

      function syncUrl() {
        var p = new URLSearchParams();
        p.set("tab", state.tab);
        if (state.mentions) p.set("co", "1");
        if (state.focus) p.set("focus", state.focus);
        try {
          window.history.replaceState(
            null,
            "",
            window.location.pathname + "?" + p.toString()
          );
        } catch (e) {
          /* file:// or a sandboxed frame — the view still works */
        }
      }

      function isExpanded(gid) {
        return state.expanded[gid] === true;
      }

      /** The node an entry is DRAWN as: itself, or its collapsed group. */
      function renderIdOf(entryId) {
        var d = byId[entryId];
        if (d.ntype !== "entry") return entryId;
        return isExpanded(d.parent) ? entryId : d.parent;
      }

      /* ==============================================================
       * 3. Projection — data + state -> the elements actually drawn
       * ============================================================== */
      var rendered = {};   // rendered node id -> {out:[], in:[]} adjacency
      var crossPorts = {}; // rendered node id -> {out:{tab:[items]}, in:{…}}

      /** Fold the raw relation onto the nodes currently DRAWN.
       *
       * Returns ``{agg, ports}``:
       *
       *   * ``agg``   — one slot per drawn ordered pair, keeping the two
       *     kinds APART (``depends`` / ``mentions``) so the caller can style
       *     and weigh each on its own evidence;
       *   * ``ports`` — per drawn node, per direction, per foreign tab, the
       *     DISTINCT foreign entries it reaches.  Distinct is the whole
       *     point: a collapsed section funnels all of its entries into one
       *     bucket, so the same target arrives once per raw edge, and a
       *     bucket that counted arrivals would badge (and list) the same
       *     entry several times over.
       *
       * ``withMentions`` is passed explicitly rather than read from the
       * view state so the co-reference toggle can price itself against the
       * same code that draws the canvas.
       */
      function aggregate(withMentions) {
        var tab = state.tab;
        var agg = {};
        var ports = {};
        var seen = {};   // host \0 dir \0 tab \0 foreign entry -> true

        function port(host, dir, otherTab, otherId) {
          var mark = [host, dir, otherTab, otherId].join("\u0000");
          if (seen[mark]) return;
          seen[mark] = true;
          var slot = ports[host] || (ports[host] = { out: {}, in: {} });
          var bucket = slot[dir][otherTab] || (slot[dir][otherTab] = []);
          bucket.push(otherId);
        }

        rawEdges.forEach(function (e) {
          if (e.kind === "mentions" && !withMentions) return;
          var sIn = byId[e.s].tab === tab;
          var tIn = byId[e.t].tab === tab;
          if (!sIn && !tIn) return;
          if (sIn && tIn) {
            var a = renderIdOf(e.s);
            var b = renderIdOf(e.t);
            // Both endpoints inside the same COLLAPSED group: the edge is
            // internal to that box, so it is not drawn (it reappears when
            // the group is expanded) rather than becoming a self-loop.
            if (a === b) return;
            var key = a + "\u0000" + b;
            var slot = agg[key];
            if (!slot) {
              slot = agg[key] = { s: a, t: b, depends: 0, mentions: 0 };
            }
            slot[e.kind] += 1;
          } else if (sIn) {
            port(renderIdOf(e.s), "out", byId[e.t].tab, e.t);
          } else {
            port(renderIdOf(e.t), "in", byId[e.s].tab, e.s);
          }
        });
        return { agg: agg, ports: ports };
      }

      function portTotal(ports) {
        var n = 0;
        Object.keys(ports).forEach(function (host) {
          ["out", "in"].forEach(function (dir) {
            Object.keys(ports[host][dir]).forEach(function (t) {
              n += ports[host][dir][t].length;
            });
          });
        });
        return n;
      }

      /** What switching co-references ON actually costs IN THIS VIEW.
       *
       * Not the dataset's co-reference count: in a view with sections
       * folded, most raw co-references are internal to one box, or already
       * duplicated by a dependency edge drawn between the same pair, or
       * leave the tab and land in a port.  Quoting the raw number next to a
       * checkbox that visibly adds a handful of edges is what made the
       * flagship control look broken, so the label quotes what will be
       * drawn: the dashed edges, and the extra port entries.
       */
      function coReferenceCost() {
        var on = aggregate(true);
        var off = aggregate(false);
        var dashed = 0;
        Object.keys(on.agg).forEach(function (k) {
          if (!on.agg[k].depends) dashed += 1;
        });
        return {
          edges: dashed,
          ports: portTotal(on.ports) - portTotal(off.ports),
          total: tabMentions[state.tab] || 0,
        };
      }

      function project() {
        var tab = state.tab;
        var nodes = [];
        var edges = [];
        rendered = {};
        crossPorts = {};

        groupsOfTab[tab].forEach(function (gid) {
          var g = byId[gid];
          var open = isExpanded(gid);
          var kids = entriesOfGroup[gid] || [];
          nodes.push({
            data: {
              id: gid,
              label: open
                ? g.label
                : g.label + "\n" + kids.length + " entr" +
                  (kids.length === 1 ? "y" : "ies"),
              title: g.label,
              ntype: open ? "group" : "gcol",
              tab: tab,
              n: kids.length,
              url: g.url || "",
            },
            classes: open ? "grp grp-open" : "grp grp-closed",
          });
          rendered[gid] = { out: [], in: [] };
          if (!open) return;
          kids.forEach(function (eid) {
            var d = byId[eid];
            nodes.push({
              data: {
                id: eid,
                parent: gid,
                label: elide(d.label, MAX_LABEL),
                title: d.label,
                ntype: "entry",
                tab: tab,
                kind: d.kind || "",
                url: d.url || "",
              },
              classes: "ent",
            });
            rendered[eid] = { out: [], in: [] };
          });
        });

        var built = aggregate(state.mentions);
        crossPorts = built.ports;

        Object.keys(built.agg).forEach(function (key, i) {
          var a = built.agg[key];
          // The stronger relation NAMES the edge -- but only the dependency
          // tally may thicken a solid "depends" line, or prose weight would
          // masquerade as proof weight on the very edge the legend calls a
          // real Coq proof dependency.  A dashed co-reference line is
          // thickened by its own tally, which is what it claims to show.
          var kind = a.depends ? "depends" : "mentions";
          var weight = kind === "depends" ? a.depends : a.mentions;
          var id = "E" + i;
          edges.push({
            data: {
              id: id,
              source: a.s,
              target: a.t,
              kind: kind,
              w: Math.max(1, Math.min(weight, 8)),
              n: a.depends + a.mentions,
              nd: a.depends,
              nm: a.mentions,
            },
            classes: kind,
          });
          rendered[a.s].out.push({ to: a.t, edge: id });
          rendered[a.t].in.push({ to: a.s, edge: id });
        });

        return nodes.concat(edges);
      }

      /* ==============================================================
       * 4. Cytoscape instance + stylesheet
       * ============================================================== */
      var pal = palette(appEl);
      function tabColor(t) {
        return pal[t] || pal.stub;
      }

      function stylesheet() {
        return [
          {
            selector: "node",
            style: {
              "font-family":
                'system-ui, -apple-system, "Segoe UI", Roboto, sans-serif',
              "text-wrap": "wrap",
              "text-max-width": 132,
            },
          },
          {
            selector: "node.ent",
            style: {
              label: "data(label)",
              "background-color": function (n) {
                return tabColor(n.data("tab"));
              },
              shape: "round-rectangle",
              width: "label",
              height: "label",
              padding: "7px",
              "text-valign": "center",
              "text-halign": "center",
              color: pal.nodeFg,
              "font-size": 10,
              "font-weight": 600,
              "border-width": 0,
              "transition-property": "opacity",
              "transition-duration": REDUCED_MOTION ? 0 : 120,
            },
          },
          {
            selector: "node.grp-closed",
            style: {
              label: "data(label)",
              shape: "round-rectangle",
              width: "label",
              height: "label",
              padding: "11px",
              "text-valign": "center",
              "text-halign": "center",
              "text-max-width": 168,
              "background-color": function (n) {
                return tabColor(n.data("tab"));
              },
              "background-opacity": 0.12,
              "border-width": 1.6,
              "border-color": function (n) {
                return tabColor(n.data("tab"));
              },
              "border-opacity": 0.85,
              color: pal.groupFg,
              "font-size": 11,
              "font-weight": 700,
              "text-margin-y": 0,
            },
          },
          {
            selector: "node.grp-open",
            style: {
              label: "data(label)",
              shape: "round-rectangle",
              "background-color": function (n) {
                return tabColor(n.data("tab"));
              },
              "background-opacity": 0.05,
              "border-width": 1.4,
              "border-color": function (n) {
                return tabColor(n.data("tab"));
              },
              "border-opacity": 0.45,
              "text-valign": "top",
              "text-halign": "center",
              "text-margin-y": -4,
              "text-max-width": 260,
              color: function (n) {
                return tabColor(n.data("tab"));
              },
              "font-size": 11,
              "font-weight": 700,
              padding: "16px",
            },
          },
          {
            selector: "node.stub",
            style: {
              label: "data(label)",
              shape: "ellipse",
              width: 16,
              height: 16,
              "background-color": function (n) {
                return tabColor(n.data("otherTab"));
              },
              "background-opacity": 0.16,
              "border-width": 1.2,
              "border-color": function (n) {
                return tabColor(n.data("otherTab"));
              },
              color: function (n) {
                return tabColor(n.data("otherTab"));
              },
              "font-size": 8,
              "font-weight": 700,
              "text-valign": "center",
              "text-halign": "center",
              "z-compound-depth": "top",
            },
          },
          {
            selector: "edge",
            style: {
              "curve-style": "bezier",
              "target-arrow-shape": "triangle",
              "arrow-scale": 0.75,
              width: "mapData(w, 1, 8, 1.3, 3.6)",
              "line-color": pal.edge,
              "target-arrow-color": pal.edge,
              opacity: 0.5,
            },
          },
          {
            selector: "edge.mentions",
            style: {
              "line-style": "dashed",
              "line-color": pal.mention,
              "target-arrow-color": pal.mention,
              opacity: 0.4,
            },
          },
          // -- focus cone ------------------------------------------------
          { selector: ".dim", style: { opacity: 0.07 } },
          {
            selector: "node.cone",
            style: { "border-width": 2, "border-color": pal.focus, "border-opacity": 0.55 },
          },
          {
            selector: "edge.cone",
            style: {
              opacity: 0.95,
              "line-color": pal.focus,
              "target-arrow-color": pal.focus,
            },
          },
          {
            selector: "node.root",
            style: {
              "border-width": 3.2,
              "border-color": pal.focus,
              "border-opacity": 1,
            },
          },
          {
            selector: "node.hit",
            style: {
              "border-width": 3,
              "border-color": pal.focus,
              "border-style": "dashed",
              "border-opacity": 0.9,
            },
          },
        ];
      }

      var cy = window.cytoscape({
        container: container,
        elements: [],
        wheelSensitivity: 0.2,
        minZoom: 0.05,
        maxZoom: 3,
        textureOnViewport: true,
        style: stylesheet(),
        layout: { name: "preset" },
      });

      if (window.matchMedia) {
        var scheme = window.matchMedia("(prefers-color-scheme: dark)");
        var onScheme = function () {
          pal = palette(appEl);
          cy.style(stylesheet());
        };
        if (scheme.addEventListener) scheme.addEventListener("change", onScheme);
        else if (scheme.addListener) scheme.addListener(onScheme);
      }

      /* ==============================================================
       * 5. Render = project -> lay out -> hang the cross-tab ports
       * ============================================================== */
      function layoutOpts() {
        if (!hasDagre) {
          return {
            name: "breadthfirst",
            directed: true,
            fit: false,
            padding: 24,
            spacingFactor: 1.1,
          };
        }
        return {
          name: "dagre",
          rankDir: "LR",          // dependency flow: left -> right
          nodeSep: 16,
          rankSep: 64,
          edgeSep: 8,
          animate: false,         // never animate: reduced-motion safe
          fit: false,
          padding: 24,
        };
      }

      function addPorts() {
        var stubs = [];
        Object.keys(crossPorts).forEach(function (host) {
          var node = cy.getElementById(host);
          if (!node || node.empty()) return;
          var pos = node.position();
          var w = node.outerWidth();
          ["out", "in"].forEach(function (dir) {
            var tabs = Object.keys(crossPorts[host][dir]).sort();
            tabs.forEach(function (otherTab, i) {
              var items = crossPorts[host][dir][otherTab];
              stubs.push({
                group: "nodes",
                data: {
                  id: "port::" + dir + "::" + otherTab + "::" + host,
                  label: String(items.length),
                  ntype: "stub",
                  dir: dir,
                  host: host,
                  otherTab: otherTab,
                  n: items.length,
                },
                classes: "stub",
                position: {
                  x: pos.x + (w / 2 + 13) * (dir === "out" ? 1 : -1),
                  y: pos.y + (i - (tabs.length - 1) / 2) * 19,
                },
                selectable: false,
                grabbable: false,
              });
            });
          });
        });
        if (stubs.length) cy.add(stubs);
      }

      function repositionPorts(node) {
        var host = node.id();
        if (!crossPorts[host]) return;
        var pos = node.position();
        var w = node.outerWidth();
        ["out", "in"].forEach(function (dir) {
          var tabs = Object.keys(crossPorts[host][dir]).sort();
          tabs.forEach(function (otherTab, i) {
            var stub = cy.getElementById(
              "port::" + dir + "::" + otherTab + "::" + host
            );
            if (stub.empty()) return;
            stub.position({
              x: pos.x + (w / 2 + 13) * (dir === "out" ? 1 : -1),
              y: pos.y + (i - (tabs.length - 1) / 2) * 19,
            });
          });
        });
      }

      var rendering = false;
      function render(opts) {
        opts = opts || {};
        rendering = true;
        cy.startBatch();
        cy.elements().remove();
        cy.add(project());
        cy.endBatch();

        var eles = cy.elements();
        if (eles.length) {
          try {
            eles.layout(layoutOpts()).run();
          } catch (e) {
            eles.layout({ name: "grid", fit: false }).run();
          }
        }
        addPorts();
        applyFocus();
        rendering = false;
        if (!opts.keepViewport) fit();
        updateStats();
        updateCaption();
        // Folding a section changes what the co-reference toggle would add,
        // so its price tag is re-quoted on every projection, not just when
        // the tab changes.
        syncMentionsLabel();
        syncUrl();
      }

      function fit(target) {
        var eles = target || cy.elements();
        if (!eles.length) return;
        cy.fit(eles, 28);
      }

      /* ==============================================================
       * 6. Focus cone
       * ============================================================== */
      function coneOf(rootId) {
        var nodes = {};
        var edges = {};
        nodes[rootId] = true;
        var limit = state.depth === DEPTH_ALL ? Infinity : state.depth;

        function walk(dir) {
          var frontier = [rootId];
          var depth = 0;
          while (frontier.length && depth < limit) {
            var next = [];
            frontier.forEach(function (id) {
              var adj = (rendered[id] || {})[dir] || [];
              adj.forEach(function (link) {
                edges[link.edge] = true;
                if (!nodes[link.to]) {
                  nodes[link.to] = true;
                  next.push(link.to);
                }
              });
            });
            frontier = next;
            depth += 1;
          }
        }
        if (state.up) walk("out");     // what this node builds on
        if (state.down) walk("in");    // what builds on this node
        return { nodes: nodes, edges: edges };
      }

      function applyFocus() {
        cy.elements().removeClass("dim cone root");
        var focusbar = el("cy-focusbar");
        if (!state.focus || cy.getElementById(state.focus).empty()) {
          state.focus = null;
          if (focusbar) focusbar.hidden = true;
          renderPanel(null);
          return;
        }
        if (focusbar) focusbar.hidden = false;
        var cone = coneOf(state.focus);
        cy.batch(function () {
          cy.nodes().forEach(function (n) {
            var id = n.id();
            if (n.hasClass("stub")) {
              if (!cone.nodes[n.data("host")]) n.addClass("dim");
              return;
            }
            if (cone.nodes[id]) {
              n.addClass("cone");
              return;
            }
            // A section box stays lit when it contains a cone member, so
            // the cone is readable *in its structural context*.
            if (
              n.isParent() &&
              n.children().filter(function (c) {
                return !!cone.nodes[c.id()];
              }).length > 0
            ) {
              return;
            }
            n.addClass("dim");
          });
          cy.edges().forEach(function (e) {
            if (cone.edges[e.id()]) e.addClass("cone");
            else e.addClass("dim");
          });
          cy.getElementById(state.focus).removeClass("cone").addClass("root");
        });
        renderPanel(state.focus, cone);
      }

      /** Bring a node into view — instantly when motion is unwanted. */
      function centerOn(node, zoomTo) {
        if (!node || node.empty()) return;
        var level = zoomTo ? Math.max(cy.zoom(), 0.75) : null;
        if (REDUCED_MOTION) {
          if (level) cy.zoom({ level: level, position: node.position() });
          cy.center(node);
          return;
        }
        var anim = { center: { eles: node } };
        if (level) anim.zoom = level;
        cy.animate(anim, { duration: 220 });
      }

      function setFocus(id, opts) {
        opts = opts || {};
        state.focus = id;
        state.stub = null;
        applyFocus();
        syncUrl();
        if (id && opts.center) centerOn(cy.getElementById(id));
        announce(
          id && byId[id]
            ? "Focused " + (byId[id].label || id)
            : "Focus cleared"
        );
      }

      /* ==============================================================
       * 7. Info panel
       * ============================================================== */
      function neighbourList(id, dir) {
        var adj = (rendered[id] || {})[dir] || [];
        return adj.map(function (link) {
          return link.to;
        });
      }

      function portCount(id, dir) {
        var slot = crossPorts[id];
        if (!slot) return 0;
        var total = 0;
        Object.keys(slot[dir]).forEach(function (t) {
          total += slot[dir][t].length;
        });
        return total;
      }

      function linkRow(id) {
        var d = byId[id] || {};
        var label = esc(d.label || id);
        var tabBadge =
          d.tab && d.tab !== state.tab
            ? ' <span class="graph-tag graph-tag-' + esc(d.tab) + '">' +
              esc(TAB_LABEL[d.tab] || d.tab) + "</span>"
            : "";
        return (
          '<li><button type="button" class="graph-jump" data-node="' +
          esc(id) + '">' + label + "</button>" + tabBadge +
          (d.url
            ? ' <a class="graph-open" href="' + esc(d.url) +
              '" aria-label="Open the page for ' + label + '">↗</a>'
            : "") +
          "</li>"
        );
      }

      function listBlock(title, ids, extra) {
        if (!ids.length && !extra) return "";
        var shown = ids.slice(0, 8);
        var more = ids.length - shown.length;
        return (
          '<div class="graph-panel-block"><h3>' + esc(title) +
          ' <span class="graph-count">' + (ids.length + (extra || 0)) +
          "</span></h3><ul>" + shown.map(linkRow).join("") +
          (more > 0 ? '<li class="graph-more">+' + more + " more</li>" : "") +
          (extra
            ? '<li class="graph-more">' + extra +
              " in other tabs (see the ports on the node)</li>"
            : "") +
          "</ul></div>"
        );
      }

      function renderPanel(id, cone) {
        var body = el("cy-panel-body");
        var placeholder = el("cy-panel-empty");
        if (!body) return;
        if (!id) {
          body.hidden = true;
          body.innerHTML = "";
          if (placeholder) placeholder.hidden = false;
          return;
        }
        if (placeholder) placeholder.hidden = true;
        body.hidden = false;

        var d = byId[id] || {};
        var isGroup = d.ntype === "group";
        var uses = neighbourList(id, "out");
        var usedBy = neighbourList(id, "in");
        var coneSize = cone ? Object.keys(cone.nodes).length - 1 : 0;

        var head =
          '<p class="graph-panel-kicker">' +
          esc(isGroup ? "Section" : d.kind || "Entry") +
          ' · <span class="graph-tag graph-tag-' + esc(d.tab) + '">' +
          esc(TAB_LABEL[d.tab] || d.tab) + "</span></p>" +
          "<h2>" + esc(d.label || id) + "</h2>";

        var facts = "<dl class=\"graph-facts\">";
        if (!isGroup && d.group_label) {
          facts +=
            "<dt>Section</dt><dd>" + esc(d.group_label) + "</dd>";
        }
        if (isGroup) {
          facts +=
            "<dt>Entries</dt><dd>" + (d.n_entries || 0) +
            (isExpanded(id) ? " (expanded)" : " (collapsed)") + "</dd>";
        }
        if (d.files && d.files.length) {
          facts +=
            "<dt>Source</dt><dd>" +
            d.files
              .map(function (f) {
                return '<code class="mono">' + esc(f) + "</code>";
              })
              .join("<br>") +
            "</dd>";
        }
        if (d.idents && d.idents.length) {
          facts +=
            "<dt>Rocq</dt><dd>" +
            d.idents
              .slice(0, 6)
              .map(function (i) {
                return '<code class="mono">' + esc(i) + "</code>";
              })
              .join(" ") +
            (d.idents.length > 6
              ? ' <span class="graph-more">+' + (d.idents.length - 6) + "</span>"
              : "") +
            "</dd>";
        }
        if (d.status && d.status.length) {
          facts +=
            '<dt>Status</dt><dd class="badges">' +
            d.status
              .map(function (s) {
                return '<span class="badge badge-' + esc(s) + '">' +
                  esc(s) + "</span>";
              })
              .join(" ") +
            "</dd>";
        }
        facts +=
          "<dt>Cone</dt><dd>" + coneSize + " connected node" +
          (coneSize === 1 ? "" : "s") + " at " +
          (state.depth === DEPTH_ALL ? "any depth" : "depth " + state.depth) +
          "</dd></dl>";

        var link = d.url
          ? '<a class="graph-panel-link" href="' + esc(d.url) + '">' +
            (isGroup ? "Open section page" : "Open entry page") + " →</a>"
          : "";

        body.innerHTML =
          head + facts + link +
          listBlock("Uses", uses, portCount(id, "out")) +
          listBlock("Used by", usedBy, portCount(id, "in"));
      }

      function renderPortPanel(stub) {
        var body = el("cy-panel-body");
        var placeholder = el("cy-panel-empty");
        if (!body) return;
        if (placeholder) placeholder.hidden = true;
        body.hidden = false;
        var host = stub.data("host");
        var dir = stub.data("dir");
        var otherTab = stub.data("otherTab");
        var items = ((crossPorts[host] || {})[dir] || {})[otherTab] || [];
        var hostLabel = (byId[host] || {}).label || host;
        body.innerHTML =
          '<p class="graph-panel-kicker">Cross-tab port</p><h2>' +
          esc(hostLabel) + "</h2>" +
          "<p class=\"graph-panel-note\">" +
          esc(
            dir === "out"
              ? "Depends on " + items.length + " entr" +
                (items.length === 1 ? "y" : "ies") + " in "
              : "Used by " + items.length + " entr" +
                (items.length === 1 ? "y" : "ies") + " in "
          ) +
          '<span class="graph-tag graph-tag-' + esc(otherTab) + '">' +
          esc(TAB_LABEL[otherTab] || otherTab) +
          "</span>. Jumping to one switches the graph to that tab.</p>" +
          '<div class="graph-panel-block"><ul>' +
          items.map(linkRow).join("") +
          "</ul></div>";
      }

      /* ==============================================================
       * 8. Interaction
       * ============================================================== */
      var lastTap = { id: null, at: 0 };

      cy.on("tap", "node", function (evt) {
        var n = evt.target;
        var id = n.id();
        var now = Date.now();
        var isDouble = lastTap.id === id && now - lastTap.at < 380;
        lastTap = { id: id, at: now };

        if (n.hasClass("stub")) {
          state.stub = id;
          renderPortPanel(n);
          return;
        }
        if (n.hasClass("grp")) {
          // A section box: expand it (or fold it back), keeping the
          // viewport so the reader does not lose their place.  Groups
          // deliberately do NOT navigate on double-click — the second tap
          // of an over-eager double-click just folds the box back, and the
          // section page is one labelled click away in the panel.
          if (isExpanded(id)) delete state.expanded[id];
          else state.expanded[id] = true;
          syncExpandAll();
          render({ keepViewport: true });
          if (!state.focus) renderPanel(id);
          announce(
            (byId[id] || {}).label +
              (isExpanded(id) ? " expanded" : " collapsed")
          );
          return;
        }
        if (isDouble) {
          var url = n.data("url");
          if (url) window.location.href = url;
          return;
        }
        setFocus(id, {});
      });

      cy.on("tap", function (evt) {
        if (evt.target !== cy) return;
        if (state.focus || state.stub) setFocus(null, {});
      });

      cy.on("drag", "node", function (evt) {
        repositionPorts(evt.target);
      });
      cy.on("position", "node", function (evt) {
        if (!rendering) repositionPorts(evt.target);
      });

      cy.on("mouseover", "node", function () {
        container.style.cursor = "pointer";
      });
      cy.on("mouseout", "node", function () {
        container.style.cursor = "default";
      });

      document.addEventListener("keydown", function (ev) {
        if (ev.key === "Escape") {
          if (searchBox && document.activeElement === searchBox) {
            closeResults();
            return;
          }
          if (state.focus || state.stub) setFocus(null, {});
        } else if (
          ev.key === "/" &&
          document.activeElement !== searchBox &&
          !/^(INPUT|TEXTAREA|SELECT)$/.test(
            (document.activeElement || {}).tagName || ""
          )
        ) {
          if (searchBox) {
            ev.preventDefault();
            searchBox.focus();
          }
        }
      });

      /* ==============================================================
       * 9. Controls
       * ============================================================== */
      function announce(msg) {
        var live = el("cy-live");
        if (live) live.textContent = msg;
      }

      function segment(rootId, onPick) {
        var root = el(rootId);
        if (!root) return function () {};
        var btns = Array.prototype.slice.call(
          root.querySelectorAll("[role='radio']")
        );
        btns.forEach(function (b, i) {
          b.addEventListener("click", function () {
            onPick(b);
          });
          // Roving tabindex: arrows move (and pick) within the group, the
          // way a native radiogroup behaves.
          b.addEventListener("keydown", function (ev) {
            var step =
              ev.key === "ArrowRight" || ev.key === "ArrowDown"
                ? 1
                : ev.key === "ArrowLeft" || ev.key === "ArrowUp"
                ? -1
                : 0;
            if (!step) return;
            ev.preventDefault();
            var next = btns[(i + step + btns.length) % btns.length];
            next.focus();
            onPick(next);
          });
        });
        return function (isOn) {
          btns.forEach(function (b) {
            var on = isOn(b);
            b.setAttribute("aria-checked", on ? "true" : "false");
            b.classList.toggle("is-on", on);
            b.tabIndex = on ? 0 : -1;
          });
        };
      }

      var syncTabSeg = segment("cy-tabs", function (b) {
        var next = b.getAttribute("data-tab");
        if (next === state.tab) return;
        state.tab = next;
        state.focus = null;
        state.stub = null;
        state.expanded = budgetedExpansion(next);
        syncExpandAll();
        syncTabSeg(function (x) {
          return x.getAttribute("data-tab") === state.tab;
        });
        syncMentionsLabel();
        render({});
        announce(TAB_LABEL[state.tab] + " tab shown");
      });
      syncTabSeg(function (b) {
        return b.getAttribute("data-tab") === state.tab;
      });

      var syncDepthSeg = segment("cy-depths", function (b) {
        state.depth = parseInt(b.getAttribute("data-depth"), 10) || DEPTH_ALL;
        syncDepthSeg(function (x) {
          return (
            (parseInt(x.getAttribute("data-depth"), 10) || DEPTH_ALL) ===
            state.depth
          );
        });
        applyFocus();
      });
      syncDepthSeg(function (b) {
        return (
          (parseInt(b.getAttribute("data-depth"), 10) || DEPTH_ALL) ===
          state.depth
        );
      });

      var mentionsBox = el("cy-mentions");
      function syncMentionsLabel() {
        var out = el("cy-mentions-count");
        if (!out) return;
        var cost = coReferenceCost();
        out.textContent = state.mentions
          ? cost.edges + " in this view"
          : "+" + cost.edges + " in this view";
        // The dataset figure is real, just not the one the checkbox owes
        // the reader; it stays available as the control's tooltip.
        out.title =
          cost.total + " co-reference edge" + (cost.total === 1 ? "" : "s") +
          " touch the " + (TAB_LABEL[state.tab] || state.tab) +
          " tab in the data. In this view they draw " + cost.edges +
          " dashed edge" + (cost.edges === 1 ? "" : "s") +
          (cost.ports
            ? " and add " + cost.ports + " cross-tab port entr" +
              (cost.ports === 1 ? "y" : "ies")
            : "") +
          "; the rest are inside a folded section, or duplicate a proof " +
          "dependency already drawn.";
      }
      if (mentionsBox) {
        mentionsBox.checked = state.mentions;
        mentionsBox.addEventListener("change", function () {
          state.mentions = mentionsBox.checked;
          syncMentionsLabel();
          render({ keepViewport: true });
          announce(
            state.mentions
              ? "Prose co-references shown"
              : "Prose co-references hidden"
          );
        });
      }
      syncMentionsLabel();

      var expandBox = el("cy-expand-all");
      function syncExpandAll() {
        if (!expandBox) return;
        var groups = groupsOfTab[state.tab] || [];
        var open = groups.filter(isExpanded).length;
        expandBox.checked = groups.length > 0 && open === groups.length;
        expandBox.indeterminate = open > 0 && open < groups.length;
      }
      if (expandBox) {
        expandBox.addEventListener("change", function () {
          var groups = groupsOfTab[state.tab] || [];
          state.expanded = {};
          if (expandBox.checked) {
            groups.forEach(function (g) {
              state.expanded[g] = true;
            });
          }
          render({});
          announce(
            expandBox.checked ? "All sections expanded" : "All sections collapsed"
          );
        });
      }

      var resetBtn = el("cy-reset");
      if (resetBtn) {
        resetBtn.addEventListener("click", function () {
          state.expanded = budgetedExpansion(state.tab);
          state.focus = null;
          state.stub = null;
          state.mentions = false;
          state.up = true;
          state.down = true;
          state.depth = DEPTH_ALL;
          if (mentionsBox) mentionsBox.checked = false;
          var upBox = el("cy-dir-up");
          var downBox = el("cy-dir-down");
          if (upBox) upBox.checked = true;
          if (downBox) downBox.checked = true;
          syncDepthSeg(function (x) {
            return (
              (parseInt(x.getAttribute("data-depth"), 10) || DEPTH_ALL) ===
              DEPTH_ALL
            );
          });
          syncMentionsLabel();
          syncExpandAll();
          render({});
          announce("View reset");
        });
      }

      ["up", "down"].forEach(function (dir) {
        var box = el("cy-dir-" + dir);
        if (!box) return;
        box.checked = state[dir];
        box.addEventListener("change", function () {
          state[dir] = box.checked;
          if (!state.up && !state.down) {
            // Never leave the cone empty in both directions.
            var other = dir === "up" ? "down" : "up";
            state[other] = true;
            var otherBox = el("cy-dir-" + other);
            if (otherBox) otherBox.checked = true;
          }
          applyFocus();
        });
      });

      // Panel + search results delegate their node jumps here.
      document.addEventListener("click", function (ev) {
        var btn = ev.target.closest && ev.target.closest(".graph-jump");
        if (!btn) return;
        ev.preventDefault();
        jumpTo(btn.getAttribute("data-node"));
      });

      /** Focus a node wherever it lives: switch tab and open its section. */
      function jumpTo(id) {
        var d = byId[id];
        if (!d) return;
        var target = id;
        if (d.ntype === "entry") {
          if (d.tab !== state.tab) {
            state.tab = d.tab;
            state.expanded = budgetedExpansion(d.tab);
            syncTabSeg(function (x) {
              return x.getAttribute("data-tab") === state.tab;
            });
          }
          state.expanded[d.parent] = true;
        } else if (d.ntype === "group") {
          if (d.tab !== state.tab) {
            state.tab = d.tab;
            state.expanded = budgetedExpansion(d.tab);
            syncTabSeg(function (x) {
              return x.getAttribute("data-tab") === state.tab;
            });
          }
        } else {
          return;
        }
        syncExpandAll();
        state.focus = target;
        state.stub = null;
        render({ keepViewport: false });
        var node = cy.getElementById(target);
        if (!node.empty()) {
          centerOn(node, true);
          node.addClass("hit");
          window.setTimeout(function () {
            node.removeClass("hit");
          }, 1400);
        }
        announce("Jumped to " + (d.label || id));
      }

      /* ==============================================================
       * 10. Search (titles + Rocq identifiers, across every tab)
       * ============================================================== */
      var searchBox = el("cy-search");
      var resultsBox = el("cy-search-results");

      function closeResults() {
        if (!resultsBox) return;
        resultsBox.hidden = true;
        resultsBox.innerHTML = "";
        if (searchBox) searchBox.setAttribute("aria-expanded", "false");
      }

      function runSearch(q) {
        q = q.trim().toLowerCase();
        if (!resultsBox) return;
        if (q.length < 2) {
          closeResults();
          return;
        }
        var hits = [];
        for (var i = 0; i < searchIndex.length && hits.length < MAX_RESULTS; i++) {
          var it = searchIndex[i];
          if (it.hay.indexOf(q) < 0) continue;
          var matchIdent = null;
          for (var k = 0; k < it.idents.length; k++) {
            if (it.idents[k].toLowerCase().indexOf(q) >= 0) {
              matchIdent = it.idents[k];
              break;
            }
          }
          hits.push({ it: it, ident: matchIdent });
        }
        if (!hits.length) {
          resultsBox.hidden = false;
          resultsBox.innerHTML =
            '<li class="graph-search-none">No entry or identifier matches “' +
            esc(q) + "”</li>";
          if (searchBox) searchBox.setAttribute("aria-expanded", "true");
          return;
        }
        resultsBox.innerHTML = hits
          .map(function (h) {
            return (
              '<li role="option" aria-selected="false"><button type="button" ' +
              'class="graph-result" data-node="' + esc(h.it.id) + '">' +
              '<span class="graph-result-label">' + esc(h.it.label) +
              "</span>" +
              '<span class="graph-tag graph-tag-' + esc(h.it.tab) + '">' +
              esc(TAB_LABEL[h.it.tab] || h.it.tab) + "</span>" +
              (h.ident
                ? '<code class="mono graph-result-ident">' + esc(h.ident) +
                  "</code>"
                : '<span class="graph-result-sec">' + esc(h.it.group) +
                  "</span>") +
              "</button></li>"
            );
          })
          .join("");
        resultsBox.hidden = false;
        if (searchBox) searchBox.setAttribute("aria-expanded", "true");
      }

      if (searchBox && resultsBox) {
        searchBox.addEventListener("input", function () {
          runSearch(searchBox.value);
        });
        searchBox.addEventListener("keydown", function (ev) {
          if (ev.key === "ArrowDown") {
            var first = resultsBox.querySelector(".graph-result");
            if (first) {
              ev.preventDefault();
              first.focus();
            }
          } else if (ev.key === "Enter") {
            var hit = resultsBox.querySelector(".graph-result");
            if (hit) {
              ev.preventDefault();
              hit.click();
            }
          }
        });
        resultsBox.addEventListener("keydown", function (ev) {
          var items = Array.prototype.slice.call(
            resultsBox.querySelectorAll(".graph-result")
          );
          var i = items.indexOf(document.activeElement);
          if (ev.key === "ArrowDown" && i >= 0 && i < items.length - 1) {
            ev.preventDefault();
            items[i + 1].focus();
          } else if (ev.key === "ArrowUp") {
            ev.preventDefault();
            if (i > 0) items[i - 1].focus();
            else searchBox.focus();
          } else if (ev.key === "Escape") {
            closeResults();
            searchBox.focus();
          }
        });
        // Keep the listbox's selected option in step with real DOM focus.
        resultsBox.addEventListener("focusin", function (ev) {
          Array.prototype.forEach.call(
            resultsBox.querySelectorAll("[role='option']"),
            function (li) {
              li.setAttribute(
                "aria-selected",
                li.contains(ev.target) ? "true" : "false"
              );
            }
          );
        });
        resultsBox.addEventListener("click", function (ev) {
          var btn = ev.target.closest && ev.target.closest(".graph-result");
          if (!btn) return;
          ev.preventDefault();
          var id = btn.getAttribute("data-node");
          closeResults();
          searchBox.value = "";
          jumpTo(id);
        });
        document.addEventListener("click", function (ev) {
          if (
            resultsBox.hidden ||
            resultsBox.contains(ev.target) ||
            ev.target === searchBox
          ) {
            return;
          }
          closeResults();
        });
      }

      /* ==============================================================
       * 11. Caption + stats line
       * ============================================================== */

      /** Re-state the caption for the tab actually on screen.
       *
       * The caption used to quote the three-tab entry total directly above a
       * stats line reporting one tab with its sections folded, so the page
       * contradicted itself on first paint.  ``meta.nodes_by_tab`` already
       * carries the per-tab split; the caption now describes the tab you are
       * looking at, and the stats line below it describes what is drawn of
       * that tab right now. */
      function updateCaption() {
        var capEl = el("cy-caption");
        if (!capEl) return;
        var by = (meta.nodes_by_tab || {})[state.tab] || {};
        var ents = by.entries || 0;
        var groups = by.groups || 0;
        capEl.textContent =
          (TAB_LABEL[state.tab] || state.tab) + " tab: " + ents + " entr" +
          (ents === 1 ? "y" : "ies") + " in " + groups + " section" +
          (groups === 1 ? "" : "s");
      }

      function updateStats() {
        var statsEl = el("cy-stats");
        if (!statsEl) return;
        var groups = cy.nodes(".grp").length;
        var ents = cy.nodes(".ent").length;
        var deps = cy.edges(".depends").length;
        var ments = cy.edges(".mentions").length;
        var ports = cy.nodes(".stub").length;
        var open = cy.nodes(".grp-open").length;
        var bits = [
          "Drawn now: " + groups + " section" + (groups === 1 ? "" : "s") +
            " (" + open + " unfolded)",
          ents + " entr" + (ents === 1 ? "y" : "ies"),
          deps + " dependency edge" + (deps === 1 ? "" : "s"),
        ];
        if (state.mentions) {
          bits.push(ments + " co-reference edge" + (ments === 1 ? "" : "s"));
        }
        if (ports) bits.push(ports + " cross-tab port" + (ports === 1 ? "" : "s"));
        statsEl.textContent = bits.join(" · ");
      }

      /* -- go ------------------------------------------------------- */
      syncExpandAll();
      render({});
      if (state.focus) {
        var f = cy.getElementById(state.focus);
        if (!f.empty()) {
          cy.center(f);
        }
      }

      var resizeTimer = null;
      window.addEventListener("resize", function () {
        window.clearTimeout(resizeTimer);
        resizeTimer = window.setTimeout(function () {
          cy.resize();
        }, 150);
      });
    }
  });
})();
