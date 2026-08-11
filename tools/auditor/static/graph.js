/* The dependency graph, drawn as ARCHITECTURAL SWIM-LANES.
 *
 * The data (graph.json, emitted by tools/auditor/graph.py) is the whole
 * three-tab relation: ~220 entry nodes inside ~20 section groups, plus
 * ~1400 edges of two kinds (real .glob proof dependencies, and weaker doc
 * co-references).  Drawing all of that at once produces a hairball, so
 * this client never does.  It renders a PROJECTION of the data:
 *
 *   * ONE tab at a time (default: ?tab=… , else "paper");
 *   * "depends" edges only, unless prose co-references are switched on;
 *   * every entry placed in the LANE of its architectural layer —
 *     Foundations → Measurable → Linear ∥ Stable → Exponential → CBV →
 *     PPL, left to right, the CI-enforced import order of theories/ (see
 *     tools/check_layers.py).  Nothing on the left can depend on anything
 *     to its right, so the picture reads as a stack of layers instead of
 *     "wherever the layout engine happened to put it";
 *   * edges that leave the visible tab drawn as small stub PORTS on the
 *     node (one per foreign tab, count-badged, click to list) rather
 *     than as edges pointing at nodes that are not on screen.
 *
 * The lane layout is a PRESET: x comes from the lane (and its sub-band —
 * two parallel directories such as homs ∥ stable are stacked bands of one
 * lane), y from a deterministic within-lane order — section blocks, then
 * a two-pass barycentre of each node's neighbours to cut crossings.  No
 * physics and no randomness: the same graph.json always draws the same
 * picture.  Dagre is kept for the legacy "group by section" view only.
 *
 * On top of that projection sits the interaction the page exists for:
 * clicking an entry dims everything outside its dependency CONE — the
 * transitive "uses" side, the transitive "used by" side, each toggleable
 * with a depth limit — and shows the entry's card link in a side panel.
 * The same dimming mechanism, multi-target, drives the "leaves" filter
 * that lights every headline result at once.  Double-click (or the panel
 * link) opens the entry page; Esc or a click on the background clears.
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
  var NODE_BUDGET = 40;       // drawn nodes the "group by section" view aims for

  /* -- readability ------------------------------------------------------
   * The label size is the contract: a node label is drawn at NODE_FONT
   * graph units, so at zoom z it lands on screen at NODE_FONT * z pixels.
   * Auto-fit may therefore never zoom below MIN_LABEL_PX / NODE_FONT — a
   * graph too big to fit at a readable size is one you PAN, not one drawn
   * at 5px. */
  var NODE_FONT = 13;
  var MIN_LABEL_PX = 12;
  var READ_ZOOM = MIN_LABEL_PX / NODE_FONT;   // ≈ 0.92
  var MAX_FIT_ZOOM = 1.4;     // don't blow a three-node tab up to fill 800px
  var FIT_PAD = 26;
  var ZOOM_STEP = 1.3;

  /* -- lane geometry, in graph units (== CSS px at zoom 1) -------------- */
  var NODE_GAP = 9;           // between stacked entries of one section
  var SECTION_GAP = 16;       // extra between two section blocks
  var BAND_GAP = 44;          // between the stacked sub-bands of one lane
  var LANE_PAD = 20;          // band background padding around its content
  var LANE_GAP = 52;          // between two lane bands
  var COL_GAP = 22;           // between two sub-columns of one lane
  /* The height budget for a WHOLE LANE — every band it stacks, plus the gaps
   * and box chrome between them — above which the lane wraps into
   * sub-columns.  Kept near one canvas height (at the readability zoom) on
   * purpose: the reader then pans in ONE direction — right, along the lanes —
   * instead of hunting a 2000px ribbon up and down, and the lane caption
   * (drawn at the top of the box) stays on screen to say where "here" is.
   * A constant, not a viewport reading, so the picture does not depend on the
   * window it was first opened in.
   *
   * Per LANE, emphatically not per band: handing each band the full budget
   * made the two-band Linear ∥ Stable lane 1133 units tall against a 700 cap,
   * which broke the invariant on the very lane holding 63 of the paper tab's
   * 142 entries.  An extra band must buy more COLUMNS, never more height. */
  var TARGET_COL_H = 700;
  var MIN_BAND_H = 150;       // a band never wraps below this, budget or not
  var BAND_CHROME = 22;       // the sub-band box's own padding (see :boxes)
  var MIN_LANE_W = 116;       // a POPULATED lane is at least this wide
  /* An EMPTY lane is a thin captioned rail, not a full column.  A layer that
   * this tab does not touch is worth one line of "the layer exists and is
   * empty here" — it is not worth MIN_LANE_W of blank canvas, which on the
   * Examples tab meant five empty lanes eating 58% of the fitted width while
   * the twenty real nodes shared an 18% sliver. */
  var EMPTY_LANE_W = 26;
  var EMPTY_LANE_GAP = 22;    // rails also pack tighter than real lanes
  var BARY_PASSES = 2;        // crossing-reduction sweeps (deterministic)

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
      band: v("--g-band", "#eceef2"),
      bandLine: v("--g-band-line", "#d3d7de"),
      bandFg: v("--g-band-fg", "#5a5f6b"),
      leaf: v("--g-leaf", "#b4530a"),
      rootMark: v("--g-root", "#8b8f98"),
      backward: v("--g-backward", "#b91c1c"),
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
      var entriesOfTab = {};         // tab -> [entry id] in document order
      var entriesOfGroup = {};       // group id -> [entry id]
      var groupIndex = {};           // group id -> its index within its tab
      var entryIndex = {};           // entry id -> its index within its tab
      var entryIds = [];             // every entry id, document order
      TABS.forEach(function (t) {
        groupsOfTab[t] = [];
        entriesOfTab[t] = [];
      });

      (data.nodes || []).forEach(function (n) {
        var d = n.data;
        byId[d.id] = d;
        if (d.ntype === "group") {
          if (groupsOfTab[d.tab]) {
            groupIndex[d.id] = groupsOfTab[d.tab].length;
            groupsOfTab[d.tab].push(d.id);
          }
          entriesOfGroup[d.id] = [];
        }
      });
      (data.nodes || []).forEach(function (n) {
        var d = n.data;
        if (d.ntype !== "entry") return;
        entryIds.push(d.id);
        if (entriesOfTab[d.tab]) {
          entryIndex[d.id] = entriesOfTab[d.tab].length;
          entriesOfTab[d.tab].push(d.id);
        }
        if (entriesOfGroup[d.parent]) entriesOfGroup[d.parent].push(d.id);
      });

      /* The lane table travels in the data (graph.py owns it, so the client
       * cannot drift from the layer checker).  An older graph.json without
       * it degrades to a single unnamed lane, which is just the flat view. */
      var laneDefs = (meta.lanes || []).length
        ? meta.lanes
        : [{ index: 0, id: "all", title: "All", subtitle: "", bands: [{ index: 0, id: "all", title: "" }] }];
      /* Leaf/root marks mean nothing when the build had no .glob data: with
       * no real dependency relation EVERY node is trivially both, so the
       * marks would flag the whole canvas.  Say so instead of drawing it. */
      var marksMeaningful = (meta.n_depends || 0) > 0;

      function laneOf(d) {
        var i = d && typeof d.lane === "number" ? d.lane : 0;
        return Math.max(0, Math.min(laneDefs.length - 1, i));
      }
      function bandOf(d) {
        var lane = laneDefs[laneOf(d)] || {};
        var bands = lane.bands || [{}];
        var i = d && typeof d.band === "number" ? d.band : 0;
        return Math.max(0, Math.min(bands.length - 1, i));
      }
      /* An ISOLATED entry (no proof dependency either way) satisfies the
       * letter of "leaf" without being a headline result — flagging the 14
       * of them would spend the strongest mark on the least interesting
       * nodes.  They get the quiet root mark instead. */
      function isLeaf(id) {
        var d = byId[id];
        return !!(
          marksMeaningful && d && d.ntype === "entry" && d.leaf && !d.isolated
        );
      }
      function isRoot(id) {
        var d = byId[id];
        return !!(marksMeaningful && d && d.ntype === "entry" && d.root);
      }

      var rawEdges = (data.edges || [])
        .map(function (e) {
          return {
            s: e.data.source,
            t: e.data.target,
            kind: e.data.kind === "depends" ? "depends" : "mentions",
            // graph.py flags a dependency that runs AGAINST the lane order
            // (its source sits left of its target).  Carried through so the
            // canvas can draw the exceptions instead of the hero copy having
            // to promise they do not exist.
            back: !!e.data.backward,
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
        // "lanes" (default): entries placed by architectural layer.
        // "sections": the legacy compound view, sections foldable, dagre.
        view: params.get("view") === "sections" ? "sections" : "lanes",
        mentions: params.get("co") === "1",
        expanded: {},              // group id -> true (sections view only)
        focus: null,               // rendered node id
        mark: params.get("mark") === "leaves" ? "leaves" : null,
        up: true,                  // cone: what the node builds on
        down: true,                // cone: what builds on the node
        depth: DEPTH_ALL,
        stub: null,                // id of the cross-tab port being listed
      };
      if (!marksMeaningful) state.mark = null;

      /* SECTIONS VIEW ONLY.  There, a page whose first paint is eight boxes
       * reads as a graph with eight nodes and gives the reader nothing to
       * click that they can recognise; a page whose first paint is every
       * entry is a hairball, because nothing organises the entries.  So the
       * section view unfolds sections, in document order, while the drawn
       * count stays inside a budget.  The lane view needs none of this: the
       * lanes ARE the organisation, so every entry is drawn. */
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
        if (state.view !== "lanes") p.set("view", state.view);
        if (state.mentions) p.set("co", "1");
        if (state.mark) p.set("mark", state.mark);
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

      /** The node an entry is DRAWN as: itself, or its collapsed group.
       *
       * The lane view has no collapsing — placing entries by architectural
       * layer is precisely what replaces "fold the sections away" as the
       * way the picture stays readable — so there an entry is always drawn
       * as itself. */
      function renderIdOf(entryId) {
        var d = byId[entryId];
        if (d.ntype !== "entry") return entryId;
        if (state.view === "lanes") return entryId;
        return isExpanded(d.parent) ? entryId : d.parent;
      }

      /* ==============================================================
       * 3. Projection — data + state -> the elements actually drawn
       * ============================================================== */
      var rendered = {};   // rendered node id -> {out:[], in:[]} adjacency
      var crossPorts = {}; // rendered node id -> {out:{tab:[items]}, in:{…}}
      var coPorts = {};    // rendered node id -> {tab:[items]} (undirected)

      /** Fold the raw relation onto the nodes currently DRAWN.
       *
       * Returns ``{agg, ports, co}``:
       *
       *   * ``agg``   — one slot per drawn pair, keeping the two kinds APART
       *     (``depends`` / ``mentions``) so the caller can style and weigh
       *     each on its own evidence.  A dependency slot is keyed by the
       *     ORDERED pair; a co-reference slot is keyed by the pair in
       *     canonical order, because that relation has no direction and two
       *     opposed halves of one undirected fact must not draw as two
       *     lines facing each other;
       *   * ``ports`` — per drawn node, per direction, per foreign tab, the
       *     DISTINCT foreign entries it reaches BY A DEPENDENCY.  Distinct
       *     is the whole point: a collapsed section funnels all of its
       *     entries into one bucket, so the same target arrives once per raw
       *     edge, and a bucket that counted arrivals would badge (and list)
       *     the same entry several times over;
       *   * ``co``    — the same, for cross-tab CO-REFERENCES, in a separate
       *     direction-free bucket.  A port is an inherently directional
       *     device — left = what this entry uses, right = what uses it — so
       *     an undirected relation may not be drawn as one, or the port
       *     panel ends up announcing "Depends on 3 entries in PPL" about
       *     three prose mentions.  The entry panel reports these as a count.
       *
       * ``withMentions`` is passed explicitly rather than read from the
       * view state so the co-reference toggle can price itself against the
       * same code that draws the canvas.
       */
      function aggregate(withMentions) {
        var tab = state.tab;
        var agg = {};
        var ports = {};
        var co = {};
        var seen = {};   // host \0 dir \0 tab \0 foreign entry -> true

        function port(host, dir, otherTab, otherId) {
          var mark = [host, dir, otherTab, otherId].join("\u0000");
          if (seen[mark]) return;
          seen[mark] = true;
          var slot = ports[host] || (ports[host] = { out: {}, in: {} });
          var bucket = slot[dir][otherTab] || (slot[dir][otherTab] = []);
          bucket.push(otherId);
        }

        function coPort(host, otherTab, otherId) {
          var mark = [host, "co", otherTab, otherId].join("\u0000");
          if (seen[mark]) return;
          seen[mark] = true;
          var slot = co[host] || (co[host] = {});
          var bucket = slot[otherTab] || (slot[otherTab] = []);
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
            // Folding a section can bring two co-references that ran between
            // different entries onto the same pair of boxes in opposite
            // orientations.  Canonicalise: one undirected fact, one slot.
            if (e.kind === "mentions" && b < a) {
              var swap = a; a = b; b = swap;
            }
            var key = a + "\u0000" + b;
            var slot = agg[key];
            if (!slot) {
              slot = agg[key] = { s: a, t: b, depends: 0, mentions: 0, back: 0 };
            }
            slot[e.kind] += 1;
            if (e.kind === "depends" && e.back) slot.back += 1;
          } else if (e.kind === "mentions") {
            if (sIn) coPort(renderIdOf(e.s), byId[e.t].tab, e.t);
            else coPort(renderIdOf(e.t), byId[e.s].tab, e.s);
          } else if (sIn) {
            port(renderIdOf(e.s), "out", byId[e.t].tab, e.t);
          } else {
            port(renderIdOf(e.t), "in", byId[e.s].tab, e.s);
          }
        });
        return { agg: agg, ports: ports, co: co };
      }

      /** What switching co-references ON actually costs IN THIS VIEW.
       *
       * Not the dataset's co-reference count: in a view with sections
       * folded, most raw co-references are internal to one box, or leave the
       * tab, or name a pair the proofs already relate (in which case the
       * payload carries only the dependency).  Quoting the raw number next
       * to a checkbox that visibly adds a handful of edges is what made the
       * flagship control look broken, so the label quotes what will be
       * drawn: the dashed edges, plus the cross-tab partners the panel
       * gains — ``ports`` for historical reasons, though a co-reference
       * gets no port.
       */
      function coReferenceCost() {
        var on = aggregate(true);
        var dashed = 0;
        Object.keys(on.agg).forEach(function (k) {
          if (!on.agg[k].depends) dashed += 1;
        });
        // A cross-tab co-reference gets no port — a port points a way and
        // this relation does not — so it is listed in the entry panel
        // instead, and counted here so the tooltip still accounts for it.
        var listed = 0;
        Object.keys(on.co).forEach(function (host) {
          Object.keys(on.co[host]).forEach(function (t) {
            listed += on.co[host][t].length;
          });
        });
        return {
          edges: dashed,
          ports: listed,
          total: tabMentions[state.tab] || 0,
        };
      }

      /** Entry label + its leaf mark.
       *
       * The flag rides IN the label (rather than as a decoration only the
       * canvas knows about) so it survives the panel, the announcer and a
       * screen reader reading the node out. */
      function entryLabel(d) {
        return elide(d.label, MAX_LABEL) + (isLeaf(d.id) ? "  ⚑" : "");
      }

      function entryClasses(d) {
        var cls = "ent";
        if (isLeaf(d.id)) cls += " is-leaf";
        else if (isRoot(d.id)) cls += " is-root";
        return cls;
      }

      /** The LANE projection: every entry of the tab, no compound boxes. */
      function projectLanes() {
        var tab = state.tab;
        var nodes = [];
        rendered = {};
        crossPorts = {};
        coPorts = {};

        (entriesOfTab[tab] || []).forEach(function (eid) {
          var d = byId[eid];
          nodes.push({
            data: {
              id: eid,
              label: entryLabel(d),
              title: d.label,
              ntype: "entry",
              tab: tab,
              kind: d.kind || "",
              url: d.url || "",
              lane: laneOf(d),
              band: bandOf(d),
              sec: d.parent || "",
              secIdx: groupIndex[d.parent] || 0,
              doc: entryIndex[eid] || 0,
            },
            classes: entryClasses(d),
          });
          rendered[eid] = { out: [], in: [] };
        });

        return nodes.concat(buildEdges());
      }

      /** The legacy SECTION projection: compound boxes, foldable, dagre. */
      function projectSections() {
        var tab = state.tab;
        var nodes = [];
        rendered = {};
        crossPorts = {};
        coPorts = {};

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
                label: entryLabel(d),
                title: d.label,
                ntype: "entry",
                tab: tab,
                kind: d.kind || "",
                url: d.url || "",
                lane: laneOf(d),
                band: bandOf(d),
              },
              classes: entryClasses(d),
            });
            rendered[eid] = { out: [], in: [] };
          });
        });

        return nodes.concat(buildEdges());
      }

      /** Fold the relation onto the drawn nodes and emit the edge elements.
       *
       * Shared by both projections: which nodes are drawn differs, the way
       * edges aggregate onto them does not. */
      function buildEdges() {
        var edges = [];
        var built = aggregate(state.mentions);
        crossPorts = built.ports;
        coPorts = built.co;

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
          // A dependency running against the lane order gets its own class:
          // the reader who spots a right-to-left arrow can see at a glance
          // that the picture KNOWS about it, rather than concluding the lane
          // order is a lie.
          var backward = kind === "depends" && a.back > 0;
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
              nb: a.back,
            },
            classes: backward ? kind + " backward" : kind,
          });
          rendered[a.s].out.push({ to: a.t, edge: id, kind: kind });
          rendered[a.t].in.push({ to: a.s, edge: id, kind: kind });
          if (kind === "mentions") {
            // Undirected, so it is filed BOTH ways.  Anything reading this
            // adjacency — the focus cone, the info panel — then cannot pick
            // a direction out of the storage order, and the cone reaches a
            // co-referenced neighbour whichever way the reader is walking.
            rendered[a.t].out.push({ to: a.s, edge: id, kind: kind });
            rendered[a.s].in.push({ to: a.t, edge: id, kind: kind });
          }
        });

        return edges;
      }

      function project() {
        return state.view === "lanes" ? projectLanes() : projectSections();
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
              padding: "9px",
              "text-valign": "center",
              "text-halign": "center",
              color: pal.nodeFg,
              // The readability contract (see READ_ZOOM): 13 graph units,
              // never auto-fitted below 12/13 zoom, so a label is never
              // drawn smaller than 12px.
              "font-size": NODE_FONT,
              "font-weight": 600,
              "border-width": 0,
              "z-index": 3,
              "transition-property": "opacity",
              "transition-duration": REDUCED_MOTION ? 0 : 120,
            },
          },
          // -- the two data-driven marks --------------------------------
          // A LEAF is a headline result: nothing in the whole three-tab
          // dependency relation builds on it.  Heavy border + the ⚑ its
          // label already carries.
          {
            selector: "node.is-leaf",
            style: {
              "border-width": 3,
              "border-color": pal.leaf,
              "border-opacity": 1,
            },
          },
          // A ROOT rests on nothing: the complementary, quieter mark.
          {
            selector: "node.is-root",
            style: {
              "border-width": 1.6,
              "border-style": "dotted",
              "border-color": pal.rootMark,
              "border-opacity": 0.95,
            },
          },
          // -- lane bands (background, below the edges) ------------------
          {
            selector: "node.lane-band",
            style: {
              shape: "round-rectangle",
              width: "data(w)",
              height: "data(h)",
              label: "data(label)",
              "background-color": pal.band,
              "background-opacity": 0.75,
              "border-width": 1,
              "border-color": pal.bandLine,
              "border-opacity": 0.9,
              "text-valign": "top",
              "text-halign": "center",
              "text-margin-y": -7,
              "text-max-width": 260,
              "text-wrap": "wrap",
              color: pal.bandFg,
              "font-size": 13,
              "font-weight": 700,
              events: "no",           // clicks fall through to the canvas
              "z-index": 0,
              "z-index-compare": "manual",
              "z-compound-depth": "bottom",
            },
          },
          // A layer this tab does not touch: a thin rail with its name read
          // vertically.  Present (the layer exists), and cheap (it costs
          // EMPTY_LANE_W, not a full column of blank canvas).
          {
            selector: "node.lane-empty",
            style: {
              "background-opacity": 0.4,
              "border-style": "dashed",
              "border-opacity": 0.55,
              "text-valign": "center",
              "text-margin-y": 0,
              "text-rotation": (-90 * Math.PI) / 180,
              "text-max-width": 400,
              "text-wrap": "none",
              "font-size": 11,
              "font-weight": 600,
              opacity: 0.7,
            },
          },
          {
            selector: "node.lane-subband",
            style: {
              "background-color": pal.band,
              "background-opacity": 0.55,
              "border-style": "dashed",
              "border-opacity": 0.7,
              "font-size": 11,
              "font-weight": 600,
              "text-margin-y": -4,
              "z-index": 1,
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
              "font-size": NODE_FONT,
              "font-weight": 700,
              "text-margin-y": 0,
              "z-index": 3,
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
              "font-size": 12,
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
              "font-size": 9,
              "font-weight": 700,
              "text-valign": "center",
              "text-halign": "center",
              "z-index": 5,
              "z-compound-depth": "top",
            },
          },
          // An edge is stored as "A uses B" (source = the dependent), but it
          // is DRAWN with the arrowhead on the A end, so every arrow runs
          // left → right along the lanes: from the lemma to the result that
          // rests on it.  Both views agree on this (the section view ranks
          // right-to-left for the same reason), so the reader never has to
          // re-learn which way an arrow points.
          {
            selector: "edge",
            style: {
              "curve-style": "bezier",
              "target-arrow-shape": "none",
              "source-arrow-shape": "triangle",
              "arrow-scale": 0.8,
              width: "mapData(w, 1, 8, 1.3, 3.6)",
              "line-color": pal.edge,
              "source-arrow-color": pal.edge,
              opacity: 0.42,
              "z-index": 2,
            },
          },
          // A co-reference is UNDIRECTED — both entries' text names the same
          // identifier, which points no way at all.  So it is drawn with NO
          // arrowhead on either end: an arrow here would restate, on the
          // canvas, the very direction claim the cards were fixed for
          // ("Thm 4.19 · Used by · Thm 4.18", minted by a sentence in Thm
          // 4.18 pointing the reader FORWARD).  Dashed + arrowless is the
          // whole visual grammar of the relation.
          {
            selector: "edge.mentions",
            style: {
              "line-style": "dashed",
              "line-color": pal.mention,
              "source-arrow-shape": "none",
              "target-arrow-shape": "none",
              opacity: 0.4,
            },
          },
          // A dependency that runs against the lane order.  Drawn, not
          // hidden and not silently blended into the others: it is the
          // visible half of the count the legend reports.
          {
            selector: "edge.backward",
            style: {
              "line-style": "dotted",
              "line-color": pal.backward,
              "source-arrow-color": pal.backward,
              "target-arrow-shape": "circle",
              "target-arrow-color": pal.backward,
              "arrow-scale": 0.7,
              opacity: 0.72,
              "z-index": 3,
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
              "source-arrow-color": pal.focus,
              "z-index": 4,
            },
          },
          {
            selector: "node.focusroot",
            style: {
              "border-width": 3.2,
              "border-color": pal.focus,
              "border-opacity": 1,
            },
          },
          // Multi-target highlight (the "leaves" quick filter) — the same
          // dimming mechanism as the cone, with a set instead of one root.
          {
            selector: "node.marked",
            style: {
              "border-width": 3.2,
              "border-color": pal.leaf,
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
       * 5. Layout — swim-lanes (preset) or the legacy dagre ranking
       * ============================================================== */

      /** A node's box, measured, with a font-metric fallback.
       *
       * Cytoscape sizes ``width: label`` from a canvas text measurement,
       * which a headless harness (and a browser that has not painted yet)
       * cannot give.  Falling back to an estimate keeps the stacking sane
       * there instead of piling every node at height 0. */
      function boxOf(n) {
        var w = 0;
        var h = 0;
        try {
          w = n.outerWidth();
          h = n.outerHeight();
        } catch (e) {
          /* headless: no canvas to measure with */
        }
        var label = String(n.data("label") || "");
        var chars = Math.min(label.length, 26);
        if (!isFinite(w) || w < 24) w = Math.round(chars * 7.2 + 26);
        if (!isFinite(h) || h < 14) {
          h = Math.ceil(label.length / 26) * 16 + 16;
        }
        return { w: Math.round(w), h: Math.round(h) };
      }

      /** THE SWIM-LANE LAYOUT.
       *
       * ``items`` are ``{id, lane, band, sec, secIdx, doc, w, h}`` records;
       * the answer is ``{pos, boxes, laneCounts}`` — a position per item and
       * the band rectangles to draw behind them.
       *
       * x comes from the lane (and, when a lane is too tall to read, from a
       * sub-column inside it — still the same lane, so the left→right layer
       * order is untouched).  y comes from a fixed pipeline:
       *
       *   1. section blocks in document order, entries in document order;
       *   2. BARY_PASSES barycentre sweeps: each node is pulled towards the
       *      average normalised height of its neighbours, sections move as
       *      blocks (by their members' mean), entries move inside them;
       *   3. stack, with a gap between sections and a bigger one between
       *      the sub-bands of a lane.
       *
       * Every step is a total order with an explicit tie-break, so the same
       * graph.json always produces the same picture — no physics, no seeds,
       * no "run it again and the graph moves". */
      function computeLaneLayout(items) {
        var LN = laneDefs.length;
        var lanes = [];
        var li;
        for (li = 0; li < LN; li++) {
          var nbands = ((laneDefs[li] || {}).bands || [{}]).length || 1;
          var bands = [];
          for (var bi = 0; bi < nbands; bi++) bands.push([]);
          lanes.push(bands);
        }
        items.forEach(function (it) {
          var lb = lanes[it.lane] || lanes[0];
          lb[Math.min(it.band, lb.length - 1)].push(it);
        });

        // 1. document order --------------------------------------------
        lanes.forEach(function (bnds) {
          bnds.forEach(function (arr) {
            arr.sort(function (a, b) {
              return a.secIdx - b.secIdx || a.doc - b.doc || (a.id < b.id ? -1 : 1);
            });
          });
        });

        // 2. barycentre sweeps ------------------------------------------
        var norm = {};                       // id -> normalised height 0..1
        function normalise() {
          lanes.forEach(function (bnds) {
            var seq = [];
            bnds.forEach(function (arr) {
              seq = seq.concat(arr);
            });
            var n = seq.length || 1;
            seq.forEach(function (it, i) {
              norm[it.id] = (i + 0.5) / n;
            });
          });
        }
        function sortBand(arr) {
          if (arr.length < 2) return;
          var sums = {};
          var counts = {};
          var firstIdx = {};
          arr.forEach(function (it) {
            sums[it.sec] = (sums[it.sec] || 0) + it.bary;
            counts[it.sec] = (counts[it.sec] || 0) + 1;
            if (firstIdx[it.sec] === undefined) firstIdx[it.sec] = it.secIdx;
          });
          var rank = {};
          Object.keys(sums)
            .sort(function (a, b) {
              var ma = sums[a] / counts[a];
              var mb = sums[b] / counts[b];
              if (ma !== mb) return ma - mb;
              if (firstIdx[a] !== firstIdx[b]) return firstIdx[a] - firstIdx[b];
              return a < b ? -1 : 1;
            })
            .forEach(function (s, i) {
              rank[s] = i;
            });
          arr.sort(function (a, b) {
            if (rank[a.sec] !== rank[b.sec]) return rank[a.sec] - rank[b.sec];
            if (a.bary !== b.bary) return a.bary - b.bary;
            return a.doc - b.doc || (a.id < b.id ? -1 : 1);
          });
        }
        for (var pass = 0; pass < BARY_PASSES; pass++) {
          normalise();
          items.forEach(function (it) {
            var adj = rendered[it.id] || {};
            var sum = 0;
            var cnt = 0;
            ["out", "in"].forEach(function (dir) {
              (adj[dir] || []).forEach(function (link) {
                // PROOF dependencies only.  Letting prose co-references pull
                // on the layout would mean switching them on re-shuffles the
                // whole map — the reader's mental picture of where things
                // are must not depend on a display toggle.
                if (link.kind !== "depends") return;
                if (norm[link.to] === undefined) return;
                sum += norm[link.to];
                cnt += 1;
              });
            });
            it.bary = cnt ? sum / cnt : norm[it.id];
          });
          lanes.forEach(function (bnds) {
            bnds.forEach(sortBand);
          });
        }

        // 3. columns + stacking ------------------------------------------
        function stackHeight(col) {
          var h = 0;
          col.forEach(function (it, i) {
            h += it.h;
            if (i) {
              h += NODE_GAP + (col[i - 1].sec !== it.sec ? SECTION_GAP : 0);
            }
          });
          return h;
        }
        /* A lane taller than TARGET_COL_H wraps into sub-columns, breaking
         * at section boundaries where it can.  Wrapping inside the lane is
         * what keeps a 60-entry layer from being a 2500px ribbon nobody can
         * see the ends of, without breaking the left→right layer order. */
        function columnsOf(arr, budget) {
          var total = stackHeight(arr);
          var ncols = Math.max(1, Math.ceil(total / budget));
          if (ncols === 1 || arr.length < 2) return [arr];
          // Aim for ncols columns of equal height: break at a section
          // boundary once the column is nearly full, and unconditionally
          // before a node that would overflow it.  No column may run long,
          // so the lane's height stays near TARGET_COL_H whatever the
          // section sizes happen to be.
          var cap = total / ncols;
          var cols = [];
          var cur = [];
          var curH = 0;
          arr.forEach(function (it, i) {
            var newSec = i > 0 && arr[i - 1].sec !== it.sec;
            var add = it.h + (cur.length ? NODE_GAP + (newSec ? SECTION_GAP : 0) : 0);
            if (
              cur.length &&
              ((newSec && curH >= cap * 0.72) || curH + add > cap * 1.06)
            ) {
              cols.push(cur);
              cur = [];
              curH = 0;
              add = it.h;
            }
            cur.push(it);
            curH += add;
          });
          if (cur.length) cols.push(cur);
          return cols;
        }

        var geom = lanes.map(function (bnds) {
          /* TARGET_COL_H is the budget for the LANE, not for each of its
           * bands: a lane stacks its live bands vertically, so handing every
           * band the full budget makes a two-band lane twice as tall as the
           * one-canvas-height invariant promises, and the reader is forced
           * into the vertical pan the whole design exists to avoid (and the
           * lane caption, drawn at the top, scrolls away with it).  Split the
           * budget across the live bands, minus the chrome stacking them
           * costs, so an extra band buys more COLUMNS, never more height. */
          var liveN = bnds.filter(function (b) {
            return b.length > 0;
          }).length || 1;
          var budget = Math.max(
            MIN_BAND_H,
            (TARGET_COL_H - (liveN - 1) * BAND_GAP - liveN * BAND_CHROME) / liveN
          );
          var cols = bnds.map(function (b) {
            return columnsOf(b, budget);
          });
          var ncols = 1;
          var colW = MIN_LANE_W;
          var bandH = [];
          cols.forEach(function (cs, i) {
            var live = bnds[i].length > 0;
            ncols = Math.max(ncols, live ? cs.length : 1);
            var hmax = 0;
            cs.forEach(function (col) {
              hmax = Math.max(hmax, stackHeight(col));
              col.forEach(function (it) {
                colW = Math.max(colW, it.w);
              });
            });
            bandH[i] = live ? hmax : 0;
          });
          var liveBands = bandH.filter(function (h) {
            return h > 0;
          }).length;
          var laneH =
            bandH.reduce(function (a, b) {
              return a + b;
            }, 0) + Math.max(0, liveBands - 1) * BAND_GAP;
          return { cols: cols, ncols: ncols, colW: colW, bandH: bandH, laneH: laneH };
        });

        var maxLaneH = geom.reduce(function (m, g) {
          return Math.max(m, g.laneH);
        }, 0);
        var top = -maxLaneH / 2 - LANE_PAD;
        var bottom = maxLaneH / 2 + LANE_PAD;

        var pos = {};                        // id -> {x, y}, the answer
        var boxes = [];
        var laneCounts = [];
        var cursor = 0;
        var anchor = null;                   // densest lane, for the pan floor
        geom.forEach(function (g, i) {
          var def = laneDefs[i] || {};
          var n = lanes[i].reduce(function (a, arr) {
            return a + arr.length;
          }, 0);
          laneCounts.push(n);
          var empty = n === 0;
          var innerW = g.ncols * g.colW + (g.ncols - 1) * COL_GAP;
          var boxW = empty ? EMPTY_LANE_W : innerW + 2 * LANE_PAD;
          var left = cursor;
          boxes.push({
            key: "lane-" + i,
            kind: "lane",
            empty: empty,
            x: left + boxW / 2,
            y: (top + bottom) / 2,
            w: boxW,
            h: bottom - top,
            // A rail has no room for "Foundations · 0" across it, so it
            // carries the layer's name down its length instead (see the
            // .lane-empty style) and drops the count, which is zero by
            // construction and stated by the rail itself.
            label: empty
              ? def.title || "Lane " + i
              : (def.title || "Lane " + i) + " · " + n,
          });
          if (!anchor || n > anchor.n) {
            anchor = { n: n, x1: left, x2: left + boxW };
          }
          if (empty) {
            cursor = left + boxW + EMPTY_LANE_GAP;
            return;
          }

          var y = -g.laneH / 2;
          g.cols.forEach(function (cs, bIdx) {
            if (!lanes[i][bIdx].length) return;
            var bh = g.bandH[bIdx];
            if ((def.bands || []).length > 1) {
              var bandDef = (def.bands || [])[bIdx] || {};
              boxes.push({
                key: "band-" + i + "-" + bIdx,
                kind: "band",
                x: left + boxW / 2,
                y: y + bh / 2,
                w: innerW + 14,
                h: bh + BAND_CHROME,
                label:
                  (bandDef.title || bandDef.id || "") +
                  " · " + lanes[i][bIdx].length,
              });
            }
            cs.forEach(function (col, ci) {
              var colX = left + LANE_PAD + ci * (g.colW + COL_GAP) + g.colW / 2;
              var cy0 = y;
              col.forEach(function (it, k) {
                if (k) {
                  cy0 += NODE_GAP + (col[k - 1].sec !== it.sec ? SECTION_GAP : 0);
                }
                pos[it.id] = { x: colX, y: cy0 + it.h / 2 };
                cy0 += it.h;
              });
            });
            y += bh + BAND_GAP;
          });
          cursor = left + boxW + LANE_GAP;
        });

        return {
          pos: pos,
          boxes: boxes,
          laneCounts: laneCounts,
          anchor: anchor,
        };
      }

      var laneCounts = [];
      /* Model-space x-range of the lane holding the most entries.  When the
       * tab is too wide to fit at the readability floor, THIS is what the
       * viewport lands on — the left edge is where the emptiest layers are,
       * and landing there is how the PPL tab used to open with 9 of its 57
       * entries on screen and its 48-entry lane a full canvas off to the
       * right. */
      var laneAnchor = null;

      function layoutLanes() {
        var ents = cy.nodes(".ent");
        if (!ents.length) return;
        var items = ents.map(function (n) {
          var box = boxOf(n);
          return {
            id: n.id(),
            lane: Math.max(0, Math.min(laneDefs.length - 1, n.data("lane") | 0)),
            band: Math.max(0, n.data("band") | 0),
            sec: n.data("sec") || "",
            secIdx: n.data("secIdx") | 0,
            doc: n.data("doc") | 0,
            w: box.w,
            h: box.h,
          };
        });
        var out = computeLaneLayout(items);
        laneCounts = out.laneCounts;
        laneAnchor = out.anchor;
        cy.batch(function () {
          ents.forEach(function (n) {
            var p = out.pos[n.id()];
            if (p) n.position({ x: p.x, y: p.y });
          });
        });
        if (out.boxes.length) {
          cy.add(
            out.boxes.map(function (b) {
              return {
                group: "nodes",
                data: {
                  id: "band::" + b.key,
                  label: b.label,
                  ntype: "band",
                  w: b.w,
                  h: b.h,
                },
                position: { x: b.x, y: b.y },
                classes:
                  b.kind === "lane"
                    ? "lane-band" + (b.empty ? " lane-empty" : "")
                    : "lane-band lane-subband",
                selectable: false,
                grabbable: false,
                pannable: true,
              };
            })
          );
        }
      }

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
          // RL, not LR: an edge is "A uses B", so ranking right-to-left puts
          // the DEPENDENCIES (B, the foundations) on the left — the same
          // reading order the lane view enforces architecturally.
          rankDir: "RL",
          nodeSep: 18,
          rankSep: 70,
          edgeSep: 8,
          animate: false,         // never animate: reduced-motion safe
          fit: false,
          padding: 24,
        };
      }

      /* Ports sit on the side the missing node WOULD be on: an "out" port
       * stands for dependencies (which live to the LEFT, in a lower layer),
       * an "in" port for dependents (to the right).  Same convention as the
       * lanes, so a port reads as an edge running off the canvas. */
      function portSide(dir) {
        return dir === "out" ? -1 : 1;
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
                  x: pos.x + (w / 2 + 13) * portSide(dir),
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
              x: pos.x + (w / 2 + 13) * portSide(dir),
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

        laneAnchor = null;   // stale the moment the projection changes
        if (state.view === "lanes") {
          layoutLanes();
        } else {
          var eles = cy.elements();
          if (eles.length) {
            try {
              eles.layout(layoutOpts()).run();
            } catch (e) {
              eles.layout({ name: "grid", fit: false }).run();
            }
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

      /** What "fit" should frame: the CONTENT, not the empty scaffolding.
       *
       * The rails standing in for layers this tab does not touch are part of
       * the picture but they are not what the reader came for; letting them
       * drive the zoom is how a tab whose real nodes span 240 model units
       * used to be fitted as if it spanned 1340. */
      function fitTarget() {
        var eles = cy.elements().not(".lane-empty");
        return eles.length ? eles : cy.elements();
      }

      /** Fit the content — but never below the readability zoom.
       *
       * The old landing view simply fitted everything, which on a laptop
       * meant 6px labels: a picture of a graph rather than a graph you can
       * read.  Here the floor wins: if the tab does not fit at READ_ZOOM we
       * stay at READ_ZOOM and pan so that the DENSEST lane is what lands on
       * screen, then the reader pans out from there along the lanes — the
       * axis the layout is organised on anyway.  Anchoring on the left edge
       * instead (the old rule) opens the tab on whichever layer happens to
       * be leftmost, which on the PPL tab is a nearly empty one. */
      function fit(target) {
        var eles = target || fitTarget();
        if (!eles.length) return;
        cy.fit(eles, FIT_PAD);
        var z = cy.zoom();
        if (z > MAX_FIT_ZOOM) {
          cy.zoom(MAX_FIT_ZOOM);
          cy.center(eles);
        } else if (z < READ_ZOOM) {
          var bb = eles.boundingBox();
          cy.zoom(READ_ZOOM);
          var vw = cy.width();
          var vh = cy.height();
          var cw = bb.w * READ_ZOOM;
          var ch = bb.h * READ_ZOOM;
          var panX;
          if (cw <= vw) {
            panX = (vw - cw) / 2 - bb.x1 * READ_ZOOM;
          } else {
            // Too wide to show at a readable size: frame the densest lane
            // (centred if it fits, else its left edge), then clamp so we
            // never pan past the content into blank canvas.
            // A caller-supplied target (a focus cone) is already the thing to
            // frame — do not yank the view to the densest lane instead.
            var a =
              target || !laneAnchor
                ? { x1: bb.x1, x2: Math.min(bb.x2, bb.x1 + vw / READ_ZOOM) }
                : { x1: laneAnchor.x1, x2: laneAnchor.x2 };
            var aw = (a.x2 - a.x1) * READ_ZOOM;
            panX =
              aw <= vw - 2 * FIT_PAD
                ? (vw - aw) / 2 - a.x1 * READ_ZOOM
                : FIT_PAD - a.x1 * READ_ZOOM;
            panX = Math.min(
              FIT_PAD - bb.x1 * READ_ZOOM,
              Math.max(vw - FIT_PAD - bb.x2 * READ_ZOOM, panX)
            );
          }
          cy.pan({
            x: panX,
            y:
              (ch <= vh ? (vh - ch) / 2 : FIT_PAD) -
              bb.y1 * READ_ZOOM,
          });
        }
        syncZoomReadout();
      }

      function zoomBy(factor) {
        var next = Math.max(
          cy.minZoom(),
          Math.min(cy.maxZoom(), cy.zoom() * factor)
        );
        cy.zoom({
          level: next,
          renderedPosition: { x: cy.width() / 2, y: cy.height() / 2 },
        });
        syncZoomReadout();
      }

      function syncZoomReadout() {
        var out = el("cy-zoom-level");
        if (!out) return;
        var pct = Math.round(cy.zoom() * 100);
        out.textContent = pct + "%";
        var small = cy.zoom() < READ_ZOOM - 0.001;
        out.classList.toggle("is-small", small);
        out.title = small
          ? "Labels are below " + MIN_LABEL_PX + "px at this zoom — “Fit” " +
            "returns to the readable floor."
          : "Node labels are at least " + MIN_LABEL_PX + "px at this zoom.";
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

      /** Every drawn node that IS (or contains) a leaf of the relation. */
      function markedIds() {
        var out = {};
        if (state.mark !== "leaves") return out;
        Object.keys(rendered).forEach(function (id) {
          var d = byId[id];
          if (!d) return;
          if (d.ntype === "entry") {
            if (isLeaf(id)) out[id] = true;
            return;
          }
          // A collapsed section stands in for its entries, so it lights up
          // when it holds one (the section view; lanes never collapse).
          var kids = entriesOfGroup[id] || [];
          for (var i = 0; i < kids.length; i++) {
            if (isLeaf(kids[i])) {
              out[id] = true;
              return;
            }
          }
        });
        return out;
      }

      /** Light a SET of nodes, dimming the rest — the cone mechanism with
       * many roots instead of one.  Edges stay lit only when both ends are
       * in the set, so the highlight cannot imply a dependency that is not
       * there. */
      function applyMarkSet() {
        var set = markedIds();
        var n = 0;
        cy.batch(function () {
          cy.nodes().forEach(function (node) {
            if (node.hasClass("lane-band")) return;
            if (node.hasClass("stub")) {
              if (!set[node.data("host")]) node.addClass("dim");
              return;
            }
            if (set[node.id()]) {
              node.addClass("marked");
              n += 1;
            } else if (
              !node.isParent() ||
              node.children().filter(function (c) {
                return !!set[c.id()];
              }).length === 0
            ) {
              node.addClass("dim");
            }
          });
          cy.edges().forEach(function (e) {
            if (set[e.data("source")] && set[e.data("target")]) return;
            e.addClass("dim");
          });
        });
        renderLeavesPanel(Object.keys(set));
        return n;
      }

      function applyFocus() {
        cy.elements().removeClass("dim cone focusroot marked");
        var focusbar = el("cy-focusbar");
        if (!state.focus || cy.getElementById(state.focus).empty()) {
          state.focus = null;
          if (focusbar) focusbar.hidden = true;
          if (state.mark) {
            applyMarkSet();
            return;
          }
          renderPanel(null);
          return;
        }
        if (focusbar) focusbar.hidden = false;
        var cone = coneOf(state.focus);
        cy.batch(function () {
          cy.nodes().forEach(function (n) {
            var id = n.id();
            if (n.hasClass("lane-band")) return;   // background, never dimmed
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
          cy.getElementById(state.focus).removeClass("cone").addClass("focusroot");
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
        // One highlight at a time: picking a node answers a different
        // question than "where are the headline results".
        if (id && state.mark) setMark(null, { quiet: true });
        applyFocus();
        syncUrl();
        if (id && opts.center) centerOn(cy.getElementById(id));
        announce(
          id && byId[id]
            ? "Focused " + (byId[id].label || id)
            : "Focus cleared"
        );
      }

      /** Toggle a multi-target highlight ("leaves" is the only one today). */
      function setMark(kind, opts) {
        opts = opts || {};
        state.mark = kind || null;
        if (state.mark) {
          state.focus = null;
          state.stub = null;
        }
        var btn = el("cy-leaves");
        if (btn) {
          btn.setAttribute("aria-pressed", state.mark ? "true" : "false");
          btn.classList.toggle("is-on", !!state.mark);
        }
        if (opts.quiet) return;
        applyFocus();
        syncUrl();
        announce(
          state.mark
            ? "Headline results highlighted"
            : "Highlight cleared"
        );
      }

      /* ==============================================================
       * 7. Info panel
       * ============================================================== */
      /** The DEPENDENCY neighbours of ``id`` on one side.
       *
       * Proof-level only.  These two lists are rendered under "Uses" and
       * "Used by" — verbs that make a claim about the proof — so a prose
       * co-reference must never reach them: that is exactly the sentence
       * the owner reported ("Thm 4.19 · Used by · Thm 4.18"), and it was
       * still being published here, one click from the fixed card, whenever
       * the co-reference toggle was on. */
      function neighbourList(id, dir) {
        var adj = (rendered[id] || {})[dir] || [];
        return adj
          .filter(function (link) {
            return link.kind === "depends";
          })
          .map(function (link) {
            return link.to;
          });
      }

      /** The CO-REFERENCE neighbours of ``id`` — one direction-free list.
       *
       * The adjacency files an undirected link both ways, so reading one
       * side and de-duplicating yields each partner exactly once. */
      function coNeighbourList(id) {
        var adj = (rendered[id] || {}).out || [];
        var out = [];
        var seenTo = {};
        adj.forEach(function (link) {
          if (link.kind !== "mentions" || seenTo[link.to]) return;
          seenTo[link.to] = true;
          out.push(link.to);
        });
        return out;
      }

      /** Cross-tab co-reference partners of ``id``, which get no port. */
      function coPortCount(id) {
        var slot = coPorts[id];
        if (!slot) return 0;
        var total = 0;
        Object.keys(slot).forEach(function (t) {
          total += slot[t].length;
        });
        return total;
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

      /** ``extraNote`` says where the ``extra`` cross-tab items went.  It is
       * a parameter because dependencies leave the tab as a PORT on the node
       * while co-references cannot (a port is directional), so pointing the
       * reader at a port that does not exist would be its own small lie. */
      function listBlock(title, ids, extra, limit, extraNote) {
        if (!ids.length && !extra) return "";
        var shown = ids.slice(0, limit || 8);
        var more = ids.length - shown.length;
        return (
          '<div class="graph-panel-block"><h3>' + esc(title) +
          ' <span class="graph-count">' + (ids.length + (extra || 0)) +
          "</span></h3><ul>" + shown.map(linkRow).join("") +
          (more > 0 ? '<li class="graph-more">+' + more + " more</li>" : "") +
          (extra
            ? '<li class="graph-more">' + extra + " " +
              (extraNote || "in other tabs (see the ports on the node)") +
              "</li>"
            : "") +
          "</ul></div>"
        );
      }

      /** "Linear + Stable · homs — inherited from the section", in words. */
      function laneDescription(d) {
        var lane = laneDefs[laneOf(d)] || {};
        var band = (lane.bands || [])[bandOf(d)] || {};
        var out = esc(lane.title || lane.id || "—");
        if ((lane.bands || []).length > 1 && (band.title || band.id)) {
          out += ' <span class="graph-more">· ' + esc(band.title || band.id) +
            "</span>";
        }
        if (d.lane_src === "section") {
          out +=
            ' <span class="graph-more">(no source file — inherited from the ' +
            "section)</span>";
        } else if (d.lane_src === "fallback") {
          out += ' <span class="graph-more">(unplaced)</span>';
        }
        if (isLeaf(d.id)) {
          out += '<br><span class="graph-mark graph-mark-leaf">⚑ leaf</span> ' +
            "nothing in the three tabs depends on this";
        } else if (d.isolated) {
          out += '<br><span class="graph-mark graph-mark-root">isolated</span> ' +
            "no proof dependency either way at entry level";
        } else if (isRoot(d.id)) {
          out += '<br><span class="graph-mark graph-mark-root">root</span> ' +
            "depends on no other documented entry";
        }
        return out;
      }

      /** The panel for the multi-target "leaves" highlight. */
      function renderLeavesPanel(ids) {
        var body = el("cy-panel-body");
        var placeholder = el("cy-panel-empty");
        if (!body) return;
        if (placeholder) placeholder.hidden = true;
        body.hidden = false;
        var entries = ids.filter(function (id) {
          return (byId[id] || {}).ntype === "entry";
        });
        var groups = ids.length - entries.length;
        entries.sort(function (a, b) {
          return (entryIndex[a] || 0) - (entryIndex[b] || 0);
        });
        body.innerHTML =
          '<p class="graph-panel-kicker">Highlight</p><h2>Headline results</h2>' +
          '<p class="graph-panel-note">Entries no other entry depends on, in ' +
          "any of the three tabs — the results the development is FOR, rather " +
          "than the machinery under them. A leaf can sit in any lane: a layer " +
          "is where a result is PROVED, not how far up the stack it is." +
          (groups
            ? " " + groups + " folded section" + (groups === 1 ? "" : "s") +
              " also contain one."
            : "") +
          "</p>" +
          listBlock("Leaves in this tab", entries, 0, 30);
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
        facts += "<dt>Layer</dt><dd>" + laneDescription(d) + "</dd>";
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

        // "Uses" / "Used by" state a direction, so only the proof-level
        // relation may fill them.  Co-references get their own block under a
        // direction-free heading, and only when they are being drawn — the
        // panel never states a relation the canvas is hiding.
        var mentionedWith = state.mentions ? coNeighbourList(id) : [];
        var coBlock = "";
        if (mentionedWith.length || (state.mentions && coPortCount(id))) {
          coBlock =
            listBlock(
              "Mentioned with", mentionedWith, coPortCount(id), 0,
              "in other tabs"
            ) +
            '<p class="graph-panel-note">Both entries\' text names the same ' +
            "identifier. That points in no direction — it is not a " +
            "dependency, and cross-tab co-references are listed here rather " +
            "than drawn as a port.</p>";
        }

        body.innerHTML =
          head + facts + link +
          listBlock("Uses", uses, portCount(id, "out")) +
          listBlock("Used by", usedBy, portCount(id, "in")) +
          coBlock;
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

        if (n.hasClass("lane-band")) return;   // background, not a target
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
        if (state.mark) setMark(null, {});
        else if (state.focus || state.stub) setFocus(null, {});
      });

      /* Plain wheel PANS (the lane view is a wide picture you scroll along);
       * Shift+wheel and pinch — which arrives as a ctrl-modified wheel —
       * still zoom, and so do the +/− buttons.
       *
       * Cytoscape binds its own wheel handler on the container in the
       * CAPTURE phase, so a listener on the container itself would run
       * second (same element, registration order) and lose.  Listening on
       * the container's PARENT, still capturing, puts this handler earlier
       * in the propagation path: stopPropagation then means Cytoscape never
       * sees the event at all. */
      (function bindWheel() {
        var host = container.parentNode || container;
        host.addEventListener(
          "wheel",
          function (ev) {
            if (!container.contains(ev.target) && ev.target !== container) {
              return;                     // the side panel scrolls normally
            }
            if (ev.shiftKey || ev.ctrlKey || ev.metaKey) {
              window.setTimeout(syncZoomReadout, 0);
              return;                     // let Cytoscape zoom
            }
            ev.preventDefault();
            ev.stopPropagation();
            var pan = cy.pan();
            cy.pan({ x: pan.x - ev.deltaX, y: pan.y - ev.deltaY });
          },
          { capture: true, passive: false }
        );
      })();

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
          if (state.mark) setMark(null, {});
          else if (state.focus || state.stub) setFocus(null, {});
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

      /* The layout switch.  "Lanes" is the default and the answer to "where
       * does this sit in the development"; "Sections" is the previous
       * compound view, kept for readers who navigate by document structure
       * (and it is the only view where folding a section means anything). */
      var syncViewSeg = segment("cy-views", function (b) {
        var next = b.getAttribute("data-view") === "sections" ? "sections" : "lanes";
        if (next === state.view) return;
        state.view = next;
        state.stub = null;
        if (next === "sections") state.expanded = budgetedExpansion(state.tab);
        syncViewSeg(function (x) {
          return (
            (x.getAttribute("data-view") === "sections" ? "sections" : "lanes") ===
            state.view
          );
        });
        syncViewChrome();
        syncExpandAll();
        render({});
        announce(
          state.view === "lanes"
            ? "Architectural lane layout"
            : "Grouped by section"
        );
      });
      syncViewSeg(function (b) {
        return (
          (b.getAttribute("data-view") === "sections" ? "sections" : "lanes") ===
          state.view
        );
      });

      /** Controls that only mean something in one of the two views. */
      function syncViewChrome() {
        appEl.setAttribute("data-view", state.view);
      }
      syncViewChrome();

      var leavesBtn = el("cy-leaves");
      if (leavesBtn) {
        if (!marksMeaningful) {
          leavesBtn.disabled = true;
          leavesBtn.title =
            "This build has no .glob dependency data, so no entry can be " +
            "shown to be a leaf.";
        } else {
          leavesBtn.title =
            (meta.leaves_by_tab
              ? "Light the entries nothing depends on. "
              : "") + "Click again (or press Esc) to clear.";
          leavesBtn.addEventListener("click", function () {
            setMark(state.mark === "leaves" ? null : "leaves", {});
          });
        }
      }

      var zoomInBtn = el("cy-zoom-in");
      var zoomOutBtn = el("cy-zoom-out");
      var fitBtn = el("cy-fit");
      if (zoomInBtn) {
        zoomInBtn.addEventListener("click", function () {
          zoomBy(ZOOM_STEP);
        });
      }
      if (zoomOutBtn) {
        zoomOutBtn.addEventListener("click", function () {
          zoomBy(1 / ZOOM_STEP);
        });
      }
      if (fitBtn) {
        fitBtn.addEventListener("click", function () {
          fit();
          announce("View fitted");
        });
      }
      cy.on("zoom", function () {
        if (!rendering) syncZoomReadout();
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
            ? " and list " + cost.ports + " cross-tab partner" +
              (cost.ports === 1 ? "" : "s") + " in the panel (they get no " +
              "port: a port points a way and a co-reference does not)"
            : "") +
          (state.view === "lanes"
            ? "; the rest duplicate a proof dependency already drawn, or " +
              "leave the tab."
            : "; the rest are inside a folded section, or duplicate a proof " +
              "dependency already drawn.");
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
          state.view = "lanes";
          setMark(null, { quiet: true });
          syncViewSeg(function (x) {
            return x.getAttribute("data-view") !== "sections";
          });
          syncViewChrome();
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
        setMark(null, { quiet: true });
        if (d.ntype === "entry") {
          if (d.tab !== state.tab) {
            state.tab = d.tab;
            state.expanded = budgetedExpansion(d.tab);
            syncTabSeg(function (x) {
              return x.getAttribute("data-tab") === state.tab;
            });
          }
          // The lane view draws every entry, so there is nothing to unfold.
          if (state.view === "sections") state.expanded[d.parent] = true;
        } else if (d.ntype === "group") {
          // A section is not a node in the lane view: land on the section's
          // first entry instead of dropping the reader nowhere.
          if (state.view === "lanes") {
            var kids = entriesOfGroup[id] || [];
            if (!kids.length) return;
            return jumpTo(kids[0]);
          }
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
        var lanesUsed = ((meta.lanes_by_tab || {})[state.tab] || []).filter(
          function (n) {
            return n > 0;
          }
        ).length;
        capEl.textContent =
          (TAB_LABEL[state.tab] || state.tab) + " tab: " + ents + " entr" +
          (ents === 1 ? "y" : "ies") + " in " + groups + " section" +
          (groups === 1 ? "" : "s") +
          (lanesUsed
            ? ", spread over " + lanesUsed + " architectural layer" +
              (lanesUsed === 1 ? "" : "s")
            : "");
      }

      function updateStats() {
        var statsEl = el("cy-stats");
        if (!statsEl) return;
        var ents = cy.nodes(".ent").length;
        var deps = cy.edges(".depends").length;
        var ments = cy.edges(".mentions").length;
        var ports = cy.nodes(".stub").length;
        var bits = [];
        if (state.view === "lanes") {
          var filled = laneCounts.filter(function (n) {
            return n > 0;
          }).length;
          var leaves = cy.nodes(".is-leaf").length;
          bits.push(
            "Drawn now: " + ents + " entr" + (ents === 1 ? "y" : "ies") +
              " across " + filled + " lane" + (filled === 1 ? "" : "s")
          );
          var perLane = [];
          laneCounts.forEach(function (n, i) {
            if (n) perLane.push((laneDefs[i] || {}).title + " " + n);
          });
          if (perLane.length) bits.push(perLane.join(" · "));
          if (marksMeaningful) {
            bits.push(leaves + " leaf result" + (leaves === 1 ? "" : "s"));
          }
        } else {
          var groups = cy.nodes(".grp").length;
          var open = cy.nodes(".grp-open").length;
          bits.push(
            "Drawn now: " + groups + " section" + (groups === 1 ? "" : "s") +
              " (" + open + " unfolded)"
          );
          bits.push(ents + " entr" + (ents === 1 ? "y" : "ies"));
        }
        bits.push(deps + " dependency edge" + (deps === 1 ? "" : "s"));
        // Say how many of THOSE run against the lane order, on the same line
        // that counts them — the exception is reported where the rule is.
        var backw = cy.edges(".backward").length;
        if (backw) {
          bits.push(backw + " against the lane order");
        }
        if (state.mentions) {
          bits.push(ments + " co-reference edge" + (ments === 1 ? "" : "s"));
        }
        if (ports) bits.push(ports + " cross-tab port" + (ports === 1 ? "" : "s"));
        statsEl.textContent = bits.join(" · ");
      }

      /* -- go ------------------------------------------------------- */
      syncExpandAll();
      setMark(state.mark, { quiet: true });
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
