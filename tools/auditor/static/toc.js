/* Progressive enhancement for the table-of-contents sidebar.
 *
 * The sidebar is fully functional WITHOUT JavaScript: collapse is native
 * <details>/<summary>, and the active branch is server-rendered `open`.
 * This script only enhances:
 *   1. scroll the active node into view inside the (independently
 *      scrollable) rail, so the current page is visible on load;
 *   2. persist which top-level tab groups the user has manually expanded,
 *      across page navigations, in localStorage;
 *   3. type-to-filter the (tab-scoped) tree by node label.
 *
 * It must never be required for the sidebar to work; every step is guarded
 * and degrades silently.
 */
(function () {
  "use strict";

  var nav = document.getElementById("toc-sidebar");
  if (!nav) return;

  var KEY = "icones-toc-open-tabs";

  // -- 1. Scroll the active node into view ---------------------------------
  try {
    var active = nav.querySelector('.toc-link[aria-current="true"]');
    if (active && typeof active.scrollIntoView === "function") {
      // Center it within the rail without jumping the whole page.
      active.scrollIntoView({ block: "center", inline: "nearest" });
    }
  } catch (e) {
    /* non-fatal */
  }

  // -- 2. Persist manually-toggled top-level tab folds ---------------------
  function readOpen() {
    try {
      return JSON.parse(localStorage.getItem(KEY) || "[]") || [];
    } catch (e) {
      return [];
    }
  }
  function writeOpen(list) {
    try {
      localStorage.setItem(KEY, JSON.stringify(list));
    } catch (e) {
      /* storage may be unavailable; ignore */
    }
  }

  // -- 3. Type-to-filter the sidebar --------------------------------------
  // Hides every .toc-node whose label (and whose descendants' labels) do not
  // match the query; keeps ancestors of a match visible and opens the folds
  // along the way so deep hits are revealed. Empty query restores everything.
  var filter = nav.querySelector(".toc-filter");
  if (filter) {
    var nodes = Array.prototype.slice.call(nav.querySelectorAll(".toc-node"));

    var ownLink = function (n) {
      for (var i = 0; i < n.children.length; i++) {
        var c = n.children[i];
        if (c.classList.contains("toc-link")) return c;         // leaf
        if (c.classList.contains("toc-fold")) {                 // group
          return c.querySelector(".toc-summary > .toc-link");
        }
      }
      return null;
    };
    var ownFold = function (n) {
      for (var i = 0; i < n.children.length; i++) {
        if (n.children[i].classList.contains("toc-fold")) return n.children[i];
      }
      return null;
    };
    var txt = function (el) {
      return el ? (el.textContent || "").toLowerCase() : "";
    };

    var apply = function () {
      var q = filter.value.trim().toLowerCase();
      if (!q) {
        nodes.forEach(function (n) { n.hidden = false; });
        return;
      }
      // Pass 1: does each node's OWN label match?
      nodes.forEach(function (n) {
        n._tocMatch = txt(ownLink(n)).indexOf(q) !== -1;
      });
      // Pass 2: visible = self-match OR any descendant match OR any ancestor
      // match. Descendant links (incl. own) are all .toc-link within the node.
      nodes.forEach(function (n) {
        var show = n._tocMatch;
        if (!show) {
          var links = n.querySelectorAll(".toc-link");
          for (var i = 0; i < links.length && !show; i++) {
            if (txt(links[i]).indexOf(q) !== -1) show = true;
          }
        }
        if (!show) {
          var p = n.parentNode;
          while (p && p !== nav) {
            if (p.classList && p.classList.contains("toc-node") && p._tocMatch) {
              show = true;
              break;
            }
            p = p.parentNode;
          }
        }
        n.hidden = !show;
        if (show) {
          var fold = ownFold(n);
          if (fold) fold.open = true;   // reveal path to deep matches
        }
      });
    };

    filter.addEventListener("input", apply);
  }

  var tabFolds = nav.querySelectorAll(".toc-tab-fold");
  if (!tabFolds.length) return;

  // Restore previously-open tabs (additive to the server's active branch).
  var remembered = readOpen();
  Array.prototype.forEach.call(tabFolds, function (d) {
    var li = d.closest(".toc-tab");
    if (!li) return;
    var id = (li.className.match(/toc-tab-(\w+)/) || [])[1];
    if (id && remembered.indexOf(id) !== -1) d.open = true;
  });

  // Record toggles.
  Array.prototype.forEach.call(tabFolds, function (d) {
    d.addEventListener("toggle", function () {
      var li = d.closest(".toc-tab");
      if (!li) return;
      var id = (li.className.match(/toc-tab-(\w+)/) || [])[1];
      if (!id) return;
      var list = readOpen();
      var i = list.indexOf(id);
      if (d.open && i === -1) list.push(id);
      else if (!d.open && i !== -1) list.splice(i, 1);
      writeOpen(list);
    });
  });
})();
