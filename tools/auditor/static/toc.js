/* Progressive enhancement for the table-of-contents sidebar.
 *
 * The sidebar is fully functional WITHOUT JavaScript: collapse is native
 * <details>/<summary>, and the active branch is server-rendered `open`.
 * This script only enhances:
 *   1. scroll the active node into view inside the (independently
 *      scrollable) rail, so the current page is visible on load;
 *   2. persist which top-level tab groups the user has manually expanded,
 *      across page navigations, in localStorage.
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
