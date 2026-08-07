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

  // -- 0. Pin the rail below the REAL header height ------------------------
  // The CSS fallback (--toc-sticky-top: 7rem) assumes the sticky header's
  // three rows fit in ~7rem.  On narrower windows / higher zoom the rows
  // wrap and the header grows, so a 7rem-pinned rail slides UNDER it and
  // its top becomes unreachable.  Measure the real height instead, and
  // keep it in sync on resize (the same var also sizes the rail's
  // max-height, so the internal scrollbar stays correct).
  var header = document.querySelector(".site-header");
  function alignRail() {
    if (!header) return;
    try {
      var h = Math.ceil(header.getBoundingClientRect().height) + 12;
      document.documentElement.style.setProperty("--toc-sticky-top", h + "px");
    } catch (e) {
      /* non-fatal */
    }
  }
  alignRail();
  try {
    if (typeof ResizeObserver === "function" && header) {
      new ResizeObserver(alignRail).observe(header);
    } else {
      window.addEventListener("resize", alignRail);
    }
  } catch (e) {
    /* non-fatal */
  }

  // -- 1. Scroll the active node into view ---------------------------------
  try {
    var active = nav.querySelector('.toc-link[aria-current="true"]');
    if (active) {
      // Scroll WITHIN the rail only.  scrollIntoView() would also scroll
      // every scrollable ancestor — i.e. jump the page content on load.
      var navBox = nav.getBoundingClientRect();
      var actBox = active.getBoundingClientRect();
      nav.scrollTop += actBox.top - navBox.top - nav.clientHeight / 2;
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
