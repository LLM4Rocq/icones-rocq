/* Icones auditor — progressive enhancement.
 * Lives in one file: copy-to-clipboard, sticky header shadow, smooth scroll,
 * Pagefind UI loader. Pages remain functional without JS.
 * (Sidebar type-to-filter lives in toc.js.) */
(() => {
  'use strict';
  const $$ = (sel, root = document) => Array.from(root.querySelectorAll(sel));

  // --- Copy Rocq identifier to clipboard ------------------------------------
  $$('.ident.copy').forEach(el => el.addEventListener('click', async () => {
    const txt = el.dataset.copy || el.textContent.trim();
    try {
      await navigator.clipboard.writeText(txt);
      el.classList.add('is-copied');
      setTimeout(() => el.classList.remove('is-copied'), 900);
    } catch { /* clipboard blocked; silently ignore. */ }
  }));

  // --- Header shadow on scroll ----------------------------------------------
  // Desktop app-shell: the content pane is the scroll container; mobile:
  // the window scrolls. Listen on both, read whichever is scrolled.
  const hdr = document.querySelector('.site-header');
  if (hdr) {
    const pane = document.querySelector('.content-pane');
    const onScroll = () => hdr.classList.toggle(
      'is-scrolled', (window.scrollY || (pane ? pane.scrollTop : 0)) > 4);
    onScroll();
    window.addEventListener('scroll', onScroll, { passive: true });
    if (pane) pane.addEventListener('scroll', onScroll, { passive: true });
  }

  // --- Smooth in-page scroll for anchor links -------------------------------
  $$('a[href^="#"]').forEach(a => a.addEventListener('click', ev => {
    const id = a.getAttribute('href').slice(1);
    if (!id) return;
    const t = document.getElementById(id);
    if (!t) return;
    ev.preventDefault();
    t.scrollIntoView({ behavior: 'smooth', block: 'start' });
    history.replaceState(null, '', '#' + id);
  }));

  // --- Pagefind UI loader (M4) ---------------------------------------------
  // Pagefind builds /pagefind/ at CI time. If absent (mock/dev), we silently
  // leave the fallback search-shell placeholder visible.
  const shell = document.getElementById('search');
  if (shell && !shell.dataset.loaded) {
    shell.dataset.loaded = '1';
    const base = (document.documentElement.dataset.pagefindBase || '/pagefind/');
    // `base` is relative to the *page* (e.g. "pagefind/", "../pagefind/").  A
    // bare dynamic-import specifier is resolved against this module's URL
    // (…/static/app.js), not the document — that pointed at
    // …/static/pagefind/pagefind-ui.js and 404'd, silently leaving the inert
    // CSS placeholder visible.  Resolve against the document base instead so
    // the absolute URL is correct on every page depth and hosting subpath.
    const uiUrl = new URL(base + 'pagefind-ui.js', document.baseURI).href;
    import(/* webpackIgnore: true */ uiUrl).then((mod) => {
      // pagefind-ui.js is an IIFE bundle, not an ES module: it attaches
      // `window.PagefindUI` and exports nothing, so destructuring the module
      // namespace yields undefined and `new undefined()` throws — which the
      // catch below used to swallow, leaving the inert placeholder shell
      // (the "search bar you cannot click" bug).  Prefer a real export if a
      // future ESM build provides one; otherwise use the global the script
      // just set.
      const PagefindUI = (mod && mod.PagefindUI) || window.PagefindUI;
      if (!PagefindUI) {
        throw new Error('pagefind-ui.js loaded but PagefindUI is undefined');
      }
      // Pagefind CSS is auto-injected by the UI module.  `bundlePath` tells the
      // UI where the index/fragment files live — give it the same absolute,
      // document-resolved base so its index/fragment fetches don't default to
      // /pagefind/ and 404 on non-root or nested-page hosting (incl. file://).
      new PagefindUI({
        element: '#search',
        bundlePath: new URL(base, document.baseURI).href,
        showImages: false,
        resetStyles: false,
        showSubResults: true,
        excerptLength: 24,
        translations: {
          placeholder: 'Search entries, Rocq identifiers, file paths…',
          zero_results: 'No results for "[SEARCH_TERM]"',
        },
      });
    }).catch((err) => {
      // Keep the fallback shell, but never silently: a missing /pagefind/
      // (mock/dev build) and a broken UI init look identical to the user,
      // and the silent variant already cost us one shipped bug.
      console.warn('[auditor] search UI unavailable:', err && err.message ? err.message : err);
    });
  }
})();
