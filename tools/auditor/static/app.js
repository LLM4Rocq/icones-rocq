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

  // --- Sticky header shadow on scroll ---------------------------------------
  const hdr = document.querySelector('.site-header');
  if (hdr) {
    const onScroll = () => hdr.classList.toggle('is-scrolled', window.scrollY > 4);
    onScroll();
    window.addEventListener('scroll', onScroll, { passive: true });
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
    import(/* webpackIgnore: true */ uiUrl).then(({ PagefindUI }) => {
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
    }).catch(() => { /* offline / mock — keep the fallback shell. */ });
  }
})();
