/* Icones auditor — progressive enhancement.
 * Lives in one file: tab filter, copy-to-clipboard, sticky header shadow,
 * smooth scroll, Pagefind UI loader. Pages remain functional without JS. */
(() => {
  'use strict';
  const $$ = (sel, root = document) => Array.from(root.querySelectorAll(sel));

  // --- Tab filter (no-JS fallback: all entries stay visible) ----------------
  const tabs = $$('.tabs .tab');
  if (tabs.length) {
    const body = document.body;
    const STATUSES = ['axiom-free', 'regression-anchor', 'beyond-paper',
                      'discharged-deferred', 'gap'];
    const clearFilters = () =>
      STATUSES.forEach(s => body.classList.remove('filter-' + s));
    tabs.forEach(btn => btn.addEventListener('click', () => {
      tabs.forEach(b => {
        b.classList.remove('is-active');
        b.setAttribute('aria-selected', 'false');
      });
      btn.classList.add('is-active');
      btn.setAttribute('aria-selected', 'true');
      clearFilters();
      const f = btn.dataset.filter;
      if (f) body.classList.add('filter-' + f);
      // Sync hash for shareable filtered views.
      const url = new URL(location.href);
      if (f) url.searchParams.set('filter', f); else url.searchParams.delete('filter');
      history.replaceState(null, '', url.toString());
    }));
    // Apply initial filter from URL.
    const init = new URL(location.href).searchParams.get('filter');
    if (init) {
      const btn = tabs.find(b => b.dataset.filter === init);
      if (btn) btn.click();
    }
  }

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
    import(/* webpackIgnore: true */ base + 'pagefind-ui.js').then(({ PagefindUI }) => {
      // Pagefind CSS is auto-injected by the UI module.  `bundlePath` tells the
      // UI where the index/fragment files live — it must match the (relative)
      // base the script was imported from, else the UI defaults to /pagefind/
      // and 404s on non-root or nested-page hosting (incl. file://).
      new PagefindUI({
        element: '#search',
        bundlePath: base,
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
