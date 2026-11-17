// ==UserScript==
// @name         Kokam Pro
// @namespace    kokam-pro
// @version      16.0.0
// @updateURL    https://raw.githubusercontent.com/filselfon/Koka_price/main/koka_price.user.js
// @downloadURL  https://raw.githubusercontent.com/filselfon/Koka_price/main/koka_price.user.js
// @description  مقایسهٔ قیمت فروشندگان، تاریخچهٔ رسمی قیمت دیجی‌کالا (بازهٔ واقعی داده)، بازرس تخفیف، واچ‌لیست و هشدار — یک پنل واحد
// @author       حامد
// @contributor  حامد
// @homepageURL  https://t.me/R0oo0t
// @supportURL   https://t.me/R0oo0t
// @match        https://www.digikala.com/*
// @match        https://digikala.com/*
// @match        https://torob.com/*
// @match        https://www.torob.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_notification
// @connect      api.torob.com
// @connect      torob.com
// @connect      api.digikala.com
// @connect      www.digikala.com
// @noframes
// @run-at       document-idle
// ==/UserScript==
/* CHANGELOG
 * 16.0.0 — Kokam Pro؛ سازنده: حامد (https://t.me/R0oo0t)
 *          + ارزش زمان، محصولات مشابه، کمینه ۳۰روزه، مقایسه همه،
 *            تعویق ۴۲۹، قیمت منصفانه، جستجوی کد مدل، تغییر از دیروز،
 *            CSV تحلیلی، تست سلامت API
 * 15.0.0 — تغییر نام، محدودسازی @match، کش، backoff، waitForElement، observer SPA
 * 14.0.0 — نسخهٔ پایه
 */
/* Kokam Pro 16 — Creator: حامد (https://t.me/R0oo0t)
   Built from readable modules. The 8.7 engine logic is preserved in src/06-extract.js (extraction),
   src/07-match.js (baseline rule) and src/08-sources.js (Torob flow). */
(function () {
'use strict';

// ---- 01-util.js ----
const U = (() => {
  const FA = '۰۱۲۳۴۵۶۷۸۹', AR = '٠١٢٣٤٥٦٧٨٩';
  const STOP = new Set(['با','و','در','از','برای','خرید','قیمت','مدل','اصل','جدید','تومان','ریال','the','and','for','new']);

  const digits = s => String(s ?? '').replace(/[۰-۹]/g, c => FA.indexOf(c)).replace(/[٠-٩]/g, c => AR.indexOf(c));
  const normalize = s => digits(s).replace(/[يى]/g, 'ی').replace(/ك/g, 'ک')
    .replace(/[\u064B-\u0652\u0640\u200c\u200e\u200f]/g, ' ').replace(/[^a-zA-Z0-9آ-ی]+/g, ' ').toLowerCase().trim();
  const compact = s => normalize(s).replace(/\s+/g, '');
  const tokens = s => normalize(s).split(' ').filter(t => t.length > 1 && !STOP.has(t));

  const toFa = s => String(s).replace(/\d/g, d => FA[d]);
  const fmt = n => (n == null || !isFinite(n)) ? '—' : Math.round(n).toLocaleString('fa-IR');
  const fmtPct = n => (n == null || !isFinite(n)) ? '—' : toFa((Math.abs(n) < 10 ? n.toFixed(1) : Math.round(n)).toString()) + '٪';
  const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  const sleep = ms => new Promise(r => setTimeout(r, ms));
  const waitForElement = (sel, timeout = 8000) => new Promise(res => {
    const el = document.querySelector(sel); if (el) return res(el);
    const ob = new MutationObserver(() => { const e = document.querySelector(sel); if (e) { ob.disconnect(); res(e); } });
    ob.observe(document.documentElement, { childList: true, subtree: true });
    setTimeout(() => { ob.disconnect(); res(null); }, timeout);
  });
  const median = a => { if (!a.length) return null; const s = [...a].sort((x, y) => x - y), m = s.length >> 1; return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2; };
  const DAY = 86400000;
  const hoursOfWork = (price, hourlyWage) => (hourlyWage > 0 && price > 0) ? price / hourlyWage : null;

  function pricesWithCurrency(text) {
    const t = digits(text).replace(/[\u200c\u200e\u200f\u00a0]/g, '').replace(/[٬،]/g, ',');
    const re = /(\d{1,3}(?:,\d{3})+|\d{5,})\s*(تومان|تومن|ریال|ت)(?![آ-ی])/g, out = []; let m;
    while ((m = re.exec(t))) {
      const v = Number(m[1].replace(/\D/g, ''));
      if (v >= 1000) out.push(m[2] === 'ریال' ? Math.round(v / 10) : v);
    }
    return out;
  }
  function numbersIn(text) {
    const t = digits(text).replace(/[\u200c\u200e\u200f\u00a0]/g, '').replace(/[٬،]/g, ',');
    const re = /(?<![\d,.])(\d{1,3}(?:,\d{3})+|\d{5,})(?![\d,])/g, out = []; let m;
    while ((m = re.exec(t))) out.push(Number(m[1].replace(/\D/g, '')));
    return out;
  }

  const div = (a, b) => ~~(a / b), mod = (a, b) => a - ~~(a / b) * b;
  const BREAKS = [-61, 9, 38, 199, 426, 686, 756, 818, 1111, 1181, 1210, 1635, 2060, 2097, 2192, 2262, 2324, 2394, 2456, 3178];
  function jalCal(jy) {
    const bl = BREAKS.length, gy = jy + 621; let leapJ = -14, jp = BREAKS[0], jm, jump = 0, n, i;
    if (jy < jp || jy >= BREAKS[bl - 1]) throw new Error('bad jalali year ' + jy);
    for (i = 1; i < bl; i++) { jm = BREAKS[i]; jump = jm - jp; if (jy < jm) break; leapJ += div(jump, 33) * 8 + div(mod(jump, 33), 4); jp = jm; }
    n = jy - jp; leapJ += div(n, 33) * 8 + div(mod(n, 33) + 3, 4);
    if (mod(jump, 33) === 4 && jump - n === 4) leapJ++;
    const leapG = div(gy, 4) - div((div(gy, 100) + 1) * 3, 4) - 150;
    return { gy, march: 20 + leapJ - leapG };
  }
  const g2d = (gy, gm, gd) => { const d = div((gy + div(gm - 8, 6) + 100100) * 1461, 4) + div(153 * mod(gm + 9, 12) + 2, 5) + gd - 34840408; return d - div(div(gy + 100100 + div(gm - 8, 6), 100) * 3, 4) + 752; };
  const j2d = (jy, jm, jd) => { const r = jalCal(jy); return g2d(r.gy, 3, r.march) + (jm - 1) * 31 - div(jm, 7) * (jm - 7) + jd - 1; };
  function d2g(jdn) {
    let j = 4 * jdn + 139361631; j += div(div(4 * jdn + 183187720, 146097) * 3, 4) * 4 - 3908;
    const i = div(mod(j, 1461), 4) * 5 + 308, gd = div(mod(i, 153), 5) + 1, gm = mod(div(i, 153), 12) + 1;
    return { gy: div(j, 1461) - 100100 + div(8 - gm, 6), gm, gd };
  }
  function jalaliToTime(str) {
    const m = digits(str).match(/^\s*(\d{4})[\/\-.](\d{1,2})[\/\-.](\d{1,2})\s*$/); if (!m) return null;
    const jy = +m[1], jm = +m[2], jd = +m[3]; if (jm < 1 || jm > 12 || jd < 1 || jd > 31) return null;
    try { const g = d2g(j2d(jy, jm, jd)); return Date.UTC(g.gy, g.gm - 1, g.gd, 12); } catch { return null; }
  }
  const isoDay = t => new Date(t).toISOString().slice(0, 10);
  const faDate = t => { try { return new Date(t).toLocaleDateString('fa-IR', { month: 'short', day: 'numeric' }); } catch { return isoDay(t); } };

  return { DAY, STOP, digits, normalize, compact, tokens, toFa, fmt, fmtPct, esc, sleep, waitForElement, median, hoursOfWork, pricesWithCurrency, numbersIn, jalaliToTime, isoDay, faDate };
})();


// ---- 02-log.js ----
const Log = (() => {
  const buf = []; const MAX = 200; const subs = new Set();
  function add(level, scope, msg, extra) {
    const e = { t: Date.now(), level, scope, msg: String(msg), extra };
    buf.push(e); if (buf.length > MAX) buf.shift();
    try { (level === 'error' ? console.error : console.log)('[KokamPro]', scope, msg, extra ?? ''); } catch {}
    subs.forEach(f => { try { f(e); } catch {} });
  }
  return { info: (s, m, x) => add('info', s, m, x), warn: (s, m, x) => add('warn', s, m, x), error: (s, m, x) => add('error', s, m, x), all: () => buf.slice(), on: f => subs.add(f) };
})();


// ---- 03-store.js ----
const Store = (() => {
  const KEY = 'kokampro:db';
  const OLD_KEY = 'ghafel13:db';
  const DEFAULT = () => ({
    v: 1,
    settings: {
      theme: 'dark', productPageOnly: true,
      sources: { torob: true, emalls: false, basalam: false },
      alerts: { enabled: true, intervalMin: 60 },
      pos: null, open: false, tab: 'compare', table: false, wide: false, size: null, snap: true,
      hourlyWage: 0,
      low30d: {}
    },
    products: {}
  });
  const hasGM = () => typeof GM_getValue === 'function' && typeof GM_setValue === 'function';
  let db = null;

  function rawGet() {
    try { if (hasGM()) return GM_getValue(KEY, null); } catch (e) { Log.warn('store', 'GM_getValue failed: ' + e.message); }
    try { return localStorage.getItem(KEY); } catch { return null; }
  }
  function rawSet(s) {
    try { if (hasGM()) { GM_setValue(KEY, s); return; } } catch (e) { Log.warn('store', 'GM_setValue failed: ' + e.message); }
    try { localStorage.setItem(KEY, s); } catch (e) { Log.error('store', 'save failed: ' + e.message); }
  }
  function merge(base, src) {
    for (const k of Object.keys(src || {})) {
      if (src[k] && typeof src[k] === 'object' && !Array.isArray(src[k]) && base[k] && typeof base[k] === 'object' && !Array.isArray(base[k])) merge(base[k], src[k]);
      else base[k] = src[k];
    }
    return base;
  }
  function load() {
    const base = DEFAULT();
    try {
      let s = rawGet();
      if (!s) {
        try { s = hasGM() ? GM_getValue(OLD_KEY, null) : localStorage.getItem(OLD_KEY); } catch {}
        if (s) { rawSet(s); Log.info('store', 'داده‌های نسخهٔ قبل مهاجرت کرد'); }
      }
      if (s) db = merge(base, typeof s === 'string' ? JSON.parse(s) : s); else db = base;
    }
    catch (e) { Log.error('store', 'corrupt db, starting fresh: ' + e.message); db = base; }
    return db;
  }
  const get = () => db || load();
  const save = () => rawSet(JSON.stringify(get()));

  function touchProduct(key, init) {
    const d = get();
    const p = d.products[key] ||= { key, host: '', pid: '', title: '', url: '', variantTitle: '', local: [], watch: false, target: null, lastPrice: null, lastTs: 0, notifiedAt: 0, lastSource: '' };
    if (init) Object.assign(p, init);
    return p;
  }
  const MAX_LOCAL = 1500, MIN_GAP = 6 * 3600e3;
  function recordLocal(p, price, source, ts = Date.now()) {
    if (!(price > 0)) return false;
    const last = p.local[p.local.length - 1];
    p.lastPrice = price; p.lastTs = ts; p.lastSource = source;
    if (last && last.p === price && ts - last.t < MIN_GAP) return false;
    p.local.push({ t: ts, p: price, src: source });
    if (p.local.length > MAX_LOCAL) p.local.splice(0, p.local.length - MAX_LOCAL);
    return true;
  }
  function reset() { db = DEFAULT(); save(); }
  return { load, get, save, touchProduct, recordLocal, reset, DEFAULT, KEY };
})();


// ---- 04-net.js ----
const Net = (() => {
  const ALLOWED = ['api.torob.com', 'torob.com', 'api.digikala.com', 'www.digikala.com', 'digikala.com'];
  const allowed = url => { try { const h = new URL(url).hostname; return ALLOWED.includes(h); } catch { return false; } };
  let COOLDOWN_UNTIL = 0;
  const COOLDOWN_MS = 10 * 60e3;

  function gmRequest(url, { accept = 'application/json', referer, headers = {}, timeout = 15000, anonymous = true } = {}) {
    return new Promise((resolve, reject) => {
      if (!allowed(url)) return reject(new Error('دامنهٔ مجاز نیست: ' + (() => { try { return new URL(url).hostname; } catch { return url; } })()));
      const gm = typeof GM_xmlhttpRequest === 'function' ? GM_xmlhttpRequest : (typeof GM !== 'undefined' && GM.xmlHttpRequest);
      if (!gm) return reject(new Error('GM_xmlhttpRequest در دسترس نیست (مجوز @grant را بررسی کنید)'));
      const t0 = Date.now();
      gm({
        method: 'GET', url, timeout, anonymous,
        headers: { Accept: accept, 'Accept-Language': 'fa-IR,fa;q=0.9,en;q=0.8', ...(referer ? { Referer: referer } : {}), ...headers },
        onload: r => {
          const ms = Date.now() - t0, u = new URL(url);
          Log.info('net', `${r.status} ${u.hostname}${u.pathname} (${ms}ms)`);
          if (r.status === 200) resolve(r.responseText || '');
          else { const e = new Error('HTTP ' + r.status); e.status = r.status; reject(e); }
        },
        onerror: e => { const d = e ? JSON.stringify({ error: e.error, status: e.status, finalUrl: e.finalUrl }) : ''; Log.warn('net', 'onerror ' + new URL(url).hostname + ' ' + d); reject(new Error('خطای شبکه' + (e && e.error ? ` (${e.error})` : ' (GM_xmlhttpRequest بدون جزئیات؛ مجوز @connect یا کوکی/VPN را بررسی کنید)'))); },
        ontimeout: () => reject(new Error('timeout'))
      });
    });
  }
  async function pageFetch(url, { accept = 'application/json', timeout = 15000 } = {}) {
    const ctl = typeof AbortController === 'function' ? new AbortController() : null; const tm = ctl && setTimeout(() => ctl.abort(), timeout);
    try {
      const r = await fetch(url, { credentials: 'include', headers: { Accept: accept }, signal: ctl && ctl.signal });
      if (!r.ok) { const e = new Error('HTTP ' + r.status); e.status = r.status; throw e; }
      return await r.text();
    } finally { if (tm) clearTimeout(tm); }
  }
  async function request(url, opts = {}) {
    if (Date.now() < COOLDOWN_UNTIL) {
      const left = Math.ceil((COOLDOWN_UNTIL - Date.now()) / 60000);
      throw new Error(`محدودیت نرخ فعال است؛ ${left} دقیقه دیگر تلاش کنید`);
    }
    let attempt = 0;
    while (true) {
      try { return await gmRequest(url, opts); }
      catch (e) {
        if (e.status === 429) {
          COOLDOWN_UNTIL = Date.now() + COOLDOWN_MS;
          Log.warn('net', '۴۲۹ — ۱۰ دقیقه تعویق فعال شد');
          if (attempt < 2) {
            const wait = 2000 * Math.pow(2, attempt);
            Log.warn('net', `429 — تلاش دوباره پس از ${wait}ms`);
            await U.sleep(wait); attempt++; continue;
          }
          throw new Error(`محدودیت نرخ دیجی‌کالا (HTTP 429)؛ ۱۰ دقیقه تعویق فعال شد`);
        }
        if (!opts.pageFetchFallback || e.status) throw e;
        Log.warn('net', 'GM ناموفق بود، تلاش با fetch صفحه: ' + e.message);
        try { const t = await pageFetch(url, opts); Log.info('net', 'fetch صفحه موفق بود'); return t; }
        catch (e2) { throw new Error(e.message + ' | fetch صفحه: ' + e2.message); }
      }
    }
  }
  async function json(url, opts) {
    const txt = await request(url, opts);
    try { return JSON.parse(txt); } catch { throw new Error('پاسخ JSON معتبر نیست'); }
  }
  const CACHE = new Map();
  const CACHE_TTL = 5 * 60e3;
  async function cachedJson(url, opts) {
    const hit = CACHE.get(url);
    if (hit && Date.now() - hit.t < CACHE_TTL) { Log.info('net', 'cache hit ' + url); return hit.v; }
    const v = await json(url, opts);
    CACHE.set(url, { t: Date.now(), v });
    return v;
  }
  async function health() {
    const tests = [
      { name: 'digikala', url: 'https://api.digikala.com/v1/search/?q=test&page=1' },
      { name: 'torob', url: 'https://api.torob.com/v4/base-product/search/?page=0&query=test&size=1' }
    ];
    const out = [];
    for (const t of tests) {
      const t0 = Date.now();
      try {
        const txt = await gmRequest(t.url, { referer: 'https://www.digikala.com/', timeout: 10000 });
        out.push({ name: t.name, ok: true, ms: Date.now() - t0, len: txt.length });
      } catch (e) {
        out.push({ name: t.name, ok: false, ms: Date.now() - t0, error: e.message, status: e.status });
      }
    }
    return out;
  }
  return { request, json, cachedJson, allowed, ALLOWED, health, cooldownLeft: () => Math.max(0, Math.ceil((COOLDOWN_UNTIL - Date.now()) / 60000)) };
})();


// ---- 05-model.js ----
const Model = (() => {
  const now = () => Date.now();
  function product(o) {
    return {
      id: o.id || '', key: o.key || '', host: o.host || '', title: o.title || '', url: o.url || '',
      price: o.price ?? null, currency: 'IRT', priceSource: o.priceSource || '', priceTs: o.priceTs || now(),
      oldPrice: o.oldPrice ?? null, variantId: o.variantId || '', variantTitle: o.variantTitle || '',
      seller: o.seller || '', warranty: o.warranty || '', nameCandidates: o.nameCandidates || [],
      priceDelta: o.priceDelta ?? null
    };
  }
  function offer(o) {
    return {
      sourceId: o.sourceId, productId: o.productId || '', seller: o.seller || '', sellerKey: o.sellerKey || '',
      sellerUrl: o.sellerUrl || '', price: o.price, currency: 'IRT', shippingCost: o.shippingCost ?? null,
      ts: o.ts || now(), dataSource: o.dataSource || o.sourceId, matchConfidence: o.matchConfidence ?? null,
      matchLevel: o.matchLevel || '', matchTitle: o.matchTitle || '', flags: o.flags || []
    };
  }
  function point(o) {
    return { t: o.t, day: o.day || '', price: o.price, rrp: o.rrp ?? null, seller: o.seller || '', warranty: o.warranty || '',
      marketable: o.marketable !== false, source: o.source, kind: o.kind || 'selling_price', currency: 'IRT' };
  }
  return { product, offer, point };
})();


// ---- 06-extract.js ----
const Extract = (() => {
  const KNOWN = {
    'digikala.com': ['دیجی‌کالا', 'دیجیکالا', 'دیجی کالا'], 'torob.com': ['ترب'], 'emalls.ir': ['ای‌مالز', 'ایمالز', 'امالز'],
    'technolife.com': ['تکنولایف', 'تکنو لایف'], 'basalam.com': ['باسلام'], 'banimode.com': ['بانی‌مد', 'بانی مد'],
    'okala.com': ['اکالا'], 'mobile140.com': ['موبایل ۱۴۰', 'موبایل140'], 'digistyle.com': ['دیجی‌استایل', 'دیجی استایل']
  };
  const BRAND_KEYS = Object.keys(KNOWN).flatMap(k => [U.compact(k.split('.')[0]), ...KNOWN[k].map(U.compact)]).filter(k => k.length >= 4);
  const isStoreName = s => { const c = U.compact(s); return !!c && BRAND_KEYS.some(b => c === b || c.includes(b)); };
  const matchKnownSite = d => {
    const c = U.compact(d); if (!c) return null;
    for (const k of Object.keys(KNOWN)) {
      for (const a of [U.compact(k.split('.')[0]), ...KNOWN[k].map(U.compact)]) {
        if (!a) continue; if (c === a) return k; if (a.length >= 5 && c.includes(a)) return k;
      }
    }
    return null;
  };
  const hasUnit = s => { const t = U.digits(s); return /\d/.test(t) && /گرم|کیلو|میلی|لیتر|عدد|بسته|سانتی|متر|سی.?سی|\b(ml|kg|g|l|gr|cm|mm)\b/i.test(t); };
  const NAME_JUNK = [/^\s*قیمت\s*و\s*خرید\s+/, /^\s*خرید\s+/, /\s*(با|در)\s*قیمت\s*(روز|مناسب|ارزان|عمده)?.*$/, /\s*خرید\s*(آنلاین|اینترنتی|قسطی|اقساطی).*$/, /\s*(ارسال\s*رایگان|تخفیف|گارانتی|اصل|اورجینال).*$/];
  function cleanTitle(raw) {
    const parts = String(raw || '').split(/\s*[|—–]\s*|\s+-\s+/).map(s => s.trim()).filter(Boolean);
    let t = parts.filter((p, i) => i === 0 || (!isStoreName(p) && hasUnit(p))).join(' - ').replace(/\d[\d٬,،\s]*\s*(تومان|تومن|ت)\b.*$/u, '').replace(/\s+/g, ' ').trim();
    for (const r of NAME_JUNK) t = t.replace(r, '').trim();
    return t.slice(0, 120);
  }
  function titleFromUrl() {
    try {
      const last = decodeURIComponent(location.pathname).split('/').filter(Boolean).pop() || '';
      const t = last.replace(/^\d+[-_]?/, '').replace(/[-_+]+/g, ' ').replace(/\s+/g, ' ').trim();
      return /[آ-ی]/.test(t) && t.split(' ').length >= 3 ? t : '';
    } catch { return ''; }
  }

  const STRIKE_CLASS = /line-through|strikethrough|(^|[\s_:-])(old|del|strike|discount)(?=$|[\s_:-])/i;
  const isStruck = el => {
    if (STRIKE_CLASS.test(el.className && el.className.toString ? el.className.toString() : '')) return true;
    try { if ((getComputedStyle(el).textDecorationLine || '').includes('line-through')) return true; } catch {}
    return !!el.closest('del, s, strike');
  };
  const struckNumbers = root => { const s = new Set(); root.querySelectorAll('*').forEach(e => { if (isStruck(e)) U.numbersIn(e.textContent).forEach(v => s.add(v)); }); return s; };
  let _bodyText = null, _bodyTs = 0;
  function bodyTextCached() {
    const now = Date.now();
    if (!_bodyText || now - _bodyTs > 500) { _bodyText = document.body.innerText || ''; _bodyTs = now; }
    return _bodyText;
  }
  const visibleOnPage = n => { const t = U.digits(bodyTextCached()).replace(/(\d)[,٬،](?=\d)/g, '$1'); return new RegExp('(?<!\\d)' + n + '(?!\\d)').test(t); };

  function jsonLd(root) {
    let found = null;
    root.querySelectorAll('script[type="application/ld+json"]').forEach(sc => {
      if (found) return; let data; try { data = JSON.parse(sc.textContent); } catch { return; }
      (function walk(o) {
        if (!o || typeof o !== 'object' || found) return;
        if (Array.isArray(o)) { o.forEach(walk); return; }
        const ty = o['@type'];
        if (ty === 'Product' || (Array.isArray(ty) && ty.includes('Product'))) {
          let raw = 0, cur = '';
          for (const of of [].concat(o.offers || [])) {
            const x = of && of.offers ? [].concat(of.offers)[0] : of;
            const v = Number(String(x?.price ?? x?.lowPrice ?? '').replace(/[^\d.]/g, ''));
            if (v > 0) { raw = v; cur = String(x.priceCurrency || '').toUpperCase(); break; }
          }
          found = { name: o.name || '', raw: raw || null, cur }; return;
        }
        Object.values(o).forEach(walk);
      })(data);
    });
    return found;
  }
  function reconcileJsonLd(ld, visible) {
    if (!ld || !ld.raw) return null;
    const asToman = ld.cur === 'IRR' ? Math.round(ld.raw / 10) : Math.round(ld.raw), asRaw = Math.round(ld.raw), asDiv = Math.round(ld.raw / 10);
    if (!visible) {
      if (!visibleOnPage(asToman)) {
        if (visibleOnPage(asRaw)) return { price: asRaw, note: ' (واحد JSON-LD اصلاح شد)' };
        if (visibleOnPage(asDiv)) return { price: asDiv, note: ' (واحد JSON-LD اصلاح شد)' };
      }
      return { price: asToman, note: '' };
    }
    const near = v => Math.abs(v - visible) / visible < 0.02;
    if (near(asToman)) return { price: asToman, note: '' };
    if (near(asRaw)) return { price: asRaw, note: ' (واحد JSON-LD اصلاح شد)' };
    if (near(asDiv)) return { price: asDiv, note: ' (واحد JSON-LD اصلاح شد)' };
    return null;
  }

  const SELLER_BLOCK = "[data-testid*='seller'], [class*='seller'], [class*='related'], [class*='similar']";
  function buyBarPrice() {
    const btns = [...document.querySelectorAll('button, a, div, span')].filter(e => {
      if (e.children.length > 4) return false; const t = (e.innerText || '').trim(); return t.length > 0 && t.length < 30 && /افزودن به سبد/.test(t);
    });
    for (const b of btns) {
      let p = b.parentElement;
      for (let i = 0; i < 6 && p; i++, p = p.parentElement) {
        const txt = p.innerText || ''; if (txt.length > 500) break;
        const struck = struckNumbers(p), cand = U.numbersIn(txt).filter(v => v >= 10000 && !struck.has(v));
        if (cand.length) return Math.min(...cand);
      }
    }
    return null;
  }
  function claimedOldPrice(current) {
    const btns = [...document.querySelectorAll('button, a, div, span')].filter(e => e.children.length <= 4 && /افزودن به سبد/.test((e.innerText || '').trim()) && (e.innerText || '').trim().length < 30);
    for (const b of btns) {
      let p = b.parentElement;
      for (let i = 0; i < 6 && p; i++, p = p.parentElement) {
        const txt = p.innerText || ''; if (txt.length > 500) break;
        const s = [...struckNumbers(p)].filter(v => v >= 10000 && (!current || v > current));
        if (s.length) return Math.max(...s);
      }
    }
    return null;
  }
  function testIdPrice() {
    for (const el of document.querySelectorAll('[data-testid="price-final"], [data-testid="price-current"], [data-testid="price"]')) {
      if (el.closest("[data-testid*='seller'], [class*='seller']")) continue;
      const a = U.pricesWithCurrency((el.innerText || el.textContent || '') + ' تومان'); if (a.length) return Math.min(...a);
      const n = Number(U.digits(el.textContent).replace(/\D/g, '')); if (n >= 10000) return n;
    }
    return null;
  }
  function classPrice() {
    const els = [...document.querySelectorAll("[class*='price'], [data-testid*='price'], [id*='price']")].filter(e => {
      if (e.closest(SELLER_BLOCK) || isStruck(e)) return false;
      return /^\d{1,3}(?:[,٬،]\d{3})+$|^\d{5,}$/.test(U.digits(e.textContent).replace(/\s|تومان|ت$/g, '').trim());
    });
    const arr = els.map(e => ({ top: e.getBoundingClientRect().top + window.scrollY, value: Number(U.digits(e.textContent).replace(/\D/g, '')) })).filter(x => x.value >= 10000);
    arr.sort((a, b) => a.top - b.top); return arr.length ? arr[0].value : null;
  }
  function unstruckPrice() {
    const els = [...document.querySelectorAll('p, span, div, strong, b')].filter(e => {
      if (e.children.length !== 0) return false; const t = U.digits(e.textContent).trim();
      if (!/^\d{1,3}(?:[,٬]\d{3})+$/.test(t) || isStruck(e) || e.closest(SELLER_BLOCK)) return false;
      const n = Number(t.replace(/\D/g, '')); return n >= 100000 && n <= 100000000;
    });
    const arr = els.map(e => ({ value: Number(U.digits(e.textContent).replace(/\D/g, '')), score: /font-semibold|font-bold|text-h4|text-xl|text-primary/.test(e.className.toString()) ? 2 : 0 }));
    arr.sort((a, b) => b.score - a.score); return arr.length ? arr[0].value : null;
  }
  function nearBuyButton() {
    const els = [...document.querySelectorAll('button, a, div')].filter(e => { const t = (e.innerText || '').trim(); return t.length > 0 && t.length < 40 && /افزودن به سبد|خرید/.test(t); });
    for (const b of els) {
      let p = b;
      for (let i = 0; i < 8 && p; i++) {
        const t = p.innerText || '';
        if (t.length < 400) { const a = U.pricesWithCurrency(t.split('\n').filter(l => !/ارزان|گران|تخفیف|پیشنهاد|قسط|ماه|سود|بخرید|اعتبار/.test(l)).join('\n')); if (a.length) return Math.min(...a); }
        p = p.parentElement;
      }
    }
    return null;
  }

  function selectedColor() {
    const m = U.digits(document.body.innerText || '').match(/رنگ\s*[:：]\s*([^\n\r]{1,30})/); return m ? m[1].trim() : '';
  }
  function digikalaIds() {
    const m = location.pathname.match(/dkp-(\d+)/i); const v = new URLSearchParams(location.search).get('variant_id');
    return m ? { pid: m[1], variantId: v || '' } : null;
  }

  function product(root = document) {
    const ld = jsonLd(root) || {};
    const meta = sel => root.querySelector(sel)?.getAttribute('content') || '';
    const h1 = root.querySelector('h1')?.textContent?.trim() || '';
    const cands = [h1, ld.name, meta('meta[property="og:title"]'), root.title, titleFromUrl()].map(cleanTitle).filter(c => c && !isStoreName(c) && !/^فروشگاه\s*اینترنتی/.test(c));
    let name = cands[0] || '';
    if (U.tokens(name).length < 3) { const alt = cands.find(c => U.tokens(c).length >= 3); if (alt) name = alt; }
    const nn = U.normalize(name);
    for (const c of cands) { const cn = U.normalize(c); if (nn && cn.length > nn.length && cn.includes(nn) && c.length <= 120) { name = c; break; } }

    let price = null, src = '';
    const visible = buyBarPrice(), rec = reconcileJsonLd(ld, visible);
    if (rec) { price = rec.price; src = 'JSON-LD' + rec.note; }
    if (!price && visible) { price = visible; src = 'نوار خرید'; }
    if (!price) { const v = Number(meta('meta[property="product:price:amount"]').replace(/[^\d]/g, '')); if (v > 0) { price = v; src = 'متای صفحه'; } }
    if (!price) { const v = testIdPrice(); if (v) { price = v; src = 'data-testid'; } }
    if (!price) { const v = classPrice(); if (v) { price = v; src = 'کلاس قیمت'; } }
    if (!price) { const v = unstruckPrice(); if (v) { price = v; src = 'قیمت بدون خط‌خوردگی'; } }
    if (!price) { const v = nearBuyButton(); if (v) { price = v; src = 'نزدیک دکمهٔ خرید'; } }
    const dk = digikalaIds();
    const out = { title: name, price, priceSource: src, oldPrice: price ? claimedOldPrice(price) : null, nameCandidates: cands, color: selectedColor(),
      host: location.hostname.replace(/^www\./, ''), url: location.href, id: dk ? dk.pid : '', variantId: dk ? dk.variantId : '' };
    Log.info('extract', `name="${name}" price=${price || '—'} src=${src || '—'} old=${out.oldPrice || '—'}`);
    return out;
  }
  function looksLikeProductPage() {
    if (/dkp-\d+/i.test(location.pathname)) return true;
    if (document.querySelector('meta[property="og:type"][content*="product"]')) return true;
    if (jsonLd(document)) return true;
    return !!([...document.querySelectorAll('button')].some(b => /افزودن به سبد/.test(b.textContent || '')) && document.querySelector('h1'));
  }
  return { KNOWN, isStoreName, matchKnownSite, cleanTitle, jsonLd, reconcileJsonLd, product, looksLikeProductPage, digikalaIds, selectedColor, buyBarPrice, claimedOldPrice };
})();


// ---- 07-match.js ----
const Match = (() => {
  function baseline(src, cand) {
    const st = U.tokens(src); if (!st.length) return false;
    const cn = U.normalize(cand), set = new Set(cn.split(' ')), cc = cn.replace(/\s+/g, '');
    const hit = st.filter(t => set.has(t) || (t.length >= 4 && cc.includes(t))).length;
    if (hit / st.length < 0.5) return false;
    return st.filter(t => /\d/.test(t) && /[a-z]/.test(t)).every(t => cc.includes(t));
  }
  function modelCodes(raw) {
    const t = U.digits(raw).replace(/[ـ]/g, '');
    const out = new Set();
    const re = /[A-Za-z]+[A-Za-z0-9]*?[\s\/\-_.]?\d+[A-Za-z0-9]*|\d+[\s]?[A-Za-z]+[A-Za-z0-9]*/g; let m;
    while ((m = re.exec(t))) { const c = m[0].toLowerCase().replace(/[^a-z0-9]/g, ''); if (c.length >= 3 && /[a-z]/.test(c) && /\d/.test(c)) out.add(c); }
    return [...out];
  }
  const UNITS = [['gb', /گیگابایت|گیگ|gb/], ['tb', /ترابایت|tb/], ['ml', /میلی ?لیتر|ml/], ['l', /لیتر/], ['kg', /کیلوگرم|کیلو|kg/], ['g', /گرم|gr|(?<![a-z])g(?![a-z])/], ['mah', /mah|میلی ?آمپر/], ['w', /وات|(?<![a-z])w(?![a-z])/], ['inch', /اینچ|inch/], ['cm', /سانتی ?متر|cm/], ['mm', /میلی ?متر|mm/]];
  function specs(raw) {
    const t = U.normalize(raw).replace(/(\d)\s+(?=[a-zآ-ی])/g, '$1'), out = {};
    for (const [u, re] of UNITS) {
      const rx = new RegExp('(\\d+)(?:' + re.source + ')', 'g'); let m;
      while ((m = rx.exec(t))) (out[u] ||= new Set()).add(Number(m[1]));
    }
    return out;
  }
  function evaluate(src, cand) {
    const reasons = [], flags = [];
    const base = baseline(src, cand);
    const st = U.tokens(src), cn = U.normalize(cand), set = new Set(cn.split(' ')), cc = cn.replace(/\s+/g, '');
    const cov = st.length ? st.filter(t => set.has(t) || (t.length >= 4 && cc.includes(t))).length / st.length : 0;
    if (!base) return { ok: false, score: cov * 0.4, level: 'low', reasons: ['عدم تطبیق پایه (نام/توکن‌ها)'], flags: ['base-mismatch'] };

    const codes = modelCodes(src), found = codes.filter(c => cc.includes(c));
    let model = codes.length ? found.length / codes.length : null;
    if (codes.length && found.length === 0) return { ok: false, score: cov * 0.3, level: 'low', reasons: ['کد مدل مبدا (' + codes.join('، ') + ') در نتیجه نیست'], flags: ['model-mismatch'] };
    if (codes.length && found.length < codes.length) { flags.push('partial-model'); reasons.push('بخشی از کد مدل/ظرفیت تأیید نشد'); }
    const a = specs(src), b = specs(cand);
    for (const u of Object.keys(a)) if (b[u] && ![...a[u]].some(v => b[u].has(v))) return { ok: false, score: cov * 0.3, level: 'low', reasons: ['مشخصه ' + u + ' متفاوت است'], flags: ['spec-mismatch'] };
    let score = codes.length ? 0.35 * cov + 0.65 * model : Math.min(0.85, cov);
    if (!codes.length) { flags.push('no-model-code'); reasons.push('کد مدل لاتین برای تأیید وجود ندارد'); }
    if (cov < 0.75) { flags.push('low-coverage'); reasons.push('پوشش کلمات نام ' + Math.round(cov * 100) + '٪'); }
    const level = score >= 0.85 ? 'high' : score >= 0.65 ? 'medium' : 'low';
    if (level === 'low') flags.push('suspicious');
    return { ok: true, score: +score.toFixed(2), level, reasons, flags };
  }
  return { baseline, modelCodes, specs, evaluate };
})();


// ---- 08-sources.js ----
const Sources = (() => {
  const TOROB_REF = 'https://torob.com/';
  const DK_REF = 'https://www.digikala.com/';
  const DK_OPTS = { referer: DK_REF, headers: { 'x-web-client': 'desktop', 'x-web-client-id': 'web' }, anonymous: false, pageFetchFallback: true };

  const torob = {
    id: 'torob', label: 'ترب', kind: 'offers', implemented: true, hosts: ['api.torob.com'],
    note: 'جست‌وجوی چندمرحله‌ای ← انتخاب محصول مطابق (قابل‌تغییر دستی) ← فهرست فروشندگان',
    titles: prod => [prod.title, ...(prod.altTitles || [])].filter(Boolean),
    queries(prod, override) {
      if (override) return [override.trim()];
      const t = torob.titles(prod), codes = [...new Set(t.flatMap(Match.modelCodes))];
      const en = (prod.altTitles || []).find(x => /^[\x00-\x7F\s]+$/.test(x));
      const short = codes.length ? (U.tokens(prod.title).slice(0, 4).join(' ') + ' ' + codes.join(' ')).trim() : '';
      return [...new Set([prod.title, en, short].filter(Boolean).map(x => x.trim()))].slice(0, 3);
    },
    async search(q) {
      const e = encodeURIComponent(q);
      const url = `https://api.torob.com/v4/base-product/search/?page=0&sort=popularity&size=24&query=${e}&q=${e}&source=next_desktop`;
      let last;
      for (let i = 0; i < 2; i++) {
        try {
          const r = await Net.json(url, { referer: TOROB_REF, timeout: 15000 });
          return { results: Array.isArray(r.results) ? r.results : [], searchId: r.search_id || r.searchId || '' };
        } catch (err) { last = err; await U.sleep(1000 * (i + 1)); }
      }
      throw last;
    },
    evalCand(prod, r) {
      const ct = r.name1 + ' ' + (r.name2 || ''); let best = null;
      for (const t of torob.titles(prod)) { const ev = Match.evaluate(t, ct); if (!best || (ev.ok && !best.ok) || (ev.ok === best.ok && ev.score > best.score)) best = ev; }
      return best;
    },
    async sellers(prod, base, ev, searchId) {
      const baseTitle = base.name1 + ' ' + (base.name2 || '');
      const params = new URLSearchParams({ source: 'next_mobile', discover_method: 'direct', prk: base.random_key, list_type: 'products_info' });
      if (searchId) params.set('search_id', searchId);
      const res = await Net.json('https://api.torob.com/v4/base-product/sellers/?' + params, { referer: TOROB_REF, timeout: 15000 });
      const list = res?.results || res?.products_info?.result || [], ts = Date.now();
      const raw = list.map(s => {
        const shop = String(s.shop_name || s.domain || s.shop_text || '').replace(/^www\./, '');
        const key = Extract.matchKnownSite(s.domain || shop) || Extract.matchKnownSite(shop);
        return Model.offer({ sourceId: 'torob', productId: prod.id, seller: key ? (Extract.KNOWN[key][0] || key) : shop, sellerKey: key || '', sellerUrl: String(s.page_url || ''), price: Number(s.price ?? s.price_value),
          ts, dataSource: 'torob:base-product/sellers', matchConfidence: ev.score, matchLevel: ev.level, matchTitle: baseTitle, flags: ev.flags });
      }).filter(o => o.seller && o.price > 0);
      const byS = new Map(), dup = {};
      for (const o of raw) { const k = o.sellerKey || o.seller; dup[k] = (dup[k] || 0) + 1; const cur = byS.get(k); if (!cur || o.price < cur.price) byS.set(k, o); }
      const offers = [...byS.values()].map(o => { const k = o.sellerKey || o.seller; if (dup[k] > 1) o.flags = [...o.flags, 'dedup:' + dup[k]]; return o; });
      Log.info('torob', `${raw.length} فروشنده → ${offers.length} پس از حذف تکراری`);
      return offers;
    },
    async fetch(prod, { query, pickKey } = {}) {
      const tried = []; let found = null; const nearMiss = []; let rejected = 0;
      const qs = torob.queries(prod, query);
      for (let i = 0; i < qs.length && !found; i++) {
        let res; try { res = await torob.search(qs[i]); } catch (e) { if (i === 0) throw e; Log.warn('torob', 'جست‌وجوی مرحلهٔ ' + (i + 1) + ' ناموفق: ' + e.message); break; }
        tried.push(qs[i]); Log.info('torob', `«${qs[i]}» → ${res.results.length} نتیجه`);
        const valid = res.results.filter(r => r && r.name1 && !r.is_adv && Number(r.price) > 0 && r.random_key);
        const evaluated = valid.map(r => ({ r, ev: torob.evalCand(prod, r) })), ok = evaluated.filter(x => x.ev.ok);
        rejected += evaluated.length - ok.length;
        for (const x of evaluated.filter(x => !x.ev.ok && x.ev.flags.includes('model-mismatch')).slice(0, 3)) nearMiss.push({ title: x.r.name1 + ' ' + (x.r.name2 || ''), reason: x.ev.reasons[0] });
        if (ok.length) { const rank = { high: 0, medium: 1, low: 2 }; ok.sort((a, b) => rank[a.ev.level] - rank[b.ev.level] || Number(a.r.price) - Number(b.r.price)); found = { ok, searchId: res.searchId, q: qs[i] }; }
      }
      if (!found) return { status: 'no-match', offers: [], note: 'محصول مطابقی در ترب با اطمینان کافی پیدا نشد (' + tried.length + ' جست‌وجو)', nearMiss: nearMiss.slice(0, 3), rejected, tried, candidates: [], query: tried[0] || '' };
      const pick = (pickKey && found.ok.find(x => x.r.random_key === pickKey)) || found.ok[0], base = pick.r;
      const baseTitle = base.name1 + ' ' + (base.name2 || '');
      Log.info('torob', `محصول انتخاب‌شده: ${baseTitle} [${pick.ev.level} ${pick.ev.score}]`);
      const offers = await torob.sellers(prod, base, pick.ev, found.searchId);
      const candidates = found.ok.slice(0, 6).map(x => ({ key: x.r.random_key, title: x.r.name1 + ' ' + (x.r.name2 || ''), price: Number(x.r.price), level: x.ev.level }));
      return { status: offers.length ? 'ok' : 'empty', offers, note: baseTitle, nearMiss: nearMiss.slice(0, 3), rejected, tried, candidates, chosenKey: base.random_key, query: found.q };
    }
  };

  const unverified = (id, label, hosts) => ({ id, label, kind: 'offers', implemented: false, hosts, note: 'پیاده‌سازی نشده: اندپوینت رسمی/قابل‌اتکا هنوز تأیید نشده؛ هیچ قیمت حدسی نمایش داده نمی‌شود', async fetch() { return { status: 'unavailable', offers: [], note: this.note }; } });
  const emalls = unverified('emalls', 'ایمالز', ['emalls.ir']);
  const basalam = unverified('basalam', 'باسلام', ['basalam.com']);

  const dk = {
    parseProduct(json, variantId) {
      const p = json?.data?.product; if (!p) return null;
      const vs = Array.isArray(p.variants) ? p.variants : [];
      const toT = r => (r == null ? null : Math.round(Number(r) / 10));
      const mk = v => { const pr = v.price || {}; return { variantId: String(v.id), title: (v.themes || []).map(t => t.value && t.value.title).filter(Boolean).join(' / '), price: toT(pr.selling_price), rrp: pr.discount_percent ? toT(pr.rrp_price) : null, discountPct: pr.discount_percent || 0, seller: v.seller?.title || '', warranty: v.warranty?.title_fa || '' }; };
      const all = vs.map(mk).filter(x => x.price > 0).sort((a, b) => a.price - b.price);
      const chosen = (variantId && all.find(x => x.variantId === String(variantId))) || null;
      const prices = all.map(v => v.price).filter(x => x > 0);
      const medianPrice = prices.length ? U.median(prices) : null;
      return { title: p.title_fa || '', titleEn: p.title_en || '', brand: p.brand?.title_fa || '', variants: all, chosen, exact: !!chosen, lowest30dOfficial: toT(p.properties?.min_price_in_last_month), medianPrice };
    },
    async product(pid, variantId) {
      const json = await Net.cachedJson(`https://api.digikala.com/product/v1/products/${pid}/`, DK_OPTS);
      return dk.parseProduct(json, variantId);
    },
    async search(q) {
      const e = encodeURIComponent(q);
      const json = await Net.cachedJson(`https://api.digikala.com/v1/search/?q=${e}&page=1`, DK_OPTS);
      const list = json?.data?.products || [];
      return list.map(p => ({
        id: String(p.id),
        title: p.title_fa || '',
        price: p.default_variant?.price?.selling_price ? Math.round(p.default_variant.price.selling_price / 10) : null,
        url: `https://www.digikala.com/product/dkp-${p.id}/`
      })).filter(x => x.title && x.price > 0);
    },
    parseChart(json) {
      const d = json?.data; if (!d || !Array.isArray(d.price_chart)) return null;
      const variants = d.price_chart.map((c, i) => {
        const pts = (c.history || []).map(h => {
          const t = U.jalaliToTime(h.day); if (t == null) return null;
          const sp = Number(h.selling_price);
          return Model.point({ t, day: h.day, price: sp > 0 ? Math.round(sp / 10) : null, rrp: Number(h.rrp_price) > 0 ? Math.round(Number(h.rrp_price) / 10) : null,
            seller: h.seller || '', warranty: h.product_warranty || '', marketable: !!h.is_marketable && sp > 0, source: 'digikala:price-chart' });
        }).filter(Boolean).sort((a, b) => a.t - b.t);
        return { id: String(c.id ?? i), title: c.title || '', points: pts };
      });
      const all = variants.flatMap(v => v.points), ts = all.map(p => p.t);
      return { today: d.today || '', selectionTitle: d.chart_selection_title || '', variants, range: ts.length ? { from: Math.min(...ts), to: Math.max(...ts), days: Math.round((Math.max(...ts) - Math.min(...ts)) / U.DAY) + 1 } : null };
    },
    async chart(pid) {
      const json = await Net.cachedJson(`https://api.digikala.com/v1/product/${pid}/price-chart/`, DK_OPTS);
      const c = dk.parseChart(json); if (!c) throw new Error('ساختار پاسخ نمودار قیمت شناخته نشد');
      return c;
    },
    pickVariant(chart, color) {
      if (!chart || !chart.variants.length) return null;
      const c = U.compact(color || '');
      if (c) { const m = chart.variants.find(v => U.compact(v.title) === c) || chart.variants.find(v => c.includes(U.compact(v.title)) || U.compact(v.title).includes(c)); if (m) return { variant: m, exact: true }; }
      const live = chart.variants.filter(v => v.points.some(p => p.marketable));
      const best = (live.length ? live : chart.variants).slice().sort((a, b) => b.points.length - a.points.length)[0];
      return { variant: best, exact: chart.variants.length === 1 };
    }
  };

  const registry = { torob, emalls, basalam };
  return { registry, torob, emalls, basalam, dk };
})();
// ---- 09-analysis.js ----
const Analysis = (() => {
  const valid = pts => pts.filter(p => p.marketable && p.price > 0).sort((a, b) => a.t - b.t);
  const lastN = (pts, days, end) => pts.filter(p => p.t > end - days * U.DAY);
  function stats(pts) {
    const s = valid(pts); if (!s.length) return null;
    const prices = s.map(p => p.price), first = s[0], last = s[s.length - 1];
    const span = Math.round((last.t - first.t) / U.DAY) + 1;
    const minP = s.reduce((a, b) => (b.price < a.price ? b : a)), maxP = s.reduce((a, b) => (b.price > a.price ? b : a));
    let held = null; for (let i = 1; i < s.length; i++) { const m = Math.max(s[i - 1].price, s[i].price); if (held == null || m < held) held = m; }
    const sellers = new Set(s.map(p => p.seller).filter(Boolean));
    return { count: s.length, span, from: first.t, to: last.t, min: minP.price, minT: minP.t, max: maxP.price, maxT: maxP.t, median: U.median(prices), first: first.price, last: last.price, heldLow: held, sellers: sellers.size, missingDays: Math.max(0, span - s.length) };
  }
  const confidenceOf = st => !st ? 'none' : (st.span >= 60 && st.count >= 45) ? 'high' : (st.span >= 21 && st.count >= 15) ? 'medium' : 'low';

  function inspect(pts, ctx = {}) {
    const s = valid(pts), st = stats(s), res = { verdict: 'insufficient', confidence: confidenceOf(st), reasons: [], signals: [], numbers: {}, stats: st };
    if (!st) { res.reasons.push('هیچ نقطهٔ تاریخی معتبر (قابل‌فروش) وجود ندارد.'); return res; }
    if (st.count < 10 || st.span < 21) { res.reasons.push(`داده برای نتیجه‌گیری کافی نیست: ${U.toFa(st.count)} نقطه در بازهٔ ${U.toFa(st.span)} روز (حداقل ۱۰ نقطه و ۲۱ روز لازم است).`); return res; }
    const end = st.to, cut = end - 14 * U.DAY;
    const prior = s.filter(p => p.t <= cut), recent = s.filter(p => p.t > cut);
    if (prior.length < 5) { res.reasons.push('برای ساخت «قیمت پایه»، دادهٔ کافی قبل از ۱۴ روز اخیر وجود ندارد.'); return res; }
    const baseline = U.median(prior.map(p => p.price));
    const current = ctx.currentPrice > 0 ? ctx.currentPrice : st.last;
    const lastPt = s[s.length - 1];
    const claimedOld = ctx.claimedOld > 0 ? ctx.claimedOld : (lastPt.rrp && lastPt.rrp > lastPt.price ? lastPt.rrp : null);
    const realDrop = (baseline - current) / baseline;
    const claimedPct = claimedOld ? (claimedOld - current) / claimedOld : null;
    res.numbers = { baseline, current, claimedOld, realDropPct: realDrop * 100, claimedPct: claimedPct == null ? null : claimedPct * 100, min: st.min, max: st.max };

    const peak = recent.filter(p => p.t < end - 2 * U.DAY).reduce((a, b) => (!a || b.price > a.price ? b : a), null);
    if (peak && peak.price >= baseline * 1.08 && current <= peak.price * 0.95)
      res.signals.push({ code: 'pre-rise', text: `قیمت در ${U.faDate(peak.t)} به ${U.fmt(peak.price)} تومان رسیده (${U.fmtPct((peak.price / baseline - 1) * 100)} بالاتر از قیمت پایه) و سپس پایین آمده.` });
    if (claimedOld && claimedOld >= baseline * 1.08)
      res.signals.push({ code: 'inflated-reference', text: `«قیمت قبل از تخفیف» (${U.fmt(claimedOld)}) از قیمت پایهٔ واقعی (${U.fmt(baseline)}) ${U.fmtPct((claimedOld / baseline - 1) * 100)} بالاتر است.` });
    if (claimedPct != null && claimedPct - realDrop > 0.10)
      res.signals.push({ code: 'claim-gap', text: `تخفیف ادعایی ${U.fmtPct(claimedPct * 100)} است اما نسبت به قیمت پایه فقط ${U.fmtPct(Math.max(0, realDrop) * 100)} کاهش دیده می‌شود.` });

    if (res.signals.length) { res.verdict = 'rise-signal'; res.reasons.push('نشانه‌هایی از افزایش قیمت یا مرجع قیمتی بالاتر پیش از تخفیف دیده می‌شود؛ این به‌تنهایی اثبات تخلف نیست (ممکن است تغییر فروشنده، موجودی یا گارانتی باشد).'); }
    else if (realDrop >= 0.05) { res.verdict = 'confirmed'; res.reasons.push(`قیمت فعلی ${U.fmtPct(realDrop * 100)} پایین‌تر از قیمت پایهٔ ${U.toFa(prior.length)} روز قبل‌تر است و نشانهٔ افزایش پیش از تخفیف دیده نشد.`); }
    else { res.verdict = 'insufficient'; res.detail = 'no-drop'; res.reasons.push('داده کافی است اما کاهش معناداری (≥۵٪) نسبت به قیمت پایه دیده نمی‌شود؛ تخفیف تأییدشده‌ای وجود ندارد.'); }
    if (st.sellers > 1) res.reasons.push(`برندهٔ «خرید» در این بازه ${U.toFa(st.sellers)} فروشندهٔ مختلف بوده؛ قیمت روزانه ممکن است بین فروشنده‌ها جابه‌جا شده باشد.`);
    if (st.span < 90) res.reasons.push(`بازهٔ واقعی داده ${U.toFa(st.span)} روز است (کمتر از ۹۰ روز).`);
    if (st.missingDays > 0) res.reasons.push(`${U.toFa(st.missingDays)} روز در بازه داده‌ای ثبت نشده است (درون‌یابی نشده).`);
    return res;
  }

  function advise({ current, offers = [], hostKey = '', st = null, insp = null }) {
    const points = [], caveats = []; let tone = 'neutral', headline = 'اطلاعات کافی برای توصیهٔ قطعی نیست';
    if (!(current > 0)) return { tone, headline: 'قیمت فعلی پیدا نشد', points, caveats: ['ابتدا قیمت را دستی ثبت کنید.'] };
    const trusted = offers.filter(o => o.matchLevel !== 'low' && o.sellerKey !== hostKey);
    const best = trusted.slice().sort((a, b) => a.price - b.price)[0];
    let cheaper = false;
    if (best) {
      const diff = (current - best.price) / current;
      if (diff >= 0.02) { cheaper = true; points.push({ k: 'good', text: `${best.seller} حدود ${U.fmtPct(diff * 100)} (${U.fmt(current - best.price)} تومان) ارزان‌تر است.` }); }
      else points.push({ k: 'ok', text: 'قیمت این صفحه با ارزان‌ترین فروشندهٔ تطبیق‌یافته برابر یا کمتر است.' });
      if (best.matchLevel === 'medium') caveats.push('اطمینان تطبیق محصول در ترب «متوسط» است؛ مدل را قبل از خرید تأیید کنید.');
    } else caveats.push('فروشندهٔ دیگری با تطبیق قابل‌اتکا پیدا نشد.');
    let histGood = null;
    if (st && st.count >= 10) {
      if (current <= st.min * 1.03) { histGood = true; points.push({ k: 'good', text: `قیمت نزدیک کمترین قیمت ثبت‌شده (${U.fmt(st.min)}) در ${U.toFa(st.span)} روز اخیر است.` }); }
      else if (current >= st.median * 1.1) { histGood = false; points.push({ k: 'warn', text: `قیمت ${U.fmtPct((current / st.median - 1) * 100)} بالاتر از میانهٔ ${U.toFa(st.span)} روز اخیر (${U.fmt(st.median)}) است.` }); }
      else points.push({ k: 'ok', text: `قیمت در محدودهٔ معمول ${U.toFa(st.span)} روز اخیر است (کمینه ${U.fmt(st.min)}، میانه ${U.fmt(st.median)}).` });
    } else caveats.push('سابقهٔ قیمت کافی برای قضاوت دربارهٔ زمان خرید وجود ندارد.');
    if (insp && insp.verdict === 'rise-signal') { points.push({ k: 'warn', text: 'نشانهٔ افزایش قیمت پیش از تخفیف دیده می‌شود؛ تخفیف ادعایی را با احتیاط ببینید.' }); }
    caveats.push('هزینهٔ ارسال و گارانتی در مقایسه لحاظ نشده (داده‌ی قابل‌اتکا موجود نیست).');
    if (cheaper) { tone = 'warn'; headline = 'فروشندهٔ ارزان‌تری وجود دارد'; }
    else if (histGood === true) { tone = 'good'; headline = 'از نظر قیمت، زمان نسبتاً مناسبی است'; }
    else if (histGood === false) { tone = 'warn'; headline = 'قیمت فعلی از حد معمول بالاتر است'; }
    else if (best) { tone = 'good'; headline = 'قیمت این صفحه رقابتی است'; }
    return { tone, headline, points, caveats };
  }
  return { valid, stats, inspect, advise, confidenceOf };
})();


// ---- 10-app.js ----
const App = (() => {
  const state = {
    product: null, key: '', offers: [], sources: {},
    dk: null, chart: null, chartError: '', chartLoading: false, variantIdx: 0, variantExact: false,
    range: 90, tab: 'compare', running: false, sort: 'price', trustedOnly: false, banner: '',
    similar: [], similarLoading: false, compareAllResult: [], healthResult: []
  };
  const subs = new Set(); const emit = () => subs.forEach(f => { try { f(state); } catch (e) { Log.error('ui', e.message); } });
  const on = f => subs.add(f);

  const settings = () => Store.get().settings;
  const keyFor = p => `${p.host}:${p.id || U.compact(location.pathname).slice(0, 60)}`;

  async function refreshProduct() {
    const x = Extract.product(document);
    const prev = state.product;
    const p = Model.product({ ...x, key: '', priceTs: Date.now() });
    p.key = keyFor(p);
    if (!p.price && prev && prev.key === p.key && prev.priceSource === 'دستی') { p.price = prev.price; p.priceSource = 'دستی'; }
    if (state.key && state.key !== p.key) { state.offers = []; state.sources = {}; state.chart = null; state.chartError = ''; state.dk = null; state.dkTs = 0; state.similar = []; state.compareAllResult = []; }
    state.product = p; state.key = p.key;
    const rec = Store.touchProduct(p.key, { host: p.host, pid: p.id, title: p.title || '', url: p.url, variantTitle: x.color || '', variantId: p.variantId });
    const dayAgo = Date.now() - 24 * 3600e3;
    const yesterday = [...rec.local].reverse().find(z => z.t <= dayAgo);
    p.priceDelta = (p.price && yesterday) ? ((p.price - yesterday.p) / yesterday.p * 100) : null;
    const TRUSTED = /JSON-LD|نوار خرید|متای صفحه|data-testid|دستی/;
    if (p.price && p.title && TRUSTED.test(p.priceSource || '')) { if (Store.recordLocal(rec, p.price, 'page:' + p.priceSource)) Log.info('store', 'نقطهٔ محلی ثبت شد'); }
    else if (p.price) Log.info('store', 'قیمت برای تاریخچهٔ محلی ثبت نشد (منبع ضعیف یا نام خالی)');
    Store.save(); emit();
    if (p.id && p.host.endsWith('digikala.com') && (!state.dk || Date.now() - (state.dkTs || 0) > 120000)) { state.dkTs = Date.now(); loadDigikala(p, x.color); }
    return p;
  }

  async function loadDigikala(p, color) {
    try {
      state.dk = await Sources.dk.product(p.id, p.variantId);
      const d = state.dk;
      if (d) p.altTitles = [d.title, d.titleEn].filter(Boolean);
      if (d && d.chosen) {
        p.seller = d.chosen.seller; p.warranty = d.chosen.warranty; p.variantTitle = d.chosen.title;
        if (!p.oldPrice && d.chosen.rrp) p.oldPrice = d.chosen.rrp;
        if (!p.price) { p.price = d.chosen.price; p.priceSource = 'API دیجی‌کالا (واریانت دقیق)'; }
        else if (Math.abs(p.price - d.chosen.price) / d.chosen.price > 0.02) { Log.warn('price', `اختلاف قیمت صفحه (${p.price}) و API (${d.chosen.price})`); p.priceNote = 'قیمت صفحه با API دیجی‌کالا اختلاف دارد'; }
        if (d.medianPrice && d.chosen.price > d.medianPrice * 1.2) p.priceNote = `این واریانت ${U.fmtPct((d.chosen.price / d.medianPrice - 1) * 100)} از میانه واریانت‌های این محصول گران‌تر است`;
      } else if (d && !p.price && d.variants.length) { p.price = d.variants[0].price; p.priceSource = 'API دیجی‌کالا (ارزان‌ترین واریانت؛ واریانت دقیق نامشخص)'; }
      emit();
    } catch (e) { Log.warn('dk-product', e.message); }
    if (!state.chart) loadHistory(color);
  }

  async function loadHistory(color) {
    const p = state.product; if (!p || !p.id || state.chartLoading) return;
    state.chartLoading = true; state.chartError = ''; emit();
    try {
      state.chart = await Sources.dk.chart(p.id);
      const pick = Sources.dk.pickVariant(state.chart, color || p.variantTitle || Extract.selectedColor());
      state.variantIdx = pick ? Math.max(0, state.chart.variants.indexOf(pick.variant)) : 0; state.variantExact = !!(pick && pick.exact);
      Log.info('history', `بازهٔ داده: ${state.chart.range ? state.chart.range.days + ' روز' : '—'}, واریانت‌ها: ${state.chart.variants.length}`);
    } catch (e) { state.chart = null; state.chartError = (e.status === 429 ? 'محدودیت نرخ دیجی‌کالا (HTTP 429)؛ بعداً تلاش کنید' : e.message); Log.error('history', e.message); }
    state.chartLoading = false; emit();
  }

  async function runCompare(opts = {}) {
    if (state.running) return;
    const p = state.product || await refreshProduct();
    if (!p.title) { state.banner = 'نام محصول در این صفحه پیدا نشد.'; emit(); return; }
    state.banner = ''; state.running = true; state.offers = []; state.sources = {};
    const reg = Sources.registry, cfg = settings().sources;
    for (const id of Object.keys(reg)) state.sources[id] = { status: reg[id].implemented ? (cfg[id] ? 'loading' : 'off') : 'unavailable', count: 0, note: reg[id].implemented ? '' : reg[id].note };
    emit();
    await Promise.all(Object.keys(reg).filter(id => reg[id].implemented && cfg[id]).map(async id => {
      try {
        const r = await reg[id].fetch(p, opts);
        state.sources[id] = { status: r.status, count: r.offers.length, note: r.note || '', nearMiss: r.nearMiss || [], candidates: r.candidates || [], chosenKey: r.chosenKey || '', query: r.query || '', tried: r.tried || [], ts: Date.now() };
        state.offers.push(...r.offers);
      } catch (e) { state.sources[id] = { status: 'error', count: 0, error: e.message, ts: Date.now() }; Log.error(id, e.message); }
      emit();
    }));
    state.running = false; emit();
  }

  async function pickCandidate(key) {
    const p = state.product, st = state.sources.torob; if (!p || !st || state.running) return;
    state.running = true; emit();
    try {
      const r = await Sources.torob.fetch(p, { query: st.query, pickKey: key });
      state.offers = state.offers.filter(o => o.sourceId !== 'torob').concat(r.offers);
      state.sources.torob = { ...st, status: r.status, count: r.offers.length, note: r.note, candidates: r.candidates, chosenKey: r.chosenKey || key, ts: Date.now(), error: '' };
    } catch (e) { state.sources.torob = { ...st, status: 'error', error: e.message }; Log.error('torob', e.message); }
    state.running = false; emit();
  }
  function setManualPrice(n) {
    const p = state.product; if (!p || !(n > 0)) return;
    p.price = n; p.priceSource = 'دستی'; p.priceTs = Date.now();
    const rec = Store.touchProduct(p.key); Store.recordLocal(rec, n, 'manual'); Store.save(); emit();
  }

  async function loadSimilar() {
    const p = state.product; if (!p || !p.title || state.similarLoading) return;
    state.similarLoading = true; state.similar = []; emit();
    try {
      const q = U.tokens(p.title).slice(0, 5).join(' ');
      state.similar = await Sources.dk.search(q);
    } catch (e) { Log.warn('similar', e.message); }
    state.similarLoading = false; emit();
  }

  const selectedVariant = () => state.chart && state.chart.variants[state.variantIdx] || null;
  function historyPoints() { const v = selectedVariant(); return v ? v.points : []; }
  function inspector() {
    const pts = historyPoints(); const p = state.product || {};
    return Analysis.inspect(pts, { currentPrice: p.price, claimedOld: p.oldPrice });
  }
  function advice() {
    const p = state.product || {}; const pts = historyPoints();
    const hostKey = Extract.matchKnownSite(p.host || '') || '';
    return Analysis.advise({ current: p.price, offers: state.offers, hostKey, st: Analysis.stats(pts), insp: pts.length ? inspector() : null });
  }
  return { state, on, emit, pickCandidate, settings, refreshProduct, loadHistory, runCompare, setManualPrice, loadSimilar, selectedVariant, historyPoints, inspector, advice };
})();


// ---- 11-alerts.js ----
const Alerts = (() => {
  const TICK = 5 * 60e3;
  async function currentPriceFor(p) {
    if (/digikala\.com$/.test(p.host) && p.pid) {
      const d = await Sources.dk.product(p.pid, p.variantId);
      if (d && d.chosen) return { price: d.chosen.price, src: 'digikala-api:variant' };
      return null;
    }
    return null;
  }
  function notify(p, price) {
    const text = `${p.title || p.key}\nقیمت فعلی ${U.fmt(price)} تومان (هدف ${U.fmt(p.target)})`;
    try { if (typeof GM_notification === 'function') { GM_notification({ title: 'Kokam Pro — هشدار قیمت', text, timeout: 15000, onclick: () => window.open(p.url, '_blank') }); return true; } } catch (e) { Log.warn('alerts', e.message); }
    App.state.banner = 'هشدار قیمت: ' + text.replace('\n', ' — '); App.emit(); return false;
  }
  function evaluate(p, price) {
    if (!p.watch || !(p.target > 0) || !(price > 0) || price > p.target) return false;
    const day = 24 * 3600e3;
    if (!p.notifiedAt || price < (p.notifiedPrice || Infinity) || Date.now() - p.notifiedAt > day) { p.notifiedAt = Date.now(); p.notifiedPrice = price; notify(p, price); return true; }
    return false;
  }
  async function checkAll(force = false) {
    const db = Store.get(), a = db.settings.alerts; if (!a.enabled && !force) return { checked: 0, fired: 0 };
    const due = Date.now() - (a.lastRun || 0) >= Math.max(15, a.intervalMin) * 60e3; if (!due && !force) return { checked: 0, fired: 0 };
    a.lastRun = Date.now(); Store.save();
    let checked = 0, fired = 0;
    for (const p of Object.values(db.products).filter(x => x.watch)) {
      try {
        const r = await currentPriceFor(p);
        if (r) {
          checked++;
          Store.recordLocal(p, r.price, r.src);
          const cur = db.settings.low30d[p.key] || { min: Infinity, ts: 0 };
          if (Date.now() - cur.ts > 30 * 24 * 3600e3 || r.price < cur.min) {
            db.settings.low30d[p.key] = { min: Math.min(cur.min === Infinity ? r.price : cur.min, r.price), ts: Date.now() };
            Store.save();
          }
          if (evaluate(p, r.price)) fired++;
        } else if (p.lastPrice) { if (evaluate(p, p.lastPrice)) fired++; }
      } catch (e) { Log.warn('alerts', `${p.key}: ${e.message}`); }
      await U.sleep(1200 + Math.random() * 800);
    }
    Store.save(); Log.info('alerts', `بررسی ${checked} محصول، ${fired} هشدار`); return { checked, fired };
  }
  async function compareAll() {
    const db = Store.get();
    const list = Object.values(db.products).filter(p => p.watch && /digikala\.com$/.test(p.host) && p.pid);
    const out = [];
    for (const p of list) {
      try {
        const d = await Sources.dk.product(p.pid, p.variantId);
        if (d && d.chosen) out.push({ key: p.key, title: p.title, price: d.chosen.price, target: p.target, low30: (db.settings.low30d[p.key] || {}).min || null });
        await U.sleep(1000 + Math.random() * 500);
      } catch (e) { Log.warn('compareAll', p.key + ': ' + e.message); }
    }
    return out;
  }
  let timer = null;
  const start = () => { if (timer) return; timer = setInterval(() => checkAll(false).catch(e => Log.warn('alerts', e.message)), TICK); setTimeout(() => checkAll(false).catch(() => {}), 8000); };
  return { start, checkAll, evaluate, compareAll };
})();


// ---- 12-export.js ----
const Exporter = (() => {
  const q = v => { const s = String(v ?? ''); return /[",\n]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s; };
  function csvFor(key, chartPoints) {
    const p = Store.get().products[key];
    const rows = [['product_key', 'title', 'date_iso', 'price_toman', 'kind', 'source', 'seller', 'warranty', 'marketable']];
    for (const x of (chartPoints || [])) rows.push([key, p?.title || '', U.isoDay(x.t), x.price ?? '', 'store', x.source, x.seller || '', x.warranty || '', x.marketable ? '1' : '0']);
    for (const x of (p?.local || [])) rows.push([key, p?.title || '', new Date(x.t).toISOString(), x.p, 'local', x.src || 'local', '', '', '1']);
    return rows.map(r => r.map(q).join(',')).join('\n');
  }
  const jsonAll = extra => JSON.stringify({ app: 'Kokam Pro 16', exportedAt: new Date().toISOString(), db: Store.get(), ...extra }, null, 2);
  function parseCsv(text) {
    const out = []; const lines = String(text || '').replace(/^\uFEFF/, '').split(/\r?\n/).filter(Boolean); if (!lines.length) return out;
    const head = lines[0].toLowerCase().split(',').map(s => s.trim().replace(/"/g, ''));
    const ci = n => head.indexOf(n), di = ci('date_iso') >= 0 ? ci('date_iso') : ci('date'), pi = ci('price_toman'), si = ci('source'), ki = ci('kind');
    if (di < 0 || pi < 0) throw new Error('ستون‌های date/date_iso و price_toman لازم است');
    for (const ln of lines.slice(1)) {
      const c = ln.split(','); const t = Date.parse(c[di]); const price = Number(U.digits(c[pi]).replace(/\D/g, ''));
      if (!isFinite(t) || !(price > 0)) continue; if (ki >= 0 && c[ki] === 'store') continue;
      out.push({ t, p: price, src: 'imported:' + (c[si] || 'csv') });
    }
    return out;
  }
  function importLocal(key, rows) {
    const p = Store.touchProduct(key); const have = new Set(p.local.map(x => x.t + ':' + x.p)); let n = 0;
    for (const r of rows) if (!have.has(r.t + ':' + r.p)) { p.local.push(r); n++; }
    p.local.sort((a, b) => a.t - b.t); Store.save(); return n;
  }
  function download(name, text, mime) {
    const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob(['\uFEFF' + text], { type: (mime || 'text/csv') + ';charset=utf-8' }));
    a.download = name; document.documentElement.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 500);
  }
  return { csvFor, jsonAll, parseCsv, importLocal, download };
})();
// ---- 13-ui.js ----
const UI = (() => {
  const HOST_ID = 'kokam-pro-host';
  const CSS = `
:host{all:initial;direction:rtl;font-family:Vazirmatn,Tahoma,"Segoe UI",Arial,sans-serif;font-size:13px;line-height:1.55;position:fixed;z-index:2147483646}
*{box-sizing:border-box}
.dark{--bg:#12102a;--panel:#1a1740;--card:#242052;--ink:#eceaff;--mut:#a9a6d6;--acc:#8b5cf6;--acc2:#34d399;--warn:#fbbf24;--bad:#f87171;--line:#38347f;--shadow:0 12px 40px rgba(10,8,40,.55)}
.light{--bg:#f6f5ff;--panel:#fff;--card:#f1efff;--ink:#1f1b3d;--mut:#6b6891;--acc:#6d28d9;--acc2:#047857;--warn:#b45309;--bad:#dc2626;--line:#ddd8f5;--shadow:0 12px 40px rgba(60,40,120,.22)}
.wrap{color:var(--ink)}
#pill{all:unset;cursor:pointer;display:inline-flex;gap:6px;align-items:center;padding:9px 16px;border-radius:999px;background:linear-gradient(135deg,#6d28d9,#4338ca);color:#fff;font-weight:700;box-shadow:var(--shadow);user-select:none;font-family:inherit;font-size:13px}
#pill:hover{filter:brightness(1.1)}
#panel{position:relative;display:none;width:min(390px,calc(100vw - 20px));max-height:min(84vh,680px);flex-direction:column;background:var(--panel);border:1px solid var(--line);border-radius:18px;box-shadow:var(--shadow);overflow:hidden}
#panel.open{display:flex}
#panel.wide{width:min(560px,calc(100vw - 20px))}
header,.hero,.tabs,.foot{flex-shrink:0}
.tb{width:100%;border-collapse:collapse;font-size:12px}.tb td{padding:5px 3px;border-bottom:1px solid var(--line);vertical-align:middle}.tb tr.best td{background:rgba(52,211,153,.08)}.dot{width:8px;height:8px;border-radius:50%;display:inline-block;margin-left:4px}.dot.high{background:var(--acc2)}.dot.medium{background:var(--warn)}.dot.low{background:var(--bad)}
input[type=text]{min-width:0}#q{flex:1}
#rs{position:absolute;right:0;bottom:0;width:18px;height:18px;cursor:nwse-resize;touch-action:none;background:linear-gradient(135deg,transparent 50%,var(--mut) 50%);opacity:.55;border-bottom-right-radius:18px;z-index:5}#rs:hover{opacity:1}
.tabs{position:relative;z-index:2;background:var(--panel)}
.body{min-height:0;overscroll-behavior:contain}
#panel.compact .meta{display:none}#panel.compact .price{font-size:16px;margin:0}#panel.compact .name{-webkit-line-clamp:1;font-size:12px}#panel.compact .hero{padding:6px 14px}
#pill{touch-action:none}header{touch-action:none}
header{cursor:move;padding:12px 14px 10px;background:linear-gradient(135deg,rgba(109,40,217,.35),rgba(67,56,202,.2));border-bottom:1px solid var(--line);position:relative}
.brand{font-weight:800;font-size:15px;letter-spacing:.2px}.brand b{color:var(--acc2)}
.credit{display:flex;gap:6px;flex-wrap:wrap;margin-top:7px}
.cr{all:unset;cursor:pointer;display:inline-flex;align-items:center;gap:5px;padding:3px 10px;border-radius:999px;font-size:11px;border:1px solid var(--line);color:var(--ink);background:var(--card);font-family:inherit;text-decoration:none}
.cr small{color:var(--mut);font-size:10px}.cr:hover{border-color:var(--acc)}
.cr.dev{background:linear-gradient(135deg,#7c3aed,#4f46e5);border-color:transparent;color:#fff;font-weight:800;font-size:12px;padding:4px 12px;box-shadow:0 2px 10px rgba(124,58,237,.45)}
.cr.dev small{color:#e9e5ff}
.x{all:unset;cursor:pointer;position:absolute;left:10px;top:10px;width:26px;height:26px;border-radius:8px;text-align:center;line-height:26px;color:var(--mut);font-size:15px}.x:hover{background:var(--card);color:var(--ink)}
.x2{left:40px}.x3{left:70px}
.hero{padding:10px 14px;border-bottom:1px solid var(--line)}
.name{font-weight:700;font-size:13px;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.price{font-size:24px;font-weight:800;color:var(--acc2);margin:2px 0}.price small{font-size:12px;color:var(--mut);font-weight:400}
.meta{font-size:11px;color:var(--mut)}.meta s{opacity:.8}
.tabs{display:flex;gap:2px;padding:6px 8px;overflow-x:auto;border-bottom:1px solid var(--line);scrollbar-width:none}
.tab{all:unset;cursor:pointer;white-space:nowrap;padding:5px 10px;border-radius:9px;color:var(--mut);font-size:12px;font-family:inherit}
.tab.on{background:var(--acc);color:#fff;font-weight:700}
.body{padding:12px 14px;overflow-y:auto;flex:1}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:10px 12px;margin-bottom:9px}
.row{display:flex;align-items:center;justify-content:space-between;gap:8px}
.btn{all:unset;cursor:pointer;padding:7px 12px;border-radius:10px;background:var(--acc);color:#fff;font-weight:700;font-size:12px;text-align:center;font-family:inherit}
.btn.sec{background:var(--card);color:var(--ink);border:1px solid var(--line)}.btn.bad{background:var(--bad)}.btn[disabled]{opacity:.5;cursor:default}
.btns{display:flex;gap:6px;flex-wrap:wrap;margin:6px 0 10px}
.chip{display:inline-block;padding:1px 8px;border-radius:999px;font-size:10.5px;border:1px solid var(--line);color:var(--mut)}
.chip.good{color:var(--acc2);border-color:var(--acc2)}.chip.warn{color:var(--warn);border-color:var(--warn)}.chip.bad{color:var(--bad);border-color:var(--bad)}
.muted{color:var(--mut);font-size:11.5px}.good{color:var(--acc2)}.warn{color:var(--warn)}.bad{color:var(--bad)}
.offer{display:flex;justify-content:space-between;gap:8px;align-items:center}.offer.best{border-color:var(--acc2);box-shadow:0 0 0 1px var(--acc2) inset}
.offer a{color:var(--acc);text-decoration:none;font-size:11px}
.pv{font-weight:800;font-size:15px;white-space:nowrap}
select,input[type=number],input[type=text]{background:var(--card);color:var(--ink);border:1px solid var(--line);border-radius:8px;padding:5px 8px;font-family:inherit;font-size:12px}
input[type=number]{width:130px}
label.ck{display:flex;gap:6px;align-items:center;margin:5px 0;font-size:12px}
.grid2{display:grid;grid-template-columns:1fr 1fr;gap:8px}.m{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:7px 9px}.m span{display:block;color:var(--mut);font-size:10.5px}.m b{font-size:13px}
.banner{background:rgba(251,191,36,.12);border:1px solid var(--warn);color:var(--warn);border-radius:10px;padding:7px 10px;margin-bottom:9px;font-size:11.5px}
.verdict{border-radius:12px;padding:10px 12px;margin-bottom:9px;font-weight:700;border:1px solid}
.v-confirmed{background:rgba(52,211,153,.1);border-color:var(--acc2);color:var(--acc2)}.v-rise-signal{background:rgba(251,191,36,.1);border-color:var(--warn);color:var(--warn)}.v-insufficient{background:rgba(169,166,214,.08);border-color:var(--line);color:var(--mut)}
ul{margin:4px 0 0;padding:0 16px}li{margin:3px 0}
.log{font-family:ui-monospace,Consolas,monospace;font-size:10.5px;direction:ltr;text-align:left;white-space:pre-wrap;word-break:break-all;color:var(--mut)}.log .e{color:var(--bad)}.log .w{color:var(--warn)}
svg text{font-family:inherit}
.foot{padding:7px 14px;border-top:1px solid var(--line);font-size:10px;color:var(--mut);text-align:center}
`;
  let host, root, S;
  const $ = s => root.querySelector(s);

  const LV = { high: ['اطمینان بالا', 'good'], medium: ['اطمینان متوسط', 'warn'], low: ['مشکوک', 'bad'] };
  const STATUS = { ok: ['فعال', 'good'], loading: ['در حال دریافت…', ''], empty: ['بدون نتیجه', 'warn'], 'no-match': ['تطبیقی پیدا نشد', 'warn'], error: ['خطا', 'bad'], unavailable: ['در دسترس نیست', ''], off: ['خاموش', ''] };

  function chart(storePts, localPts, rangeDays) {
    const W = 340, H = 150, pl = 8, pr = 8, pt = 10, pb = 22;
    const all = [...storePts, ...localPts.map(x => ({ t: x.t, price: x.p }))].filter(p => p.price > 0);
    if (all.length < 2) return '<div class="muted" style="padding:14px 0;text-align:center">نقطهٔ کافی برای رسم نمودار وجود ندارد.</div>';
    const end = Math.max(...all.map(p => p.t)), from = end - rangeDays * U.DAY;
    const sp = storePts.filter(p => p.t >= from && p.price > 0), lp = localPts.filter(p => p.t >= from);
    const vals = [...sp.map(p => p.price), ...lp.map(p => p.p)]; if (vals.length < 2) return '<div class="muted" style="padding:14px 0;text-align:center">در این بازه داده‌ای نیست.</div>';
    const mn = Math.min(...vals), mx = Math.max(...vals), pad = (mx - mn) * 0.08 || mx * 0.05;
    const x = t => pl + (t - from) / (end - from || 1) * (W - pl - pr), y = v => pt + (1 - (v - (mn - pad)) / ((mx + pad) - (mn - pad))) * (H - pt - pb);
    let d = '', prev = null; for (const p of sp) { d += (prev && p.t - prev.t <= 2.5 * U.DAY ? 'L' : 'M') + x(p.t).toFixed(1) + ' ' + y(p.price).toFixed(1) + ' '; prev = p; }
    const dots = lp.map(p => `<circle cx="${x(p.t).toFixed(1)}" cy="${y(p.p).toFixed(1)}" r="2.6" fill="#fbbf24"/>`).join('');
    const minP = sp.length ? sp.reduce((a, b) => b.price < a.price ? b : a) : null;
    return `<svg viewBox="0 0 ${W} ${H}" width="100%" style="direction:ltr"><path d="${d}" fill="none" stroke="#8b5cf6" stroke-width="2" stroke-linejoin="round"/>${dots}
      ${minP ? `<circle cx="${x(minP.t).toFixed(1)}" cy="${y(minP.price).toFixed(1)}" r="4" fill="#34d399"/>` : ''}
      <text x="${pl}" y="${H - 6}" font-size="9.5" fill="#a9a6d6">${U.faDate(from)}</text><text x="${W - pr}" y="${H - 6}" font-size="9.5" fill="#a9a6d6" text-anchor="end">${U.faDate(end)}</text>
      <text x="${W - pr}" y="${pt + 2}" font-size="9.5" fill="#a9a6d6" text-anchor="end">${U.fmt(mx)}</text><text x="${W - pr}" y="${H - pb - 3}" font-size="9.5" fill="#a9a6d6" text-anchor="end">${U.fmt(mn)}</text></svg>`;
  }

  function tabCompare() {
    const p = S.product || {}, srcs = S.sources; let h = '';
    const cd = Net.cooldownLeft();
    if (cd > 0) h += `<div class="banner">محدودیت نرخ دیجی‌کالا فعال است؛ ${U.toFa(cd)} دقیقه دیگر تلاش کنید.</div>`;
    h += `<div class="btns"><button class="btn" data-act="compare" ${S.running ? 'disabled' : ''}>${S.running ? 'در حال مقایسه…' : 'شروع مقایسه'}</button><button class="btn sec" data-act="reread">بازخوانی صفحه</button><button class="btn sec" data-act="manual">ثبت دستی قیمت</button><button class="btn sec" data-act="similar">محصولات مشابه</button></div>`;
    h += `<div class="row" style="margin-bottom:8px;gap:6px"><input type="text" id="q" placeholder="جست‌وجوی دستی در ترب (اختیاری)" value="${U.esc(S.manualQuery || '')}"><button class="btn sec" data-act="manualSearch">جست‌وجو</button></div>`;
    const codes = Match.modelCodes(p.title || '');
    if (codes.length) h += `<div class="btns"><button class="btn sec" data-act="codeSearch">جستجو با کد مدل (${U.esc(codes.join('، '))})</button></div>`;
    const chips = Object.keys(Sources.registry).map(id => { const r = Sources.registry[id], st = srcs[id] || { status: Store.get().settings.sources[id] && r.implemented ? 'idle' : (r.implemented ? 'off' : 'unavailable') }; const [lbl, cl] = STATUS[st.status] || ['آماده', '']; return `<span class="chip ${cl}" title="${U.esc(st.error || st.note || r.note)}">${U.esc(r.label)}: ${lbl}${st.count ? ' · ' + U.toFa(st.count) : ''}</span>`; }).join(' ');
    h += `<div style="margin-bottom:9px">${chips}</div>`;
    const tr = srcs.torob;
    if (tr && tr.status === 'no-match') h += `<div class="card warn"><b>در ترب محصول مطابقی پیدا نشد.</b><div class="muted">عبارت‌های جست‌وجو شده: ${U.toFa((tr.tried || []).length)} — ${U.esc((tr.tried || []).join(' · '))}</div><div class="muted">می‌توانید عبارت دقیق‌تری در کادر بالا وارد و «جست‌وجو» را بزنید.</div></div>`;
    if (tr && tr.candidates && tr.candidates.length > 1) h += `<div class="card"><div class="muted" style="margin-bottom:4px">محصول تطبیق‌یافته در ترب — اگر رنگ/مدل دیگری مدنظر است تغییر دهید</div><select data-sel="cand" style="width:100%">${tr.candidates.map(c => `<option value="${U.esc(c.key)}" ${c.key === tr.chosenKey ? 'selected' : ''}>${U.esc(c.title.slice(0, 60))} · ${U.fmt(c.price)}</option>`).join('')}</select></div>`;
    if (tr && tr.tried && tr.tried.length > 1) h += `<div class="muted" style="margin-bottom:6px">جست‌وجوی چندمرحله‌ای: ${U.toFa(tr.tried.length)} عبارت امتحان شد؛ عبارت موفق: «${U.esc(tr.query)}»</div>`;
    for (const id of Object.keys(srcs)) { const st = srcs[id]; if (st.error) h += `<div class="banner">خطای ${U.esc(Sources.registry[id].label)}: ${U.esc(st.error)} — سایر منابع و موتور اصلی فعال می‌مانند.</div>`; }
    let offers = S.offers.slice();
    if (S.trustedOnly) offers = offers.filter(o => o.matchLevel !== 'low');
    offers.sort((a, b) => S.sort === 'name' ? a.seller.localeCompare(b.seller, 'fa') : S.sort === 'desc' ? b.price - a.price : a.price - b.price);
    if (S.offers.length) {
      h += `<div class="row" style="margin-bottom:6px"><select data-sel="sort"><option value="price" ${S.sort === 'price' ? 'selected' : ''}>ارزان‌ترین</option><option value="desc" ${S.sort === 'desc' ? 'selected' : ''}>گران‌ترین</option><option value="name" ${S.sort === 'name' ? 'selected' : ''}>نام فروشنده</option></select><label class="ck"><input type="checkbox" data-ck="trusted" ${S.trustedOnly ? 'checked' : ''}>فقط تطبیق قابل‌اتکا</label><button class="btn sec" data-act="toggleTable">${S.table ? 'نمای کارتی' : 'نمای جدول'}</button></div>`;
      const a = App.advice();
      h += `<div class="card"><b class="${a.tone === 'good' ? 'good' : a.tone === 'warn' ? 'warn' : ''}">مشاور خرید: ${U.esc(a.headline)}</b><ul>${a.points.map(x => `<li class="${x.k === 'good' ? 'good' : x.k === 'warn' ? 'warn' : ''}">${U.esc(x.text)}</li>`).join('')}</ul><div class="muted" style="margin-top:6px">${a.caveats.map(U.esc).join('<br>')}</div></div>`;
      const bestPrice = Math.min(...S.offers.filter(o => o.matchLevel !== 'low').map(o => o.price));
      const shown = S.showAll ? offers : offers.slice(0, 5);
      if (S.table) {
        h += '<table class="tb">' + shown.map(o => { const diff = p.price ? (o.price - p.price) / p.price * 100 : null; return `<tr class="${o.price === bestPrice && o.matchLevel !== 'low' ? 'best' : ''}"><td><span class="dot ${o.matchLevel}" title="${(LV[o.matchLevel] || [''])[0]}"></span>${U.esc(o.seller)}</td><td><b>${U.fmt(o.price)}</b></td><td class="${diff != null && diff < -0.5 ? 'good' : diff > 0.5 ? 'bad' : 'muted'}">${diff == null ? '' : (diff < 0 ? '−' : diff > 0 ? '+' : '') + U.fmtPct(Math.abs(diff))}</td><td>${o.sellerUrl ? `<a style="color:var(--acc)" href="${U.esc(o.sellerUrl)}" target="_blank" rel="noopener noreferrer">↗</a>` : ''}</td></tr>`; }).join('') + '</table>';
      }
      else for (const o of shown) {
        const diff = p.price ? (o.price - p.price) / p.price * 100 : null, lv = LV[o.matchLevel] || ['', ''];
        const dd = diff == null ? '' : Math.abs(diff) < 0.5 ? '<span class="muted">هم‌قیمت با این صفحه</span>' : diff < 0 ? `<span class="good">${U.fmtPct(-diff)} ارزان‌تر · صرفه‌جویی ${U.fmt(p.price - o.price)}</span>` : `<span class="bad">${U.fmtPct(diff)} گران‌تر</span>`;
        h += `<div class="card offer ${o.price === bestPrice && o.matchLevel !== 'low' ? 'best' : ''}"><div><b>${U.esc(o.seller)}</b> ${o.price === bestPrice && o.matchLevel !== 'low' ? '<span class="chip good">ارزان‌ترین</span>' : ''}<br>${dd}<br><span class="chip ${lv[1]}" title="${U.esc((o.flags || []).join(' | '))}">${lv[0]} · ${U.toFa(Math.round((o.matchConfidence || 0) * 100))}٪</span> <span class="chip">ارسال: نامشخص</span> ${o.flags.some(f => f.startsWith('dedup')) ? '<span class="chip">تکراری‌ها حذف شد</span>' : ''}<div class="muted">منبع: ${U.esc(o.sourceId)} · تطبیق: ${U.toFa(Math.round((o.matchConfidence || 0) * 100))}٪ · ${new Date(o.ts).toLocaleTimeString('fa-IR')}</div></div><div style="text-align:left"><div class="pv">${U.fmt(o.price)} <small class="muted">تومان</small></div>${o.sellerUrl ? `<a href="${U.esc(o.sellerUrl)}" target="_blank" rel="noopener noreferrer">مشاهده فروشنده ↗</a>` : ''}</div></div>`;
      }
      if (offers.length > 5) h += `<div class="btns"><button class="btn sec" data-act="toggleAll">${S.showAll ? 'نمایش کمتر' : 'نمایش همهٔ ' + U.toFa(offers.length) + ' مورد'}</button></div>`;
    } else if (!S.running && Object.keys(srcs).length) h += '<div class="card muted">هیچ فروشندهٔ دیگری با تطبیق قابل‌اتکا یافت نشد. هیچ قیمت حدسی نمایش داده نمی‌شود.</div>';
    for (const id of Object.keys(srcs)) { const nm = srcs[id].nearMiss; if (nm && nm.length) h += `<div class="card muted"><b>نتایج ردشده (مدل متفاوت):</b><ul>${nm.map(n => `<li>${U.esc(n.title)} — ${U.esc(n.reason)}</li>`).join('')}</ul></div>`; }
    if (S.similarLoading) h += '<div class="card muted">در حال دریافت محصولات مشابه…</div>';
    else if (S.similar.length) h += `<div class="card"><b>محصولات مشابه در دیجی‌کالا</b>${S.similar.slice(0, 6).map(x => `<div class="row" style="margin-top:4px"><a href="${U.esc(x.url)}" target="_blank" rel="noopener" style="color:var(--acc);font-size:11px">${U.esc(x.title.slice(0, 50))}</a><b>${U.fmt(x.price)}</b></div>`).join('')}</div>`;
    if (!S.offers.length && !Object.keys(srcs).length) h += '<div class="card muted">برای دریافت قیمت فروشندگان «شروع مقایسه» را بزنید.</div>';
    return h;
  }

  function tabHistory() {
    let h = '';
    if (!S.product || !S.product.id) return '<div class="card muted">تاریخچهٔ رسمی فقط برای صفحات دیجی‌کالا (dkp) در دسترس است. نقاط ثبت‌شدهٔ محلی در واچ‌لیست/خروجی قابل‌مشاهده‌اند.</div>' + localOnly();
    h += `<div class="btns"><button class="btn sec" data-act="reloadHistory">${S.chartLoading ? 'در حال دریافت…' : 'دریافت دوباره'}</button>${[7, 30, 90].map(d => `<button class="btn ${S.range === d ? '' : 'sec'}" data-range="${d}">${U.toFa(d)} روز</button>`).join('')}</div>`;
    if (S.chartError) h += `<div class="banner">${U.esc(S.chartError)}</div>`;
    if (S.chart) {
      const c = S.chart, v = App.selectedVariant();
      if (c.variants.length > 1) h += `<div style="margin-bottom:6px"><select data-sel="variant">${c.variants.map((x, i) => `<option value="${i}" ${i === S.variantIdx ? 'selected' : ''}>${U.esc(x.title || 'واریانت ' + (i + 1))}</option>`).join('')}</select> <span class="chip ${S.variantExact ? 'good' : 'warn'}">${S.variantExact ? 'مطابق رنگ صفحه' : 'رنگ دقیق مشخص نشد'}</span></div>`;
      const pts = v ? v.points : [], st = Analysis.stats(pts), loc = (Store.get().products[S.key] || { local: [] }).local;
      h += `<div class="card">${chart(Analysis.valid(pts), loc, S.range)}<div class="muted">خط بنفش: دادهٔ رسمی دیجی‌کالا · نقطه‌های زرد: ثبت‌شدهٔ محلی افزونه · نقطهٔ سبز: کمینه</div></div>`;
      if (st) h += `<div class="grid2"><div class="m"><span>کمترین قیمت</span><b>${U.fmt(st.min)}</b></div><div class="m"><span>بیشترین قیمت</span><b>${U.fmt(st.max)}</b></div><div class="m"><span>میانه</span><b>${U.fmt(st.median)}</b></div><div class="m"><span>بازهٔ واقعی داده</span><b>${U.toFa(st.span)} روز · ${U.toFa(st.count)} نقطه</b></div></div><div class="muted" style="margin-top:6px">از ${U.isoDay(st.from)} تا ${U.isoDay(st.to)}. ${st.span < 90 ? 'دیجی‌کالا کمتر از ۹۰ روز داده داده است؛ چیزی ساخته یا درون‌یابی نشده.' : ''} روزهای بدون داده در نمودار پیوسته نمی‌شوند.</div>`;
      else h += '<div class="card muted">این واریانت نقطهٔ قابل‌فروش ندارد.</div>';
    } else if (!S.chartError && !S.chartLoading) h += '<div class="card muted">تاریخچه هنوز دریافت نشده.</div>';
    return h;
  }
  const localOnly = () => { const p = Store.get().products[S.key]; if (!p || !p.local.length) return ''; return `<div class="card"><b>نقاط ثبت‌شدهٔ محلی</b>${chart([], p.local, 365)}</div>`; };

  function tabInspector() {
    if (!S.chart) return '<div class="card muted">بازرس تخفیف به تاریخچهٔ رسمی دیجی‌کالا نیاز دارد؛ ابتدا تاریخچه دریافت شود.</div>';
    const r = App.inspector(), T = { confirmed: 'تخفیف تأییدشده با داده کافی', 'rise-signal': 'نشانهٔ افزایش قیمت پیش از تخفیف', insufficient: r.detail === 'no-drop' ? 'تخفیف تأییدشده‌ای دیده نمی‌شود' : 'داده ناکافی برای نتیجه‌گیری' };
    const cf = { high: 'بالا', medium: 'متوسط', low: 'پایین', none: 'ندارد' }[r.confidence];
    let h = `<div class="verdict v-${r.verdict}">${T[r.verdict]}<div class="muted" style="font-weight:400">میزان اطمینان تحلیل: ${cf}</div></div>`;
    const n = r.numbers; if (n && n.baseline) h += `<div class="grid2"><div class="m"><span>قیمت پایه (میانهٔ پیش از ۱۴ روز اخیر)</span><b>${U.fmt(n.baseline)}</b></div><div class="m"><span>قیمت فعلی</span><b>${U.fmt(n.current)}</b></div><div class="m"><span>کاهش واقعی</span><b>${U.fmtPct(n.realDropPct)}</b></div><div class="m"><span>تخفیف ادعایی</span><b>${n.claimedPct == null ? '—' : U.fmtPct(n.claimedPct)}</b></div><div class="m"><span>کمترین دوره</span><b>${U.fmt(n.min)}</b></div><div class="m"><span>بیشترین دوره</span><b>${U.fmt(n.max)}</b></div></div>`;
    if (r.signals.length) h += `<div class="card"><b class="warn">نشانه‌ها</b><ul>${r.signals.map(s => `<li>${U.esc(s.text)}</li>`).join('')}</ul></div>`;
    h += `<div class="card muted"><ul>${r.reasons.map(x => `<li>${U.esc(x)}</li>`).join('')}</ul></div>`;
    return h;
  }

  function tabWatch() {
    const db = Store.get(), cur = S.key && db.products[S.key]; let h = '';
    if (cur) h += `<div class="card"><label class="ck"><input type="checkbox" data-ck="watch" ${cur.watch ? 'checked' : ''}>این محصول را در واچ‌لیست نگه دار</label><div class="row" style="margin-top:6px"><span class="muted">قیمت هدف (تومان)</span><span><input type="number" id="tgt" min="0" value="${cur.target || ''}"> <button class="btn" data-act="setTarget">ثبت</button></span></div></div>`;
    const list = Object.values(db.products).filter(p => p.watch);
    h += list.length ? list.map(p => {
      const first = p.local[0], ch = first && p.lastPrice ? (p.lastPrice - first.p) / first.p * 100 : null;
      const hit = p.target > 0 && p.lastPrice <= p.target;
      const low30 = db.settings.low30d[p.key];
      const lowTxt = low30 ? ` · کمینه ۳۰ روزه: ${U.fmt(low30.min)}` : '';
      return `<div class="card"><div class="row"><b style="font-size:12px">${U.esc((p.title || p.key).slice(0, 60))}</b><button class="btn sec" data-rm="${U.esc(p.key)}">حذف</button></div><div class="row"><span class="pv">${U.fmt(p.lastPrice)}</span><span class="${hit ? 'good' : 'muted'}">${p.target ? 'هدف ' + U.fmt(p.target) + (hit ? ' ✓ رسیده' : '') : 'بدون هدف'}${lowTxt}</span></div><div class="muted">آخرین ثبت: ${p.lastTs ? new Date(p.lastTs).toLocaleString('fa-IR') : '—'} (${U.esc(p.lastSource || '')})${ch != null ? ' · تغییر از اولین ثبت: ' + U.fmtPct(ch) : ''} · <a style="color:var(--acc)" href="${U.esc(p.url)}" target="_blank" rel="noopener">باز کردن</a></div></div>`;
    }).join('') : '<div class="card muted">واچ‌لیست خالی است.</div>';
    h += `<div class="btns"><button class="btn sec" data-act="checkNow">بررسی همین حالا</button><button class="btn sec" data-act="compareAll">مقایسه همه</button></div>`;
    if (S.compareAllResult && S.compareAllResult.length) h += `<div class="card"><b>نتیجه مقایسه همه</b>${S.compareAllResult.map(x => `<div class="row" style="margin-top:4px"><span style="font-size:11px">${U.esc((x.title || x.key).slice(0, 40))}</span><b>${U.fmt(x.price)}</b>${x.low30 ? '<span class="chip">کمینه ۳۰روزه: ' + U.fmt(x.low30) + '</span>' : ''}</div>`).join('')}</div>`;
    h += `<div class="muted">هشدار فقط وقتی بررسی می‌شود که حداقل یک تب با این افزونه باز باشد (محدودیت Userscript). بررسی خودکار فقط برای محصولات دیجی‌کالا با واریانت مشخص قیمت زنده می‌گیرد؛ برای سایر سایت‌ها آخرین قیمتِ ثبت‌شده هنگام بازدید ملاک است.</div>`;
    return h;
  }

  function tabSettings() {
    const st = Store.get().settings; let h = '';
    h += `<div class="card"><label class="ck"><input type="checkbox" data-set="theme">تم روشن</label><label class="ck"><input type="checkbox" data-set="snap" ${st.snap ? 'checked' : ''}>چسبیدن به لبه‌های صفحه هنگام جابه‌جایی</label><label class="ck"><input type="checkbox" data-set="productPageOnly" ${st.productPageOnly ? 'checked' : ''}>نمایش فقط در صفحهٔ محصول</label></div>`;
    h += `<div class="card"><b>منابع قیمت</b>${Object.values(Sources.registry).map(r => `<label class="ck" title="${U.esc(r.note)}"><input type="checkbox" data-src="${r.id}" ${st.sources[r.id] ? 'checked' : ''} ${r.implemented ? '' : 'disabled'}>${U.esc(r.label)} ${r.implemented ? '' : '<span class="chip">پیاده‌سازی نشده</span>'}</label>`).join('')}<div class="muted">میانبر: Alt+Shift+G برای باز/بسته‌کردن پنل · مجوزهای شبکه فقط: ${Net.ALLOWED.join('، ')}</div></div>`;
    h += `<div class="card"><b>ارزش زمان</b><div class="row"><span class="muted">درآمد ساعتی (تومان)</span><input type="number" id="wage" min="0" value="${st.hourlyWage || ''}" style="width:130px"></div><div class="muted">اگر مقدار بدهی، کنار هر قیمت معادل ساعت کار نمایش داده می‌شود.</div></div>`;
    h += `<div class="card"><b>هشدار قیمت</b><label class="ck"><input type="checkbox" data-set="alertsEnabled" ${st.alerts.enabled ? 'checked' : ''}>فعال</label><div class="row"><span class="muted">فاصلهٔ بررسی (دقیقه، حداقل ۱۵)</span><input type="number" id="ival" min="15" value="${st.alerts.intervalMin}" style="width:80px"></div><div class="btns"><button class="btn sec" data-act="testNotify">تست هشدار</button></div></div>`;
    h += `<div class="card"><b>داده‌ها</b><div class="btns"><button class="btn sec" data-act="expCsv">خروجی CSV</button><button class="btn sec" data-act="expJson">خروجی JSON</button><button class="btn sec" data-act="impCsv">ورود CSV</button><button class="btn bad" data-act="clearProd">پاک‌کردن تاریخچهٔ محلی این محصول</button><button class="btn bad" data-act="clearAll">پاک‌کردن همه</button></div><input type="file" id="file" accept=".csv" style="display:none"></div>`;
    return h;
  }

  function tabLog() {
    const legacy = ['ghpro12-host', 'ghafel-pc-btn', 'ghafel-pc-panel', 'ghafel-pro-host'].filter(id => document.getElementById(id));
    let h = legacy.length ? `<div class="banner">نسخه‌های قدیمی هم‌زمان فعال‌اند (${legacy.join('، ')}). در Tampermonkey آن‌ها را غیرفعال کنید تا فقط یک پنل بماند.</div>` : '';
    h += `<div class="card muted">نسخه ۱۶.۰.۰ · محصول: ${U.esc(S.key)} · منبع قیمت: ${U.esc((S.product || {}).priceSource || '—')}${(S.product || {}).priceNote ? ' · ' + U.esc(S.product.priceNote) : ''}</div>`;
    h += `<div class="card"><b>تست اتصال</b><div class="btns"><button class="btn sec" data-act="health">اجرای تست</button></div>${(S.healthResult || []).map(x => `<div class="row" style="margin-top:4px"><span>${U.esc(x.name)}</span><span class="${x.ok ? 'good' : 'bad'}">${x.ok ? 'سالم' : 'خطا'} · ${U.toFa(x.ms)}ms${x.status ? ' · HTTP ' + x.status : ''}</span></div>`).join('')}</div>`;
    h += `<div class="card log">${Log.all().slice(-60).reverse().map(e => `<div class="${e.level === 'error' ? 'e' : e.level === 'warn' ? 'w' : ''}">${new Date(e.t).toLocaleTimeString('en-GB')} [${U.esc(e.scope)}] ${U.esc(e.msg)}</div>`).join('') || 'بدون رویداد'}</div>`;
    return h;
  }

  const TABS = [['compare', 'مقایسه'], ['history', 'تاریخچه'], ['inspect', 'بازرس تخفیف'], ['watch', 'واچ‌لیست'], ['settings', 'تنظیمات'], ['log', 'عیب‌یابی']];
  function render() {
    if (!root) return; const st = Store.get().settings, p = S.product || {};
    const pn = $('#panel'); if (!pn) return;
    pn.classList.toggle('wide', !!st.wide);
    if (st.size) { pn.style.width = st.size.w + 'px'; pn.style.height = st.size.h + 'px'; pn.style.maxHeight = 'none'; } else { pn.style.width = pn.style.height = pn.style.maxHeight = ''; }
    $('.wrap').className = 'wrap ' + (st.theme === 'light' ? 'light' : 'dark');
    $('#name').textContent = p.title || 'نام محصول شناسایی نشد';
    const wage = st.hourlyWage;
    const hw = p.price ? U.hoursOfWork(p.price, wage) : null;
    const delta = p.priceDelta;
    const deltaTxt = delta == null ? '' : Math.abs(delta) < 0.5 ? '' : delta < 0
      ? ` <span class="good">(${U.fmtPct(-delta)} از دیروز)</span>`
      : ` <span class="bad">(+${U.fmtPct(delta)} از دیروز)</span>`;
    $('#price').innerHTML = p.price
      ? `${U.fmt(p.price)} <small>تومان · ${U.esc(p.priceSource || '')}${hw ? ' · معادل ' + U.toFa(hw.toFixed(1)) + ' ساعت کار' : ''}${deltaTxt}</small>`
      : '<span class="warn" style="font-size:16px">قیمت شناسایی نشد — «ثبت دستی قیمت»</span>';
    const dk = S.dk && S.dk.chosen;
    $('#meta').innerHTML = [p.oldPrice ? `قبل از تخفیف: <s>${U.fmt(p.oldPrice)}</s>` : '', p.seller ? 'فروشنده: ' + U.esc(p.seller) : '', p.warranty ? 'گارانتی: ' + U.esc(p.warranty) : '', dk && S.dk.lowest30dOfficial ? 'کمینهٔ ۳۰روزهٔ اعلامی دیجی‌کالا: ' + U.fmt(S.dk.lowest30dOfficial) : ''].filter(Boolean).join(' · ');
    $('#tabs').innerHTML = TABS.map(([k, l]) => `<button class="tab ${S.tab === k ? 'on' : ''}" data-tab="${k}">${l}</button>`).join('');
    const body = { compare: tabCompare, history: tabHistory, inspect: tabInspector, watch: tabWatch, settings: tabSettings, log: tabLog }[S.tab]();
    const keep = $('#body').scrollTop;
    $('#body').innerHTML = (S.banner ? `<div class="banner">${U.esc(S.banner)}</div>` : '') + body;
    $('#body').scrollTop = keep;
    const th = $('[data-set="theme"]'); if (th) th.checked = st.theme === 'light';
  }

  function applyPos() {
    const pos = Store.get().settings.pos || { right: 16, bottom: 16 };
    const vw = innerWidth, vh = innerHeight; const r = host.getBoundingClientRect();
    let { left, top } = pos.left != null ? pos : { left: vw - (r.width || 150) - pos.right, top: vh - (r.height || 40) - pos.bottom };
    left = Math.min(Math.max(4, left), Math.max(4, vw - (r.width || 150) - 4)); top = Math.min(Math.max(4, top), Math.max(4, vh - (r.height || 40) - 4));
    host.style.left = left + 'px'; host.style.top = top + 'px'; host.style.right = 'auto'; host.style.bottom = 'auto';
  }
  function setOpen(o) {
    const st = Store.get().settings; st.open = o; Store.save();
    $('#panel').classList.toggle('open', o); $('#pill').style.display = o ? 'none' : 'inline-flex';
    if (o) { App.refreshProduct(); } requestAnimationFrame(applyPos);
  }

  function snapToEdges() {
    if (!Store.get().settings.snap) return; const r = host.getBoundingClientRect(), M = 8, T = 24, vw = innerWidth, vh = innerHeight;
    let l = r.left, t = r.top;
    if (l < T) l = M; else if (vw - r.right < T) l = vw - r.width - M;
    if (t < T) t = M; else if (vh - r.bottom < T) t = vh - r.height - M;
    host.style.left = Math.max(0, l) + 'px'; host.style.top = Math.max(0, t) + 'px';
  }
  function bind() {
    const hdr = $('header'), pill = $('#pill');
    function makeDraggable(el, { ignore, onTap }) {
      let drag = null;
      el.addEventListener('pointerdown', e => { if (ignore && e.target.closest(ignore)) return; const r = host.getBoundingClientRect(); drag = { dx: e.clientX - r.left, dy: e.clientY - r.top, x0: e.clientX, y0: e.clientY, moved: false }; try { el.setPointerCapture(e.pointerId); } catch {} });
      el.addEventListener('pointermove', e => {
        if (!drag) return; if (!drag.moved && Math.hypot(e.clientX - drag.x0, e.clientY - drag.y0) < 5) return; drag.moved = true;
        const r = host.getBoundingClientRect(), w = r.width || 150, h = r.height || 40;
        host.style.left = Math.min(Math.max(0, e.clientX - drag.dx), Math.max(0, innerWidth - w)) + 'px'; host.style.top = Math.min(Math.max(0, e.clientY - drag.dy), Math.max(0, innerHeight - h)) + 'px'; host.style.right = host.style.bottom = 'auto';
      });
      el.addEventListener('pointerup', () => {
        if (!drag) return; const d = drag; drag = null;
        if (d.moved) { snapToEdges(); const r = host.getBoundingClientRect(); Store.get().settings.pos = { left: r.left, top: r.top }; Store.save(); } else if (onTap) onTap();
      });
      el.addEventListener('pointercancel', () => { drag = null; });
    }
    makeDraggable(hdr, { ignore: '.x' }); makeDraggable(pill, { onTap: () => setOpen(true) });
    $('#wide').onclick = () => { const st = Store.get().settings; st.wide = !st.wide; st.size = null; Store.save(); render(); requestAnimationFrame(applyPos); };
    const rs = $('#rs'); let rz = null;
    rs.addEventListener('pointerdown', e => { e.stopPropagation(); const r = $('#panel').getBoundingClientRect(); rz = { l: r.left, t: r.top }; try { rs.setPointerCapture(e.pointerId); } catch {} });
    rs.addEventListener('pointermove', e => { if (!rz) return; const w = Math.min(Math.max(320, e.clientX - rz.l), innerWidth - rz.l - 4), h = Math.min(Math.max(300, e.clientY - rz.t), innerHeight - rz.t - 4); const st = Store.get().settings; st.size = { w: Math.round(w), h: Math.round(h) }; const pn = $('#panel'); pn.style.width = st.size.w + 'px'; pn.style.height = st.size.h + 'px'; pn.style.maxHeight = 'none'; });
    rs.addEventListener('pointerup', () => { if (rz) { rz = null; Store.save(); } });
    rs.addEventListener('dblclick', () => { Store.get().settings.size = null; Store.save(); render(); });
    $('#body').addEventListener('scroll', () => { const t = $('#body').scrollTop, pn = $('#panel'); if (t > 60) pn.classList.add('compact'); else if (t < 8) pn.classList.remove('compact'); });
    $('#min').onclick = () => setOpen(false); $('#close').onclick = () => { host.style.display = 'none'; };
    root.addEventListener('click', async e => {
      const t = e.target.closest('[data-tab],[data-act],[data-range],[data-rm]'); if (!t) return; const db = Store.get();
      if (t.dataset.tab) { S.tab = t.dataset.tab; db.settings.tab = S.tab; Store.save(); if (S.tab === 'history' && !S.chart && !S.chartLoading) App.loadHistory(); return render(); }
      if (t.dataset.range) { S.range = +t.dataset.range; return render(); }
      if (t.dataset.rm) { const p = db.products[t.dataset.rm]; if (p) p.watch = false; Store.save(); return render(); }
      const a = t.dataset.act;
      if (a === 'compare') App.runCompare();
      else if (a === 'toggleTable') { S.table = !S.table; db.settings.table = S.table; Store.save(); render(); }
      else if (a === 'manualSearch') { S.manualQuery = ($('#q').value || '').trim(); App.runCompare(S.manualQuery ? { query: S.manualQuery } : {}); }
      else if (a === 'codeSearch') { const codes = Match.modelCodes((S.product || {}).title || ''); if (codes.length) { S.manualQuery = codes.join(' '); App.runCompare({ query: S.manualQuery }); } }
      else if (a === 'toggleAll') { S.showAll = !S.showAll; render(); }
      else if (a === 'reread') App.refreshProduct();
      else if (a === 'similar') App.loadSimilar();
      else if (a === 'manual') { const v = Number(U.digits(prompt('قیمت فعلی محصول (تومان):', '') || '').replace(/\D/g, '')); if (v > 0) App.setManualPrice(v); }
      else if (a === 'reloadHistory') App.loadHistory();
      else if (a === 'setTarget') { const v = Number(U.digits($('#tgt').value).replace(/\D/g, '')); const p = Store.touchProduct(S.key); p.target = v > 0 ? v : null; if (v > 0) p.watch = true; Store.save(); render(); }
      else if (a === 'checkNow') { const r = await Alerts.checkAll(true); S.banner = `بررسی انجام شد: ${U.toFa(r.checked)} محصول، ${U.toFa(r.fired)} هشدار`; render(); }
      else if (a === 'compareAll') { S.compareAllResult = await Alerts.compareAll(); render(); }
      else if (a === 'testNotify') {
        try {
          if (typeof GM_notification === 'function') GM_notification({ title: 'Kokam Pro — تست', text: 'اگر این را می‌بینید، هشدار درست کار می‌کند.', timeout: 8000 });
          else S.banner = 'GM_notification در دسترس نیست؛ هشدار به صورت بنر نمایش داده می‌شود.';
        } catch (err) { S.banner = 'خطای هشدار: ' + err.message; }
        render();
      }
      else if (a === 'health') { S.healthResult = await Net.health(); render(); }
      else if (a === 'expCsv') Exporter.download(`kokam-${S.key.replace(/[^\w.-]+/g, '_')}.csv`, Exporter.csvFor(S.key, Analysis.valid(App.historyPoints())));
      else if (a === 'expJson') Exporter.download('kokam-pro16-export.json', Exporter.jsonAll({ chart: S.chart }), 'application/json');
      else if (a === 'impCsv') $('#file').click();
      else if (a === 'clearProd') { if (confirm('تاریخچهٔ محلی این محصول پاک شود؟')) { Store.touchProduct(S.key).local = []; Store.save(); render(); } }
      else if (a === 'clearAll') { if (confirm('همهٔ داده‌ها و تنظیمات افزونه پاک شود؟')) { Store.reset(); render(); } }
    });
    root.addEventListener('input', e => {
      if (e.target.id === 'q') S.manualQuery = e.target.value;
      else if (e.target.id === 'wage') { const st = Store.get().settings; st.hourlyWage = Math.max(0, Number(U.digits(e.target.value)) || 0); Store.save(); }
    });
    root.addEventListener('keydown', e => { if (e.target.id === 'q' && e.key === 'Enter') { e.preventDefault(); S.manualQuery = e.target.value.trim(); App.runCompare(S.manualQuery ? { query: S.manualQuery } : {}); } });
    root.addEventListener('change', e => {
      const t = e.target, st = Store.get().settings;
      if (t.dataset.sel === 'cand') { App.pickCandidate(t.value); return; }
      else if (t.dataset.sel === 'sort') S.sort = t.value; else if (t.dataset.sel === 'variant') S.variantIdx = +t.value;
      else if (t.dataset.ck === 'trusted') S.trustedOnly = t.checked;
      else if (t.dataset.ck === 'watch') { Store.touchProduct(S.key).watch = t.checked; Store.save(); }
      else if (t.dataset.set === 'theme') { st.theme = t.checked ? 'light' : 'dark'; Store.save(); }
      else if (t.dataset.set === 'snap') { st.snap = t.checked; Store.save(); }
      else if (t.dataset.set === 'productPageOnly') { st.productPageOnly = t.checked; Store.save(); }
      else if (t.dataset.set === 'alertsEnabled') { st.alerts.enabled = t.checked; Store.save(); }
      else if (t.dataset.src) { st.sources[t.dataset.src] = t.checked; Store.save(); }
      else if (t.id === 'ival') { st.alerts.intervalMin = Math.max(15, Number(U.digits(t.value)) || 60); Store.save(); }
      else if (t.id === 'file' && t.files[0]) { t.files[0].text().then(tx => { try { const n = Exporter.importLocal(S.key, Exporter.parseCsv(tx)); S.banner = `${U.toFa(n)} نقطه وارد شد (به‌عنوان دادهٔ محلی)`; } catch (er) { S.banner = 'ورود CSV ناموفق: ' + er.message; } render(); }); return; }
      render();
    });
  }

  function mount() {
    if (document.getElementById(HOST_ID)) return;
    S = App.state; S.tab = Store.get().settings.tab || 'compare'; S.table = !!Store.get().settings.table; host = document.createElement('div'); host.id = HOST_ID; document.documentElement.appendChild(host);
    root = host.attachShadow({ mode: 'open' });
    root.innerHTML = `<style>${CSS}</style><div class="wrap dark"><button id="pill" title="Kokam Pro — بکشید تا جابه‌جا شود (Alt+Shift+G)">⚡ کوکام PRO</button>
      <section id="panel"><header><div class="brand">KOKAM <b>PRO 16</b></div><div class="credit"><a class="cr dev" href="https://t.me/R0oo0t" target="_blank" rel="noopener noreferrer" title="Creator"><small>سازنده · Created by</small> حامد ↗</a></div><button class="x x3" id="wide" title="عریض/باریک">⇔</button><button class="x x2" id="min" title="جمع‌کردن">–</button><button class="x" id="close" title="بستن">✕</button></header>
      <div class="hero"><div class="name" id="name"></div><div class="price" id="price"></div><div class="meta" id="meta"></div></div>
      <nav class="tabs" id="tabs"></nav><div class="body" id="body"></div><div id="rs" title="تغییر اندازه (دابل‌کلیک: بازنشانی)"></div><div class="foot">Kokam Pro 16 · ساختهٔ حامد (https://t.me/R0oo0t) · هیچ داده‌ای بدون منبع و زمان نمایش داده نمی‌شود</div></section></div>`;
    bind(); App.on(render); render(); requestAnimationFrame(applyPos);
    addEventListener('resize', applyPos);
    if (Store.get().settings.open) setOpen(true);
  }
  const toggle = () => { if (!host) return false; setOpen(!$('#panel').classList.contains('open')); return true; };
  const unmount = () => { const h = document.getElementById(HOST_ID); if (h) h.remove(); host = root = null; };
  return { mount, unmount, render, setOpen, toggle, HOST_ID };
})();


// ---- 99-main.js ----
const Main = (() => {
  function init() {
    if (window.top !== window.self) return;
    if (window.__KOKAM_PRO__) return; window.__KOKAM_PRO__ = true;
    Store.load();
    document.addEventListener('keydown', e => { if (e.altKey && e.shiftKey && e.code === 'KeyG') { e.preventDefault(); UI.toggle(); } });
    const isDk = /(^|\.)digikala\.com$/.test(location.hostname);
    if (isDk) Alerts.start();
    let lastHref = location.href;
    const check = () => {
      const should = !Store.get().settings.productPageOnly || Extract.looksLikeProductPage();
      const mounted = !!document.getElementById(UI.HOST_ID);
      if (should && !mounted) { UI.mount(); App.refreshProduct(); }
      if (!should && mounted) UI.unmount();
    };
    const onUrlChange = () => {
      if (location.href === lastHref) return;
      lastHref = location.href;
      const should = !Store.get().settings.productPageOnly || Extract.looksLikeProductPage();
      if (should) {
        U.waitForElement('h1').then(el => { if (el) App.refreshProduct(); });
        setTimeout(() => App.refreshProduct(), 5000);
      } else { check(); }
    };
    const navObs = new MutationObserver(() => onUrlChange());
    navObs.observe(document.documentElement, { childList: true, subtree: true });
    addEventListener('beforeunload', () => { try { navObs.disconnect(); } catch {} });
    setTimeout(() => { try { check(); } catch (e) { Log.error('main', e.message); } }, 600);
    Log.info('main', 'Kokam Pro 16 آماده شد');
  }
  return { init };
})();


Main.init();
})();
