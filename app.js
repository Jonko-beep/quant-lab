/* Quant Lab: data loading, Monte Carlo, Black-Scholes, canvas charts. No dependencies. */
(function () {
  'use strict';

  /* ================= Math ================= */
  var QL = {};

  QL.normPdf = function (x) { return Math.exp(-0.5 * x * x) / Math.sqrt(2 * Math.PI); };

  // Abramowitz & Stegun 26.2.17, absolute error < 7.5e-8
  QL.normCdf = function (x) {
    var t = 1 / (1 + 0.2316419 * Math.abs(x));
    var p = QL.normPdf(x) * t * (0.319381530 + t * (-0.356563782 + t * (1.781477937 + t * (-1.821255978 + t * 1.330274429))));
    return x >= 0 ? 1 - p : p;
  };

  // European option, no dividends. T in years, r and sigma as decimals.
  QL.bs = function (type, S, K, T, r, sigma) {
    var call = type === 'call';
    if (!(T > 0) || !(sigma > 0)) {
      var intr = Math.max(call ? S - K : K - S, 0);
      return { price: intr, delta: call ? (S > K ? 1 : 0) : (S < K ? -1 : 0), gamma: 0, vega: 0, theta: 0, rho: 0, pItm: intr > 0 ? 1 : 0 };
    }
    var sq = Math.sqrt(T);
    var d1 = (Math.log(S / K) + (r + 0.5 * sigma * sigma) * T) / (sigma * sq);
    var d2 = d1 - sigma * sq;
    var disc = Math.exp(-r * T);
    var pdf = QL.normPdf(d1);
    var out = { d1: d1, d2: d2, gamma: pdf / (S * sigma * sq), vega: S * pdf * sq / 100 };
    if (call) {
      out.price = S * QL.normCdf(d1) - K * disc * QL.normCdf(d2);
      out.delta = QL.normCdf(d1);
      out.theta = (-S * pdf * sigma / (2 * sq) - r * K * disc * QL.normCdf(d2)) / 365;
      out.rho = K * T * disc * QL.normCdf(d2) / 100;
      out.pItm = QL.normCdf(d2);
    } else {
      out.price = K * disc * QL.normCdf(-d2) - S * QL.normCdf(-d1);
      out.delta = QL.normCdf(d1) - 1;
      out.theta = (-S * pdf * sigma / (2 * sq) + r * K * disc * QL.normCdf(-d2)) / 365;
      out.rho = -K * T * disc * QL.normCdf(-d2) / 100;
      out.pItm = QL.normCdf(-d2);
    }
    return out;
  };

  // Bisection on volatility. Returns null when the price is outside no-arbitrage bounds.
  QL.impliedVol = function (type, price, S, K, T, r) {
    if (!(price > 0) || !(T > 0)) return null;
    var disc = Math.exp(-r * T);
    var lower = Math.max(type === 'call' ? S - K * disc : K * disc - S, 0);
    var upper = type === 'call' ? S : K * disc;
    if (price <= lower + 1e-9 || price >= upper) return null;
    var lo = 1e-4, hi = 6;
    if (QL.bs(type, S, K, T, r, hi).price < price) return null;
    for (var i = 0; i < 80; i++) {
      var mid = 0.5 * (lo + hi);
      if (QL.bs(type, S, K, T, r, mid).price > price) hi = mid; else lo = mid;
    }
    return 0.5 * (lo + hi);
  };

  QL.logReturns = function (c) {
    var r = [];
    for (var i = 1; i < c.length; i++) r.push(Math.log(c[i] / c[i - 1]));
    return r;
  };
  QL.mean = function (a) { var s = 0; for (var i = 0; i < a.length; i++) s += a[i]; return a.length ? s / a.length : NaN; };
  QL.stdev = function (a) {
    if (a.length < 2) return NaN;
    var m = QL.mean(a), s = 0;
    for (var i = 0; i < a.length; i++) s += (a[i] - m) * (a[i] - m);
    return Math.sqrt(s / (a.length - 1));
  };
  QL.realizedVol = function (closes, n, ann) {
    var r = QL.logReturns(closes);
    if (r.length < 2) return NaN;
    return QL.stdev(r.slice(-Math.min(n, r.length))) * Math.sqrt(ann);
  };
  QL.maxDrawdown = function (c) {
    var peak = c[0], mdd = 0;
    for (var i = 1; i < c.length; i++) {
      if (c[i] > peak) peak = c[i];
      var dd = c[i] / peak - 1;
      if (dd < mdd) mdd = dd;
    }
    return mdd;
  };
  QL.sma = function (c, n) {
    var out = new Array(c.length).fill(null), s = 0;
    for (var i = 0; i < c.length; i++) {
      s += c[i];
      if (i >= n) s -= c[i - n];
      if (i >= n - 1) out[i] = s / n;
    }
    return out;
  };
  QL.quantile = function (sorted, q) {
    var n = sorted.length;
    if (!n) return NaN;
    var pos = (n - 1) * q, lo = Math.floor(pos), hi = Math.min(lo + 1, n - 1);
    return sorted[lo] + (sorted[hi] - sorted[lo]) * (pos - lo);
  };

  QL.mulberry32 = function (seed) {
    var a = seed >>> 0;
    return function () {
      a = (a + 0x6D2B79F5) >>> 0;
      var t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  };
  QL.gaussian = function (rng) {
    var spare = null;
    return function () {
      if (spare !== null) { var s = spare; spare = null; return s; }
      var u = 0, v = 0;
      while (u === 0) u = rng();
      v = rng();
      var m = Math.sqrt(-2 * Math.log(u));
      spare = m * Math.sin(2 * Math.PI * v);
      return m * Math.cos(2 * Math.PI * v);
    };
  };

  // GBM: S(t+dt) = S(t) * exp((mu - sigma^2/2) dt + sigma sqrt(dt) Z)
  QL.simulate = function (o) {
    var n = o.paths, steps = o.days, dt = 1 / o.ann;
    var gauss = QL.gaussian(o.rng || Math.random);
    var a = (o.mu - 0.5 * o.sigma * o.sigma) * dt, b = o.sigma * Math.sqrt(dt);
    var cols = steps + 1;
    var data = new Float32Array(n * cols);
    for (var p = 0; p < n; p++) {
      var s = o.s0, base = p * cols;
      data[base] = s;
      for (var t = 1; t <= steps; t++) {
        s *= Math.exp(a + b * gauss());
        data[base + t] = s;
      }
    }
    var qs = [0.05, 0.25, 0.5, 0.75, 0.95];
    var pct = qs.map(function () { return new Float32Array(cols); });
    var col = new Float32Array(n);
    for (var t2 = 0; t2 <= steps; t2++) {
      for (var p2 = 0; p2 < n; p2++) col[p2] = data[p2 * cols + t2];
      col.sort();
      for (var k = 0; k < qs.length; k++) pct[k][t2] = QL.quantile(col, qs[k]);
    }
    var terminal = Float32Array.from(col); // sorted terminal prices
    return { data: data, n: n, steps: steps, cols: cols, pct: pct, terminal: terminal, s0: o.s0 };
  };

  QL.simStats = function (sim, target) {
    var t = sim.terminal, n = t.length, s0 = sim.s0, sum = 0, above = 0;
    for (var i = 0; i < n; i++) { sum += t[i]; if (t[i] > target) above++; }
    var q05 = QL.quantile(t, 0.05);
    var tailN = Math.max(1, Math.floor(n * 0.05)), tail = 0;
    for (var j = 0; j < tailN; j++) tail += t[j];
    return {
      median: QL.quantile(t, 0.5), p5: q05, p95: QL.quantile(t, 0.95),
      probAbove: above / n, expRet: sum / n / s0 - 1,
      var95: q05 / s0 - 1, cvar95: tail / tailN / s0 - 1
    };
  };

  QL.niceStep = function (raw) {
    if (!(raw > 0)) return 1;
    var mag = Math.pow(10, Math.floor(Math.log10(raw))), f = raw / mag;
    var s = f < 1.5 ? 1 : f < 2.25 ? 2 : f < 3.5 ? 2.5 : f < 7.5 ? 5 : 10;
    return s * mag;
  };
  QL.ticks = function (lo, hi, count) {
    var step = QL.niceStep((hi - lo) / Math.max(count, 1));
    var out = [];
    for (var v = Math.ceil(lo / step) * step; v <= hi + step * 1e-9; v += step) out.push(Math.abs(v) < step * 1e-9 ? 0 : v);
    return out;
  };

  // Parses pasted text: one close per line, or CSV with date/close columns.
  QL.parsePasted = function (text) {
    var lines = String(text).split(/\r?\n/).map(function (l) { return l.trim(); }).filter(Boolean);
    if (!lines.length) return { closes: [], dates: [] };
    var split = function (l) { return l.split(/[,;\t]/).map(function (c) { return c.trim().replace(/^"|"$/g, ''); }); };
    var head = split(lines[0]);
    var closeIdx = -1, dateIdx = -1, start = 0;
    var hasHeader = head.some(function (c) { return /[a-df-z]/i.test(c) && isNaN(Date.parse(c)); });
    if (hasHeader) {
      start = 1;
      head.forEach(function (c, i) {
        var k = c.toLowerCase();
        if (k === 'close' || (closeIdx < 0 && /^(adj[ _]?close|price|last)$/.test(k))) closeIdx = i;
        if (dateIdx < 0 && /^(date|datetime|time|timestamp)$/.test(k)) dateIdx = i;
      });
    }
    var closes = [], dates = [];
    for (var i = start; i < lines.length; i++) {
      var cells = split(lines[i]);
      var ci = closeIdx >= 0 ? closeIdx : cells.length - 1;
      var di = dateIdx >= 0 ? dateIdx : (cells.length > 1 ? 0 : -1);
      var v = parseFloat(String(cells[ci]).replace(/[$\s]/g, ''));
      if (!(v > 0)) continue;
      closes.push(v);
      var d = di >= 0 ? cells[di] : '';
      var ts = d ? Date.parse(d) : NaN;
      dates.push(isNaN(ts) ? null : new Date(ts).toISOString().slice(0, 10));
    }
    var dated = dates.every(Boolean);
    if (dated && dates.length > 1 && dates[0] > dates[dates.length - 1]) { closes.reverse(); dates.reverse(); }
    return { closes: closes, dates: dated ? dates : null };
  };

  if (typeof module !== 'undefined' && module.exports) module.exports = QL;
  if (typeof document === 'undefined') return;

  /* ================= App ================= */
  var $ = function (id) { return document.getElementById(id); };
  var root = document.documentElement;
  var KEY_STORE = 'quantlab.twelvedata.key';
  var CACHE_MS = 5 * 60 * 1000;
  var cache = {};
  var state = { symbol: 'NVDA', data: null, sim: null, optType: 'call', mode: 'sample' };

  var store = {
    get: function (k) { try { return localStorage.getItem(k); } catch (e) { return null; } },
    set: function (k, v) { try { localStorage.setItem(k, v); } catch (e) {} },
    del: function (k) { try { localStorage.removeItem(k); } catch (e) {} }
  };
  var memKey = null;
  function getKey() { return memKey || store.get(KEY_STORE) || ''; }

  /* ---------- formatting ---------- */
  function fmtPrice(v) {
    if (!isFinite(v)) return '—';
    var d = (Math.abs(v) >= 1 || Math.abs(v) < 5e-5) ? 2 : 4;
    return v.toLocaleString('en-US', { minimumFractionDigits: d, maximumFractionDigits: d });
  }
  function fmtPct(v, signed, d) {
    if (!isFinite(v)) return '—';
    var s = (v * 100).toFixed(d == null ? 1 : d) + '%';
    return signed && v > 0 ? '+' + s : s.replace('-', '−');
  }
  function fmtAxis(v, step) {
    var d = step >= 1 ? 0 : step >= 0.1 ? 1 : step >= 0.01 ? 2 : 4;
    return v.toLocaleString('en-US', { minimumFractionDigits: d, maximumFractionDigits: d });
  }
  var MONTHS = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];
  function fmtDate(iso) {
    if (!iso) return '';
    var p = iso.slice(0, 10).split('-');
    return MONTHS[+p[1] - 1] + ' ' + (+p[2]) + ', ' + p[0];
  }
  function num(id) { var v = parseFloat($(id).value); return isFinite(v) ? v : NaN; }
  function setNum(id, v, d) { $(id).value = isFinite(v) ? (+v.toFixed(d == null ? 2 : d)) : ''; }

  var toastTimer;
  function toast(msg) {
    var t = $('toast');
    t.textContent = msg; t.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { t.hidden = true; }, 6000);
  }

  /* ---------- data sources ---------- */
  function hashStr(s) { var h = 2166136261; for (var i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); } return h >>> 0; }
  var SAMPLE_VOL = { NVDA: 0.45, AAPL: 0.25, TSLA: 0.6, SPY: 0.15, BTCUSD: 0.55 };

  function businessDaysBack(n) {
    var out = [], d = new Date();
    while (out.length < n) {
      var wd = d.getDay();
      if (wd !== 0 && wd !== 6) out.push(d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0'));
      d.setDate(d.getDate() - 1);
    }
    return out.reverse();
  }

  function sampleData(sym) {
    var rng = QL.mulberry32(hashStr(sym)), g = QL.gaussian(rng);
    var vol = SAMPLE_VOL[sym] || 0.2 + rng() * 0.35;
    var mu = 0.04 + rng() * 0.16, n = 253, dt = 1 / 252;
    var c = [100];
    for (var i = 1; i < n; i++) c.push(c[i - 1] * Math.exp((mu - 0.5 * vol * vol) * dt + vol * Math.sqrt(dt) * g()));
    var k = 100 / c[n - 1];
    c = c.map(function (v) { return v * k; });
    return { symbol: sym, name: 'Simulated sample series, indexed to 100', source: 'sample', closes: c, dates: businessDaysBack(n), ann: 252, asof: 'Sample data, not real prices' };
  }

  function tdSymbol(sym) {
    var m = /^([A-Z]{2,6})(USD|USDT|EUR)$/.exec(sym);
    return (m && sym.indexOf('/') < 0 && sym.length >= 6) ? m[1] + '/' + m[2] : sym;
  }

  function fetchJson(url) {
    return fetch(url).then(function (r) { return r.json(); }, function () {
      throw new Error('This page could not reach Twelve Data. Hosted previews block outside requests; open the downloaded files or your own deployment for live prices.');
    });
  }

  function liveData(sym) {
    var key = getKey(), tds = tdSymbol(sym), crypto = tds.indexOf('/') > 0;
    var hit = cache[sym];
    if (hit && Date.now() - hit.t < CACHE_MS) return Promise.resolve(hit.d);
    var base = 'https://api.twelvedata.com/', q = 'symbol=' + encodeURIComponent(tds) + '&apikey=' + encodeURIComponent(key);
    var series = fetchJson(base + 'time_series?interval=1day&outputsize=' + (crypto ? 366 : 253) + '&' + q);
    var quote = fetchJson(base + 'quote?' + q).catch(function () { return null; });
    return Promise.all([series, quote]).then(function (res) {
      var ts = res[0], qt = res[1];
      if (!ts || ts.status === 'error' || !ts.values) throw new Error((ts && ts.message) || 'Twelve Data returned no history for ' + sym + '.');
      var rows = ts.values.slice().sort(function (a, b) { return a.datetime < b.datetime ? -1 : 1; });
      var closes = [], dates = [];
      rows.forEach(function (r) { var v = parseFloat(r.close); if (v > 0) { closes.push(v); dates.push(r.datetime.slice(0, 10)); } });
      if (closes.length < 30) throw new Error('Not enough history for ' + sym + ' (' + closes.length + ' daily bars).');
      var name = (qt && qt.name) || (ts.meta && ts.meta.symbol) || sym;
      var cur = (ts.meta && ts.meta.currency) || (qt && qt.currency) || '';
      var d = {
        symbol: sym, name: name, source: 'live', closes: closes, dates: dates, ann: crypto ? 365 : 252,
        asof: 'Daily close, ' + fmtDate(dates[dates.length - 1]) + (cur ? ' · ' + cur : '') + ' · Twelve Data'
      };
      cache[sym] = { t: Date.now(), d: d };
      return d;
    });
  }

  function loadSymbol(sym) {
    sym = String(sym || '').trim().toUpperCase().replace(/[^A-Z0-9./-]/g, '');
    if (!sym) return;
    if (state.mode === 'pasted') state.mode = getKey() ? 'live' : 'sample';
    state.symbol = sym;
    $('ticker-input').value = sym;
    document.querySelectorAll('.chips .chip').forEach(function (c) { c.classList.toggle('is-active', c.dataset.sym === sym); });
    if (state.mode === 'live' && getKey()) {
      setStatus('loading');
      $('q-symbol').textContent = sym;
      liveData(sym).then(applyData).catch(function (e) {
        toast(e.message + ' Showing sample data instead.');
        applyData(sampleData(sym), e.message);
      });
    } else {
      applyData(sampleData(sym));
    }
  }

  function setStatus(s) { var el = $('q-status'); el.textContent = s; el.dataset.state = s; }

  /* ---------- apply data to the page ---------- */
  function applyData(d, liveError) {
    state.data = d;
    var c = d.closes, last = c[c.length - 1], prev = c[c.length - 2];
    var year = c.slice(-Math.min(c.length, d.ann + 1));
    $('q-symbol').textContent = d.symbol;
    setStatus(d.source);
    $('q-name').textContent = d.name;
    $('q-price').textContent = fmtPrice(last);
    var chg = last - prev, chgEl = $('q-change');
    chgEl.textContent = (chg >= 0 ? '+' : '−') + fmtPrice(Math.abs(chg)) + ' (' + fmtPct(chg / prev, true, 2) + ')';
    chgEl.className = 'price-change num ' + (chg >= 0 ? 'up' : 'down');
    $('q-asof').textContent = d.asof;

    var v20 = QL.realizedVol(c, 20, d.ann), v60 = QL.realizedVol(c, 60, d.ann), v1y = QL.realizedVol(year, year.length, d.ann);
    $('k-vol20').textContent = fmtPct(v20);
    $('k-vol60').textContent = fmtPct(v60);
    $('k-vol1y').textContent = fmtPct(v1y);
    var ret = last / year[0] - 1, retEl = $('k-ret');
    retEl.textContent = fmtPct(ret, true);
    retEl.className = 'kpi-value num ' + (ret >= 0 ? 'up' : 'down');
    $('k-mdd').textContent = fmtPct(QL.maxDrawdown(year));
    var lo = Math.min.apply(null, year), hi = Math.max.apply(null, year);
    var pos = hi > lo ? (last - lo) / (hi - lo) * 100 : 50;
    $('k-low').textContent = fmtPrice(lo); $('k-high').textContent = fmtPrice(hi);
    $('k-range-fill').style.width = pos + '%'; $('k-range-marker').style.left = pos + '%';

    // drift preset values
    var rets = QL.logReturns(year);
    state.histDrift = QL.mean(rets) * d.ann + 0.5 * v1y * v1y;

    setNum('mc-vol', v1y * 100, 1);
    setNum('mc-drift', Math.max(-100, Math.min(200, state.histDrift * 100)), 1);
    setNum('mc-target', last * 1.1, last >= 1 ? 2 : 4);
    $('mc-days-out').textContent = $('mc-days').value + (d.ann === 365 ? ' days' : ' trading days');

    var step = QL.niceStep(last * 0.025);
    setNum('o-spot', last, last >= 1 ? 2 : 4);
    setNum('o-strike', Math.round(last / step) * step, 4);
    $('o-strike').step = step;
    setNum('o-vol', (isFinite(v60) ? v60 : v1y) * 100, 1);
    $('o-mkt').value = '';

    // notice + footnote
    var note = $('data-note'), txt = $('data-note-text');
    if (d.source === 'sample') {
      txt.textContent = liveError ? 'Live lookup failed, so this is simulated sample data. ' + liveError
        : 'Showing simulated sample data, not real prices. Add a free Twelve Data key or paste your own price history.';
      note.hidden = false;
    } else { note.hidden = true; }
    var src = d.source === 'live' ? 'Market data from Twelve Data, daily closes, cached for 5 minutes per ticker. '
      : d.source === 'pasted' ? 'Price history pasted by you. ' : 'Sample series are simulated and indexed to 100. ';
    $('footnote').textContent = src + 'Models assume lognormal returns, constant volatility and no dividends. A teaching tool, not trading advice.';

    drawHistory();
    runMC();
    renderOptions();
  }

  /* ---------- canvas helpers ---------- */
  function css(name) { return getComputedStyle(root).getPropertyValue(name).trim(); }
  function prep(canvas) {
    var r = canvas.getBoundingClientRect(), dpr = window.devicePixelRatio || 1;
    canvas.width = Math.max(1, Math.round(r.width * dpr));
    canvas.height = Math.max(1, Math.round(r.height * dpr));
    var ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, r.width, r.height);
    ctx.font = '11px "IBM Plex Mono", ui-monospace, monospace';
    ctx.textBaseline = 'middle';
    return { ctx: ctx, w: r.width, h: r.height };
  }
  function gridY(ctx, ticks, y, x0, x1, labelX, step, col) {
    ctx.lineWidth = 1;
    ticks.forEach(function (v) {
      var py = Math.round(y(v)) + 0.5;
      ctx.strokeStyle = col.line; ctx.beginPath(); ctx.moveTo(x0, py); ctx.lineTo(x1, py); ctx.stroke();
      ctx.fillStyle = col.muted; ctx.textAlign = 'left'; ctx.fillText(fmtAxis(v, step), labelX, py);
    });
  }
  function palette() { return { ink: css('--ink'), muted: css('--muted'), line: css('--line'), accent: css('--accent'), amber: css('--amber'), surface: css('--surface') }; }

  /* ---------- price history ---------- */
  var histGeom = null;
  function drawHistory(hover) {
    var d = state.data; if (!d) return;
    var c = d.closes.slice(-Math.min(d.closes.length, d.ann + 1));
    var dates = d.dates ? d.dates.slice(-c.length) : null;
    var sma = QL.sma(d.closes, 20).slice(-c.length);
    var P = prep($('hist-canvas')), ctx = P.ctx, col = palette();
    var m = { l: 6, r: 62, t: 10, b: 24 }, pw = P.w - m.l - m.r, ph = P.h - m.t - m.b;
    var lo = Math.min.apply(null, c), hi = Math.max.apply(null, c), pad = (hi - lo) * 0.08 || 1;
    lo -= pad; hi += pad;
    var x = function (i) { return m.l + (c.length > 1 ? i / (c.length - 1) : 0) * pw; };
    var y = function (v) { return m.t + (1 - (v - lo) / (hi - lo)) * ph; };
    var tk = QL.ticks(lo, hi, 5), step = tk.length > 1 ? tk[1] - tk[0] : 1;
    gridY(ctx, tk, y, m.l, m.l + pw, m.l + pw + 8, step, col);

    // month labels
    ctx.fillStyle = col.muted; ctx.textAlign = 'center';
    if (dates) {
      var lastX = -99;
      for (var i = 1; i < dates.length; i++) {
        if (dates[i].slice(5, 7) !== dates[i - 1].slice(5, 7) && x(i) - lastX > 44 && x(i) < m.l + pw - 14 && x(i) > m.l + 14) {
          ctx.fillText(MONTHS[+dates[i].slice(5, 7) - 1], x(i), P.h - 10); lastX = x(i);
        }
      }
    } else {
      ctx.textAlign = 'left'; ctx.fillText(c.length + ' observations', m.l, P.h - 10);
    }

    // area + line
    ctx.beginPath();
    c.forEach(function (v, i) { if (i) ctx.lineTo(x(i), y(v)); else ctx.moveTo(x(i), y(v)); });
    ctx.strokeStyle = col.accent; ctx.lineWidth = 1.8; ctx.lineJoin = 'round'; ctx.stroke();
    ctx.lineTo(x(c.length - 1), m.t + ph); ctx.lineTo(x(0), m.t + ph); ctx.closePath();
    var g = ctx.createLinearGradient(0, m.t, 0, m.t + ph);
    ctx.globalAlpha = 0.16; g.addColorStop(0, col.accent); g.addColorStop(1, 'transparent');
    ctx.fillStyle = col.accent; ctx.fill(); ctx.globalAlpha = 1;

    // 20-day mean
    ctx.beginPath(); var started = false;
    sma.forEach(function (v, i) { if (v == null) return; if (started) ctx.lineTo(x(i), y(v)); else { ctx.moveTo(x(i), y(v)); started = true; } });
    ctx.strokeStyle = col.muted; ctx.lineWidth = 1.2; ctx.setLineDash([4, 3]); ctx.stroke(); ctx.setLineDash([]);

    // endpoint
    var ex = x(c.length - 1), ey = y(c[c.length - 1]);
    ctx.fillStyle = col.accent; ctx.beginPath(); ctx.arc(ex, ey, 3.5, 0, 7); ctx.fill();

    histGeom = { m: m, pw: pw, n: c.length, c: c, dates: dates, sma: sma, x: x, y: y, w: P.w };
    if (hover != null) {
      var hx = x(hover);
      ctx.strokeStyle = col.muted; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(hx + 0.5, m.t); ctx.lineTo(hx + 0.5, m.t + ph); ctx.stroke();
      ctx.fillStyle = col.surface; ctx.strokeStyle = col.accent; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(hx, y(c[hover]), 4, 0, 7); ctx.fill(); ctx.stroke();
    }
  }
  function histHover(e) {
    if (!histGeom) return;
    var g = histGeom, r = $('hist-canvas').getBoundingClientRect();
    var i = Math.round((e.clientX - r.left - g.m.l) / g.pw * (g.n - 1));
    i = Math.max(0, Math.min(g.n - 1, i));
    drawHistory(i);
    var tip = $('hist-tip');
    tip.innerHTML = '';
    var b = document.createElement('b'); b.textContent = fmtPrice(g.c[i]); tip.appendChild(b);
    var s = document.createElement('span');
    s.textContent = ' ' + (g.dates ? fmtDate(g.dates[i]) : 'obs ' + (i + 1)) + (g.sma[i] != null ? ' · 20d ' + fmtPrice(g.sma[i]) : '');
    tip.appendChild(s);
    tip.hidden = false;
    var tw = tip.offsetWidth, px = g.x(i) + 12;
    if (px + tw > g.w - 4) px = g.x(i) - tw - 12;
    tip.style.left = Math.max(4, px) + 'px';
  }

  /* ---------- Monte Carlo ---------- */
  function runMC() {
    var d = state.data; if (!d) return;
    var s0 = d.closes[d.closes.length - 1];
    var sigma = num('mc-vol') / 100, mu = num('mc-drift') / 100;
    if (!(sigma > 0)) sigma = 0.2;
    if (!isFinite(mu)) mu = 0;
    state.sim = QL.simulate({ s0: s0, mu: mu, sigma: sigma, days: +$('mc-days').value, paths: +$('mc-paths').value, ann: d.ann });
    drawMC(); mcStats();
  }
  function mcStats() {
    var sim = state.sim; if (!sim) return;
    var target = num('mc-target'); if (!isFinite(target)) target = sim.s0;
    var s = QL.simStats(sim, target);
    $('s-median').textContent = fmtPrice(s.median);
    $('s-p5p95').textContent = fmtPrice(s.p5) + ' / ' + fmtPrice(s.p95);
    $('s-prob').textContent = fmtPct(s.probAbove);
    var e = $('s-exp'); e.textContent = fmtPct(s.expRet, true); e.className = 'stat-value num ' + (s.expRet >= 0 ? 'up' : 'down');
    $('s-var').textContent = fmtPct(s.var95, true);
    $('s-cvar').textContent = fmtPct(s.cvar95, true);
  }
  function drawMC() {
    var sim = state.sim; if (!sim) return;
    var P = prep($('mc-canvas')), ctx = P.ctx, col = palette();
    var histW = P.w < 560 ? 64 : 120, axisW = 58;
    var m = { l: 6, t: 12, b: 24 }, pw = P.w - m.l - axisW - histW, ph = P.h - m.t - m.b;
    var target = num('mc-target');
    var lo = Math.min(QL.quantile(sim.terminal, 0.005), sim.s0), hi = Math.max(QL.quantile(sim.terminal, 0.995), sim.s0);
    var showTarget = isFinite(target) && target > lo * 0.5 && target < hi * 1.6;
    if (showTarget) { lo = Math.min(lo, target); hi = Math.max(hi, target); }
    var pad = (hi - lo) * 0.05; lo = Math.max(0, lo - pad); hi += pad;
    var x = function (t) { return m.l + t / sim.steps * pw; };
    var y = function (v) { return m.t + (1 - (v - lo) / (hi - lo)) * ph; };
    var tk = QL.ticks(lo, hi, 6), step = tk.length > 1 ? tk[1] - tk[0] : 1;
    gridY(ctx, tk, y, m.l, m.l + pw, m.l + pw + histW + 8, step, col);

    // x axis labels
    ctx.fillStyle = col.muted;
    QL.ticks(0, sim.steps, 6).forEach(function (t) {
      ctx.textAlign = t === 0 ? 'left' : 'center';
      if (x(t) < m.l + pw - 10) ctx.fillText(t === 0 ? 'Today' : 'Day ' + t, x(t), P.h - 10);
    });

    ctx.save(); ctx.beginPath(); ctx.rect(m.l, m.t, pw, ph); ctx.clip();
    // sample paths
    var show = Math.min(50, sim.n), stride = Math.floor(sim.n / show);
    ctx.strokeStyle = col.muted; ctx.lineWidth = 0.7; ctx.globalAlpha = 0.22;
    for (var p = 0; p < show; p++) {
      var base = p * stride * sim.cols;
      ctx.beginPath(); ctx.moveTo(x(0), y(sim.data[base]));
      for (var t = 1; t <= sim.steps; t++) ctx.lineTo(x(t), y(sim.data[base + t]));
      ctx.stroke();
    }
    // bands
    var band = function (a, b, alpha) {
      ctx.globalAlpha = alpha; ctx.fillStyle = col.accent; ctx.beginPath();
      for (var t = 0; t <= sim.steps; t++) { if (t) ctx.lineTo(x(t), y(sim.pct[b][t])); else ctx.moveTo(x(t), y(sim.pct[b][t])); }
      for (var t2 = sim.steps; t2 >= 0; t2--) ctx.lineTo(x(t2), y(sim.pct[a][t2]));
      ctx.closePath(); ctx.fill();
    };
    band(0, 4, 0.13); band(1, 3, 0.2);
    ctx.globalAlpha = 1;
    // median
    ctx.beginPath();
    for (var t3 = 0; t3 <= sim.steps; t3++) { if (t3) ctx.lineTo(x(t3), y(sim.pct[2][t3])); else ctx.moveTo(x(t3), y(sim.pct[2][t3])); }
    ctx.strokeStyle = col.accent; ctx.lineWidth = 2; ctx.stroke();
    ctx.restore();

    // histogram of terminal prices
    var bins = 40, counts = new Array(bins).fill(0), maxC = 0;
    for (var i = 0; i < sim.terminal.length; i++) {
      var b = Math.floor((sim.terminal[i] - lo) / (hi - lo) * bins);
      if (b >= 0 && b < bins) { counts[b]++; if (counts[b] > maxC) maxC = counts[b]; }
    }
    var hx = m.l + pw + 4, bh = ph / bins;
    for (var k = 0; k < bins; k++) {
      if (!counts[k]) continue;
      var mid = lo + (k + 0.5) / bins * (hi - lo);
      var above = showTarget ? mid > target : mid > sim.s0;
      ctx.fillStyle = above ? col.accent : col.muted; ctx.globalAlpha = above ? 0.75 : 0.45;
      ctx.fillRect(hx, m.t + ph - (k + 1) * bh + 0.5, counts[k] / maxC * (histW - 10), Math.max(1, bh - 1));
    }
    ctx.globalAlpha = 1;
    ctx.strokeStyle = col.line; ctx.beginPath(); ctx.moveTo(m.l + pw + 0.5, m.t); ctx.lineTo(m.l + pw + 0.5, m.t + ph); ctx.stroke();

    // spot + target lines
    var hline = function (v, color, label) {
      var py = Math.round(y(v)) + 0.5;
      ctx.strokeStyle = color; ctx.lineWidth = 1.2; ctx.setLineDash([5, 4]);
      ctx.beginPath(); ctx.moveTo(m.l, py); ctx.lineTo(m.l + pw + histW, py); ctx.stroke(); ctx.setLineDash([]);
      ctx.fillStyle = color; ctx.textAlign = 'left';
      ctx.fillText(label, m.l + 6, py + (py < m.t + 16 ? 10 : -9));
    };
    if (showTarget) hline(target, col.amber, 'Target ' + fmtPrice(target));
  }

  /* ---------- options ---------- */
  function optInputs() {
    return { S: num('o-spot'), K: num('o-strike'), T: num('o-days') / 365, r: num('o-rate') / 100, sigma: num('o-vol') / 100 };
  }
  function renderOptions() {
    var o = optInputs(), type = state.optType;
    var ok = o.S > 0 && o.K > 0 && o.T > 0 && o.sigma > 0 && isFinite(o.r);
    $('o-price-label').textContent = type === 'call' ? 'Call value' : 'Put value';
    if (!ok) {
      ['o-price', 'g-delta', 'g-gamma', 'g-vega', 'g-theta', 'g-rho', 'g-iv'].forEach(function (id) { $(id).textContent = '—'; });
      $('o-price-sub').textContent = 'Enter spot, strike, expiry and volatility';
      $('ladder').tBodies[0].innerHTML = '';
      prep($('opt-canvas'));
      return;
    }
    var b = QL.bs(type, o.S, o.K, o.T, o.r, o.sigma);
    var intr = Math.max(type === 'call' ? o.S - o.K : o.K - o.S, 0);
    $('o-price').textContent = fmtPrice(b.price);
    $('o-price-sub').textContent = 'Intrinsic ' + fmtPrice(intr) + ' · time value ' + fmtPrice(b.price - intr);
    $('g-delta').textContent = b.delta.toFixed(3).replace('-', '−');
    $('g-gamma').textContent = b.gamma.toFixed(4);
    $('g-vega').textContent = b.vega.toFixed(3);
    $('g-theta').textContent = b.theta.toFixed(3).replace('-', '−');
    $('g-rho').textContent = b.rho.toFixed(3).replace('-', '−');
    var mkt = num('o-mkt'), ivEl = $('g-iv');
    if (mkt > 0) {
      var iv = QL.impliedVol(type, mkt, o.S, o.K, o.T, o.r);
      ivEl.textContent = iv == null ? 'no solution' : fmtPct(iv, false, 2);
      ivEl.title = iv == null ? 'That price is outside the range any volatility can produce for this option.' : '';
    } else { ivEl.textContent = '—'; ivEl.title = ''; }
    drawOption(o, b);
    renderLadder(o);
  }

  function drawOption(o, b) {
    var type = state.optType;
    var P = prep($('opt-canvas')), ctx = P.ctx, col = palette();
    var m = { l: 6, r: 58, t: 12, b: 24 }, pw = P.w - m.l - m.r, ph = P.h - m.t - m.b;
    var x0 = Math.min(o.S, o.K) * 0.6, x1 = Math.max(o.S, o.K) * 1.4;
    var payoff = function (s) { return Math.max(type === 'call' ? s - o.K : o.K - s, 0); };
    var value = function (s) { return QL.bs(type, s, o.K, o.T, o.r, o.sigma).price; };
    var hi = Math.max(value(type === 'call' ? x1 : x0), payoff(type === 'call' ? x1 : x0)) * 1.08 || 1, lo = 0;
    var x = function (s) { return m.l + (s - x0) / (x1 - x0) * pw; };
    var y = function (v) { return m.t + (1 - (v - lo) / (hi - lo)) * ph; };
    var tk = QL.ticks(lo, hi, 5), step = tk.length > 1 ? tk[1] - tk[0] : 1;
    gridY(ctx, tk, y, m.l, m.l + pw, m.l + pw + 8, step, col);
    var xt = QL.ticks(x0, x1, P.w < 520 ? 4 : 7), xs = xt.length > 1 ? xt[1] - xt[0] : 1;
    ctx.fillStyle = col.muted; ctx.textAlign = 'center';
    xt.forEach(function (s) { if (x(s) > m.l + 16 && x(s) < m.l + pw - 16) ctx.fillText(fmtAxis(s, xs), x(s), P.h - 10); });

    var vline = function (s, color, label, dash, row) {
      if (s <= x0 || s >= x1) return;
      var px = Math.round(x(s)) + 0.5;
      ctx.strokeStyle = color; ctx.lineWidth = 1.2; ctx.setLineDash(dash);
      ctx.beginPath(); ctx.moveTo(px, m.t); ctx.lineTo(px, m.t + ph); ctx.stroke(); ctx.setLineDash([]);
      ctx.fillStyle = color;
      var right = px + 6 + ctx.measureText(label).width < m.l + pw;
      ctx.textAlign = right ? 'left' : 'right';
      ctx.fillText(label, px + (right ? 6 : -6), m.t + 8 + row * 15);
    };
    vline(o.S, col.muted, 'Spot ' + fmtPrice(o.S), [2, 3], 0);
    var be = type === 'call' ? o.K + b.price : o.K - b.price;
    vline(be, col.amber, 'Breakeven ' + fmtPrice(be), [5, 4], 1);

    ctx.save(); ctx.beginPath(); ctx.rect(m.l, m.t, pw, ph + 1); ctx.clip();
    // payoff at expiry
    ctx.beginPath(); ctx.moveTo(x(x0), y(payoff(x0))); ctx.lineTo(x(o.K), y(0)); ctx.lineTo(x(x1), y(payoff(x1)));
    ctx.strokeStyle = col.muted; ctx.lineWidth = 1.5; ctx.stroke();
    // value today
    ctx.beginPath();
    for (var i = 0; i <= 120; i++) { var s = x0 + (x1 - x0) * i / 120; if (i) ctx.lineTo(x(s), y(value(s))); else ctx.moveTo(x(s), y(value(s))); }
    ctx.strokeStyle = col.accent; ctx.lineWidth = 2; ctx.stroke();
    ctx.restore();
    ctx.fillStyle = col.accent; ctx.beginPath(); ctx.arc(x(o.S), y(b.price), 4, 0, 7); ctx.fill();
  }

  function renderLadder(o) {
    var step = QL.niceStep(o.S * 0.025), center = Math.round(o.S / step) * step;
    var body = $('ladder').tBodies[0]; body.innerHTML = '';
    var dec = step >= 1 ? (step % 1 ? 1 : 0) : (step >= 0.1 ? 2 : 4);
    var cell = function (tr, text, cls) { var td = document.createElement('td'); td.textContent = text; if (cls) td.className = cls; tr.appendChild(td); };
    for (var i = -5; i <= 5; i++) {
      var K = +(center + i * step).toFixed(6);
      if (!(K > 0)) continue;
      var c = QL.bs('call', o.S, K, o.T, o.r, o.sigma), p = QL.bs('put', o.S, K, o.T, o.r, o.sigma);
      var tr = document.createElement('tr');
      if (i === 0) tr.className = 'atm';
      if (Math.abs(K - o.K) < step * 1e-6) tr.classList.add('sel');
      tr.dataset.k = K;
      cell(tr, c.delta.toFixed(2), 'dim');
      cell(tr, fmtPrice(c.price));
      cell(tr, K.toLocaleString('en-US', { minimumFractionDigits: dec, maximumFractionDigits: dec }), 'strike-col');
      cell(tr, fmtPrice(p.price));
      cell(tr, p.delta.toFixed(2).replace('-', '−'), 'dim');
      cell(tr, fmtPct(c.pItm));
      body.appendChild(tr);
    }
  }

  /* ---------- theme ---------- */
  var SUN = '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/></svg>';
  var MOON = '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20 14.5A8 8 0 0 1 9.5 4a8 8 0 1 0 10.5 10.5z"/></svg>';
  var mq = window.matchMedia ? window.matchMedia('(prefers-color-scheme: dark)') : null;
  function isDark() { var a = root.getAttribute('data-theme'); return a ? a === 'dark' : !!(mq && mq.matches); }
  function syncTheme() {
    var btn = document.querySelector('[data-theme-toggle]'), dark = isDark();
    btn.innerHTML = dark ? SUN : MOON;
    btn.setAttribute('aria-label', dark ? 'Switch to light mode' : 'Switch to dark mode');
    redraw();
  }
  function redraw() { drawHistory(); drawMC(); if (state.data) renderOptions(); }

  /* ---------- data source panel ---------- */
  function openModal() { $('key-input').value = getKey(); $('data-msg').textContent = ''; $('data-modal').hidden = false; $('key-input').focus(); }
  function closeModal() { $('data-modal').hidden = true; }

  /* ---------- wiring ---------- */
  function debounce(fn, ms) { var t; return function () { clearTimeout(t); t = setTimeout(fn, ms); }; }

  function init() {
    $('ticker-form').addEventListener('submit', function (e) { e.preventDefault(); loadSymbol($('ticker-input').value); });
    document.querySelectorAll('.chips .chip').forEach(function (c) { c.addEventListener('click', function () { loadSymbol(c.dataset.sym); }); });

    var cv = $('hist-canvas');
    cv.addEventListener('mousemove', histHover);
    cv.addEventListener('touchstart', function (e) { if (e.touches[0]) histHover(e.touches[0]); }, { passive: true });
    cv.addEventListener('touchmove', function (e) { if (e.touches[0]) histHover(e.touches[0]); }, { passive: true });
    cv.addEventListener('mouseleave', function () { $('hist-tip').hidden = true; drawHistory(); });

    var rerun = debounce(runMC, 90);
    $('mc-paths').addEventListener('input', function () { $('mc-paths-out').textContent = (+this.value).toLocaleString('en-US'); rerun(); });
    $('mc-days').addEventListener('input', function () {
      $('mc-days-out').textContent = this.value + (state.data && state.data.ann === 365 ? ' days' : ' trading days'); rerun();
    });
    $('mc-vol').addEventListener('input', rerun);
    $('mc-drift').addEventListener('input', rerun);
    $('mc-target').addEventListener('input', function () { drawMC(); mcStats(); });
    $('mc-run').addEventListener('click', runMC);
    $('mc-use-hist').addEventListener('click', function () { setNum('mc-drift', Math.max(-100, Math.min(200, state.histDrift * 100)), 1); runMC(); });
    $('mc-use-rn').addEventListener('click', function () { var r = num('o-rate'); setNum('mc-drift', isFinite(r) ? r : 0, 2); runMC(); });
    $('mc-use-zero').addEventListener('click', function () { setNum('mc-drift', 0, 1); runMC(); });

    ['o-spot', 'o-strike', 'o-days', 'o-rate', 'o-vol', 'o-mkt'].forEach(function (id) { $(id).addEventListener('input', renderOptions); });
    document.querySelectorAll('.seg-btn').forEach(function (b) {
      b.addEventListener('click', function () {
        state.optType = b.dataset.type;
        document.querySelectorAll('.seg-btn').forEach(function (o) {
          var on = o === b; o.classList.toggle('is-active', on); o.setAttribute('aria-selected', on ? 'true' : 'false');
        });
        renderOptions();
      });
    });
    $('ladder').addEventListener('click', function (e) {
      var tr = e.target.closest ? e.target.closest('tr[data-k]') : null;
      if (tr) { $('o-strike').value = tr.dataset.k; renderOptions(); }
    });

    document.querySelector('[data-theme-toggle]').addEventListener('click', function () {
      root.setAttribute('data-theme', isDark() ? 'light' : 'dark');
    });
    new MutationObserver(syncTheme).observe(root, { attributes: true, attributeFilter: ['data-theme'] });
    if (mq && mq.addEventListener) mq.addEventListener('change', syncTheme);

    $('data-btn').addEventListener('click', openModal);
    $('data-note-btn').addEventListener('click', openModal);
    $('data-close').addEventListener('click', closeModal);
    $('data-modal').addEventListener('click', function (e) { if (e.target === this) closeModal(); });
    document.addEventListener('keydown', function (e) { if (e.key === 'Escape') closeModal(); });
    $('key-save').addEventListener('click', function () {
      var k = $('key-input').value.trim();
      if (!k) { $('data-msg').textContent = 'Paste your Twelve Data API key first.'; return; }
      memKey = k; store.set(KEY_STORE, k); state.mode = 'live'; cache = {};
      closeModal(); loadSymbol(state.symbol);
    });
    $('key-clear').addEventListener('click', function () {
      memKey = null; store.del(KEY_STORE); state.mode = 'sample'; $('key-input').value = '';
      closeModal(); loadSymbol(state.symbol);
    });
    $('sample-use').addEventListener('click', function () { state.mode = 'sample'; closeModal(); loadSymbol(state.symbol); });
    $('paste-load').addEventListener('click', function () {
      var res = QL.parsePasted($('paste-input').value);
      if (res.closes.length < 30) { $('data-msg').textContent = 'Found ' + res.closes.length + ' usable prices. Paste at least 30 daily closes.'; return; }
      var label = ($('paste-name').value.trim() || 'CUSTOM').toUpperCase().slice(0, 24);
      state.mode = 'pasted'; state.symbol = label; $('ticker-input').value = label;
      closeModal();
      applyData({
        symbol: label, name: label + ' · pasted price history', source: 'pasted', closes: res.closes, dates: res.dates, ann: 252,
        asof: res.closes.length + ' pasted closes' + (res.dates ? ', through ' + fmtDate(res.dates[res.dates.length - 1]) : '')
      });
    });

    if (window.ResizeObserver) {
      var ro = new ResizeObserver(debounce(redraw, 60));
      document.querySelectorAll('.chart-wrap').forEach(function (el) { ro.observe(el); });
    } else { window.addEventListener('resize', debounce(redraw, 100)); }
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(redraw);

    state.mode = getKey() ? 'live' : 'sample';
    syncTheme();
    loadSymbol('NVDA');
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init); else init();
})();
