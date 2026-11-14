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

  // Multi-leg strategy, per share. Legs: { kind: 'stock' | 'call' | 'put', q: +1 | -1, k: strike }.
  // Profit and loss at expiry is piecewise linear with kinks at the strikes.
  QL.strategy = function (legs, S, T, r, sigma) {
    var prices = legs.map(function (l) { return l.kind === 'stock' ? S : QL.bs(l.kind, S, l.k, T, r, sigma).price; });
    var cost = 0, slope = 0, knots = [0];
    legs.forEach(function (l, i) {
      cost += l.q * prices[i];
      if (l.kind !== 'put') slope += l.q; // slope of P/L above the highest strike
      if (l.kind !== 'stock' && knots.indexOf(l.k) < 0) knots.push(l.k);
    });
    knots.sort(function (a, b) { return a - b; });
    var plExp = function (s) {
      var v = -cost;
      legs.forEach(function (l) { v += l.q * (l.kind === 'stock' ? s : Math.max(l.kind === 'call' ? s - l.k : l.k - s, 0)); });
      return v;
    };
    var plNow = function (s) {
      var v = -cost;
      legs.forEach(function (l) { v += l.q * (l.kind === 'stock' ? s : QL.bs(l.kind, s, l.k, T, r, sigma).price); });
      return v;
    };
    var vals = knots.map(plExp);
    var maxP = Math.max.apply(null, vals), maxL = Math.min.apply(null, vals);
    if (slope > 1e-9) maxP = Infinity;
    if (slope < -1e-9) maxL = -Infinity;
    var bes = [];
    for (var i = 1; i < knots.length; i++) {
      var a = vals[i - 1], b = vals[i];
      if (a * b < 0) bes.push(knots[i - 1] + (knots[i] - knots[i - 1]) * a / (a - b));
    }
    var last = knots[knots.length - 1], lv = vals[vals.length - 1];
    if (Math.abs(slope) > 1e-9 && -lv / slope > 0) bes.push(last - lv / slope);
    // Chance the price at expiry lands where P/L is positive (lognormal, drifting at the risk-free rate).
    var cdf = function (x) {
      if (!(x > 0)) return 0;
      if (x === Infinity) return 1;
      return QL.normCdf(-(Math.log(S / x) + (r - 0.5 * sigma * sigma) * T) / (sigma * Math.sqrt(T)));
    };
    var edges = [0].concat(bes, [Infinity]), prob = 0, zones = []; // zones: price ranges that end in profit
    for (var j = 0; j + 1 < edges.length; j++) {
      var lo = edges[j], hi = edges[j + 1], mid = hi === Infinity ? lo * 2 + 1 : (lo + hi) / 2;
      if (plExp(mid) > 0) { prob += cdf(hi) - cdf(lo); zones.push([lo, hi]); }
    }
    return { prices: prices, cost: cost, plExp: plExp, plNow: plNow, knots: knots, maxP: maxP, maxL: maxL, bes: bes, prob: prob, zones: zones };
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
  // Rolling annualized volatility. out[i] covers the n returns ending at close i; null before that.
  QL.rollingVol = function (closes, n, ann) {
    var r = QL.logReturns(closes), out = new Array(closes.length).fill(null);
    for (var i = n; i < closes.length; i++) out[i] = QL.stdev(r.slice(i - n, i)) * Math.sqrt(ann);
    return out;
  };
  // Share of the earlier values that sit below the latest one, from 0 to 1.
  QL.percentRank = function (vals) {
    var n = vals.length;
    if (n < 2) return NaN;
    var cur = vals[n - 1], below = 0;
    for (var i = 0; i < n - 1; i++) if (vals[i] < cur) below++;
    return below / (n - 1);
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
      median: QL.quantile(t, 0.5), p5: q05, p95: QL.quantile(t, 0.95), p25: QL.quantile(t, 0.25), p75: QL.quantile(t, 0.75),
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
  var state = { symbol: 'NVDA', data: null, sim: null, optType: 'call', mode: 'sample', strat: 'covered', stratK: {}, vol: null };

  var store = {
    get: function (k) { try { return localStorage.getItem(k); } catch (e) { return null; } },
    set: function (k, v) { try { localStorage.setItem(k, v); } catch (e) {} },
    del: function (k) { try { localStorage.removeItem(k); } catch (e) {} }
  };
  var memKey = null;
  function getKey() { return memKey || store.get(KEY_STORE) || ''; }
  // True when the deployment's /api/td proxy has a shared key configured.
  var serverKey = false;
  function hasLive() { return !!getKey() || serverKey; }

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

  /* ---------- plain-English takeaways ---------- */
  // parts: plain strings, or [text] for an emphasised figure. Pass null to hide the line.
  function say(id, parts) {
    var el = $(id);
    el.innerHTML = '';
    if (!parts) { el.hidden = true; return; }
    var tag = document.createElement('span'); tag.className = 'takeaway-tag'; tag.textContent = 'In plain English';
    el.appendChild(tag);
    parts.forEach(function (p) {
      if (typeof p === 'string') el.appendChild(document.createTextNode(p));
      else { var b = document.createElement('b'); b.textContent = p[0]; el.appendChild(b); }
    });
    el.hidden = false;
  }
  // A probability as an everyday fraction: 0.34 -> "about 1 in 3".
  var ODDS = [[1, 100], [1, 50], [1, 20], [1, 10], [1, 8], [1, 6], [1, 5], [1, 4], [1, 3], [2, 5], [1, 2], [3, 5], [2, 3], [3, 4], [4, 5], [5, 6], [7, 8], [9, 10], [19, 20], [49, 50], [99, 100]];
  function oddsText(p) {
    if (!(p >= 0.005)) return 'almost none';
    if (p > 0.995) return 'almost all';
    var best = ODDS[0];
    ODDS.forEach(function (f) { if (Math.abs(f[0] / f[1] - p) < Math.abs(best[0] / best[1] - p)) best = f; });
    return best[1] === 2 ? 'about half' : 'about ' + best[0] + ' in ' + best[1];
  }
  // A number of days as rough calendar time: 126 trading days -> "about 6 months".
  function spanWords(days, ann) {
    var months = days / ann * 12;
    if (months < 0.9) { var w = Math.max(1, Math.round(days / (ann / 52))); return 'about ' + w + (w === 1 ? ' week' : ' weeks'); }
    if (months < 23.5) { var mo = Math.round(months); return mo === 12 ? 'about a year' : 'about ' + mo + (mo === 1 ? ' month' : ' months'); }
    return 'about ' + Math.round(months / 12 * 2) / 2 + ' years';
  }
  // How to describe the stretch of history on screen: n is the number of daily steps it covers.
  function periodText(d, n) {
    if (n >= d.ann * 0.9) return 'the past year';
    return d.dates ? 'the past ' + n + (d.ann === 365 ? ' days' : ' trading days') : 'these ' + (n + 1) + ' prices';
  }
  function unitWord() { return state.data && state.data.ann === 365 ? 'unit' : 'share'; }
  function fmtSmall(v) { return v >= 0.1 ? v.toFixed(2) : v >= 0.01 ? v.toFixed(3) : v.toFixed(4); }

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
    // A personal key goes straight to Twelve Data; otherwise use the server proxy.
    var url = key
      ? function (ep, extra) { return 'https://api.twelvedata.com/' + ep + '?symbol=' + encodeURIComponent(tds) + '&apikey=' + encodeURIComponent(key) + extra; }
      : function (ep, extra) { return '/api/td?endpoint=' + ep + '&symbol=' + encodeURIComponent(tds) + extra; };
    var series = fetchJson(url('time_series', '&interval=1day&outputsize=' + (crypto ? 366 : 253)));
    var quote = fetchJson(url('quote', '')).catch(function () { return null; });
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
    if (state.mode === 'pasted') state.mode = hasLive() ? 'live' : 'sample';
    state.symbol = sym;
    $('ticker-input').value = sym;
    document.querySelectorAll('.chips .chip').forEach(function (c) { c.classList.toggle('is-active', c.dataset.sym === sym); });
    if (state.mode === 'live' && hasLive()) {
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

    histTake(d, year, last, ret, hi);
    renderVol();
    state.stratK = {};
    drawHistory();
    runMC(true);
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
  function gridY(ctx, ticks, y, x0, x1, labelX, step, col, suffix) {
    ctx.lineWidth = 1;
    ticks.forEach(function (v) {
      var py = Math.round(y(v)) + 0.5;
      ctx.strokeStyle = col.line; ctx.beginPath(); ctx.moveTo(x0, py); ctx.lineTo(x1, py); ctx.stroke();
      ctx.fillStyle = col.muted; ctx.textAlign = 'left'; ctx.fillText(fmtAxis(v, step) + (suffix || ''), labelX, py);
    });
  }
  // Month names along the bottom of a dated chart, or a point count when there are no dates.
  function monthAxis(ctx, dates, count, x, left, right, py, col) {
    ctx.fillStyle = col.muted; ctx.textAlign = 'center';
    if (dates) {
      var lastX = -99;
      for (var i = 1; i < dates.length; i++) {
        if (dates[i].slice(5, 7) !== dates[i - 1].slice(5, 7) && x(i) - lastX > 44 && x(i) < right - 14 && x(i) > left + 14) {
          ctx.fillText(MONTHS[+dates[i].slice(5, 7) - 1], x(i), py); lastX = x(i);
        }
      }
    } else {
      ctx.textAlign = 'left'; ctx.fillText(count + ' observations', left, py);
    }
  }
  function palette() { return { ink: css('--ink'), muted: css('--muted'), line: css('--line'), accent: css('--accent'), amber: css('--amber'), surface: css('--surface'), up: css('--up'), down: css('--down') }; }

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

    monthAxis(ctx, dates, c.length, x, m.l, m.l + pw, P.h - 10, col);

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

  function histTake(d, year, last, ret, hi) {
    var parts = [(d.source === 'sample' ? 'This sample series' : d.symbol) + ' is ' + (ret >= 0 ? 'up ' : 'down '), [fmtPct(Math.abs(ret))],
      ' over ' + periodText(d, year.length - 1)];
    var off = last / hi - 1;
    if (off > -0.0005) parts.push(' and is at its highest close of that period.');
    else parts.push(' and sits ', [fmtPct(-off)], ' below its highest close of that period, ', [fmtPrice(hi)], '.');
    var mdd = QL.maxDrawdown(year);
    if (mdd < -0.0005) parts.push(' Its deepest fall from a peak along the way was ', [fmtPct(-mdd)], '.');
    say('hist-take', parts);
  }

  /* ---------- volatility check ---------- */
  var VOL_WIN = 20;
  var VOL_LEVELS = [
    [0.8, 'high', 'High', 'much more than usual'], [0.6, 'above', 'Above normal', 'a little more than usual'],
    [0.4, 'normal', 'Normal', 'about as much as usual'], [0.2, 'below', 'Below normal', 'a little less than usual'],
    [-1, 'low', 'Low', 'much less than usual']
  ];
  function renderVol() {
    var d = state.data; if (!d) return;
    var n = Math.min(d.closes.length, d.ann + 1);
    var roll = QL.rollingVol(d.closes, VOL_WIN, d.ann).slice(-n), dates = d.dates ? d.dates.slice(-n) : null;
    var first = 0; while (first < roll.length && roll[first] == null) first++;
    var v = roll.slice(first);
    if (v.length < 5 || !(v[v.length - 1] > 0)) {
      state.vol = null; $('vol-pill').hidden = true; say('vol-take', null); drawVol();
      return;
    }
    var sorted = v.slice().sort(function (a, b) { return a - b; });
    var cur = v[v.length - 1], rank = QL.percentRank(v);
    var lvl = VOL_LEVELS.filter(function (l) { return rank >= l[0]; })[0];
    state.vol = { v: v, dates: dates ? dates.slice(first) : null, q25: QL.quantile(sorted, 0.25), q75: QL.quantile(sorted, 0.75), lo: sorted[0], hi: sorted[sorted.length - 1] };
    var pill = $('vol-pill'); pill.textContent = lvl[2]; pill.dataset.level = lvl[1]; pill.hidden = false;
    var fullYear = v.length - 1 >= d.ann * 0.9, where = fullYear ? 'of the past year' : 'in this price history';
    var parts = [(d.source === 'sample' ? "This sample series'" : d.symbol + "'s") + ' ' + VOL_WIN + '-day volatility is ', [fmtPct(cur)], ' a year, '];
    if (rank >= 1) parts.push('its highest reading ' + where);
    else if (rank <= 0) parts.push('its lowest reading ' + where);
    else if (fullYear) parts.push('higher than on ', [fmtPct(rank, false, 0)], ' of days in the past year');
    else parts.push('higher than ', [fmtPct(rank, false, 0)], ' of the ' + (v.length - 1) + ' earlier readings in this price history');
    parts.push(', so the price has been swinging ' + lvl[3] + '. At this level a typical day moves it about ', [fmtPct(cur / Math.sqrt(d.ann))], ' up or down.');
    say('vol-take', parts);
    drawVol();
  }

  var volGeom = null;
  function drawVol(hover) {
    var V = state.vol, P = prep($('vol-canvas'));
    volGeom = null;
    if (!V) return;
    var ctx = P.ctx, col = palette(), v = V.v;
    var m = { l: 6, r: 50, t: 10, b: 24 }, pw = P.w - m.l - m.r, ph = P.h - m.t - m.b;
    var pad = (V.hi - V.lo) * 0.12 || V.hi * 0.1, lo = Math.max(0, V.lo - pad) * 100, hi = (V.hi + pad) * 100;
    var x = function (i) { return m.l + (v.length > 1 ? i / (v.length - 1) : 0) * pw; };
    var y = function (val) { return m.t + (1 - (val * 100 - lo) / (hi - lo)) * ph; };
    var tk = QL.ticks(lo, hi, 5), step = tk.length > 1 ? tk[1] - tk[0] : 1;
    gridY(ctx, tk, function (pct) { return y(pct / 100); }, m.l, m.l + pw, m.l + pw + 8, step, col, '%');
    monthAxis(ctx, V.dates, v.length, x, m.l, m.l + pw, P.h - 10, col);

    // typical range: the middle half of the year's readings
    ctx.fillStyle = col.accent; ctx.globalAlpha = 0.14;
    ctx.fillRect(m.l, y(V.q75), pw, y(V.q25) - y(V.q75)); ctx.globalAlpha = 1;

    ctx.beginPath();
    v.forEach(function (val, i) { if (i) ctx.lineTo(x(i), y(val)); else ctx.moveTo(x(i), y(val)); });
    ctx.strokeStyle = col.accent; ctx.lineWidth = 1.8; ctx.lineJoin = 'round'; ctx.stroke();
    ctx.fillStyle = col.accent; ctx.beginPath(); ctx.arc(x(v.length - 1), y(v[v.length - 1]), 3.5, 0, 7); ctx.fill();

    volGeom = { m: m, pw: pw, n: v.length, x: x, w: P.w };
    if (hover != null) {
      var hx = x(hover);
      ctx.strokeStyle = col.muted; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(hx + 0.5, m.t); ctx.lineTo(hx + 0.5, m.t + ph); ctx.stroke();
      ctx.fillStyle = col.surface; ctx.strokeStyle = col.accent; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(hx, y(v[hover]), 4, 0, 7); ctx.fill(); ctx.stroke();
    }
  }
  function volHover(e) {
    if (!volGeom || !state.vol) return;
    var g = volGeom, V = state.vol, r = $('vol-canvas').getBoundingClientRect();
    var i = Math.max(0, Math.min(g.n - 1, Math.round((e.clientX - r.left - g.m.l) / g.pw * (g.n - 1))));
    drawVol(i);
    var tip = $('vol-tip');
    tip.innerHTML = '';
    var b = document.createElement('b'); b.textContent = fmtPct(V.v[i]); tip.appendChild(b);
    var sp = document.createElement('span'); sp.textContent = ' ' + (V.dates ? fmtDate(V.dates[i]) : 'obs ' + (i + 1)); tip.appendChild(sp);
    tip.hidden = false;
    var tw = tip.offsetWidth, px = g.x(i) + 12;
    if (px + tw > g.w - 4) px = g.x(i) - tw - 12;
    tip.style.left = Math.max(4, px) + 'px';
  }

  /* ---------- Monte Carlo ---------- */
  var mcAnim = 0;
  function reducedMotion() { return !!(window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches); }
  // animate === true draws the paths outward from today; anything else paints the finished chart.
  function runMC(animate) {
    var d = state.data; if (!d) return;
    var s0 = d.closes[d.closes.length - 1];
    var sigma = num('mc-vol') / 100, mu = num('mc-drift') / 100;
    if (!(sigma > 0)) sigma = 0.2;
    if (!isFinite(mu)) mu = 0;
    state.sim = QL.simulate({ s0: s0, mu: mu, sigma: sigma, days: +$('mc-days').value, paths: +$('mc-paths').value, ann: d.ann });
    mcStats();
    if (mcAnim) { cancelAnimationFrame(mcAnim); mcAnim = 0; }
    if (animate === true && window.requestAnimationFrame && !reducedMotion()) {
      var t0 = null, dur = 1200;
      var frame = function (ts) {
        if (t0 === null) t0 = ts;
        var p = Math.min(1, (ts - t0) / dur);
        drawMC(1 - Math.pow(1 - p, 3), true);
        mcAnim = p < 1 ? requestAnimationFrame(frame) : 0;
      };
      drawMC(0, true);
      mcAnim = requestAnimationFrame(frame);
    } else drawMC();
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
    var ann = state.data ? state.data.ann : 252, hasTarget = isFinite(num('mc-target'));
    say('mc-take', ['With these settings, ' + oddsText(s.probAbove) + ' of the simulated paths (', [fmtPct(s.probAbove)], ') end above ' +
      (hasTarget ? 'the ' : "today's price of "), [fmtPrice(target)], (hasTarget ? ' target' : '') + ' after ' + sim.steps +
      (ann === 365 ? ' days' : ' trading days') + ' (' + spanWords(sim.steps, ann) + '). Half of them finish between ', [fmtPrice(s.p25)], ' and ', [fmtPrice(s.p75)],
      ', and 1 in 20 ends below ', [fmtPrice(s.p5)], ' (', [fmtPct(s.var95, true)], ' from today).']);
  }
  function drawMC(prog, fromAnim) {
    var sim = state.sim; if (!sim) return;
    if (mcAnim && !fromAnim) return; // the running animation repaints on its next frame
    if (prog == null) prog = 1;
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

    ctx.save(); ctx.beginPath(); ctx.rect(m.l, m.t, pw * prog, ph); ctx.clip();
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
    if (prog < 1) { // leading dot on the median while the paths draw
      var tf = prog * sim.steps, ti = Math.min(sim.steps - 1, Math.floor(tf)), med = sim.pct[2];
      ctx.fillStyle = col.accent; ctx.beginPath();
      ctx.arc(x(tf), y(med[ti] + (med[ti + 1] - med[ti]) * (tf - ti)), 3.5, 0, 7); ctx.fill();
    }

    // histogram of terminal prices (grows in as the paths arrive)
    var grow = Math.max(0, Math.min(1, (prog - 0.7) / 0.3));
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
      ctx.fillRect(hx, m.t + ph - (k + 1) * bh + 0.5, counts[k] / maxC * (histW - 10) * grow, Math.max(1, bh - 1));
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
      say('opt-take', null); say('ladder-take', null);
      prep($('opt-canvas'));
      renderStrategy();
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
    var call = type === 'call', be = call ? o.K + b.price : o.K - b.price, unit = unitWord();
    var parts = ['This ' + type + ' costs ', [fmtPrice(b.price)], ' per ' + unit];
    if (unit === 'share') parts.push(' (', [fmtPrice(+b.price.toFixed(b.price >= 1 ? 2 : 4) * 100)], ' for a standard 100-share contract)');
    parts.push(' and makes money at expiry only if the price ends ' + (call ? 'above ' : 'below '), [fmtPrice(be)], ', ', [fmtPct(be / o.S - 1, true)], ' from here.');
    if (Math.abs(b.theta) >= 0.00005) {
      parts.push(' Each day that passes ' + (b.theta < 0 ? 'takes about ' : 'adds about '), [fmtSmall(Math.abs(b.theta))],
        (b.theta < 0 ? ' off' : ' to') + ' its value, all else equal.');
    }
    say('opt-take', parts);
    drawOption(o, b);
    renderLadder(o);
    renderStrategy();
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
    var fmtK = function (K) { return K.toLocaleString('en-US', { minimumFractionDigits: dec, maximumFractionDigits: dec }); };
    var kUp = +(center + 2 * step).toFixed(6), kDn = +(center - 2 * step).toFixed(6);
    if (kDn > 0) {
      var up = QL.bs('call', o.S, kUp, o.T, o.r, o.sigma), dn = QL.bs('call', o.S, kDn, o.T, o.r, o.sigma);
      say('ladder-take', ['Higher strikes make calls cheaper but less likely to pay off: the ', [fmtK(kUp)], ' call costs ', [fmtPrice(up.price)],
        ' and the model gives it a ', [fmtPct(up.pItm, false, 0)], ' chance of finishing above its strike, while the ', [fmtK(kDn)], ' call costs ',
        [fmtPrice(dn.price)], ' with a ', [fmtPct(dn.pItm, false, 0)], ' chance.']);
    } else say('ladder-take', null);
  }

  /* ---------- strategy builder ---------- */
  // Each leg: [kind, quantity, strike offset in ladder steps from the at-the-money strike].
  var STRATS = {
    covered: { best: 'a small rise', legs: [['stock', 1, 0], ['call', -1, 2]], desc: 'You own the shares and sell a call above the current price. You pocket the premium now, but your gains stop at the strike.' },
    protective: { best: 'a rise, with a floor', legs: [['stock', 1, 0], ['put', 1, -2]], desc: 'You own the shares and buy a put below the current price as insurance. Losses stop at the strike, for the cost of the put.' },
    straddle: { best: 'a big move', legs: [['call', 1, 0], ['put', 1, 0]], desc: 'You buy a call and a put at the same strike. You profit from a big move in either direction and lose if the price stays where it is.' },
    strangle: { best: 'a big move', legs: [['call', 1, 2], ['put', 1, -2]], desc: 'You buy a call above and a put below the current price. Cheaper than a straddle, but the price has to move further before you profit.' },
    bull: { best: 'a moderate rise', legs: [['call', 1, 0], ['call', -1, 2]], desc: 'You buy a call and sell a higher-strike call to cut the cost. A bet on a moderate rise, with both profit and loss capped.' },
    condor: { best: 'a quiet market', legs: [['put', 1, -4], ['put', -1, -2], ['call', -1, 2], ['call', 1, 4]], desc: 'You sell a call and a put around the current price and buy further-out ones as protection. You keep the credit if the price stays in the middle.' }
  };
  var stratView = null;
  function fmtAmt(v, S) {
    var d = S < 1 ? 4 : 2;
    return Math.abs(v).toLocaleString('en-US', { minimumFractionDigits: d, maximumFractionDigits: d });
  }
  function fmtPL(v, S) { return (v < 0 ? '−' : '+') + fmtAmt(v, S != null ? S : stratView ? stratView.S : 100); }

  function stratLegs(S) {
    var step = QL.niceStep(S * 0.025), center = Math.round(S / step) * step;
    return STRATS[state.strat].legs.map(function (l, i) {
      var custom = state.stratK[i];
      var k = custom > 0 ? custom : Math.max(step, +(center + l[2] * step).toFixed(6));
      return { kind: l[0], q: l[1], k: k };
    });
  }

  function setStrat(name) {
    state.strat = name; state.stratK = {};
    document.querySelectorAll('#st-presets .chip').forEach(function (c) {
      var on = c.dataset.strat === name; c.classList.toggle('is-active', on); c.setAttribute('aria-pressed', on ? 'true' : 'false');
    });
    $('st-desc').textContent = STRATS[name].desc;
    $('st-best').textContent = STRATS[name].best.charAt(0).toUpperCase() + STRATS[name].best.slice(1);
    var box = $('st-legs'); box.innerHTML = '';
    STRATS[name].legs.forEach(function (l, i) {
      var el = document.createElement('div'); el.className = 'leg';
      var side = document.createElement('span'); side.className = 'leg-side ' + (l[1] > 0 ? 'buy' : 'sell'); side.textContent = l[1] > 0 ? 'Buy' : 'Sell';
      var what = document.createElement('span'); what.className = 'leg-what'; what.textContent = l[0] === 'stock' ? 'shares' : l[0];
      el.appendChild(side); el.appendChild(what);
      if (l[0] !== 'stock') {
        var lab = document.createElement('label'); lab.appendChild(document.createTextNode('Strike'));
        var inp = document.createElement('input'); inp.type = 'number'; inp.min = '0.01'; inp.dataset.leg = i;
        inp.setAttribute('aria-label', (l[1] > 0 ? 'Buy ' : 'Sell ') + l[0] + ' strike');
        inp.addEventListener('input', function () {
          var v = parseFloat(inp.value);
          if (v > 0) state.stratK[i] = v; else delete state.stratK[i];
          renderStrategy();
        });
        lab.appendChild(inp); el.appendChild(lab);
      }
      var pr = document.createElement('span'); pr.className = 'leg-price num'; el.appendChild(pr);
      box.appendChild(el);
    });
    renderStrategy();
  }

  function renderStrategy() {
    var o = optInputs();
    var ok = o.S > 0 && o.T > 0 && o.sigma > 0 && isFinite(o.r);
    if (!ok) {
      stratView = null;
      ['st-cost', 'st-maxp', 'st-maxl', 'st-be', 'st-prob'].forEach(function (id) { $(id).textContent = '—'; });
      say('st-take', null);
      prep($('st-canvas'));
      return;
    }
    var legs = stratLegs(o.S), res = QL.strategy(legs, o.S, o.T, o.r, o.sigma);
    var step = QL.niceStep(o.S * 0.025);
    [].forEach.call($('st-legs').children, function (el, i) {
      var inp = el.querySelector('input');
      if (inp) {
        inp.step = step;
        if (!(state.stratK[i] > 0) && document.activeElement !== inp) inp.value = +legs[i].k.toFixed(4);
      }
      el.querySelector('.leg-price').textContent = '@ ' + fmtPrice(res.prices[i]);
    });
    $('st-cost-label').textContent = res.cost >= 0 ? 'Net cost' : 'Net credit';
    $('st-cost').textContent = fmtAmt(res.cost, o.S);
    $('st-maxp').textContent = res.maxP === Infinity ? 'Unlimited' : fmtPL(res.maxP, o.S);
    $('st-maxl').textContent = res.maxL === -Infinity ? 'Unlimited' : fmtPL(res.maxL, o.S);
    $('st-be').textContent = res.bes.length ? res.bes.map(fmtPrice).join(' / ') : '—';
    $('st-prob').textContent = fmtPct(res.prob);
    stratView = { res: res, S: o.S, legs: legs };
    stratTake(res, o.S);
    drawStrategy();
  }
  function stratTake(res, S) {
    var unit = unitWord(), parts, amt = function (v) { return fmtAmt(v, S); };
    if (res.cost > 0.005) parts = ['You pay ', [amt(res.cost)], ' per ' + unit + ' up front'];
    else if (res.cost < -0.005) parts = ['You collect ', [amt(res.cost)], ' per ' + unit + ' up front'];
    else parts = ['It costs nothing up front'];
    if (res.zones.length) {
      parts.push(', and it makes money if the price ends ');
      res.zones.forEach(function (z, i) {
        if (i) parts.push(' or ');
        if (!(z[0] > 0) && z[1] === Infinity) parts.push('anywhere');
        else if (!(z[0] > 0)) parts.push('below ', [fmtPrice(z[1])]);
        else if (z[1] === Infinity) parts.push('above ', [fmtPrice(z[0])]);
        else parts.push('between ', [fmtPrice(z[0])], ' and ', [fmtPrice(z[1])]);
      });
      parts.push(' at expiry; the model puts that at a ', [fmtPct(res.prob, false, 0)], ' chance.');
    } else parts.push(', but with these strikes it cannot make money at expiry.');
    if (res.maxL === -Infinity) parts.push(' The possible loss has no limit');
    else if (res.maxL < -0.005) parts.push(' The most you can lose is ', [amt(res.maxL)]);
    else parts.push(' It cannot lose money at expiry');
    if (res.maxP === Infinity) parts.push(', and there is no cap on the gain.');
    else if (res.maxP > 0.005) parts.push(', and the most you can make is ', [amt(res.maxP)], '.');
    else parts.push('.');
    say('st-take', parts);
  }

  var stratGeom = null;
  function drawStrategy(hoverS) {
    var v = stratView; if (!v) return;
    var res = v.res, P = prep($('st-canvas')), ctx = P.ctx, col = palette();
    var m = { l: 6, r: 58, t: 12, b: 24 }, pw = P.w - m.l - m.r, ph = P.h - m.t - m.b;
    var ks = v.legs.filter(function (l) { return l.kind !== 'stock'; }).map(function (l) { return l.k; });
    var x0 = Math.min.apply(null, ks.concat(v.S)) * 0.75, x1 = Math.max.apply(null, ks.concat(v.S)) * 1.25;
    var xs = [x0].concat(res.knots.filter(function (k) { return k > x0 && k < x1; }), [x1]);
    var now = [], lo = 0, hi = 0, i;
    for (i = 0; i <= 120; i++) { var s = x0 + (x1 - x0) * i / 120, pv = res.plNow(s); now.push([s, pv]); lo = Math.min(lo, pv); hi = Math.max(hi, pv); }
    xs.forEach(function (s) { var e = res.plExp(s); lo = Math.min(lo, e); hi = Math.max(hi, e); });
    var pad = (hi - lo) * 0.1 || 1; lo -= pad; hi += pad;
    var x = function (s) { return m.l + (s - x0) / (x1 - x0) * pw; };
    var y = function (p) { return m.t + (1 - (p - lo) / (hi - lo)) * ph; };
    var tk = QL.ticks(lo, hi, 5), step = tk.length > 1 ? tk[1] - tk[0] : 1;
    gridY(ctx, tk, y, m.l, m.l + pw, m.l + pw + 8, step, col);
    var xt = QL.ticks(x0, x1, P.w < 520 ? 4 : 8), xstep = xt.length > 1 ? xt[1] - xt[0] : 1;
    ctx.fillStyle = col.muted; ctx.textAlign = 'center';
    xt.forEach(function (s) { if (x(s) > m.l + 16 && x(s) < m.l + pw - 16) ctx.fillText(fmtAxis(s, xstep), x(s), P.h - 10); });

    // zero line
    var y0 = Math.round(y(0)) + 0.5;
    ctx.strokeStyle = col.muted; ctx.lineWidth = 1; ctx.globalAlpha = 0.7;
    ctx.beginPath(); ctx.moveTo(m.l, y0); ctx.lineTo(m.l + pw, y0); ctx.stroke(); ctx.globalAlpha = 1;

    var labels = [];
    var vline = function (s, color, label, dash, row, preferLeft) {
      if (s <= x0 || s >= x1) return;
      var px = Math.round(x(s)) + 0.5, tw = ctx.measureText(label).width;
      ctx.strokeStyle = color; ctx.lineWidth = 1.2; ctx.setLineDash(dash);
      ctx.beginPath(); ctx.moveTo(px, m.t); ctx.lineTo(px, m.t + ph); ctx.stroke(); ctx.setLineDash([]);
      var right = preferLeft ? px - 6 - tw < m.l : px + 6 + tw < m.l + pw;
      if (label) labels.push({ text: label, color: color, w: tw, x: right ? px + 6 : px - 6 - tw, y: m.t + 8 + row * 16 });
    };
    vline(v.S, col.muted, 'Spot ' + fmtPrice(v.S), [2, 3], 0);
    // with two breakevens the lower one is labelled on its left, away from the profit zone
    // (on narrow screens the lines stay unlabelled; the values are in the stats below)
    res.bes.forEach(function (be, n) { vline(be, col.amber, P.w < 520 ? '' : 'Breakeven ' + fmtPrice(be), [5, 4], 1, res.bes.length > 1 && n === 0); });

    // P/L at expiry: green above zero, red below
    var expPath = function () { ctx.beginPath(); xs.forEach(function (s, n) { if (n) ctx.lineTo(x(s), y(res.plExp(s))); else ctx.moveTo(x(s), y(res.plExp(s))); }); };
    [[m.t, y0 - m.t, col.up], [y0, m.t + ph - y0, col.down]].forEach(function (z) {
      if (z[1] <= 0) return;
      ctx.save(); ctx.beginPath(); ctx.rect(m.l, z[0], pw, z[1]); ctx.clip();
      expPath(); ctx.lineTo(x(x1), y0); ctx.lineTo(x(x0), y0); ctx.closePath();
      ctx.fillStyle = z[2]; ctx.globalAlpha = 0.13; ctx.fill(); ctx.globalAlpha = 1;
      expPath(); ctx.strokeStyle = z[2]; ctx.lineWidth = 2; ctx.lineJoin = 'round'; ctx.stroke();
      ctx.restore();
    });
    // P/L today
    ctx.save(); ctx.beginPath(); ctx.rect(m.l, m.t, pw, ph); ctx.clip();
    ctx.beginPath(); now.forEach(function (pt, n) { if (n) ctx.lineTo(x(pt[0]), y(pt[1])); else ctx.moveTo(x(pt[0]), y(pt[1])); });
    ctx.strokeStyle = col.accent; ctx.lineWidth = 1.6; ctx.setLineDash([6, 4]); ctx.stroke(); ctx.setLineDash([]);
    ctx.restore();

    labels.forEach(function (l) {
      ctx.fillStyle = col.surface; ctx.globalAlpha = 0.85; ctx.fillRect(l.x - 3, l.y - 8, l.w + 6, 16); ctx.globalAlpha = 1;
      ctx.fillStyle = l.color; ctx.textAlign = 'left'; ctx.fillText(l.text, l.x, l.y);
    });

    stratGeom = { m: m, pw: pw, x0: x0, x1: x1, x: x, w: P.w };
    if (hoverS != null) {
      var hx = x(hoverS), e = res.plExp(hoverS);
      ctx.strokeStyle = col.muted; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(hx + 0.5, m.t); ctx.lineTo(hx + 0.5, m.t + ph); ctx.stroke();
      ctx.fillStyle = col.surface; ctx.strokeStyle = e >= 0 ? col.up : col.down; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(hx, y(e), 4, 0, 7); ctx.fill(); ctx.stroke();
    }
  }
  function stratHover(e) {
    if (!stratGeom || !stratView) return;
    var g = stratGeom, r = $('st-canvas').getBoundingClientRect();
    var f = Math.max(0, Math.min(1, (e.clientX - r.left - g.m.l) / g.pw)), s = g.x0 + f * (g.x1 - g.x0);
    drawStrategy(s);
    var tip = $('st-tip'), pl = stratView.res.plExp(s);
    tip.innerHTML = '';
    var b = document.createElement('b'); b.textContent = fmtPL(pl); b.className = pl >= 0 ? 'up' : 'down'; tip.appendChild(b);
    var sp = document.createElement('span');
    sp.textContent = ' at expiry · today ' + fmtPL(stratView.res.plNow(s)) + ' · price ' + fmtPrice(s);
    tip.appendChild(sp);
    tip.hidden = false;
    var tw = tip.offsetWidth, px = g.x(s) + 12;
    if (px + tw > g.w - 4) px = g.x(s) - tw - 12;
    tip.style.left = Math.max(4, px) + 'px';
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
  function redraw() { drawHistory(); drawVol(); drawMC(); if (state.data) renderOptions(); }

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

    var vc = $('vol-canvas');
    vc.addEventListener('mousemove', volHover);
    vc.addEventListener('touchstart', function (e) { if (e.touches[0]) volHover(e.touches[0]); }, { passive: true });
    vc.addEventListener('touchmove', function (e) { if (e.touches[0]) volHover(e.touches[0]); }, { passive: true });
    vc.addEventListener('mouseleave', function () { $('vol-tip').hidden = true; drawVol(); });

    var rerun = debounce(runMC, 90);
    $('mc-paths').addEventListener('input', function () { $('mc-paths-out').textContent = (+this.value).toLocaleString('en-US'); rerun(); });
    $('mc-days').addEventListener('input', function () {
      $('mc-days-out').textContent = this.value + (state.data && state.data.ann === 365 ? ' days' : ' trading days'); rerun();
    });
    $('mc-vol').addEventListener('input', rerun);
    $('mc-drift').addEventListener('input', rerun);
    $('mc-target').addEventListener('input', function () { drawMC(); mcStats(); });
    $('mc-run').addEventListener('click', function () { runMC(true); });
    $('mc-use-hist').addEventListener('click', function () { setNum('mc-drift', Math.max(-100, Math.min(200, state.histDrift * 100)), 1); runMC(true); });
    $('mc-use-rn').addEventListener('click', function () { var r = num('o-rate'); setNum('mc-drift', isFinite(r) ? r : 0, 2); runMC(true); });
    $('mc-use-zero').addEventListener('click', function () { setNum('mc-drift', 0, 1); runMC(true); });

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
    document.querySelectorAll('#st-presets .chip').forEach(function (c) { c.addEventListener('click', function () { setStrat(c.dataset.strat); }); });
    var sc = $('st-canvas');
    sc.addEventListener('mousemove', stratHover);
    sc.addEventListener('touchstart', function (e) { if (e.touches[0]) stratHover(e.touches[0]); }, { passive: true });
    sc.addEventListener('touchmove', function (e) { if (e.touches[0]) stratHover(e.touches[0]); }, { passive: true });
    sc.addEventListener('mouseleave', function () { $('st-tip').hidden = true; drawStrategy(); });
    setStrat(state.strat);

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
      memKey = null; store.del(KEY_STORE); state.mode = serverKey ? 'live' : 'sample'; $('key-input').value = ''; cache = {};
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

    // On a deployment with a shared key, switch from sample data to live prices.
    if (!getKey() && location.protocol.indexOf('http') === 0) {
      fetch('/api/td?ping=1').then(function (r) { return r.ok ? r.json() : null; }).then(function (j) {
        if (j && j.ok && !getKey() && state.mode === 'sample') { serverKey = true; state.mode = 'live'; loadSymbol(state.symbol); }
        else if (j && j.ok) serverKey = true;
      }).catch(function () {});
    }
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init); else init();
})();
