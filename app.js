/* =============================================================
   Personal TradingView — engine v3
   Architecture: real data + cached indicator computation +
   separate base/overlay canvases (crosshair never recomputes TA)
   ============================================================= */

var VERSION = '3.1.0';
var AXIS_W = 58;
var AXIS_H = 20;
var VOL_H = 68;
var OSC_H = 118;

/* ---------------- Universe ----------------
   Two providers, measured 2026-11-27 from this network:
     gate  — api.gateio.ws  · HTTP 200 · ACAO:* · 1000 real OHLCV bars · all 8 intervals
     cg    — api.coingecko.com · HTTP 200 · ACAO:* · price ticks only (5m native, 1h beyond 1 day)
   Blocked here (so never tried): binance 451, bybit 403, okx 403, coinbase 403, kraken 403.
   `gate` is primary because it returns genuine open/high/low/volume; `cg` only derives
   high/low from consecutive ticks, which is acceptable for coarse frames, not for 1m. */
var SYMBOLS = {
  'pax-gold':    { label: 'GOLD (PAXG/USDT)', dec: 2, gate: 'PAXG_USDT', cg: 'pax-gold',    ref: 3670 },
  'tether-gold': { label: 'GOLD (XAUT/USDT)', dec: 2, gate: 'XAUT_USDT', cg: 'tether-gold', ref: 3675 },
  'bitcoin':     { label: 'BTC/USDT',         dec: 2, gate: 'BTC_USDT',  cg: 'bitcoin',     ref: 61800 },
  'ethereum':    { label: 'ETH/USDT',         dec: 2, gate: 'ETH_USDT',  cg: 'ethereum',    ref: 2100 },
  'solana':      { label: 'SOL/USDT',         dec: 3, gate: 'SOL_USDT',  cg: 'solana',      ref: 145 },
  'ripple':      { label: 'XRP/USDT',         dec: 4, gate: 'XRP_USDT',  cg: 'ripple',      ref: 1.4 },
  'binancecoin': { label: 'BNB/USDT',         dec: 2, gate: 'BNB_USDT',  cg: 'binancecoin', ref: 620 },
  'dogecoin':    { label: 'DOGE/USDT',        dec: 5, gate: 'DOGE_USDT', cg: 'dogecoin',    ref: 0.12 },
  'cardano':     { label: 'ADA/USDT',         dec: 4, gate: 'ADA_USDT',  cg: 'cardano',     ref: 0.55 }
};

/* gate = Gate.io interval id · sec = bar seconds · cgDays = CoinGecko window
   cgMin = smallest bar spacing CoinGecko can actually produce for that window */
var TFS = {
  '1m':  { gate: '1m',  sec: 60,    cgDays: 1,  cgMin: 300 },
  '3m':  { gate: '3m',  sec: 180,   cgDays: 1,  cgMin: 300 },
  '5m':  { gate: '5m',  sec: 300,   cgDays: 1,  cgMin: 300 },
  '15m': { gate: '15m', sec: 900,   cgDays: 1,  cgMin: 300 },
  '30m': { gate: '30m', sec: 1800,  cgDays: 1,  cgMin: 300 },
  '1h':  { gate: '1h',  sec: 3600,  cgDays: 7,  cgMin: 3600 },
  '4h':  { gate: '4h',  sec: 14400, cgDays: 30, cgMin: 3600 },
  '1D':  { gate: '1d',  sec: 86400, cgDays: 90, cgMin: 3600 }
};
var TF_ORDER = ['1m', '3m', '5m', '15m', '30m', '1h', '4h', '1D'];

/* ---------------- TA helpers (aligned, null-padded) ---------------- */
function pad(n) { var a = [], i; for (i = 0; i < n; i++) a.push(null); return a; }

function sma(src, len) {
  var out = pad(src.length), sum = 0, i;
  for (i = 0; i < src.length; i++) {
    if (src[i] == null) { out[i] = null; continue; }
    sum += src[i];
    if (i >= len) sum -= src[i - len];
    out[i] = i >= len - 1 ? sum / len : null;
  }
  return out;
}

function ema(src, len) {
  var out = pad(src.length), k = 2 / (len + 1), prev = null, i;
  for (i = 0; i < src.length; i++) {
    if (src[i] == null) continue;
    prev = prev == null ? src[i] : src[i] * k + prev * (1 - k);
    out[i] = i >= len - 1 ? prev : null;
  }
  return out;
}

function stdev(src, len) {
  var out = pad(src.length), i, j, s, m, v;
  for (i = len - 1; i < src.length; i++) {
    s = 0; m = 0;
    for (j = 0; j < len; j++) { if (src[i - j] == null) { m = null; break; } m += src[i - j]; }
    if (m == null) continue;
    m /= len; v = 0;
    for (j = 0; j < len; j++) v += Math.pow(src[i - j] - m, 2);
    out[i] = Math.sqrt(v / len);
  }
  return out;
}

function rsi(src, len) {
  var out = pad(src.length), ag = 0, al = 0, i, ch, g, l;
  for (i = 1; i < src.length; i++) {
    if (src[i] == null || src[i - 1] == null) continue;
    ch = src[i] - src[i - 1];
    g = ch > 0 ? ch : 0; l = ch < 0 ? -ch : 0;
    if (i <= len) { ag += g; al += l; if (i === len) { ag /= len; al /= len; out[i] = al === 0 ? 100 : 100 - 100 / (1 + ag / al); } }
    else { ag = (ag * (len - 1) + g) / len; al = (al * (len - 1) + l) / len; out[i] = al === 0 ? 100 : 100 - 100 / (1 + ag / al); }
  }
  return out;
}

function atrOf(cs, len) {
  var tr = pad(cs.length), i;
  for (i = 0; i < cs.length; i++) {
    if (i === 0) tr[i] = cs[i].high - cs[i].low;
    else tr[i] = Math.max(cs[i].high - cs[i].low, Math.abs(cs[i].high - cs[i - 1].close), Math.abs(cs[i].low - cs[i - 1].close));
  }
  return sma(tr, len);
}

function hh(src, len) {
  var out = pad(src.length), i, j, m;
  for (i = len - 1; i < src.length; i++) {
    m = -Infinity;
    for (j = 0; j < len; j++) if (src[i - j] != null) m = Math.max(m, src[i - j]);
    out[i] = m === -Infinity ? null : m;
  }
  return out;
}

function ll(src, len) {
  var out = pad(src.length), i, j, m;
  for (i = len - 1; i < src.length; i++) {
    m = Infinity;
    for (j = 0; j < len; j++) if (src[i - j] != null) m = Math.min(m, src[i - j]);
    out[i] = m === Infinity ? null : m;
  }
  return out;
}

function shift(a, n) {
  var out = pad(a.length), i;
  for (i = 0; i < a.length - n; i++) out[i + n] = a[i];
  return out;
}

function demarker(cs, len) {
  var up = pad(cs.length), dn = pad(cs.length), i;
  for (i = 1; i < cs.length; i++) {
    up[i] = Math.max(cs[i].high - cs[i - 1].high, 0);
    dn[i] = Math.max(cs[i - 1].low - cs[i].low, 0);
  }
  var su = sma(up, len), sd = sma(dn, len), out = pad(cs.length);
  for (i = 0; i < cs.length; i++) {
    if (su[i] == null || sd[i] == null) continue;
    var den = su[i] + sd[i];
    out[i] = den > 0 ? su[i] / den : 0.5;
  }
  return out;
}

function crossUp(a, b) {
  var out = [], i;
  for (i = 0; i < a.length; i++) out.push(i > 0 && a[i] != null && b[i] != null && a[i - 1] != null && b[i - 1] != null && a[i - 1] <= b[i - 1] && a[i] > b[i]);
  return out;
}

/* ---------------- Volume profile core (shared by B2) ---------------- */
function volumeProfile(cs, lookback, bins, vaPct) {
  var n = Math.min(cs.length, lookback);
  if (n < 10) return null;
  var seg = cs.slice(cs.length - n);
  var minP = Infinity, maxP = -Infinity, i;
  for (i = 0; i < seg.length; i++) { minP = Math.min(minP, seg[i].low); maxP = Math.max(maxP, seg[i].high); }
  if (!(maxP > minP)) return null;
  var bw = (maxP - minP) / bins;
  var vb = new Array(bins), b;
  for (b = 0; b < bins; b++) vb[b] = 0;
  for (i = 0; i < seg.length; i++) {
    var c = seg[i];
    var b0 = Math.max(0, Math.min(bins - 1, Math.floor((c.low - minP) / bw)));
    var b1 = Math.max(0, Math.min(bins - 1, Math.floor((c.high - minP) / bw)));
    var per = (c.volume || 1) / (b1 - b0 + 1);
    for (b = b0; b <= b1; b++) vb[b] += per;
  }
  var total = 0, poc = 0, mv = -1;
  for (b = 0; b < bins; b++) {
    total += vb[b];
    if (vb[b] > mv) { mv = vb[b]; poc = b; }
  }
  var used = new Array(bins), acc = vb[poc], vLo = poc, vHi = poc, tgt = total * vaPct / 100, guard = 0;
  for (b = 0; b < bins; b++) used[b] = false;
  used[poc] = true;
  while (acc < tgt && guard < bins) {
    var bi = -1, bv = -1;
    for (b = 0; b < bins; b++) if (!used[b] && vb[b] > bv) { bv = vb[b]; bi = b; }
    if (bi < 0) break;
    used[bi] = true; acc += bv;
    vLo = Math.min(vLo, bi); vHi = Math.max(vHi, bi); guard++;
  }
  return {
    vah: minP + (vHi + 1) * bw,
    val: minP + vLo * bw,
    poc: minP + (poc + 0.5) * bw,
    bins: vb.map(function (v, k) { return { price: minP + (k + 0.5) * bw, vol: v }; }),
    maxVol: mv, minP: minP, bw: bw
  };
}

/* ---------------- Indicator registry ---------------- */
var DEFS = {
  sma: {
    name: 'Moving Average (SMA)', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 20, min: 1, max: 400 }],
    compute: function (cs, p) {
      var c = cs.close;
      return { series: [{ title: 'SMA ' + p.len, data: sma(c, p.len), color: '#2962ff', width: 2 }] };
    }
  },
  ema: {
    name: 'EMA', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 21, min: 1, max: 400 }],
    compute: function (cs, p) {
      return { series: [{ title: 'EMA ' + p.len, data: ema(cs.close, p.len), color: '#ff9800', width: 2 }] };
    }
  },
  bbands: {
    name: 'Bollinger Bands', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 20, min: 2, max: 200 }, { k: 'mult', l: 'StdDev mult', t: 'float', d: 2, min: 0.5, max: 5, step: 0.1 }],
    compute: function (cs, p) {
      var mid = sma(cs.close, p.len), sd = stdev(cs.close, p.len);
      var up = [], lo = [], i;
      for (i = 0; i < cs.length; i++) {
        up.push(mid[i] == null || sd[i] == null ? null : mid[i] + sd[i] * p.mult);
        lo.push(mid[i] == null || sd[i] == null ? null : mid[i] - sd[i] * p.mult);
      }
      return {
        series: [
          { title: 'BB Upper', data: up, color: '#7e57c2', width: 1 },
          { title: 'BB Basis', data: mid, color: '#b0bec5', width: 1, dash: [3, 3] },
          { title: 'BB Lower', data: lo, color: '#7e57c2', width: 1, fillTo: lo, fillFrom: up, fillColor: 'rgba(126,87,194,0.10)' }
        ]
      };
    }
  },
  supertrend: {
    name: 'SuperTrend', pane: 'price',
    params: [{ k: 'atrLen', l: 'ATR length', t: 'int', d: 10, min: 1, max: 100 }, { k: 'mult', l: 'Factor', t: 'float', d: 3, min: 0.5, max: 10, step: 0.1 }],
    compute: function (C, p, cs) {
      var a = atrOf(cs, p.atrLen), line = [], dir = [], i;
      for (i = 0; i < cs.length; i++) {
        if (a[i] == null) { line.push(null); dir.push(null); continue; }
        var hl2 = (cs[i].high + cs[i].low) / 2;
        var ub = hl2 + p.mult * a[i], lb = hl2 - p.mult * a[i];
        var prev = line[i - 1];
        if (prev == null) { line.push(ub); dir.push(1); continue; }
        if (cs[i].close > prev) { dir.push(1); line.push(lb); }
        else { dir.push(-1); line.push(ub); }
      }
      var up = [], dn = [], j;
      for (j = 0; j < cs.length; j++) { up.push(dir[j] === 1 ? line[j] : null); dn.push(dir[j] === -1 ? line[j] : null); }
      return {
        series: [
          { title: 'ST Up', data: up, color: '#089981', width: 2 },
          { title: 'ST Down', data: dn, color: '#f23645', width: 2 }
        ]
      };
    }
  },
  vwap: {
    name: 'VWAP', pane: 'price',
    params: [],
    compute: function (C, p, cs) {
      var out = [], pv = 0, vv = 0, i;
      for (i = 0; i < cs.length; i++) {
        var tp = (cs[i].high + cs[i].low + cs[i].close) / 3;
        pv += tp * (cs[i].volume || 1); vv += (cs[i].volume || 1);
        out.push(vv > 0 ? pv / vv : null);
      }
      return { series: [{ title: 'VWAP', data: out, color: '#e91e63', width: 2, dash: [4, 2] }] };
    }
  },
  volume: {
    name: 'Volume', pane: 'vol',
    params: [{ k: 'maLen', l: 'Volume MA', t: 'int', d: 20, min: 0, max: 100 }],
    compute: function (C, p, cs) {
      var v = cs.map(function (c) { return c.volume; });
      var s = [{ title: 'Volume', data: v, color: '#26a69a', width: 1, bars: true }];
      if (p.maLen > 0) s.push({ title: 'Vol MA ' + p.maLen, data: sma(v, p.maLen), color: '#ff9800', width: 1 });
      return { series: s };
    }
  },
  rsi: {
    name: 'RSI', pane: 'osc', scale: '0-100',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 14, min: 2, max: 100 }, { k: 'ob', l: 'Overbought', t: 'float', d: 70, min: 50, max: 99 }, { k: 'os', l: 'Oversold', t: 'float', d: 30, min: 1, max: 50 }],
    compute: function (cs, p) {
      return {
        series: [{ title: 'RSI ' + p.len, data: rsi(cs.close, p.len), color: '#e91e63', width: 2 }],
        levels: [{ price: p.ob, color: 'rgba(242,54,69,0.55)', title: 'OB' }, { price: p.os, color: 'rgba(8,153,129,0.55)', title: 'OS' }]
      };
    }
  },
  stoch: {
    name: 'Stochastic', pane: 'osc', scale: '0-100',
    params: [{ k: 'kLen', l: '%K length', t: 'int', d: 14, min: 1, max: 100 }, { k: 'dLen', l: '%D length', t: 'int', d: 3, min: 1, max: 50 }],
    compute: function (C, p, cs) {
      var h = cs.map(function (c) { return c.high; }), l = cs.map(function (c) { return c.low; });
      var hhv = hh(h, p.kLen), llv = ll(l, p.kLen), k = [], i;
      for (i = 0; i < cs.length; i++) {
        if (hhv[i] == null || llv[i] == null || hhv[i] === llv[i]) { k.push(null); continue; }
        k.push((cs[i].close - llv[i]) / (hhv[i] - llv[i]) * 100);
      }
      return {
        series: [
          { title: '%K', data: k, color: '#2962ff', width: 2 },
          { title: '%D', data: sma(k, p.dLen), color: '#ff9800', width: 1.5 }
        ],
        levels: [{ price: 80, color: 'rgba(242,54,69,0.5)' }, { price: 20, color: 'rgba(8,153,129,0.5)' }]
      };
    }
  },
  macd: {
    name: 'MACD', pane: 'osc', scale: 'auto',
    params: [{ k: 'fast', l: 'Fast', t: 'int', d: 12, min: 1, max: 100 }, { k: 'slow', l: 'Slow', t: 'int', d: 26, min: 2, max: 200 }, { k: 'sig', l: 'Signal', t: 'int', d: 9, min: 1, max: 50 }],
    compute: function (cs, p) {
      var f = ema(cs.close, p.fast), s = ema(cs.close, p.slow), line = [], i;
      for (i = 0; i < cs.length; i++) line.push(f[i] == null || s[i] == null ? null : f[i] - s[i]);
      var sigl = smaSignal(line, p.sig), hist = [];
      for (i = 0; i < cs.length; i++) hist.push(line[i] == null || sigl[i] == null ? null : line[i] - sigl[i]);
      return {
        series: [
          { title: 'MACD', data: line, color: '#2962ff', width: 2 },
          { title: 'Signal', data: sigl, color: '#ff9800', width: 1.5 },
          { title: 'Hist', data: hist, color: '#787b86', width: 1, bars: true }
        ],
        levels: [{ price: 0, color: 'rgba(120,123,134,0.5)' }]
      };
    }
  },
  demarker: {
    name: 'DeMarker', pane: 'osc', scale: '0-1',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 7, min: 2, max: 100 }, { k: 'sigLen', l: 'Signal EMA', t: 'int', d: 3, min: 1, max: 50 }, { k: 'ob', l: 'Overbought', t: 'float', d: 0.8, min: 0.5, max: 0.99, step: 0.01 }, { k: 'os', l: 'Oversold', t: 'float', d: 0.2, min: 0.01, max: 0.5, step: 0.01 }],
    compute: function (C, p, cs) {
      var dm = demarker(cs, p.len);
      return {
        series: [
          { title: 'DeMarker ' + p.len, data: dm, color: '#2962ff', width: 2 },
          { title: 'Signal EMA ' + p.sigLen, data: ema(dm, p.sigLen), color: '#ff9800', width: 1.5 }
        ],
        levels: [{ price: p.ob, color: 'rgba(242,54,69,0.55)' }, { price: p.os, color: 'rgba(8,153,129,0.55)' }]
      };
    }
  },
  b2: {
    name: 'B2 — VP Edge + DeMarker gate', pane: 'price',
    params: [
      { k: 'lookback', l: 'Profile lookback (bars)', t: 'int', d: 120, min: 20, max: 500 },
      { k: 'bins', l: 'Price bins', t: 'int', d: 50, min: 10, max: 200 },
      { k: 'vaPct', l: 'Value area %', t: 'float', d: 70, min: 50, max: 95 },
      { k: 'dmLen', l: 'DeMarker length', t: 'int', d: 7, min: 2, max: 100 },
      { k: 'sigLen', l: 'Signal EMA', t: 'int', d: 3, min: 1, max: 50 },
      { k: 'ob', l: 'Overbought', t: 'float', d: 0.8, min: 0.5, max: 0.99, step: 0.01 },
      { k: 'os', l: 'Oversold', t: 'float', d: 0.2, min: 0.01, max: 0.5, step: 0.01 },
      { k: 'nearPct', l: 'Gate distance %', t: 'float', d: 0.25, min: 0.05, max: 2, step: 0.05 },
      { k: 'showLevels', l: 'Draw VAH/VAL/POC', t: 'bool', d: true }
    ],
    compute: function (C, p, cs) {
      var vp = volumeProfile(cs, p.lookback, p.bins, p.vaPct);
      var dm = demarker(cs, p.dmLen), sg = ema(dm, p.sigLen);
      var res = { series: [], levels: [], markers: [] };
      if (vp && p.showLevels) {
        res.levels.push({ price: vp.vah, color: '#ff9800', title: 'VAH', tag: true });
        res.levels.push({ price: vp.val, color: '#2196f3', title: 'VAL', tag: true });
        res.levels.push({ price: vp.poc, color: '#9e9e9e', title: 'POC' });
        var gate = p.nearPct / 100;
        for (var i = 2; i < cs.length; i++) {
          var c = cs[i];
          var near = Math.abs(c.close - vp.val) / c.close < gate || Math.abs(c.close - vp.vah) / c.close < gate;
          if (!near) continue;
          if (dm[i] != null && dm[i] < p.os + 0.05 && dm[i] > dm[i - 1]) res.markers.push({ i: i, kind: 'buy', price: c.low, text: 'L' });
          else if (dm[i] != null && dm[i] > p.ob - 0.05 && dm[i] < dm[i - 1]) res.markers.push({ i: i, kind: 'sell', price: c.high, text: 'S' });
        }
        res.vp = vp;
      }
      return res;
    }
  },
  custom: {
    name: 'Custom formula', pane: 'price', custom: true,
    params: [
      { k: 'expr', l: 'Formula', t: 'expr', d: 'ema($close,21)' },
      { k: 'color', l: 'Colour', t: 'color', d: '#00e5ff' },
      { k: 'width', l: 'Width', t: 'int', d: 2, min: 1, max: 6 }
    ],
    compute: function (C, p, cs) {
      var out = evalExpr(p.expr, cs);
      return { series: [{ title: 'f: ' + short(p.expr, 28), data: out, color: p.color, width: p.width }] };
    }
  }
};

function smaSignal(a, n) { return ema(a, n); }
function short(s, n) { return s.length > n ? s.slice(0, n) + '…' : s; }

/* ---------------- Formula engine ----------------
   Pine-like semantics, evaluated bar by bar:
     close / high / low / open / volume / hl2 / atr   -> current-bar scalar
     close[1]                                         -> history (previous bars)
     ema($close, 21)  sma($close,14)  rsi($close,14)  -> functions take the array ($)
   Any bare identifier that is not a series name resolves from the scope
   (numbers, Math helpers, i, time). Bad input throws, never blanks silently. */
var SERIES_NAMES = ['open', 'high', 'low', 'close', 'volume', 'hl2', 'atr'];

function seriesArrays(cs) {
  return {
    open: cs.map(function (c) { return c.open; }),
    high: cs.map(function (c) { return c.high; }),
    low: cs.map(function (c) { return c.low; }),
    close: cs.map(function (c) { return c.close; }),
    volume: cs.map(function (c) { return c.volume; }),
    hl2: cs.map(function (c) { return (c.high + c.low) / 2; }),
    atr: atrOf(cs, 14)
  };
}

function transformExpr(src) {
  var s = String(src);
  /* $name -> A.name (array accessor, for functions) */
  s = s.replace(/\$\s*([A-Za-z_]\w*)/g, function (m, n) {
    return SERIES_NAMES.indexOf(n) >= 0 ? 'A.' + n : m;
  });
  /* name[2] -> H("name",2) (history), but not A.name[...] and not array literals */
  s = s.replace(/(^|[^\w$."])(open|high|low|close|volume|hl2|atr)\s*\[\s*(\d+)\s*\]/g, function (m, pre, n, k) {
    return pre + 'H("' + n + '",' + k + ')';
  });
  /* bare name -> V("name") (current-bar scalar), skipping calls and already-transformed */
  s = s.replace(/(^|[^\w$."])(open|high|low|close|volume|hl2|atr)\b(?!\s*[\[\("])/g, function (m, pre, n) {
    return pre + 'V("' + n + '")';
  });
  return s;
}

function evalExpr(expr, cs) {
  if (!expr || !String(expr).trim()) throw new Error('formula: empty expression');
  var A = seriesArrays(cs);
  var src = transformExpr(expr);
  var iCur = 0;
  var scope = {
    A: A,
    V: function (n) { var a = A[n]; return a ? a[iCur] : null; },
    H: function (n, k) { var a = A[n]; if (!a) return null; var j = iCur - k; return j >= 0 ? a[j] : null; },
    sma: sma, ema: ema, rsi: rsi, stdev: stdev, hh: hh, ll: ll, shift: shift, atr: atrOf(cs, 14),
    abs: Math.abs, min: Math.min, max: Math.max, sqrt: Math.sqrt, pow: Math.pow,
    floor: Math.floor, ceil: Math.ceil, round: Math.round, log: Math.log, exp: Math.exp,
    sin: Math.sin, cos: Math.cos, tan: Math.tan,
    nz: function (v, d) { return (v == null || !isFinite(v)) ? (d == null ? 0 : d) : v; },
    /* at(series, back) — pull a scalar out of a series-producing call,
       so close > at(ema($close,21)) works */
    at: function (ser, back) {
      var k = back == null ? 0 : back;
      if (Array.isArray(ser)) {
        var j = iCur - k;
        if (j < 0 || j >= ser.length) return null;
        return typeof ser[j] === 'number' && isFinite(ser[j]) ? ser[j] : null;
      }
      return typeof ser === 'number' && isFinite(ser) ? ser : null;
    },
    i: 0, bar_index: 0, time: 0
  };
  var f;
  try {
    f = new Function('__s', 'with(__s){ return (' + src + '); }');
  } catch (e) {
    throw new Error('formula: ' + ((e && e.message) || e));
  }
  var out = [], i, val, bad = 0;

  /* probe bar 0: a formula may return a whole series (e.g. ema($close,21))
     or a scalar for the current bar (e.g. close - close[1]) */
  iCur = 0; scope.i = 0; scope.bar_index = 0; scope.time = cs[0].time;
  try { val = f(scope); } catch (e) { throw new Error('formula: ' + ((e && e.message) || e)); }

  if (Array.isArray(val)) {
    var arr = [];
    for (i = 0; i < cs.length; i++) {
      var av = val[i];
      arr.push(typeof av === 'number' && isFinite(av) ? av : null);
    }
    var anyA = arr.some(function (v) { return v != null; });
    if (!anyA) throw new Error('formula: series is empty on this data');
    return arr;
  }

  for (i = 0; i < cs.length; i++) {
    iCur = i; scope.i = i; scope.bar_index = i; scope.time = cs[i].time;
    try {
      val = i === 0 ? val : f(scope);
    } catch (e) { val = null; bad++; continue; }
    if (Array.isArray(val)) { /* series mixed in: take this bar's value */
      var mv = val[i];
      out.push(typeof mv === 'number' && isFinite(mv) ? mv : null);
      continue;
    }
    out.push(typeof val === 'number' && isFinite(val) ? val : null);
  }
  if (bad === cs.length) throw new Error('formula: no bar produced a number (' + short(src, 60) + ')');

  /* Guard the classic trap: an array silently coerced in bare arithmetic
     (e.g. `rsi($close,14) > 70` compares the whole array once and yields a
     constant). A series-referencing formula that comes back flat on varying
     data is almost certainly that mistake — say so instead of plotting a lie. */
  var firstV = null, flat = true, seen = 0, varies = false, k;
  for (k = 0; k < cs.length - 1; k++) {
    if (cs[k].close !== cs[k + 1].close) { varies = true; break; }
  }
  for (k = 0; k < out.length; k++) {
    if (out[k] == null) continue;
    seen++;
    if (firstV == null) firstV = out[k];
    else if (out[k] !== firstV) { flat = false; break; }
  }
  if (flat && seen > 5 && varies && /[$A-Za-z]/.test(src) && /(\$|\b(close|high|low|open|volume|hl2|atr)\b)/.test(src)) {
    throw new Error('formula returned a flat line on varying data — wrap series calls in at(), e.g. at(ema($close,21)) or at(rsi($close,14)) > 70 ? 1 : 0');
  }
  return out;
}

/* ---------------- State ---------------- */
var state = {
  symbol: 'pax-gold',
  tf: '5m',
  candles: [],
  source: 'idle',
  provider: null,
  note: '',
  updatedAt: 0,
  offset: 0,
  visible: 70,
  active: [],
  uid: 1,
  hover: null,
  drag: null,
  computed: null,
  geo: null,
  busy: false,
  msg: ''
};

var els = {};
var baseCtx = null, ovCtx = null, dpr = 1;

/* ---------------- Geometry ---------------- */
function computeGeo() {
  var W = els.stack.clientWidth, H = els.stack.clientHeight;
  var panes = paneSet();
  var volH = panes.vol ? VOL_H : 0, oscH = panes.osc ? OSC_H : 0;
  var plotW = Math.max(60, W - AXIS_W);
  var priceH = Math.max(80, H - AXIS_H - volH - oscH);
  return {
    W: W, H: H, plotW: plotW,
    priceTop: 0, priceH: priceH,
    volTop: priceH, volH: volH,
    oscTop: priceH + volH, oscH: oscH,
    axisTop: H - AXIS_H, axisH: AXIS_H,
    panes: panes
  };
}

function paneSet() {
  var s = { price: false, vol: false, osc: false };
  state.active.forEach(function (a) { s[DEFS[a.def].pane] = true; });
  s.price = true;
  return s;
}

/* ---------------- Computation (cached) ---------------- */
function recompute() {
  var cs = state.candles;
  if (!cs.length) { state.computed = null; return; }
  var ctx = {
    length: cs.length,
    open: cs.map(function (c) { return c.open; }),
    high: cs.map(function (c) { return c.high; }),
    low: cs.map(function (c) { return c.low; }),
    close: cs.map(function (c) { return c.close; }),
    volume: cs.map(function (c) { return c.volume; })
  };
  var out = [];
  state.active.forEach(function (a) {
    var d = DEFS[a.def];
    var r = null, err = null;
    try {
      r = d.compute(ctx, a.params, cs);
    } catch (e) {
      err = String((e && e.message) || e);
      r = { series: [], levels: [], markers: [] };
    }
    if (r && r.error) err = r.error;
    out.push({ uid: a.uid, def: a.def, pane: d.pane, scale: d.scale || 'auto', title: a.title || d.name, r: r, error: err });
  });
  state.computed = out;
}

/* ---------------- Visible slice ---------------- */
function view() {
  var cs = state.candles;
  var end = Math.max(2, cs.length - state.offset);
  var start = Math.max(0, end - state.visible);
  return { start: start, end: end, slice: cs.slice(start, end), n: end - start };
}

function stepW(geo, v) { return geo.plotW / Math.max(1, v.n); }
function barX(geo, v, idx) { return idx * stepW(geo, v) + 1; }
function barW(geo, v) { return Math.max(1, stepW(geo, v) - 2); }

/* ---------------- Scales ---------------- */
function priceScale(geo, v, comps) {
  var lo = Infinity, hi = -Infinity, i;
  for (i = 0; i < v.slice.length; i++) { lo = Math.min(lo, v.slice[i].low); hi = Math.max(hi, v.slice[i].high); }
  comps.forEach(function (c) {
    if (c.pane !== 'price') return;
    (c.r.series || []).forEach(function (s) {
      for (var k = v.start; k < v.end; k++) if (s.data[k] != null) { lo = Math.min(lo, s.data[k]); hi = Math.max(hi, s.data[k]); }
    });
    (c.r.levels || []).forEach(function (L) { if (L.price != null) { lo = Math.min(lo, L.price); hi = Math.max(hi, L.price); } });
  });
  if (!isFinite(lo) || !isFinite(hi) || hi <= lo) { lo = 0; hi = 1; }
  var padv = (hi - lo) * 0.08;
  lo -= padv; hi += padv;
  return {
    lo: lo, hi: hi,
    toY: function (p) { return geo.priceTop + geo.priceH - ((p - lo) / (hi - lo)) * geo.priceH; },
    toP: function (y) { return lo + (1 - (y - geo.priceTop) / geo.priceH) * (hi - lo); }
  };
}

function volScale(geo, v) {
  var mx = 0, i;
  for (i = 0; i < v.slice.length; i++) mx = Math.max(mx, v.slice[i].volume || 0);
  mx = mx || 1;
  return {
    hi: mx,
    toY: function (p) { return geo.volTop + geo.volH - (p / mx) * geo.volH; }
  };
}

function oscScale(geo, comps, v) {
  var items = comps.filter(function (c) { return c.pane === 'osc'; });
  if (!items.length) return null;
  var fixed = items[0].scale;
  if (fixed === '0-1') return { lo: 0, hi: 1, toY: function (p) { return geo.oscTop + geo.oscH - p * geo.oscH; } };
  if (fixed === '0-100') return { lo: 0, hi: 100, toY: function (p) { return geo.oscTop + geo.oscH - (p / 100) * geo.oscH; } };
  var lo = Infinity, hi = -Infinity;
  items.forEach(function (c) {
    (c.r.series || []).forEach(function (s) {
      for (var k = v.start; k < v.end; k++) if (s.data[k] != null) { lo = Math.min(lo, s.data[k]); hi = Math.max(hi, s.data[k]); }
    });
  });
  if (!isFinite(lo) || !isFinite(hi)) { lo = 0; hi = 1; }
  if (hi === lo) { hi += 1; lo -= 1; }
  var pd = (hi - lo) * 0.12; lo -= pd; hi += pd;
  return { lo: lo, hi: hi, toY: function (p) { return geo.oscTop + geo.oscH - ((p - lo) / (hi - lo)) * geo.oscH; } };
}

/* ---------------- Formatting ---------------- */
function dec() { return (SYMBOLS[state.symbol] && SYMBOLS[state.symbol].dec) || 2; }
function fmt(n) { return n == null || !isFinite(n) ? '—' : n.toFixed(dec()); }
function fmtAxis(n) {
  if (n == null || !isFinite(n)) return '—';
  var d = dec();
  return Math.abs(n) >= 1000 ? n.toFixed(Math.min(1, d)) : n.toFixed(d);
}
function fmtVol(n) {
  if (n == null || !isFinite(n)) return '—';
  if (n >= 1e9) return (n / 1e9).toFixed(2) + 'B';
  if (n >= 1e6) return (n / 1e6).toFixed(2) + 'M';
  if (n >= 1e3) return (n / 1e3).toFixed(1) + 'K';
  return n.toFixed(0);
}
function fmtTime(sec) {
  var d = new Date(sec * 1000);
  if (state.tf === '1D') return d.getUTCDate() + ' ' + ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'][d.getUTCMonth()];
  return ('0' + d.getUTCHours()).slice(-2) + ':' + ('0' + d.getUTCMinutes()).slice(-2);
}
function fmtFull(sec) {
  var d = new Date(sec * 1000);
  return d.getUTCFullYear() + '-' + ('0' + (d.getUTCMonth() + 1)).slice(-2) + '-' + ('0' + d.getUTCDate()).slice(-2) + ' ' + ('0' + d.getUTCHours()).slice(-2) + ':' + ('0' + d.getUTCMinutes()).slice(-2) + ' UTC';
}

/* ---------------- Base drawing ---------------- */
function drawBase() {
  var cs = state.candles;
  if (!cs.length || !state.computed) return;
  if (!state.geo) state.geo = computeGeo();
  var geo = state.geo;
  if (!geo || geo.W <= 0 || geo.H <= 0) return;
  var v = view();
  var ctx = baseCtx;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, geo.W, geo.H);
  ctx.fillStyle = '#131722';
  ctx.fillRect(0, 0, geo.W, geo.H);

  var ps = priceScale(geo, v, state.computed);
  var vs = volScale(geo, v);
  var os = oscScale(geo, state.computed, v);
  state.scales = { ps: ps, vs: vs, os: os, v: v, geo: geo };

  var bw = barW(geo, v);

  /* grid + price axis */
  ctx.font = '10px monospace';
  ctx.textBaseline = 'middle';
  var rows = 6, r, y, p;
  for (r = 0; r <= rows; r++) {
    p = ps.lo + (ps.hi - ps.lo) * (r / rows);
    y = ps.toY(p);
    ctx.strokeStyle = '#1c2130'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(geo.plotW, y); ctx.stroke();
    ctx.fillStyle = '#787b86'; ctx.textAlign = 'left';
    ctx.fillText(fmtAxis(p), geo.plotW + 5, y);
  }
  /* vertical grid + time axis */
  var tickEvery = Math.max(1, Math.round(v.n / 7));
  ctx.textAlign = 'center';
  for (r = 0; r < v.n; r += tickEvery) {
    var x = barX(geo, v, r) + bw / 2;
    ctx.strokeStyle = '#1a1f2b'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(x, 0); ctx.lineTo(x, geo.axisTop); ctx.stroke();
    ctx.fillStyle = '#787b86';
    ctx.fillText(fmtTime(v.slice[r].time), Math.min(x, geo.plotW - 24), geo.axisTop + geo.axisH / 2);
  }
  /* axis frame */
  ctx.strokeStyle = '#2a2e39'; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(geo.plotW, 0); ctx.lineTo(geo.plotW, geo.axisTop); ctx.stroke();
  ctx.beginPath(); ctx.moveTo(0, geo.axisTop); ctx.lineTo(geo.W, geo.axisTop); ctx.stroke();
  if (geo.volH) { ctx.beginPath(); ctx.moveTo(0, geo.volTop); ctx.lineTo(geo.plotW, geo.volTop); ctx.stroke(); }
  if (geo.oscH) { ctx.beginPath(); ctx.moveTo(0, geo.oscTop); ctx.lineTo(geo.plotW, geo.oscTop); ctx.stroke(); }

  /* volume pane */
  if (geo.volH) {
    state.computed.filter(function (c) { return c.pane === 'vol'; }).forEach(function (c) {
      (c.r.series || []).forEach(function (s) {
        if (s.bars) {
          for (var k = 0; k < v.n; k++) {
            var val = s.data[v.start + k];
            if (val == null) continue;
            var up = v.slice[k].close >= v.slice[k].open;
            ctx.fillStyle = up ? 'rgba(8,153,129,0.55)' : 'rgba(242,54,69,0.55)';
            var yy = vs.toY(val);
            ctx.fillRect(barX(geo, v, k), yy, bw, geo.volTop + geo.volH - yy);
          }
        } else drawLine(ctx, s, geo, v, function (p) { return vs.toY(p); });
      });
    });
    ctx.fillStyle = '#9aa0ab'; ctx.textAlign = 'left'; ctx.font = '10px sans-serif';
    ctx.fillText('Volume  ' + fmtVol(v.slice[v.n - 1].volume), 6, geo.volTop + 10);
    ctx.fillStyle = '#787b86';
    ctx.fillText(fmtAxis(vs.hi), geo.plotW + 5, geo.volTop + 10);
  }

  /* price pane: levels, series, candles, markers */
  state.computed.filter(function (c) { return c.pane === 'price'; }).forEach(function (c) {
    (c.r.levels || []).forEach(function (L) {
      if (L.price == null) return;
      var yy = ps.toY(L.price);
      ctx.strokeStyle = L.color; ctx.lineWidth = 1.5; ctx.setLineDash([5, 3]);
      ctx.beginPath(); ctx.moveTo(0, yy); ctx.lineTo(geo.plotW, yy); ctx.stroke();
      ctx.setLineDash([]);
      if (L.tag) {
        ctx.fillStyle = L.color; ctx.fillRect(geo.plotW, yy - 8, AXIS_W, 16);
        ctx.fillStyle = L.color === '#2196f3' ? '#fff' : '#111';
        ctx.font = 'bold 9px monospace'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
        ctx.fillText((L.title || '') + ' ' + fmtAxis(L.price), geo.plotW + 3, yy);
      }
    });
    (c.r.series || []).forEach(function (s) {
      if (s.fillFrom && s.fillTo) fillBetween(ctx, s.fillFrom, s.fillTo, s.fillColor || 'rgba(120,120,120,0.15)', geo, v, ps.toY);
      drawLine(ctx, s, geo, v, ps.toY);
    });
  });

  /* candles */
  for (var i = 0; i < v.n; i++) {
    var cd = v.slice[i];
    var x0 = barX(geo, v, i);
    var up2 = cd.close >= cd.open;
    var col = up2 ? '#089981' : '#f23645';
    ctx.strokeStyle = col; ctx.fillStyle = col; ctx.lineWidth = 1;
    var cx = x0 + bw / 2;
    ctx.beginPath(); ctx.moveTo(cx, ps.toY(cd.high)); ctx.lineTo(cx, ps.toY(cd.low)); ctx.stroke();
    var yo = ps.toY(cd.open), yc = ps.toY(cd.close);
    ctx.fillRect(x0, Math.min(yo, yc), bw, Math.max(1.5, Math.abs(yc - yo)));
  }

  /* markers */
  state.computed.forEach(function (c) {
    (c.r.markers || []).forEach(function (m) {
      if (m.i < v.start || m.i >= v.end) return;
      var k = m.i - v.start;
      var x = barX(geo, v, k) + bw / 2;
      var buy = m.kind === 'buy';
      var y = buy ? ps.toY(m.price) + 14 : ps.toY(m.price) - 14;
      ctx.fillStyle = buy ? '#089981' : '#f23645';
      ctx.beginPath();
      if (buy) { ctx.moveTo(x, y - 8); ctx.lineTo(x - 5, y); ctx.lineTo(x + 5, y); }
      else { ctx.moveTo(x, y + 8); ctx.lineTo(x - 5, y); ctx.lineTo(x + 5, y); }
      ctx.closePath(); ctx.fill();
      ctx.font = 'bold 9px sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillText(m.text || (buy ? 'L' : 'S'), x, buy ? y + 9 : y - 9);
    });
  });

  /* osc pane */
  if (geo.oscH && os) {
    state.computed.filter(function (c) { return c.pane === 'osc'; }).forEach(function (c) {
      (c.r.levels || []).forEach(function (L) {
        var yy = os.toY(L.price);
        ctx.strokeStyle = L.color || '#555'; ctx.lineWidth = 1; ctx.setLineDash([4, 2]);
        ctx.beginPath(); ctx.moveTo(0, yy); ctx.lineTo(geo.plotW, yy); ctx.stroke();
        ctx.setLineDash([]);
      });
      (c.r.series || []).forEach(function (s) {
        if (s.bars) {
          for (var k = 0; k < v.n; k++) {
            var val = s.data[v.start + k];
            if (val == null) continue;
            var zero = os.toY(Math.max(0, os.lo));
            var yy2 = os.toY(val);
            ctx.fillStyle = val >= 0 ? 'rgba(8,153,129,0.6)' : 'rgba(242,54,69,0.6)';
            ctx.fillRect(barX(geo, v, k), Math.min(yy2, zero), bw, Math.abs(zero - yy2));
          }
        } else drawLine(ctx, s, geo, v, os.toY);
      });
    });
    /* osc axis labels */
    ctx.fillStyle = '#787b86'; ctx.font = '10px monospace'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
    ctx.fillText(fmtAxis(os.hi), geo.plotW + 5, geo.oscTop + 8);
    ctx.fillText(fmtAxis(os.lo), geo.plotW + 5, geo.oscTop + geo.oscH - 8);
  }

  /* last price tag */
  var last = cs[cs.length - 1];
  var ly = ps.toY(last.close);
  if (ly > 0 && ly < geo.axisTop) {
    var lc = last.close >= last.open ? '#089981' : '#f23645';
    ctx.fillStyle = lc; ctx.fillRect(geo.plotW, ly - 9, AXIS_W, 18);
    ctx.fillStyle = '#fff'; ctx.font = 'bold 10px monospace'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
    ctx.fillText(fmt(last.close), geo.plotW + 4, ly);
    ctx.strokeStyle = lc; ctx.setLineDash([2, 2]); ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(0, ly); ctx.lineTo(geo.plotW, ly); ctx.stroke(); ctx.setLineDash([]);
  }

  drawLegends(geo, v, ps, os);
}

function drawLine(ctx, s, geo, v, toY) {
  ctx.strokeStyle = s.color || '#2962ff';
  ctx.lineWidth = s.width || 1.5;
  if (s.dash) ctx.setLineDash(s.dash); else ctx.setLineDash([]);
  ctx.beginPath();
  var started = false, k, val;
  for (k = 0; k < v.n; k++) {
    val = s.data[v.start + k];
    if (val == null) continue;
    var x = barX(geo, v, k) + barW(geo, v) / 2, y = toY(val);
    if (!started) { ctx.moveTo(x, y); started = true; } else ctx.lineTo(x, y);
  }
  ctx.stroke();
  ctx.setLineDash([]);
}

function fillBetween(ctx, a, b, col, geo, v, toY) {
  ctx.fillStyle = col;
  ctx.beginPath();
  var pts = [], k;
  for (k = 0; k < v.n; k++) {
    if (a[v.start + k] == null || b[v.start + k] == null) continue;
    pts.push([barX(geo, v, k) + barW(geo, v) / 2, toY(a[v.start + k]), toY(b[v.start + k])]);
  }
  if (pts.length < 2) return;
  ctx.moveTo(pts[0][0], pts[0][1]);
  for (k = 1; k < pts.length; k++) ctx.lineTo(pts[k][0], pts[k][1]);
  for (k = pts.length - 1; k >= 0; k--) ctx.lineTo(pts[k][0], pts[k][2]);
  ctx.closePath(); ctx.fill();
}

function drawLegends(geo, v, ps, os) {
  var ctx = baseCtx;
  ctx.font = '11px sans-serif'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
  var y = 12;
  state.computed.forEach(function (c) {
    var top = c.pane === 'price' ? 0 : (c.pane === 'vol' ? geo.volTop : geo.oscTop);
    if (c.pane === 'vol' || c.pane === 'osc') return;
    var parts = [c.title];
    (c.r.series || []).forEach(function (s) {
      var lastv = null;
      for (var k = v.end - 1; k >= v.start; k--) if (s.data[k] != null) { lastv = s.data[k]; break; }
      parts.push(s.title + ' ' + (lastv == null ? '—' : fmtAxis(lastv)));
    });
    ctx.fillStyle = 'rgba(19,23,34,0.85)';
    var tw = parts.join('   ').length * 5.6 + 8;
    ctx.fillRect(4, y - 8, tw, 16);
    ctx.fillStyle = '#d1d4dc';
    ctx.fillText(parts.join('   '), 8, y);
    y += 18;
  });
}

/* ---------------- Overlay (crosshair only — cheap) ---------------- */
function drawOverlay() {
  var geo = state.geo, sc = state.scales;
  if (!geo || !sc) return;
  var ctx = ovCtx;
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, geo.W, geo.H);
  var h = state.hover;
  if (!h || h.x > geo.plotW || h.y > geo.axisTop) return;

  var v = sc.v;
  var idx = Math.max(0, Math.min(v.n - 1, Math.floor(h.x / stepW(geo, v))));
  var cd = v.slice[idx];
  if (!cd) return;
  var cx = barX(geo, v, idx) + barW(geo, v) / 2;

  ctx.strokeStyle = 'rgba(209,212,220,0.35)';
  ctx.lineWidth = 1; ctx.setLineDash([4, 4]);
  ctx.beginPath(); ctx.moveTo(cx, 0); ctx.lineTo(cx, geo.axisTop); ctx.stroke();
  ctx.beginPath(); ctx.moveTo(0, h.y); ctx.lineTo(geo.plotW, h.y); ctx.stroke();
  ctx.setLineDash([]);

  /* value tag on right axis for the pane under cursor */
  var label = null, col = '#2962ff';
  if (h.y < geo.volTop && sc.ps) label = fmt(sc.ps.toP(h.y));
  else if (geo.volH && h.y < geo.oscTop) {
    var pv = (geo.volTop + geo.volH - h.y) / geo.volH * sc.vs.hi;
    label = fmtVol(pv);
  } else if (geo.oscH && sc.os) {
    var ov = sc.os.lo + (1 - (h.y - geo.oscTop) / geo.oscH) * (sc.os.hi - sc.os.lo);
    label = ov.toFixed(3);
  }
  if (label != null) {
    ctx.fillStyle = col; ctx.fillRect(geo.plotW, h.y - 9, AXIS_W, 18);
    ctx.fillStyle = '#fff'; ctx.font = 'bold 10px monospace'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
    ctx.fillText(label, geo.plotW + 4, h.y);
  }
  /* time tag */
  ctx.fillStyle = col;
  var tl = fmtTime(cd.time);
  ctx.fillRect(cx - 26, geo.axisTop, 52, geo.axisH);
  ctx.fillStyle = '#fff'; ctx.font = '10px monospace'; ctx.textAlign = 'center';
  ctx.fillText(tl, cx, geo.axisTop + geo.axisH / 2);

  /* OHLC readout */
  var up = cd.close >= cd.open;
  var txt = fmtFull(cd.time) + '   O ' + fmt(cd.open) + '  H ' + fmt(cd.high) + '  L ' + fmt(cd.low) + '  C ' + fmt(cd.close) + '  V ' + fmtVol(cd.volume);
  ctx.font = '11px monospace'; ctx.textAlign = 'left';
  var w = ctx.measureText(txt).width + 12;
  var bx = Math.min(cx + 12, geo.plotW - w - 4);
  if (bx < 4) bx = 4;
  ctx.fillStyle = 'rgba(30,34,45,0.94)';
  ctx.fillRect(bx, geo.axisTop - 26, w, 20);
  ctx.strokeStyle = '#2a2e39'; ctx.strokeRect(bx, geo.axisTop - 26, w, 20);
  ctx.fillStyle = up ? '#089981' : '#f23645';
  ctx.textBaseline = 'middle';
  ctx.fillText(txt, bx + 6, geo.axisTop - 16);
}

/* ---------------- Draw scheduling ----------------
   requestAnimationFrame is parked in some WebViews until the page paints,
   so schedule with a timer (always fires) and use RAF only as a fast path. */
var pendBase = 0, pendOv = 0;

function reportDrawError(e) {
  var m = 'draw error: ' + ((e && e.message) || e);
  state.msg = m;
  try { els.hSrc.textContent = m; els.hSrc.className = 'chip chip-sim'; } catch (x) {}
  if (window.console && console.error) console.error(m, e);
}

function scheduleBase() {
  if (pendBase || !els.stack) return;
  pendBase = 1;
  var run = function () {
    if (!pendBase) return;
    pendBase = 0;
    try { drawBase(); drawOverlay(); } catch (e) { reportDrawError(e); }
  };
  setTimeout(run, 0);
  if (typeof requestAnimationFrame === 'function') requestAnimationFrame(run);
}

function scheduleOverlay() {
  if (pendOv || !els.overlay) return;
  pendOv = 1;
  var run = function () {
    if (!pendOv) return;
    pendOv = 0;
    try { drawOverlay(); } catch (e) { reportDrawError(e); }
  };
  setTimeout(run, 0);
  if (typeof requestAnimationFrame === 'function') requestAnimationFrame(run);
}
function redrawAll() { recompute(); scheduleBase(); }

/* ---------------- Canvas sizing ---------------- */
function sizeCanvases() {
  dpr = Math.min(2.5, window.devicePixelRatio || 1);
  var W = els.stack.clientWidth || window.innerWidth;
  var H = els.stack.clientHeight || (window.innerHeight - 150);
  [els.base, els.overlay].forEach(function (cv) {
    cv.width = Math.round(W * dpr);
    cv.height = Math.round(H * dpr);
    cv.style.width = W + 'px';
    cv.style.height = H + 'px';
  });
  baseCtx = els.base.getContext('2d');
  ovCtx = els.overlay.getContext('2d');
  state.geo = computeGeo();
  scheduleBase();
}

/* ---------------- Data layer ---------------- */
function lsGet(k) { try { return JSON.parse(localStorage.getItem(k)); } catch (e) { return null; } }
function lsSet(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }

function synth(sym, tf) {
  var spec = TFS[tf], S = SYMBOLS[sym] || {};
  var base = S.ref || 100;
  var n = 220, now = Math.floor(Date.now() / 1000);
  now = Math.floor(now / spec.sec) * spec.sec;
  var out = [], p = base, i;
  for (i = n; i >= 0; i--) {
    var t = now - i * spec.sec;
    var d = (Math.sin(i / 9) * 0.6 + (i % 13 === 0 ? 0.5 : -0.2)) * base * 0.004;
    var o = p, c = p + d;
    out.push({ time: t, open: o, high: Math.max(o, c) + Math.random() * base * 0.002,
               low: Math.min(o, c) - Math.random() * base * 0.002, close: c,
               volume: 20 + Math.random() * 120 });
    p = c;
  }
  return out;
}

/* CoinGecko returns price ticks, not candles: derive each bar from two
   consecutive ticks. high/low are therefore a bound, not a true extremes. */
function buildFromPoints(prices, vols) {
  var out = [], i, prev = null;
  for (i = 0; i < prices.length; i++) {
    var t = Math.floor(prices[i][0] / 1000);
    var c = prices[i][1];
    var vol = vols && vols[i] ? vols[i][1] : 1;
    if (prev == null) { prev = c; continue; }
    out.push({ time: t, open: prev, high: Math.max(prev, c), low: Math.min(prev, c), close: c, volume: vol });
    prev = c;
  }
  return out;
}

function aggregate(src, agg, sec) {
  if (agg <= 1) return src;
  var out = [], i;
  for (i = 0; i < src.length; i += agg) {
    var grp = src.slice(i, i + agg);
    if (!grp.length) break;
    var o = grp[0].open, c = grp[grp.length - 1].close;
    var h = -Infinity, l = Infinity, v = 0, j;
    for (j = 0; j < grp.length; j++) { h = Math.max(h, grp[j].high); l = Math.min(l, grp[j].low); v += grp[j].volume; }
    out.push({ time: Math.floor(grp[0].time / sec) * sec, open: o, high: h, low: l, close: c, volume: v });
  }
  return out;
}

/* Gate.io v4 spot candlestick row layout, confirmed empirically 2026-11-27 by
   continuity (open[i+1] chains to close[i]) rather than by trusting docs:
     0 t · 1 quoteVol · 2 close · 3 high · 4 low · 5 open · 6 baseVol · 7 windowClosed
   Swapping 2 and 5 is the classic mistake; it passes low<=o/c<=high checks but
   inverts every candle, hence the continuity test in the suite. */
function parseGateRows(arr) {
  var cs = arr.map(function (row) {
    return {
      time: Math.floor(parseFloat(row[0])),
      open: parseFloat(row[5]),
      high: parseFloat(row[3]),
      low: parseFloat(row[4]),
      close: parseFloat(row[2]),
      volume: parseFloat(row[6])
    };
  });
  cs.sort(function (a, b) { return a.time - b.time; });
  /* never keep the still-forming bar */
  var lastRaw = arr[arr.length - 1];
  if (lastRaw && String(lastRaw[7]) === 'false') cs.pop();
  return cs;
}

/* drop bars whose geometry is impossible — a provider that changes field order
   mid-release would otherwise paint inverted candles */
function sanitize(cs) {
  var out = [], i;
  for (i = 0; i < cs.length; i++) {
    var c = cs[i];
    if (!c || !isFinite(c.open) || !isFinite(c.high) || !isFinite(c.low) || !isFinite(c.close)) continue;
    if (c.low > Math.min(c.open, c.close) + 1e-9) continue;
    if (c.high < Math.max(c.open, c.close) - 1e-9) continue;
    if (i && c.time <= out[out.length - 1].time) continue;
    out.push(c);
  }
  return out;
}

/* ---------------- Providers ----------------
   Each returns { candles, note } or throws with a short reason.
   `supports(tf)` is the honesty gate: CoinGecko physically cannot produce 1m. */
var PROVIDERS = {
  gate: {
    id: 'gate',
    label: 'Gate.io',
    realCandles: true,
    supports: function (tf) { return !!TFS[tf].gate; },
    fetch: async function (sym, tf, signal) {
      var S = SYMBOLS[sym], spec = TFS[tf];
      if (!S || !S.gate) throw new Error('no gate pair');
      var url = 'https://api.gateio.ws/api/v4/spot/candlesticks?currency_pair=' + S.gate +
                '&interval=' + spec.gate + '&limit=1000';
      var r = await fetch(url, { headers: { Accept: 'application/json' }, signal: signal });
      if (r.status === 429) throw new Error('rate-limit');
      if (!r.ok) throw new Error('http ' + r.status);
      var arr = await r.json();
      if (!Array.isArray(arr) || arr.length < 5) throw new Error('empty');
      var clean = sanitize(parseGateRows(arr));
      if (clean.length < 30) throw new Error('only ' + clean.length + ' valid bars');
      return { candles: clean, note: clean.length + ' bars' };
    }
  },
  cg: {
    id: 'cg',
    label: 'CoinGecko',
    realCandles: false,
    supports: function (tf) { return TFS[tf].sec >= TFS[tf].cgMin; },
    fetch: async function (sym, tf, signal) {
      var S = SYMBOLS[sym], spec = TFS[tf];
      if (!S || !S.cg) throw new Error('no coingecko id');
      var url = 'https://api.coingecko.com/api/v3/coins/' + S.cg +
                '/market_chart?vs_currency=usd&days=' + spec.cgDays;
      var r = await fetch(url, { headers: { Accept: 'application/json' }, signal: signal });
      if (r.status === 429) throw new Error('rate-limit');
      if (!r.ok) throw new Error('http ' + r.status);
      var j = await r.json();
      if (!j || !j.prices || j.prices.length < 10) throw new Error('empty');
      var ticks = buildFromPoints(j.prices, j.total_volumes || null);
      var agg = Math.max(1, Math.round(spec.sec / spec.cgMin));
      var clean = sanitize(aggregate(ticks, agg, spec.sec));
      if (clean.length < 20) throw new Error('only ' + clean.length + ' valid bars');
      return { candles: clean, note: clean.length + ' bars (ticks, not true OHLC)' };
    }
  }
};
var PROVIDER_ORDER = ['gate', 'cg'];

/* ---------------- Cache ---------------- */
function cacheKey(sym, tf) { return 'tv3_' + sym + '_' + tf; }
var CACHE_TTL = 45000;

function cacheGet(sym, tf) {
  var c = lsGet(cacheKey(sym, tf));
  return c && c.candles && c.candles.length ? c : null;
}
function cacheSet(sym, tf, provider, candles) {
  lsSet(cacheKey(sym, tf), { t: Date.now(), p: provider, candles: candles });
}

/* ---------------- Load ----------------
   Two independent guards against the race that bit v3.0:
     gen   — a slower older response may never overwrite a newer one
     abort — the superseded request is cancelled, so it costs no rate limit */
var loadGen = 0;
var loadCtl = null;

async function loadData(force) {
  var gen = ++loadGen;
  var wantSym = state.symbol, wantTf = state.tf;
  var spec = TFS[wantTf];

  /* cancel whatever previous request is still in flight */
  if (loadCtl) { try { loadCtl.abort(); } catch (e) {} }
  var ctl = (typeof AbortController === 'function') ? new AbortController() : null;
  loadCtl = ctl;

  state.busy = true;
  setMsg('loading…');
  updateHud();

  /* 1. fresh cache wins — keeps us under the free rate limits */
  var cached = cacheGet(wantSym, wantTf);
  if (cached && !force && (Date.now() - cached.t) < CACHE_TTL) {
    if (gen !== loadGen) return;
    applyData(cached.candles, 'cached', cached.p, wantSym, wantTf);
    return;
  }

  var attempts = [];
  var signal = ctl ? ctl.signal : undefined;

  for (var i = 0; i < PROVIDER_ORDER.length; i++) {
    var pv = PROVIDERS[PROVIDER_ORDER[i]];
    if (!pv) continue;
    if (!pv.supports(wantTf)) { attempts.push(pv.label + ': unsupported ' + wantTf); continue; }
    try {
      var res = await pv.fetch(wantSym, wantTf, signal);
      if (gen !== loadGen) return;               /* superseded while in flight */
      if (ctl && ctl.signal && ctl.signal.aborted) return;
      cacheSet(wantSym, wantTf, pv.id, res.candles);
      applyData(res.candles, 'live', pv.id, wantSym, wantTf, res.note);
      return;
    } catch (e) {
      if (e && (e.name === 'AbortError' || (ctl && ctl.signal && ctl.signal.aborted))) return;
      attempts.push(pv.label + ': ' + (((e && e.message) || e) + '').slice(0, 40));
    }
  }

  /* 2. every provider failed → stale cache is better than fiction */
  if (gen !== loadGen) return;
  if (cached) {
    applyData(cached.candles, 'stale', cached.p || 'unknown', wantSym, wantTf);
    setMsg('providers unreachable — showing last cached data');
    return;
  }

  /* 3. nothing at all → synthetic, announced loudly, never presented as real */
  applyData(synth(wantSym, wantTf), 'sim', 'synthetic', wantSym, wantTf);
  setMsg('no reachable data source — SIMULATED bars: ' + attempts.join(' · '));
}

function applyData(candles, mode, provider, wantSym, wantTf, note) {
  if (!candles || !candles.length) candles = synth(wantSym, wantTf), mode = 'sim';
  state.candles = candles;
  state.source = mode;
  state.provider = provider;
  state.note = note || '';
  state.updatedAt = Date.now();
  state.offset = Math.min(state.offset, Math.max(0, candles.length - state.visible - 1));
  state.busy = false;
  loadCtl = null;
  updateHud();
  redrawAll();
}

/* live tick: only advance the forming bar when data is synthetic;
   for real feeds re-fetch, which the cache window keeps cheap */
function refreshTick() {
  if (state.source === 'sim') {
    var last = state.candles[state.candles.length - 1];
    if (!last) return;
    var d = (Math.random() - 0.49) * last.close * 0.0012;
    last.close += d;
    last.high = Math.max(last.high, last.close);
    last.low = Math.min(last.low, last.close);
    updateHud(); scheduleBase();
  } else {
    loadData(true);
  }
}

/* ---------------- HUD / chrome ---------------- */
function setMsg(m) { state.msg = m; }

function edMsg(m, ok) {
  var el = els.edMsg;
  if (!el) return;
  el.textContent = (ok ? '✓ ' : '✕ ') + m;
  el.style.color = ok ? '#37d39b' : '#ff7a7a';
}

function updateHud() {
  var cs = state.candles;
  if (!cs.length) return;
  if (!els.hSym) return;                 /* headless / pre-boot: nothing to write */
  var last = cs[cs.length - 1], prev = cs[cs.length - 2] || last;
  var chg = last.close - prev.close, pct = prev.close ? chg / prev.close * 100 : 0;
  els.hSym.textContent = (SYMBOLS[state.symbol] ? SYMBOLS[state.symbol].label : state.symbol) + ' · ' + state.tf;
  els.hPrice.textContent = fmt(last.close);
  els.hPrice.className = chg >= 0 ? 'text-emerald-400' : 'text-rose-400';
  els.hChg.textContent = (chg >= 0 ? '+' : '') + fmt(chg) + ' (' + pct.toFixed(2) + '%)';
  els.hChg.className = chg >= 0 ? 'text-emerald-400' : 'text-rose-400';

  var badge = els.hSrc;
  var pl = (PROVIDERS[state.provider] && PROVIDERS[state.provider].label) || state.provider || '—';
  if (state.source === 'live') {
    badge.textContent = 'LIVE · ' + pl + (PROVIDERS[state.provider] && !PROVIDERS[state.provider].realCandles ? ' (ticks)' : '');
    badge.className = 'chip chip-live';
    badge.title = state.note || '';
  } else if (state.source === 'cached') {
    badge.textContent = 'CACHED · ' + pl;
    badge.className = 'chip chip-cache';
    badge.title = 'served from local cache to stay under the free rate limit';
  } else if (state.source === 'stale') {
    badge.textContent = 'STALE · ' + pl;
    badge.className = 'chip chip-cache';
    badge.title = state.msg || 'no provider reachable — showing last cached data';
  } else {
    badge.textContent = 'SIMULATED';
    badge.className = 'chip chip-sim';
    badge.title = state.msg || 'no data source reachable — these bars are invented, do not trade on them';
  }
  els.hTime.textContent = state.updatedAt ? new Date(state.updatedAt).toLocaleTimeString() : '—';
  els.hRange.textContent = 'bars ' + cs.length + ' · shown ' + Math.min(state.visible, cs.length) + ' · zoom ' + state.visible;
  els.verTag.textContent = 'v' + VERSION;
}

function renderChips() {
  if (!els.chips) return;
  els.chips.innerHTML = '';
  if (!state.active.length) {
    var e = document.createElement('span');
    e.className = 'chip chip-empty';
    e.textContent = 'no indicator — click “Indicators” to add one';
    els.chips.appendChild(e);
  }
  var errs = {};
  (state.computed || []).forEach(function (c) { if (c.error) errs[c.uid] = c.error; });
  state.active.forEach(function (a) {
    var d = DEFS[a.def];
    var w = document.createElement('span');
    w.className = 'chip ' + (errs[a.uid] ? 'chip-sim' : 'chip-on');
    if (errs[a.uid]) w.title = 'compute error: ' + errs[a.uid];
    var nm = document.createElement('button');
    nm.className = 'chip-name';
    nm.textContent = (errs[a.uid] ? '⚠ ' : '') + (a.title || d.name);
    nm.title = 'edit parameters';
    nm.onclick = function () { openParams(a.uid); };
    w.appendChild(nm);
    if (d.params && d.params.length) {
      var g = document.createElement('button');
      g.className = 'chip-gear'; g.innerHTML = '&#9881;';
      g.title = 'parameters';
      g.onclick = function () { openParams(a.uid); };
      w.appendChild(g);
    }
    var x = document.createElement('button');
    x.className = 'chip-x'; x.textContent = '×';
    x.title = 'remove';
    x.onclick = function () { removeIndicator(a.uid); };
    w.appendChild(x);
    els.chips.appendChild(w);
  });
  savePrefs();
}

/* ---------------- Indicator management ---------------- */
function addIndicator(defId, params) {
  var d = DEFS[defId];
  if (!d) return null;
  var p = {};
  (d.params || []).forEach(function (x) { p[x.k] = x.d; });
  if (params) Object.keys(params).forEach(function (k) { if (k in p) p[k] = params[k]; });
  var a = { uid: state.uid++, def: defId, params: p, title: d.name };
  state.active.push(a);
  renderChips(); redrawAll();
  return a;
}

function removeIndicator(uid) {
  state.active = state.active.filter(function (a) { return a.uid !== uid; });
  renderChips();
  state.geo = computeGeo();
  redrawAll();
}

function openParams(uid) {
  var a = state.active.filter(function (x) { return x.uid === uid; })[0];
  if (!a) return;
  var d = DEFS[a.def];
  els.modTitle.textContent = d.name;
  els.modBody.innerHTML = '';
  var titleRow = mkRow('Title', 'text', a.title, null);
  els.modBody.appendChild(titleRow);
  (d.params || []).forEach(function (prm) {
    if (prm.t === 'bool') {
      var lab = document.createElement('label');
      lab.className = 'row-check';
      var cb = document.createElement('input');
      cb.type = 'checkbox'; cb.checked = !!a.params[prm.k];
      var sp = document.createElement('span'); sp.textContent = prm.l;
      lab.appendChild(cb); lab.appendChild(sp);
      lab._key = prm.k; lab._type = prm.t; lab._cb = cb;
      els.modBody.appendChild(lab);
    } else if (prm.t === 'expr') {
      var wrap = document.createElement('div');
      wrap.className = 'row';
      var l = document.createElement('label'); l.textContent = prm.l;
      var ta = document.createElement('textarea');
      ta.className = 'expr'; ta.rows = 3; ta.spellcheck = false;
      ta.value = a.params[prm.k];
      var hint = document.createElement('div');
      hint.className = 'hint';
      hint.innerHTML = 'current bar: <b>close high low open volume hl2 atr</b><br>' +
        'history: <code>close[1]</code>, <code>high[3]</code><br>' +
        'functions take the whole series with <b>$</b>: <code>ema($close,21)</code> · <code>sma($close,14)</code> · <code>rsi($close,14)</code> · <code>stdev($close,20)</code> · <code>hh($high,14)</code> · <code>ll($low,14)</code> · <code>shift($close,1)</code><br>' +
        'mix a series into per-bar maths with <b>at()</b>: <code>close &gt; at(ema($close,21)) ? 1 : 0</code><br>' +
        'math: <b>abs min max sqrt pow round log exp sin cos tan nz</b> · loop index <b>i</b><br>' +
        'example: <code>(close - close[1]) / close[1] * 100</code>';
      wrap.appendChild(l); wrap.appendChild(ta); wrap.appendChild(hint);
      wrap._key = prm.k; wrap._type = 'text'; wrap._inp = ta;
      els.modBody.appendChild(wrap);
    } else if (prm.t === 'color') {
      var w2 = document.createElement('div'); w2.className = 'row';
      var l2 = document.createElement('label'); l2.textContent = prm.l;
      var inp = document.createElement('input'); inp.type = 'color'; inp.value = a.params[prm.k];
      w2.appendChild(l2); w2.appendChild(inp);
      w2._key = prm.k; w2._type = 'color'; w2._inp = inp;
      els.modBody.appendChild(w2);
    } else {
      els.modBody.appendChild(mkRow(prm.l, prm.t === 'int' ? 'number' : 'number', a.params[prm.k], prm, prm.t === 'int' ? 1 : '0.01'));
    }
  });
  els.modSave.onclick = function () {
    Array.prototype.forEach.call(els.modBody.children, function (row) {
      if (!row._key) return;
      if (row._type === 'bool') a.params[row._key] = row._cb.checked;
      else if (row._type === 'color') a.params[row._key] = row._inp.value;
      else {
        var raw = row._inp.value;
        if (row._type === 'text') a.params[row._key] = raw;
        else {
          var n = parseNum(raw, DEFS[a.def].params.filter(function (x) { return x.k === row._key; })[0].d);
          a.params[row._key] = n;
          row._inp.value = n;
        }
      }
    });
    a.title = els.modBody.children[0]._inp.value || DEFS[a.def].name;
    closeModal(); renderChips(); redrawAll();
  };
  openModal();
}

function mkRow(label, type, val, prm, step) {
  var w = document.createElement('div'); w.className = 'row';
  var l = document.createElement('label'); l.textContent = label;
  var i = document.createElement('input');
  i.type = type; i.value = val;
  if (type === 'number') {
    i.step = step || 1;
    if (prm && prm.min != null) i.min = prm.min;
    if (prm && prm.max != null) i.max = prm.max;
  }
  w.appendChild(l); w.appendChild(i);
  w._key = prm ? prm.k : 'title'; w._type = type === 'number' ? 'num' : 'text'; w._inp = i;
  return w;
}

function parseNum(v, def) {
  if (typeof v !== 'string') return typeof v === 'number' && isFinite(v) ? v : def;
  var fa = ['۰','۱','۲','۳','۴','۵','۶','۷','۸','۹'];
  var s = v;
  for (var i = 0; i < 10; i++) s = s.split(fa[i]).join(String(i));
  s = s.replace(/٫/g, '.').replace(/,/g, '.').trim();
  var n = parseFloat(s);
  return isFinite(n) ? n : def;
}

/* ---------------- Indicators catalogue modal ---------------- */
function openCatalogue(filter) {
  var q = (filter || '').toLowerCase();
  els.catBody.innerHTML = '';
  var groups = { price: 'Overlay on price', vol: 'Volume pane', osc: 'Oscillator pane' };
  Object.keys(groups).forEach(function (pane) {
    var ids = Object.keys(DEFS).filter(function (id) {
      return DEFS[id].pane === pane && DEFS[id].name.toLowerCase().indexOf(q) >= 0;
    });
    if (!ids.length) return;
    var h = document.createElement('div'); h.className = 'cat-h'; h.textContent = groups[pane];
    els.catBody.appendChild(h);
    ids.forEach(function (id) {
      var d = DEFS[id];
      var row = document.createElement('button');
      row.className = 'cat-row';
      row.innerHTML = '<span class="cat-n">' + d.name + '</span><span class="cat-a">+ add</span>';
      row.onclick = function () { addIndicator(id); closeCat(); };
      els.catBody.appendChild(row);
    });
  });
  if (!els.catBody.children.length) {
    var n = document.createElement('div'); n.className = 'cat-empty'; n.textContent = 'no match';
    els.catBody.appendChild(n);
  }
  els.catModal.classList.remove('hidden');
  els.catSearch.value = filter || '';
  els.catSearch.focus();
}
function closeCat() { els.catModal.classList.add('hidden'); }
function openModal() { els.paramModal.classList.remove('hidden'); }
function closeModal() { els.paramModal.classList.add('hidden'); }

/* ---------------- Persistence ---------------- */
function savePrefs() {
  lsSet('prefs3', {
    symbol: state.symbol, tf: state.tf, visible: state.visible,
    active: state.active.map(function (a) { return { def: a.def, params: a.params, title: a.title }; })
  });
}
function loadPrefs() {
  var p = lsGet('prefs3');
  if (!p) return false;
  if (SYMBOLS[p.symbol]) state.symbol = p.symbol;
  if (TFS[p.tf]) state.tf = p.tf;
  if (p.visible) state.visible = p.visible;
  if (p.active && p.active.length) {
    p.active.forEach(function (a) {
      if (!DEFS[a.def]) return;
      var d = DEFS[a.def], params = {};
      (d.params || []).forEach(function (x) { params[x.k] = (a.params && a.params[x.k] != null) ? a.params[x.k] : x.d; });
      state.active.push({ uid: state.uid++, def: a.def, params: params, title: a.title || d.name });
    });
    return true;
  }
  return false;
}

/* ---------------- Interaction ---------------- */
function bindEvents() {
  var stack = els.stack;

  function pos(e) {
    var r = stack.getBoundingClientRect();
    return { x: e.clientX - r.left, y: e.clientY - r.top };
  }

  stack.addEventListener('mousedown', function (e) {
    state.drag = { x: e.clientX, off: state.offset };
    stack.classList.add('grabbing');
  });
  window.addEventListener('mousemove', function (e) {
    var p = pos(e);
    state.hover = p;
    if (state.drag && state.geo) {
      var v = view();
      var per = state.geo.plotW / Math.max(1, v.n);
      var d = Math.round((e.clientX - state.drag.x) / per);
      var maxOff = Math.max(0, state.candles.length - state.visible - 1);
      var no = Math.max(0, Math.min(maxOff, state.drag.off + d));
      if (no !== state.offset) { state.offset = no; scheduleBase(); updateHud(); }
    }
    scheduleOverlay();
  });
  window.addEventListener('mouseup', function () { state.drag = null; stack.classList.remove('grabbing'); });
  stack.addEventListener('mouseleave', function () { state.hover = null; scheduleOverlay(); });

  stack.addEventListener('wheel', function (e) {
    e.preventDefault();
    var nv = e.deltaY < 0 ? state.visible - 5 : state.visible + 5;
    nv = Math.max(15, Math.min(state.candles.length, nv));
    if (nv !== state.visible) {
      state.visible = nv;
      state.offset = Math.min(state.offset, Math.max(0, state.candles.length - nv - 1));
      scheduleBase(); updateHud(); savePrefs();
    }
  }, { passive: false });

  stack.addEventListener('dblclick', resetView);

  /* touch */
  var tStart = 0, tOff = 0, pinch = 0;
  stack.addEventListener('touchstart', function (e) {
    if (e.touches.length === 1) { tStart = e.touches[0].clientX; tOff = state.offset; }
    else if (e.touches.length === 2) { pinch = dist2(e.touches); tStart = 0; }
  }, { passive: true });
  stack.addEventListener('touchmove', function (e) {
    if (e.touches.length === 1 && tStart && state.geo) {
      var v = view();
      var per = state.geo.plotW / Math.max(1, v.n);
      var d = Math.round((e.touches[0].clientX - tStart) / per);
      var maxOff = Math.max(0, state.candles.length - state.visible - 1);
      state.offset = Math.max(0, Math.min(maxOff, tOff + d));
      var r = stack.getBoundingClientRect();
      state.hover = { x: e.touches[0].clientX - r.left, y: e.touches[0].clientY - r.top };
      scheduleBase(); scheduleOverlay(); updateHud();
    } else if (e.touches.length === 2 && pinch) {
      var nd = dist2(e.touches);
      var f = nd / pinch;
      if (f > 1.06) { state.visible = Math.max(15, state.visible - 4); pinch = nd; }
      else if (f < 0.94) { state.visible = Math.min(state.candles.length, state.visible + 4); pinch = nd; }
      scheduleBase(); updateHud();
    }
    e.preventDefault();
  }, { passive: false });
  stack.addEventListener('touchend', function () { tStart = 0; pinch = 0; state.hover = null; scheduleOverlay(); savePrefs(); }, { passive: true });

  function dist2(t) { return Math.hypot(t[0].clientX - t[1].clientX, t[0].clientY - t[1].clientY); }

  window.addEventListener('resize', sizeCanvases);
  window.addEventListener('orientationchange', function () { setTimeout(sizeCanvases, 250); });

  /* chrome */
  document.querySelectorAll('#tfGroup .tf-btn').forEach(function (b) {
    b.addEventListener('click', function () {
      document.querySelectorAll('#tfGroup .tf-btn').forEach(function (x) { x.classList.remove('active-tf'); });
      b.classList.add('active-tf');
      state.tf = b.getAttribute('data-tf');
      state.offset = 0; state.visible = 70;
      savePrefs(); loadData(true);
    });
  });
  els.sym.addEventListener('change', function (e) {
    state.symbol = e.target.value;
    state.offset = 0;
    savePrefs(); loadData(true);
  });
  els.reset.addEventListener('click', resetView);
  els.catBtn.addEventListener('click', function () { openCatalogue(''); });
  els.catClose.addEventListener('click', closeCat);
  els.catSearch.addEventListener('input', function (e) { openCatalogue(e.target.value); });
  els.catModal.addEventListener('click', function (e) { if (e.target === els.catModal) closeCat(); });
  els.modClose.addEventListener('click', closeModal);
  els.paramModal.addEventListener('click', function (e) { if (e.target === els.paramModal) closeModal(); });
  els.edBtn.addEventListener('click', function () { els.drawer.classList.toggle('hidden'); });
  els.edClose.addEventListener('click', function () { els.drawer.classList.add('hidden'); });
  els.edCopy.addEventListener('click', function () {
    var t = els.edText; t.select();
    try { navigator.clipboard.writeText(t.value); } catch (e) { document.execCommand('copy'); }
    els.edCopy.textContent = 'copied';
    setTimeout(function () { els.edCopy.textContent = 'copy'; }, 1500);
  });
  els.edApply.addEventListener('click', function () {
    var expr = els.edText.value.trim();
    if (!expr) { edMsg('enter a formula'); return; }
    /* validate before touching the chart — never plot a blank line */
    try {
      var probe = evalExpr(expr, state.candles);
      var hasVal = false, k;
      for (k = 0; k < probe.length; k++) if (probe[k] != null) { hasVal = true; break; }
      if (!hasVal) { edMsg('formula produced no values on this data'); return; }
    } catch (e) {
      edMsg(((e && e.message) || e));
      return;
    }
    var found = state.active.filter(function (a) { return a.def === 'custom'; })[0];
    if (found) { found.params.expr = expr; renderChips(); redrawAll(); }
    else addIndicator('custom', { expr: expr });
    edMsg('plotted: ' + expr, true);
    els.drawer.classList.add('hidden');
  });
}

function resetView() {
  state.offset = 0; state.visible = 70;
  scheduleBase(); updateHud(); savePrefs();
}


/* ---------------- Boot ---------------- */
function boot() {
  els.stack = document.getElementById('stack');
  els.base = document.getElementById('baseCanvas');
  els.overlay = document.getElementById('ovCanvas');
  els.hSym = document.getElementById('hSym');
  els.hPrice = document.getElementById('hPrice');
  els.hChg = document.getElementById('hChg');
  els.hSrc = document.getElementById('hSrc');
  els.hTime = document.getElementById('hTime');
  els.hRange = document.getElementById('hRange');
  els.chips = document.getElementById('chips');
  els.sym = document.getElementById('symSel');
  els.tfGroup = document.getElementById('tfGroup');
  els.reset = document.getElementById('resetBtn');
  els.catBtn = document.getElementById('catBtn');
  els.catModal = document.getElementById('catModal');
  els.catBody = document.getElementById('catBody');
  els.catSearch = document.getElementById('catSearch');
  els.catClose = document.getElementById('catClose');
  els.paramModal = document.getElementById('paramModal');
  els.modTitle = document.getElementById('modTitle');
  els.modBody = document.getElementById('modBody');
  els.modSave = document.getElementById('modSave');
  els.modClose = document.getElementById('modClose');
  els.edBtn = document.getElementById('edBtn');
  els.edClose = document.getElementById('edClose');
  els.edText = document.getElementById('edText');
  els.edCopy = document.getElementById('edCopy');
  els.edApply = document.getElementById('edApply');
  els.drawer = document.getElementById('drawer');
  els.edMsg = document.getElementById('edMsg');
  els.verTag = document.getElementById('verTag');

  // populate symbol select
  Object.keys(SYMBOLS).forEach(function (k) {
    var o = document.createElement('option');
    o.value = k; o.textContent = SYMBOLS[k].label;
    els.sym.appendChild(o);
  });

  var hadPrefs = loadPrefs();
  els.sym.value = state.symbol;
  document.querySelectorAll('#tfGroup .tf-btn').forEach(function (b) {
    b.classList.toggle('active-tf', b.getAttribute('data-tf') === state.tf);
  });
  if (!els.edText.value.trim()) els.edText.value = 'ema($close,21)';

  if (!hadPrefs || !state.active.length) {
    addIndicator('volume');
    addIndicator('b2');
    addIndicator('demarker');
  }
  renderChips();

  bindEvents();
  sizeCanvases();
  loadData(false);

  setInterval(refreshTick, 60000);
}

/* Self-diagnosis: honest check that pixels were actually painted. */
window.__diag = function () {
  var out = {
    version: VERSION,
    source: state.source,
    msg: state.msg,
    candles: state.candles.length,
    active: state.active.map(function (a) { return a.def; }),
    geo: state.geo,
    errors: (state.computed || []).filter(function (c) { return c.error; }).map(function (c) { return c.def + ': ' + c.error; })
  };
  var cv = els.base;
  if (!cv || !cv.width || !cv.height) { out.painted = false; out.why = 'canvas has no size'; return out; }
  try {
    var d = cv.getContext('2d').getImageData(0, 0, cv.width, cv.height).data;
    var non = 0, i;
    for (i = 0; i < d.length; i += 4) {
      if (d[i] > 45 || d[i + 1] > 45 || d[i + 2] > 55) non++;
    }
    out.paintedPixels = non;
    out.totalPixels = d.length / 4;
    out.painted = non > 400;
  } catch (e) {
    out.painted = false;
    out.why = 'getImageData blocked: ' + ((e && e.message) || e);
  }
  return out;
};

if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
else boot();
