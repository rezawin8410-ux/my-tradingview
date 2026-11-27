/* =============================================================
   Personal TradingView — engine v3
   Architecture: real data + cached indicator computation +
   separate base/overlay canvases (crosshair never recomputes TA)
   ============================================================= */

var VERSION = '3.4.0';
var AXIS_W = 58;
var AXIS_H = 20;
var VOL_H = 68;
var OSC_H = 118;
var OSC_MIN = 84;

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

/* Null-safe running mean. The incremental version subtracted src[i-len]
   unconditionally, so a null early in the window corrupted the sum with NaN
   and every later value died. Recompute the window instead: 1000 bars x len<=200
   is cheap, and correctness of every indicator depends on it. */
function sma(src, len) {
  var out = pad(src.length), i, j, sv, ct, v;
  for (i = len - 1; i < src.length; i++) {
    sv = 0; ct = 0;
    for (j = 0; j < len; j++) {
      v = src[i - j];
      if (v != null && isFinite(v)) { sv += v; ct++; }
    }
    out[i] = ct === len ? sv / len : null;
  }
  return out;
}

/* Wilder / exponential moving average (alpha = 1/len) — the smoother behind
   ADX, ATR, TSI and the rest of the Wilder family. */
function rma(src, len) {
  var out = pad(src.length), prev = null, sum = 0, ct = 0, i, v;
  for (i = 0; i < src.length; i++) {
    v = src[i];
    if (v == null || !isFinite(v)) continue;
    if (ct < len) {
      sum += v; ct++;
      if (ct === len) { prev = sum / len; out[i] = prev; }
    } else {
      prev = (prev * (len - 1) + v) / len;
      out[i] = prev;
    }
  }
  return out;
}

function wma(src, len) {
  var out = pad(src.length), i, j, sw, sv, w, v;
  for (i = len - 1; i < src.length; i++) {
    sw = 0; sv = 0;
    for (j = 0; j < len; j++) {
      v = src[i - j];
      if (v == null || !isFinite(v)) { sw = -1; break; }
      w = len - j; sw += w; sv += v * w;
    }
    out[i] = sw > 0 ? sv / sw : null;
  }
  return out;
}

/* Hull MA: WMA(2*WMA(n/2) − WMA(n), √n) — built on the null-safe WMA above. */
function hma(src, len) {
  var half = Math.max(1, Math.round(len / 2)), sq = Math.max(1, Math.round(Math.sqrt(len)));
  var a = wma(src, half), b = wma(src, len), diff = pad(src.length), i;
  for (i = 0; i < src.length; i++) {
    diff[i] = (a[i] == null || b[i] == null) ? null : 2 * a[i] - b[i];
  }
  return wma(diff, sq);
}

function mdev(src, len) {
  var out = pad(src.length), i, j, m, sv;
  for (i = len - 1; i < src.length; i++) {
    m = 0;
    for (j = 0; j < len; j++) m += src[i - j];
    m /= len; sv = 0;
    for (j = 0; j < len; j++) sv += Math.abs(src[i - j] - m);
    out[i] = sv / len;
  }
  return out;
}

function rocAt(src, back) {
  var out = pad(src.length), i, b;
  for (i = back; i < src.length; i++) {
    b = src[i - back];
    out[i] = (b == null || b === 0 || src[i] == null) ? null : (src[i] - b) / b * 100;
  }
  return out;
}

function hl2(cs) { return cs.map(function (c) { return (c.high + c.low) / 2; }); }
function hlc3(cs) { return cs.map(function (c) { return (c.high + c.low + c.close) / 3; }); }

/* Williams %R — note: locals are named hA/lA, not h/l, because hh() and ll()
   are functions in outer scope and `var hh = hh(...)` would shadow them. */
function willr(cs, len) {
  var hA = cs.map(function (c) { return c.high; }), lA = cs.map(function (c) { return c.low; });
  var hH = hh(hA, len), lL = ll(lA, len), out = pad(cs.length), i;
  for (i = 0; i < cs.length; i++) {
    if (hH[i] == null || lL[i] == null || hH[i] === lL[i]) { out[i] = null; continue; }
    out[i] = -100 * (hH[i] - cs[i].close) / (hH[i] - lL[i]);
  }
  return out;
}

/* CCI */
function cci(cs, len) {
  var tp = hlc3(cs), m = sma(tp, len), d = mdev(tp, len), out = pad(cs.length), i;
  for (i = 0; i < cs.length; i++) {
    out[i] = (m[i] == null || d[i] == null || d[i] === 0) ? null : (tp[i] - m[i]) / (0.015 * d[i]);
  }
  return out;
}

/* Money Flow Index */
function mfi(cs, len) {
  var tp = hlc3(cs), n = cs.length, pf = pad(n), nf = pad(n), i, den, out = pad(n);
  for (i = 1; i < n; i++) {
    var m = tp[i] - tp[i - 1], v = cs[i].volume || 0;
    pf[i] = m > 0 ? m * v : 0;
    nf[i] = m < 0 ? -m * v : 0;
  }
  for (i = len; i < n; i++) {
    var sp = 0, sn = 0, j;
    for (j = i - len + 1; j <= i; j++) { sp += pf[j]; sn += nf[j]; }
    den = sn === 0 ? Infinity : sp / sn;
    out[i] = 100 - 100 / (1 + den);
  }
  return out;
}

/* ADX with +DI / -DI */
function adxFn(cs, len) {
  var n = cs.length, pdm = pad(n), mdm = pad(n), tr = pad(n), i;
  for (i = 1; i < n; i++) {
    var up = cs[i].high - cs[i - 1].high, dn = cs[i - 1].low - cs[i].low;
    pdm[i] = (up > dn && up > 0) ? up : 0;
    mdm[i] = (dn > up && dn > 0) ? dn : 0;
    tr[i] = Math.max(cs[i].high - cs[i].low, Math.abs(cs[i].high - cs[i - 1].close), Math.abs(cs[i].low - cs[i - 1].close));
  }
  var atrV = rma(tr, len), ps = rma(pdm, len), ms = rma(mdm, len);
  var dip = pad(n), dim = pad(n), dx = pad(n);
  for (i = 0; i < n; i++) {
    if (atrV[i] == null || atrV[i] === 0) continue;
    dip[i] = 100 * ps[i] / atrV[i];
    dim[i] = 100 * ms[i] / atrV[i];
    var den = dip[i] + dim[i];
    dx[i] = den === 0 ? 0 : 100 * Math.abs(dip[i] - dim[i]) / den;
  }
  return { adx: rma(dx, len), diPlus: dip, diMinus: dim };
}

/* True Strength Index */
function tsiFn(src, len, smooth) {
  var n = src.length, mom = pad(n), i, a, b, out = pad(n);
  for (i = 1; i < n; i++) mom[i] = (src[i] == null || src[i - 1] == null) ? null : src[i] - src[i - 1];
  a = rma(rma(mom, smooth), len);
  b = rma(rma(mom.map(function (v) { return v == null ? null : Math.abs(v); }), smooth), len);
  for (i = 0; i < n; i++) out[i] = (a[i] == null || b[i] == null || b[i] === 0) ? null : 100 * a[i] / b[i];
  return out;
}

/* Ultimate Oscillator */
function uoFn(cs, p1, p2, p3) {
  var n = cs.length, bp = pad(n), rs = pad(n), i, j;
  for (i = 1; i < n; i++) {
    var lh = Math.min(cs[i].low, cs[i - 1].close), hv = Math.max(cs[i].high, cs[i - 1].close);
    bp[i] = cs[i].close - lh; rs[i] = hv - lh;
  }
  function raw(len) {
    var o = pad(n);
    for (i = len; i < n; i++) {
      var sv = 0, d = 0;
      for (j = i - len + 1; j <= i; j++) { if (rs[j] == null || rs[j] === 0) continue; sv += bp[j]; d += rs[j]; }
      o[i] = d === 0 ? null : 100 * sv / d;
    }
    return o;
  }
  var a = raw(p1), b = raw(p2), c = raw(p3), out = pad(n);
  for (i = 0; i < n; i++) out[i] = (a[i] == null || b[i] == null || c[i] == null) ? null : 100 * (4 * a[i] + 2 * b[i] + c[i]) / 7;
  return out;
}

/* Fisher Transform */
function fisherFn(cs, len) {
  var n = cs.length, out = pad(n), sig = pad(n), prev = 0, i, j, mh, ml, price;
  for (i = 2; i < n; i++) {
    mh = -Infinity; ml = Infinity;
    for (j = 0; j < len; j++) { if (i - j < 0) break; mh = Math.max(mh, cs[i - j].high); ml = Math.min(ml, cs[i - j].low); }
    if (mh === ml) price = prev;
    else {
      price = 0.66 * ((cs[i].close - ml) / (mh - ml) - 0.5) * 2 + 0.67 * prev;
      price = Math.max(-0.999, Math.min(0.999, price));
      price = 0.5 * Math.log((1 + price) / (1 - price)) + 0.5 * prev;
    }
    sig[i] = prev; out[i] = price; prev = price;
  }
  return { fisher: out, signal: sig };
}

/* Parabolic SAR */
function psarFn(cs, af0, afStep, afMax) {
  var n = cs.length, out = pad(n);
  if (n < 3) return out;
  var bull = true, ep = cs[0].high, af = af0, sar = cs[0].low, i;
  for (i = 1; i < n; i++) {
    sar = sar + af * (ep - sar);
    var p1l = cs[i - 1].low, p2l = i >= 2 ? cs[i - 2].low : p1l;
    var p1h = cs[i - 1].high, p2h = i >= 2 ? cs[i - 2].high : p1h;
    if (bull) {
      sar = Math.min(sar, p1l, p2l);
      if (cs[i].low < sar) { bull = false; sar = ep; ep = cs[i].low; af = af0; }
      else if (cs[i].high > ep) { ep = cs[i].high; af = Math.min(afMax, af + afStep); }
    } else {
      sar = Math.max(sar, p1h, p2h);
      if (cs[i].high > sar) { bull = true; sar = ep; ep = cs[i].high; af = af0; }
      else if (cs[i].low < ep) { ep = cs[i].low; af = Math.min(afMax, af + afStep); }
    }
    out[i] = sar;
  }
  return out;
}

/* ALMA */
function almaFn(src, len, sig, off) {
  var n = src.length, out = pad(n), i, j, m = off * (len - 1), sd = sig * len, sw, sv, w, v;
  for (i = Math.floor(m); i < n; i++) {
    sw = 0; sv = 0;
    for (j = 0; j < len; j++) {
      v = src[i - len + 1 + j];
      if (v == null || !isFinite(v)) { sw = -1; break; }
      w = Math.exp(-((j - m) * (j - m)) / (2 * sd * sd));
      sw += w; sv += v * w;
    }
    out[i] = sw > 0 ? sv / sw : null;
  }
  return out;
}

/* On-Balance Volume / Accumulation-Distribution / Chaikin Money Flow / NVI */
function obvFn(cs) {
  var out = [], v = 0, i;
  for (i = 0; i < cs.length; i++) {
    if (i > 0) {
      if (cs[i].close > cs[i - 1].close) v += cs[i].volume;
      else if (cs[i].close < cs[i - 1].close) v -= cs[i].volume;
    }
    out.push(v);
  }
  return out;
}
function adFn(cs) {
  var out = [], v = 0, i;
  for (i = 0; i < cs.length; i++) {
    var rng = cs[i].high - cs[i].low;
    var mfm = rng > 0 ? ((cs[i].close - cs[i].low) - (cs[i].high - cs[i].close)) / rng : 0;
    v += mfm * (cs[i].volume || 0);
    out.push(v);
  }
  return out;
}
function cmfFn(cs, len) {
  var num = [], den = [], i, out = pad(cs.length);
  for (i = 0; i < cs.length; i++) {
    var rng = cs[i].high - cs[i].low;
    var mfm = rng > 0 ? ((cs[i].close - cs[i].low) - (cs[i].high - cs[i].close)) / rng : 0;
    num.push(mfm * (cs[i].volume || 0));
    den.push(cs[i].volume || 0);
  }
  var a = sma(num, len), b = sma(den, len);
  for (i = 0; i < cs.length; i++) out[i] = (a[i] == null || b[i] == null || b[i] === 0) ? null : a[i] / b[i];
  return out;
}
function nviFn(cs) {
  var out = [], v = 0, i;
  for (i = 0; i < cs.length; i++) {
    if (i > 0 && cs[i].volume < cs[i - 1].volume && cs[i - 1].close !== 0) {
      v += (cs[i].close - cs[i - 1].close) / cs[i - 1].close * 1000;
    }
    out.push(v);
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

/* median bar spacing in seconds — derived from the data itself, so hour-based
   windows survive a provider that returns irregular or gap-filled bars */
function barSeconds(cs) {
  if (!cs || cs.length < 3) return 0;
  var gaps = [], i;
  for (i = 1; i < cs.length; i++) {
    var g = cs[i].time - cs[i - 1].time;
    if (g > 0) gaps.push(g);
  }
  if (!gaps.length) return 0;
  gaps.sort(function (a, b) { return a - b; });
  return gaps[Math.floor(gaps.length / 2)];
}

/* ================= Multi-timeframe resolution =================
   Pine's request.security(sym, tf, expr, lookahead=barmerge.lookahead_on)
   maps another timeframe's series onto the chart bars. The alignment rule
   differs by direction and getting it wrong silently repaints the future,
   so it is implemented once, here, and reused by every MTF indicator:

     srcSec >  chartSec (higher TF) : chart bar t takes the value of the HTF
        bar whose OPEN is floor(t/srcSec)*srcSec. lookahead_on means that bar's
        FINAL value is used for every chart bar inside it — including bars
        before it closed. That is the documented repaint of lookahead_on and
        we reproduce it deliberately, because the Pine does.
     srcSec == chartSec            : exact time match.
     srcSec <  chartSec (lower TF) : Pine can only hand back the LT bar that
        starts at the chart bar's open. Anything else would be invented.

   Values are never interpolated and never carried forward across a gap:
   a chart bar with no source bar stays null. */

var GATE_IVL = [[60, '1m'], [180, '3m'], [300, '5m'], [900, '15m'],
                [1800, '30m'], [3600, '1h'], [14400, '4h'], [86400, '1d']];

function gateIntervalFor(sec) {
  var i;
  for (i = 0; i < GATE_IVL.length; i++) if (GATE_IVL[i][0] === sec) return GATE_IVL[i][1];
  return null;
}

/* Pine timeframe literal -> seconds. Bare number = minutes ("1"=60, "60"=3600). */
function tfToSec(str) {
  var s = String(str == null ? '' : str).trim();
  if (!s) return 0;
  var m = s.match(/^(\d+)([mhdwMHDW]?)$/);
  if (m) {
    var n = parseInt(m[1], 10), u = (m[2] || 'm').toLowerCase();
    return n * (u === 'm' ? 60 : u === 'h' ? 3600 : u === 'd' ? 86400 : 604800);
  }
  var w = s.toUpperCase();
  if (w === 'D') return 86400;
  if (w === 'W') return 604800;
  if (w === 'M') return 2592000;
  return 0;
}

function indexByTime(cs) {
  var map = {}, i;
  for (i = 0; i < cs.length; i++) map[cs[i].time] = i;
  return map;
}

/* src = { cs, byTime, sec } as built by fetchMtf; vals = per-source-bar array */
function toChartSeries(src, vals, chartCs) {
  var out = new Array(chartCs.length), i;
  for (i = 0; i < chartCs.length; i++) out[i] = null;
  if (!src || !src.cs || !src.cs.length) return out;
  var srcSec = src.sec;
  if (!srcSec) return out;
  var chartSecV = barSeconds(chartCs);
  if (!chartSecV) return out;

  if (Math.abs(srcSec - chartSecV) < 1) {
    for (i = 0; i < chartCs.length; i++) {
      var k = src.byTime[chartCs[i].time];
      out[i] = (k == null) ? null : (vals[k] == null ? null : vals[k]);
    }
    return out;
  }
  if (srcSec > chartSecV) {
    for (i = 0; i < chartCs.length; i++) {
      var open = Math.floor(chartCs[i].time / srcSec) * srcSec;
      var kk = src.byTime[open];
      out[i] = (kk == null) ? null : (vals[kk] == null ? null : vals[kk]);
    }
    return out;
  }
  /* lower timeframe: only the bar aligned with the chart bar's open exists */
  for (i = 0; i < chartCs.length; i++) {
    var kl = src.byTime[chartCs[i].time];
    out[i] = (kl == null) ? null : (vals[kl] == null ? null : vals[kl]);
  }
  return out;
}

var mtfStore = {};        /* sec -> { cs, byTime, sec, provider } */
var mtfPending = {};      /* sec -> 1 while in flight */
var mtfError = {};        /* sec -> reason string */

function resetMtf() { mtfStore = {}; mtfPending = {}; mtfError = {}; }

function fetchMtf(sec) {
  var S = SYMBOLS[state.symbol];
  var ivl = gateIntervalFor(sec);
  if (!S || !S.gate) return Promise.reject(new Error('no exchange pair for ' + state.symbol));
  if (!ivl) return Promise.reject(new Error('interval ' + sec + 's not offered'));
  var url = 'https://api.gateio.ws/api/v4/spot/candlesticks?currency_pair=' + S.gate +
            '&interval=' + ivl + '&limit=1000';
  return fetch(url, { headers: { Accept: 'application/json' } }).then(function (r) {
    if (!r.ok) throw new Error('http ' + r.status);
    return r.json();
  }).then(function (arr) {
    if (!Array.isArray(arr) || arr.length < 10) throw new Error('empty');
    var cs = sanitize(parseGateRows(arr, true));
    if (cs.length < 10) throw new Error('only ' + cs.length + ' bars');
    var secV = barSeconds(cs);
    mtfStore[secV || sec] = { cs: cs, byTime: indexByTime(cs), sec: secV || sec, provider: 'gate' };
    delete mtfError[sec];
    return mtfStore[secV || sec];
  });
}

function neededMtfSecs() {
  var set = {}, chartSecV = barSeconds(state.candles) || (TFS[state.tf] && TFS[state.tf].sec);
  state.active.forEach(function (a) {
    var d = DEFS[a.def];
    if (!d || !d.needsMtf) return;
    d.needsMtf(a.params).forEach(function (sec) {
      if (sec && sec !== chartSecV) set[sec] = 1;
    });
  });
  return Object.keys(set).map(Number);
}

function ensureMtf() {
  if (!state.candles.length) return;
  var secs = neededMtfSecs();
  var fired = 0;
  secs.forEach(function (sec) {
    if (mtfStore[sec] || mtfPending[sec]) return;
    mtfPending[sec] = 1; fired++;
    fetchMtf(sec).then(function () {
      delete mtfPending[sec];
      redrawAll();
    }, function (e) {
      delete mtfPending[sec];
      mtfError[sec] = ((e && e.message) || e) + '';
      redrawAll();
    });
  });
  return fired;
}

/* ta.pivotlow / ta.pivothigh, faithful to Pine: the pivot is the bar
   `right` bars back, and it is reported on the CURRENT bar i. Ties count as
   pivots (Pine compares against ta.lowest/ta.highest of the window). */
function pivotFlags(arr, left, right, isHigh) {
  var n = arr.length, flags = new Array(n), i, j;
  for (i = 0; i < n; i++) flags[i] = false;
  for (i = left + right; i < n; i++) {
    var c = i - right, v = arr[c];
    if (v == null || !isFinite(v)) continue;
    var okAll = true;
    for (j = c - left; j <= c + right; j++) {
      if (j < 0 || j >= n) { okAll = false; break; }
      var x = arr[j];
      if (x == null || !isFinite(x)) { okAll = false; break; }
      if (isHigh ? (x > v + 1e-12) : (x < v - 1e-12)) { okAll = false; break; }
    }
    if (okAll) flags[i] = true;
  }
  return flags;
}

/* The four divergence branches of DeMarker Pro, transcribed bar for bar.
   Order matters: Pine tests regular-bull, regular-bear, hidden-bull,
   hidden-bear in sequence and each consumed branch clears the state var,
   so a bar that fires regular cannot also fire hidden on the same pivot. */
function divergences(dm, hi, lo, vo, volAvg, p, osLvl, obLvl) {
  var n = dm.length, lines = [], i;
  var pl = pivotFlags(lo, p.divLookback, p.divLookback, false);
  var ph = pivotFlags(hi, p.divLookback, p.divLookback, true);
  var lp = null, ld = null, lb = null;   /* last low pivot: price, dm, bar */
  var hp = null, hd = null, hb = null;   /* last high pivot */

  for (i = 0; i < n; i++) {
    if (pl[i]) { var c1 = i - p.divLookback; lp = lo[c1]; ld = dm[c1]; lb = c1; }
    if (ph[i]) { var c2 = i - p.divLookback; hp = hi[c2]; hd = dm[c2]; hb = c2; }

    var volOk = !p.volFilter || (vo[i] != null && volAvg != null && volAvg[i] != null && vo[i] >= volAvg[i]);
    var d = dm[i], a = lo[i], b = hi[i];
    if (d == null || a == null || b == null) continue;

    /* regular bullish: lower low in price, higher low in DeMarker, both oversold */
    if (lp != null && (i - lb) >= p.minBarDist) {
      if (Math.abs(a - lp) >= p.minPriceMove && a < lp && d > ld && d < osLvl && ld < osLvl && volOk) {
        lines.push({ i1: lb, y1: ld, i2: i, y2: d, color: p.bullDivColor, width: p.divLineWidth, dotted: false });
        lp = null; ld = null; lb = null;
      }
    }
    /* regular bearish: higher high in price, lower high in DeMarker, both overbought */
    if (hp != null && (i - hb) >= p.minBarDist) {
      if (Math.abs(b - hp) >= p.minPriceMove && b > hp && d < hd && d > obLvl && hd > obLvl && volOk) {
        lines.push({ i1: hb, y1: hd, i2: i, y2: d, color: p.bearDivColor, width: p.divLineWidth, dotted: false });
        hp = null; hd = null; hb = null;
      }
    }
    /* hidden bullish: higher low in price, lower low in DeMarker */
    if (lp != null && (i - lb) >= p.minBarDist) {
      if (a > lp && d < ld && d < osLvl && ld < osLvl && volOk) {
        lines.push({ i1: lb, y1: ld, i2: i, y2: d, color: p.hiddenDivColor, width: p.divLineWidth, dotted: true });
        lp = null; ld = null; lb = null;
      }
    }
    /* hidden bearish: lower high in price, higher high in DeMarker */
    if (hp != null && (i - hb) >= p.minBarDist) {
      if (b < hp && d > hd && d > obLvl && hd > obLvl && volOk) {
        lines.push({ i1: hb, y1: hd, i2: i, y2: d, color: p.hiddenDivColor, width: p.divLineWidth, dotted: true });
        hp = null; hd = null; hb = null;
      }
    }
  }
  return lines;
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
  /* Faithful port of B2_indicator.pine: TWO rolling volume profiles measured in
     HOURS (winH1=24h, winH2=4h), not in bars. The gate fires when price is within
     nearPct of ANY of the four edges, exactly as the Pine does with
     `show2 ? (near(val1) or near(vah1) or near(val2) or near(vah2)) : …`.
     Windows are converted to bar counts from the candles' own spacing, so the
     real span is 24h on 5m and on 1D alike. */
  b2: {
    name: 'B2 — VP Edge + DeMarker gate', pane: 'price',
    params: [
      { k: 'winH1', l: 'Profile 1 window (hours)', t: 'float', d: 24, min: 1, max: 240, step: 1 },
      { k: 'winH2', l: 'Profile 2 window (hours)', t: 'float', d: 4, min: 0, max: 240, step: 1 },
      { k: 'bins', l: 'Price bins', t: 'int', d: 50, min: 10, max: 200 },
      { k: 'vaPct', l: 'Value area %', t: 'float', d: 70, min: 50, max: 95 },
      { k: 'dmLen', l: 'DeMarker length', t: 'int', d: 7, min: 2, max: 100 },
      { k: 'sigLen', l: 'Signal EMA', t: 'int', d: 3, min: 1, max: 50 },
      { k: 'ob', l: 'Overbought', t: 'float', d: 0.8, min: 0.5, max: 0.99, step: 0.01 },
      { k: 'os', l: 'Oversold', t: 'float', d: 0.2, min: 0.01, max: 0.5, step: 0.01 },
      { k: 'nearPct', l: 'Gate distance %', t: 'float', d: 0.25, min: 0.05, max: 2, step: 0.05 },
      { k: 'show2', l: 'Use profile 2 (4h) too', t: 'bool', d: true },
      { k: 'showLevels', l: 'Draw VAH/VAL/POC', t: 'bool', d: true }
    ],
    compute: function (C, p, cs) {
      var barSec = barSeconds(cs);
      var res = { series: [], levels: [], markers: [], lines: [], edges: [], notes: [], meta: {} };
      if (!barSec || cs.length < 10) return res;

      var n1 = Math.round(p.winH1 * 3600 / barSec);
      var n2 = Math.round(p.winH2 * 3600 / barSec);
      /* Pine: `if win < 30 or bar_index < win + 1 -> [na, na, na]`. A window narrower
         than 30 bars has no meaningful value area, and a window wider than the loaded
         history is not silently shrunk — both produce NO profile. On 1D this means the
         24h window is 1 bar, so the real Pine draws nothing there either. */
      var vp1 = (n1 >= 30 && cs.length > n1) ? volumeProfile(cs, n1, p.bins, p.vaPct) : null;
      var vp2 = (p.show2 && p.winH2 > 0 && n2 >= 30 && cs.length > n2) ? volumeProfile(cs, n2, p.bins, p.vaPct) : null;
      if (n1 < 30) res.notes.push('24h window = ' + n1 + ' bar(s) < 30 → no profile (same as the Pine)');
      else if (cs.length <= n1) res.notes.push('need ' + (n1 + 1) + ' bars for the 24h window, have ' + cs.length + ' → no profile');
      if (p.show2 && p.winH2 > 0 && n2 < 30) res.notes.push('4h window = ' + n2 + ' bar(s) < 30 → no profile');

      res.meta.barSec = barSec;
      res.meta.n1 = n1;
      res.meta.n2 = n2;
      res.meta.clamped1 = n1 > cs.length;
      res.meta.clamped2 = vp2 ? res.meta.n2 > cs.length : false;

      if (vp1 && p.showLevels) {
        res.levels.push({ price: vp1.vah, color: '#ff9800', title: 'VAH ' + p.winH1 + 'h', tag: true });
        res.levels.push({ price: vp1.val, color: '#2196f3', title: 'VAL ' + p.winH1 + 'h', tag: true });
        res.levels.push({ price: vp1.poc, color: '#9e9e9e', title: 'POC' });
        res.edges.push(vp1.vah, vp1.val);
      }
      if (vp2 && p.showLevels) {
        res.levels.push({ price: vp2.vah, color: 'rgba(255,152,0,0.55)', title: 'VAH ' + p.winH2 + 'h' });
        res.levels.push({ price: vp2.val, color: 'rgba(33,150,243,0.55)', title: 'VAL ' + p.winH2 + 'h' });
        res.edges.push(vp2.vah, vp2.val);
      }
      res.vp = vp1; res.vp2 = vp2;

      if (!res.edges.length) return res;

      var dm = demarker(cs, p.dmLen);
      var gate = p.nearPct / 100;
      for (var i = 2; i < cs.length; i++) {
        var c = cs[i], near = false, e;
        for (e = 0; e < res.edges.length; e++) {
          if (Math.abs(c.close - res.edges[e]) / c.close < gate) { near = true; break; }
        }
        if (!near) continue;
        if (dm[i] != null && dm[i] < p.os + 0.05 && dm[i] > dm[i - 1]) res.markers.push({ i: i, kind: 'buy', price: c.low, text: 'L' });
        else if (dm[i] != null && dm[i] > p.ob - 0.05 && dm[i] < dm[i - 1]) res.markers.push({ i: i, kind: 'sell', price: c.high, text: 'S' });
      }
      return res;
    }
  },

  /* Verbatim port of DeMarker_Pro_Scalping.pine (16,871 bytes, md5 21c96acc1de9808907b2b2a624074cea — shipped next to this file).
     Three DeMarker instances, each computed on ITS OWN timeframe inside
     request.security(..., lookahead_on) and then mapped onto the chart bars;
     four divergence kinds per instance off ta.pivotlow/pivothigh; optional
     volume filter; and the confluence label, which Pine keeps singular
     (label.delete on every new one) — reproduced via keepHistory. */
  dmpro: {
    name: 'DeMarker Pro (scalping · multi-TF · divergence)', pane: 'osc', scale: '0-1',
    needsMtf: function (p) {
      var out = [];
      [1, 2, 3].forEach(function (k) {
        if (p['enable' + k]) { var sec = tfToSec(p['tf' + k]); if (sec) out.push(sec); }
      });
      return out;
    },
    params: [
      { k: 'enable1', l: 'DeMarker 1 — active', t: 'bool', d: true },
      { k: 'tf1', l: 'DeMarker 1 — timeframe (Pine literal)', t: 'text', d: '1' },
      { k: 'len1', l: 'DeMarker 1 — period', t: 'int', d: 7, min: 1, max: 100 },
      { k: 'col1', l: 'DeMarker 1 — colour', t: 'color', d: '#2962ff' },
      { k: 'showSig1', l: 'DeMarker 1 — signal line', t: 'bool', d: true },
      { k: 'sigLen1', l: 'DeMarker 1 — signal length', t: 'int', d: 3, min: 1, max: 50 },
      { k: 'sigWidth1', l: 'DeMarker 1 — signal width', t: 'int', d: 1, min: 1, max: 4 },
      { k: 'showDiv1', l: 'DeMarker 1 — divergence', t: 'bool', d: true },
      { k: 'enable2', l: 'DeMarker 2 — active', t: 'bool', d: true },
      { k: 'tf2', l: 'DeMarker 2 — timeframe (Pine literal)', t: 'text', d: '5' },
      { k: 'len2', l: 'DeMarker 2 — period', t: 'int', d: 14, min: 1, max: 100 },
      { k: 'col2', l: 'DeMarker 2 — colour', t: 'color', d: '#ff9800' },
      { k: 'showSig2', l: 'DeMarker 2 — signal line', t: 'bool', d: true },
      { k: 'sigLen2', l: 'DeMarker 2 — signal length', t: 'int', d: 5, min: 1, max: 50 },
      { k: 'sigWidth2', l: 'DeMarker 2 — signal width', t: 'int', d: 1, min: 1, max: 4 },
      { k: 'showDiv2', l: 'DeMarker 2 — divergence', t: 'bool', d: true },
      { k: 'enable3', l: 'DeMarker 3 — active', t: 'bool', d: false },
      { k: 'tf3', l: 'DeMarker 3 — timeframe (Pine literal)', t: 'text', d: '15' },
      { k: 'len3', l: 'DeMarker 3 — period', t: 'int', d: 21, min: 1, max: 100 },
      { k: 'col3', l: 'DeMarker 3 — colour', t: 'color', d: '#9c27b0' },
      { k: 'showSig3', l: 'DeMarker 3 — signal line', t: 'bool', d: false },
      { k: 'sigLen3', l: 'DeMarker 3 — signal length', t: 'int', d: 5, min: 1, max: 50 },
      { k: 'sigWidth3', l: 'DeMarker 3 — signal width', t: 'int', d: 1, min: 1, max: 4 },
      { k: 'showDiv3', l: 'DeMarker 3 — divergence', t: 'bool', d: false },
      { k: 'obLevel', l: 'Overbought', t: 'float', d: 0.8, min: 0.5, max: 0.99, step: 0.01 },
      { k: 'osLevel', l: 'Oversold', t: 'float', d: 0.2, min: 0.01, max: 0.5, step: 0.01 },
      { k: 'volFilter', l: 'Volume filter', t: 'bool', d: true },
      { k: 'volAvgLen', l: 'Volume MA length', t: 'int', d: 20, min: 5, max: 200 },
      { k: 'divLookback', l: 'Divergence pivot lookback', t: 'int', d: 25, min: 10, max: 60 },
      { k: 'minBarDist', l: 'Min bars between pivot and signal', t: 'int', d: 4, min: 2, max: 60 },
      { k: 'minPriceMove', l: 'Min price move', t: 'float', d: 0.0001, min: 0, max: 1000, step: 0.0001 },
      { k: 'bullDivColor', l: 'Regular bull divergence colour', t: 'color', d: '#089981' },
      { k: 'bearDivColor', l: 'Regular bear divergence colour', t: 'color', d: '#f23645' },
      { k: 'hiddenDivColor', l: 'Hidden divergence colour', t: 'color', d: '#ffeb3b' },
      { k: 'divLineWidth', l: 'Divergence line width', t: 'int', d: 1, min: 1, max: 3 },
      { k: 'showConfluence', l: 'Confluence signal', t: 'bool', d: true },
      { k: 'keepHistory', l: 'Keep every confluence (Pine keeps only the last)', t: 'bool', d: false },
      { k: 'midLine', l: 'Draw 0.5 midline', t: 'bool', d: true }
    ],
    compute: function (C, p, cs) {
      var res = { series: [], levels: [], markers: [], lines: [], notes: [] };
      var chartSecV = barSeconds(cs);
      var vols = cs.map(function (c) { return c.volume; });
      var volAvg = p.volFilter ? sma(vols, p.volAvgLen) : null;
      var dms = {};
      var slots = 0;

      [1, 2, 3].forEach(function (k) {
        if (!p['enable' + k]) return;
        var wantSec = tfToSec(p['tf' + k]);
        var src = null, how = 'chart';
        if (!wantSec) { res.notes.push('DeMarker ' + k + ': timeframe \'' + p['tf' + k] + '\' unreadable'); return; }
        if (Math.abs(wantSec - chartSecV) < 1) { src = { cs: cs, byTime: indexByTime(cs), sec: chartSecV }; }
        else { src = mtfStore[wantSec]; how = 'MTF'; }
        if (!src || !src.cs) {
          res.notes.push('DeMarker ' + k + ' @ ' + (wantSec / 60) + 'm: no data' +
            (mtfPending[wantSec] ? ' (loading…)' : (mtfError[wantSec] ? ' — ' + mtfError[wantSec] : ' — unavailable on this feed')));
          return;
        }
        var srcDm = demarker(src.cs, p['len' + k]);
        var dm = toChartSeries(src, srcDm, cs);
        var hi = toChartSeries(src, src.cs.map(function (c) { return c.high; }), cs);
        var lo = toChartSeries(src, src.cs.map(function (c) { return c.low; }), cs);
        var vo = toChartSeries(src, src.cs.map(function (c) { return c.volume; }), cs);
        var tag = 'DM' + k + ' ' + (wantSec / 60) + 'm/' + p['len' + k] + (how === 'MTF' ? '' : '*');
        res.series.push({ title: tag, data: dm, color: p['col' + k], width: 2 });
        dms[k] = dm;
        if (p['showSig' + k]) {
          res.series.push({ title: 'sig' + k, data: ema(dm, p['sigLen' + k]), color: p['col' + k], width: p['sigWidth' + k], alpha: 50 });
        }
        if (p['showDiv' + k]) {
          var L = divergences(dm, hi, lo, vo, volAvg, p, p.osLevel, p.obLevel);
          res.lines = res.lines.concat(L);
          res.notes.push('DM' + k + ': ' + L.length + ' divergence(s)');
        }
        slots++;
      });

      res.levels.push({ price: p.obLevel, color: 'rgba(242,54,69,0.6)', title: 'OB' });
      res.levels.push({ price: p.osLevel, color: 'rgba(8,153,129,0.6)', title: 'OS' });
      if (p.midLine) res.levels.push({ price: 0.5, color: 'rgba(120,123,134,0.5)', dotted: true, title: 'Mid' });

      /* confluence: DM1 and DM2 both oversold and both above their signal, or both
         overbought and both below their signal. Pine needs enable1 AND enable2. */
      if (p.showConfluence && dms[1] && dms[2]) {
        var s1 = ema(dms[1], p.sigLen1), s2 = ema(dms[2], p.sigLen2);
        var hits = [], i;
        for (i = 0; i < cs.length; i++) {
          var a = dms[1][i], b = dms[2][i], x = s1[i], y = s2[i];
          if (a == null || b == null || x == null || y == null) continue;
          var bull = a < p.osLevel && b < p.osLevel && a > x && b > y;
          var bear = a > p.obLevel && b > p.obLevel && a < x && b < y;
          if (bull || bear) hits.push({ i: i, bull: bull });
        }
        var shown = p.keepHistory ? hits : (hits.length ? [hits[hits.length - 1]] : []);
        shown.forEach(function (h) {
          res.markers.push({ i: h.i, kind: h.bull ? 'buy' : 'sell', price: 0.5,
            text: h.bull ? 'CONFLUENCE BUY' : 'CONFLUENCE SELL', label: true });
        });
        res.notes.push('confluence: ' + hits.length + ' hit(s)' + (p.keepHistory ? '' : ' — showing last only (Pine label.delete)'));
      } else if (p.showConfluence) {
        res.notes.push('confluence needs DeMarker 1 and 2 both active');
      }
      if (!slots) res.notes.push('no DeMarker slot is active');
      return res;
    }
  },
  /* ══════════ price-pane overlays ══════════ */
  wma: {
    name: 'WMA', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 21, min: 1, max: 400 }],
    compute: function (C, p, cs) { return { series: [{ title: 'WMA ' + p.len, data: wma(C.close, p.len), color: '#26a69a', width: 2 }] }; }
  },
  hma: {
    name: 'Hull MA', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 21, min: 2, max: 400 }],
    compute: function (C, p, cs) { return { series: [{ title: 'HMA ' + p.len, data: hma(C.close, p.len), color: '#ff7043', width: 2 }] }; }
  },
  dema: {
    name: 'DEMA', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 21, min: 1, max: 400 }],
    compute: function (C, p, cs) {
      var e1 = ema(C.close, p.len), e2 = ema(e1, p.len), out = pad(cs.length), i;
      for (i = 0; i < cs.length; i++) out[i] = (e1[i] == null || e2[i] == null) ? null : 2 * e1[i] - e2[i];
      return { series: [{ title: 'DEMA ' + p.len, data: out, color: '#ab47bc', width: 2 }] };
    }
  },
  tema: {
    name: 'TEMA', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 21, min: 1, max: 400 }],
    compute: function (C, p, cs) {
      var e1 = ema(C.close, p.len), e2 = ema(e1, p.len), e3 = ema(e2, p.len), out = pad(cs.length), i;
      for (i = 0; i < cs.length; i++) out[i] = (e1[i] == null || e2[i] == null || e3[i] == null) ? null : 3 * e1[i] - 3 * e2[i] + e3[i];
      return { series: [{ title: 'TEMA ' + p.len, data: out, color: '#42a5f5', width: 2 }] };
    }
  },
  vwma: {
    name: 'VWMA', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 20, min: 1, max: 400 }],
    compute: function (C, p, cs) {
      var pv = C.close.map(function (c, i) { return c * (C.volume[i] || 0); });
      var a = sma(pv, p.len), b = sma(C.volume, p.len), out = pad(cs.length), i;
      for (i = 0; i < cs.length; i++) out[i] = (a[i] == null || b[i] == null || b[i] === 0) ? null : a[i] / b[i];
      return { series: [{ title: 'VWMA ' + p.len, data: out, color: '#ec407a', width: 2 }] };
    }
  },
  alma: {
    name: 'ALMA', pane: 'price',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 21, min: 2, max: 200 }, { k: 'sig', l: 'Sigma', t: 'float', d: 6, min: 1, max: 20 }, { k: 'off', l: 'Offset', t: 'float', d: 0.85, min: 0, max: 1, step: 0.05 }],
    compute: function (C, p, cs) { return { series: [{ title: 'ALMA ' + p.len, data: almaFn(C.close, p.len, p.sig, p.off), color: '#8d6e63', width: 2 }] }; }
  },
  psar: {
    name: 'Parabolic SAR', pane: 'price',
    params: [{ k: 'af0', l: 'Start AF', t: 'float', d: 0.02, min: 0.001, max: 0.5, step: 0.01 }, { k: 'afStep', l: 'Increment', t: 'float', d: 0.02, min: 0.001, max: 0.5, step: 0.01 }, { k: 'afMax', l: 'Max AF', t: 'float', d: 0.2, min: 0.01, max: 1, step: 0.05 }],
    compute: function (C, p, cs) {
      var s = psarFn(cs, p.af0, p.afStep, p.afMax), up = [], dn = [], i;
      for (i = 0; i < cs.length; i++) {
        if (s[i] == null) { up.push(null); dn.push(null); continue; }
        var bull = s[i] < cs[i].close;
        up.push(bull ? s[i] : null); dn.push(bull ? null : s[i]);
      }
      return { series: [{ title: 'SAR up', data: up, color: '#089981', width: 1, dots: true }, { title: 'SAR down', data: dn, color: '#f23645', width: 1, dots: true }] };
    }
  },
  donchian: {
    name: 'Donchian Channel', pane: 'price',
    params: [{ k: 'len', l: 'Channel length', t: 'int', d: 20, min: 2, max: 200 }, { k: 'mid', l: 'Show midpoint', t: 'bool', d: true }],
    compute: function (C, p, cs) {
      var u = hh(C.high, p.len), l = ll(C.low, p.len), mid = [], i;
      for (i = 0; i < cs.length; i++) mid.push((u[i] == null || l[i] == null) ? null : (u[i] + l[i]) / 2);
      var ser = [
        { title: 'DC Upper', data: u, color: '#26a69a', width: 1 },
        { title: 'DC Lower', data: l, color: '#ef5350', width: 1, fillTo: l, fillFrom: u, fillColor: 'rgba(38,166,154,0.10)' }
      ];
      if (p.mid) ser.push({ title: 'DC Mid', data: mid, color: '#b0bec5', width: 1, dash: [3, 3] });
      return { series: ser };
    }
  },
  keltner: {
    name: 'Keltner Channel', pane: 'price',
    params: [{ k: 'emaLen', l: 'EMA length', t: 'int', d: 20, min: 2, max: 200 }, { k: 'atrLen', l: 'ATR length', t: 'int', d: 10, min: 1, max: 100 }, { k: 'mult', l: 'ATR mult', t: 'float', d: 1.5, min: 0.5, max: 6, step: 0.1 }],
    compute: function (C, p, cs) {
      var e = ema(C.close, p.emaLen), a = atrOf(cs, p.atrLen), u = [], l = [], i;
      for (i = 0; i < cs.length; i++) {
        u.push(e[i] == null || a[i] == null ? null : e[i] + p.mult * a[i]);
        l.push(e[i] == null || a[i] == null ? null : e[i] - p.mult * a[i]);
      }
      return { series: [
        { title: 'KC Upper', data: u, color: '#7e57c2', width: 1 },
        { title: 'KC Basis', data: e, color: '#b0bec5', width: 1, dash: [2, 2] },
        { title: 'KC Lower', data: l, color: '#7e57c2', width: 1, fillTo: l, fillFrom: u, fillColor: 'rgba(126,87,194,0.10)' }
      ] };
    }
  },
  sr: {
    name: 'Support / Resistance pivots', pane: 'price',
    params: [{ k: 'left', l: 'Pivot left bars', t: 'int', d: 10, min: 2, max: 60 }, { k: 'right', l: 'Pivot right bars', t: 'int', d: 10, min: 2, max: 60 }, { k: 'maxLines', l: 'Levels to keep', t: 'int', d: 6, min: 1, max: 20 }],
    compute: function (C, p, cs) {
      var pl = pivotFlags(C.low, p.left, p.right, false), ph = pivotFlags(C.high, p.left, p.right, true);
      var lows = [], highs = [], i;
      for (i = 0; i < cs.length; i++) {
        if (pl[i]) lows.push({ i: i - p.right, price: C.low[i - p.right] });
        if (ph[i]) highs.push({ i: i - p.left, price: C.high[i - p.left] });
      }
      var res = { series: [], levels: [], markers: [], notes: [] };
      lows.slice(-p.maxLines).forEach(function (L) { res.levels.push({ price: L.price, color: 'rgba(8,153,129,0.75)', title: 'S' }); res.markers.push({ i: L.i, kind: 'buy', price: L.price, text: 'S' }); });
      highs.slice(-p.maxLines).forEach(function (H) { res.levels.push({ price: H.price, color: 'rgba(242,54,69,0.75)', title: 'R' }); res.markers.push({ i: H.i, kind: 'sell', price: H.price, text: 'R' }); });
      res.notes.push(lows.length + ' low pivot(s), ' + highs.length + ' high pivot(s) — keeping last ' + p.maxLines + ' each');
      return res;
    }
  },
  fib: {
    name: 'Auto Fib Retracement', pane: 'price',
    params: [{ k: 'lookback', l: 'Range lookback (bars)', t: 'int', d: 120, min: 10, max: 500 }],
    compute: function (C, p, cs) {
      var n = Math.min(cs.length, p.lookback), seg = cs.slice(cs.length - n);
      var hi = -Infinity, lo = Infinity, i;
      for (i = 0; i < seg.length; i++) { hi = Math.max(hi, seg[i].high); lo = Math.min(lo, seg[i].low); }
      var rng = hi - lo, res = { series: [], levels: [], notes: [] };
      if (!(rng > 0)) { res.notes.push('flat range — no fib levels'); return res; }
      [0, 0.236, 0.382, 0.5, 0.618, 0.786, 1].forEach(function (f) {
        res.levels.push({ price: hi - rng * f, color: 'rgba(255,193,7,0.55)', title: (f * 100).toFixed(1) + '%' });
      });
      res.notes.push('range ' + n + ' bars: ' + lo.toFixed(2) + ' → ' + hi.toFixed(2));
      return res;
    }
  },
  session: {
    name: 'Session Open / High / Low (UTC)', pane: 'price',
    params: [],
    compute: function (C, p, cs) {
      if (!cs.length) return { series: [], levels: [], notes: [] };
      var day = Math.floor(cs[cs.length - 1].time / 86400) * 86400;
      var o = null, hi = -Infinity, lo = Infinity, i;
      for (i = 0; i < cs.length; i++) {
        if (cs[i].time < day) continue;
        if (o == null) o = cs[i].open;
        hi = Math.max(hi, cs[i].high); lo = Math.min(lo, cs[i].low);
      }
      var res = { series: [], levels: [], notes: [] };
      if (o == null) { res.notes.push('no bars in the current UTC session'); return res; }
      res.levels.push({ price: o, color: 'rgba(41,98,255,0.8)', title: 'Open' });
      res.levels.push({ price: hi, color: 'rgba(8,153,129,0.8)', title: 'SH' });
      res.levels.push({ price: lo, color: 'rgba(242,54,69,0.8)', title: 'SL' });
      res.notes.push('session ' + new Date(day * 1000).toISOString().slice(0, 10));
      return res;
    }
  },
  patterns: {
    name: 'Candlestick Patterns', pane: 'price',
    params: [{ k: 'dojiPct', l: 'Doji body ≤ % of range', t: 'float', d: 10, min: 1, max: 40 }, { k: 'wickMult', l: 'Hammer wick ≥ × body', t: 'float', d: 2, min: 1, max: 6, step: 0.1 }, { k: 'showDoji', l: 'Doji', t: 'bool', d: true }, { k: 'showReversal', l: 'Hammer / Shooting star', t: 'bool', d: true }, { k: 'showEngulf', l: 'Engulfing', t: 'bool', d: true }],
    compute: function (C, p, cs) {
      var res = { series: [], levels: [], markers: [], notes: [] }, i, cnt = 0;
      for (i = 1; i < cs.length; i++) {
        var c = cs[i], b = cs[i - 1];
        var rng = c.high - c.low, body = Math.abs(c.close - c.open);
        if (rng <= 0) continue;
        var upWick = c.high - Math.max(c.open, c.close), dnWick = Math.min(c.open, c.close) - c.low;
        if (p.showDoji && body / rng * 100 <= p.dojiPct) { res.markers.push({ i: i, kind: 'flat', price: c.high, text: 'D', color: '#90a4ae' }); cnt++; continue; }
        if (p.showReversal) {
          if (body > 0 && dnWick >= p.wickMult * body && upWick <= body) { res.markers.push({ i: i, kind: 'buy', price: c.low, text: 'H' }); cnt++; continue; }
          if (body > 0 && upWick >= p.wickMult * body && dnWick <= body) { res.markers.push({ i: i, kind: 'sell', price: c.high, text: 'SS' }); cnt++; continue; }
        }
        if (p.showEngulf) {
          var bRng = b.high - b.low;
          if (bRng > 0 && body > Math.abs(b.close - b.open)) {
            if (b.close < b.open && c.close > c.open && c.close >= b.open && c.open <= b.close) { res.markers.push({ i: i, kind: 'buy', price: c.low, text: 'ENG+' }); cnt++; continue; }
            if (b.close > b.open && c.close < c.open && c.open >= b.close && c.close <= b.open) { res.markers.push({ i: i, kind: 'sell', price: c.high, text: 'ENG-' }); cnt++; continue; }
          }
        }
      }
      res.notes.push(cnt + ' pattern(s) detected');
      return res;
    }
  },

  /* ══════════ oscillator pane ══════════ */
  willr: {
    name: 'Williams %R', pane: 'osc', scale: '-100-0',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 14, min: 2, max: 100 }],
    compute: function (C, p, cs) {
      return { series: [{ title: '%R ' + p.len, data: willr(cs, p.len), color: '#e91e63', width: 2 }],
               levels: [{ price: -20, color: 'rgba(242,54,69,0.55)' }, { price: -80, color: 'rgba(8,153,129,0.55)' }] };
    }
  },
  cci: {
    name: 'CCI', pane: 'osc', scale: 'auto',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 20, min: 2, max: 200 }],
    compute: function (C, p, cs) {
      return { series: [{ title: 'CCI ' + p.len, data: cci(cs, p.len), color: '#00bcd4', width: 2 }],
               levels: [{ price: 100, color: 'rgba(242,54,69,0.55)' }, { price: -100, color: 'rgba(8,153,129,0.55)' }, { price: 0, color: 'rgba(120,123,134,0.4)' }] };
    }
  },
  mfi: {
    name: 'Money Flow Index', pane: 'osc', scale: '0-100',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 14, min: 2, max: 100 }],
    compute: function (C, p, cs) {
      return { series: [{ title: 'MFI ' + p.len, data: mfi(cs, p.len), color: '#7c4dff', width: 2 }],
               levels: [{ price: 80, color: 'rgba(242,54,69,0.55)' }, { price: 20, color: 'rgba(8,153,129,0.55)' }] };
    }
  },
  roc: {
    name: 'ROC (rate of change)', pane: 'osc', scale: 'auto',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 12, min: 1, max: 200 }],
    compute: function (C, p, cs) {
      return { series: [{ title: 'ROC ' + p.len, data: rocAt(C.close, p.len), color: '#ff6e40', width: 2 }], levels: [{ price: 0, color: 'rgba(120,123,134,0.4)' }] };
    }
  },
  mom: {
    name: 'Momentum', pane: 'osc', scale: 'auto',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 12, min: 1, max: 200 }],
    compute: function (C, p, cs) {
      var out = pad(cs.length), i;
      for (i = p.len; i < cs.length; i++) out[i] = C.close[i] - C.close[i - p.len];
      return { series: [{ title: 'MOM ' + p.len, data: out, color: '#ffd740', width: 2 }], levels: [{ price: 0, color: 'rgba(120,123,134,0.4)' }] };
    }
  },
  adx: {
    name: 'ADX / DI', pane: 'osc', scale: '0-100',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 14, min: 2, max: 100 }, { k: 'trend', l: 'Trend threshold', t: 'float', d: 25, min: 10, max: 60 }],
    compute: function (C, p, cs) {
      var a = adxFn(cs, p.len);
      return { series: [
        { title: '+DI', data: a.diPlus, color: '#089981', width: 1.5 },
        { title: '-DI', data: a.diMinus, color: '#f23645', width: 1.5 },
        { title: 'ADX', data: a.adx, color: '#2962ff', width: 2 }
      ], levels: [{ price: p.trend, color: 'rgba(255,152,0,0.6)', title: 'trend' }] };
    }
  },
  ao: {
    name: 'Awesome Oscillator', pane: 'osc', scale: 'auto', bars: true,
    params: [{ k: 'fast', l: 'Fast SMA', t: 'int', d: 5, min: 2, max: 50 }, { k: 'slow', l: 'Slow SMA', t: 'int', d: 34, min: 3, max: 200 }],
    compute: function (C, p, cs) {
      var m = hl2(cs), a = sma(m, p.fast), b = sma(m, p.slow), out = pad(cs.length), i;
      for (i = 0; i < cs.length; i++) out[i] = (a[i] == null || b[i] == null) ? null : a[i] - b[i];
      return { series: [{ title: 'AO', data: out, color: '#26a69a', width: 1, bars: true }], levels: [{ price: 0, color: 'rgba(120,123,134,0.4)' }] };
    }
  },
  cmo: {
    name: 'CMO', pane: 'osc', scale: '-100-100',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 14, min: 2, max: 100 }],
    compute: function (C, p, cs) {
      var n = cs.length, up = pad(n), dn = pad(n), i, out = pad(n);
      for (i = 1; i < n; i++) {
        var d = C.close[i] - C.close[i - 1];
        up[i] = d > 0 ? d : 0; dn[i] = d < 0 ? -d : 0;
      }
      for (i = p.len; i < n; i++) {
        var su = 0, sd = 0, j;
        for (j = i - p.len + 1; j <= i; j++) { su += up[j]; sd += dn[j]; }
        out[i] = (su + sd) === 0 ? null : 100 * (su - sd) / (su + sd);
      }
      return { series: [{ title: 'CMO ' + p.len, data: out, color: '#f06292', width: 2 }], levels: [{ price: 50, color: 'rgba(242,54,69,0.55)' }, { price: -50, color: 'rgba(8,153,129,0.55)' }, { price: 0, color: 'rgba(120,123,134,0.4)' }] };
    }
  },
  uo: {
    name: 'Ultimate Oscillator', pane: 'osc', scale: '0-100',
    params: [{ k: 'p1', l: 'Period 1', t: 'int', d: 7, min: 2, max: 30 }, { k: 'p2', l: 'Period 2', t: 'int', d: 14, min: 3, max: 40 }, { k: 'p3', l: 'Period 3', t: 'int', d: 28, min: 4, max: 60 }],
    compute: function (C, p, cs) {
      return { series: [{ title: 'UO', data: uoFn(cs, p.p1, p.p2, p.p3), color: '#4dd0e1', width: 2 }],
               levels: [{ price: 70, color: 'rgba(242,54,69,0.55)' }, { price: 30, color: 'rgba(8,153,129,0.55)' }] };
    }
  },
  tsi: {
    name: 'TSI', pane: 'osc', scale: 'auto',
    params: [{ k: 'len', l: 'Long smoothing', t: 'int', d: 25, min: 2, max: 100 }, { k: 'smooth', l: 'Short smoothing', t: 'int', d: 13, min: 2, max: 60 }],
    compute: function (C, p, cs) {
      return { series: [{ title: 'TSI', data: tsiFn(C.close, p.len, p.smooth), color: '#ba68c8', width: 2 },
                        { title: 'TSI sig', data: ema(tsiFn(C.close, p.len, p.smooth), 7), color: '#ff9800', width: 1.5 }],
               levels: [{ price: 0, color: 'rgba(120,123,134,0.4)' }, { price: 25, color: 'rgba(242,54,69,0.4)' }, { price: -25, color: 'rgba(8,153,129,0.4)' }] };
    }
  },
  srsi: {
    name: 'StochRSI', pane: 'osc', scale: '0-100',
    params: [{ k: 'rsiLen', l: 'RSI length', t: 'int', d: 14, min: 2, max: 60 }, { k: 'kLen', l: '%K length', t: 'int', d: 14, min: 2, max: 60 }, { k: 'dLen', l: '%D length', t: 'int', d: 3, min: 1, max: 20 }],
    compute: function (C, p, cs) {
      var r = rsi(C.close, p.rsiLen), rh = hh(r, p.kLen), rl = ll(r, p.kLen), k = [], i;
      for (i = 0; i < cs.length; i++) {
        if (rh[i] == null || rl[i] == null || r[i] == null || rh[i] === rl[i]) { k.push(null); continue; }
        k.push((r[i] - rl[i]) / (rh[i] - rl[i]) * 100);
      }
      return { series: [{ title: 'StochRSI %K', data: k, color: '#2962ff', width: 2 }, { title: '%D', data: sma(k, p.dLen), color: '#ff9800', width: 1.5 }],
               levels: [{ price: 80, color: 'rgba(242,54,69,0.55)' }, { price: 20, color: 'rgba(8,153,129,0.55)' }] };
    }
  },
  coppock: {
    name: 'Coppock Curve', pane: 'osc', scale: 'auto',
    params: [{ k: 'wmaLen', l: 'WMA length', t: 'int', d: 10, min: 2, max: 50 }, { k: 'fast', l: 'ROC long', t: 'int', d: 14, min: 2, max: 60 }, { k: 'slow', l: 'ROC short', t: 'int', d: 11, min: 2, max: 60 }],
    compute: function (C, p, cs) {
      var a = rocAt(C.close, p.fast), b = rocAt(C.close, p.slow), sum = pad(cs.length), i;
      for (i = 0; i < cs.length; i++) sum[i] = (a[i] == null || b[i] == null) ? null : a[i] + b[i];
      return { series: [{ title: 'Coppock', data: wma(sum, p.wmaLen), color: '#9ccc65', width: 2 }], levels: [{ price: 0, color: 'rgba(120,123,134,0.4)' }] };
    }
  },
  fisher: {
    name: 'Fisher Transform', pane: 'osc', scale: 'auto',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 10, min: 2, max: 60 }],
    compute: function (C, p, cs) {
      var f = fisherFn(cs, p.len);
      return { series: [{ title: 'Fisher', data: f.fisher, color: '#00e5ff', width: 2 }, { title: 'Trigger', data: f.signal, color: '#ff9800', width: 1.5 }], levels: [{ price: 0, color: 'rgba(120,123,134,0.4)' }] };
    }
  },

  /* ══════════ volume pane ══════════ */
  obv: {
    name: 'OBV', pane: 'vol',
    params: [{ k: 'maLen', l: 'OBV MA', t: 'int', d: 20, min: 0, max: 100 }],
    compute: function (C, p, cs) {
      var o = obvFn(cs), ser = [{ title: 'OBV', data: o, color: '#42a5f5', width: 2 }];
      if (p.maLen > 0) ser.push({ title: 'OBV MA ' + p.maLen, data: sma(o, p.maLen), color: '#ff9800', width: 1.5 });
      return { series: ser };
    }
  },
  ad: {
    name: 'Accumulation / Distribution', pane: 'vol',
    params: [],
    compute: function (C, p, cs) { return { series: [{ title: 'A/D', data: adFn(cs), color: '#ab47bc', width: 2 }] }; }
  },
  cmf: {
    name: 'Chaikin Money Flow', pane: 'vol',
    params: [{ k: 'len', l: 'Length', t: 'int', d: 20, min: 2, max: 100 }],
    compute: function (C, p, cs) {
      return { series: [{ title: 'CMF ' + p.len, data: cmfFn(cs, p.len), color: '#26a69a', width: 2 }], levels: [{ price: 0, color: 'rgba(120,123,134,0.4)' }] };
    }
  },
  nvi: {
    name: 'Negative Volume Index', pane: 'vol',
    params: [],
    compute: function (C, p, cs) { return { series: [{ title: 'NVI', data: nviFn(cs), color: '#ef5350', width: 2 }] }; }
  },
  vosc: {
    name: 'Volume Oscillator %', pane: 'vol',
    params: [{ k: 'fast', l: 'Fast MA', t: 'int', d: 5, min: 2, max: 50 }, { k: 'slow', l: 'Slow MA', t: 'int', d: 20, min: 3, max: 200 }],
    compute: function (C, p, cs) {
      var a = sma(C.volume, p.fast), b = sma(C.volume, p.slow), out = pad(cs.length), i;
      for (i = 0; i < cs.length; i++) out[i] = (a[i] == null || b[i] == null || b[i] === 0) ? null : 100 * (a[i] - b[i]) / b[i];
      return { series: [{ title: 'VOSC', data: out, color: '#ffca28', width: 2, bars: true }], levels: [{ price: 0, color: 'rgba(120,123,134,0.4)' }] };
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
/* Size the osc pane by how many indicators actually live there. A fixed 118px
   crushed DeMarker + dmpro's four series into an unreadable knot. */
function paneCount(which) {
  var n = 0;
  state.active.forEach(function (a) { var d = DEFS[a.def]; if (d && d.pane === which) n++; });
  return n;
}

function computeGeo() {
  var W = els.stack.clientWidth, H = els.stack.clientHeight;
  var panes = paneSet();
  var volH = panes.vol ? VOL_H : 0;
  var oscH = panes.osc ? Math.min(340, OSC_H + Math.max(0, paneCount('osc') - 1) * 56) : 0;
  var plotW = Math.max(60, W - AXIS_W);
  var priceH = Math.max(120, H - AXIS_H - volH - oscH);
  var over = (priceH + volH + oscH + AXIS_H) - H;
  if (over > 0 && oscH > OSC_MIN) oscH = Math.max(OSC_MIN, oscH - over);
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
    var bh = Math.max(1.5, Math.abs(yc - yo)), by = Math.min(yo, yc);
    if (cd.provisional) {
      /* the bar still forming: filled, then outlined so it is unmistakably not final */
      ctx.fillRect(x0, by, bw, bh);
      ctx.strokeStyle = '#e0e3eb'; ctx.lineWidth = 1;
      ctx.strokeRect(x0 + 0.5, by + 0.5, Math.max(1, bw - 1), Math.max(1, bh - 1));
    } else {
      ctx.fillRect(x0, by, bw, bh);
    }
  }

  /* markers — drawn in the pane the indicator lives in, not always price */
  state.computed.forEach(function (c) {
    var toY = null;
    if (c.pane === 'price') toY = ps.toY;
    else if (c.pane === 'osc' && os) toY = os.toY;
    else if (c.pane === 'vol' && geo.volH) toY = vs.toY;
    if (!toY) return;
    (c.r.markers || []).forEach(function (m) {
      if (m.i < v.start || m.i >= v.end) return;
      var k = m.i - v.start;
      var x = barX(geo, v, k) + bw / 2;
      var buy = m.kind === 'buy';
      var col = m.color || (m.kind === 'flat' ? '#90a4ae' : buy ? '#089981' : '#f23645');

      if (m.label) {
        /* Pine label.new — a boxed caption pinned to a value, not an arrow */
        var txt = m.text || '';
        ctx.font = 'bold 9px sans-serif';
        var lw = ctx.measureText(txt).width + 10;
        var ly = toY(m.price);
        var bx = Math.max(2, Math.min(x - lw / 2, geo.plotW - lw - 2));
        ctx.fillStyle = col;
        ctx.fillRect(bx, ly - 8, lw, 16);
        ctx.fillStyle = '#fff'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
        ctx.fillText(txt, bx + lw / 2, ly);
        return;
      }
      var y = buy ? toY(m.price) + 14 : toY(m.price) - 14;
      ctx.fillStyle = col;
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
      (c.r.lines || []).forEach(function (L) {
        /* a divergence joins two bars — draw it when either end is on screen,
           clamping the off-screen end to the viewport edge */
        if (L.i2 < v.start || L.i1 >= v.end) return;
        var k1 = Math.max(0, Math.min(v.n - 1, L.i1 - v.start));
        var k2 = Math.max(0, Math.min(v.n - 1, L.i2 - v.start));
        if (k2 <= k1) return;
        ctx.strokeStyle = L.color || '#ffeb3b';
        ctx.lineWidth = L.width || 1;
        if (L.dotted) ctx.setLineDash([2, 2]); else ctx.setLineDash([]);
        ctx.beginPath();
        ctx.moveTo(barX(geo, v, k1) + bw / 2, os.toY(L.y1));
        ctx.lineTo(barX(geo, v, k2) + bw / 2, os.toY(L.y2));
        ctx.stroke();
        ctx.setLineDash([]);
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

  drawLegends(geo, v, ps, geo.volH ? vs : null, os);
}

function drawLine(ctx, s, geo, v, toY) {
  ctx.strokeStyle = s.color || '#2962ff';
  ctx.fillStyle = s.color || '#2962ff';
  ctx.lineWidth = s.width || 1.5;
  if (s.alpha) ctx.globalAlpha = Math.max(0.05, 1 - s.alpha / 100);
  if (s.dots) {
    var dk, dv, dx, dy;
    for (dk = 0; dk < v.n; dk++) {
      dv = s.data[v.start + dk];
      if (dv == null) continue;
      dx = barX(geo, v, dk) + barW(geo, v) / 2;
      dy = toY(dv);
      ctx.beginPath(); ctx.arc(dx, dy, Math.max(1.2, s.width || 1.5), 0, Math.PI * 2); ctx.fill();
    }
    ctx.globalAlpha = 1;
    return;
  }
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
  ctx.globalAlpha = 1;
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

function lastOf(arr, v) {
  var k;
  if (arr == null) return null;
  for (k = v.end - 1; k >= v.start; k--) if (arr[k] != null) return arr[k];
  return null;
}

/* One legend row per indicator, inside its own pane, in that pane's units.
   Previously vol/osc were skipped outright, so Volume and every oscillator
   showed no values at all. */
function drawLegends(geo, v, ps, vs, os) {
  var ctx = baseCtx, rows = [];
  ctx.font = '11px sans-serif'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';

  function paneRow(which, top) {
    var y = top + 12;
    state.computed.forEach(function (c) {
      if (c.pane !== which) return;
      var fmt = which === 'price' ? fmtAxis
              : which === 'vol' ? fmtVol
              : function (x) { return x == null ? '—' : x.toFixed(3); };
      var bits = [{ t: c.title, col: '#f0f3fa', bold: true }];
      (c.r.series || []).forEach(function (s) {
        var lv = lastOf(s.data, v);
        bits.push({ t: s.title + ' ' + (lv == null ? '—' : fmt(lv)), col: s.color || '#d1d4dc' });
      });
      if (!(c.r.series || []).length && (c.r.levels || []).length) {
        c.r.levels.forEach(function (L) {
          if (L.price == null) return;
          bits.push({ t: (L.title || 'lvl') + ' ' + fmt(L.price), col: '#9e9e9e' });
        });
      }
      if ((c.r.markers || []).length) {
        var vis = c.r.markers.filter(function (m) { return m.i >= v.start && m.i < v.end; });
        bits.push({ t: vis.length + ' signal' + (vis.length === 1 ? '' : 's') + ' in view', col: '#787b86' });
      }
      rows.push({ y: y, bits: bits });
      y += 14;
    });
  }
  paneRow('price', geo.priceTop);
  if (geo.volH) paneRow('vol', geo.volTop);
  if (geo.oscH) paneRow('osc', geo.oscTop);

  rows.forEach(function (r) {
    var x = 6, w = 0, i;
    for (i = 0; i < r.bits.length; i++) w += ctx.measureText(r.bits[i].t).width + (i ? 14 : 0);
    ctx.fillStyle = 'rgba(19,23,34,0.88)';
    ctx.fillRect(2, r.y - 9, Math.min(w + 12, geo.plotW - 6), 17);
    for (i = 0; i < r.bits.length; i++) {
      if (i) { ctx.fillStyle = '#3a404f'; ctx.fillRect(x - 7, r.y - 4, 1, 8); }
      ctx.fillStyle = r.bits[i].col;
      ctx.font = (r.bits[i].bold ? 'bold ' : '') + '11px sans-serif';
      ctx.fillText(r.bits[i].t, x, r.y);
      x += ctx.measureText(r.bits[i].t).width + 14;
    }
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
function parseGateRows(arr, keepForming) {
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
  if (lastRaw && String(lastRaw[7]) === 'false') {
    /* Dropping it outright is what made the chart look frozen: the newest
       candle on screen was then a CLOSED bar, which by definition cannot move
       until the next one closes. Keep it and tag it, so the user watches the
       live bar grow and can still tell it is not final. */
    if (keepForming && cs.length) cs[cs.length - 1].provisional = true;
    else cs.pop();
  }
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
      var clean = sanitize(parseGateRows(arr, true));
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
  /* MTF bars belong to a symbol, so a symbol switch invalidates them */
  if (state.symbolLoadedFor !== wantSym) { resetMtf(); state.symbolLoadedFor = wantSym; }
  state.source = mode;
  state.provider = provider;
  state.note = note || '';
  state.updatedAt = Date.now();
  state.offset = Math.min(state.offset, Math.max(0, candles.length - state.visible - 1));
  state.busy = false;
  loadCtl = null;
  updateHud();
  redrawAll();
  /* kick off any extra timeframe series the active indicators declared */
  ensureMtf();
}

/* ---------------- Live layer ----------------
   A full refetch every 60s is both wasteful and, worse, invisible: between two
   polls nothing moves. pollLatest() asks for the last few bars only (limit=3),
   merges them by timestamp, and repaints ONLY if something actually changed —
   so a 1m candle visibly grows tick to tick and the cost is one tiny request. */
var POLL_MS = 5000;
var pollFails = 0, pollCount = 0, lastChangeAt = 0;

function localTick() {
  var last = state.candles[state.candles.length - 1];
  if (!last) return;
  var d = (Math.random() - 0.49) * last.close * 0.0012;
  last.close += d;
  last.high = Math.max(last.high, last.close);
  last.low = Math.min(last.low, last.close);
  last.provisional = true;
  lastChangeAt = Date.now();
  updateHud(); scheduleBase();
}

async function pollLatest() {
  pollCount++;
  if (!state.candles.length) { loadData(false); return; }
  if (state.source === 'sim') { localTick(); return; }
  var S = SYMBOLS[state.symbol], spec = TFS[state.tf];
  if (!S || !S.gate || !spec || !spec.gate) return;

  var url = 'https://api.gateio.ws/api/v4/spot/candlesticks?currency_pair=' + S.gate +
            '&interval=' + spec.gate + '&limit=3';
  try {
    var r = await fetch(url, { headers: { Accept: 'application/json' } });
    if (!r.ok) throw new Error('http ' + r.status);
    var arr = await r.json();
    if (!Array.isArray(arr) || !arr.length) throw new Error('empty');
    var inc = sanitize(parseGateRows(arr, true));
    var byT = indexByTime(state.candles);
    var changed = 0, i;
    for (i = 0; i < inc.length; i++) {
      var b = inc[i], k = byT[b.time];
      if (k != null) {
        var cur = state.candles[k];
        if (cur.close !== b.close || cur.high !== b.high || cur.low !== b.low ||
            cur.open !== b.open || cur.volume !== b.volume) {
          state.candles[k] = b; changed++;
        }
      } else if (b.time > state.candles[state.candles.length - 1].time) {
        state.candles.push(b); changed++;
      }
    }
    pollFails = 0;
    state.pollErr = '';
    if (changed) {
      lastChangeAt = Date.now();
      state.updatedAt = Date.now();
      recompute(); scheduleBase();
    }
    /* MTF slots go stale too: refresh them every ~30s so DM1 (1m) keeps pace */
    if (pollCount % 6 === 0) {
      var need = neededMtfSecs(), j;
      for (j = 0; j < need.length; j++) delete mtfStore[need[j]];
      if (ensureMtf()) { /* repaint once the extras land */ }
    }
    updateHud();
  } catch (e) {
    pollFails++;
    state.pollErr = ((e && e.message) || e) + '';
    updateHud();
  }
}

function refreshTick() { pollLatest(); }

/* Heartbeat reflects the DATA, not a CSS loop. Before this the dot pulsed
   green forever, advertising a liveness that did not exist. */
function heartbeat() {
  var el = els.liveDot;
  var barSec = barSeconds(state.candles) || 60;
  var age = lastChangeAt ? (Date.now() - lastChangeAt) / 1000 : Infinity;
  var cls, title;
  if (state.source === 'sim') { cls = 'dot sim'; title = 'SIMULATED — no data source reachable'; }
  else if (pollFails >= 3) { cls = 'dot bad'; title = 'feed failing: ' + (state.pollErr || 'unknown') + ' (' + pollFails + ' in a row)'; }
  else if (age > barSec + 30) { cls = 'dot warn'; title = 'data is ' + Math.round(age) + 's old (bar = ' + barSec + 's) — feed stalled'; }
  else { cls = 'dot live'; title = 'LIVE — last change ' + Math.round(age) + 's ago, polling every ' + (POLL_MS / 1000) + 's'; }
  if (el) {
    if (el.className !== cls) el.className = cls;
    el.title = title;
  }
  return { cls: cls, title: title, ageSec: Math.round(age), barSec: barSec, fails: pollFails };
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

  /* countdown to the close of the forming bar — the clearest proof the feed moves */
  if (els.hNext) {
    var barSec = barSeconds(cs) || (TFS[state.tf] && TFS[state.tf].sec) || 60;
    var isProv = !!cs[cs.length - 1].provisional;
    var left = cs[cs.length - 1].time + barSec - Math.floor(Date.now() / 1000);
    if (!isProv) els.hNext.textContent = 'last bar CLOSED · poll ' + (POLL_MS / 1000) + 's';
    else if (left > 0) els.hNext.textContent = 'forming bar closes in ' + left + 's';
    else els.hNext.textContent = 'bar closing…';
    els.hNext.className = isProv && left > 0 ? 'live-count' : 'stale-count';
  }
  heartbeat();
}

function renderChips() {
  if (!els.chips) return;
  els.chips.innerHTML = '';
  if (els.catBtn) {
    var lbl = els.catBtn.querySelector('.txt');
    if (lbl) lbl.textContent = 'Indicators (' + state.active.length + ')';
  }
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
    var cc = (state.computed || []).filter(function (x) { return x.uid === a.uid; })[0];
    var notes = cc && cc.r && cc.r.notes && cc.r.notes.length ? cc.r.notes.join(' · ') : '';
    w.className = 'chip ' + (errs[a.uid] ? 'chip-sim' : (notes && /no data|unavailable|needs|< 30|no reachable/.test(notes) ? 'chip-cache' : 'chip-on'));
    if (errs[a.uid]) w.title = 'compute error: ' + errs[a.uid];
    else if (notes) w.title = notes;
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
    /* a newly shipped indicator must reach browsers that already hold prefs,
       otherwise it looks like the feature was never added */
    if (DEFS.dmpro && !state.active.some(function (a) { return a.def === 'dmpro'; })) {
      /* dmpro is a superset of the single DeMarker (3 slots + divergence +
         confluence), so it REPLACES it instead of stacking a second pane. */
      if (state.active.some(function (a) { return a.def === 'demarker'; })) {
        state.active = state.active.filter(function (a) { return a.def !== 'demarker'; });
      }
      var dp = {};
      DEFS.dmpro.params.forEach(function (x) { dp[x.k] = x.d; });
      state.active.push({ uid: state.uid++, def: 'dmpro', params: dp, title: DEFS.dmpro.name });
    }
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
  els.liveDot = document.getElementById('liveDot');
  els.hNext = document.getElementById('hNext');
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
    addIndicator('dmpro');
  }
  renderChips();

  bindEvents();
  sizeCanvases();
  loadData(false);

  setInterval(refreshTick, POLL_MS);
  setInterval(updateHud, 1000);   /* countdown only — no refetch, no repaint */
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
    errors: (state.computed || []).filter(function (c) { return c.error; }).map(function (c) { return c.def + ': ' + c.error; }),
    notes: (state.computed || []).filter(function (c) { return c.r && c.r.notes && c.r.notes.length; }).map(function (c) { return c.def + ': ' + c.r.notes.join(' | '); }),
    mtf: Object.keys(mtfStore).map(function (k) { return k + 's=' + (mtfStore[k].cs ? mtfStore[k].cs.length : 0) + 'bars'; }),
    mtfPending: Object.keys(mtfPending),
    mtfError: Object.keys(mtfError).map(function (k) { return k + 's: ' + mtfError[k]; })
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
