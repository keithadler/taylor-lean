import * as React from 'react';
const e = React.createElement;

// Colors: a dark panel of its own, so it reads the same in a light or dark editor.
const BG = '#0b0d12', PANEL = '#12151c', GRID = '#2a3040', MESH = '#7f8bb3', INK = '#e8eaf0', DIM = '#8a90a2';
const TEAL = '#5fd4b0', ORANGE = '#f2b35e', WHITE = '#ffffff', RED = '#ff7a7a';
const MONO = "ui-monospace, 'SF Mono', Menlo, Consolas, monospace";
const SANS = "-apple-system, 'Segoe UI', Inter, Helvetica, Arial, sans-serif";
const SERIF = "'CMU Serif', 'Latin Modern Roman', 'STIX Two Text', Georgia, serif";

const rat = ([p, q]) => p / q;
const fmt = (v, d = 4) => (Math.abs(v) < 5e-5 ? 0 : v).toFixed(d);

// The loss arrives from Lean as monomials c·xⁱ·yʲ (Taylor.terms, proved equal to Taylor.L).
function makeLoss(terms) {
  const ts = terms.map(([c, i, j]) => [rat(c), i, j]);
  const pw = (b, n) => (n <= 0 ? 1 : b ** n);
  const f = (x, y) => ts.reduce((s, [c, i, j]) => s + c * pw(x, i) * pw(y, j), 0);
  const fx = (x, y) => ts.reduce((s, [c, i, j]) => s + (i ? c * i * pw(x, i - 1) * pw(y, j) : 0), 0);
  const fy = (x, y) => ts.reduce((s, [c, i, j]) => s + (j ? c * j * pw(x, i) * pw(y, j - 1) : 0), 0);
  const fxx = (x, y) => ts.reduce((s, [c, i, j]) => s + (i > 1 ? c * i * (i - 1) * pw(x, i - 2) * pw(y, j) : 0), 0);
  const fxy = (x, y) => ts.reduce((s, [c, i, j]) => s + (i && j ? c * i * j * pw(x, i - 1) * pw(y, j - 1) : 0), 0);
  const fyy = (x, y) => ts.reduce((s, [c, i, j]) => s + (j > 1 ? c * j * (j - 1) * pw(x, i) * pw(y, j - 2) : 0), 0);
  return { f, fx, fy, fxx, fxy, fyy };
}

// The two models at θ = (x, y), evaluated at the step (a, b): exactly Taylor.first and Taylor.second.
function models(Lo, x, y, a, b) {
  const L0 = Lo.f(x, y), g = Lo.fx(x, y) * a + Lo.fy(x, y) * b;
  const q = (Lo.fxx(x, y) * a * a + 2 * Lo.fxy(x, y) * a * b + Lo.fyy(x, y) * b * b) / 2;
  return { L0, first: L0 + g, second: L0 + g + q, truth: Lo.f(x + a, y + b), g, q };
}

// ---------- the 3-D surface ----------

const XR = [-2.4, 1.9], YR = [-1.8, 1.8], ZMAX = 4.6;
const SW = 470, SH = 360;

function projector(yaw, el) {
  const cy = Math.cos(yaw), sy = Math.sin(yaw), ce = Math.cos(el), se = Math.sin(el);
  const S = 78, ZS = 0.62, X0 = -0.25;
  return (x, y, z) => {
    const xr = (x - X0) * cy - y * sy, yr = (x - X0) * sy + y * cy;
    return [SW / 2 + S * xr, SH * 0.70 - S * (yr * se + Math.min(z, ZMAX) * ZS * ce)];
  };
}

const path = pts => pts.map((p, i) => (i ? 'L' : 'M') + p[0].toFixed(1) + ',' + p[1].toFixed(1)).join('');

function Surface({ Lo, th, dir, h, showFirst, showSecond, trail, yaw, setYaw }) {
  const P = projector(yaw, 0.62);
  const kids = [];
  const n = 18;
  // floor grid
  for (let i = 0; i <= 8; i++) {
    const x = XR[0] + (XR[1] - XR[0]) * i / 8, y = YR[0] + (YR[1] - YR[0]) * i / 8;
    kids.push(e('path', { key: 'fx' + i, d: path([P(x, YR[0], 0), P(x, YR[1], 0)]), stroke: GRID, strokeWidth: 1 }));
    kids.push(e('path', { key: 'fy' + i, d: path([P(XR[0], y, 0), P(XR[1], y, 0)]), stroke: GRID, strokeWidth: 1 }));
  }
  // wireframe: lines of constant x and constant y, cut where the bowl leaves the box
  const line = (key, pts) => {
    let seg = [], out = [];
    for (const [x, y] of pts) {
      const z = Lo.f(x, y);
      if (z <= ZMAX) seg.push(P(x, y, z)); else { if (seg.length > 1) out.push(seg); seg = []; }
    }
    if (seg.length > 1) out.push(seg);
    out.forEach((s, k) => kids.push(e('path', { key: key + k, d: path(s), stroke: MESH, strokeOpacity: 0.45, strokeWidth: 0.9, fill: 'none' })));
  };
  for (let i = 0; i <= n; i++) {
    const x = XR[0] + (XR[1] - XR[0]) * i / n, y = YR[0] + (YR[1] - YR[0]) * i / n;
    line('cx' + i, Array.from({ length: 61 }, (_, k) => [x, YR[0] + (YR[1] - YR[0]) * k / 60]));
    line('cy' + i, Array.from({ length: 61 }, (_, k) => [XR[0] + (XR[1] - XR[0]) * k / 60, y]));
  }
  // the slice through θ along the step direction
  const sl = [];
  for (let k = 0; k <= 120; k++) {
    const t = -3 + 6 * k / 120, x = th[0] + t * dir[0], y = th[1] + t * dir[1];
    if (x < XR[0] || x > XR[1] || y < YR[0] || y > YR[1]) continue;
    const z = Lo.f(x, y); if (z <= ZMAX) sl.push(P(x, y, z));
  }
  kids.push(e('path', { key: 'slice', d: path(sl), stroke: WHITE, strokeWidth: 2.6, fill: 'none' }));
  // first-order model: a patch of the tangent plane
  const len = Math.hypot(dir[0], dir[1]) || 1, u = [dir[0] / len, dir[1] / len], v = [-u[1], u[0]], r = 0.55;
  if (showFirst) {
    const corner = (s, t) => {
      const a = r * (s * u[0] + t * v[0]), b = r * (s * u[1] + t * v[1]);
      return P(th[0] + a, th[1] + b, models(Lo, th[0], th[1], a, b).first);
    };
    kids.push(e('path', { key: 'plane', d: path([corner(-1, -1), corner(1, -1), corner(1, 1), corner(-1, 1)]) + 'Z',
      fill: TEAL, fillOpacity: 0.16, stroke: TEAL, strokeWidth: 1.2 }));
    const tl = [-1.2, 1.2].map(s => P(th[0] + s * r * u[0], th[1] + s * r * u[1],
      models(Lo, th[0], th[1], s * r * u[0], s * r * u[1]).first));
    kids.push(e('path', { key: 'tline', d: path(tl), stroke: TEAL, strokeWidth: 2 }));
  }
  // second-order model along the slice
  if (showSecond) {
    const q = [];
    for (let k = 0; k <= 40; k++) {
      const t = -1.3 + 2.6 * k / 40, a = t * dir[0], b = t * dir[1];
      const z = models(Lo, th[0], th[1], a, b).second; if (z <= ZMAX) q.push(P(th[0] + a, th[1] + b, z));
    }
    kids.push(e('path', { key: 'quad', d: path(q), stroke: ORANGE, strokeWidth: 2, strokeDasharray: '5 3', fill: 'none' }));
  }
  // gradient-descent trail
  if (trail.length > 1)
    kids.push(e('path', { key: 'trail', d: path(trail.map(([x, y]) => P(x, y, Lo.f(x, y)))), stroke: RED, strokeWidth: 1.6, fill: 'none' }));
  trail.slice(0, -1).forEach(([x, y], i) => { const p = P(x, y, Lo.f(x, y)); kids.push(e('circle', { key: 'tr' + i, cx: p[0], cy: p[1], r: 2.4, fill: RED })); });
  // θ, its shadow, and the step θ + Δ
  const p0 = P(th[0], th[1], Lo.f(th[0], th[1])), s0 = P(th[0], th[1], 0);
  kids.push(e('path', { key: 'drop', d: path([p0, s0]), stroke: DIM, strokeDasharray: '2 3' }));
  const a = h * dir[0], b = h * dir[1], m = models(Lo, th[0], th[1], a, b);
  const pt = P(th[0] + a, th[1] + b, m.truth);
  if (showFirst) {
    const pf = P(th[0] + a, th[1] + b, m.first);
    kids.push(e('path', { key: 'e1', d: path([pt, pf]), stroke: TEAL, strokeWidth: 1.5, strokeDasharray: '3 2' }));
    kids.push(e('circle', { key: 'pf', cx: pf[0], cy: pf[1], r: 3.5, fill: TEAL }));
  }
  if (showSecond) { const ps = P(th[0] + a, th[1] + b, m.second); kids.push(e('circle', { key: 'ps', cx: ps[0], cy: ps[1], r: 3.5, fill: ORANGE })); }
  kids.push(e('circle', { key: 'pt', cx: pt[0], cy: pt[1], r: 4, fill: 'none', stroke: WHITE, strokeWidth: 1.5 }));
  kids.push(e('circle', { key: 'p0', cx: p0[0], cy: p0[1], r: 5, fill: WHITE }));
  // axis labels
  const lx = P(0, YR[0] - 0.35, 0), ly = P(XR[1] + 0.3, 0, 0);
  kids.push(e('text', { key: 'lx', x: lx[0], y: lx[1], fill: DIM, fontSize: 13, fontFamily: SERIF, fontStyle: 'italic' }, 'θ₁'));
  kids.push(e('text', { key: 'ly', x: ly[0], y: ly[1], fill: DIM, fontSize: 13, fontFamily: SERIF, fontStyle: 'italic' }, 'θ₂'));

  const drag = React.useRef(null);
  return e('svg', {
    width: SW, height: SH, viewBox: `0 0 ${SW} ${SH}`, style: { cursor: 'grab', touchAction: 'none', userSelect: 'none', maxWidth: '100%' },
    onPointerDown: ev => { drag.current = { x: ev.clientX, yaw }; ev.currentTarget.setPointerCapture(ev.pointerId); },
    onPointerMove: ev => { if (drag.current) setYaw(drag.current.yaw + (ev.clientX - drag.current.x) / 140); },
    onPointerUp: () => { drag.current = null; },
  }, kids);
}

// ---------- the slice through θ ----------

const PW = 380, PH = 300, PAD = { l: 38, r: 14, t: 16, b: 34 }, TR = [-2.2, 2.2];

function Slice({ Lo, th, dir, h, setH, showFirst, showSecond }) {
  const g = t => Lo.f(th[0] + t * dir[0], th[1] + t * dir[1]);
  const mo = t => models(Lo, th[0], th[1], t * dir[0], t * dir[1]);
  let ymax = 0.5, ymin = 0;
  for (let k = 0; k <= 80; k++) {
    const z = g(TR[0] + (TR[1] - TR[0]) * k / 80);
    ymax = Math.max(ymax, Math.min(z, 6)); ymin = Math.min(ymin, z);
  }
  ymax = Math.ceil(ymax); ymin = Math.floor(ymin);
  const X = t => PAD.l + (t - TR[0]) / (TR[1] - TR[0]) * (PW - PAD.l - PAD.r);
  const Y = z => PH - PAD.b - (z - ymin) / (ymax - ymin) * (PH - PAD.t - PAD.b);
  const inY = z => z >= ymin - 0.2 && z <= ymax + 0.2;
  const curve = (fn, key, props) => {
    const segs = []; let s = [];
    for (let k = 0; k <= 160; k++) {
      const t = TR[0] + (TR[1] - TR[0]) * k / 160, z = fn(t);
      if (inY(z)) s.push([X(t), Y(z)]); else { if (s.length > 1) segs.push(s); s = []; }
    }
    if (s.length > 1) segs.push(s);
    return segs.map((sg, i) => e('path', Object.assign({ key: key + i, d: path(sg), fill: 'none' }, props)));
  };
  const kids = [];
  for (let t = -2; t <= 2; t++) {
    kids.push(e('line', { key: 'gx' + t, x1: X(t), x2: X(t), y1: PAD.t, y2: PH - PAD.b, stroke: GRID }));
    kids.push(e('text', { key: 'tx' + t, x: X(t), y: PH - PAD.b + 16, fill: DIM, fontSize: 11, textAnchor: 'middle', fontFamily: MONO }, String(t)));
  }
  for (let z = ymin; z <= ymax; z++) {
    kids.push(e('line', { key: 'gy' + z, x1: PAD.l, x2: PW - PAD.r, y1: Y(z), y2: Y(z), stroke: GRID }));
    kids.push(e('text', { key: 'ty' + z, x: PAD.l - 8, y: Y(z) + 4, fill: DIM, fontSize: 11, textAnchor: 'end', fontFamily: MONO }, String(z)));
  }
  kids.push(e('text', { key: 'xl', x: PW - PAD.r, y: PH - 4, fill: DIM, fontSize: 13, textAnchor: 'end', fontFamily: SERIF, fontStyle: 'italic' }, 'step h'));
  kids.push(e('text', { key: 'yl', x: 6, y: PAD.t + 4, fill: DIM, fontSize: 13, fontFamily: SERIF, fontStyle: 'italic' }, 'L'));
  kids.push(...curve(g, 'true', { stroke: WHITE, strokeWidth: 2.6 }));
  if (showSecond) kids.push(...curve(t => mo(t).second, 'sec', { stroke: ORANGE, strokeWidth: 1.8, strokeDasharray: '5 3' }));
  if (showFirst) kids.push(...curve(t => mo(t).first, 'fir', { stroke: TEAL, strokeWidth: 1.8 }));
  // the step: where the models land, and how far each is from the truth
  const m = mo(h), xh = X(h);
  kids.push(e('line', { key: 'hl', x1: xh, x2: xh, y1: PAD.t, y2: PH - PAD.b, stroke: DIM, strokeDasharray: '2 3' }));
  if (showFirst && inY(m.first) && inY(m.truth)) {
    kids.push(e('line', { key: 'e1', x1: xh, x2: xh, y1: Y(m.truth), y2: Y(m.first), stroke: TEAL, strokeWidth: 4, strokeOpacity: 0.35 }));
  }
  if (showFirst && inY(m.first)) kids.push(e('circle', { key: 'mf', cx: xh, cy: Y(m.first), r: 4, fill: TEAL }));
  if (showSecond && inY(m.second)) kids.push(e('circle', { key: 'ms', cx: xh, cy: Y(m.second), r: 4, fill: ORANGE }));
  if (inY(m.truth)) kids.push(e('circle', { key: 'mt', cx: xh, cy: Y(m.truth), r: 4.5, fill: 'none', stroke: WHITE, strokeWidth: 1.6 }));
  kids.push(e('circle', { key: 'th', cx: X(0), cy: Y(g(0)), r: 5, fill: WHITE }));
  kids.push(e('text', { key: 'thl', x: X(0) + 8, y: Y(g(0)) + 18, fill: INK, fontSize: 12, fontFamily: SERIF, fontStyle: 'italic' }, 'θ'));
  kids.push(e('text', { key: 'hl2', x: xh + 5, y: PAD.t + 12, fill: INK, fontSize: 12, fontFamily: SERIF, fontStyle: 'italic' }, 'θ + Δ'));

  const setFrom = ev => {
    const box = ev.currentTarget.getBoundingClientRect(), sx = (ev.clientX - box.left) * PW / box.width;
    const t = TR[0] + (sx - PAD.l) / (PW - PAD.l - PAD.r) * (TR[1] - TR[0]);
    setH(Math.round(Math.max(-2, Math.min(2, t)) * 100) / 100);
  };
  const down = React.useRef(false);
  return e('svg', {
    width: PW, height: PH, viewBox: `0 0 ${PW} ${PH}`, style: { cursor: 'ew-resize', touchAction: 'none', userSelect: 'none', maxWidth: '100%' },
    onPointerDown: ev => { down.current = true; ev.currentTarget.setPointerCapture(ev.pointerId); setFrom(ev); },
    onPointerMove: ev => { if (down.current) setFrom(ev); },
    onPointerUp: () => { down.current = false; },
  }, kids);
}

// ---------- controls and readouts ----------

function Slider({ label, value, min, max, step, onChange, color }) {
  return e('label', { style: { display: 'flex', alignItems: 'center', gap: 8, fontSize: 12, color: DIM, fontFamily: SANS } },
    e('span', { style: { width: 72, color: color || INK, fontFamily: SERIF, fontStyle: 'italic', fontSize: 14 } }, label),
    e('input', { type: 'range', min, max, step, value, onChange: ev => onChange(Number(ev.target.value)), style: { flex: 1, accentColor: color || TEAL } }),
    e('span', { style: { width: 50, textAlign: 'right', fontFamily: MONO, color: INK } }, fmt(value, 2)));
}

function Button({ onClick, children, active, color }) {
  const c = color || INK;
  return e('button', {
    onClick, style: {
      background: active ? c + '22' : 'transparent', color: active === false ? DIM : c,
      border: `1px solid ${active === false ? GRID : c}`, borderRadius: 6, padding: '5px 10px',
      fontSize: 12, fontFamily: SANS, cursor: 'pointer',
    }
  }, children);
}

function Readout({ m, showFirst, showSecond }) {
  const row = (label, color, val, err) => e('div', { style: { display: 'flex', gap: 10, fontFamily: MONO, fontSize: 12, color: INK } },
    e('span', { style: { width: 120, color, fontFamily: SANS } }, label),
    e('span', { style: { width: 70, textAlign: 'right' } }, fmt(val)),
    e('span', { style: { width: 120, textAlign: 'right', color: DIM } }, err === null ? '' : 'error ' + fmt(err)));
  return e('div', { style: { display: 'flex', flexDirection: 'column', gap: 3 } },
    row('Actual L(θ + Δ)', WHITE, m.truth, null),
    showFirst ? row('First order', TEAL, m.first, m.truth - m.first) : null,
    showSecond ? row('Second order', ORANGE, m.second, m.truth - m.second) : null);
}

function LeanTable({ table }) {
  const rows = table.map(r => r.map(rat));
  const hname = ([p, q]) => (q === 1 ? String(p) : `${p}/${q}`);
  const th = s => e('th', { style: { padding: '3px 8px', fontWeight: 500, color: DIM, textAlign: 'right' } }, s);
  const td = (s, color, title) => e('td', { title, style: { padding: '3px 8px', textAlign: 'right', color: color || INK } }, s);
  return e('div', null,
    e('div', { style: { fontSize: 12, color: DIM, fontFamily: SANS, marginBottom: 4, maxWidth: 460 } },
      'Computed by Lean on exact rationals at the starting point (Taylor.row). Each halving of the step cuts the first-order error about 4× and the second-order error about 8×. Hover an error for its exact value.'),
    e('table', { style: { borderCollapse: 'collapse', fontFamily: MONO, fontSize: 12 } },
      e('thead', null, e('tr', null, th('h'), th('actual'), th('1st-order error'), th('÷'), th('2nd-order error'), th('÷'))),
      e('tbody', null, rows.map((r, i) => e('tr', { key: i, style: { borderTop: `1px solid ${GRID}` } },
        td(hname(table[i][0])),
        td(fmt(r[1])),
        td(fmt(r[4], 6), TEAL, hname(table[i][4])),
        td(i ? (rows[i - 1][4] / r[4]).toFixed(2) : '', DIM),
        td(r[5].toExponential(2), ORANGE, hname(table[i][5])),
        td(i ? (rows[i - 1][5] / r[5]).toFixed(2) : '', DIM))))));
}

export default function TaylorWidget(props) {
  const Lo = React.useMemo(() => makeLoss(props.terms), [props.terms]);
  const th0 = props.theta.map(rat), d0 = props.dir.map(rat), dlen = Math.hypot(d0[0], d0[1]);
  const [th, setTh] = React.useState(th0);
  const [ang, setAng] = React.useState(Math.atan2(d0[1], d0[0]));
  const [h, setH] = React.useState(0.5);
  const [showFirst, setShowFirst] = React.useState(true);
  const [showSecond, setShowSecond] = React.useState(true);
  const [trail, setTrail] = React.useState([]);
  const [yaw, setYaw] = React.useState(-0.35);
  const dir = [dlen * Math.cos(ang), dlen * Math.sin(ang)];
  const m = models(Lo, th[0], th[1], h * dir[0], h * dir[1]);
  const grad = [Lo.fx(th[0], th[1]), Lo.fy(th[0], th[1])];

  const step = () => {
    const eta = 0.3, nx = th[0] - eta * grad[0], ny = th[1] - eta * grad[1];
    setTrail((trail.length ? trail : [th]).concat([[nx, ny]]));
    setTh([nx, ny]);
  };
  const reset = () => { setTh(th0); setAng(Math.atan2(d0[1], d0[0])); setH(0.5); setTrail([]); setYaw(-0.35); };

  const term = (s, color, on) => e('span', { style: { color: on ? color : '#3a4152', transition: 'color .2s' } }, s);
  const legend = (color, label, dash) => e('span', { key: label, style: { display: 'inline-flex', alignItems: 'center', gap: 6, fontSize: 12, color: INK, fontFamily: SANS } },
    e('svg', { width: 24, height: 6 }, e('line', { x1: 0, x2: 24, y1: 3, y2: 3, stroke: color, strokeWidth: 2.5, strokeDasharray: dash })), label);

  return e('div', { style: { background: BG, color: INK, borderRadius: 12, padding: 18, border: '1px solid #232838', fontFamily: SANS } },
    e('div', { style: { fontSize: 20, fontWeight: 700, letterSpacing: 1, borderBottom: `1px solid ${GRID}`, paddingBottom: 8 } }, 'TAYLOR EXPANSION'),
    e('div', { style: { textAlign: 'center', fontFamily: SERIF, fontSize: 22, margin: '14px 0 6px', fontStyle: 'italic' } },
      'L(θ + Δ) ≈ L(θ) ', term('+ ∇L(θ)ᵀΔ ', TEAL, showFirst), term('+ ½ ΔᵀH(θ)Δ', ORANGE, showSecond)),
    e('div', { style: { textAlign: 'center', fontSize: 12, color: DIM, marginBottom: 10, fontFamily: MONO } },
      `θ = (${fmt(th[0], 3)}, ${fmt(th[1], 3)})    ∇L(θ) = (${fmt(grad[0], 3)}, ${fmt(grad[1], 3)})    Δ = h·(${fmt(dir[0], 2)}, ${fmt(dir[1], 2)})`),
    e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: 16, alignItems: 'flex-start', justifyContent: 'center' } },
      e('div', { style: { background: PANEL, borderRadius: 8, padding: 8 } },
        e('div', { style: { fontSize: 11, color: DIM, letterSpacing: 1 } }, 'LOSS SURFACE  ·  DRAG TO ROTATE'),
        e(Surface, { Lo, th, dir, h, showFirst, showSecond, trail, yaw, setYaw })),
      e('div', { style: { background: PANEL, borderRadius: 8, padding: 8 } },
        e('div', { style: { fontSize: 11, color: DIM, letterSpacing: 1 } }, 'SLICE THROUGH θ ALONG Δ  ·  DRAG TO MOVE THE STEP'),
        e(Slice, { Lo, th, dir, h, setH, showFirst, showSecond }))),
    e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: 22, justifyContent: 'center', margin: '10px 0 14px' } },
      [legend(WHITE, 'Actual loss'), legend(TEAL, 'First order (tangent)'), legend(ORANGE, 'Second order (local)', '5 3'),
       trail.length ? legend(RED, 'Gradient steps') : null]),
    e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: 28, alignItems: 'flex-start' } },
      e('div', { style: { flex: '1 1 300px', display: 'flex', flexDirection: 'column', gap: 6 } },
        e(Slider, { label: 'θ₁', value: th[0], min: -2, max: 1.6, step: 0.01, onChange: v => { setTh([v, th[1]]); setTrail([]); } }),
        e(Slider, { label: 'θ₂', value: th[1], min: -1.5, max: 1.5, step: 0.01, onChange: v => { setTh([th[0], v]); setTrail([]); } }),
        e(Slider, { label: 'direction', value: ang, min: -Math.PI, max: Math.PI, step: 0.01, onChange: setAng }),
        e(Slider, { label: 'step h', value: h, min: -2, max: 2, step: 0.01, onChange: setH, color: WHITE }),
        e('div', { style: { display: 'flex', flexWrap: 'wrap', gap: 8, marginTop: 6 } },
          e(Button, { onClick: () => setShowFirst(!showFirst), active: showFirst, color: TEAL }, 'First order'),
          e(Button, { onClick: () => setShowSecond(!showSecond), active: showSecond, color: ORANGE }, 'Second order'),
          e(Button, { onClick: () => setAng(Math.atan2(-grad[1], -grad[0])) }, 'Point Δ downhill'),
          e(Button, { onClick: step, color: RED }, 'Gradient step (η = 0.3)'),
          e(Button, { onClick: reset, color: DIM }, 'Reset'))),
      e('div', { style: { flex: '1 1 320px', display: 'flex', flexDirection: 'column', gap: 12 } },
        e(Readout, { m, showFirst, showSecond }),
        e(LeanTable, { table: props.table }))));
}
