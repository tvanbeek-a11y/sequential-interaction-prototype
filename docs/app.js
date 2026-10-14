/*
  Thaw — one continuous sequence built from four interaction studies:
    1. Strike a match   (drag fast across the striker)
    2. Light the torch  (carry the flame to the torch head and hold still)
    3. Torch throw      (hold, aim, slide up, let go)
    4. Ice vs. fire     (pull back and let go to push the ice into the fire)
  The same match, torch and wood pile persist from stage to stage. Each stage
  unlocks only after the one before it succeeds; camera moves join them.
*/
(() => {
'use strict';

/* ================================================================ helpers */
const $ = id => document.getElementById(id);
const TAU = Math.PI * 2;
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const lerp = (a, b, t) => a + (b - a) * t;
const R = Math.random;
const rnd = (a = 1, b) => b === undefined ? R() * a : a + R() * (b - a);
const rad = d => d * Math.PI / 180;
const wrap = a => { a = (a + Math.PI) % TAU; if (a < 0) a += TAU; return a - Math.PI; };
const gray = v => { v = Math.round(clamp(v, 0, 255)); return `rgb(${v},${v},${v})`; };
const ease = t => t < .5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
const smooth = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
function rr(g, x, y, w, h, r) {
  r = Math.min(r, w / 2, h / 2);
  g.beginPath(); g.moveTo(x + r, y);
  g.arcTo(x + w, y, x + w, y + h, r); g.arcTo(x + w, y + h, x, y + h, r);
  g.arcTo(x, y + h, x, y, r); g.arcTo(x, y, x + w, y, r); g.closePath();
}
function radial(stops) {
  const c = document.createElement('canvas'); c.width = c.height = 64;
  const g = c.getContext('2d'), gr = g.createRadialGradient(32, 32, 0, 32, 32, 32);
  stops.forEach(([o, col]) => gr.addColorStop(o, col));
  g.fillStyle = gr; g.fillRect(0, 0, 64, 64);
  return c;
}
const greySprite = (v, mid) => radial([[0, `rgba(${v},${v},${v},1)`], [mid, `rgba(${v},${v},${v},.45)`], [1, `rgba(${v},${v},${v},0)`]]);
const buzz = p => { try { navigator.vibrate && navigator.vibrate(p); } catch (_) {} };
const reduce = matchMedia('(prefers-reduced-motion: reduce)').matches;
const tailDir = a => ({ x: Math.sin(a), y: -Math.cos(a) });   // from match head toward the stick's tail

const SPR = {
  hot:    radial([[0, 'rgba(255,255,255,1)'], [.3, 'rgba(240,240,240,.55)'], [1, 'rgba(210,210,210,0)']]),
  soft:   radial([[0, 'rgba(200,200,200,.8)'], [.5, 'rgba(160,160,160,.28)'], [1, 'rgba(130,130,130,0)']]),
  smoke2: radial([[0, 'rgba(130,130,130,.55)'], [.6, 'rgba(100,100,100,.22)'], [1, 'rgba(90,90,90,0)']]),
  light3: radial([[0, 'rgba(255,255,255,1)'], [.3, 'rgba(255,255,255,.55)'], [.65, 'rgba(255,255,255,.14)'], [1, 'rgba(255,255,255,0)']]),
  smoke3: radial([[0, 'rgba(150,150,150,1)'], [.3, 'rgba(150,150,150,.55)'], [.65, 'rgba(150,150,150,.14)'], [1, 'rgba(150,150,150,0)']]),
  white4: greySprite(255, .4), smoke4: greySprite(80, .4), shadow4: greySprite(0, .4)
};

/* ================================================================ canvas, layers, state */
const cv = $('c'), ctx = cv.getContext('2d');
const hintEl = $('hint'), sndBtn = $('snd'), endEl = $('end'), againBtn = $('again');
const layerA = document.createElement('canvas'), gA = layerA.getContext('2d');
const layerB = document.createElement('canvas'), gB = layerB.getContext('2d');
let W = 0, H = 0, DPR = 1, time = 0;
let stage = 0;          // 0 match, 1 torch, 2 throw, 3 ice
let trans = null;       // { kind: 't1' | 't2' | 't3' | 'reset', t, dur, ... }
const ptr = { down: false, id: null, x: 0, y: 0, lx: 0, ly: 0, vx: 0, vy: 0 };

const LABELS = [
  'A matchbox striker strip with a match resting on it. Drag the match fast across the strip to light it, or press Enter to strike it.',
  'A lit match in the dark and an unlit torch on a stone wall. Drag the match to the torch and hold it still to light it.',
  'A lit torch in your hand, a pile of wood, and a block of ice with a bird frozen inside. Hold the torch, drag to aim, slide up to throw.',
  'Seen from above: the burning pile and the block of ice with the bird inside. Drag back to aim, let go to push the ice into the fire.'
];

let hintText = null, hintSr = false;
function setHint(t, sr) {
  sr = !!sr;
  if (t === hintText && sr === hintSr) return;
  hintText = t; hintSr = sr;
  if (t || sr) hintEl.textContent = t;
  hintEl.classList.toggle('sr', sr);
  hintEl.classList.toggle('on', !!t && !sr);
}

/* ================================================================ audio (all synthesised) */
const A = { c: null, master: null, noise: null, on: true };
let scr1 = null, scr2 = null, matchHiss = null, heatGain = null, fireBed = null, roarGain = null, torchGain = null;
const sm = { lvl: 0 };

function makeScrapeBuffer() {
  const sr = A.c.sampleRate, n = (sr * 2) | 0, b = A.c.createBuffer(1, n, sr), d = b.getChannelData(0);
  let lp = 0, e1 = 0, e2 = 0;
  for (let i = 0; i < n; i++) {
    const w = R() * 2 - 1;
    lp += (w - lp) * .55;
    if (R() < .006) e1 = .35 + R() * .65;      // fine grit
    if (R() < .0011) e2 = .6 + R() * .8;       // chunky catches
    e1 *= .982; e2 *= .993;
    d[i] = lp * (.10 + e1 * .9 + e2 * 1.1);
  }
  let max = 0; for (let i = 0; i < n; i++) max = Math.max(max, Math.abs(d[i]));
  const fade = 240;
  for (let i = 0; i < n; i++) {
    d[i] /= max * 1.05;
    if (i < fade) d[i] *= i / fade; else if (i > n - fade) d[i] *= (n - i) / fade;
  }
  return b;
}

function initAudio() {
  if (!A.c) {
    const Ctor = window.AudioContext || window.webkitAudioContext;
    if (!Ctor) return;
    try { A.c = new Ctor(); } catch (_) { A.c = null; return; }
    const c = A.c, comp = c.createDynamicsCompressor();
    A.master = c.createGain(); A.master.gain.value = A.on ? .85 : 0;
    A.master.connect(comp); comp.connect(c.destination);
    const nb = c.createBuffer(1, c.sampleRate * 2 | 0, c.sampleRate), nd = nb.getChannelData(0);
    for (let i = 0; i < nd.length; i++) nd[i] = R() * 2 - 1;
    A.noise = nb;

    const filt = (type, f, q) => { const b = c.createBiquadFilter(); b.type = type; b.frequency.value = f; if (q) b.Q.value = q; return b; };
    const loopSrc = buf => { const s = c.createBufferSource(); s.buffer = buf; s.loop = true; s.start(0, R() * 1.5); return s; };
    const lfo = (freq, depth, param) => { const o = c.createOscillator(); o.frequency.value = freq; const g = c.createGain(); g.gain.value = depth; o.connect(g); g.connect(param); o.start(); };
    const gain0 = () => { const g = c.createGain(); g.gain.value = 0; return g; };

    // 1 — scraping on the striker, and the match's own hiss once lit
    const sb = makeScrapeBuffer();
    const mkScr = (type, f, q) => { const s = loopSrc(sb), fl = filt(type, f, q), g = gain0(); s.connect(fl); fl.connect(g); g.connect(A.master); return { s, f: fl, g }; };
    scr1 = mkScr('bandpass', 1800, .7);
    scr2 = mkScr('lowpass', 520, .9);
    matchHiss = gain0();
    { const s = loopSrc(nb), lp = filt('lowpass', 900), hp = filt('highpass', 140); s.connect(lp); lp.connect(hp); hp.connect(matchHiss); matchHiss.connect(A.master); }

    // 2 — heating hiss at the torch head and the torch's fire bed
    heatGain = gain0();
    { const s = loopSrc(nb), bp = filt('bandpass', 4500, .8); s.connect(bp); bp.connect(heatGain); heatGain.connect(A.master); }
    fireBed = gain0(); fireBed.connect(A.master);
    { const s = loopSrc(nb), lp = filt('lowpass', 480, .7), g = c.createGain(); g.gain.value = 3.5;
      s.connect(lp); lp.connect(g); g.connect(fireBed); lfo(.8, 180, lp.frequency); lfo(1.7, .9, g.gain); }
    { const s = loopSrc(nb), bp = filt('bandpass', 1000, .4), g = c.createGain(); g.gain.value = .5;
      s.connect(bp); bp.connect(g); g.connect(fireBed); lfo(3.1, .18, g.gain); lfo(.5, 250, bp.frequency); }
    { const s = loopSrc(nb), hp = filt('highpass', 3200), g = c.createGain(); g.gain.value = .12;
      s.connect(hp); hp.connect(g); g.connect(fireBed); }

    // 3/4 — the bonfire roar and the small torch hiss
    const loop3 = (cut, hpf) => { const s = loopSrc(nb), lo = filt('lowpass', cut), hi = filt('highpass', hpf), g = gain0(); s.connect(lo); lo.connect(hi); hi.connect(g); g.connect(A.master); return g; };
    roarGain = loop3(750, 70);
    torchGain = loop3(1500, 160);

    const z = c.createBufferSource(); z.buffer = c.createBuffer(1, 1, 22050); z.connect(c.destination); z.start(0); // iOS unlock
  }
  if (A.c.state !== 'running') A.c.resume().catch(() => {});
}
['pointerup', 'touchend', 'click', 'keydown'].forEach(ev =>
  document.addEventListener(ev, () => { if (A.c && A.c.state !== 'running') A.c.resume().catch(() => {}); }, { passive: true }));
document.addEventListener('visibilitychange', () => {
  if (!A.c) return;
  if (document.hidden) A.c.suspend().catch(() => {}); else A.c.resume().catch(() => {});
});
const live = () => A.c && A.on && A.c.state === 'running';

function burst(o) {
  if (!live()) return;
  const c = A.c, t = c.currentTime + (o.delay || 0);
  const s = c.createBufferSource(); s.buffer = A.noise;
  const f = c.createBiquadFilter(); f.type = o.type || 'bandpass'; f.Q.value = o.q || 1;
  f.frequency.setValueAtTime(o.f, t);
  if (o.f2) f.frequency.exponentialRampToValueAtTime(o.f2, t + o.dur * (o.sweep || 1));
  const g = c.createGain();
  g.gain.setValueAtTime(.0001, t);
  g.gain.exponentialRampToValueAtTime(o.gain, t + (o.att || .004));
  g.gain.exponentialRampToValueAtTime(.0001, t + o.dur);
  s.connect(f); f.connect(g); g.connect(A.master);
  s.start(t, R() * Math.max(0, 2 - o.dur - .05)); s.stop(t + o.dur + .05);
}
function thump(f0, f1, rampT, gain, dur) {
  if (!live()) return;
  const c = A.c, t = c.currentTime, o = c.createOscillator(), g = c.createGain();
  o.type = 'sine'; o.frequency.setValueAtTime(f0, t); o.frequency.exponentialRampToValueAtTime(f1, t + rampT);
  g.gain.setValueAtTime(.0001, t); g.gain.exponentialRampToValueAtTime(gain, t + .01); g.gain.exponentialRampToValueAtTime(.0001, t + dur);
  o.connect(g); g.connect(A.master); o.start(t); o.stop(t + dur + .05);
}
const setGain = (node, v, tc) => { if (A.c && node) node.gain.setTargetAtTime(v, A.c.currentTime, tc); };

sndBtn.addEventListener('click', () => {
  A.on = !A.on;
  sndBtn.setAttribute('aria-pressed', String(A.on));
  sndBtn.setAttribute('aria-label', A.on ? 'Turn sound off' : 'Turn sound on');
  if (A.on) initAudio();
  if (A.master) A.master.gain.setTargetAtTime(A.on ? .85 : 0, A.c.currentTime, .03);
});

/* ================================================================ 1 · STRIKE A MATCH  (+ the match, which persists) */
let u = 1, Ls = 215;
let strip = { x: 0, y: 0, w: 0, h: 0 };
const A_HELD = 2.3;                       // stick angle once lit: tail down-right, flame free above
const hv = { x: 0, y: 0 };                // smoothed head velocity (px/s)
const L = { x: 0, y: 0, R: 10, I: 0 };    // stage-1 light source
const sparks = [], smoke = [];
let m = null, auto = null, flash = 0, wasContact = false, crackleAcc = 0, s1LitT = 0, matchFade = 1;
const base = document.createElement('canvas'), litC = document.createElement('canvas'), tmpC = document.createElement('canvas');
const bctx = base.getContext('2d'), lctx = litC.getContext('2d'), tctx = tmpC.getContext('2d');

function blankMatch() {
  return { state: 'ready', hx: 0, hy: 0, a: .25, g: 80 * u, heat: 0, need: .8 + R() * .25,
           c: 0, burnT: 0, flame: 0, alpha: 0, grabAge: 0, slowT: 0, slowHold: 0, rough: 0, seed: (R() * 1e6) | 0 };
}
function restPose() { m.hx = strip.x + 30 * u; m.hy = strip.y + strip.h * .5; m.a = .25; m.g = 80 * u; }
function frontier() { const d = tailDir(m.a); return { x: m.hx + d.x * m.c * Ls, y: m.hy + d.y * m.c * Ls }; }
function flamePoint() { const f = frontier(); return { x: f.x, y: f.y - 74 * u * m.flame * .35 }; }

const PAL_DARK = { bg0: '#1d1d1d', bg1: '#0a0a0a', box0: '#2a2a2a', box1: '#181818', edge: '#4a4a4a', line: '#5a5a5a', strip: '#333333', grit: ['#4d4d4d', '#222222', '#666666'] };
const PAL_LIT  = { bg0: '#555555', bg1: '#1c1c1c', box0: '#8f8f8f', box1: '#585858', edge: '#c4c4c4', line: '#d8d8d8', strip: '#707070', grit: ['#a8a8a8', '#3c3c3c', '#dcdcdc'] };

function s1DrawScene(c, pal) {
  c.setTransform(DPR, 0, 0, DPR, 0, 0);
  const rng = mulberry32(7);
  const bg = c.createRadialGradient(W / 2, H * .5, 20 * u, W / 2, H * .5, Math.hypot(W, H) * .6);
  bg.addColorStop(0, pal.bg0); bg.addColorStop(1, pal.bg1);
  c.fillStyle = bg; c.fillRect(0, 0, W, H);
  const n = (W * H) / 140 | 0;
  for (let i = 0; i < n; i++) {
    const x = rng() * W, y = rng() * H;
    c.fillStyle = rng() < .5 ? 'rgba(255,255,255,0.045)' : 'rgba(0,0,0,0.16)';
    c.fillRect(x, y, 1.2, 1.2);
  }
  // matchbox face, bleeding off the bottom
  const bx = Math.max(10 * u, W * .035), bw = W - 2 * bx, by = strip.y - 34 * u, bh = H - by + 60 * u;
  const bgr = c.createLinearGradient(0, by, 0, by + bh * .6);
  bgr.addColorStop(0, pal.box0); bgr.addColorStop(1, pal.box1);
  c.fillStyle = bgr; rr(c, bx, by, bw, bh, 24 * u); c.fill();
  c.lineWidth = 1.5 * u; c.strokeStyle = pal.edge; c.stroke();
  c.save(); c.globalAlpha = .35; c.lineWidth = 1 * u; c.strokeStyle = pal.line;
  rr(c, bx + 10 * u, by + 10 * u, bw - 20 * u, bh, 18 * u); c.stroke(); c.restore();
  const n2 = (bw * Math.min(bh, H - by)) / 220 | 0;
  for (let i = 0; i < n2; i++) {
    const x = bx + rng() * bw, y = by + rng() * Math.min(bh, H - by);
    c.fillStyle = rng() < .5 ? 'rgba(255,255,255,0.05)' : 'rgba(0,0,0,0.14)';
    c.fillRect(x, y, 1.4, 1.4);
  }
  // striker strip
  c.fillStyle = 'rgba(0,0,0,0.38)'; rr(c, strip.x - 5 * u, strip.y - 4 * u, strip.w + 10 * u, strip.h + 8 * u, 10 * u); c.fill();
  c.fillStyle = pal.strip; rr(c, strip.x, strip.y, strip.w, strip.h, 7 * u); c.fill();
  c.save(); rr(c, strip.x, strip.y, strip.w, strip.h, 7 * u); c.clip();
  const gn = (strip.w * strip.h) / (7 * u * u) | 0;
  for (let i = 0; i < gn; i++) {
    const x = strip.x + rng() * strip.w, y = strip.y + rng() * strip.h, s = (.7 + rng() * 1.8) * u;
    c.globalAlpha = .5 + rng() * .4; c.fillStyle = pal.grit[(rng() * 3) | 0]; c.fillRect(x, y, s, s);
  }
  c.globalAlpha = 1;
  const sh = c.createLinearGradient(0, strip.y, 0, strip.y + strip.h);
  sh.addColorStop(0, 'rgba(255,255,255,0.10)'); sh.addColorStop(.5, 'rgba(255,255,255,0)'); sh.addColorStop(1, 'rgba(0,0,0,0.18)');
  c.fillStyle = sh; c.fillRect(strip.x, strip.y, strip.w, strip.h);
  c.restore();
  c.lineWidth = 1 * u; c.strokeStyle = pal.line; c.globalAlpha = .5;
  rr(c, strip.x, strip.y, strip.w, strip.h, 7 * u); c.stroke(); c.globalAlpha = 1;
}

function s1Layout() {
  u = clamp(Math.min(W / 390, H / 760), .55, 1.5);
  for (const c of [base, litC, tmpC]) { c.width = Math.round(W * DPR); c.height = Math.round(H * DPR); }
  Ls = 215 * u;
  const sw = Math.min(W * .9, 520 * u), sh = 92 * u;
  strip = { x: (W - sw) / 2, y: Math.min(H * .68 - sh / 2, H - sh - 64 * u), w: sw, h: sh };
  s1DrawScene(bctx, PAL_DARK); s1DrawScene(lctx, PAL_LIT);
  if (m && stage === 0 && !trans) {
    if (m.state === 'ready' && !ptr.down) restPose();
    m.hx = clamp(m.hx, 0, W); m.hy = clamp(m.hy, 0, H);
    m.g = clamp(m.g, 26 * u, Ls * .95);
  }
}

// audio for stage 1
function sndTick(v) { burst({ dur: .03, f: 1700, q: .8, gain: .12 + .25 * v, att: .002 }); }
function sndIgnite() {
  burst({ dur: .55, f: 4800, f2: 1500, q: .7, gain: .8, att: .006 });
  burst({ dur: .2, type: 'lowpass', f: 1200, f2: 180, q: .5, gain: .7, att: .004 });
  for (let i = 0; i < 9; i++) burst({ delay: .03 + R() * .4, dur: .012, f: 2200 + R() * 3800, q: 2.5, gain: .12 + R() * .2, att: .001 });
  thump(140, 42, .2, .45, .24);
}
function updateScrape(dt, level) {
  if (!A.c || !scr1 || A.c.state !== 'running') return;
  sm.lvl += (level - sm.lvl) * (1 - Math.exp(-dt / .04));
  const l = sm.lvl, flutter = .75 + R() * .5;
  scr1.g.gain.value = Math.pow(l, .8) * .85 * flutter;
  scr1.s.playbackRate.value = .6 + l * 1.0;
  scr1.f.frequency.value = 800 + l * 3400;
  scr2.g.gain.value = Math.pow(l, .9) * .5 * (.7 + R() * .6);
  scr2.s.playbackRate.value = (.6 + l * .9) * .6;
}

function spark(x, y, vx, vy, life, size) { sparks.push({ x, y, vx, vy, life, max: life, size }); if (sparks.length > 160) sparks.shift(); }
function puff(x, y, a) {
  const life = 2.2 + R() * 1.4;
  smoke.push({ x, y, vx: (R() - .5) * 14 * u, vy: -(34 + R() * 34) * u, r: (3 + R() * 3) * u, life, max: life, a: a || 1 });
  if (smoke.length > 90) smoke.shift();
}

function ignite() {
  m.state = 'lit'; m.burnT = 0; m.c = 0; m.flame = 2; m.heat = 0; flash = 1; s1LitT = 0;
  const n = reduce ? 8 : 20;
  for (let i = 0; i < n; i++) {
    const ang = -Math.PI / 2 + (R() - .5) * 2.6, sp = (180 + R() * 420) * u;
    spark(m.hx, m.hy, Math.cos(ang) * sp + hv.x * .3, Math.sin(ang) * sp, .3 + R() * .45, 1 + R() * 1.4);
  }
  sndIgnite();
  buzz(16);
}

function trackHead(dt, ox, oy) {
  const kv = 1 - Math.exp(-dt / .035);
  hv.x += ((m.hx - ox) / dt - hv.x) * kv; hv.y += ((m.hy - oy) / dt - hv.y) * kv;
}

// The lit match: the flame eats a little way down the stick, then holds there and never goes out
// (match failures are removed). It settles before stage 2 so the flame stays put while you hold it still.
function updateMatchFlame(dt, t) {
  if (m.state !== 'lit') return;
  m.burnT += dt; m.c = Math.min(.16, m.burnT / 16 * .9);
  const flare = 1 + 1.2 * Math.exp(-m.burnT * 6);
  const fk = reduce ? .3 : 1;
  const flick = 1 + fk * (.08 * Math.sin(t * 21) + .06 * Math.sin(t * 34.7 + 2) + .04 * Math.sin(t * 53 + 4));
  m.flame = flare * (1 - Math.min(.4, Math.hypot(hv.x, hv.y) / 5200)) * flick;
  if (matchHiss && A.c) matchHiss.gain.value += (.07 * clamp(m.flame, 0, 1.6) * (.85 + R() * .3) * matchFade - matchHiss.gain.value) * .3;
  crackleAcc += dt * 5;
  if (crackleAcc > 1 && R() < .5) { crackleAcc = 0; if (matchFade > .3) burst({ dur: .012, f: 2400 + R() * 3000, q: 2.5, gain: .05 + R() * .1, att: .001 }); }
  if (R() < dt * 3) { const f = frontier(); puff(f.x, f.y - 70 * u * m.flame, .35); }
}
function updateMatchParticles(dt) {
  for (let i = sparks.length - 1; i >= 0; i--) {
    const p = sparks[i]; p.life -= dt;
    if (p.life <= 0) { sparks.splice(i, 1); continue; }
    p.vy += 900 * u * dt; p.vx *= Math.exp(-dt * 2); p.x += p.vx * dt; p.y += p.vy * dt;
  }
  for (let i = smoke.length - 1; i >= 0; i--) {
    const p = smoke[i]; p.life -= dt;
    if (p.life <= 0) { smoke.splice(i, 1); continue; }
    p.vx += (R() - .5) * 60 * u * dt; p.vx *= Math.exp(-dt * .5);
    p.x += p.vx * dt; p.y += p.vy * dt; p.r += 8 * u * dt;
  }
}

// light source for the matchbox scene; (ox, oy) shifts screen coordinates into the scene's own
function s1UpdateLight(dt, ox, oy) {
  let tI = 0, tR = 60 * u, tx = m.hx - ox, ty = m.hy - oy;
  if (m.state === 'lit') {
    const f = flamePoint(); tx = f.x - ox; ty = f.y - oy;
    tI = clamp(.55 + .45 * m.flame, 0, 1); tR = 300 * u * (.55 + .45 * Math.min(1.6, m.flame));
  } else if (m.heat > .02) {
    const h = clamp(m.heat / m.need, 0, 1); tI = .15 + .5 * h * h; tR = (40 + 110 * h) * u;
  }
  const kL = 1 - Math.exp(-dt / .05);
  L.x += (tx - L.x) * kL; L.y += (ty - L.y) * kL; L.I += (tI - L.I) * kL; L.R += (tR - L.R) * kL;
}

function s1Update(dt, t) {
  // scripted keyboard strike
  if (auto) {
    auto.t += dt;
    const k = clamp(auto.t / auto.dur, 0, 1), p = k < .5 ? k * 2 : 2 - 2 * k;
    ptr.x = auto.sx + (auto.ex - auto.sx) * p; ptr.y = auto.sy;
    if (auto.t >= auto.dur + .06) { auto = null; ptr.down = false; }
  }
  // grip velocity (drives the lean, so no feedback loop with the head)
  if (ptr.down) {
    const k = 1 - Math.exp(-dt / .06);
    ptr.vx += ((ptr.x - ptr.lx) / dt - ptr.vx) * k; ptr.vy += ((ptr.y - ptr.ly) / dt - ptr.vy) * k;
  } else { ptr.vx *= Math.exp(-dt * 8); ptr.vy *= Math.exp(-dt * 8); }
  ptr.lx = ptr.x; ptr.ly = ptr.y;

  m.alpha = Math.min(1, m.alpha + dt * 4);
  const ready = m.state === 'ready';
  const targetA = ready ? .25 - .6 * Math.tanh(ptr.vx / (800 * u)) : A_HELD + .2 * Math.tanh(ptr.vx / (900 * u));
  m.a += (targetA - m.a) * (1 - Math.exp(-dt * (ready ? 12 : 5)));

  // head follows the grip point
  const ox = m.hx, oy = m.hy;
  if (ptr.down) {
    const d = tailDir(m.a), k = 1 - Math.exp(-dt / .028);
    m.hx += (ptr.x - d.x * m.g - m.hx) * k; m.hy += (ptr.y - d.y * m.g - m.hy) * k;
    m.grabAge += dt;
  }
  m.hx = clamp(m.hx, -10, W + 10); m.hy = clamp(m.hy, -10, H + 10);
  trackHead(dt, ox, oy);
  const vN = Math.hypot(hv.x, hv.y) / u;

  const inStrip = m.hx > strip.x - 6 * u && m.hx < strip.x + strip.w + 6 * u && m.hy > strip.y - 2 * u && m.hy < strip.y + strip.h + 2 * u;
  const contact = ptr.down && inStrip && m.grabAge > .18 && m.alpha > .5;

  // friction: sound, sparks, scuffs, heat
  updateScrape(dt, contact ? clamp(vN / 1400, 0, 1) : 0);
  m.rough += ((contact ? clamp(vN / 900, 0, 1) : 0) - m.rough) * (1 - Math.exp(-dt / .05));
  if (contact && !wasContact && vN > 120) sndTick(clamp(vN / 1200, 0, 1));
  wasContact = contact;
  if (contact && vN > 200) {
    for (const c of [bctx, lctx]) {
      c.setTransform(DPR, 0, 0, DPR, 0, 0);
      c.strokeStyle = 'rgba(0,0,0,0.22)'; c.lineWidth = (.8 + R() * 1.4) * u; c.lineCap = 'round';
      c.beginPath(); c.moveTo(ox, oy + (R() - .5) * 5 * u); c.lineTo(m.hx, m.hy + (R() - .5) * 5 * u); c.stroke();
    }
  }
  if (contact && vN > 450 && ready) {
    const n = (vN / 1500) * dt * 60 * .6;
    for (let i = 0, k = Math.floor(n) + (R() < n % 1 ? 1 : 0); i < k; i++)
      spark(m.hx, m.hy, hv.x * .35 + (R() - .5) * 160 * u, -R() * 200 * u - 40 * u, .2 + R() * .3, .8 + R() * .8);
  }

  if (ready) {
    if (contact && vN > 250) m.heat += (vN - 250) / 200 * dt;
    else if (contact) m.heat -= .6 * dt;
    else m.heat -= 1.4 * dt;
    m.heat = clamp(m.heat, 0, 1.2);
    if (contact && vN > 40 && vN <= 250) { m.slowT += dt; if (m.slowT > .5) { m.slowHold = 1.6; m.slowT = 0; } }
    else m.slowT = 0;
    if (m.heat >= m.need) ignite();
  }

  if (m.state === 'lit') {
    updateMatchFlame(dt, t);
    s1LitT += dt;
    if (s1LitT > 1.5) startTrans('t1');
  }

  if (m.state === 'ready') {
    if (m.slowHold > 0) { m.slowHold -= dt; setHint('Too slow. Drag faster.'); }
    else if (contact) setHint('');
    else setHint('Drag the match fast across the strip');
  } else setHint('');

  s1UpdateLight(dt, 0, 0);
  flash = Math.max(0, flash - dt * 4.5);
  updateMatchParticles(dt);
}

function s1DrawLight(g, x, y, Rr, I) {
  const x0 = Math.max(0, Math.floor(x - Rr)), y0 = Math.max(0, Math.floor(y - Rr));
  const x1 = Math.min(W, Math.ceil(x + Rr)), y1 = Math.min(H, Math.ceil(y + Rr));
  const w = x1 - x0, h = y1 - y0;
  if (w < 2 || h < 2) return;
  tctx.globalCompositeOperation = 'source-over';
  tctx.setTransform(1, 0, 0, 1, 0, 0);
  tctx.clearRect(0, 0, Math.ceil(w * DPR) + 2, Math.ceil(h * DPR) + 2);
  tctx.drawImage(litC, x0 * DPR, y0 * DPR, w * DPR, h * DPR, 0, 0, w * DPR, h * DPR);
  tctx.globalCompositeOperation = 'destination-in';
  tctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  const gr = tctx.createRadialGradient(x - x0, y - y0, 0, x - x0, y - y0, Rr);
  gr.addColorStop(0, `rgba(0,0,0,${I})`);
  gr.addColorStop(.2, `rgba(0,0,0,${I * .85})`);
  gr.addColorStop(.45, `rgba(0,0,0,${I * .5})`);
  gr.addColorStop(.75, `rgba(0,0,0,${I * .18})`);
  gr.addColorStop(1, 'rgba(0,0,0,0)');
  tctx.fillStyle = gr; tctx.fillRect(0, 0, w, h);
  g.drawImage(tmpC, 0, 0, w * DPR, h * DPR, x0, y0, w, h);
}

function drawMatchBody(g, t) {
  const w = 8.5 * u, r = 8 * u, cL = m.c * Ls;
  let jx = 0, jy = 0;
  if (m.rough > .02 && !reduce) { jx = (R() - .5) * 1.6 * u * m.rough; jy = (R() - .5) * 1.2 * u * m.rough; }
  g.save();
  g.globalAlpha = m.alpha;
  // cheap shadow
  g.save(); g.translate(m.hx + 7 * u, m.hy + 9 * u); g.rotate(m.a); g.fillStyle = 'rgba(0,0,0,0.3)';
  rr(g, -w / 2, -Ls, w, Ls, 2 * u); g.fill();
  g.beginPath(); g.ellipse(0, 0, r, r * 1.1, 0, 0, TAU); g.fill(); g.restore();

  g.translate(m.hx + jx, m.hy + jy); g.rotate(m.a);
  // wood
  const lg = g.createLinearGradient(-w / 2, 0, w / 2, 0);
  lg.addColorStop(0, '#b4b4b4'); lg.addColorStop(.42, '#efefef'); lg.addColorStop(1, '#858585');
  g.fillStyle = lg; rr(g, -w / 2, -Ls, w, Ls - cL, 1.5 * u); g.fill();
  g.strokeStyle = 'rgba(70,70,70,0.32)'; g.lineWidth = .7 * u;
  for (const gx of [-.26, .04, .3]) {
    g.beginPath(); g.moveTo(gx * w, -Ls + 2 * u); g.lineTo(gx * w + (gx > 0 ? .4 : -.3) * u, -cL - 2 * u); g.stroke();
  }
  // char
  if (cL > 0) {
    const cg = g.createLinearGradient(-w / 2, 0, w / 2, 0);
    cg.addColorStop(0, '#2b2b2b'); cg.addColorStop(.5, '#444444'); cg.addColorStop(1, '#141414');
    g.fillStyle = cg; g.beginPath(); g.moveTo(-w * .42, 0); g.lineTo(-w * .42, -cL);
    const rng = mulberry32(m.seed);
    for (let i = 1; i <= 4; i++) g.lineTo(-w * .42 + w * .84 * i / 4, -cL - rng() * 2.4 * u);
    g.lineTo(w * .42, 0); g.closePath(); g.fill();
    g.strokeStyle = 'rgba(130,130,130,0.35)'; g.lineWidth = .6 * u;
    for (let k = 1; k <= 4; k++) { const y = -cL * k / 5; g.beginPath(); g.moveTo(-w * .3, y); g.lineTo(w * (.05 + rng() * .25), y - .8 * u); g.stroke(); }
  }
  // head
  const spent = m.state !== 'ready';
  const hg = g.createRadialGradient(-r * .35, -r * .4, r * .1, 0, 0, r * 1.15);
  if (!spent) { hg.addColorStop(0, '#9a9a9a'); hg.addColorStop(.3, '#505050'); hg.addColorStop(1, '#141414'); }
  else { hg.addColorStop(0, '#3a3a3a'); hg.addColorStop(.5, '#202020'); hg.addColorStop(1, '#0c0c0c'); }
  g.fillStyle = hg; g.beginPath(); g.ellipse(0, 0, r * .98, r * 1.15, 0, 0, TAU); g.fill();
  g.globalCompositeOperation = 'lighter';
  if (!spent && m.heat > .02) {
    const h = clamp(m.heat / m.need, 0, 1), g2 = g.createRadialGradient(0, 0, 0, 0, 0, r * 2.2);
    g2.addColorStop(0, `rgba(255,255,255,${.75 * h * h})`); g2.addColorStop(1, 'rgba(255,255,255,0)');
    g.fillStyle = g2; g.beginPath(); g.arc(0, 0, r * 2.2, 0, TAU); g.fill();
  }
  if (m.state === 'lit') {
    const ea = .55 + .25 * Math.sin(t * 17);
    const eg = g.createRadialGradient(0, -cL, 0, 0, -cL, w * 1.8);
    eg.addColorStop(0, `rgba(255,255,255,${ea})`); eg.addColorStop(1, 'rgba(255,255,255,0)');
    g.fillStyle = eg; g.beginPath(); g.arc(0, -cL, w * 1.8, 0, TAU); g.fill();
  }
  g.restore();
}

function flamePath(g, w, h, tx) {
  g.beginPath(); g.moveTo(0, h * .1);
  g.bezierCurveTo(-w * 1.05, h * .06, -w * .9 + tx * .35, -h * .45, tx, -h);
  g.bezierCurveTo(w * .9 + tx * .35, -h * .45, w * 1.05, h * .06, 0, h * .1);
  g.closePath();
}
// extraLean: stage 2's pull of the flame toward the torch head
function drawMatchFlame(g, t, extraLean) {
  const s = m.flame; if (m.state !== 'lit' || s <= .02) return;
  const f = frontier();
  const Hf = 74 * u * s * (1 - Math.min(.3, Math.hypot(hv.x, hv.y) / 4200));
  const Wf = 15 * u * Math.pow(s, .8);
  const sway = (Math.sin(t * 7.3) * .5 + Math.sin(t * 12.9 + 1.3) * .3) * Wf * .5 * (reduce ? .3 : 1);
  const lean = clamp(-hv.x * .035 * u + (extraLean || 0) * .4, -Wf * 2.2, Wf * 2.2);
  const tx = sway + lean;
  g.save(); g.translate(f.x, f.y);
  g.globalCompositeOperation = 'lighter';
  const rg = g.createRadialGradient(tx * .2, -Hf * .3, 0, tx * .2, -Hf * .3, Hf * 1.3);
  rg.addColorStop(0, 'rgba(255,255,255,0.30)'); rg.addColorStop(1, 'rgba(255,255,255,0)');
  g.fillStyle = rg; g.beginPath(); g.arc(tx * .2, -Hf * .3, Hf * 1.3, 0, TAU); g.fill();
  let lg = g.createLinearGradient(0, 0, 0, -Hf);
  lg.addColorStop(0, 'rgba(205,205,205,0.6)'); lg.addColorStop(.55, 'rgba(165,165,165,0.35)'); lg.addColorStop(1, 'rgba(120,120,120,0)');
  g.fillStyle = lg; flamePath(g, Wf, Hf, tx); g.fill();
  lg = g.createLinearGradient(0, 0, 0, -Hf * .72);
  lg.addColorStop(0, 'rgba(255,255,255,0.95)'); lg.addColorStop(.55, 'rgba(238,238,238,0.65)'); lg.addColorStop(1, 'rgba(220,220,220,0)');
  g.fillStyle = lg; flamePath(g, Wf * .66, Hf * .72, tx * .72); g.fill();
  g.globalCompositeOperation = 'source-over';
  g.fillStyle = 'rgba(70,70,70,0.38)';
  g.translate(0, -Hf * .04); flamePath(g, Wf * .22, Hf * .26, tx * .15); g.fill();
  g.restore();
}
function drawMatchParticles(g) {
  g.save(); g.globalCompositeOperation = 'lighter'; g.lineCap = 'round';
  for (const p of sparks) {
    g.strokeStyle = `rgba(255,255,255,${p.life / p.max})`; g.lineWidth = p.size * u;
    g.beginPath(); g.moveTo(p.x, p.y); g.lineTo(p.x - p.vx * .025, p.y - p.vy * .025); g.stroke();
  }
  g.restore();
  for (const p of smoke) {
    const a = .16 * p.a * (p.life / p.max) * Math.min(1, (p.max - p.life) / .25);
    if (a < .005) continue;
    const gr = g.createRadialGradient(p.x, p.y, 0, p.x, p.y, p.r);
    gr.addColorStop(0, `rgba(170,170,170,${a})`); gr.addColorStop(1, 'rgba(170,170,170,0)');
    g.fillStyle = gr; g.beginPath(); g.arc(p.x, p.y, p.r, 0, TAU); g.fill();
  }
}
function drawMatchLayer(g, t, lean) { drawMatchBody(g, t); drawMatchFlame(g, t, lean); drawMatchParticles(g); }

function s1Render(g, withMatch) {
  g.drawImage(base, 0, 0, W, H);
  if (L.I > .01 && L.R > 4) s1DrawLight(g, L.x, L.y, L.R, clamp(L.I, 0, 1));
  if (withMatch) drawMatchLayer(g, time, 0);
  if (flash > 0 && !reduce) { g.fillStyle = `rgba(255,255,255,${.16 * flash})`; g.fillRect(0, 0, W, H); }
}

function s1Down() { auto = null; grab(ptr.x, ptr.y); }
function grab(px, py) {
  const d = tailDir(m.a), dx = px - m.hx, dy = py - m.hy;
  let g = dx * d.x + dy * d.y;
  const perp = Math.abs(-dx * d.y + dy * d.x);
  if (!(g > 26 * u && g < Ls * .95 && perp < 90 * u)) g = 80 * u;   // far from the stick: pick it up by its middle
  m.g = g; m.grabAge = 0;
}
cv.addEventListener('keydown', e => {
  if ((e.key !== 'Enter' && e.key !== ' ') || stage !== 0 || trans || m.state !== 'ready' || auto || ptr.down) return;
  e.preventDefault(); initAudio();
  const d = tailDir(m.a); m.g = 80 * u; m.grabAge = .4;
  const sx = m.hx + d.x * m.g, sy = m.hy + d.y * m.g;
  ptr.x = ptr.lx = sx; ptr.y = ptr.ly = sy; ptr.vx = ptr.vy = 0; ptr.down = true;
  auto = { t: 0, dur: .55, sx, sy, ex: strip.x + strip.w - 20 * u };
});

/* ================================================================ 2 · LIGHT THE TORCH */
const s2 = { S: 1, torch: { x: 0, headTop: 0, headH: 0, sw: 0, shaftLen: 0, lit: false, lift: 0 },
             heat: 0, litAmt: 0, litTime: 0, flare: 0, speedS: 0, near: false, indA: 1,
             tx: 0, ty: 0, vx: 0, vy: 0, tilt: .12, lean: 0, emit: true, crackT: 0, accT: 0, accS: 0, accSm: 0 };
const TF = [], SP = [], SM = [];
const s2scene = document.createElement('canvas'), s2dark = document.createElement('canvas'), s2dg = s2dark.getContext('2d');

function s2Geom(lift) {
  const T = s2.torch, S = s2.S, top = T.headTop - lift, hh = T.headH;
  const hb = top + hh * .92, cupTop = hb - hh * .05, cupH = S * .065;
  return { x: T.x, sw: T.sw, top, hh, hb, cupTop, cupH, shaftTop: cupTop + cupH * .5, shaftBot: top + hh + T.shaftLen };
}
function s2Plate() {
  const G = s2Geom(0), S = s2.S, plateTop = G.cupTop + G.cupH + S * .04;
  return { plateTop, plateBot: plateTop + S * .30, pw: G.sw * 2.5 };
}

function s2Layout() {
  const S = s2.S = Math.min(W, H / 1.55), T = s2.torch;
  T.x = W * .5; T.sw = S * .075; T.headH = S * .15; T.headTop = H * .30; T.shaftLen = S * .7;
  s2dark.width = Math.ceil(W / 2); s2dark.height = Math.ceil(H / 2);
  s2BuildScene();
  if (stage === 1 && !trans) {
    s2.tx = m.hx = clamp(m.hx, 8, W - 8); s2.ty = m.hy = clamp(m.hy, 8, H - 8);
  }
}

function s2BuildScene() {
  s2scene.width = Math.round(W * DPR); s2scene.height = Math.round(H * DPR);
  const g = s2scene.getContext('2d'), S = s2.S, T = s2.torch;
  g.setTransform(DPR, 0, 0, DPR, 0, 0);
  const rng = mulberry32(11);
  // stone wall
  g.fillStyle = '#121212'; g.fillRect(0, 0, W, H);
  const rowH = S * .21;
  let y = -rowH * .6;
  while (y < H) {
    const rh = rowH * (.82 + rng() * .36);
    let x = -rng() * S * .5;
    while (x < W) {
      const bw = S * (.34 + rng() * .34), b = 96 + Math.floor(rng() * 40), gap = Math.max(2, S * .007);
      const bx = x + gap, by = y + gap, bwid = bw - gap * 2, bh = rh - gap * 2;
      const gr = g.createLinearGradient(bx, by, bx + bwid * .3, by + bh);
      gr.addColorStop(0, `rgb(${b + 16},${b + 16},${b + 16})`); gr.addColorStop(1, `rgb(${b - 22},${b - 22},${b - 22})`);
      g.fillStyle = gr; rr(g, bx, by, bwid, bh, S * .02); g.fill();
      g.lineWidth = 1.5;
      g.strokeStyle = 'rgba(255,255,255,.13)';
      g.beginPath(); g.moveTo(bx + S * .02, by + 1); g.lineTo(bx + bwid - S * .02, by + 1); g.stroke();
      g.strokeStyle = 'rgba(0,0,0,.38)';
      g.beginPath(); g.moveTo(bx + S * .02, by + bh - 1); g.lineTo(bx + bwid - S * .02, by + bh - 1); g.stroke();
      for (let c = 0; c < 3; c++) {
        const cx = bx + rng() * bwid, cy = by + rng() * bh, cr = S * (.01 + rng() * .03);
        g.fillStyle = `rgba(0,0,0,${.05 + rng() * .09})`;
        g.beginPath(); g.ellipse(cx, cy, cr * 1.3, cr, rng() * 3, 0, TAU); g.fill();
      }
      x += bw;
    }
    y += rh;
  }
  // grain
  const n = Math.floor(W * H / 60);
  for (let i = 0; i < n; i++) {
    const v = rng() < .5 ? 0 : 255;
    g.fillStyle = `rgba(${v},${v},${v},${.03 + rng() * .08})`;
    g.fillRect(rng() * W, rng() * H, 1 + rng() * 1.6, 1 + rng() * 1.6);
  }
  // soot above the torch
  g.save(); g.translate(T.x, T.headTop - S * .18); g.scale(1, 1.7);
  const sg = g.createRadialGradient(0, 0, 0, 0, 0, S * .38);
  sg.addColorStop(0, 'rgba(0,0,0,.78)'); sg.addColorStop(.6, 'rgba(0,0,0,.35)'); sg.addColorStop(1, 'rgba(0,0,0,0)');
  g.fillStyle = sg; g.fillRect(-S * .4, -S * .4, S * .8, S * .8); g.restore();
  // iron back plate (the bracket stays on the wall; the torch is drawn live so it can lift out)
  const P = s2Plate(), x = T.x;
  g.save(); g.shadowColor = 'rgba(0,0,0,.85)'; g.shadowBlur = S * .05; g.shadowOffsetY = S * .012;
  const pg = g.createLinearGradient(x - P.pw / 2, 0, x + P.pw / 2, 0);
  pg.addColorStop(0, '#1a1a1a'); pg.addColorStop(.5, '#555'); pg.addColorStop(1, '#202020');
  g.fillStyle = pg; rr(g, x - P.pw / 2, P.plateTop, P.pw, P.plateBot - P.plateTop, P.pw * .5); g.fill(); g.restore();
  [P.plateTop + P.pw * .45, P.plateBot - P.pw * .45].forEach(yy => {
    [-1, 1].forEach(s => {
      g.save(); g.shadowColor = 'rgba(0,0,0,.8)'; g.shadowBlur = 3; g.shadowOffsetY = 1.5;
      g.fillStyle = '#7a7a7a'; g.beginPath(); g.arc(x + s * P.pw * .35, yy, S * .008, 0, TAU); g.fill(); g.restore();
    });
  });
}

function s2DrawTorch(g, lift) {
  const G = s2Geom(lift), S = s2.S, { x, sw, top, hh, hb, cupTop, cupH, shaftTop, shaftBot } = G;
  const rng = mulberry32(23);
  // wooden shaft
  g.save(); g.shadowColor = 'rgba(0,0,0,.7)'; g.shadowBlur = S * .02; g.shadowOffsetX = S * .006;
  let gr = g.createLinearGradient(x - sw / 2, 0, x + sw / 2, 0);
  gr.addColorStop(0, '#1b1b1b'); gr.addColorStop(.35, '#6b6b6b'); gr.addColorStop(.7, '#3a3a3a'); gr.addColorStop(1, '#141414');
  g.fillStyle = gr; rr(g, x - sw / 2, shaftTop, sw, shaftBot - shaftTop, sw * .3); g.fill(); g.restore();
  g.strokeStyle = 'rgba(0,0,0,.35)'; g.lineWidth = 1;
  for (let i = 0; i < 10; i++) {
    const gx = x - sw / 2 + sw * (.1 + rng() * .8), gy = shaftTop + rng() * (shaftBot - shaftTop - 60);
    g.beginPath(); g.moveTo(gx, gy); g.lineTo(gx + (rng() - .5) * 2, gy + 20 + rng() * 50); g.stroke();
  }
  // wrapped head
  g.beginPath();
  g.moveTo(x - sw * .55, hb);
  g.bezierCurveTo(x - sw * 1.1, hb - hh * .3, x - sw * 1.0, top + hh * .15, x - sw * .75, top + hh * .1);
  g.quadraticCurveTo(x, top - hh * .18, x + sw * .75, top + hh * .1);
  g.bezierCurveTo(x + sw * 1.0, top + hh * .15, x + sw * 1.1, hb - hh * .3, x + sw * .55, hb);
  g.closePath();
  gr = g.createLinearGradient(x - sw, 0, x + sw, 0);
  gr.addColorStop(0, '#0f0f0f'); gr.addColorStop(.4, '#5a5a5a'); gr.addColorStop(.75, '#202020'); gr.addColorStop(1, '#0b0b0b');
  g.fillStyle = gr; g.fill();
  g.save(); g.clip();
  for (let i = 0; i < 8; i++) {
    const yy = top + hh * (.12 + i * .11);
    g.lineWidth = S * .006;
    g.strokeStyle = 'rgba(0,0,0,.6)';
    g.beginPath(); g.moveTo(x - sw * 1.2, yy + hh * .06); g.quadraticCurveTo(x, yy - hh * .04, x + sw * 1.2, yy + hh * .06); g.stroke();
    g.strokeStyle = 'rgba(255,255,255,.12)';
    g.beginPath(); g.moveTo(x - sw * 1.2, yy + hh * .06 + 2); g.quadraticCurveTo(x, yy - hh * .04 + 2, x + sw * 1.2, yy + hh * .06 + 2); g.stroke();
  }
  const cg = g.createLinearGradient(0, top, 0, top + hh * .45);
  cg.addColorStop(0, 'rgba(0,0,0,.85)'); cg.addColorStop(1, 'rgba(0,0,0,0)');
  g.fillStyle = cg; g.fillRect(x - sw * 1.5, top - hh * .3, sw * 3, hh * .8);
  g.restore();
  // iron cup under the head
  g.save(); g.shadowColor = 'rgba(0,0,0,.7)'; g.shadowBlur = S * .02; g.shadowOffsetY = S * .008;
  gr = g.createLinearGradient(x - sw * 1.05, 0, x + sw * 1.05, 0);
  gr.addColorStop(0, '#151515'); gr.addColorStop(.45, '#7a7a7a'); gr.addColorStop(1, '#191919');
  g.fillStyle = gr; g.beginPath();
  g.moveTo(x - sw * 1.05, cupTop); g.lineTo(x + sw * 1.05, cupTop);
  g.lineTo(x + sw * .6, cupTop + cupH); g.lineTo(x - sw * .6, cupTop + cupH);
  g.closePath(); g.fill(); g.restore();
  g.strokeStyle = 'rgba(255,255,255,.25)'; g.lineWidth = 1.5;
  g.beginPath(); g.moveTo(x - sw * 1.0, cupTop + 1); g.lineTo(x + sw * 1.0, cupTop + 1); g.stroke();
}
function s2DrawBands(g) {
  const P = s2Plate(), S = s2.S, x = s2.torch.x, sw = s2.torch.sw;
  [P.plateTop + S * .05, P.plateBot - S * .06].forEach(by => {
    const bw = sw * 1.35, bh = S * .032;
    g.save(); g.shadowColor = 'rgba(0,0,0,.75)'; g.shadowBlur = S * .012; g.shadowOffsetY = S * .006;
    const bgr = g.createLinearGradient(x - bw / 2, 0, x + bw / 2, 0);
    bgr.addColorStop(0, '#111'); bgr.addColorStop(.4, '#7a7a7a'); bgr.addColorStop(1, '#1a1a1a');
    g.fillStyle = bgr; rr(g, x - bw / 2, by, bw, bh, bh * .4); g.fill(); g.restore();
    g.strokeStyle = 'rgba(255,255,255,.22)'; g.lineWidth = 1;
    g.beginPath(); g.moveTo(x - bw / 2 + 4, by + 2); g.lineTo(x + bw / 2 - 4, by + 2); g.stroke();
  });
}

function s2Burst() {
  const S = s2.S, T = s2.torch, b = T.headTop - T.lift + T.headH * .12;
  for (let i = 0; i < 55; i++)
    TF.push({ x: T.x + (R() - .5) * T.sw * 1.4, y: b, vx: (R() - .5) * S * .12, vy: -S * (.35 + R() * .55), a: 0, l: .7 + R() * .7, s: S * .05 * (.8 + R() * .6), k: R() * 10 });
  for (let i = 0; i < 16; i++)
    SP.push({ x: T.x + (R() - .5) * T.sw, y: b - S * .05, vx: (R() - .5) * S * .45, vy: -S * (.25 + R() * .55), a: 0, l: .9 + R() * 1.3, s: S * .007, k: R() * 10 });
}
function s2PuffSmoke(x, y, n) {
  const S = s2.S;
  for (let i = 0; i < n; i++)
    SM.push({ x: x + (R() - .5) * 6, y, vx: (R() - .5) * 10, vy: -S * (.06 + R() * .06), a: 0, l: 2 + R() * 1.5, s: S * (.012 + R() * .01), gr: S * .05, k: R() * 10 });
}
function s2Crackle(vol, f, delay) { burst({ dur: .012 + R() * .04, f, q: 1.2, gain: vol * 3, att: .002, delay }); }
function s2AudioIgnite() {
  if (!live()) return;
  const c = A.c, tm = c.currentTime;
  const s = c.createBufferSource(); s.buffer = A.noise; s.loop = true;
  const lp = c.createBiquadFilter(); lp.type = 'lowpass'; lp.Q.value = .8;
  lp.frequency.setValueAtTime(250, tm);
  lp.frequency.exponentialRampToValueAtTime(4200, tm + .18);
  lp.frequency.exponentialRampToValueAtTime(900, tm + .9);
  const g = c.createGain();
  g.gain.setValueAtTime(.0001, tm); g.gain.exponentialRampToValueAtTime(1.6, tm + .1); g.gain.exponentialRampToValueAtTime(.0001, tm + 1.1);
  s.connect(lp); lp.connect(g); g.connect(A.master);
  s.start(tm, R() * 1.5); s.stop(tm + 1.2);
  thump(110, 38, .35, .7, .5);
  for (let i = 0; i < 9; i++) s2Crackle(.15 + R() * .25, 1500 + R() * 3500, i * .045 + R() * .03);
  fireBed.gain.cancelScheduledValues(tm);
  fireBed.gain.setTargetAtTime(.85, tm + .1, .5);
}

function s2Ignite() {
  const T = s2.torch;
  T.lit = true; s2.litTime = 0; s2.flare = 1;
  s2AudioIgnite(); s2Burst();
  buzz(20);
}

function s2Update(dt, t) {
  const S = s2.S, T = s2.torch, active = stage === 1 && !trans;
  // the match follows the finger, its flame sitting above the grip
  if (active) {
    if (ptr.down) { s2.tx = clamp(ptr.x, 8, W - 8); s2.ty = clamp(ptr.y - S * .22, 8, H - 8); }
    const k = 1 - Math.exp(-dt * 16), px = m.hx, py = m.hy;
    m.hx += (s2.tx - m.hx) * k; m.hy += (s2.ty - m.hy) * k;
    const vx = (m.hx - px) / dt, vy = (m.hy - py) / dt, kv = 1 - Math.exp(-dt * 10);
    s2.vx += (vx - s2.vx) * kv; s2.vy += (vy - s2.vy) * kv;
    s2.speedS += (Math.hypot(s2.vx, s2.vy) - s2.speedS) * (1 - Math.exp(-dt * 6));
    const tiltT = .12 + clamp(-s2.vx / (S * 2.5), -.5, .5) + (ptr.down ? 0 : Math.sin(t * 1.7) * .02);
    s2.tilt += (tiltT - s2.tilt) * (1 - Math.exp(-dt * 8));
    m.a = Math.PI - s2.tilt;
    trackHead(dt, px, py);
  }
  updateMatchFlame(dt, t);
  updateMatchParticles(dt);

  // proximity + hold detection
  const fp = flamePoint(), top = T.headTop - T.lift;
  const igx = T.x, igy = top + T.headH * .1;
  const dist = Math.hypot(fp.x - igx, fp.y - igy);
  s2.near = m.state === 'lit' && dist < S * .15;
  const still = s2.speedS < Math.max(55, S * .18);
  const holding = active && ptr.down && s2.near && still && !T.lit;
  if (!T.lit) {
    s2.heat = clamp(s2.heat + (holding ? dt / 1.25 : -dt / .7), 0, 1);
    if (s2.heat >= 1) s2Ignite();
  }
  if (T.lit) {
    s2.litTime += dt;
    s2.litAmt = 1 - Math.exp(-s2.litTime * 6);
    s2.flare = Math.exp(-s2.litTime * 1.6);
    // once it has caught, the torch lifts itself out of the bracket
    T.lift = S * .25 * ease(clamp((s2.litTime - 1.6) / .9, 0, 1));
    if (s2.litTime > 2.6 && active) startTrans('t2');
  }
  const leanRange = S * .4;
  s2.lean = dist < leanRange && m.state === 'lit' ? ((igx - fp.x) / (dist || 1)) * (1 - dist / leanRange) * S * .25 : 0;

  // torch flame particles
  const fsz = s2.litAmt * (1 + .6 * s2.flare), baseY = top + T.headH * .12;
  if (T.lit && s2.emit) {
    s2.accT += dt * 110 * s2.litAmt * (1 + .5 * s2.flare);
    while (s2.accT >= 1) {
      s2.accT -= 1;
      TF.push({ x: T.x + (R() - .5) * T.sw * 1.1, y: baseY, vx: (R() - .5) * 10, vy: -S * .42 * (.65 + R() * .7) * (1 + .25 * s2.flare),
                a: 0, l: .8 * (.7 + R() * .6), s: S * .05 * (.7 + R() * .6) * Math.min(1.2, .5 + fsz * .6), k: R() * 10 });
    }
    s2.accS += dt * 5 * s2.litAmt;
    while (s2.accS >= 1) {
      s2.accS -= 1;
      SP.push({ x: T.x + (R() - .5) * T.sw, y: baseY - S * .08, vx: (R() - .5) * S * .15, vy: -S * (.25 + R() * .3), a: 0, l: .9 + R() * 1.2, s: S * .006, k: R() * 10 });
    }
    s2.accSm += dt * 5;
    while (s2.accSm >= 1) { s2.accSm -= 1; s2PuffSmoke(T.x + (R() - .5) * 10, top - S * .3, 1); }
    // crackle while the torch burns
    s2.crackT -= dt;
    if (s2.crackT <= 0 && s2.litTime > .3) {
      const n = 1 + Math.floor(R() * 3);
      for (let i = 0; i < n; i++) s2Crackle(.08 + R() * .22, 1200 + R() * 3800, i * R() * .06);
      s2.crackT = .05 + R() * .26;
    }
  }
  for (let i = TF.length - 1; i >= 0; i--) {
    const p = TF[i]; p.a += dt;
    if (p.a >= p.l) { TF[i] = TF[TF.length - 1]; TF.pop(); continue; }
    const k = p.a / p.l;
    p.vx += (T.x - p.x) * 5 * dt;
    p.x += (p.vx + Math.sin(t * 6 + p.k) * S * .16 * k) * dt; p.y += p.vy * dt;
  }
  for (let i = SP.length - 1; i >= 0; i--) {
    const p = SP[i]; p.a += dt;
    if (p.a >= p.l) { SP[i] = SP[SP.length - 1]; SP.pop(); continue; }
    p.vy += S * .12 * dt; p.vx *= .99;
    p.x += (p.vx + Math.sin(t * 5 + p.k) * S * .04) * dt; p.y += p.vy * dt;
  }
  // heating smoke
  if (!T.lit && s2.heat > .15) {
    s2.accSm += dt * s2.heat * 16;
    while (s2.accSm >= 1) { s2.accSm -= 1; s2PuffSmoke(T.x + (R() - .5) * T.sw * .8, top, 1); }
  }
  for (let i = SM.length - 1; i >= 0; i--) {
    const p = SM[i]; p.a += dt;
    if (p.a >= p.l) { SM[i] = SM[SM.length - 1]; SM.pop(); continue; }
    p.s += p.gr * dt;
    p.x += (p.vx + Math.sin(t * 1.7 + p.k) * S * .02) * dt; p.y += p.vy * dt;
  }

  s2.indA += ((T.lit ? 0 : 1) - s2.indA) * (1 - Math.exp(-dt * 4));
  if (active) {   // the study keeps its words for screen readers only; the pulsing target does the guiding
    if (T.lit) setHint('The torch is lit.', true);
    else if (s2.near && ptr.down) setHint('Hold still.', true);
    else setHint('Drag the match to the torch.', true);
  }
  setGain(heatGain, T.lit ? 0 : s2.heat * .12, .08);
}

function s2Light(g, x, y, r, a) {
  const cx = x * .5, cy = y * .5, cr = r * .5;
  const gr = g.createRadialGradient(cx, cy, 0, cx, cy, cr);
  gr.addColorStop(0, `rgba(0,0,0,${a})`); gr.addColorStop(.25, `rgba(0,0,0,${a * .72})`);
  gr.addColorStop(.6, `rgba(0,0,0,${a * .25})`); gr.addColorStop(1, 'rgba(0,0,0,0)');
  g.fillStyle = gr; g.fillRect(cx - cr, cy - cr, cr * 2, cr * 2);
}

// o.match: draw the match here; o.matchLight: where the match flame lights the wall (scene coords); o.torch: draw the torch here
function s2Render(g, o) {
  const S = s2.S, T = s2.torch, top = T.headTop - T.lift, t = time;
  g.drawImage(s2scene, 0, 0, W, H);
  for (const p of SM) {
    const k = p.a / p.l;
    g.globalAlpha = (1 - k) * (k < .1 ? k / .1 : 1) * .55;
    g.drawImage(SPR.smoke2, p.x - p.s, p.y - p.s, p.s * 2, p.s * 2);
  }
  g.globalAlpha = 1;
  if (o.torch) s2DrawTorch(g, T.lift);
  s2DrawBands(g);
  if (o.match) drawMatchBody(g, t);

  // darkness with light cut out
  const flick = 1 + .05 * Math.sin(t * 12.3) + .035 * Math.sin(t * 7.9 + 2) + .025 * Math.sin(t * 23.1 + 1) + (R() - .5) * .02;
  s2dg.globalCompositeOperation = 'source-over';
  s2dg.clearRect(0, 0, s2dark.width, s2dark.height);
  s2dg.fillStyle = 'rgba(0,0,0,0.82)'; s2dg.fillRect(0, 0, s2dark.width, s2dark.height);
  s2dg.globalCompositeOperation = 'destination-out';
  if (o.matchLight && m.state === 'lit') s2Light(s2dg, o.matchLight.x, o.matchLight.y, S * .62 * flick, .95);
  if (s2.heat > .02 && !T.lit) s2Light(s2dg, T.x, top, S * .28, .5 * s2.heat);
  if (s2.litAmt > .01) {
    const cy = top - S * .12;
    s2Light(s2dg, T.x, cy, S * 1.7 * s2.litAmt * (1 + .25 * s2.flare) * flick, 1.0);
    s2Light(s2dg, T.x, cy, S * 3.0 * s2.litAmt * flick, .38);
  }
  s2dg.globalCompositeOperation = 'source-over';
  g.drawImage(s2dark, 0, 0, W, H);

  // additive: glows and flames
  g.globalCompositeOperation = 'lighter';
  if (s2.heat > .02 && !T.lit) {
    const Rr = S * .06 + s2.heat * S * .05;
    g.globalAlpha = s2.heat * .8;
    g.drawImage(SPR.hot, T.x - Rr, top - Rr * .6, Rr * 2, Rr * 2);
  }
  if (s2.litAmt > .01) {
    const cy = top - S * .12, Rr = S * .5 * s2.litAmt;
    g.globalAlpha = .2 * s2.litAmt * flick;
    g.drawImage(SPR.soft, T.x - Rr, cy - Rr, Rr * 2, Rr * 2);
  }
  for (const p of TF) {
    const k = p.a / p.l, s = p.s * (1 - k * .85), a = Math.pow(1 - k, 1.2);
    g.globalAlpha = a * .16; g.drawImage(SPR.soft, p.x - s * 2.2, p.y - s * 2.2, s * 4.4, s * 4.4);
    g.globalAlpha = a * .34; g.drawImage(SPR.hot, p.x - s, p.y - s, s * 2, s * 2);
  }
  for (const p of SP) {
    const k = p.a / p.l, s = p.s * (1 - k * .5) * 3;
    g.globalAlpha = (1 - k) * (.5 + R() * .5);
    g.drawImage(SPR.hot, p.x - s, p.y - s, s * 2, s * 2);
  }
  // pulsing target on the torch head
  if (s2.indA > .01) {
    const ix = T.x, iy = top + T.headH * .1, holdingNow = s2.near && ptr.down, r0 = S * .05, ia = s2.indA;
    g.strokeStyle = '#fff'; g.fillStyle = '#fff';
    const breathe = .5 + .5 * Math.sin(t * 3.2);
    g.globalAlpha = ia * (.16 + .16 * breathe);
    g.drawImage(SPR.soft, ix - r0 * 2.4, iy - r0 * 2.4, r0 * 4.8, r0 * 4.8);
    g.lineWidth = 1.5; g.globalAlpha = ia * .28;
    g.beginPath(); g.arc(ix, iy, r0, 0, TAU); g.stroke();
    g.globalAlpha = ia * (.55 + .35 * breathe);
    g.beginPath(); g.arc(ix, iy, 3, 0, TAU); g.fill();
    if (holdingNow) {
      g.lineWidth = 3.5; g.lineCap = 'round'; g.globalAlpha = ia * .9;
      g.beginPath(); g.arc(ix, iy, r0, -Math.PI / 2, -Math.PI / 2 + Math.max(.02, s2.heat) * TAU); g.stroke();
    } else {
      const ph = (t * .9) % 1;
      g.lineWidth = 2; g.globalAlpha = ia * (1 - ph) * .7;
      g.beginPath(); g.arc(ix, iy, r0 * (.35 + 1.1 * ph), 0, TAU); g.stroke();
    }
  }
  g.globalCompositeOperation = 'source-over'; g.globalAlpha = 1;
  if (o.match) { drawMatchFlame(g, t, s2.lean); drawMatchParticles(g); }
}

/* ================================================================ 3 · TORCH THROW */
const s3 = { GW: 0, GX: 0, k: 1, horizonY: 0, groundY: 0, landY: 0, torchLen: 70, start: { x: 0, y: 0 },
             pile: { cx: 0, w: 0, h: 0, frac: .76, logs: [] }, ice: { x: 0, y: 0, s: 50 },
             torch: { x: 0, y: 0, tx: 0, ty: 0, rot: -rad(50), trot: -rad(50), vx: 0, vy: 0, spin: 0, flame: 1, bounces: 0, fizzled: false },
             aim: { theta: rad(50), p: 0 }, mode: 'idle', drag: null, burn: 0, burnTarget: 0, flash: 0, litT: 0, missT: 0,
             bg: null, acc: { torch: 0, fire: 0, smoke: 0, ember: 0, crack: 0 } };
const READY = .15;            // minimum slide (0..1) that counts as a throw
const parts3 = [];
const grainC = (() => {
  const c = document.createElement('canvas'); c.width = c.height = 128;
  const x = c.getContext('2d'), d = x.createImageData(128, 128);
  for (let i = 0; i < d.data.length; i += 4) { const v = R() * 255; d.data[i] = d.data[i + 1] = d.data[i + 2] = v; d.data[i + 3] = 255; }
  x.putImageData(d, 0, 0); return c;
})();
const grainPat = new Map();
const grainFor = g => { if (!grainPat.has(g)) grainPat.set(g, g.createPattern(grainC, 'repeat')); return grainPat.get(g); };

function s3Layout() {
  const q = s3;
  q.GW = Math.min(W, 520); q.GX = (W - q.GW) / 2; q.k = q.GW / 390;
  q.horizonY = H * .56; q.groundY = H * .73; q.landY = H * .86;
  q.torchLen = clamp(q.GW * .19, 60, 96);
  q.start.x = q.GX + q.GW * .2; q.start.y = H * .80;
  q.pile.w = clamp(q.GW * .3, 96, 160); q.pile.h = q.pile.w * .5;
  q.pile.cx = q.GX + q.GW * q.pile.frac;
  q.ice.s = clamp(q.GW * .13, 40, 62); q.ice.x = q.GX + q.GW * .47; q.ice.y = H * .93;
  s3BuildPile(); s3BuildBg();
  if (q.mode === 'idle' && !(trans && trans.kind === 't2')) { q.torch.x = q.torch.tx = q.start.x; q.torch.y = q.torch.ty = q.start.y; }
}

function s3BuildBg() {
  const q = s3;
  q.bg = document.createElement('canvas');
  q.bg.width = Math.round(W * DPR); q.bg.height = Math.round(H * DPR);
  const b = q.bg.getContext('2d'); b.setTransform(DPR, 0, 0, DPR, 0, 0);
  const rng = mulberry32(4242), hy = q.horizonY;
  let g = b.createLinearGradient(0, 0, 0, hy);
  g.addColorStop(0, '#040404'); g.addColorStop(.7, '#171717'); g.addColorStop(1, '#2a2a2a');
  b.fillStyle = g; b.fillRect(0, 0, W, hy + 2);
  for (let i = 0; i < 120; i++) {
    const x = rng() * W, y = rng() * hy * .92, a = .15 + rng() * .6, s = rng() < .1 ? 1.7 : 1;
    b.fillStyle = `rgba(255,255,255,${a})`; b.fillRect(x, y, s, s);
  }
  const mx = W * .2, my = H * .13, mr = Math.min(W, H) * .045;
  g = b.createRadialGradient(mx, my, mr * .5, mx, my, mr * 6);
  g.addColorStop(0, 'rgba(255,255,255,.2)'); g.addColorStop(1, 'rgba(255,255,255,0)');
  b.fillStyle = g; b.fillRect(mx - mr * 6, my - mr * 6, mr * 12, mr * 12);
  b.fillStyle = '#d6d6d6'; b.beginPath(); b.arc(mx, my, mr, 0, TAU); b.fill();
  b.fillStyle = 'rgba(0,0,0,.12)';
  [[-.3, -.2, .28], [.35, .15, .2], [-.1, .45, .16]].forEach(([dx, dy, r]) => { b.beginPath(); b.arc(mx + dx * mr, my + dy * mr, r * mr, 0, TAU); b.fill(); });
  b.fillStyle = '#121212'; b.beginPath(); b.moveTo(0, hy + 4);
  for (let x = 0; x <= W + 12; x += 12) b.lineTo(x, hy - 16 - Math.sin(x * .011) * 14 - Math.sin(x * .027 + 2) * 8);
  b.lineTo(W, hy + 4); b.fill();
  const pine = (x, y, h, col) => {
    b.fillStyle = col;
    for (let i = 0; i < 4; i++) {
      const ya = y - h * (1 - i * .2), yb = ya + h * .34, hw = h * (.11 + .065 * i);
      b.beginPath(); b.moveTo(x, ya); b.lineTo(x - hw, yb); b.lineTo(x + hw, yb); b.fill();
    }
    b.fillRect(x - h * .02, y - h * .08, h * .04, h * .08);
  };
  for (let x = -10; x < W + 20; x += 9 + rng() * 12) pine(x, hy + 3, H * (.05 + rng() * .05), '#0d0d0d');
  for (let x = -10; x < W + 30; x += 28 + rng() * 34) pine(x, hy + 8, H * (.08 + rng() * .07), '#070707');
  g = b.createLinearGradient(0, hy - 36, 0, hy + 50);
  g.addColorStop(0, 'rgba(255,255,255,0)'); g.addColorStop(.5, 'rgba(255,255,255,.075)'); g.addColorStop(1, 'rgba(255,255,255,0)');
  b.fillStyle = g; b.fillRect(0, hy - 36, W, 86);
  g = b.createLinearGradient(0, hy, 0, H);
  g.addColorStop(0, '#1d1d1d'); g.addColorStop(.45, '#111'); g.addColorStop(1, '#050505');
  b.fillStyle = g; b.fillRect(0, hy + 4, W, H - hy);
  for (let i = 0; i < 260; i++) {
    const y = hy + 8 + Math.pow(rng(), 1.4) * (H - hy - 8), d = (y - hy) / (H - hy), x = rng() * W, l = 2 + d * 11;
    b.strokeStyle = `rgba(255,255,255,${.04 + rng() * .08})`; b.lineWidth = 1 + d;
    b.beginPath(); b.moveTo(x, y); b.lineTo(x + (rng() - .5) * 4, y - l); b.stroke();
  }
  for (let i = 0; i < 26; i++) {
    const y = hy + 20 + rng() * (H - hy - 20), d = (y - hy) / (H - hy), x = rng() * W;
    b.fillStyle = `rgba(255,255,255,${.04 + rng() * .05})`;
    b.beginPath(); b.ellipse(x, y, (3 + rng() * 7) * (.5 + d), (2 + rng() * 3) * (.5 + d), 0, 0, TAU); b.fill();
  }
}

function s3BuildPile() {
  const p = s3.pile, rng = mulberry32(Math.floor(p.frac * 1000) + 17);
  const t = p.w * .12, gy = s3.groundY, Lg = [];
  for (let i = 0; i < 4; i++) Lg.push({ type: 'side', x: p.cx + (i / 3 - .5) * p.w * .62, y: gy - t * .5 - rng() * 2, len: p.w * .52, a: (rng() - .5) * .25, t: t * (.9 + rng() * .2), sh: rng() });
  for (let i = 0; i < 3; i++) Lg.push({ type: 'end', x: p.cx + (i / 2 - .5) * p.w * .4, y: gy - t * 1.35, r: t * .55, sh: rng() });
  for (let i = 0; i < 2; i++) Lg.push({ type: 'side', x: p.cx + (i - .5) * p.w * .3, y: gy - t * 2.15, len: p.w * .46, a: (i ? -1 : 1) * .25 + (rng() - .5) * .1, t: t * .92, sh: rng() });
  Lg.push({ type: 'side', x: p.cx - p.w * .08, y: gy - t * 3, len: p.w * .4, a: -.55, t: t * .85, sh: rng() });
  Lg.push({ type: 'side', x: p.cx + p.w * .08, y: gy - t * 3, len: p.w * .4, a: .55, t: t * .85, sh: rng() });
  p.logs = Lg;
}

// audio for stages 3 and 4
function crackle(amp, delay) { burst({ dur: .006 + rnd(.03), f: 1200 + rnd(4800), q: 1 + rnd(4), gain: amp, att: .002, delay }); }
function pop(amp, delay) { burst({ dur: .05 + rnd(.05), f: 260 + rnd(420), q: 2, gain: amp, att: .003, delay }); }
function sfxFlare() { burst({ dur: .28, f: 200, f2: 1100, sweep: .6, q: .8, gain: .22, att: .04 }); }
function sfxThrow(p) { burst({ dur: .55, f: 450, f2: 1500, sweep: .4, q: .9, gain: .22 + .3 * p, att: .05 }); }
function sfxFizzle() { burst({ dur: .7, type: 'highpass', f: 3200, q: .7, gain: .16, att: .03 }); }
function sfxIgnite3() {
  burst({ dur: 1.5, f: 220, f2: 2600, sweep: .28, q: .7, gain: .95, att: .07 });        // whoosh of the fire catching
  burst({ dur: 1.2, type: 'lowpass', f: 520, f2: 140, q: .5, gain: .9, att: .05 });      // low rumble
  thump(115, 40, .28, .7, .38);
  for (let i = 0; i < 18; i++) crackle(.45 + rnd(.5), .04 + rnd(1.1));
  for (let i = 0; i < 3; i++) pop(.5, .1 + rnd(.7));
}
function fireAudio(dt, level) {
  if (!A.c || !roarGain) return;
  const fl = level * (.82 + .18 * Math.sin(time * 9) * Math.sin(time * 4.1));
  roarGain.gain.setTargetAtTime(.22 * fl, A.c.currentTime, .08);
  if (level > .15 && live()) {
    s3.acc.crack += dt * (5 + 15 * level);
    while (s3.acc.crack >= 1) {
      s3.acc.crack -= 1;
      crackle((.1 + rnd(.25)) * (.5 + level * .5));
      if (R() < .14) pop(.25 + rnd(.3));
    }
  }
}

function spawn3(type, x, y, vx, vy, max, s0, s1, a, buoy) {
  if (parts3.length > 900) return;
  parts3.push({ type, x, y, vx, vy, life: 0, max, s0, s1, a, buoy: buoy || 0, seed: R() * 100 });
}
function s3UpdateParticles(dt) {
  const k = s3.k;
  for (let i = parts3.length - 1; i >= 0; i--) {
    const p = parts3[i]; p.life += dt;
    if (p.life >= p.max) { parts3[i] = parts3[parts3.length - 1]; parts3.pop(); continue; }
    p.vy += p.buoy * dt;
    if (p.type === 0) { p.x += (p.vx + Math.sin(time * 9 + p.seed) * 16 * k) * dt; p.y += p.vy * dt; p.vx *= Math.exp(-1.2 * dt); p.vy *= Math.exp(-.8 * dt); }
    else if (p.type === 1) { p.vx += 6 * k * dt; p.x += p.vx * dt + Math.sin(time * 1.5 + p.seed) * 8 * k * dt; p.y += p.vy * dt; p.vy *= Math.exp(-.5 * dt); }
    else { p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= Math.exp(-.6 * dt); }
  }
}
function headPos() { const T = s3.torch; return { x: T.x + Math.cos(T.rot) * s3.torchLen * .5, y: T.y + Math.sin(T.rot) * s3.torchLen * .5 }; }
function s3EmitTorch(dt) {
  const T = s3.torch, k = s3.k;
  if (T.flame < .03) return;
  const h = headPos(), Lt = s3.torchLen;
  const hx = h.x + Math.cos(T.rot) * Lt * .04, hy = h.y + Math.sin(T.rot) * Lt * .04;
  s3.acc.torch += dt * 70 * T.flame;
  while (s3.acc.torch >= 1) {
    s3.acc.torch -= 1;
    const s0 = rnd(7, 12) * k * (.5 + .5 * T.flame);
    spawn3(0, hx + rnd(-3, 3) * k, hy + rnd(-3, 3) * k, T.vx * .14 + rnd(-12, 12) * k, T.vy * .14 - rnd(20, 60) * k, rnd(.3, .6), s0, s0 * .2, .55, -170 * k);
  }
  if (R() < dt * 7 * T.flame) spawn3(1, hx, hy, rnd(-6, 6) * k, -rnd(20, 40) * k, rnd(.9, 1.5), 3 * k, 16 * k, .08, 0);
  if (s3.mode === 'fly' && R() < dt * 18) spawn3(2, hx, hy, T.vx * .05 + rnd(-30, 30) * k, rnd(-40, 20) * k, rnd(.5, 1), 1.4 * k, 1 * k, .9, 90 * k);
}
function s3EmitFire(dt) {
  const q = s3, burn = q.burn, pile = q.pile, k = q.k;
  if (burn < .01) return;
  const pk = pile.w / 117, fy = q.groundY - pile.h * .5;
  q.acc.fire += dt * 130 * burn;
  while (q.acc.fire >= 1) {
    q.acc.fire -= 1;
    const s0 = rnd(10, 24) * pk * (.35 + .85 * burn);
    spawn3(0, pile.cx + rnd(-1, 1) * pile.w * .26 * (.5 + .5 * burn), fy + rnd(-.2, .35) * pile.h, rnd(-26, 26) * pk, -rnd(60, 170) * pk * (.5 + .8 * burn), rnd(.5, 1.1), s0, s0 * .25, .5, -150 * pk);
  }
  q.acc.smoke += dt * 9 * burn;
  while (q.acc.smoke >= 1) { q.acc.smoke -= 1; spawn3(1, pile.cx + rnd(-1, 1) * pile.w * .2, fy - pile.h * .6, rnd(-8, 8) * pk, -rnd(40, 80) * pk, rnd(2, 3.6), 14 * pk, 52 * pk, .11, 0); }
  q.acc.ember += dt * 9 * burn;
  while (q.acc.ember >= 1) { q.acc.ember -= 1; spawn3(2, pile.cx + rnd(-1, 1) * pile.w * .2, fy - pile.h * .3, rnd(-45, 45) * pk, -rnd(90, 260) * pk, rnd(1.2, 2.4), rnd(1.2, 2.4) * k, .8 * k, 1, 70 * pk); }
}
function s3Burst(x, y) {
  const pk = s3.pile.w / 117, k = s3.k;
  for (let i = 0; i < 40; i++) { const s0 = rnd(14, 28) * pk; spawn3(0, x + rnd(-12, 12) * pk, y + rnd(-8, 8) * pk, rnd(-90, 90) * pk, -rnd(60, 240) * pk, rnd(.6, 1.2), s0, s0 * .2, .6, -160 * pk); }
  for (let i = 0; i < 32; i++) spawn3(2, x, y, rnd(-220, 220) * pk, -rnd(120, 420) * pk, rnd(.8, 1.8), rnd(1.4, 2.8) * k, .8 * k, 1, 220 * pk);
}

function onPile(x, y) {
  const p = s3.pile, uu = 1 - Math.abs(x - p.cx) / (p.w * .5);
  if (uu <= 0) return false;
  const top = s3.groundY - p.h * Math.pow(uu, .8);
  return y >= top && y <= s3.groundY + p.h * .15;
}
function checkHit() {
  const T = s3.torch, c = Math.cos(T.rot), s = Math.sin(T.rot), Lt = s3.torchLen;
  return onPile(T.x + c * Lt * .5, T.y + s * Lt * .5) || onPile(T.x, T.y) || onPile(T.x - c * Lt * .5, T.y - s * Lt * .5);
}
function s3Launch() {
  const T = s3.torch, p = s3.aim.p, th = s3.aim.theta, v = s3.GW * (1 + 1.2 * p);
  T.vx = Math.cos(th) * v; T.vy = -Math.sin(th) * v;
  T.spin = 9; T.bounces = 0; T.fizzled = false; T.flame = 1;
  s3.mode = 'fly'; sfxThrow(p);
}
function s3Ignite() {
  const q = s3, T = q.torch, pile = q.pile;
  q.mode = 'lit'; q.litT = 0;
  const h = headPos();
  const hx = clamp(h.x, pile.cx - pile.w * .3, pile.cx + pile.w * .3);
  const hy = clamp(h.y, q.groundY - pile.h * .85, q.groundY - pile.h * .15);
  const r = .5;
  T.trot = r; T.tx = hx - Math.cos(r) * q.torchLen * .4; T.ty = hy - Math.sin(r) * q.torchLen * .4;
  T.vx = T.vy = T.spin = 0; T.flame = .55;
  q.burnTarget = 1; q.burn = Math.max(q.burn, .15); q.flash = 1;
  s3Burst(hx, hy); sfxIgnite3();
  buzz([18, 30, 28]);
}
function s3GroundHit() {
  const T = s3.torch, k = s3.k;
  if (T.bounces < 2 && Math.abs(T.vy) > 90 * k) {
    T.y = s3.landY - .1; T.vy = -T.vy * .32; T.vx *= .55; T.spin *= .35; T.bounces++;
    if (!T.fizzled) { T.fizzled = true; sfxFizzle(); }
  } else {
    T.y = s3.landY; T.vx = T.vy = T.spin = 0; s3.mode = 'miss'; s3.missT = 0;
    if (!T.fizzled) { T.fizzled = true; sfxFizzle(); }
  }
}
function s3MissOffscreen() { const T = s3.torch; T.vx = T.vy = T.spin = 0; s3.mode = 'miss'; s3.missT = 0; T.flame = 0; }
function s3ResetTorch() {   // the same torch comes back to your hand and catches again
  const T = s3.torch;
  s3.mode = 'idle'; T.x = T.tx = s3.start.x; T.y = T.ty = s3.start.y;
  T.rot = T.trot = -rad(50); T.flame = 0; T.vx = T.vy = 0; sfxFlare();
}

function s3Down() {
  const T = s3.torch;
  if (s3.mode !== 'idle' || s3.drag) return;
  if (Math.hypot(ptr.x - T.x, ptr.y - T.y) > Math.max(90, s3.torchLen * 1.15)) return;
  s3.drag = { id: ptr.id, ox: ptr.x, oy: ptr.y, dx: 0, dy: 0 };
  s3.mode = 'aim'; sfxFlare();
}
function s3Move() { const d = s3.drag; if (!d) return; d.dx = ptr.x - d.ox; d.dy = ptr.y - d.oy; }
function s3Up(cancel) {
  if (!s3.drag) return;
  const ok = !cancel && s3.aim.p >= READY;
  s3.drag = null;
  if (ok) s3Launch(); else s3.mode = 'idle';
}

function s3Update(dt) {
  const q = s3, T = q.torch, k = q.k;
  const posed = trans && trans.kind === 't2';     // the camera move places the torch itself
  if (!posed) {
    if (q.mode === 'aim' && q.drag) {
      const dx = q.drag.dx, dy = q.drag.dy;
      q.aim.p = clamp(-dy / 200, 0, 1);
      q.aim.theta = clamp(rad(50) - dx * rad(.22), rad(14), rad(80));
      T.tx = q.start.x + clamp(dx, -120, 120) * .22;
      T.ty = q.start.y + clamp(dy, -200, 30) * .4;
      T.trot = -q.aim.theta;
    } else if (q.mode === 'idle') {
      T.tx = q.start.x; T.ty = q.start.y + Math.sin(time * 2.2) * 2.5;
      T.trot = -rad(50) + Math.sin(time * 1.7) * .02;
      q.aim.p = 0; q.aim.theta = rad(50);
    }
    if (q.mode === 'idle' || q.mode === 'aim' || q.mode === 'lit') {
      const a = 1 - Math.exp(-(q.mode === 'aim' ? 30 : 10) * dt);
      T.x += (T.tx - T.x) * a; T.y += (T.ty - T.y) * a; T.rot += wrap(T.trot - T.rot) * a;
      if (q.mode !== 'lit') T.flame += (1 - T.flame) * (1 - Math.exp(-3 * dt));
    }
  }
  if (q.mode === 'fly') {
    const gv = q.GW * 3.2, steps = Math.max(1, Math.ceil(dt * 120)), h = dt / steps;
    for (let i = 0; i < steps && q.mode === 'fly'; i++) {
      T.vy += gv * h; T.x += T.vx * h; T.y += T.vy * h; T.rot += T.spin * h;
      if (checkHit()) { s3Ignite(); break; }
      if (T.y >= q.landY) s3GroundHit();
      if (q.mode === 'fly' && (T.x < -80 || T.x > W + 80)) s3MissOffscreen();
    }
  }
  if (q.mode === 'miss') {
    q.missT += dt;
    T.flame *= Math.exp(-1.4 * dt);
    const flat = Math.round(T.rot / Math.PI) * Math.PI + .06;
    T.rot += wrap(flat - T.rot) * (1 - Math.exp(-8 * dt));
    if (q.missT > 2.1) s3ResetTorch();
  }
  if (q.mode === 'lit') {
    q.litT += dt;
    if (q.litT > 2.6 && stage === 2 && !trans) startTrans('t3');
  }
  q.burn += (q.burnTarget - q.burn) * (1 - Math.exp(-dt * (q.burnTarget > q.burn ? 2.2 : 2.8)));
  q.flash *= Math.exp(-3 * dt);

  s3EmitTorch(dt); s3EmitFire(dt); s3UpdateParticles(dt);

  if (stage === 2 && !trans) {
    if (q.mode === 'idle') setHint('Hold the torch, drag to aim, then slide up to throw');
    else if (q.mode === 'aim') setHint(q.aim.p < READY ? 'Slide up to throw' : 'Let go to throw');
    else if (q.mode === 'fly') setHint('');
    else if (q.mode === 'lit') setHint(q.litT > .4 ? 'The pile is burning' : '');
    else if (q.mode === 'miss') setHint(q.missT > .5 ? 'Missed. Try again' : '');
  }
}

function s3DrawLights(g) {
  const q = s3, T = q.torch, GW = q.GW;
  const fl = .86 + .14 * Math.sin(time * 13.1) * Math.sin(time * 7.7) + rnd(-.04, .04);
  g.globalCompositeOperation = 'lighter';
  const I = q.burn * fl + q.flash * .9;
  if (I > .01) {
    const cx = q.pile.cx, cy = q.groundY - q.pile.h * .6, Rr = GW * (.6 + .35 * Math.min(q.burn, 1)) + q.flash * GW * .2;
    let gr = g.createRadialGradient(cx, cy, 0, cx, cy, Rr);
    gr.addColorStop(0, `rgba(255,255,255,${.42 * I})`); gr.addColorStop(.35, `rgba(255,255,255,${.15 * I})`); gr.addColorStop(1, 'rgba(255,255,255,0)');
    g.fillStyle = gr; g.fillRect(cx - Rr, cy - Rr, Rr * 2, Rr * 2);
    g.save(); g.translate(cx, q.groundY + 6); g.scale(1, .3);
    const R2 = Rr * 1.5; gr = g.createRadialGradient(0, 0, 0, 0, 0, R2);
    gr.addColorStop(0, `rgba(255,255,255,${.3 * I})`); gr.addColorStop(1, 'rgba(255,255,255,0)');
    g.fillStyle = gr; g.fillRect(-R2, -R2, R2 * 2, R2 * 2); g.restore();
  }
  if (T.flame > .03) {
    const h = headPos(), Rr = GW * .3, a = .26 * T.flame * (.8 + .2 * Math.sin(time * 19));
    const gr = g.createRadialGradient(h.x, h.y, 0, h.x, h.y, Rr);
    gr.addColorStop(0, `rgba(255,255,255,${a})`); gr.addColorStop(1, 'rgba(255,255,255,0)');
    g.fillStyle = gr; g.fillRect(h.x - Rr, h.y - Rr, Rr * 2, Rr * 2);
  }
  g.globalCompositeOperation = 'source-over';
}
function s3DrawPile(g) {
  const q = s3, pile = q.pile, burn = q.burn;
  const rf = (x, y, w, h, r) => { if (g.roundRect) { g.beginPath(); g.roundRect(x, y, w, h, r); } else rr(g, x, y, w, h, r); g.fill(); };
  g.save(); g.translate(pile.cx, q.groundY + 2); g.scale(1, .18);
  let gr = g.createRadialGradient(0, 0, 0, 0, 0, pile.w * .75);
  gr.addColorStop(0, 'rgba(0,0,0,.75)'); gr.addColorStop(1, 'rgba(0,0,0,0)');
  g.fillStyle = gr; g.beginPath(); g.arc(0, 0, pile.w * .75, 0, TAU); g.fill(); g.restore();
  for (const l of pile.logs) {
    const glow = burn * (.5 + .5 * Math.sin(time * 4 + l.sh * 20)), c = 42 + l.sh * 22 + glow * 55;
    if (l.type === 'side') {
      g.save(); g.translate(l.x, l.y); g.rotate(l.a);
      gr = g.createLinearGradient(0, -l.t / 2, 0, l.t / 2);
      gr.addColorStop(0, gray(c + 26)); gr.addColorStop(.5, gray(c)); gr.addColorStop(1, gray(c - 24));
      g.fillStyle = gr; rf(-l.len / 2, -l.t / 2, l.len, l.t, l.t * .35);
      g.strokeStyle = 'rgba(0,0,0,.3)'; g.lineWidth = 1;
      for (let i = 0; i < 3; i++) {
        const yy = (-.26 + .26 * i) * l.t;
        g.beginPath(); g.moveTo(-l.len * .45, yy); g.quadraticCurveTo(0, yy + (l.sh - .5) * 3, l.len * .45, yy); g.stroke();
      }
      g.fillStyle = gray(c + 34); g.beginPath(); g.ellipse(l.len / 2 - 1, 0, l.t * .13, l.t * .5, 0, 0, TAU); g.fill();
      g.fillStyle = gray(c - 14); g.beginPath(); g.ellipse(-l.len / 2 + 1, 0, l.t * .13, l.t * .5, 0, 0, TAU); g.fill();
      g.restore();
    } else {
      gr = g.createRadialGradient(l.x - l.r * .2, l.y - l.r * .2, 0, l.x, l.y, l.r);
      gr.addColorStop(0, gray(c + 44)); gr.addColorStop(1, gray(c + 8));
      g.fillStyle = gr; g.beginPath(); g.arc(l.x, l.y, l.r, 0, TAU); g.fill();
      g.strokeStyle = 'rgba(0,0,0,.32)'; g.lineWidth = 1;
      g.beginPath(); g.arc(l.x, l.y, l.r * .66, 0, TAU); g.stroke();
      g.beginPath(); g.arc(l.x, l.y, l.r * .33, 0, TAU); g.stroke();
      g.strokeStyle = gray(c - 20); g.lineWidth = 1.5; g.beginPath(); g.arc(l.x, l.y, l.r, 0, TAU); g.stroke();
    }
  }
  if (burn > .02) {
    g.globalCompositeOperation = 'lighter';
    for (const l of pile.logs) {
      const r = (l.t || l.r * 2) * 1.5, a = .2 * burn * (.5 + .5 * Math.sin(time * 5 + l.sh * 30));
      const gg = g.createRadialGradient(l.x, l.y, 0, l.x, l.y, r);
      gg.addColorStop(0, `rgba(255,255,255,${a})`); gg.addColorStop(1, 'rgba(255,255,255,0)');
      g.fillStyle = gg; g.fillRect(l.x - r, l.y - r, r * 2, r * 2);
    }
    g.globalCompositeOperation = 'source-over';
  }
}

// a small bird seen side-on (stage 3) — head to the left
function drawBirdSide(g, x, y, s, c) {
  g.save(); g.translate(x, y);
  g.fillStyle = gray(c - 18);
  g.beginPath(); g.moveTo(s * .22, -s * .02); g.lineTo(s * .55, -s * .12); g.lineTo(s * .55, s * .04); g.closePath(); g.fill();   // tail
  g.fillStyle = gray(c);
  g.beginPath(); g.ellipse(0, 0, s * .3, s * .19, -.12, 0, TAU); g.fill();                                                   // body
  g.beginPath(); g.arc(-s * .27, -s * .14, s * .14, 0, TAU); g.fill();                                                       // head
  g.fillStyle = gray(c + 50);
  g.beginPath(); g.moveTo(-s * .39, -s * .17); g.lineTo(-s * .5, -s * .12); g.lineTo(-s * .39, -s * .1); g.closePath(); g.fill(); // beak
  g.fillStyle = gray(c - 25);
  g.beginPath(); g.ellipse(s * .06, -s * .02, s * .2, s * .1, -.25, 0, TAU); g.fill();                                       // folded wing
  g.restore();
}
function s3DrawIce(g) {
  const q = s3, I = q.ice, s = I.s, T = q.torch, h = headPos();
  const near = T.flame * Math.max(0, 1 - Math.hypot(h.x - I.x, h.y - (I.y - s * .4)) / (q.GW * .45));
  const lk = clamp(.25 + .75 * Math.max(q.burn * .8, near), 0, 1);
  const x = I.x - s / 2, y = I.y - s * .82, w = s, hh = s * .82;
  g.save();
  g.globalAlpha = .7; g.drawImage(SPR.shadow4, I.x - s * .9, I.y - s * .18, s * 1.8, s * .45); g.globalAlpha = 1;
  const gr = g.createLinearGradient(x, y, x + w, y + hh);
  gr.addColorStop(0, `rgba(250,250,250,${.35 + .5 * lk})`); gr.addColorStop(.55, `rgba(200,200,200,${.3 + .45 * lk})`); gr.addColorStop(1, `rgba(140,140,140,${.35 + .4 * lk})`);
  rr(g, x, y, w, hh, s * .14); g.fillStyle = gr; g.fill();
  g.globalAlpha = .8; drawBirdSide(g, I.x, y + hh * .55, s * .62, 40 + 30 * lk); g.globalAlpha = 1;
  g.save(); rr(g, x, y, w, hh, s * .14); g.clip();
  g.fillStyle = `rgba(255,255,255,${.12 + .3 * lk})`;
  g.beginPath(); g.moveTo(x, y + hh * .4); g.lineTo(x + w * .45, y); g.lineTo(x + w * .62, y); g.lineTo(x, y + hh * .62); g.closePath(); g.fill();
  g.restore();
  rr(g, x, y, w, hh, s * .14); g.lineWidth = 1.5; g.strokeStyle = `rgba(255,255,255,${.25 + .55 * lk})`; g.stroke();
  g.restore();
}
function s3DrawSmoke(g) {
  const lit = .35 + .65 * Math.min(1, s3.burn + s3.flash);
  for (const p of parts3) {
    if (p.type !== 1) continue;
    const k = p.life / p.max;
    g.globalAlpha = p.a * Math.sin(Math.PI * k) * lit;
    const s = lerp(p.s0, p.s1, k); g.drawImage(SPR.smoke3, p.x - s, p.y - s, s * 2, s * 2);
  }
  g.globalAlpha = 1;
}
function s3DrawFlames(g) {
  g.globalCompositeOperation = 'lighter';
  for (const p of parts3) {
    if (p.type === 1) continue;
    const k = p.life / p.max;
    if (p.type === 0) {
      const s = lerp(p.s0, p.s1, k), a = p.a * Math.pow(1 - k, 1.2);
      g.globalAlpha = a * .55; g.drawImage(SPR.light3, p.x - s, p.y - s, s * 2, s * 2);
      const s2_ = s * .55; g.globalAlpha = a * .9; g.drawImage(SPR.light3, p.x - s2_, p.y - s2_, s2_ * 2, s2_ * 2);
    } else {
      const a = (1 - k) * (.55 + .45 * Math.sin(time * 40 + p.seed)), s = lerp(p.s0, p.s1, k) * 2.2;
      g.globalAlpha = Math.max(0, a); g.drawImage(SPR.light3, p.x - s, p.y - s, s * 2, s * 2);
    }
  }
  g.globalAlpha = 1; g.globalCompositeOperation = 'source-over';
}
function s3DrawTorchBody(g, alpha) {
  const T = s3.torch, Lt = s3.torchLen, w = Lt * .1;
  const rf = (x, y, ww, hh, r) => { if (g.roundRect) { g.beginPath(); g.roundRect(x, y, ww, hh, r); } else rr(g, x, y, ww, hh, r); g.fill(); };
  g.save(); g.globalAlpha = alpha; g.translate(T.x, T.y); g.rotate(T.rot);
  let gr = g.createLinearGradient(0, -w / 2, 0, w / 2);
  gr.addColorStop(0, '#8c8c8c'); gr.addColorStop(.5, '#5a5a5a'); gr.addColorStop(1, '#2c2c2c');
  g.fillStyle = gr; rf(-Lt / 2, -w / 2, Lt * .78, w, w * .45);
  g.strokeStyle = 'rgba(0,0,0,.4)'; g.lineWidth = 1;
  for (let i = 0; i < 4; i++) { const x = -Lt / 2 + Lt * .1 + i * Lt * .12; g.beginPath(); g.moveTo(x, -w / 2); g.lineTo(x + w * .3, w / 2); g.stroke(); }
  gr = g.createLinearGradient(0, -w, 0, w);
  gr.addColorStop(0, '#5a5a5a'); gr.addColorStop(.55, '#2a2a2a'); gr.addColorStop(1, '#141414');
  g.fillStyle = gr; g.beginPath(); g.ellipse(Lt * .34, 0, Lt * .17, w * 1.15, 0, 0, TAU); g.fill();
  g.strokeStyle = 'rgba(0,0,0,.45)';
  for (let i = 0; i < 3; i++) { const x = Lt * .24 + i * Lt * .09; g.beginPath(); g.moveTo(x, -w * 1.1); g.lineTo(x + w * .25, w * 1.1); g.stroke(); }
  g.globalCompositeOperation = 'lighter';
  g.strokeStyle = `rgba(255,255,255,${.4 * T.flame})`; g.lineWidth = 1.2;
  g.beginPath(); g.ellipse(Lt * .34, 0, Lt * .17, w * 1.15, 0, 0, TAU); g.stroke();
  g.restore();
}
function s3DrawTorchGlow(g) {
  const T = s3.torch, k = s3.k;
  if (T.flame < .03) return;
  const h = headPos(), f = .8 + .2 * Math.sin(time * 17);
  g.globalCompositeOperation = 'lighter';
  let s = 30 * k * T.flame; g.globalAlpha = .55 * f; g.drawImage(SPR.light3, h.x - s, h.y - s, s * 2, s * 2);
  s = 13 * k * T.flame; g.globalAlpha = .8; g.drawImage(SPR.light3, h.x - s, h.y - s, s * 2, s * 2);
  g.globalAlpha = 1; g.globalCompositeOperation = 'source-over';
}
function s3DrawAim(g) {
  const q = s3, k = q.k, th = q.aim.theta, p = q.aim.p, ready = p >= READY, h = headPos();
  const dx = Math.cos(th), dy = -Math.sin(th), gap = 30 * k, len = (24 + p * 66) * k;
  const x0 = h.x + dx * gap, y0 = h.y + dy * gap, x1 = x0 + dx * len, y1 = y0 + dy * len;
  g.save();
  g.lineCap = 'round'; g.lineJoin = 'round'; g.lineWidth = 2.4;
  g.strokeStyle = ready ? 'rgba(255,255,255,.95)' : 'rgba(255,255,255,.5)';
  g.shadowColor = 'rgba(255,255,255,.5)'; g.shadowBlur = ready ? 8 : 0;
  if (!ready) g.setLineDash([3 * k, 6 * k]);
  g.beginPath(); g.moveTo(x0, y0); g.lineTo(x1, y1); g.stroke();
  if (ready) {
    g.setLineDash([]);
    const a = 7 * k, nx = -dy, ny = dx;
    g.beginPath(); g.moveTo(x1 - dx * a + nx * a * .6, y1 - dy * a + ny * a * .6); g.lineTo(x1, y1); g.lineTo(x1 - dx * a - nx * a * .6, y1 - dy * a - ny * a * .6); g.stroke();
  }
  g.restore();
}
function s3DrawIdleCue(g) {
  const T = s3.torch, Lt = s3.torchLen;
  const r = Lt * .62 + Math.sin(time * 2.4) * 3, a = .16 + .1 * Math.sin(time * 2.4);
  const cx = T.x + Math.cos(T.rot) * Lt * .05, cy = T.y + Math.sin(T.rot) * Lt * .05;
  g.strokeStyle = `rgba(255,255,255,${a})`; g.lineWidth = 1.2;
  g.beginPath(); g.arc(cx, cy, r, 0, TAU); g.stroke();
}
// back: everything except the torch, so a camera move can carry the torch on its own
function s3RenderBack(g) {
  g.drawImage(s3.bg, 0, 0, W, H);
  s3DrawLights(g); s3DrawPile(g); s3DrawIce(g); s3DrawSmoke(g);
  const vg = g.createRadialGradient(W / 2, H * .58, Math.min(W, H) * .3, W / 2, H * .58, Math.hypot(W, H) * .62);
  vg.addColorStop(0, 'rgba(0,0,0,0)'); vg.addColorStop(1, 'rgba(0,0,0,.62)');
  g.fillStyle = vg; g.fillRect(0, 0, W, H);
  g.save(); g.globalAlpha = .06; g.globalCompositeOperation = 'overlay';
  g.translate((R() * 128) | 0, (R() * 128) | 0);
  g.fillStyle = grainFor(g); g.fillRect(-128, -128, W + 256, H + 256); g.restore();
}
function s3RenderFront(g, torchAlpha, ui) {
  s3DrawTorchBody(g, torchAlpha); s3DrawFlames(g); s3DrawTorchGlow(g);
  if (ui && s3.mode === 'idle') s3DrawIdleCue(g);
  if (ui && s3.mode === 'aim') s3DrawAim(g);
}

/* ================================================================ 4 · ICE vs. FIRE  (melt the ice, free the bird) */
const FRIC = 1.05, FLAT = 10, STOP = 10, REST = .78, MAXV = 1050, MINV = 150, MAXPULL = 150, MINPULL = 14, DT = 1 / 120, FIRE_R = 44;
const FLAME = 0, SPARK = 1, STEAM = 2, SMOKE = 3;
const s4 = { B: { l: 12, r: 300, t: 76, b: 500 }, state: 'wait', pushes: 0, acc: 0, bird: null, ended: false };
const fire = { x: 0, y: 0, nx: .5, ny: .15, health: 1, acc: 0, sacc: 0, smokeAcc: 0 };
const ice = { x: 0, y: 0, vx: 0, vy: 0, mass: 1, ang: 0, av: 0, inFire: false, gone: false, trail: [], trailAcc: 0, wetAcc: 0, steamAcc: 0 };
let P4 = [], wet = [];
let aim4 = { active: false, id: -1, ax: 0, ay: 0, px: 0, py: 0 };
const floorC = document.createElement('canvas');
const iceSize = () => 24 + 32 * Math.pow(Math.max(ice.mass, 0), .6);
const iceR = () => iceSize() / 2;
const contact4 = (b, r) => Math.hypot(b.x - fire.x, b.y - (fire.y + 6)) < FIRE_R + r * .6;

function s4BuildFloor() {
  floorC.width = Math.round(W * DPR); floorC.height = Math.round(H * DPR);
  const g = floorC.getContext('2d'); g.setTransform(DPR, 0, 0, DPR, 0, 0);
  g.fillStyle = '#121213'; g.fillRect(0, 0, W, H);
  const v = g.createRadialGradient(W / 2, H * .45, Math.min(W, H) * .2, W / 2, H * .5, Math.max(W, H) * .75);
  v.addColorStop(0, 'rgba(44,44,46,.55)'); v.addColorStop(1, 'rgba(0,0,0,.6)');
  g.fillStyle = v; g.fillRect(0, 0, W, H);
  let s = 7; const sr = () => { s = (s * 16807) % 2147483647; return s / 2147483647; };
  const n = Math.round(W * H / 260);
  for (let i = 0; i < n; i++) { g.fillStyle = `rgba(255,255,255,${.015 + sr() * .05})`; g.fillRect(sr() * W, sr() * H, 1 + sr() * 1.2, 1 + sr() * 1.2); }
  g.lineWidth = 1;
  for (let i = 0; i < 16; i++) {
    const x = sr() * W, y = sr() * H, l = 40 + sr() * 140, a = sr() * Math.PI;
    g.strokeStyle = `rgba(255,255,255,${.015 + sr() * .03})`;
    g.beginPath(); g.moveTo(x, y);
    g.quadraticCurveTo(x + Math.cos(a) * l * .5 + sr() * 20, y + Math.sin(a) * l * .5 + sr() * 20, x + Math.cos(a) * l, y + Math.sin(a) * l);
    g.stroke();
  }
}
function s4PlaceFire() {
  const B = s4.B, mg = Math.min(76, (B.r - B.l) / 2 - 1);
  fire.x = B.l + mg + (B.r - B.l - 2 * mg) * fire.nx;
  fire.y = B.t + 112 + Math.max(0, (B.b - B.t) * .26) * fire.ny;
}
function s4SpawnIce() {
  const B = s4.B;
  ice.x = (B.l + B.r) / 2; ice.y = B.b - 54;
  ice.vx = ice.vy = 0; ice.mass = 1; ice.ang = 0; ice.av = 0;
  ice.gone = false; ice.inFire = false; ice.trail = [];
}
function s4Layout() {
  s4.B = { l: 12, r: W - 12, t: 76, b: H - 12 };
  s4PlaceFire();
  const ir = iceR(), B = s4.B;
  ice.x = clamp(ice.x, B.l + ir, B.r - ir); ice.y = clamp(ice.y, B.t + ir, B.b - ir);
  s4BuildFloor();
}

function stepBody(b, dt, r) {
  const B = s4.B, sp = Math.hypot(b.vx, b.vy);
  if (sp > 0) {
    const ns = Math.max(0, sp * Math.exp(-FRIC * dt) - FLAT * dt);
    if (ns < STOP) { b.vx = 0; b.vy = 0; return 0; }
    const k = ns / sp; b.vx *= k; b.vy *= k;
  }
  b.x += b.vx * dt; b.y += b.vy * dt;
  let hit = 0;
  if (b.x < B.l + r) { b.x = B.l + r; if (b.vx < 0) { hit = Math.max(hit, -b.vx); b.vx = -b.vx * REST; } }
  if (b.x > B.r - r) { b.x = B.r - r; if (b.vx > 0) { hit = Math.max(hit, b.vx); b.vx = -b.vx * REST; } }
  if (b.y < B.t + r) { b.y = B.t + r; if (b.vy < 0) { hit = Math.max(hit, -b.vy); b.vy = -b.vy * REST; } }
  if (b.y > B.b - r) { b.y = B.b - r; if (b.vy > 0) { hit = Math.max(hit, b.vy); b.vy = -b.vy * REST; } }
  return hit;
}
// simulates the exact same physics forward to draw the aim line
function predict(vx, vy) {
  const b = { x: ice.x, y: ice.y, vx, vy }, r = iceR(), pts = [{ x: b.x, y: b.y }];
  let hit = false;
  for (let i = 0; i < 1800; i++) {
    stepBody(b, DT, r); pts.push({ x: b.x, y: b.y });
    if (contact4(b, r)) { hit = true; break; }
    if (b.vx === 0 && b.vy === 0) break;
  }
  return { pts, hit };
}
function burst4(x, y, n, kind) {
  for (let i = 0; i < n; i++)
    P4.push({ k: kind, x: x + (R() - .5) * 26, y: y + (R() - .5) * 20, vx: (R() - .5) * 50, vy: -(20 + R() * 70), t: 0, life: 1 + R() * 1.1, s: 9 + R() * 10, g: 14 + R() * 14, seed: R() * 6.28 });
}

function s4Free() {
  s4.state = 'freed';
  ice.gone = true; ice.vx = ice.vy = 0; ice.trail = [];
  burst4(ice.x, ice.y, 16, STEAM);
  s4.bird = { x0: ice.x, y0: ice.y, x: ice.x, y: ice.y, ang: ice.ang, t: 0, wing: 0, sc: 1, alpha: 1 };
  buzz([30, 40, 30]);
  setHint('');
}

function s4Simulate(dt) {
  if (ice.gone) return;
  const r = iceR(), sp0 = Math.hypot(ice.vx, ice.vy);
  const hit = stepBody(ice, dt, r);
  if (hit > 120) ice.av += (R() - .5) * Math.min(hit, 900) / 180;
  ice.ang += ice.av * dt; ice.av *= Math.exp(-2.5 * dt);
  if (sp0 > 30) {
    ice.trailAcc += dt;
    if (ice.trailAcc >= 1 / 60) { ice.trailAcc = 0; ice.trail.push({ x: ice.x, y: ice.y, t: time }); if (ice.trail.length > 90) ice.trail.shift(); }
  }
  if (s4.state === 'play' && contact4(ice, r)) {
    if (!ice.inFire) { ice.inFire = true; ice.vx *= .45; ice.vy *= .45; burst4(ice.x, ice.y, 10, STEAM); buzz(18); }
    const d = Math.exp(-8 * dt); ice.vx *= d; ice.vy *= d;
    // a push that lands settles into the flames, so one good push melts it all the way
    const k = 1 - Math.exp(-3 * dt); ice.x += (fire.x - ice.x) * k; ice.y += (fire.y + 6 - ice.y) * k;
    ice.mass -= .5 * dt;
    // the ice dims the fire, but the fire never goes out
    fire.health = Math.max(.35, fire.health - .42 * dt * (.4 + .6 * Math.max(ice.mass, 0)));
    ice.wetAcc += dt;
    if (ice.wetAcc > .12) { ice.wetAcc = 0; wet.push({ x: ice.x + (R() - .5) * 14, y: ice.y + (R() - .5) * 14, r: 10 + R() * 10, t: 0, life: 4 }); }
    ice.steamAcc += dt * 38;
    while (ice.steamAcc >= 1) {
      ice.steamAcc -= 1;
      P4.push({ k: STEAM, x: ice.x + (R() - .5) * 20, y: ice.y + (R() - .5) * 12, vx: (R() - .5) * 18, vy: -(30 + R() * 40), t: 0, life: .9 + R() * .8, s: 8 + R() * 8, g: 16 + R() * 14, seed: 0 });
    }
    if (ice.mass <= .08) s4Free();
  } else {
    ice.inFire = false;
    fire.health = Math.min(1, fire.health + .04 * dt);
  }
}
function s4Emit(dt) {
  const h = fire.health, sc = .55 + .45 * h;
  fire.acc += dt * (40 + 170 * h);
  while (fire.acc >= 1) {
    fire.acc -= 1;
    P4.push({ k: FLAME, x: fire.x + (R() - .5) * 52 * sc, y: fire.y + 12 + R() * 8, vx: (R() - .5) * 26, vy: -(90 + R() * 120) * sc, t: 0, life: (.45 + R() * .55) * (.6 + .4 * h), s: (18 + R() * 16) * sc, seed: R() * 6.28 });
  }
  fire.sacc += dt * 10 * h;
  while (fire.sacc >= 1) {
    fire.sacc -= 1;
    P4.push({ k: SPARK, x: fire.x + (R() - .5) * 40, y: fire.y, vx: (R() - .5) * 60, vy: -(70 + R() * 150), t: 0, life: .7 + R() * .9, s: 1.2 + R() * 1.6, seed: R() * 6.28 });
  }
  const sr = h < .55 ? (1 - h / .55) * 18 : 0;
  fire.smokeAcc += dt * sr;
  while (fire.smokeAcc >= 1) {
    fire.smokeAcc -= 1;
    P4.push({ k: SMOKE, x: fire.x + (R() - .5) * 40, y: fire.y - 18, vx: (R() - .5) * 16, vy: -(28 + R() * 30), t: 0, life: 1.6 + R() + .6, s: 16, g: 22 + R() * 12, seed: 0 });
  }
}
function s4UpdateParticles(dt) {
  for (let i = P4.length - 1; i >= 0; i--) {
    const p = P4[i]; p.t += dt;
    if (p.t >= p.life) { P4[i] = P4[P4.length - 1]; P4.pop(); continue; }
    p.x += p.vx * dt; p.y += p.vy * dt;
    if (p.k === FLAME) p.vx += Math.sin(time * 7 + p.seed) * 30 * dt;
    else if (p.k === STEAM || p.k === SMOKE) { p.s += p.g * dt; p.vx *= (1 - .6 * dt); }
  }
  for (let i = wet.length - 1; i >= 0; i--) {
    const w = wet[i]; w.t += dt; w.r += 2.5 * dt;
    if (w.t >= w.life) { wet[i] = wet[wet.length - 1]; wet.pop(); }
  }
}
function s4UpdateBird(dt) {
  const b = s4.bird; if (!b) return;
  b.t += dt;
  if (b.t < .7) {                               // shakes the water off
    const k = 1 - b.t / .7;
    b.x = b.x0 + (reduce ? 0 : Math.sin(b.t * 70) * 2.4 * k);
    b.ang += wrap(0 - b.ang) * (1 - Math.exp(-dt * 6));
    b.wing = .15 * (.5 + .5 * Math.sin(b.t * 40));
    if (R() < dt * 30) P4.push({ k: STEAM, x: b.x + (R() - .5) * 18, y: b.y + (R() - .5) * 18, vx: (R() - .5) * 90, vy: (R() - .5) * 90, t: 0, life: .4 + R() * .3, s: 2 + R() * 3, g: 4, seed: 0 });
  } else {                                      // and flies up toward you, out of the frame
    const p = (b.t - .7) / 1.9;
    b.ang += wrap(0 - b.ang) * (1 - Math.exp(-dt * 6));
    b.wing = .5 + .5 * Math.sin(b.t * 24);
    b.y = b.y0 - H * .85 * p * p;
    b.x = b.x0 + Math.sin(p * 3) * 26;
    b.sc = 1 + 1.7 * p;
    b.alpha = 1 - smooth(.6, 1, p);
  }
  if (b.t > 3.3 && !s4.ended) { s4.ended = true; showEnd(); }
}
function s4Update(dt) {
  s4.acc += dt;
  let n = 0;
  while (s4.acc >= DT && n < 8) { s4Simulate(DT); s4.acc -= DT; n++; }
  if (n === 8) s4.acc = 0;
  s4Emit(dt); s4UpdateParticles(dt); s4UpdateBird(dt);
}

// a small bird seen from above, facing up; wing 0 = folded, 1 = spread
function drawBirdTop(g, s, wing, c) {
  const span = s * (.36 + .62 * wing);
  g.fillStyle = gray(c - 14);
  for (const sd of [-1, 1]) {
    g.beginPath();
    g.moveTo(sd * s * .1, -s * .14);
    g.quadraticCurveTo(sd * span, -s * (.04 + .26 * wing), sd * span * .92, s * (.12 - .04 * wing));
    g.quadraticCurveTo(sd * span * .45, s * .2, sd * s * .1, s * .12);
    g.closePath(); g.fill();
  }
  g.fillStyle = gray(c - 24);
  g.beginPath(); g.moveTo(-s * .08, s * .24); g.lineTo(-s * .17, s * .55); g.lineTo(s * .17, s * .55); g.lineTo(s * .08, s * .24); g.closePath(); g.fill();
  g.fillStyle = gray(c);
  g.beginPath(); g.ellipse(0, 0, s * .16, s * .31, 0, 0, TAU); g.fill();
  g.fillStyle = gray(c + 10);
  g.beginPath(); g.arc(0, -s * .33, s * .13, 0, TAU); g.fill();
  g.fillStyle = gray(c + 70);
  g.beginPath(); g.moveTo(0, -s * .56); g.lineTo(-s * .045, -s * .43); g.lineTo(s * .045, -s * .43); g.closePath(); g.fill();
}

const LOGS4 = [
  { x: 0, y: 30, a: -0.04, l: 124, t: 20 },
  { x: 2, y: 18, a: 0.07, l: 112, t: 19 },
  { x: -16, y: 8, a: -0.5, l: 104, t: 18 },
  { x: 16, y: 6, a: 0.52, l: 104, t: 18 }
];
function s4DrawLog(g, o) {
  const h = fire.health, b = .42 + .58 * h;
  const v = n => gray(n * b), hl = o.l / 2, ht = o.t / 2;
  g.save(); g.translate(fire.x + o.x, fire.y + o.y); g.rotate(o.a);
  const gr = g.createLinearGradient(0, -ht, 0, ht);
  gr.addColorStop(0, v(128)); gr.addColorStop(.5, v(82)); gr.addColorStop(1, v(32));
  rr(g, -hl, -ht, o.l, o.t, ht * .7); g.fillStyle = gr; g.fill();
  g.strokeStyle = 'rgba(0,0,0,.3)'; g.lineWidth = 1;
  for (let k = 0; k < 4; k++) {
    const y = -ht * .6 + k * ht * .42, x0 = -hl * .8 + ((k * 37) % 22);
    g.beginPath(); g.moveTo(x0, y); g.lineTo(x0 + 24 + ((k * 13) % 22), y); g.stroke();
  }
  g.globalCompositeOperation = 'lighter';
  g.fillStyle = `rgba(255,255,255,${.16 * h})`; rr(g, -hl, -ht, o.l, o.t, ht * .7); g.fill();
  g.globalCompositeOperation = 'source-over';
  for (const sx of [-1, 1]) {
    g.beginPath(); g.ellipse(sx * hl, 0, ht * .45, ht, 0, 0, TAU); g.fillStyle = v(158); g.fill();
    g.strokeStyle = 'rgba(0,0,0,.35)'; g.stroke();
    g.beginPath(); g.ellipse(sx * hl, 0, ht * .24, ht * .52, 0, 0, TAU); g.strokeStyle = 'rgba(0,0,0,.3)'; g.stroke();
  }
  g.restore();
}
// the torch you threw, lying in the pile with its head in the fire
function s4DrawTorch(g) {
  const h = fire.health, Lt = 82, w = 8;
  g.save(); g.translate(fire.x + 10, fire.y + 12); g.rotate(.62);
  const gr = g.createLinearGradient(0, -w / 2, 0, w / 2);
  gr.addColorStop(0, gray(70 + 50 * h)); gr.addColorStop(.5, gray(48 + 30 * h)); gr.addColorStop(1, gray(22));
  rr(g, 0, -w / 2, Lt, w, w * .45); g.fillStyle = gr; g.fill();
  g.strokeStyle = 'rgba(0,0,0,.4)'; g.lineWidth = 1;
  for (let i = 0; i < 4; i++) { const x = Lt * .3 + i * Lt * .14; g.beginPath(); g.moveTo(x, -w / 2); g.lineTo(x + w * .3, w / 2); g.stroke(); }
  g.fillStyle = gray(30); g.beginPath(); g.ellipse(2, 0, 14, w * 1.2, 0, 0, TAU); g.fill();
  g.restore();
}
function s4DrawWood(g) {
  g.globalAlpha = .85; g.drawImage(SPR.shadow4, fire.x - 100, fire.y + 28, 200, 40); g.globalAlpha = 1;
  for (const o of LOGS4) s4DrawLog(g, o);
  s4DrawTorch(g);
}
function s4DrawIce(g) {
  if (ice.gone) return;
  const s = iceSize(), r = s * .2;
  g.save(); g.translate(ice.x, ice.y);
  g.globalAlpha = .8; g.drawImage(SPR.shadow4, -s * .85, s * .18, s * 1.7, s * .8); g.globalAlpha = 1;
  g.rotate(ice.ang);
  const gr = g.createLinearGradient(-s / 2, -s / 2, s / 2, s / 2);
  gr.addColorStop(0, 'rgba(252,252,252,.97)'); gr.addColorStop(.55, 'rgba(206,206,206,.93)'); gr.addColorStop(1, 'rgba(148,148,148,.95)');
  rr(g, -s / 2, -s / 2, s, s, r); g.fillStyle = gr; g.fill();
  // the bird inside, showing through more as the ice thins
  g.globalAlpha = .55 + .35 * (1 - Math.max(ice.mass, 0)); drawBirdTop(g, 26, 0, 60); g.globalAlpha = 1;
  const g2 = g.createLinearGradient(0, -s / 2, 0, s / 2);
  g2.addColorStop(0, 'rgba(255,255,255,.30)'); g2.addColorStop(1, 'rgba(110,110,110,.14)');
  rr(g, -s * .4, -s * .4, s * .8, s * .8, r * .7); g.fillStyle = g2; g.fill();
  g.save(); rr(g, -s / 2, -s / 2, s, s, r); g.clip();
  g.fillStyle = 'rgba(255,255,255,.34)';
  g.beginPath(); g.moveTo(-s * .5, -s * .02); g.lineTo(-s * .02, -s * .5); g.lineTo(s * .14, -s * .5); g.lineTo(-s * .5, s * .14); g.closePath(); g.fill();
  g.fillStyle = 'rgba(255,255,255,.18)';
  g.beginPath(); g.moveTo(-s * .5, s * .26); g.lineTo(s * .26, -s * .5); g.lineTo(s * .32, -s * .5); g.lineTo(-s * .5, s * .32); g.closePath(); g.fill();
  g.restore();
  g.strokeStyle = 'rgba(255,255,255,.45)'; g.lineWidth = 1;
  for (const [bx, by, br] of [[.28, -.2, .04], [.18, -.32, .025], [-.2, .24, .035]]) { g.beginPath(); g.arc(bx * s, by * s, br * s, 0, TAU); g.stroke(); }
  rr(g, -s / 2, -s / 2, s, s, r); g.lineWidth = 1.5; g.strokeStyle = 'rgba(255,255,255,.8)'; g.stroke();
  g.restore();
}
function dotsAlong(pts, spacing) {
  const out = []; let acc = 0, px = pts[0].x, py = pts[0].y;
  for (let i = 1; i < pts.length; i++) {
    const q = pts[i]; let d = Math.hypot(q.x - px, q.y - py);
    while (d > 0 && acc + d >= spacing) {
      const t = (spacing - acc) / d;
      px += (q.x - px) * t; py += (q.y - py) * t; out.push({ x: px, y: py });
      d = Math.hypot(q.x - px, q.y - py); acc = 0;
    }
    acc += d; px = q.x; py = q.y;
  }
  return out;
}
function s4DrawAim(g) {
  if (!aim4.active) return;
  const dx = aim4.ax - aim4.px, dy = aim4.ay - aim4.py, len = Math.hypot(dx, dy);
  const cl = Math.min(len, MAXPULL), power = cl / MAXPULL;
  const ux = len ? dx / len : 0, uy = len ? dy / len : 0;
  const hx = aim4.ax - ux * cl, hy = aim4.ay - uy * cl, r = iceR();
  g.save(); g.lineCap = 'round';
  // rubber band from where you touched to your finger
  g.strokeStyle = 'rgba(255,255,255,.28)'; g.lineWidth = 1.5;
  g.beginPath(); g.moveTo(aim4.ax, aim4.ay); g.lineTo(hx, hy); g.stroke();
  g.beginPath(); g.arc(aim4.ax, aim4.ay, 9, 0, TAU); g.strokeStyle = 'rgba(255,255,255,.4)'; g.stroke();
  g.beginPath(); g.arc(hx, hy, 15, 0, TAU); g.fillStyle = 'rgba(255,255,255,.12)'; g.fill();
  g.strokeStyle = 'rgba(255,255,255,.65)'; g.stroke();
  if (len >= MINPULL) {
    const v0 = MINV + (MAXV - MINV) * power, pred = predict(ux * v0, uy * v0);
    const dots = dotsAlong(pred.pts, 18).slice(0, 90), n = dots.length;
    for (let i = 0; i < n; i++) {
      const d = dots[i];
      if (Math.hypot(d.x - ice.x, d.y - ice.y) < r + 8) continue;
      const f = i / Math.max(1, n);
      g.globalAlpha = .95 - f * .7;
      g.beginPath(); g.arc(d.x, d.y, 3.4 - f * 1.6, 0, TAU); g.fillStyle = '#fff'; g.fill();
    }
    g.globalAlpha = 1;
    const end = pred.pts[pred.pts.length - 1];
    if (pred.hit) {
      const pr = FIRE_R + 12 + Math.sin(time * 8) * 2.5;
      g.setLineDash([7, 7]); g.lineDashOffset = -time * 24;
      g.lineWidth = 2; g.strokeStyle = 'rgba(255,255,255,.9)';
      g.beginPath(); g.arc(fire.x, fire.y + 6, pr, 0, TAU); g.stroke(); g.setLineDash([]);
    } else {
      const s = iceSize();
      g.save(); g.translate(end.x, end.y);
      g.setLineDash([5, 5]); g.lineWidth = 1.5; g.strokeStyle = 'rgba(255,255,255,.45)';
      rr(g, -s / 2, -s / 2, s, s, s * .2); g.stroke(); g.restore();
    }
    g.setLineDash([]); g.lineWidth = 2.5;
    g.strokeStyle = 'rgba(255,255,255,.14)'; g.beginPath(); g.arc(ice.x, ice.y, r + 12, 0, TAU); g.stroke();
    g.strokeStyle = 'rgba(255,255,255,.9)'; g.beginPath(); g.arc(ice.x, ice.y, r + 12, -Math.PI / 2, -Math.PI / 2 + power * TAU); g.stroke();
  }
  g.restore();
}
function s4DrawParticles(g) {
  g.globalCompositeOperation = 'lighter';
  for (const p of P4) {
    const k = 1 - p.t / p.life;
    if (p.k === FLAME) {
      const s = p.s * (.3 + .7 * k), w = s * 2.1, h = s * 2.9;
      g.globalAlpha = Math.min(1, .34 * k + .04); g.drawImage(SPR.white4, p.x - w / 2, p.y - h * .55, w, h);
    } else if (p.k === SPARK) {
      g.globalAlpha = k * (.6 + .4 * Math.sin(time * 40 + p.seed)); g.fillStyle = '#fff'; g.fillRect(p.x - p.s / 2, p.y - p.s / 2, p.s, p.s);
    }
  }
  g.globalCompositeOperation = 'source-over';
  for (const p of P4) {
    const k = 1 - p.t / p.life;
    if (p.k === STEAM) { g.globalAlpha = .3 * k; g.drawImage(SPR.white4, p.x - p.s, p.y - p.s, p.s * 2, p.s * 2); }
    else if (p.k === SMOKE) { g.globalAlpha = .34 * k; g.drawImage(SPR.smoke4, p.x - p.s, p.y - p.s, p.s * 2, p.s * 2); }
  }
  g.globalAlpha = 1;
}
function s4DrawBird(g) {
  const b = s4.bird; if (!b || b.alpha <= .01) return;
  g.save(); g.translate(b.x, b.y); g.rotate(b.ang); g.scale(b.sc, b.sc); g.globalAlpha = b.alpha;
  drawBirdTop(g, 30, b.wing, 92);
  g.restore();
}
function s4Render(g) {
  const B = s4.B, h = fire.health;
  g.globalAlpha = 1; g.globalCompositeOperation = 'source-over'; g.setLineDash([]);
  g.drawImage(floorC, 0, 0, W, H);
  g.beginPath(); g.rect(0, 0, W, H);
  { const x = B.l, y = B.t, w = B.r - B.l, hh = B.b - B.t, r = 20;
    g.moveTo(x + r, y); g.arcTo(x + w, y, x + w, y + hh, r); g.arcTo(x + w, y + hh, x, y + hh, r); g.arcTo(x, y + hh, x, y, r); g.arcTo(x, y, x + w, y, r); g.closePath(); }
  g.fillStyle = 'rgba(0,0,0,.4)'; g.fill('evenodd');
  rr(g, B.l, B.t, B.r - B.l, B.b - B.t, 20); g.lineWidth = 1; g.strokeStyle = 'rgba(255,255,255,.14)'; g.stroke();
  // the fire lights the floor
  { const fl = 1 + .05 * Math.sin(time * 17) + .03 * Math.sin(time * 29), Rr = 330 * (.5 + .5 * h) * fl;
    const gr = g.createRadialGradient(fire.x, fire.y, 0, fire.x, fire.y, Rr);
    gr.addColorStop(0, `rgba(255,255,255,${.22 * h})`); gr.addColorStop(1, 'rgba(255,255,255,0)');
    g.globalCompositeOperation = 'lighter'; g.fillStyle = gr; g.fillRect(0, 0, W, H); g.globalCompositeOperation = 'source-over'; }
  for (const w of wet) {
    const k = 1 - w.t / w.life;
    g.globalAlpha = .12 * k; g.fillStyle = '#fff';
    g.beginPath(); g.ellipse(w.x, w.y, w.r, w.r * .7, 0, 0, TAU); g.fill();
  }
  g.globalAlpha = 1;
  while (ice.trail.length && time - ice.trail[0].t > 1.2) ice.trail.shift();
  g.lineCap = 'round';
  for (let i = 1; i < ice.trail.length; i++) {
    const a = 1 - (time - ice.trail[i].t) / 1.2;
    if (a <= 0) continue;
    g.strokeStyle = `rgba(255,255,255,${.1 * a})`; g.lineWidth = iceSize() * .55 * a;
    g.beginPath(); g.moveTo(ice.trail[i - 1].x, ice.trail[i - 1].y); g.lineTo(ice.trail[i].x, ice.trail[i].y); g.stroke();
  }
  const behind = ice.y < fire.y + 6;
  if (behind) s4DrawIce(g);
  s4DrawWood(g);
  if (!behind) s4DrawIce(g);
  { const s = 140 * (.5 + .5 * h);
    g.globalCompositeOperation = 'lighter'; g.globalAlpha = .5 * h;
    g.drawImage(SPR.white4, fire.x - s, fire.y + 12 - s * .5, s * 2, s);
    g.globalCompositeOperation = 'source-over'; g.globalAlpha = 1; }
  s4DrawParticles(g);
  s4DrawBird(g);
  if (stage === 3 && !trans) s4DrawAim(g);
}

const canAim = () => stage === 3 && !trans && s4.state === 'play' && !ice.gone && ice.vx === 0 && ice.vy === 0;
function s4Down() {
  if (aim4.active || !canAim()) return;
  aim4 = { active: true, id: ptr.id, ax: ptr.x, ay: ptr.y, px: ptr.x, py: ptr.y };
}
function s4Move() { if (aim4.active) { aim4.px = ptr.x; aim4.py = ptr.y; } }
function s4Up(cancel) {
  if (!aim4.active) return;
  const dx = aim4.ax - aim4.px, dy = aim4.ay - aim4.py, len = Math.hypot(dx, dy);
  aim4.active = false;
  if (cancel || len < MINPULL || !canAim()) return;
  const power = Math.min(len, MAXPULL) / MAXPULL, v0 = MINV + (MAXV - MINV) * power;
  ice.vx = dx / len * v0; ice.vy = dy / len * v0;
  s4.pushes++; buzz(10);
  setHint('');
  for (let i = 0; i < 5; i++)
    P4.push({ k: STEAM, x: ice.x - dx / len * 18 + (R() - .5) * 16, y: ice.y - dy / len * 18 + (R() - .5) * 16, vx: -dx / len * 20 * R(), vy: -dy / len * 20 * R(), t: 0, life: .5 + R() * .4, s: 6 + R() * 5, g: 14, seed: 0 });
}

/* ================================================================ camera moves between stages */
const TRANS_DUR = { t1: 1.9, t2: 2.4, t3: 2.3, reset: 1.4 };
function startTrans(kind) {
  if (trans) return;
  trans = { kind, t: 0, dur: TRANS_DUR[kind], done: false };
  if (kind === 't1') {
    trans.from = { x: m.hx, y: m.hy, a: m.a };
    trans.to = { x: W * .5, y: H * .80, a: Math.PI - .12 };
    ptr.down = false; auto = null;
    updateScrape(1, 0);
    setHint('');
  } else if (kind === 't2') {
    const T = s2.torch;
    s2.emit = false;
    setGain(fireBed, 0, .6); setGain(heatGain, 0, .1);
    trans.anchor2 = { x: T.x, y: T.headTop - T.lift + T.headH * .45 };
    trans.r = s3.torchLen / (s2.S * .88);
    s3.mode = 'idle'; s3.torch.flame = 1;
    setHint('', false);
  } else if (kind === 't3') {
    fire.health = clamp(s3.burn, .6, 1);
    s4.state = 'wait';
    setHint('');
  } else if (kind === 'reset') {
    endEl.classList.remove('show');
  }
}
function finishTrans(kind) {
  if (kind === 't1') {
    stage = 1; s2.tx = m.hx; s2.ty = m.hy; s2.tilt = .12; s2.speedS = 0;
  } else if (kind === 't2') {
    stage = 2; matchFade = 0;
    if (matchHiss) matchHiss.gain.value = 0;
    const T = s3.torch; T.rot = T.trot = -rad(50); T.x = T.tx = s3.start.x; T.y = T.ty = s3.start.y;
  } else if (kind === 't3') {
    stage = 3; s4.state = 'play';
    setHint('Drag back to aim, let go to push');
  }
  cv.setAttribute('aria-label', LABELS[stage]);
}

// S3: the head position at the end of the move; torch pose at progress e keeps that head fixed
function t2Pose(e) {
  const Lt = s3.torchLen, a1 = -rad(50);
  const H3 = { x: s3.start.x + Math.cos(a1) * Lt * .5, y: s3.start.y + Math.sin(a1) * Lt * .5 };
  const rot = lerp(-Math.PI / 2, a1, e);
  return { H3, rot, cx: H3.x - Math.cos(rot) * Lt * .5, cy: H3.y - Math.sin(rot) * Lt * .5 };
}

function updateTrans(dt) {
  trans.t += dt;
  const p = clamp(trans.t / trans.dur, 0, 1), e = ease(p);
  if (trans.kind === 't1') {
    const ox = m.hx, oy = m.hy;
    m.hx = lerp(trans.from.x, trans.to.x, e); m.hy = lerp(trans.from.y, trans.to.y, e);
    m.a = lerp(trans.from.a, trans.to.a, e);
    trackHead(dt, ox, oy);
    updateMatchFlame(dt, time); updateMatchParticles(dt);
    s1UpdateLight(dt, 0, H * e);
    flash = Math.max(0, flash - dt * 4.5);
  } else if (trans.kind === 't2') {
    const P = t2Pose(e), T = s3.torch;
    T.rot = T.trot = P.rot; T.x = T.tx = P.cx; T.y = T.ty = P.cy;
    matchFade = 1 - e;
  } else if (trans.kind === 'reset') {
    if (!trans.done && p >= .5) { trans.done = true; resetAll(); }
  }
  if (p >= 1) { const k = trans.kind; trans = null; if (k !== 'reset') finishTrans(k); }
}

function clearLayer(g, c) { g.setTransform(1, 0, 0, 1, 0, 0); g.globalAlpha = 1; g.globalCompositeOperation = 'source-over'; g.clearRect(0, 0, c.width, c.height); g.setTransform(DPR, 0, 0, DPR, 0, 0); }

function renderTrans() {
  const p = clamp(trans.t / trans.dur, 0, 1), e = ease(p);
  ctx.fillStyle = '#000'; ctx.fillRect(0, 0, W, H);
  if (trans.kind === 't1') {
    // the camera tilts up from the matchbox to the wall; the match stays in your hand
    const off = H * e, fp = flamePoint();
    clearLayer(gA, layerA); s1Render(gA, false);
    clearLayer(gB, layerB); s2Render(gB, { match: false, matchLight: { x: fp.x, y: fp.y + H * (1 - e) }, torch: true });
    ctx.drawImage(layerA, 0, off, W, H);
    ctx.drawImage(layerB, 0, off - H, W, H);
    drawMatchLayer(ctx, time, 0);
  } else if (trans.kind === 't2') {
    // the camera pulls back from the wall to the field; the torch turns into your hand
    const a2 = trans.anchor2, r = trans.r, P = t2Pose(e);
    const sx = lerp(a2.x, P.H3.x, e), sy = lerp(a2.y, P.H3.y, e);
    const sA = lerp(1, r, e), sB = sA / r, q = smooth(.15, .75, e), q2 = smooth(.3, .8, e);
    clearLayer(gA, layerA); s2Render(gA, { match: true, matchLight: flamePoint(), torch: false });
    clearLayer(gB, layerB); s3RenderBack(gB);
    ctx.save(); ctx.translate(sx, sy); ctx.scale(sA, sA); ctx.translate(-a2.x, -a2.y); ctx.drawImage(layerA, 0, 0, W, H); ctx.restore();
    ctx.save(); ctx.globalAlpha = q; ctx.translate(sx, sy); ctx.scale(sB, sB); ctx.translate(-P.H3.x, -P.H3.y); ctx.drawImage(layerB, 0, 0, W, H); ctx.restore();
    if (q2 < 1) {
      ctx.save(); ctx.globalAlpha = 1 - q2;
      ctx.translate(sx, sy); ctx.rotate(P.rot + Math.PI / 2); ctx.scale(sA, sA); ctx.translate(-a2.x, -a2.y);
      s2DrawTorch(ctx, s2.torch.lift); ctx.restore();
    }
    ctx.save(); ctx.translate(sx, sy); ctx.scale(sB, sB); ctx.translate(-P.H3.x, -P.H3.y);
    s3RenderFront(ctx, q2, false); ctx.restore();
    ctx.globalAlpha = 1;
  } else if (trans.kind === 't3') {
    // the camera rises overhead: the same pile, now seen from above
    const P3 = { x: s3.pile.cx, y: s3.groundY - s3.pile.h * .5 }, P4p = { x: fire.x, y: fire.y };
    const cx = lerp(P3.x, P4p.x, e), cy = lerp(P3.y, P4p.y, e), q = smooth(.2, .8, e);
    clearLayer(gA, layerA); s3RenderBack(gA); s3RenderFront(gA, 1, false);
    clearLayer(gB, layerB); s4Render(gB);
    ctx.save(); ctx.translate(cx, cy); ctx.scale(lerp(1, .9, e), lerp(1, .3, e)); ctx.translate(-P3.x, -P3.y); ctx.drawImage(layerA, 0, 0, W, H); ctx.restore();
    ctx.save(); ctx.globalAlpha = q; ctx.translate(cx, cy); ctx.scale(lerp(1.15, 1, e), lerp(2.6, 1, e)); ctx.translate(-P4p.x, -P4p.y); ctx.drawImage(layerB, 0, 0, W, H); ctx.restore();
  }
}

function renderStage(g) {
  if (stage === 0) s1Render(g, true);
  else if (stage === 1) s2Render(g, { match: true, matchLight: m.state === 'lit' ? flamePoint() : null, torch: true });
  else if (stage === 2) { s3RenderBack(g); s3RenderFront(g, 1, true); }
  else s4Render(g);
}

/* ================================================================ ending & reset */
function showEnd() {
  endEl.classList.add('show');
  setTimeout(() => { try { againBtn.focus({ preventScroll: true }); } catch (_) {} }, 200);
}
againBtn.addEventListener('click', () => { initAudio(); startTrans('reset'); });

function resetAll() {
  stage = 0;
  // 1
  m = blankMatch(); s1Layout(); restPose();
  L.x = m.hx; L.y = m.hy; L.I = 0; L.R = 10; hv.x = hv.y = 0;
  sparks.length = 0; smoke.length = 0; auto = null; flash = 0; s1LitT = 0; matchFade = 1; wasContact = false;
  // 2
  Object.assign(s2.torch, { lit: false, lift: 0 });
  Object.assign(s2, { heat: 0, litAmt: 0, litTime: 0, flare: 0, speedS: 0, near: false, indA: 1, vx: 0, vy: 0, tilt: .12, lean: 0, emit: true, crackT: 0 });
  TF.length = 0; SP.length = 0; SM.length = 0;
  // 3
  Object.assign(s3, { mode: 'idle', drag: null, burn: 0, burnTarget: 0, flash: 0, litT: 0, missT: 0 });
  Object.assign(s3.torch, { x: s3.start.x, y: s3.start.y, tx: s3.start.x, ty: s3.start.y, rot: -rad(50), trot: -rad(50), vx: 0, vy: 0, spin: 0, flame: 1 });
  parts3.length = 0;
  // 4
  Object.assign(s4, { state: 'wait', pushes: 0, acc: 0, bird: null, ended: false });
  fire.health = 1; P4 = []; wet = []; aim4.active = false;
  s4SpawnIce();
  // sound
  if (A.c) {
    for (const n of [fireBed, heatGain, roarGain, torchGain]) n.gain.cancelScheduledValues(A.c.currentTime);
    setGain(fireBed, 0, .2); setGain(heatGain, 0, .1); setGain(roarGain, 0, .2); setGain(torchGain, 0, .2);
    matchHiss.gain.value = 0;
  }
  hintText = null; setHint('Drag the match fast across the strip');
  cv.setAttribute('aria-label', LABELS[0]);
}

/* ================================================================ input */
function localPos(e) { const r = cv.getBoundingClientRect(); return { x: e.clientX - r.left, y: e.clientY - r.top }; }
cv.addEventListener('pointerdown', e => {
  if (e.pointerType === 'mouse' && e.button !== 0) return;
  e.preventDefault();
  initAudio();
  if (ptr.down && ptr.id !== e.pointerId) return;      // one finger at a time
  try { cv.setPointerCapture(e.pointerId); } catch (_) {}
  const p = localPos(e);
  ptr.down = true; ptr.id = e.pointerId; ptr.x = ptr.lx = p.x; ptr.y = ptr.ly = p.y; ptr.vx = ptr.vy = 0;
  if (trans) return;
  if (stage === 0) s1Down();
  else if (stage === 2) s3Down();
  else if (stage === 3) s4Down();
});
cv.addEventListener('pointermove', e => {
  if (!ptr.down || e.pointerId !== ptr.id) return;
  if (stage === 0 && auto) return;
  e.preventDefault();
  const p = localPos(e); ptr.x = p.x; ptr.y = p.y;
  if (trans) return;
  if (stage === 2) s3Move();
  else if (stage === 3) s4Move();
});
function release(e, cancel) {
  if (e.pointerId !== ptr.id || (stage === 0 && auto)) return;
  ptr.down = false;
  if (trans) { s3.drag = null; aim4.active = false; return; }
  if (stage === 2) s3Up(cancel);
  else if (stage === 3) s4Up(cancel);
}
cv.addEventListener('pointerup', e => release(e, false));
cv.addEventListener('pointercancel', e => release(e, true));
cv.addEventListener('contextmenu', e => e.preventDefault());
document.addEventListener('touchmove', e => { if (e.target === cv) e.preventDefault(); }, { passive: false });

/* ================================================================ layout & loop */
function resize() {
  const r = cv.getBoundingClientRect();
  const nW = Math.max(200, r.width), nH = Math.max(300, r.height), nD = Math.min(window.devicePixelRatio || 1, 2);
  if (nW === W && nH === H && nD === DPR) return;
  W = nW; H = nH; DPR = nD;
  for (const c of [cv, layerA, layerB]) { c.width = Math.round(W * DPR); c.height = Math.round(H * DPR); }
  grainPat.clear();
  s1Layout(); s2Layout(); s3Layout(); s4Layout();
}

function update(dt) {
  if (trans) updateTrans(dt);
  if (stage === 0 && !trans) s1Update(dt, time);
  if (stage === 1) s2Update(dt, time);
  if (stage === 2 || (trans && trans.kind === 't2')) s3Update(dt);
  if (stage === 3 || (trans && trans.kind === 't3')) s4Update(dt);

  // continuous fire and torch sound across stages 2 to 4
  if (A.c) {
    const tk = trans && trans.kind;
    const level = stage === 3 ? fire.health : stage === 2 ? s3.burn : 0;
    fireAudio(dt, level);
    let tv = 0;
    if (stage === 2) tv = (s3.mode === 'lit' ? .35 : 1) * s3.torch.flame;
    if (tk === 't2') tv = smooth(.2, .9, trans.t / trans.dur) * s3.torch.flame;
    if (tk === 't3') tv *= 1 - clamp(trans.t / trans.dur, 0, 1);
    setGain(torchGain, .05 * tv, .1);
    if (stage === 0 && !trans) setGain(heatGain, 0, .1);
  }
}

function render() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
  if (trans && trans.kind !== 'reset') renderTrans();
  else renderStage(ctx);
  if (trans && trans.kind === 'reset') {
    const p = trans.t / trans.dur, a = p < .5 ? smooth(0, .5, p) : 1 - smooth(.5, 1, p);
    ctx.fillStyle = `rgba(0,0,0,${a})`; ctx.fillRect(0, 0, W, H);
  }
}

// boot
const ro = new ResizeObserver(() => resize());
ro.observe(document.body);
window.addEventListener('orientationchange', () => setTimeout(resize, 200));
resize();
resetAll();
let last = performance.now();
function frame(now) {
  const dt = clamp((now - last) / 1000, .001, .05); last = now;
  time += dt;
  update(dt); render();
  requestAnimationFrame(frame);
}
requestAnimationFrame(frame);

// a small handle for automated checks; not used by the experience itself
window.__thaw = { get stage() { return stage; }, get trans() { return trans && trans.kind; },
  get match() { return m; }, s2, s3, fire, ice, s4 };
})();
