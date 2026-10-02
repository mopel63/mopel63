/* ============================================================
   Soundscape Sculptor — процедурный эмбиент-генератор
   Canvas 2D + Web Audio, ноль сетевых запросов, ноль mp3.
   ============================================================ */
'use strict';

/* ---------- Утилиты ---------- */
const $ = (id) => document.getElementById(id);
const rand = (a, b) => a + Math.random() * (b - a);
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const lerp = (a, b, t) => a + (b - a) * t;
const TAU = Math.PI * 2;

const REDUCED = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;
const DRIFT = REDUCED ? 0.25 : 1;
const MAX_SHAPES = 24;
const LINK_DIST = 180;
const HIT_DIST = 24;

/* Пентатоника (ля-минор): A C D E G через октавы */
const PENTA = [110, 130.81, 146.83, 164.81, 196, 220, 261.63, 293.66, 329.63, 392, 440, 523.25, 587.33, 659.25, 784];
const pickPenta = () => PENTA[(Math.random() * PENTA.length) | 0];

/* X -> панорама, Y -> срез фильтра */
function xToPan(x, w) { return clamp((x / w) * 2 - 1, -1, 1); }
function yToCutoff(y, h) {
  const t = clamp(1 - y / h, 0, 1);           // верх = открыто
  return Math.round(lerp(300, 8000, Math.pow(t, 1.4)));
}
function yToOrbFreq(y, h) {
  const t = clamp(1 - y / h, 0, 1);
  return lerp(40, 80, t);
}

/* ---------- Состояние ---------- */
const canvas = $('stage');
const ctx = canvas.getContext('2d');
const waveCanvas = $('wave');
const waveCtx = waveCanvas.getContext('2d');
let W = 0, H = 0, DPR = 1;

let shapes = [];          // {id,type,x,y,vx,vy,r,hue,sides,rot,vr,flash,nextChime,audio}
let pairPads = new Map(); // "idA|idB" -> {osc1,osc2,gain,filter}
let nextId = 1;
let gravityOn = false;
let soundOn = false;      // AudioContext запущен и не на паузе
let muted = false;
let startedOnce = false;

/* Свои звуки: закэшированные AudioBuffer'ы (key -> AudioBuffer + имя) */
const sampleBuffers = new Map();
let sampleSeq = 1;
const MAX_FILE_MB = 20;

/* ---------- Аудио-ядро ---------- */
let AC = null, master = null, analyser = null, analyserData = null, streamDest = null;
let noiseBuffer = null;

function ensureAudio() {
  if (AC) {
    if (AC.state === 'suspended' && soundOn) AC.resume().catch(() => {});
    return true;
  }
  const Ctor = window.AudioContext || window.webkitAudioContext;
  if (!Ctor) { toast('Браузер не поддерживает Web Audio'); return false; }
  AC = new Ctor();
  master = AC.createGain();
  master.gain.value = muted ? 0 : 0.85;
  analyser = AC.createAnalyser();
  analyser.fftSize = 256;
  analyserData = new Uint8Array(analyser.frequencyBinCount);
  master.connect(analyser);
  analyser.connect(AC.destination);
  streamDest = AC.createMediaStreamDestination();
  master.connect(streamDest);

  // Общий буфер белого шума (2 c) — из него делаем «дождь/ветер» фильтрами
  noiseBuffer = AC.createBuffer(1, AC.sampleRate * 2, AC.sampleRate);
  const d = noiseBuffer.getChannelData(0);
  let last = 0;
  for (let i = 0; i < d.length; i++) {
    const white = Math.random() * 2 - 1;
    last = (last + 0.02 * white) / 1.02;      // розоватый оттенок
    d[i] = (last * 3.2 + white * 0.12) * 0.6;
  }
  return true;
}

/* Колокольчик FM: carrier + modulator, экспоненциальный спад */
function bellPing(destNode, freq, when, dur, vol) {
  const t = when;
  const car = AC.createOscillator(); car.type = 'sine'; car.frequency.value = freq;
  const mod = AC.createOscillator(); mod.type = 'sine'; mod.frequency.value = freq * 3.5;
  const modG = AC.createGain(); modG.gain.value = freq * 2.2;
  const g = AC.createGain();
  g.gain.setValueAtTime(0.0001, t);
  g.gain.exponentialRampToValueAtTime(Math.max(vol, 0.0011), t + 0.012);
  g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  mod.connect(modG); modG.connect(car.frequency);
  car.connect(g); g.connect(destNode);
  car.start(t); mod.start(t);
  const stop = t + dur + 0.1;
  car.stop(stop); mod.stop(stop);
}

/* Создать голос фигуры: Source -> Filter -> Panner -> voiceGain -> master */
function createVoice(s) {
  const t = AC.currentTime;
  const filter = AC.createBiquadFilter();
  filter.type = 'lowpass';
  filter.frequency.value = yToCutoff(s.y, H);
  filter.Q.value = 0.7;
  const pan = AC.createStereoPanner ? AC.createStereoPanner() : null;
  if (pan) pan.pan.value = xToPan(s.x, W);
  const out = AC.createGain();
  out.gain.value = 0;
  filter.connect(pan || out);
  if (pan) pan.connect(out);
  out.connect(master);

  const A = { filter, pan, out, extra: [] };
  const fadeIn = (v, peak, sec) => {
    v.gain.setValueAtTime(0.0001, t);
    v.gain.exponentialRampToValueAtTime(Math.max(peak, 0.0011), t + sec);
  };

  if (s.type === 'orb') {
    // Суб-бас-синус + шум дождя + медленная LFO-пульсация
    const osc = AC.createOscillator(); osc.type = 'sine';
    osc.frequency.value = yToOrbFreq(s.y, H);
    const og = AC.createGain(); og.gain.value = 0.5;
    osc.connect(og); og.connect(filter); osc.start(t);
    const nsrc = AC.createBufferSource(); nsrc.buffer = noiseBuffer; nsrc.loop = true;
    const nf = AC.createBiquadFilter(); nf.type = 'lowpass';
    nf.frequency.value = clamp(yToCutoff(s.y, H) * 0.25, 200, 2400);
    const ng = AC.createGain(); ng.gain.value = 0.05;
    nsrc.connect(nf); nf.connect(ng); ng.connect(filter); nsrc.start(t);
    const lfo = AC.createOscillator(); lfo.type = 'sine'; lfo.frequency.value = rand(0.05, 0.12);
    const lg = AC.createGain(); lg.gain.value = 0.02;
    lfo.connect(lg); lg.connect(ng.gain); lfo.start(t);
    A.extra.push(osc, nsrc, lfo);
    A.orbOsc = osc; A.noiseFilter = nf;
    fadeIn(out, 0.16, 2.5);
  } else if (s.type === 'ring') {
    // Пэд-дрон: два расстроенных пилообразных через lowpass, медленная атака
    const base = PENTA[((s.hue / 360) * 5) | 0] || 146.83;
    const o1 = AC.createOscillator(); o1.type = 'sawtooth'; o1.frequency.value = base; o1.detune.value = -7;
    const o2 = AC.createOscillator(); o2.type = 'triangle'; o2.frequency.value = base * 1.005; o2.detune.value = 6;
    const mg = AC.createGain(); mg.gain.value = 0.5;
    o1.connect(mg); o2.connect(mg); mg.connect(filter);
    o1.start(t); o2.start(t);
    A.extra.push(o1, o2);
    filter.frequency.value = clamp(yToCutoff(s.y, H) * 0.6, 250, 5000);
    fadeIn(out, 0.11, 4.0);
  } else if (s.type === 'sample') {
    // Свой звук: зацикленный BufferSource -> тот же фильтр/пан
    const buf = s.sampleBuffer || sampleBuffers.get(s.sampleKey)?.buffer;
    if (!buf) { s.audio = A; updateVoiceFromPos(s); return; }
    s.sampleBuffer = buf;
    const src = AC.createBufferSource();
    src.buffer = buf; src.loop = true;
    src.playbackRate.value = s.sampleRate || 1.0;
    src.connect(filter); src.start(t);
    A.extra.push(src);
    A.sampleSrc = src;
    fadeIn(out, 0.16, 2.0);
  } else {
    // Кристалл: тихий шиммер-фон; перезвоны планируются в tick через bellPing
    const shimmer = AC.createOscillator(); shimmer.type = 'sine';
    shimmer.frequency.value = pickPenta() * 2;
    const sg = AC.createGain(); sg.gain.value = 0.05;
    shimmer.connect(sg); sg.connect(filter); shimmer.start(t);
    A.extra.push(shimmer);
    fadeIn(out, 0.05, 2.0);
    s.nextChime = t + rand(0.6, 2.5);
  }
  s.audio = A;
  updateVoiceFromPos(s);
}

function updateVoiceFromPos(s) {
  if (!s.audio || !AC) return;
  const { filter, pan } = s.audio;
  const t = AC.currentTime;
  filter.frequency.setTargetAtTime(yToCutoff(s.y, H), t, 0.08);
  if (pan) pan.pan.setTargetAtTime(xToPan(s.x, W), t, 0.08);
  if (s.type === 'orb' && s.audio.orbOsc) {
    s.audio.orbOsc.frequency.setTargetAtTime(yToOrbFreq(s.y, H), t, 0.1);
    if (s.audio.noiseFilter) s.audio.noiseFilter.frequency.setTargetAtTime(clamp(yToCutoff(s.y, H) * 0.25, 200, 2400), t, 0.1);
  }
}

function removeVoice(s) {
  if (!s.audio || !AC) return;
  const t = AC.currentTime;
  const A = s.audio;
  try {
    A.out.gain.cancelScheduledValues(t);
    A.out.gain.setTargetAtTime(0.0001, t, 0.18);
    const nodes = A.extra.slice();
    setTimeout(() => { nodes.forEach(n => { try { n.stop(); } catch (e) {} }); try { A.out.disconnect(); } catch (e) {} }, 700);
  } catch (e) {}
  s.audio = null;
}

/* Парные пэды для близких фигур */
function pairKey(a, b) { return a < b ? a + '|' + b : b + '|' + a; }

function updatePairPads() {
  if (!AC || !soundOn) return;
  const active = new Set();
  for (let i = 0; i < shapes.length; i++) {
    for (let j = i + 1; j < shapes.length; j++) {
      const a = shapes[i], b = shapes[j];
      const dx = a.x - b.x, dy = a.y - b.y;
      const dist = Math.hypot(dx, dy);
      if (dist < LINK_DIST) {
        const key = pairKey(a.id, b.id);
        active.add(key);
        const closeness = 1 - dist / LINK_DIST;
        const midY = (a.y + b.y) / 2, midX = (a.x + b.x) / 2;
        let p = pairPads.get(key);
        if (!p) {
          const t = AC.currentTime;
          const o1 = AC.createOscillator(); o1.type = 'sine'; o1.frequency.value = 164.81;
          const o2 = AC.createOscillator(); o2.type = 'sine'; o2.frequency.value = 246.94;
          const f = AC.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = yToCutoff(midY, H);
          const pn = AC.createStereoPanner ? AC.createStereoPanner() : null;
          const g = AC.createGain(); g.gain.value = 0.0001;
          g.gain.setTargetAtTime(0.028 + closeness * 0.05, t, 1.2);
          o1.connect(f); o2.connect(f); f.connect(pn || g);
          if (pn) { pn.pan.value = xToPan(midX, W); pn.connect(g); }
          g.connect(master);
          o1.start(t); o2.start(t);
          p = { osc1: o1, osc2: o2, gain: g, filter: f, pan: pn };
          pairPads.set(key, p);
  } else if (s.type === 'sample') {
    // сэмпл: бирюзово-розовый квадрат с волной внутри — отличим от остальных
    const half = R;
    const grad = ctx.createLinearGradient(s.x - half, s.y - half, s.x + half, s.y + half);
    grad.addColorStop(0, `rgba(94,234,212,${0.85 * alpha})`);
    grad.addColorStop(1, `rgba(244,114,182,${0.85 * alpha})`);
    ctx.fillStyle = grad;
    ctx.strokeStyle = `rgba(255,255,255,${0.75 * alpha})`;
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    if (ctx.roundRect) ctx.roundRect(s.x - half, s.y - half, half * 2, half * 2, 6);
    else ctx.rect(s.x - half, s.y - half, half * 2, half * 2);
    ctx.fill(); ctx.stroke();
    // волна: берём реальную форму буфера, если есть
    ctx.save();
    ctx.shadowBlur = 0;
    ctx.strokeStyle = `rgba(5,8,12,${0.8 * alpha})`;
    ctx.lineWidth = 1.6;
    ctx.beginPath();
    ctx.rect(s.x - half, s.y - half, half * 2, half * 2);
    ctx.clip();
    const ch = s.sampleBuffer ? s.sampleBuffer.getChannelData(0) : null;
    const midY = s.y, amp = half * 0.6;
    for (let i = 0; i <= 40; i++) {
      const px = s.x - half + (i / 40) * half * 2;
      let v = 0;
      if (ch) v = ch[((i / 40) * (ch.length - 1)) | 0] || 0;
      else v = Math.sin(i * 0.7 + performance.now() * 0.003) * 0.4;
      const py = midY + clamp(v, -1, 1) * amp;
      if (i === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
    }
    ctx.stroke();
    ctx.restore();
  } else {
          const t = AC.currentTime;
          p.gain.gain.setTargetAtTime(0.028 + closeness * 0.05, t, 0.4);
          p.filter.frequency.setTargetAtTime(yToCutoff(midY, H), t, 0.3);
          if (p.pan) p.pan.pan.setTargetAtTime(xToPan(midX, W), t, 0.3);
        }
      }
    }
  }
  for (const [key, p] of pairPads) {
    if (!active.has(key)) {
      const t = AC.currentTime;
      try {
        p.gain.gain.setTargetAtTime(0.0001, t, 0.4);
        setTimeout(() => { try { p.osc1.stop(); p.osc2.stop(); } catch (e) {} }, 1500);
      } catch (e) {}
      pairPads.delete(key);
    }
  }
}

function clearPairPads() {
  for (const [, p] of pairPads) { try { p.osc1.stop(); p.osc2.stop(); } catch (e) {} }
  pairPads.clear();
}

/* ---------- Офлайн-граф для экспорта (переиспользует сцену) ---------- */
function buildGraph(context, destination, scene, duration) {
  const sr = context.sampleRate;
  const m = context.createGain(); m.gain.value = 0.85; m.connect(destination);
  // локальный шумовой буфер под sampleRate контекста
  const nb = context.createBuffer(1, sr * 2, sr);
  const nd = nb.getChannelData(0);
  let last = 0;
  for (let i = 0; i < nd.length; i++) {
    const w = Math.random() * 2 - 1;
    last = (last + 0.02 * w) / 1.02;
    nd[i] = (last * 3.2 + w * 0.12) * 0.6;
  }
  const Wpx = 1000, Hpx = 700;
  const cutoffOf = (yn) => Math.round(lerp(300, 8000, Math.pow(clamp(1 - yn, 0, 1), 1.4)));
  const panOf = (xn) => clamp(xn * 2 - 1, -1, 1);

  scene.forEach((s) => {
    const f = context.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = cutoffOf(s.y);
    let out = f;
    if (context.createStereoPanner) {
      const pn = context.createStereoPanner(); pn.pan.value = panOf(s.x);
      f.connect(pn); out = pn;
    }
    const g = context.createGain(); out.connect(g); g.connect(m);
    const t0 = 0;
    if (s.type === 'orb') {
      const fr = lerp(40, 80, clamp(1 - s.y, 0, 1));
      const o = context.createOscillator(); o.type = 'sine'; o.frequency.value = fr;
      const og = context.createGain();
      og.gain.setValueAtTime(0.0001, t0);
      og.gain.exponentialRampToValueAtTime(0.5, 2.0);
      o.connect(og); og.connect(f); o.start(t0); o.stop(duration);
      const ns = context.createBufferSource(); ns.buffer = nb; ns.loop = true;
      const nf = context.createBiquadFilter(); nf.type = 'lowpass'; nf.frequency.value = clamp(cutoffOf(s.y) * 0.25, 200, 2400);
      const ng = context.createGain(); ng.gain.value = 0.05;
      ns.connect(nf); nf.connect(ng); ng.connect(f); ns.start(t0); ns.stop(duration);
      g.gain.value = 0.32;
    } else if (s.type === 'ring') {
      const base = PENTA[(s.hue * 5) | 0] || 146.83;
      [ [base, 'sawtooth', -7], [base * 1.005, 'triangle', 6] ].forEach(([fr, ty, dt]) => {
        const o = context.createOscillator(); o.type = ty; o.frequency.value = fr; o.detune.value = dt;
        const og = context.createGain(); og.gain.value = 0.25;
        o.connect(og); og.connect(f); o.start(t0); o.stop(duration);
      });
      g.gain.setValueAtTime(0.0001, t0);
      g.gain.exponentialRampToValueAtTime(0.22, 4.0);
      g.gain.setValueAtTime(0.22, Math.max(4.0, duration - 2));
      g.gain.linearRampToValueAtTime(0.0001, duration);
    } else if (s.type === 'crystal') {
      const sh = context.createOscillator(); sh.type = 'sine'; sh.frequency.value = 440;
      const sg = context.createGain(); sg.gain.value = 0.04;
      sh.connect(sg); sg.connect(f); sh.start(t0); sh.stop(duration);
      g.gain.value = 0.5;
      // несколько перезвонов за duration
      let tt = 0.8;
      while (tt < duration - 0.5) {
        const fr = PENTA[(Math.random() * PENTA.length) | 0];
        const car = context.createOscillator(); car.type = 'sine'; car.frequency.value = fr;
        const mod = context.createOscillator(); mod.type = 'sine'; mod.frequency.value = fr * 3.5;
        const mg = context.createGain(); mg.gain.value = fr * 2.2;
        const bg = context.createGain();
        bg.gain.setValueAtTime(0.0001, tt);
        bg.gain.exponentialRampToValueAtTime(0.22, tt + 0.012);
        bg.gain.exponentialRampToValueAtTime(0.0001, tt + 2.0);
        mod.connect(mg); mg.connect(car.frequency); car.connect(bg); bg.connect(f);
        car.start(tt); mod.start(tt); car.stop(tt + 2.2); mod.stop(tt + 2.2);
        tt += rand(3, 7);
      }
    } else if (s.type === 'sample') {
      // Свой звук из кэша: зацикленный на всю длительность рендера
      const entry = s.sampleKey ? sampleBuffers.get(s.sampleKey) : null;
      const buf = entry ? entry.buffer : null;
      if (!buf) { g.gain.value = 0; }
      else {
        const src = context.createBufferSource();
        src.buffer = buf; src.loop = true;
        src.playbackRate.value = s.sampleRate || 1.0;
        src.connect(f); src.start(t0); src.stop(duration);
        g.gain.setValueAtTime(0.0001, t0);
        g.gain.exponentialRampToValueAtTime(0.32, 2.0);
        g.gain.setValueAtTime(0.32, Math.max(2.0, duration - 2));
        g.gain.linearRampToValueAtTime(0.0001, duration);
      }
    }
  });
  return m;
}

/* ---------- Сцена: создание / удаление ---------- */
const TYPE_COLORS = { orb: [125, 211, 252], ring: [251, 191, 36], crystal: [192, 132, 252], sample: [94, 234, 212] };

function spawnShape(x, y, forcedType) {
  if (shapes.length >= MAX_SHAPES) {
    const old = shapes.shift();
    removeVoice(old);
    toast('Лимит 24 фигуры — самая старая растворилась');
  }
  const types = ['orb', 'ring', 'crystal'];
  const type = forcedType || types[(Math.random() * 3) | 0];
  const s = {
    id: nextId++,
    type,
    x: clamp(x, 20, W - 20), y: clamp(y, 70, H - 50),
    vx: rand(-8, 8) * DRIFT, vy: rand(-6, 6) * DRIFT,
    r: type === 'orb' ? rand(16, 30) : type === 'ring' ? rand(20, 34) : rand(18, 30),
    hue: Math.random(),
    sides: 5 + ((Math.random() * 3) | 0),
    rot: rand(0, TAU), vr: rand(-0.004, 0.004) * (REDUCED ? 0.3 : 1),
    flash: 0,
    nextChime: 0,
    born: performance.now(),
    audio: null
  };
  shapes.push(s);
  if (AC && soundOn) {
    createVoice(s);
    if (type === 'crystal') {
      // приветственный перезвон
      bellPing(s.audio.filter, pickPenta() * 2, AC.currentTime + 0.05, 2.0, 0.2);
      s.nextChime = AC.currentTime + rand(3, 7);
    }
  }
  scheduleAutosave();
  updateCounter();
  return s;
}

/* Фигура-сэмпл из пользовательского аудио: тот же лимит, тот же drag/delete */
function spawnSampleShape(x, y, buffer, name, rate) {
  if (shapes.length >= MAX_SHAPES) {
    const old = shapes.shift();
    removeVoice(old);
    toast('Лимит 24 фигуры — самая старая растворилась');
  }
  const key = 'smp' + (sampleSeq++);
  sampleBuffers.set(key, { buffer, name: name || 'запись' });
  const s = {
    id: nextId++,
    type: 'sample',
    x: clamp(x, 20, W - 20), y: clamp(y, 70, H - 50),
    vx: rand(-8, 8) * DRIFT, vy: rand(-6, 6) * DRIFT,
    r: rand(20, 30),
    hue: Math.random(),
    sides: 4,
    rot: 0, vr: rand(-0.002, 0.002) * (REDUCED ? 0.3 : 1),
    flash: 0,
    nextChime: 0,
    born: performance.now(),
    audio: null,
    sampleBuffer: buffer,
    sampleKey: key,
    sampleName: name || 'запись',
    sampleRate: rate || 1.0
  };
  shapes.push(s);
  if (AC && soundOn) createVoice(s);
  scheduleAutosave();
  updateCounter();
  toast('♪ ' + s.sampleName + ' — фигура-сэмпл');
  return s;
}

function deleteShape(s) {
  removeVoice(s);
  shapes = shapes.filter((o) => o !== s);
  scheduleAutosave();
  updateCounter();
}

function clearAll() {
  shapes.forEach(removeVoice);
  shapes = [];
  clearPairPads();
  scheduleAutosave();
  updateCounter();
}

/* ---------- Canvas: размер, фон ---------- */
function resize() {
  DPR = Math.min(window.devicePixelRatio || 1, 2);
  W = window.innerWidth; H = window.innerHeight;
  canvas.width = Math.round(W * DPR);
  canvas.height = Math.round(H * DPR);
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.fillStyle = '#050608';
  ctx.fillRect(0, 0, W, H);
}
window.addEventListener('resize', resize);
resize();

/* ---------- Физика + рендер ---------- */
let lastT = performance.now();

function physics(dt) {
  const damp = 0.995;
  if (gravityOn) {
    // центр масс
    let cx = 0, cy = 0;
    shapes.forEach((s) => { cx += s.x; cy += s.y; });
    if (shapes.length) { cx /= shapes.length; cy /= shapes.length; }
    for (const s of shapes) {
      s.vx += (cx - s.x) * 0.00012 * dt;
      s.vy += (cy - s.y) * 0.00012 * dt;
      for (const o of shapes) {
        if (o === s) continue;
        const dx = o.x - s.x, dy = o.y - s.y;
        const d2 = dx * dx + dy * dy + 400;
        const f = 900 / d2 * dt * 0.016;
        s.vx += (dx / Math.sqrt(d2)) * f;
        s.vy += (dy / Math.sqrt(d2)) * f;
      }
      // столкновение
      for (const o of shapes) {
        if (o === s || o.id < s.id) continue;
        const dx = o.x - s.x, dy = o.y - s.y;
        const dist = Math.hypot(dx, dy);
        if (dist < HIT_DIST && dist > 0.01) {
          const nx = dx / dist, ny = dy / dist;
          const push = (HIT_DIST - dist) / 2;
          s.x -= nx * push; s.y -= ny * push;
          o.x += nx * push; o.y += ny * push;
          const rvx = s.vx - o.vx, rvy = s.vy - o.vy;
          const vn = rvx * nx + rvy * ny;
          if (vn > 0) {
            s.vx -= nx * vn * 0.9; s.vy -= ny * vn * 0.9;
            o.vx += nx * vn * 0.9; o.vy += ny * vn * 0.9;
          }
          s.flash = 1; o.flash = 1;
          collisionPing((s.x + o.x) / 2, (s.y + o.y) / 2);
        }
      }
    }
  }
  for (const s of shapes) {
    s.x += s.vx * dt * 0.016 * (gravityOn ? 1.6 : 1);
    s.y += s.vy * dt * 0.016 * (gravityOn ? 1.6 : 1);
    s.vx *= damp; s.vy *= damp;
    // мягкое удержание в кадре
    if (s.x < s.r) { s.x = s.r; s.vx = Math.abs(s.vx) * 0.8; }
    if (s.x > W - s.r) { s.x = W - s.r; s.vx = -Math.abs(s.vx) * 0.8; }
    if (s.y < 60 + s.r) { s.y = 60 + s.r; s.vy = Math.abs(s.vy) * 0.8; }
    if (s.y > H - 40 - s.r) { s.y = H - 40 - s.r; s.vy = -Math.abs(s.vy) * 0.8; }
    s.rot += s.vr * dt;
    if (s.flash > 0) s.flash = Math.max(0, s.flash - dt * 0.002);
  }
}

function collisionPing(x, y) {
  if (!AC || !soundOn) return;
  const t = AC.currentTime;
  const tmp = AC.createGain();
  const f = AC.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = yToCutoff(y, H);
  const pn = AC.createStereoPanner ? AC.createStereoPanner() : null;
  tmp.connect(f); f.connect(pn || master);
  if (pn) { pn.pan.value = xToPan(x, W); pn.connect(master); }
  else tmp.connect(master);
  bellPing(f, pickPenta() * 2, t + 0.01, 1.2, 0.16);
}

function drawShape(s) {
  const [r, g, b] = TYPE_COLORS[s.type] || TYPE_COLORS.orb;
  const born = clamp((performance.now() - s.born) / 900, 0, 1);
  const alpha = 0.35 + 0.65 * born;
  const flash = s.flash;
  const R = s.r * (1 + flash * 0.35);

  ctx.save();
  ctx.globalAlpha = alpha;
  ctx.shadowBlur = 26 + flash * 40;
  ctx.shadowColor = `rgba(${r},${g},${b},.9)`;

  if (s.type === 'orb') {
    const grad = ctx.createRadialGradient(s.x - R * 0.3, s.y - R * 0.3, 1, s.x, s.y, R);
    grad.addColorStop(0, `rgba(255,255,255,${0.95 * alpha})`);
    grad.addColorStop(0.35, `rgba(${r},${g},${b},${0.85 * alpha})`);
    grad.addColorStop(1, `rgba(${r},${g},${b},0)`);
    ctx.fillStyle = grad;
    ctx.beginPath(); ctx.arc(s.x, s.y, R, 0, TAU); ctx.fill();
    ctx.shadowBlur = 0;
    ctx.fillStyle = 'rgba(255,255,255,.9)';
    ctx.beginPath(); ctx.arc(s.x - R * 0.28, s.y - R * 0.3, R * 0.14, 0, TAU); ctx.fill();
  } else if (s.type === 'ring') {
    ctx.strokeStyle = `rgba(${r},${g},${b},${0.9 * alpha})`;
    ctx.lineWidth = 2 + flash * 2;
    ctx.beginPath(); ctx.arc(s.x, s.y, R, 0, TAU); ctx.stroke();
    ctx.shadowBlur = 8;
    ctx.strokeStyle = `rgba(255,255,255,${0.35 * alpha})`;
    ctx.lineWidth = 1;
    ctx.beginPath(); ctx.arc(s.x, s.y, R * 0.62, s.rot, s.rot + TAU * 0.8); ctx.stroke();
  } else {
    // кристалл-полигон
    ctx.translate(s.x, s.y); ctx.rotate(s.rot);
    const grad = ctx.createRadialGradient(0, 0, 1, 0, 0, R);
    grad.addColorStop(0, `rgba(255,255,255,${0.85 * alpha})`);
    grad.addColorStop(0.55, `rgba(${r},${g},${b},${0.55 * alpha})`);
    grad.addColorStop(1, `rgba(${r},${g},${b},${0.12 * alpha})`);
    ctx.fillStyle = grad;
    ctx.strokeStyle = `rgba(${r},${g},${b},${0.9 * alpha})`;
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    for (let i = 0; i < s.sides; i++) {
      const a = (i / s.sides) * TAU;
      const px = Math.cos(a) * R, py = Math.sin(a) * R;
      if (i === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
    }
    ctx.closePath(); ctx.fill(); ctx.stroke();
  }
  ctx.restore();
}

function frame(now) {
  const dt = clamp(now - lastT, 8, 50);
  lastT = now;

  physics(dt);

  // затухающий след
  ctx.fillStyle = REDUCED ? 'rgba(5,6,8,0.32)' : 'rgba(5,6,8,0.16)';
  ctx.fillRect(0, 0, W, H);

  // связи-линии
  for (let i = 0; i < shapes.length; i++) {
    for (let j = i + 1; j < shapes.length; j++) {
      const a = shapes[i], b = shapes[j];
      const dist = Math.hypot(a.x - b.x, a.y - b.y);
      if (dist < LINK_DIST) {
        const t = 1 - dist / LINK_DIST;
        ctx.save();
        ctx.globalAlpha = t * 0.5;
        ctx.strokeStyle = `rgba(150,180,255,${0.1 + t * 0.5})`;
        ctx.lineWidth = 1;
        ctx.shadowBlur = 8;
        ctx.shadowColor = 'rgba(140,170,255,.7)';
        ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
        ctx.restore();
      }
    }
  }
  shapes.forEach(drawShape);

  // перезвоны кристаллов + обновление парных пэдов
  if (AC && soundOn) {
    const t = AC.currentTime;
    for (const s of shapes) {
      if (s.type === 'crystal' && s.audio && t >= s.nextChime) {
        bellPing(s.audio.filter, pickPenta() * 2, t + 0.02, rand(1.5, 2.5), 0.2);
        s.nextChime = t + rand(3, 7);
      }
    }
    if ((frame.n = (frame.n || 0) + 1) % 20 === 0) updatePairPads();
  }

  drawWave();
  requestAnimationFrame(frame);
}

function drawWave() {
  waveCtx.clearRect(0, 0, waveCanvas.width, waveCanvas.height);
  waveCtx.strokeStyle = 'rgba(140,160,200,.5)';
  waveCtx.lineWidth = 1;
  waveCtx.beginPath();
  if (analyser && soundOn && !muted) {
    analyser.getByteFrequencyData(analyserData);
    const n = analyserData.length;
    for (let i = 0; i < waveCanvas.width; i++) {
      const v = analyserData[((i / waveCanvas.width) * n) | 0] / 255;
      const y = waveCanvas.height - v * waveCanvas.height - 1;
      if (i === 0) waveCtx.moveTo(i, y); else waveCtx.lineTo(i, y);
    }
  } else {
    const y = waveCanvas.height / 2;
    waveCtx.moveTo(0, y);
    for (let i = 0; i < waveCanvas.width; i += 6) waveCtx.lineTo(i, y + Math.sin(i * 0.1 + performance.now() * 0.001) * 2);
  }
  waveCtx.stroke();
}

/* ---------- Взаимодействие: клик / drag / удаление / touch ---------- */
let dragShape = null, downPos = null, downTime = 0, moved = false;
const dragTip = $('dragTip');

function hitShape(x, y) {
  for (let i = shapes.length - 1; i >= 0; i--) {
    const s = shapes[i];
    if (Math.hypot(s.x - x, s.y - y) < s.r + 16) return s;
  }
  return null;
}
function evPos(e) {
  if (e.touches && e.touches[0]) return { x: e.touches[0].clientX, y: e.touches[0].clientY };
  return { x: e.clientX, y: e.clientY };
}

canvas.addEventListener('pointerdown', (e) => {
  const { x, y } = evPos(e);
  downPos = { x, y }; downTime = performance.now(); moved = false;
  const hit = hitShape(x, y);
  if (hit) {
    dragShape = hit;
    canvas.setPointerCapture && canvas.setPointerCapture(e.pointerId);
  }
});
canvas.addEventListener('pointermove', (e) => {
  if (!downPos) return;
  const { x, y } = evPos(e);
  if (Math.hypot(x - downPos.x, y - downPos.y) > 6) moved = true;
  if (dragShape) {
    dragShape.x = clamp(x, 10, W - 10);
    dragShape.y = clamp(y, 60, H - 30);
    dragShape.vx *= 0.6; dragShape.vy *= 0.6;
    updateVoiceFromPos(dragShape);
    // тонкая подсказка при drag
    const pan = xToPan(dragShape.x, W).toFixed(2);
    const cf = yToCutoff(dragShape.y, H);
    dragTip.hidden = false;
    dragTip.style.left = x + 'px';
    dragTip.style.top = y + 'px';
    dragTip.textContent = dragShape.type === 'sample' && dragShape.sampleName
      ? `♪ ${dragShape.sampleName} · pan ${pan} · cutoff ${cf} Гц`
      : `pan ${pan} · cutoff ${cf} Гц`;
    scheduleAutosave();
  }
});
function endPointer(e) {
  dragTip.hidden = true;
  if (dragShape) { dragShape = null; }
  else if (downPos && !moved) {
    // чистый клик в пустоте — спавн
    const { x, y } = evPos(e.changedTouches ? { touches: e.changedTouches } : e);
    startSoundIfNeeded();
    spawnShape(x, y);
  }
  downPos = null;
}
canvas.addEventListener('pointerup', endPointer);
canvas.addEventListener('pointercancel', () => { dragTip.hidden = true; dragShape = null; downPos = null; });
canvas.addEventListener('touchmove', (e) => e.preventDefault(), { passive: false });

canvas.addEventListener('dblclick', (e) => {
  const s = hitShape(e.clientX, e.clientY);
  if (s) { deleteShape(s); toast('Фигура удалена'); }
});
canvas.addEventListener('contextmenu', (e) => {
  e.preventDefault();
  const s = hitShape(e.clientX, e.clientY);
  if (s) { deleteShape(s); toast('Фигура удалена'); }
});

/* ---------- Звук: старт / пауза / мьют ---------- */
const btnSound = $('btnSound');
function startSoundIfNeeded() {
  if (!ensureAudio()) return;
  if (AC.state === 'suspended') AC.resume().catch(() => {});
  if (!soundOn) {
    soundOn = true; startedOnce = true;
    shapes.forEach((s) => { if (!s.audio) createVoice(s); });
    btnSound.innerHTML = '⏸&nbsp;Пауза';
    btnSound.classList.add('on');
    toast('Звук включён — кликай и тяни фигуры');
  }
}
btnSound.addEventListener('click', () => {
  if (!startedOnce || !AC) { startSoundIfNeeded(); return; }
  if (soundOn) {
    soundOn = false;
    AC.suspend();
    btnSound.innerHTML = '▶&nbsp;Звук';
    btnSound.classList.remove('on');
  } else {
    soundOn = true;
    AC.resume().catch(() => {});
    shapes.forEach((s) => { if (!s.audio) createVoice(s); });
    btnSound.innerHTML = '⏸&nbsp;Пауза';
    btnSound.classList.add('on');
  }
});
$('btnMute').addEventListener('click', (e) => {
  muted = !muted;
  if (master && AC) master.gain.setTargetAtTime(muted ? 0 : 0.85, AC.currentTime, 0.05);
  e.currentTarget.classList.toggle('on', muted);
  e.currentTarget.textContent = muted ? 'Unmute' : 'Mute';
});

/* ---------- Гравитация / Очистить ---------- */
$('btnGravity').addEventListener('click', (e) => {
  gravityOn = !gravityOn;
  e.currentTarget.classList.toggle('on', gravityOn);
  e.currentTarget.setAttribute('aria-pressed', String(gravityOn));
  toast(gravityOn ? 'Гравитация включена — фигуры притягиваются' : 'Гравитация выключена — свободный дрейф');
});
$('btnClear').addEventListener('click', () => {
  if (!shapes.length) return;
  clearAll();
  toast('Сцена очищена');
});

/* ---------- Счётчик ---------- */
function updateCounter() {
  $('statShapes').textContent = shapes.length;
  $('statVoices').textContent = shapes.length + pairPads.size;
}
setInterval(updateCounter, 800);

/* ---------- Пресеты: hash + localStorage ---------- */
function hasSamples() { return shapes.some((s) => s.type === 'sample'); }
function serializeScene() {
  // Свои звуки в ссылку/слоты не пишем — только синтез (orb/ring/crystal)
  const arr = shapes.filter((s) => s.type !== 'sample').map((s) => [
    s.type === 'orb' ? 0 : s.type === 'ring' ? 1 : 2,
    Math.round((s.x / W) * 1000),
    Math.round((s.y / H) * 1000)
  ]);
  return arr;
}
function noteSamplesSkipped() {
  if (hasSamples()) toast('Свои звуки не сохраняются в ссылку');
}
function applyScene(arr) {
  clearAll();
  const names = ['orb', 'ring', 'crystal'];
  arr.slice(0, MAX_SHAPES).forEach(([ti, xn, yn]) => {
    if (ti === 3) return; // сэмплы из hash не восстанавливаем (без аудио)
    const type = names[ti] || 'orb';
    const x = clamp(xn / 1000, 0, 1) * W;
    const y = clamp(yn / 1000, 0, 1) * H;
    const s = {
      id: nextId++, type, x, y,
      vx: rand(-8, 8) * DRIFT, vy: rand(-6, 6) * DRIFT,
      r: type === 'orb' ? rand(16, 30) : type === 'ring' ? rand(20, 34) : rand(18, 30),
      hue: Math.random(), sides: 5 + ((Math.random() * 3) | 0),
      rot: rand(0, TAU), vr: rand(-0.004, 0.004),
      flash: 0, nextChime: 0, born: performance.now(), audio: null
    };
    shapes.push(s);
    if (AC && soundOn) createVoice(s);
  });
  updateCounter();
}
function sceneToHash() {
  const json = JSON.stringify(serializeScene());
  const b64 = btoa(unescape(encodeURIComponent(json))).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  return '#s=' + b64;
}
function sceneFromHash() {
  const m = window.location.hash.match(/#s=([A-Za-z0-9\-_]+)/);
  if (!m) return null;
  try {
    let b64 = m[1].replace(/-/g, '+').replace(/_/g, '/');
    while (b64.length % 4) b64 += '=';
    return JSON.parse(decodeURIComponent(escape(atob(b64))));
  } catch (e) { return null; }
}
function writeHash() {
  history.replaceState(null, '', sceneToHash());
}

let autosaveT = null;
function scheduleAutosave() {
  writeHashDebounced();
  clearTimeout(autosaveT);
  autosaveT = setTimeout(() => {
    try { localStorage.setItem('ss_autosave', JSON.stringify(serializeScene())); } catch (e) {}
  }, 600);
}
let hashT = null;
function writeHashDebounced() {
  clearTimeout(hashT);
  hashT = setTimeout(writeHash, 600);
}

const presetPanel = $('presetPanel');
$('btnSave').addEventListener('click', () => {
  presetPanel.hidden = !presetPanel.hidden;
  if (!presetPanel.hidden) { writeHash(); noteSamplesSkipped(); }
});
$('btnClosePresets').addEventListener('click', () => { presetPanel.hidden = true; });
document.querySelectorAll('[data-save]').forEach((b) => b.addEventListener('click', () => {
  try { localStorage.setItem('ss_slot_' + b.dataset.save, JSON.stringify(serializeScene())); } catch (e) {}
  $('presetMsg').textContent = 'Слот ' + b.dataset.save + ' сохранён.';
  if (hasSamples()) { $('presetMsg').textContent = 'Слот ' + b.dataset.save + ' сохранён (без своих звуков).'; toast('Свои звуки не сохраняются в ссылку'); }
  else toast('Пресет сохранён в слот ' + b.dataset.save);
}));
document.querySelectorAll('[data-load]').forEach((b) => b.addEventListener('click', () => {
  try {
    const raw = localStorage.getItem('ss_slot_' + b.dataset.load);
    if (!raw) { toast('Слот ' + b.dataset.load + ' пуст'); return; }
    applyScene(JSON.parse(raw));
    writeHash();
    toast('Пресет из слота ' + b.dataset.load + ' загружен');
  } catch (e) { toast('Не удалось загрузить слот'); }
}));
$('btnCopyLink').addEventListener('click', async () => {
  writeHash();
  noteSamplesSkipped();
  const url = window.location.href;
  try {
    await navigator.clipboard.writeText(url);
    toast('Ссылка скопирована — отправь её другу');
  } catch (e) {
    prompt('Скопируй ссылку вручную:', url);
  }
});

/* Загрузка при старте: hash -> слоты-автосейв -> демо-сцена */
function restoreAtStart() {
  const fromHash = sceneFromHash();
  if (fromHash && fromHash.length) { applyScene(fromHash); return; }
  try {
    const auto = localStorage.getItem('ss_autosave');
    if (auto && JSON.parse(auto).length) { applyScene(JSON.parse(auto)); return; }
  } catch (e) {}
  // демо: 3 фигуры, чтобы первый кадр не был пустым
  setTimeout(() => {
    if (!shapes.length) {
      spawnShape(W * 0.3, H * 0.4, 'orb');
      spawnShape(W * 0.62, H * 0.55, 'ring');
      spawnShape(W * 0.48, H * 0.3, 'crystal');
    }
  }, 400);
}

/* ---------- Экспорт .wav ---------- */
function encodeWav(buffers, sampleRate) {
  const nCh = buffers.length;
  const len = buffers[0].length;
  const bytesPerSample = 2;
  const blockAlign = nCh * bytesPerSample;
  const buf = new ArrayBuffer(44 + len * blockAlign);
  const v = new DataView(buf);
  const wstr = (o, s) => { for (let i = 0; i < s.length; i++) v.setUint8(o + i, s.charCodeAt(i)); };
  wstr(0, 'RIFF'); v.setUint32(4, 36 + len * blockAlign, true); wstr(8, 'WAVE');
  wstr(12, 'fmt '); v.setUint32(16, 16, true); v.setUint16(20, 1, true);
  v.setUint16(22, nCh, true); v.setUint32(24, sampleRate, true);
  v.setUint32(28, sampleRate * blockAlign, true); v.setUint16(32, blockAlign, true);
  v.setUint16(34, 16, true); wstr(36, 'data'); v.setUint32(40, len * blockAlign, true);
  let off = 44;
  for (let i = 0; i < len; i++) {
    for (let ch = 0; ch < nCh; ch++) {
      const s = clamp(buffers[ch][i], -1, 1);
      v.setInt16(off, s < 0 ? s * 0x8000 : s * 0x7FFF, true);
      off += 2;
    }
  }
  return new Blob([buf], { type: 'audio/wav' });
}

$('btnExport').addEventListener('click', async (e) => {
  const btn = e.currentTarget;
  if (!shapes.length) { toast('Сцена пуста — создай хотя бы одну фигуру'); return; }
  const DUR = 18;
  btn.classList.add('busy');
  const old = btn.textContent;
  btn.textContent = 'Рендер…';
  try {
    const sr = 44100;
    const OC = new OfflineAudioContext(2, sr * DUR, sr);
    const scene = shapes.map((s) => ({ type: s.type, x: s.x / W, y: s.y / H, hue: s.hue, sampleKey: s.sampleKey, sampleRate: s.sampleRate }));
    buildGraph(OC, OC.destination, scene, DUR);
    const rendered = await OC.startRendering();
    const blob = encodeWav([rendered.getChannelData(0), rendered.getChannelData(1)], sr);
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'soundscape.wav';
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 4000);
    toast('soundscape.wav — 18 секунд, скачан');
  } catch (err) {
    // Fallback: запись реального времени через MediaRecorder
    try {
      if (!ensureAudio()) throw err;
      toast('Офлайн-рендер недоступен — пишу 15 с в реальном времени…');
      if (AC.state === 'suspended') await AC.resume();
      if (!soundOn) startSoundIfNeeded();
      const rec = new MediaRecorder(streamDest.stream);
      const chunks = [];
      rec.ondataavailable = (ev) => { if (ev.data.size) chunks.push(ev.data); };
      const done = new Promise((res) => { rec.onstop = res; });
      rec.start();
      setTimeout(() => rec.stop(), 15000);
      await done;
      const blob = new Blob(chunks, { type: rec.mimeType || 'audio/webm' });
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = 'soundscape-live.webm';
      document.body.appendChild(a); a.click(); a.remove();
      toast('Запись 15 с сохранена (live-режим)');
    } catch (e2) {
      toast('Экспорт не удался в этом браузере');
    }
  } finally {
    btn.classList.remove('busy');
    btn.textContent = old;
  }
});

/* ---------- Свои звуки: файлы, drag&drop, микрофон ---------- */
const fileInput = $('fileInput');
const dropHint = $('dropHint');
$('btnSample').addEventListener('click', () => fileInput.click());
fileInput.addEventListener('change', () => {
  if (fileInput.files && fileInput.files.length) handleAudioFiles(fileInput.files);
  fileInput.value = '';
});

async function handleAudioFiles(list) {
  const files = Array.from(list || []).filter((f) =>
    (f.type && f.type.startsWith('audio/')) || /\.(mp3|wav|ogg|m4a|flac|webm|aac)$/i.test(f.name || ''));
  if (!files.length) { toast('Это не аудиофайл'); return; }
  if (!ensureAudio()) return;
  if (AC.state === 'suspended') AC.resume().catch(() => {});
  startSoundIfNeeded();
  for (const file of files) {
    if (file.size > MAX_FILE_MB * 1024 * 1024) {
      toast('«' + file.name + '» больше 20 МБ — пропустил');
      continue;
    }
    if (shapes.length >= MAX_SHAPES) {
      toast('Лимит 24 фигуры — остальные файлы пропущены');
      break;
    }
    try {
      const raw = await file.arrayBuffer();
      const buf = await AC.decodeAudioData(raw);
      spawnSampleShape(rand(W * 0.25, W * 0.75), rand(H * 0.3, H * 0.7), buf, file.name, rand(0.7, 1.2));
    } catch (e) {
      toast('Не смог прочитать «' + file.name + '»');
    }
  }
}

/* Drag&drop в любое место окна */
let dragDepth = 0;
window.addEventListener('dragenter', (e) => {
  e.preventDefault();
  if (e.dataTransfer && Array.from(e.dataTransfer.types || []).includes('Files')) {
    dragDepth++;
    canvas.classList.add('dragover');
    dropHint.hidden = false;
  }
});
window.addEventListener('dragover', (e) => e.preventDefault());
window.addEventListener('dragleave', (e) => {
  e.preventDefault();
  if (--dragDepth <= 0) { dragDepth = 0; canvas.classList.remove('dragover'); dropHint.hidden = true; }
});
window.addEventListener('drop', (e) => {
  e.preventDefault();
  dragDepth = 0;
  canvas.classList.remove('dragover');
  dropHint.hidden = true;
  if (e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files.length) {
    handleAudioFiles(e.dataTransfer.files);
  }
});

/* Запись с микрофона: getUserMedia + MediaRecorder -> decode -> сэмпл */
let micRec = null, micStream = null, micChunks = [], micTimer = null, micSec = 0;
const btnRec = $('btnRec');
btnRec.addEventListener('click', async () => {
  if (micRec && micRec.state !== 'inactive') { stopMic(); return; }
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    toast('Браузер не даёт доступ к микрофону'); return;
  }
  try {
    micStream = await navigator.mediaDevices.getUserMedia({ audio: true });
  } catch (e) {
    toast('Нет доступа к микрофону');
    return;
  }
  try {
    micRec = new MediaRecorder(micStream);
  } catch (e) {
    micStream.getTracks().forEach((t) => t.stop());
    toast('Запись не поддерживается в этом браузере');
    return;
  }
  micChunks = []; micSec = 0;
  micRec.ondataavailable = (ev) => { if (ev.data && ev.data.size) micChunks.push(ev.data); };
  micRec.onstop = async () => {
    clearInterval(micTimer);
    btnRec.classList.remove('rec-on');
    btnRec.textContent = '● Rec';
    micStream.getTracks().forEach((t) => t.stop());
    const blob = new Blob(micChunks, { type: (micRec && micRec.mimeType) || 'audio/webm' });
    if (!blob.size) { toast('Запись пустая'); return; }
    if (!ensureAudio()) return;
    if (AC.state === 'suspended') AC.resume().catch(() => {});
    startSoundIfNeeded();
    try {
      const raw = await blob.arrayBuffer();
      const buf = await AC.decodeAudioData(raw);
      const name = 'запись ' + new Date().toLocaleTimeString('ru-RU', { hour: '2-digit', minute: '2-digit', second: '2-digit' });
      spawnSampleShape(rand(W * 0.25, W * 0.75), rand(H * 0.3, H * 0.7), buf, name, 1.0);
    } catch (e) {
      toast('Не смог декодировать запись');
    }
    micRec = null;
  };
  micRec.start();
  btnRec.classList.add('rec-on');
  btnRec.textContent = '■ Стоп (0:00)';
  toast('Запись с микрофона… нажми «Стоп» для фигуры');
  micTimer = setInterval(() => {
    micSec++;
    btnRec.textContent = '■ Стоп (' + Math.floor(micSec / 60) + ':' + String(micSec % 60).padStart(2, '0') + ')';
  }, 1000);
});
function stopMic() { try { if (micRec && micRec.state !== 'inactive') micRec.stop(); } catch (e) {} }

/* ---------- Помощь / тосты / клавиатура ---------- */
const helpModal = $('helpModal');
$('btnHelp').addEventListener('click', () => { helpModal.hidden = false; });
$('btnCloseHelp').addEventListener('click', () => { helpModal.hidden = true; });
helpModal.addEventListener('click', (e) => { if (e.target === helpModal) helpModal.hidden = true; });

let toastT = null;
function toast(msg) {
  const el = $('toast');
  el.textContent = msg;
  el.hidden = false;
  clearTimeout(toastT);
  toastT = setTimeout(() => { el.hidden = true; }, 2600);
}

window.addEventListener('keydown', (e) => {
  if (e.key === '?' || (e.key === 'h' && e.ctrlKey)) helpModal.hidden = !helpModal.hidden;
  if (e.key === 'Escape') { helpModal.hidden = true; presetPanel.hidden = true; }
  if (e.key === ' ' && e.target === document.body) { e.preventDefault(); btnSound.click(); }
});

/* ---------- Старт ---------- */
restoreAtStart();
updateCounter();
requestAnimationFrame((t) => { lastT = t; requestAnimationFrame(frame); });
