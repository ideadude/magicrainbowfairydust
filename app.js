/**
 * Magic Rainbow Fairy Dust
 *
 * A generative music toy: six notes rotating through a scale with delay echo,
 * convolution reverb, and an SMR-style LED ring around a big arcade button.
 * Every press gives you a different sound. Inspired by magicrainbowfairydust.com
 * and Andrew Huang's Spectral Multiband Resonator video.
 *
 * Signal chain:
 *   OscillatorNode → GainNode (ADSR) → 3-band main EQ → DynamicsCompressor → masterGain → destination
 *                                    ↘ DelayNode (per-note) → tone LPF → 3-band delay EQ → fbGain ⟲
 *                                                                                         ↘ delayOutGain → main EQ
 *                                    → ConvolverNode (reverb IR, normal or reversed) → reverbGain → masterGain
 */

;(function () {
  'use strict';

  // ===========================================================================
  // CONSTANTS
  // ===========================================================================

  const SCALES = {
    pentatonic:    { name: 'Major Pentatonic', intervals: [0, 2, 4, 7, 9] },
    pent_minor:    { name: 'Minor Pentatonic', intervals: [0, 3, 5, 7, 10] },
    major:         { name: 'Major',            intervals: [0, 2, 4, 5, 7, 9, 11] },
    natural_minor: { name: 'Natural Minor',    intervals: [0, 2, 3, 5, 7, 8, 10] },
    dorian:        { name: 'Dorian',           intervals: [0, 2, 3, 5, 7, 9, 10] },
    lydian:        { name: 'Lydian',           intervals: [0, 2, 4, 6, 7, 9, 11] },
    mixolydian:    { name: 'Mixolydian',       intervals: [0, 2, 4, 5, 7, 9, 10] },
    whole_tone:    { name: 'Whole Tone',       intervals: [0, 2, 4, 6, 8, 10] },
    phrygian:      { name: 'Phrygian',         intervals: [0, 1, 3, 5, 7, 8, 10] },
    augmented:     { name: 'Augmented',        intervals: [0, 3, 4, 7, 8, 11] },
  };

  const NICE_SCALES = ['pentatonic', 'pent_minor', 'major', 'dorian', 'lydian', 'mixolydian'];
  const NOTE_NAMES  = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
  const LED_COUNT   = 12;

  const NICE_DIVS = [0.5, 0.25, 0.125];
  const ALL_DIVS  = [0.5, 0.25, 0.125, 0.0625, 0.333, 0.1667];

  const NOTE_DIV_LABELS = {
    0.5: '1/2', 0.25: '1/4', 0.125: '1/8', 0.0625: '1/16',
    0.333: '1/3', 0.1667: '1/6 (trip)',
  };

  const NAME_ADJ = [
    'Sparkle', 'Crystal', 'Rainbow', 'Cosmic', 'Fairy', 'Neon', 'Prism',
    'Lunar', 'Electric', 'Mystic', 'Glitter', 'Pixel', 'Candy', 'Velvet',
    'Hyper', 'Dream', 'Ghost', 'Laser', 'Cloud', 'Solar', 'Quantum',
    'Nebula', 'Frozen', 'Melting', 'Spectral', 'Molten', 'Shiver', 'Flutter',
  ];

  const NAME_NOUN = [
    'Mountain', 'Cascade', 'Storm', 'Dust', 'Wave', 'Echo', 'Drift',
    'Flash', 'Rain', 'Field', 'River', 'Forest', 'Cave', 'Garden',
    'Current', 'Bloom', 'Vault', 'Prism', 'Comet', 'Aurora', 'Fountain',
    'Glacier', 'Rift', 'Spiral', 'Throne', 'Choir', 'Valley', 'Burst',
  ];

  // Keys included in share URLs — everything that affects sound
  const SHARE_KEYS = [
    'scale', 'rootNoteIdx', 'octave', 'numNotes', 'octaveRange',
    'bpm', 'noteDiv', 'noteDuration', 'direction', 'pickedNotes',
    'reverbAmount', 'delayTime', 'delayFeedback', 'delayVol', 'delayTone',
    'eqLow', 'eqMid', 'eqHigh', 'delayEqLow', 'delayEqMid', 'delayEqHigh',
    'volume', 'reverseEcho',
  ];

  const STORAGE_KEY = 'mrfd-favorites';


  // ===========================================================================
  // PARAMS — the single source of truth for the current sound
  // ===========================================================================

  const P = {
    scale:         'pentatonic',
    rootNoteIdx:   0,
    octave:        4,
    numNotes:      6,
    octaveRange:   2,
    bpm:           90,
    noteDiv:       0.25,
    noteDuration:  400,
    direction:     'asc',
    reverbAmount:  0.45,
    delayTime:     300,
    delayFeedback: 0.35,
    delayVol:      0.8,
    delayTone:     50,
    eqLow:         0,
    eqMid:         0,
    eqHigh:        0,
    delayEqLow:    0,
    delayEqMid:    0,
    delayEqHigh:   0,
    volume:        0.65,
    pickedNotes:   [],
    holdMode:      false,
    wildMode:      false,
    autoRandomize: true,
    reverseEcho:   false,
  };


  // ===========================================================================
  // STATE
  // ===========================================================================

  // Audio graph
  let actx = null;
  let masterGain, limiter, eqLow, eqMid, eqHigh;
  let reverbConv, reverbGain, delayOutGain;
  let builtReverbReversed = null;

  // Playback
  let activeNodes  = [];
  let playGen      = 0;

  // Visualization
  let rotation     = 0;     // 0–1, drives note cluster selection
  let visualAngle  = 0;     // radians, physical LED ring rotation
  let lastFrameTime = 0;
  const ledBright       = new Float32Array(LED_COUNT);
  const activeLedExpiry = {};
  const cascadeLines    = [];
  const particles       = [];

  // Hold / loop
  let isHeld    = false;
  let holdTimer = null;

  // Recent plays
  const recentPlays = [];

  // Canvas
  const canvas = document.getElementById('viz');
  const ctx2d  = canvas.getContext('2d');
  let canvasW = 0, canvasH = 0;


  // ===========================================================================
  // HELPERS
  // ===========================================================================

  const $ = id => document.getElementById(id);

  function getRootMidi() {
    return (P.octave + 1) * 12 + P.rootNoteIdx;
  }

  function getSpacingMs() {
    return Math.max(20, Math.round((60 / P.bpm) * P.noteDiv * 1000));
  }

  function getNoteDivLabel(div) {
    const key = Object.keys(NOTE_DIV_LABELS)
      .reduce((a, b) => Math.abs(b - div) < Math.abs(a - div) ? b : a);
    return NOTE_DIV_LABELS[key] || String(div);
  }

  function pick(arr) {
    return arr[Math.floor(Math.random() * arr.length)];
  }

  function randInt(min, max) {
    return min + Math.floor(Math.random() * (max - min + 1));
  }

  function clamp(val, lo, hi) {
    return Math.max(lo, Math.min(hi, val));
  }

  function escapeHtml(str) {
    return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }

  function generateName() {
    return pick(NAME_ADJ) + ' ' + pick(NAME_NOUN);
  }

  function midiToName(midi) {
    return NOTE_NAMES[midi % 12] + Math.floor(midi / 12 - 1);
  }

  function shuffleArray(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
  }


  // ===========================================================================
  // TOAST
  // ===========================================================================

  let toastTimer = null;

  function showToast(msg) {
    let el = $('toast');
    if (!el) {
      el = document.createElement('div');
      el.id = 'toast';
      document.body.appendChild(el);
    }
    el.textContent = msg;
    el.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => el.classList.remove('show'), 2200);
  }


  // ===========================================================================
  // AUDIO ENGINE
  // ===========================================================================

  function initAudio() {
    if (actx) {
      if (actx.state === 'suspended') actx.resume();
      return;
    }

    actx = new (window.AudioContext || window.webkitAudioContext)();

    // Master output
    masterGain = actx.createGain();
    masterGain.gain.value = P.volume;
    masterGain.connect(actx.destination);

    // Limiter (protects against feedback-loop stacking)
    limiter = actx.createDynamicsCompressor();
    limiter.threshold.value = -4;
    limiter.knee.value      = 2;
    limiter.ratio.value     = 20;
    limiter.attack.value    = 0.001;
    limiter.release.value   = 0.08;
    limiter.connect(masterGain);

    // 3-band main EQ chain: eqLow → eqMid → eqHigh → limiter
    eqHigh = actx.createBiquadFilter();
    eqHigh.type = 'highshelf';
    eqHigh.frequency.value = 4000;
    eqHigh.gain.value = P.eqHigh;
    eqHigh.connect(limiter);

    eqMid = actx.createBiquadFilter();
    eqMid.type = 'peaking';
    eqMid.frequency.value = 1200;
    eqMid.Q.value = 1.0;
    eqMid.gain.value = P.eqMid;
    eqMid.connect(eqHigh);

    eqLow = actx.createBiquadFilter();
    eqLow.type = 'lowshelf';
    eqLow.frequency.value = 250;
    eqLow.gain.value = P.eqLow;
    eqLow.connect(eqMid);

    // Global delay output — all per-note delay chains converge here
    delayOutGain = actx.createGain();
    delayOutGain.gain.value = P.delayVol;
    delayOutGain.connect(eqLow);

    // Convolution reverb (bypasses limiter for natural tail)
    reverbConv = buildReverb(2.8, 2.5, false);
    reverbGain = actx.createGain();
    reverbGain.gain.value = P.reverbAmount;
    reverbConv.connect(reverbGain);
    reverbGain.connect(masterGain);
    eqHigh.connect(reverbConv);
    builtReverbReversed = false;
  }

  function buildReverb(duration, decay, reversed) {
    const len = Math.floor(actx.sampleRate * duration);
    const buf = actx.createBuffer(2, len, actx.sampleRate);
    for (let ch = 0; ch < 2; ch++) {
      const d = buf.getChannelData(ch);
      for (let i = 0; i < len; i++) {
        const envelope = reversed ? (i / len) : (1 - i / len);
        d[i] = (Math.random() * 2 - 1) * Math.pow(envelope, decay);
      }
    }
    const conv = actx.createConvolver();
    conv.buffer = buf;
    return conv;
  }

  function rebuildReverb() {
    if (!actx || builtReverbReversed === P.reverseEcho) return;
    try { eqHigh.disconnect(reverbConv); } catch (_) {}
    try { reverbConv.disconnect(reverbGain); } catch (_) {}
    reverbConv = buildReverb(2.8, 2.5, P.reverseEcho);
    eqHigh.connect(reverbConv);
    reverbConv.connect(reverbGain);
    builtReverbReversed = P.reverseEcho;
  }

  function syncAudioToParams() {
    if (!actx) return;
    const t = actx.currentTime;
    masterGain.gain.setTargetAtTime(P.volume, t, 0.05);
    eqLow.gain.setTargetAtTime(P.eqLow, t, 0.05);
    eqMid.gain.setTargetAtTime(P.eqMid, t, 0.05);
    eqHigh.gain.setTargetAtTime(P.eqHigh, t, 0.05);
    reverbGain.gain.setTargetAtTime(P.reverbAmount, t, 0.1);
    delayOutGain.gain.setTargetAtTime(P.delayVol, t, 0.05);
    rebuildReverb();
  }


  // ===========================================================================
  // NOTE PLAYBACK
  // ===========================================================================

  function stopAllNotes() {
    playGen++;
    const now = actx ? actx.currentTime : 0;

    for (const node of activeNodes) {
      try {
        node.fbGain.gain.cancelScheduledValues(now);
        node.fbGain.gain.setValueAtTime(0, now);
        node.fbGain.disconnect();
      } catch (_) {}
      try {
        node.vca.gain.cancelScheduledValues(now);
        node.vca.gain.setValueAtTime(0.001, now);
        node.vca.gain.exponentialRampToValueAtTime(0.0001, now + 0.04);
      } catch (_) {}
      try { node.osc.stop(now + 0.05); } catch (_) {}
      clearTimeout(node.timerId);

      setTimeout(() => {
        try {
          node.osc.disconnect();
          node.vca.disconnect();
          node.delayNode.disconnect();
          node.toneLPF.disconnect();
          node.dEqL.disconnect();
          node.dEqM.disconnect();
          node.dEqH.disconnect();
          node.fbGain.disconnect();
        } catch (_) {}
      }, 200);
    }
    activeNodes = [];
    cascadeLines.length = 0;
  }

  function playNote(midiNote, startOffsetSec, gen) {
    if (!actx || gen !== playGen) return;

    const freq = 440 * Math.pow(2, (midiNote - 69) / 12);
    const t0   = actx.currentTime + startOffsetSec;
    const durS = P.noteDuration / 1000;
    const atkS = Math.min(0.06, durS * 0.15);
    const peak = 0.22 / Math.max(1, P.numNotes * 0.65);

    // Oscillator
    const osc = actx.createOscillator();
    osc.type = 'sine';
    osc.frequency.value = freq;
    osc.detune.value = (Math.random() - 0.5) * 7;

    // ADSR envelope
    const vca = actx.createGain();
    vca.gain.setValueAtTime(0.0001, t0);
    vca.gain.exponentialRampToValueAtTime(peak, t0 + atkS);
    vca.gain.setValueAtTime(peak, t0 + durS * 0.7);
    vca.gain.exponentialRampToValueAtTime(0.0001, t0 + durS);

    osc.connect(vca);
    vca.connect(eqLow);

    // Per-note delay chain with feedback loop
    const delayTimeSec = P.delayTime / 1000;
    const delayNode = actx.createDelay(6.0);
    delayNode.delayTime.value = delayTimeSec;

    const toneLPF = actx.createBiquadFilter();
    toneLPF.type = 'lowpass';
    toneLPF.frequency.value = 180 + (P.delayTone / 100) * 7500;

    const dEqL = actx.createBiquadFilter();
    dEqL.type = 'lowshelf';  dEqL.frequency.value = 250;  dEqL.gain.value = P.delayEqLow;
    const dEqM = actx.createBiquadFilter();
    dEqM.type = 'peaking';   dEqM.frequency.value = 1200; dEqM.Q.value = 1.0; dEqM.gain.value = P.delayEqMid;
    const dEqH = actx.createBiquadFilter();
    dEqH.type = 'highshelf'; dEqH.frequency.value = 4000; dEqH.gain.value = P.delayEqHigh;

    const fb = Math.min(0.76, P.delayFeedback);
    const fbGain = actx.createGain();
    fbGain.gain.value = fb;

    // Route: vca → delay → tone → dEqL → dEqM → dEqH → fbGain ⟲ delay
    //                                                   ↘ delayOutGain → main EQ
    vca.connect(delayNode);
    delayNode.connect(toneLPF);
    toneLPF.connect(dEqL);
    dEqL.connect(dEqM);
    dEqM.connect(dEqH);
    dEqH.connect(fbGain);
    fbGain.connect(delayNode);
    dEqH.connect(delayOutGain);

    // Schedule feedback decay so echoes die naturally
    const logFb     = fb > 0.01 ? Math.log(fb) : -10;
    const echoDecay = Math.min(8, Math.abs(Math.log(0.001) / logFb) * delayTimeSec);
    const stopAt    = t0 + durS + echoDecay + 0.2;

    fbGain.gain.setValueAtTime(fb, t0);
    fbGain.gain.exponentialRampToValueAtTime(0.0001, stopAt - 0.2);

    osc.start(t0);
    try { osc.stop(t0 + durS + 0.1); } catch (_) {}

    // Deferred cleanup
    const captGen = gen;
    const cleanMs = Math.max(200, (stopAt - actx.currentTime) * 1000 + 400);
    const timerId = setTimeout(() => {
      if (captGen !== playGen) return;
      try {
        osc.disconnect(); vca.disconnect(); delayNode.disconnect();
        toneLPF.disconnect(); dEqL.disconnect(); dEqM.disconnect();
        dEqH.disconnect(); fbGain.disconnect();
      } catch (_) {}
      activeNodes = activeNodes.filter(n => n.osc !== osc);
    }, cleanMs);

    activeNodes.push({ osc, vca, fbGain, delayNode, toneLPF, dEqL, dEqM, dEqH, timerId, gen });
  }


  // ===========================================================================
  // SCALE & NOTE LOGIC
  // ===========================================================================

  function getScaleIntervals() {
    return SCALES[P.scale]?.intervals || SCALES.pentatonic.intervals;
  }

  function getAllScaleNotes() {
    const intervals = getScaleIntervals();
    const root  = getRootMidi();
    const notes = [];

    for (let oct = 0; oct <= P.octaveRange; oct++) {
      for (const iv of intervals) {
        const midi = root + oct * 12 + iv;
        if (midi >= 36 && midi <= 96 && midi <= root + P.octaveRange * 12) {
          notes.push(midi);
        }
      }
    }
    return [...new Set(notes)].sort((a, b) => a - b);
  }

  function getScaleLedSet() {
    const intervals = getScaleIntervals();
    const root = getRootMidi();
    return new Set(intervals.map(iv => (root + iv) % 12));
  }

  function getActiveNotes() {
    const all = getAllScaleNotes();
    if (!all.length) return [];

    const rotIdx = Math.floor(rotation * all.length) % all.length;
    const count  = Math.min(P.numNotes, all.length);
    const step   = Math.max(1, Math.floor(all.length / count));
    const notes  = [];

    for (let i = 0; i < count; i++) {
      notes.push(all[(rotIdx + i * step) % all.length]);
    }
    return notes;
  }


  // ===========================================================================
  // RANDOM NOTE PICKING
  // ===========================================================================

  function pickRandomNotes() {
    const all = getAllScaleNotes();
    if (!all.length) { P.pickedNotes = []; renderPickedNotes(); return; }
    P.pickedNotes = [];
    for (let i = 0; i < P.numNotes; i++) {
      P.pickedNotes.push(pick(all));
    }
    renderPickedNotes();
  }

  function renderPickedNotes() {
    const container = $('picked-notes');
    if (!container) return;

    if (P.direction !== 'rand' || !P.pickedNotes.length) {
      container.style.display = 'none';
      return;
    }

    container.style.display = 'flex';
    const notesHtml = P.pickedNotes.map(midi =>
      `<span class="picked-note">${midiToName(midi)}</span>`
    ).join('');

    container.innerHTML =
      `<div class="picked-note-list">${notesHtml}</div>` +
      `<button class="picked-dice-btn" id="dice-notes-btn" aria-label="Randomize notes">🎲</button>`;
  }


  // ===========================================================================
  // PLAY ENGINE
  // ===========================================================================

  function playNotesOnly() {
    initAudio();
    stopAllNotes();

    const gen = playGen;
    let ordered;

    if (P.direction === 'rand' && P.pickedNotes && P.pickedNotes.length) {
      ordered = [...P.pickedNotes];
    } else {
      const notes = getActiveNotes();
      ordered = [...notes].sort((a, b) => a - b);
      if (P.direction === 'desc') ordered.reverse();
    }

    const spacingMs = getSpacingMs();

    for (let i = 0; i < ordered.length; i++) {
      playNote(ordered[i], (i * spacingMs) / 1000, gen);

      // Fire LED when the note actually sounds
      const midi    = ordered[i];
      const delayMs = i * spacingMs;
      setTimeout(() => {
        if (gen !== playGen) return;
        activeLedExpiry[midi % 12] = Date.now() + P.noteDuration + 600;
        spawnParticles(midi % 12);
      }, delayMs);

      // Cascade line from previous note
      if (i > 0) {
        const fromMidi = ordered[i - 1];
        setTimeout(() => {
          if (gen !== playGen) return;
          cascadeLines.push({ fromIdx: fromMidi % 12, toIdx: midi % 12, bornAt: Date.now() });
        }, delayMs);
      }
    }

    // Brief button flash
    const btn = $('play-btn');
    btn.classList.add('pressed');
    setTimeout(() => { if (!isHeld) btn.classList.remove('pressed'); }, 100);
  }

  function playCluster() {
    if (P.wildMode) wildRandomize();
    else smartRandomize();

    rotation = Math.random();
    syncAudioToParams();
    syncUIToParams();
    addToRecentPlays();
    playNotesOnly();
  }

  /**
   * Play a sound from saved params without changing P or the UI.
   * All audio reads happen synchronously in playNotesOnly/playNote,
   * so we can swap P, play, and restore immediately.
   */
  function previewSound(params) {
    const snapshot = {};
    for (const k of SHARE_KEYS) snapshot[k] = P[k];

    for (const k of SHARE_KEYS) {
      if (k in params) P[k] = params[k];
    }

    initAudio();
    syncAudioToParams();
    rotation = Math.random();
    playNotesOnly();

    // Restore P — audio nodes keep the preview values until next play
    for (const k of SHARE_KEYS) P[k] = snapshot[k];
  }


  // ===========================================================================
  // RANDOMIZERS
  // ===========================================================================

  function smartRandomize() {
    P.scale       = pick(NICE_SCALES);
    P.rootNoteIdx = randInt(0, 11);
    P.octave      = randInt(3, 4);
    P.numNotes    = randInt(4, 7);
    P.octaveRange = randInt(1, 2);
    P.bpm         = 60 + Math.floor(Math.random() * 24) * 5;
    P.noteDiv     = pick(NICE_DIVS);
    P.direction   = pick(['asc', 'desc', 'rand']);

    const spacingMs = Math.round((60 / P.bpm) * P.noteDiv * 1000);
    P.noteDuration  = clamp(Math.round(spacingMs * (1.5 + Math.random() * 1.5)), 150, 1200);

    const beatMs     = Math.round((60 / P.bpm) * 1000);
    const delayFracs = [0.5, 0.333, 0.25, 0.75, 0.667, 0.125];
    P.delayTime     = clamp(Math.round(beatMs * pick(delayFracs)), 80, 800);
    P.delayFeedback = 0.2 + Math.random() * 0.38;
    P.delayVol      = 0.5 + Math.random() * 0.5;
    P.delayTone     = randInt(20, 80);
    P.reverbAmount  = 0.3 + Math.random() * 0.45;

    P.eqLow      = Math.round((Math.random() - 0.5) * 8);
    P.eqMid      = Math.round((Math.random() - 0.5) * 6);
    P.eqHigh     = Math.round((Math.random() - 0.5) * 8);
    P.delayEqLow = 0;
    P.delayEqMid = 0;
    P.delayEqHigh = 0;

    P.reverseEcho = Math.random() < 0.35;

    if (P.direction === 'rand') pickRandomNotes();
  }

  function wildRandomize() {
    const allKeys = Object.keys(SCALES);
    P.scale       = pick(allKeys);
    P.rootNoteIdx = randInt(0, 11);
    P.octave      = randInt(2, 5);
    P.numNotes    = randInt(2, 8);
    P.octaveRange = randInt(1, 3);
    P.bpm         = 60 + Math.floor(Math.random() * 24) * 5;
    P.noteDiv     = pick(ALL_DIVS);
    P.noteDuration = randInt(80, 2000);
    P.direction   = pick(['asc', 'desc', 'rand']);

    P.delayTime     = randInt(30, 900);
    P.delayFeedback = Math.random() * 0.77;
    P.delayVol      = 0.3 + Math.random() * 0.7;
    P.delayTone     = randInt(0, 100);
    P.reverbAmount  = Math.random() * 0.95;

    P.eqLow       = Math.round((Math.random() - 0.5) * 24);
    P.eqMid       = Math.round((Math.random() - 0.5) * 16);
    P.eqHigh      = Math.round((Math.random() - 0.5) * 24);
    P.delayEqLow  = Math.round((Math.random() - 0.5) * 16);
    P.delayEqMid  = Math.round((Math.random() - 0.5) * 12);
    P.delayEqHigh = Math.round((Math.random() - 0.5) * 16);

    P.reverseEcho = Math.random() < 0.5;

    if (P.direction === 'rand') pickRandomNotes();
  }


  // ===========================================================================
  // HOLD / LOOP MODE
  // ===========================================================================

  function holdLoopMs() {
    return Math.max(400, getSpacingMs() * P.numNotes);
  }

  function scheduleHoldLoop() {
    clearTimeout(holdTimer);
    holdTimer = setTimeout(() => {
      if (!isHeld) return;
      playNotesOnly();
      scheduleHoldLoop();
    }, holdLoopMs());
  }

  function startHold() {
    if (isHeld) return;
    isHeld = true;
    $('play-btn').classList.add('held', 'pressed');
    if (P.autoRandomize) playCluster();
    else playNotesOnly();
    scheduleHoldLoop();
  }

  function endHold() {
    if (!isHeld) return;
    isHeld = false;
    clearTimeout(holdTimer);
    holdTimer = null;
    stopAllNotes();
    $('play-btn').classList.remove('held', 'pressed');
  }


  // ===========================================================================
  // CANVAS VISUALIZATION
  // ===========================================================================

  function resizeCanvas() {
    const rect = canvas.parentElement.getBoundingClientRect();
    canvasW = canvas.width  = rect.width;
    canvasH = canvas.height = rect.height;
  }

  function getLEDPositions() {
    const cx = canvasW / 2;
    const cy = canvasH / 2;
    const r  = Math.min(canvasW, canvasH) * 0.38;
    return Array.from({ length: LED_COUNT }, (_, i) => {
      const angle = (i / LED_COUNT) * Math.PI * 2 - Math.PI / 2 + visualAngle;
      return { x: cx + Math.cos(angle) * r, y: cy + Math.sin(angle) * r, hue: (i / LED_COUNT) * 360 };
    });
  }

  function spawnParticles(ledIdx) {
    const pos = getLEDPositions()[ledIdx];
    const cx  = canvasW / 2, cy = canvasH / 2;
    const outAngle = Math.atan2(pos.y - cy, pos.x - cx);
    const count    = randInt(4, 8);

    for (let i = 0; i < count; i++) {
      const spread = (Math.random() - 0.5) * Math.PI * 0.9;
      const speed  = 1.5 + Math.random() * 4.5;
      particles.push({
        x: pos.x, y: pos.y,
        vx: Math.cos(outAngle + spread) * speed,
        vy: Math.sin(outAngle + spread) * speed,
        life: 1.0,
        decay: 0.014 + Math.random() * 0.022,
        size: 1.5 + Math.random() * 4,
        hue: pos.hue + (Math.random() - 0.5) * 50,
      });
    }
  }

  function drawFrame(timestamp) {
    const dt = Math.min(0.05, (timestamp - lastFrameTime) / 1000);
    lastFrameTime = timestamp;

    // Visual ring rotation tied to BPM (note selection uses `rotation` separately)
    const cycleRate = (P.bpm / 60) / 32;
    visualAngle += (P.reverseEcho ? -1 : 1) * cycleRate * Math.PI * 2 * dt;

    // Fade background
    ctx2d.fillStyle = 'rgba(6, 6, 16, 0.2)';
    ctx2d.fillRect(0, 0, canvasW, canvasH);

    const now       = Date.now();
    const positions = getLEDPositions();
    const scaleSet  = getScaleLedSet();

    // Update LED brightness
    for (let i = 0; i < LED_COUNT; i++) {
      const playing = activeLedExpiry[i] && now < activeLedExpiry[i];
      const target  = playing ? 1.0 : scaleSet.has(i) ? 0.22 : 0.04;
      ledBright[i] += (target - ledBright[i]) * dt * (playing ? 12 : 4);
      ledBright[i]  = clamp(ledBright[i], 0, 1);
    }

    drawScalePolygon(positions, scaleSet, timestamp);
    drawCascadeLines(positions, now);
    drawLEDs(positions);
    drawCenterHalo(now);
    drawParticles();

    requestAnimationFrame(drawFrame);
  }

  function drawScalePolygon(positions, scaleSet, timestamp) {
    const arr = [...scaleSet].sort((a, b) => a - b);
    if (arr.length < 2) return;

    const waveFreq = 0.35 + (1 - P.reverbAmount) * 0.7;
    const timeSec  = timestamp * 0.001;

    for (let i = 0; i < arr.length; i++) {
      const ai = arr[i];
      const bi = arr[(i + 1) % arr.length];
      const pa = positions[ai];
      const pb = positions[bi];
      const avg = (ledBright[ai] + ledBright[bi]) * 0.5;
      const alpha = 0.07 + avg * 0.28;

      // Wavy bezier: midpoint offset perpendicular to the line, driven by reverb
      const mx = (pa.x + pb.x) / 2, my = (pa.y + pb.y) / 2;
      const dx = pb.x - pa.x,       dy = pb.y - pa.y;
      const len = Math.sqrt(dx * dx + dy * dy) || 1;
      const nx = -dy / len, ny = dx / len;
      const amp   = 12 * P.reverbAmount * (0.25 + avg * 0.75);
      const phase = timeSec * waveFreq + ai * 0.85;
      const cpx = mx + nx * Math.sin(phase) * amp;
      const cpy = my + ny * Math.sin(phase) * amp;

      const grad = ctx2d.createLinearGradient(pa.x, pa.y, pb.x, pb.y);
      grad.addColorStop(0, `hsla(${pa.hue}, 100%, 65%, ${alpha})`);
      grad.addColorStop(1, `hsla(${pb.hue}, 100%, 65%, ${alpha})`);

      ctx2d.strokeStyle = grad;
      ctx2d.lineWidth = 0.7 + avg * 1.8;
      ctx2d.beginPath();
      ctx2d.moveTo(pa.x, pa.y);
      ctx2d.quadraticCurveTo(cpx, cpy, pb.x, pb.y);
      ctx2d.stroke();
    }
  }

  function drawCascadeLines(positions, now) {
    const LIFE = 700;
    for (let i = cascadeLines.length - 1; i >= 0; i--) {
      const cl  = cascadeLines[i];
      const age = now - cl.bornAt;
      if (age > LIFE) { cascadeLines.splice(i, 1); continue; }

      const t  = 1 - age / LIFE;
      const pa = positions[cl.fromIdx];
      const pb = positions[cl.toIdx];

      const grad = ctx2d.createLinearGradient(pa.x, pa.y, pb.x, pb.y);
      grad.addColorStop(0, `hsla(${pa.hue}, 100%, 80%, ${t * 0.95})`);
      grad.addColorStop(1, `hsla(${pb.hue}, 100%, 80%, ${t * 0.95})`);

      ctx2d.strokeStyle = grad;
      ctx2d.lineWidth   = 1.5 + t * 3;
      ctx2d.shadowColor = `hsla(${(pa.hue + pb.hue) / 2}, 100%, 70%, ${t * 0.6})`;
      ctx2d.shadowBlur  = 8 + t * 12;
      ctx2d.beginPath();
      ctx2d.moveTo(pa.x, pa.y);
      ctx2d.lineTo(pb.x, pb.y);
      ctx2d.stroke();
      ctx2d.shadowBlur  = 0;
      ctx2d.shadowColor = 'transparent';
    }
  }

  function drawLEDs(positions) {
    for (let i = 0; i < LED_COUNT; i++) {
      const { x, y, hue } = positions[i];
      const b = ledBright[i];
      const r = 4 + b * 9;

      // Bloom glow
      if (b > 0.08) {
        const bloomR = r * (b > 0.5 ? 6 : 4);
        const bloom  = ctx2d.createRadialGradient(x, y, 0, x, y, bloomR);
        bloom.addColorStop(0,   `hsla(${hue}, 100%, 75%, ${b * 0.55})`);
        bloom.addColorStop(0.5, `hsla(${hue}, 100%, 60%, ${b * 0.18})`);
        bloom.addColorStop(1,   `hsla(${hue}, 100%, 50%, 0)`);
        ctx2d.fillStyle = bloom;
        ctx2d.beginPath();
        ctx2d.arc(x, y, bloomR, 0, Math.PI * 2);
        ctx2d.fill();
      }

      // Core
      const core = ctx2d.createRadialGradient(x - r * 0.2, y - r * 0.2, 0, x, y, r);
      core.addColorStop(0, `hsla(${hue}, 80%, ${45 + b * 48}%, ${0.4 + b * 0.6})`);
      core.addColorStop(1, `hsla(${hue}, 100%, ${18 + b * 32}%, ${0.3 + b * 0.7})`);
      ctx2d.fillStyle = core;
      ctx2d.beginPath();
      ctx2d.arc(x, y, r, 0, Math.PI * 2);
      ctx2d.fill();

      // Specular highlight
      if (b > 0.15) {
        ctx2d.fillStyle = `rgba(255, 255, 255, ${b * 0.3})`;
        ctx2d.beginPath();
        ctx2d.arc(x - r * 0.22, y - r * 0.28, r * 0.28, 0, Math.PI * 2);
        ctx2d.fill();
      }
    }
  }

  function drawCenterHalo(now) {
    const maxB = Math.max(0.05, ...Object.entries(activeLedExpiry)
      .filter(([, exp]) => now < exp)
      .map(([i]) => ledBright[i] || 0));

    if (maxB <= 0.1) return;

    const hr = Math.min(canvasW, canvasH) * 0.15;
    const cx = canvasW / 2, cy = canvasH / 2;
    const halo = ctx2d.createRadialGradient(cx, cy, 0, cx, cy, hr);
    halo.addColorStop(0,   `rgba(200, 100, 255, ${maxB * 0.16})`);
    halo.addColorStop(0.5, `rgba(140, 60, 255, ${maxB * 0.07})`);
    halo.addColorStop(1,   'rgba(100, 30, 200, 0)');
    ctx2d.fillStyle = halo;
    ctx2d.beginPath();
    ctx2d.arc(cx, cy, hr, 0, Math.PI * 2);
    ctx2d.fill();
  }

  function drawParticles() {
    ctx2d.save();
    for (let i = particles.length - 1; i >= 0; i--) {
      const p = particles[i];
      p.x += p.vx;
      p.y += p.vy;
      p.vy += 0.055;
      p.vx *= 0.985;
      p.life -= p.decay;
      if (p.life <= 0) { particles.splice(i, 1); continue; }
      ctx2d.globalAlpha = p.life * p.life;
      ctx2d.fillStyle = `hsl(${p.hue}, 100%, 75%)`;
      ctx2d.beginPath();
      ctx2d.arc(p.x, p.y, p.size * p.life, 0, Math.PI * 2);
      ctx2d.fill();
    }
    ctx2d.restore();
  }


  // ===========================================================================
  // RECENT PLAYS
  // ===========================================================================

  function addToRecentPlays() {
    recentPlays.unshift({
      id:        Date.now(),
      name:      generateName(),
      scaleName: SCALES[P.scale]?.name || P.scale,
      rootName:  NOTE_NAMES[P.rootNoteIdx] + P.octave,
      params:    JSON.parse(JSON.stringify(P)),
    });
    if (recentPlays.length > 5) recentPlays.pop();
    renderRecentPlays();
  }

  function replayRecent(id) {
    const r = recentPlays.find(x => x.id === id);
    if (!r) return;
    previewSound(r.params);
  }

  function loadRecentById(id) {
    const r = recentPlays.find(x => x.id === id);
    if (!r) return;
    loadSound(r.params);
    showToast('Loaded: ' + r.name);
  }

  function saveRecentById(id) {
    const r = recentPlays.find(x => x.id === id);
    if (!r) return;
    const favs = getFavorites();
    favs.unshift({
      id: Date.now(),
      name: r.name,
      params: r.params,
      createdAt: new Date().toISOString(),
    });
    if (favs.length > 30) favs.length = 30;
    saveFavorites(favs);
    renderSoundBank();
    showToast('Saved: ' + r.name);
  }

  function renderRecentPlays() {
    const list = $('recent-list');
    if (!recentPlays.length) {
      list.innerHTML = '<p class="empty-bank">Hit PLAY to start sparkling...</p>';
      return;
    }
    list.innerHTML = recentPlays.map(r => {
      const name = escapeHtml(r.name);
      const bpm  = r.params?.bpm ?? P.bpm;
      const div  = getNoteDivLabel(r.params?.noteDiv ?? P.noteDiv);
      return `
        <div class="recent-card" data-id="${r.id}">
          <div class="recent-info">
            <span class="recent-name">${name}</span>
            <span class="recent-meta">${r.rootName} ${r.scaleName} · ${bpm}bpm ${div}</span>
          </div>
          <div class="recent-actions">
            <button class="recent-play-btn" data-action="replay" aria-label="Play">▶</button>
            <button class="recent-load-btn" data-action="load" aria-label="Load">LOAD</button>
            <button class="recent-save-btn" data-action="save" aria-label="Save">💾</button>
            <button class="recent-save-btn" data-action="share" aria-label="Share">🔗</button>
          </div>
        </div>`;
    }).join('');
  }


  // ===========================================================================
  // FAVORITES / SOUND BANK
  // ===========================================================================

  function getFavorites() {
    try { return JSON.parse(localStorage.getItem(STORAGE_KEY) || '[]'); }
    catch (_) { return []; }
  }

  function saveFavorites(favs) {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(favs));
  }

  function loadSound(savedParams) {
    Object.assign(P, savedParams);
    P.autoRandomize = false;
    syncAudioToParams();
    syncUIToParams();
  }

  function deleteSavedSound(id) {
    saveFavorites(getFavorites().filter(f => f.id !== id));
    renderSoundBank();
  }

  function renameSavedSound(id) {
    const favs = getFavorites();
    const f = favs.find(x => x.id === id);
    if (!f) return;
    const n = prompt('Rename sound:', f.name);
    if (n && n.trim()) {
      f.name = n.trim();
      saveFavorites(favs);
      renderSoundBank();
    }
  }

  function loadSoundById(id) {
    const f = getFavorites().find(x => x.id === id);
    if (f) {
      loadSound(f.params);
      showToast('Loaded: ' + f.name);
    }
  }

  function loadAndPlay(id) {
    const f = getFavorites().find(x => x.id === id);
    if (!f) return;
    previewSound(f.params);
  }

  function renderSoundBank() {
    const list = $('favorites-list');
    const favs = getFavorites();
    $('bank-count').textContent = favs.length + ' saved';

    if (!favs.length) {
      list.innerHTML = '<p class="empty-bank">No saved sounds. Hit 💾 on a recent play to save it.</p>';
      return;
    }

    list.innerHTML = favs.map(f => {
      const scale   = SCALES[f.params?.scale]?.name || '?';
      const rootIdx = f.params?.rootNoteIdx ?? 0;
      const oct     = f.params?.octave ?? 4;
      const root    = NOTE_NAMES[rootIdx] + oct;
      const date    = new Date(f.createdAt).toLocaleDateString();
      const name    = escapeHtml(f.name);
      return `
        <div class="sound-card" data-id="${f.id}">
          <div class="sound-header">
            <span class="sound-name" title="${name}">${name}</span>
            <button class="sound-icon-btn" data-action="share" aria-label="Share">🔗</button>
            <button class="sound-icon-btn" data-action="rename" aria-label="Rename">✏</button>
            <button class="sound-icon-btn" data-action="delete" aria-label="Delete">✕</button>
          </div>
          <div class="sound-meta">${root} ${scale} · ${date}</div>
          <div class="sound-actions">
            <button class="sound-play-btn" data-action="play">▶ PLAY</button>
            <button class="sound-load-btn" data-action="load">LOAD</button>
          </div>
        </div>`;
    }).join('');
  }


  // ===========================================================================
  // SHARE / URL
  // ===========================================================================

  function shareParams(params) {
    const data = {};
    for (const k of SHARE_KEYS) {
      if (k in params) data[k] = params[k];
    }
    const encoded = btoa(JSON.stringify(data));
    const url = location.origin + location.pathname + '?s=' + encoded;

    navigator.clipboard.writeText(url)
      .then(() => showToast('🔗 link copied!'))
      .catch(() => { try { prompt('Copy this link:', url); } catch (_) {} });
  }

  function loadFromURL() {
    try {
      const s = new URLSearchParams(location.search).get('s');
      if (!s) return false;
      const data = JSON.parse(atob(s));
      for (const k of SHARE_KEYS) {
        if (k in data) P[k] = data[k];
      }
      return true;
    } catch (_) { return false; }
  }


  // ===========================================================================
  // UI: SYNC & BIND
  // ===========================================================================

  function setAutoRandomize(val) {
    if (P.autoRandomize === val) return;
    P.autoRandomize = val;

    const btn = $('auto-btn');
    if (btn) {
      btn.dataset.active = String(val);
      btn.querySelector('.tgl-state').textContent = val ? 'ON' : 'OFF';
    }

    const subLabel = $('btn-sub-label');
    if (subLabel) {
      subLabel.classList.add('fade-swap');
      setTimeout(() => {
        subLabel.textContent = val ? 'click to sparkle' : '▶ play your mix';
        subLabel.classList.remove('fade-swap');
      }, 150);
    }

    showToast(val ? '🎲 auto on — every press unique' : '✏ manual — play repeats your mix');
  }

  function syncUIToParams() {
    const set = (id, v) => { const e = $(id); if (e) e.value = v; };
    const txt = (id, v) => { const e = $(id); if (e) e.textContent = v; };

    set('scale-select',     P.scale);
    set('root-note-select', P.rootNoteIdx);
    set('octave-select',    P.octave);
    set('direction-select', P.direction);
    set('note-div-select',  P.noteDiv);

    set('sl-notes',     P.numNotes);     txt('v-notes',     P.numNotes);
    set('sl-oct-range', P.octaveRange);  txt('v-oct-range', P.octaveRange);
    set('sl-bpm',       P.bpm);          txt('v-bpm',       P.bpm);
    set('sl-dur',       P.noteDuration); txt('v-dur',       P.noteDuration);

    set('sl-reverb',    Math.round(P.reverbAmount * 100));   txt('v-reverb',    Math.round(P.reverbAmount * 100));
    set('sl-delay',     P.delayTime);                         txt('v-delay',     P.delayTime);
    set('sl-feedback',  Math.round(P.delayFeedback * 100));   txt('v-feedback',  Math.round(P.delayFeedback * 100));
    set('sl-delay-vol', Math.round(P.delayVol * 100));        txt('v-delay-vol', Math.round(P.delayVol * 100));
    set('sl-tone',      P.delayTone);                         txt('v-tone',      P.delayTone);
    set('sl-vol',       Math.round(P.volume * 100));           txt('v-vol',       Math.round(P.volume * 100));

    set('sl-eq-low',   P.eqLow);   txt('v-eq-low',   P.eqLow);
    set('sl-eq-mid',   P.eqMid);   txt('v-eq-mid',   P.eqMid);
    set('sl-eq-high',  P.eqHigh);  txt('v-eq-high',  P.eqHigh);
    set('sl-deq-low',  P.delayEqLow);  txt('v-deq-low',  P.delayEqLow);
    set('sl-deq-mid',  P.delayEqMid);  txt('v-deq-mid',  P.delayEqMid);
    set('sl-deq-high', P.delayEqHigh); txt('v-deq-high', P.delayEqHigh);

    syncToggle('wild-btn',         P.wildMode);
    syncToggle('reverse-echo-btn', P.reverseEcho);
    syncToggle('auto-btn',         P.autoRandomize);

    renderPickedNotes();

    const subLabel = $('btn-sub-label');
    if (subLabel && !isHeld) {
      subLabel.textContent = P.autoRandomize ? 'click to sparkle' : '▶ play your mix';
    }
  }

  function syncToggle(id, active) {
    const el = $(id);
    if (!el) return;
    el.dataset.active = String(active);
    el.querySelector('.tgl-state').textContent = active ? 'ON' : 'OFF';
  }

  function bindSlider(slId, key, valId, transform, onChange) {
    const sl = $(slId);
    if (!sl) return;
    const vl = $(valId);
    sl.addEventListener('input', e => {
      P[key] = transform(e.target.value);
      if (vl) vl.textContent = e.target.value;
      setAutoRandomize(false);
      if (onChange) onChange();
    });
  }

  function populateDropdowns() {
    const scaleEl = $('scale-select');
    for (const [k, v] of Object.entries(SCALES)) {
      const o = document.createElement('option');
      o.value = k;
      o.textContent = v.name;
      scaleEl.appendChild(o);
    }

    const noteEl = $('root-note-select');
    NOTE_NAMES.forEach((name, i) => {
      const o = document.createElement('option');
      o.value = i;
      o.textContent = name;
      if (i === P.rootNoteIdx) o.selected = true;
      noteEl.appendChild(o);
    });

    const octEl = $('octave-select');
    for (let oct = 2; oct <= 6; oct++) {
      const o = document.createElement('option');
      o.value = oct;
      o.textContent = oct;
      if (oct === P.octave) o.selected = true;
      octEl.appendChild(o);
    }
  }


  // ===========================================================================
  // EVENT DELEGATION
  // ===========================================================================

  function setupDelegatedEvents() {
    // Recent plays — delegate clicks on action buttons
    $('recent-list').addEventListener('click', e => {
      const btn = e.target.closest('[data-action]');
      if (!btn) return;
      const card = btn.closest('[data-id]');
      if (!card) return;
      const id = parseInt(card.dataset.id);

      switch (btn.dataset.action) {
        case 'replay': replayRecent(id); break;
        case 'load':   loadRecentById(id); break;
        case 'save':   saveRecentById(id); break;
        case 'share': {
          const r = recentPlays.find(x => x.id === id);
          if (r) shareParams(r.params);
          break;
        }
      }
    });

    // Sound bank — delegate clicks on action buttons
    $('favorites-list').addEventListener('click', e => {
      const btn = e.target.closest('[data-action]');
      if (!btn) return;
      const card = btn.closest('[data-id]');
      if (!card) return;
      const id = parseInt(card.dataset.id);

      switch (btn.dataset.action) {
        case 'play':   loadAndPlay(id); break;
        case 'load':   loadSoundById(id); break;
        case 'share': {
          const f = getFavorites().find(x => x.id === id);
          if (f) shareParams(f.params);
          break;
        }
        case 'rename': renameSavedSound(id); break;
        case 'delete': deleteSavedSound(id); break;
      }
    });
  }


  // ===========================================================================
  // INIT
  // ===========================================================================

  function bindAllUI() {
    populateDropdowns();
    syncUIToParams();

    // Dropdowns
    $('scale-select').addEventListener('change', e => { P.scale = e.target.value; setAutoRandomize(false); if (P.direction === 'rand') pickRandomNotes(); });
    $('root-note-select').addEventListener('change', e => { P.rootNoteIdx = parseInt(e.target.value); setAutoRandomize(false); if (P.direction === 'rand') pickRandomNotes(); });
    $('octave-select').addEventListener('change', e => { P.octave = parseInt(e.target.value); setAutoRandomize(false); if (P.direction === 'rand') pickRandomNotes(); });
    $('direction-select').addEventListener('change', e => { P.direction = e.target.value; setAutoRandomize(false); if (P.direction === 'rand') pickRandomNotes(); else renderPickedNotes(); });
    $('note-div-select').addEventListener('change', e => { P.noteDiv = parseFloat(e.target.value); setAutoRandomize(false); });

    // Sliders
    const int = v => parseInt(v);
    const pct = v => parseInt(v) / 100;

    bindSlider('sl-notes',     'numNotes',      'v-notes',     int, () => { if (P.direction === 'rand') pickRandomNotes(); });
    bindSlider('sl-oct-range', 'octaveRange',   'v-oct-range', int, () => { if (P.direction === 'rand') pickRandomNotes(); });
    bindSlider('sl-bpm',       'bpm',           'v-bpm',       int);
    bindSlider('sl-dur',       'noteDuration',  'v-dur',       int);
    bindSlider('sl-reverb',    'reverbAmount',  'v-reverb',    pct, () => { if (actx) reverbGain.gain.setTargetAtTime(P.reverbAmount, actx.currentTime, 0.1); });
    bindSlider('sl-delay',     'delayTime',     'v-delay',     int);
    bindSlider('sl-feedback',  'delayFeedback', 'v-feedback',  pct);
    bindSlider('sl-delay-vol', 'delayVol',      'v-delay-vol', pct, () => { if (actx) delayOutGain.gain.setTargetAtTime(P.delayVol, actx.currentTime, 0.05); });
    bindSlider('sl-tone',      'delayTone',     'v-tone',      int);
    bindSlider('sl-vol',       'volume',        'v-vol',       pct, () => { if (actx) masterGain.gain.setTargetAtTime(P.volume, actx.currentTime, 0.05); });
    bindSlider('sl-eq-low',    'eqLow',         'v-eq-low',    int, () => { if (actx) eqLow.gain.setTargetAtTime(P.eqLow, actx.currentTime, 0.05); });
    bindSlider('sl-eq-mid',    'eqMid',         'v-eq-mid',    int, () => { if (actx) eqMid.gain.setTargetAtTime(P.eqMid, actx.currentTime, 0.05); });
    bindSlider('sl-eq-high',   'eqHigh',        'v-eq-high',   int, () => { if (actx) eqHigh.gain.setTargetAtTime(P.eqHigh, actx.currentTime, 0.05); });
    bindSlider('sl-deq-low',   'delayEqLow',    'v-deq-low',   int);
    bindSlider('sl-deq-mid',   'delayEqMid',    'v-deq-mid',   int);
    bindSlider('sl-deq-high',  'delayEqHigh',   'v-deq-high',  int);

    // Toggle buttons
    $('hold-btn').addEventListener('click', () => {
      P.holdMode = !P.holdMode;
      syncToggle('hold-btn', P.holdMode);
      document.body.classList.toggle('hold-active', P.holdMode);
      if (P.holdMode) {
        initAudio();
        startHold();
        $('btn-sub-label').textContent = '⟳ looping';
      } else {
        endHold();
        $('btn-sub-label').textContent = P.autoRandomize ? 'click to sparkle' : '▶ play your mix';
      }
    });

    $('reverse-echo-btn').addEventListener('click', () => {
      P.reverseEcho = !P.reverseEcho;
      syncToggle('reverse-echo-btn', P.reverseEcho);
      rebuildReverb();
      setAutoRandomize(false);
      showToast(P.reverseEcho ? '↩ reverse echo on' : 'reverse echo off');
    });

    $('auto-btn').addEventListener('click', () => setAutoRandomize(!P.autoRandomize));

    $('wild-btn').addEventListener('click', () => {
      P.wildMode = !P.wildMode;
      syncToggle('wild-btn', P.wildMode);
      showToast(P.wildMode ? '🎲 wild mode: anything goes' : 'wild mode off: nice sounds only');
    });

    // Action buttons
    $('share-btn').addEventListener('click', () => shareParams(P));

    $('save-btn').addEventListener('click', () => {
      if (recentPlays.length > 0) saveRecentById(recentPlays[0].id);
      else showToast('Play a sound first!');
    });

    // Settings collapse
    const settingsBtn   = $('settings-btn');
    const settingsPanel = $('settings-panel');
    settingsBtn.classList.add('open');
    settingsBtn.addEventListener('click', () => {
      const open = settingsPanel.dataset.open === 'true';
      settingsPanel.dataset.open = String(!open);
      settingsBtn.textContent = open ? '▼ SETTINGS' : '▲ SETTINGS';
      settingsBtn.classList.toggle('open', !open);
    });

    // Play button
    const playBtn = $('play-btn');
    playBtn.addEventListener('click', () => {
      initAudio();
      if (P.autoRandomize) playCluster();
      else { syncAudioToParams(); playNotesOnly(); }
      if (P.holdMode) scheduleHoldLoop();
    });

    playBtn.addEventListener('touchstart', e => {
      e.preventDefault();
      playBtn.click();
    }, { passive: false });

    // Keyboard shortcuts
    window.addEventListener('keydown', e => {
      if (e.target.tagName === 'INPUT' || e.target.tagName === 'SELECT') return;
      if (e.code === 'Space') { e.preventDefault(); playBtn.click(); }
      if (e.code === 'KeyS' && recentPlays.length) saveRecentById(recentPlays[0].id);
      if (e.code === 'KeyH') $('hold-btn').click();
    });

    // Dice button for re-rolling random notes
    $('picked-notes').addEventListener('click', e => {
      if (e.target.closest('#dice-notes-btn')) {
        pickRandomNotes();
        setAutoRandomize(false);
      }
    });

    // Delegated events for dynamic lists
    setupDelegatedEvents();
  }

  document.addEventListener('DOMContentLoaded', () => {
    bindAllUI();

    if (loadFromURL()) {
      P.autoRandomize = false;
      syncUIToParams();
      syncAudioToParams();
      showToast('🔗 shared sound loaded — hit PLAY');
    }

    renderSoundBank();
    renderRecentPlays();
    resizeCanvas();
    window.addEventListener('resize', resizeCanvas);
    requestAnimationFrame(drawFrame);
  });

})();
