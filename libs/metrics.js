/*!
 * metrics.js — coleta de métricas de desempenho para WebAR (A-Frame vs Three.js)
 *
 * Um único arquivo, IDÊNTICO nas duas versões da aplicação. Não faz nada a menos
 * que a URL traga ?metrics=1 (ou ?marks=1), então pode ficar sempre incluído.
 *
 * Carregue DEPOIS do A-Frame / Three.js / AR.js:
 *   <script src="metrics.js"></script>
 *
 * Parâmetros de URL:
 *   metrics=1        ativa a coleta (passe A)
 *   marks=1          só grava performance.measure() das fases, para aparecerem na
 *                    linha do tempo do DevTools (passe B). Não calcula nada.
 *   scenario=C0      rótulo do cenário (C0, C1, C2, C3, init)
 *   version=aframe   rótulo da versão (padrão: aframe se houver AFRAME, senão threejs)
 *   run=01           número da repetição
 *   commit=abc123    commit publicado no GitHub Pages (vai para o JSON)
 *   warmup=5         segundos de aquecimento descartados      (padrão 5)
 *   duration=30      segundos de gravação                     (padrão 30)
 *   hz=60            taxa da tela usada para o prazo por quadro (padrão 60)
 *   autostart=1      inicia sozinho ~1 s depois do load (senão, toque em "Iniciar")
 *   ui=0             esconde o painel
 *   raw=1            inclui as amostras brutas no JSON
 *   passe=A          rótulo do passe, usado no nome do arquivo
 *
 * Saída: baixa  <version>_<scenario>_<passe>_<run>.json  e deixa o objeto em
 * window.ARMetrics.lastReport (e no console).
 *
 * Ganchos automáticos (A-Frame 1.3.0 + AR.js 3.4.5, conferidos no código-fonte):
 *   fase "tick"      scene.tick           componentes + sistemas do A-Frame
 *   fase "tracking"  arContext.update     rastreamento do AR.js (chamada interna do tick)
 *   fase "resize"    arSession.onResize   o sistema arjs chama isso a CADA quadro
 *   fase "render"    renderer.render
 * Versão Three.js: chame ARMetrics.hookThree({ renderer, arContext }) — ver exemplo no plano.
 */
(function () {
  'use strict';
  if (window.ARMetrics) return;

  /* ------------------------------------------------------------ configuração */
  var qs = new URLSearchParams(location.search);
  function num(v, d) { var n = parseFloat(v); return isFinite(n) && n > 0 ? n : d; }
  var CFG = {
    enabled: qs.get('metrics') === '1',
    marks: qs.get('marks') === '1',
    ui: qs.get('ui') !== '0',
    autostart: qs.get('autostart') === '1',
    passe: qs.get('passe') || 'A',
    scenario: qs.get('scenario') || 'C0',
    run: qs.get('run') || '01',
    commit: qs.get('commit') || '',
    warmup: num(qs.get('warmup'), 5),
    duration: num(qs.get('duration'), 30),
    hz: num(qs.get('hz'), 60),
    raw: qs.get('raw') === '1'
  };
  var ACTIVE = CFG.enabled || CFG.marks;

  /* API pública (esqueleto; é preenchida abaixo se ACTIVE) */
  var API = { config: CFG, active: ACTIVE, lastReport: null, state: 'idle' };
  window.ARMetrics = API;

  if (!ACTIVE) {              // sem parâmetros na URL: tudo vira no-op
    API.event = API.begin = API.end = API.nest = API.start = API.stop = function () {};
    API.hookThree = function () { return false; };
    API.phase = function (n, fn) { return fn; };
    return;
  }

  /* ------------------------------------------------------------- utilidades */
  var now = function () { return performance.now(); };
  function r(x, d) { if (x == null || !isFinite(x)) return null; var m = Math.pow(10, d == null ? 3 : d); return Math.round(x * m) / m; }
  function base(u) { try { return String(u).split('?')[0].split('/').slice(-1)[0] || String(u); } catch (e) { return ''; } }

  function stats(arr) {
    var n = arr.length; if (!n) return null;
    var a = Float64Array.from(arr).sort();
    var sum = 0, i; for (i = 0; i < n; i++) sum += a[i];
    var mean = sum / n, v = 0; for (i = 0; i < n; i++) v += (a[i] - mean) * (a[i] - mean);
    function q(p) { var k = (n - 1) * p, lo = Math.floor(k), hi = Math.ceil(k); return a[lo] + (a[hi] - a[lo]) * (k - lo); }
    return { n: n, mean: r(mean), sd: r(Math.sqrt(v / n)), min: r(a[0]), p50: r(q(0.5)), p95: r(q(0.95)), p99: r(q(0.99)), max: r(a[n - 1]), sum: r(sum) };
  }

  /* ----------------------------------------------------------------- estado */
  var CAP = 60000;                                  // amostras máximas por série
  var state = 'idle';                               // idle | warmup | recording | done
  var recStart = 0, recEnd = 0, recEpoch = 0, timers = [], rafId = 0;
  var frameTs = new Float64Array(CAP), nFrames = 0;
  var lagSamples = [], heapSeries = [], camSamples = [], lastCam = null, camVideo = null, camFound = false;
  var phases = {};                                  // nome -> {n,total,max,s:Float64Array,ns}
  var nest = { tracking: 'tick', resize: 'tick' };  // filho -> pai (tempo do filho está dentro do pai)
  var trackCalls = 0, trackDetect = 0, e2e = [], e2eRef = null, e2eBad = 0;
  var ltAll = [], loafAll = [];                     // long tasks / long animation frames (sempre observando)
  var evAll = [];                                   // eventos com tempo absoluto
  var batStart = null, batEnd = null, warnings = [];
  var liveFps = 0, liveLast = 0, liveCount = 0, hiddenDuring = false;

  /* ------------------------------------------------------------------ fases */
  function phaseObj(name) {
    return phases[name] || (phases[name] = { n: 0, total: 0, max: 0, s: new Float64Array(CAP), ns: 0 });
  }
  function rec(name, t0, t1) {
    var d = t1 - t0;
    if (CFG.marks) { try { performance.measure('arm:' + name, { start: t0, end: t1 }); } catch (e) {} }
    if (state !== 'recording') return;
    var p = phaseObj(name);
    p.n++; p.total += d; if (d > p.max) p.max = d;
    if (p.ns < CAP) p.s[p.ns++] = d;
  }
  /* Substitui obj[method] por uma versão que cronometra a chamada.
     defineProperty é necessário: o scene.tick do A-Frame é não-gravável no protótipo. */
  function wrap(obj, method, phase, onResult) {
    var orig = obj && obj[method];
    if (typeof orig !== 'function' || orig.__arm) return false;
    var w = function () {
      var t0 = now(), res;
      try { res = orig.apply(this, arguments); return res; }
      finally { var t1 = now(); rec(phase, t0, t1); if (onResult) onResult(res, t0, t1); }
    };
    w.__arm = true; w.__orig = orig;
    Object.defineProperty(obj, method, { value: w, writable: true, configurable: true, enumerable: true });
    return true;
  }
  function onTrackingResult(res, t0, t1) {            // res === true: o AR.js realmente processou o quadro
    if (state !== 'recording') return;
    trackCalls++;
    if (res === true) {
      trackDetect++; rec('tracking_detect', t0, t1);
      if (lastCam) {
        var ref = lastCam.capture != null ? lastCam.capture : lastCam.now;
        e2eRef = lastCam.capture != null ? 'captureTime' : 'rvfc_now';
        var d = t1 - ref;
        if (d >= 0 && d < 2000) e2e.push(d); else e2eBad++;
      }
    }
  }

  /* ---------------------------------------------------- ganchos A-Frame/AR.js */
  var hk = { scene: false, renderer: false, ar: false }, hookTries = 0, hookTimer = 0;
  function tryHookAFrame() {
    var A = window.AFRAME;
    if (!A || !A.scenes || !A.scenes.length) return false;
    var scene = A.scenes[0];
    if (!hk.scene) hk.scene = wrap(scene, 'tick', 'tick');
    if (!hk.renderer && scene.renderer) hk.renderer = wrap(scene.renderer, 'render', 'render');
    var sys = scene.systems && scene.systems.arjs;
    if (sys && sys._arSession && !hk.ar) {
      var s = sys._arSession;
      var a = s.arContext ? wrap(s.arContext, 'update', 'tracking', onTrackingResult) : false;
      var b = wrap(s, 'onResize', 'resize');
      hk.ar = a || b;
    }
    return hk.scene && hk.renderer && hk.ar;
  }
  function hookLoop() {
    if (!window.AFRAME) { if (++hookTries > 8) return; }      // página sem A-Frame: versão Three.js
    else if (tryHookAFrame() || ++hookTries > 240) { return; }
    hookTimer = setTimeout(hookLoop, 250);
  }

  /* ------------------------------------------------- observadores (sempre on) */
  try {
    new PerformanceObserver(function (l) {
      l.getEntries().forEach(function (e) { if (ltAll.length < 5000) ltAll.push({ s: e.startTime, d: e.duration }); });
    }).observe({ type: 'longtask', buffered: true });
  } catch (e) { API.noLongTask = true; }
  try {
    new PerformanceObserver(function (l) {
      l.getEntries().forEach(function (e) {
        if (loafAll.length >= 3000) return;
        loafAll.push({
          s: e.startTime, d: e.duration, block: e.blockingDuration, rs: e.renderStart, sl: e.styleAndLayoutStart,
          scripts: (e.scripts || []).map(function (c) {
            return { k: (c.invokerType || '') + '|' + (c.sourceFunctionName || c.invoker || '') + '|' + base(c.sourceURL),
                     d: c.duration, fl: c.forcedStyleAndLayoutDuration || 0 };
          })
        });
      });
    }).observe({ type: 'long-animation-frame', buffered: true });
  } catch (e) { API.noLoAF = true; }

  function pushEvent(name, id, src) { if (evAll.length < 2000) evAll.push({ t: now(), name: name, id: id || '', src: src || '' }); }
  function onMarker(ev) {
    var id = '', src = ev.target === window ? 'core' : 'el';
    try {
      if (src === 'core') { var p = ev.detail && ev.detail.parameters; id = p ? (p.patternUrl ? base(p.patternUrl) : (p.barcodeValue != null ? 'barcode' + p.barcodeValue : p.type)) : ''; }
      else { var t = ev.target; id = t.id || (t.getAttribute && (t.getAttribute('url') || t.getAttribute('value'))) || t.tagName; }
    } catch (e) {}
    pushEvent(ev.type, id, src);
  }
  ['markerFound', 'markerLost', 'camera-init', 'camera-error', 'renderstart', 'loaded'].forEach(function (n) {
    window.addEventListener(n, n.indexOf('marker') === 0 ? onMarker : function (e) { pushEvent(e.type, '', 'scene'); }, true);
  });
  document.addEventListener('visibilitychange', function () { if (state === 'recording' && document.hidden) hiddenDuring = true; });

  /* --------------------------------------------------------- amostradores */
  function frameLoop(t) {
    if (state !== 'warmup' && state !== 'recording') return;
    if (state === 'recording' && nFrames < CAP) frameTs[nFrames++] = t;
    liveCount++;
    rafId = requestAnimationFrame(frameLoop);
  }
  function ensureCam() {
    if (camFound) return;
    var v = document.getElementById('arjs-video') || document.querySelector('video');
    if (!v || typeof v.requestVideoFrameCallback !== 'function') return;
    camVideo = v; camFound = true;
    (function cb(t, md) {
      if (state === 'done' || state === 'idle') { camFound = false; return; }
      var c = (md && md.captureTime != null) ? md.captureTime : null;
      lastCam = { now: t, capture: c };
      if (state === 'recording' && camSamples.length < CAP)
        camSamples.push({ t: t, c: c, pf: md ? md.presentedFrames : null, w: md ? md.width : null, h: md ? md.height : null });
      camVideo.requestVideoFrameCallback(cb);
    })(now(), null);
  }
  function lagLoop() {                                // atraso do event loop: um timer de 10 ms que "atrasa" quando a thread está ocupada
    var last = now(), iv = 10;
    timers.push(setInterval(function () {
      var t = now(); var lag = t - last - iv; last = t;
      if (state === 'recording' && lagSamples.length < CAP) lagSamples.push(lag < 0 ? 0 : lag);
    }, iv));
  }
  function housekeeping() {                           // 1x por segundo: heap, câmera, painel, limpeza de measures
    ensureCam();
    var m = performance.memory;
    if (state === 'recording' && m) heapSeries.push(r(m.usedJSHeapSize / 1048576, 2));
    if (CFG.marks) { try { performance.clearMeasures(); } catch (e) {} }
    var t = now(); liveFps = liveCount * 1000 / (t - (liveLast || t - 1000)); liveCount = 0; liveLast = t;
    paintUI();
  }
  function battery() { return (navigator.getBattery ? navigator.getBattery().then(function (b) { return { level: b.level, charging: b.charging }; }, function () { return null; }) : Promise.resolve(null)); }

  /* --------------------------------------------------------------- ciclo */
  function start() {
    if (CFG.marks && !CFG.enabled) return;
    if (state !== 'idle' && state !== 'done') return;
    state = 'warmup'; API.state = state;
    nFrames = 0; lagSamples = []; heapSeries = []; camSamples = []; phases = {}; trackCalls = trackDetect = e2eBad = 0; e2e = []; hiddenDuring = false; warnings = [];
    camFound = false; liveLast = 0; liveCount = 0;
    battery().then(function (b) { batStart = b; });
    rafId = requestAnimationFrame(frameLoop);
    timers.push(setTimeout(beginRecord, CFG.warmup * 1000));
    paintUI();
  }
  function beginRecord() {
    nFrames = 0; lagSamples = []; heapSeries = []; camSamples = []; phases = {}; trackCalls = trackDetect = e2eBad = 0; e2e = [];
    recStart = now(); recEpoch = performance.timeOrigin + recStart;
    state = 'recording'; API.state = state;
    timers.push(setTimeout(finish, CFG.duration * 1000));
    paintUI();
  }
  function stop() { if (state === 'recording') finish(); else if (state === 'warmup') { cancel(); } }
  function cancel() { timers.forEach(function (t) { clearTimeout(t); }); cancelAnimationFrame(rafId); state = 'idle'; API.state = state; paintUI(); }
  function finish() {
    recEnd = now(); state = 'done'; API.state = state; cancelAnimationFrame(rafId);
    timers.forEach(function (t) { clearTimeout(t); }); timers = []; lagLoop.started = false;
    Promise.all([battery(), uaData()]).then(function (x) {
      batEnd = x[0];
      var rep = build(x[1]);
      API.lastReport = rep; paintUI();
      try { console.log('[ARMetrics] pronto', rep); } catch (e) {}
      download(rep);
    });
  }

  /* ------------------------------------------------------------- relatório */
  function uaData() {
    var u = navigator.userAgentData;
    if (!u || !u.getHighEntropyValues) return Promise.resolve(null);
    return u.getHighEntropyValues(['model', 'platformVersion', 'uaFullVersion']).then(function (v) { return v; }, function () { return null; });
  }
  function inWin(s) { return s >= recStart && s <= recEnd; }
  function build(uadata) {
    var wall = recEnd - recStart, budget = 1000 / CFG.hz, i;
    /* frames */
    var deltas = []; for (i = 1; i < nFrames; i++) deltas.push(frameTs[i] - frameTs[i - 1]);
    var ds = stats(deltas), jank = 0, severe = 0, dropped = 0, jit = 0;
    for (i = 0; i < deltas.length; i++) {
      if (deltas[i] > budget * 1.5) jank++;
      if (deltas[i] > budget * 3) severe++;
      dropped += Math.max(0, Math.round(deltas[i] / budget) - 1);
      if (i) jit += Math.abs(deltas[i] - deltas[i - 1]);
    }
    var refresh = ds ? 1000 / ds.p50 : null;
    if (refresh && Math.abs(refresh - CFG.hz) / CFG.hz > 0.1) warnings.push('taxa_de_quadros_estimada_' + r(refresh, 0) + 'Hz_difere_de_hz=' + CFG.hz + ' (fixe a tela em ' + CFG.hz + ' Hz ou ajuste o parametro hz)');
    if (nFrames < 10) warnings.push('poucos_quadros');
    if (hiddenDuring) warnings.push('aba_ficou_oculta_durante_a_gravacao');
    var frames = {
      n: nFrames, fps: nFrames > 1 ? r((nFrames - 1) * 1000 / (frameTs[nFrames - 1] - frameTs[0]), 2) : null,
      refresh_hz_est: r(refresh, 1), budget_ms: r(budget, 2), delta_ms: ds,
      jank_n: jank, jank_pct: r(deltas.length ? jank * 100 / deltas.length : 0, 2), severe_jank_n: severe,
      dropped_est: dropped, jitter_ms: r(deltas.length > 1 ? jit / (deltas.length - 1) : null),
      def: 'jank = quadro com intervalo > 1.5x o prazo; severo > 3x; dropped_est = soma(round(intervalo/prazo)-1); jitter = media de |delta_i - delta_(i-1)|'
    };
    frames.deltas_ms = deltas.map(function (x) { return r(x, 2); });
    /* tarefas longas */
    var lt = ltAll.filter(function (e) { return inWin(e.s); }), ltSum = 0, ltMax = 0;
    lt.forEach(function (e) { ltSum += e.d; if (e.d > ltMax) ltMax = e.d; });
    var longtasks = { supported: !API.noLongTask, threshold_ms: 50, n: lt.length, total_ms: r(ltSum), max_ms: r(ltMax),
                      items: lt.slice(0, 200).map(function (e) { return { start_ms: r(e.s - recStart, 1), dur_ms: r(e.d, 1) }; }) };
    /* long animation frames (com atribuição por script) */
    var lf = loafAll.filter(function (e) { return inWin(e.s); }), agg = {}, forced = 0, blk = 0, lsum = 0;
    lf.forEach(function (e) {
      lsum += e.d; blk += e.block || 0;
      e.scripts.forEach(function (c) { var a = agg[c.k] || (agg[c.k] = { n: 0, ms: 0, forced_ms: 0 }); a.n++; a.ms += c.d; a.forced_ms += c.fl; forced += c.fl; });
    });
    var top = Object.keys(agg).map(function (k) { return { script: k, n: agg[k].n, ms: r(agg[k].ms, 1), forced_layout_ms: r(agg[k].forced_ms, 1) }; })
      .sort(function (a, b) { return b.ms - a.ms; }).slice(0, 15);
    var loaf = { supported: !API.noLoAF, threshold_ms: 50, n: lf.length, total_ms: r(lsum), blocking_ms: r(blk), forced_layout_ms: r(forced), top_scripts: top };
    /* câmera */
    var camInt = [], capLat = [];
    for (i = 1; i < camSamples.length; i++) camInt.push(camSamples[i].t - camSamples[i - 1].t);
    camSamples.forEach(function (c) { if (c.c != null) capLat.push(c.t - c.c); });
    var pf0 = camSamples.length ? camSamples[0].pf : null, pf1 = camSamples.length ? camSamples[camSamples.length - 1].pf : null;
    var camera = { found: camFound || camSamples.length > 0, n_callbacks: camSamples.length,
      fps_callbacks: camSamples.length > 1 ? r((camSamples.length - 1) * 1000 / (camSamples[camSamples.length - 1].t - camSamples[0].t), 2) : null,
      presented_frames_delta: (pf0 != null && pf1 != null) ? pf1 - pf0 : null,
      resolution: camSamples.length ? camSamples[0].w + 'x' + camSamples[0].h : null,
      interval_ms: stats(camInt), capture_to_callback_ms: stats(capLat) };
    if (!camera.found) warnings.push('video_da_camera_nao_encontrado');
    /* fases */
    var ph = {}, sumTop = 0;
    Object.keys(phases).forEach(function (k) {
      var p = phases[k], s = stats(p.s.subarray(0, p.ns));
      ph[k] = { n: p.n, total_ms: r(p.total), pct_wall: r(p.total * 100 / wall, 2), mean_ms: s && s.mean, p95_ms: s && s.p95, max_ms: r(p.max), parent: nest[k] || null };
      if (!nest[k] || !phases[nest[k]]) sumTop += p.total;
    });
    var derived = {};
    Object.keys(phases).forEach(function (par) {
      var kids = Object.keys(nest).filter(function (c) { return nest[c] === par && phases[c]; });
      if (!kids.length) return;
      var ks = 0; kids.forEach(function (c) { ks += phases[c].total; });
      derived[par + '_proprio'] = { total_ms: r(phases[par].total - ks), pct_wall: r((phases[par].total - ks) * 100 / wall, 2),
                                    nota: par + ' menos ' + kids.join(' e ') };
    });
    if (!Object.keys(phases).length) warnings.push('nenhuma_fase_instrumentada (ganchos nao instalados)');
    else if (!hk.ar && window.AFRAME) warnings.push('gancho_do_AR.js_nao_instalado');
    /* rastreamento */
    var tracking = { calls: trackCalls, detections: trackDetect, detect_rate_hz: r(trackDetect * 1000 / wall, 2), call_rate_hz: r(trackCalls * 1000 / wall, 2),
      detect_ms: phases.tracking_detect ? stats(phases.tracking_detect.s.subarray(0, phases.tracking_detect.ns)) : null,
      e2e_ms: stats(e2e), e2e_ref: e2eRef, e2e_discarded: e2eBad,
      nota: 'detections = chamadas de arContext.update que devolveram true (o AR.js processou o quadro; as demais foram puladas por maxDetectionRate). e2e = fim da deteccao - captureTime (ou instante do callback de video) do quadro mais recente: aproximacao, o AR.js le o <video> no tick.' };
    /* heap */
    var m = performance.memory, hs = heapSeries.slice();
    var heap = { supported: !!m, series_mb: hs, min_mb: hs.length ? Math.min.apply(null, hs) : null, max_mb: hs.length ? Math.max.apply(null, hs) : null,
                 mean_mb: hs.length ? r(hs.reduce(function (a, b) { return a + b; }, 0) / hs.length, 2) : null, last_mb: hs.length ? hs[hs.length - 1] : null,
                 nota: 'performance.memory e aproximado (Chrome); serve para comparar tendencias, nao valores absolutos' };
    /* eventos e inicializacao */
    var evs = evAll.filter(function (e) { return inWin(e.t); }).slice(0, 300).map(function (e) { return { t_ms: r(e.t - recStart, 1), name: e.name, id: e.id, src: e.src }; });
    var life = evAll.slice(0, 120).map(function (e) { return { t_ms: r(e.t, 1), name: e.name, id: e.id, src: e.src }; });
    var nav = (performance.getEntriesByType('navigation') || [])[0];
    var res = (performance.getEntriesByType('resource') || []).slice(0, 150).map(function (e) { return { name: base(e.name), type: e.initiatorType, start_ms: r(e.startTime, 1), dur_ms: r(e.duration, 1), transfer: e.transferSize, body: e.decodedBodySize }; });
    var firstFound = null; evAll.some(function (e) { if (e.name === 'markerFound') { firstFound = r(e.t, 1); return true; } });
    var init = { dom_content_loaded_ms: nav ? r(nav.domContentLoadedEventEnd, 1) : null, load_ms: nav ? r(nav.loadEventEnd, 1) : null,
                 first_marker_found_ms_since_nav: firstFound, resources_n: res.length,
                 resources_transfer_bytes: res.reduce(function (a, b) { return a + (b.transfer || 0); }, 0), resources: res,
                 nota: 'tempos desde o inicio da navegacao; para a etapa de inicializacao use scenario=init e recarregue a pagina a cada repeticao' };
    var T = window.THREE || (window.AFRAME && window.AFRAME.THREE);
    var conn = navigator.connection ? { type: navigator.connection.type, effectiveType: navigator.connection.effectiveType, downlink: navigator.connection.downlink, rtt: navigator.connection.rtt } : null;
    var rep = {
      meta: { schema: 'arm/1', passe: CFG.passe, version: qs.get('version') || (window.AFRAME ? 'aframe' : 'threejs'), scenario: CFG.scenario, run: CFG.run, commit: CFG.commit,
              started_iso: new Date(recEpoch).toISOString(), epoch_ms_start: r(recEpoch, 0), warmup_s: CFG.warmup, duration_s: r(wall / 1000, 2), hz: CFG.hz,
              valid: warnings.length === 0, warnings: warnings, url: location.href,
              overhead: 'o proprio script cronometra chamadas e roda um timer de 10 ms e um laco de rAF; o custo e o mesmo nas duas versoes' },
      env: { ua: navigator.userAgent, ua_data: uadata, dpr: window.devicePixelRatio, viewport: innerWidth + 'x' + innerHeight, cores: navigator.hardwareConcurrency,
             device_memory_gb: navigator.deviceMemory || null, connection: conn, battery_start: batStart, battery_end: batEnd,
             versions: { aframe: window.AFRAME ? window.AFRAME.version : null, three: T ? T.REVISION : null, arjs: window.ARjs ? window.ARjs.REVISION || 'presente' : null } },
      frames: frames, longtasks: longtasks, loaf: loaf, event_loop_lag_ms: stats(lagSamples), camera: camera,
      phases: ph, phases_derived: derived, phases_accounted_pct_wall: r(sumTop * 100 / wall, 2), tracking: tracking, heap: heap,
      events: evs, lifecycle: life, init: init
    };
    if (CFG.raw) rep.raw = { lag_ms: lagSamples.map(function (x) { return r(x, 2); }), e2e_ms: e2e.map(function (x) { return r(x, 2); }), camera: camSamples };
    return rep;
  }
  function download(rep) {
    var name = rep.meta.version + '_' + rep.meta.scenario + '_' + rep.meta.passe + '_' + rep.meta.run + '.json';
    API.lastName = name;
    try {
      var blob = new Blob([JSON.stringify(rep, null, 1)], { type: 'application/json' });
      var a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name;
      document.body.appendChild(a); a.click();
      setTimeout(function () { URL.revokeObjectURL(a.href); a.remove(); }, 3000);
    } catch (e) { console.warn('[ARMetrics] download falhou; use ARMetrics.lastReport', e); }
  }

  /* ------------------------------------------------------------------ painel */
  var box, line, bStart, bStop, bSave;
  function buildUI() {
    if (!CFG.ui || box || !document.body) return;
    box = document.createElement('div');
    box.setAttribute('style', 'position:fixed;left:6px;bottom:6px;z-index:2147483647;font:11px/1.3 monospace;color:#fff;background:rgba(0,0,0,.55);padding:4px 6px;border-radius:4px;max-width:70vw');
    line = document.createElement('div'); box.appendChild(line);
    function btn(t, f) { var b = document.createElement('button'); b.textContent = t; b.setAttribute('style', 'font:11px monospace;margin:2px 4px 0 0;padding:3px 7px'); b.addEventListener('click', f); box.appendChild(b); return b; }
    bStart = btn('Iniciar', start); bStop = btn('Parar', stop); bSave = btn('Baixar JSON', function () { if (API.lastReport) download(API.lastReport); });
    document.body.appendChild(box);
  }
  function paintUI() {
    if (!CFG.ui) return; buildUI(); if (!line) return;
    var s = state === 'recording' ? 'gravando ' + Math.max(0, Math.round(CFG.duration - (now() - recStart) / 1000)) + 's'
          : state === 'warmup' ? 'aquecendo' : state === 'done' ? 'pronto: ' + (API.lastName || '') : 'parado';
    var t = 'ARM ' + (qs.get('version') || (window.AFRAME ? 'A-Frame' : 'Three.js')) + ' ' + CFG.scenario + '/' + CFG.run + ' | ' + s + ' | ' + Math.round(liveFps) + ' fps' + (CFG.marks ? ' | marks' : '');
    if (line.textContent !== t) line.textContent = t;
  }

  /* -------------------------------------------------------------- API pública */
  API.start = start; API.stop = stop;
  API.event = function (name, id) { pushEvent(name, id, 'app'); };      // ex.: ARMetrics.event('modal_open', 'sorte')
  API.begin = function (n) { (API._b || (API._b = {}))[n] = now(); };   // cronometragem manual de uma fase
  API.end = function (n) { var t0 = API._b && API._b[n]; if (t0 != null) rec(n, t0, now()); };
  API.nest = function (child, parent) { nest[child] = parent; };        // declara que 'child' acontece dentro de 'parent'
  API.phase = function (name, fn) {                                     // devolve fn cronometrada como fase
    return function () { var t0 = now(); try { return fn.apply(this, arguments); } finally { rec(name, t0, now()); } };
  };
  API.hookThree = function (o) {                                        // versão Three.js
    o = o || {}; var ok = false;
    if (o.renderer) ok = wrap(o.renderer, 'render', 'render') || ok;
    if (o.arContext) ok = wrap(o.arContext, 'update', 'tracking', onTrackingResult) || ok;
    if (o.arSource && o.trackResize) ok = wrap(o.arSource, 'onResizeElement', 'resize') || ok;
    return ok;
  };
  API.snapshot = function () { return { state: state, fps: liveFps, frames: nFrames, phases: Object.keys(phases) }; };

  /* ------------------------------------------------------------------- início */
  hookLoop();
  if (CFG.enabled) { lagLoop(); }
  timers.push(setInterval(housekeeping, 1000));
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', paintUI); else paintUI();
  if (CFG.autostart && CFG.enabled) window.addEventListener('load', function () { setTimeout(start, 1000); });
})();
