(async function () {

var logBoxEl = document.getElementById('logBox');
function appendLog(m) { logBoxEl.textContent += '\n' + m; logBoxEl.scrollTop = logBoxEl.scrollHeight; }
['log', 'warn', 'error'].forEach(function (k) {
  var orig = console[k].bind(console);
  console[k] = function () { try { appendLog('[' + k + '] ' + Array.from(arguments).map(String).join(' ')); } catch (e) {} orig.apply(null, arguments); };
});
window.onerror = function (m, s, l, c, e) { appendLog('onerror: ' + m + (e && e.stack ? '\n' + e.stack : '')); };
window.addEventListener('unhandledrejection', function (ev) { appendLog('reject: ' + (ev.reason && ev.reason.message ? ev.reason.message : String(ev.reason))); });

var el = function (id) { return document.getElementById(id); };
var statusEl = el('status');
var lastStatusText = '';

function setStatus(text) {
  var msg = text || '';
  if (statusEl) statusEl.textContent = '';
  if (msg === 'Loading') {
    if (msg !== lastStatusText) appendLog('Loading');
    lastStatusText = msg;
    return;
  }
  if (msg && msg !== lastStatusText) appendLog(msg);
  lastStatusText = msg;
}

/* ====== File state ====== */
var folderFiles = [], modelEntries = [], motionEntries = [], cameraEntries = [], audioEntries = [];
var folderName = '', filePathMap = {}, fileBaseMap = {};
var runtimeUrls = [];
var characters = [], charSeq = 0, selectedCharId = -1, cameraSel = 'free', audioSel = -1;

/* ====== Babylon state ====== */
var engine, scene, arcCamera, canvas;
var hemi, dir, grid, shadowGenerator, shadowGround;
var forcedGroundShadows = {}, forcedGroundShadowTexture = null, forcedGroundShadowMaterial = null, forcedGroundShadowObserver = null;
var moveGizmoLayer = null, moveGizmo = null, rotateGizmo = null;
var moveGizmoDragBound = false, rotateGizmoDragBound = false;
var mmdRuntime = null, mmdCamNode = null, audioPlayer = null, audioUrl = null;
var modelFpsLimiterObserver = null;
var toonMaterialDefaults = new WeakMap();
var materialBuilder = null;
var wasmInstance = null, physicsRuntime = null, physicsReady = false;
var glowLayer = null, fxPipeline = null;
var appliedEffectCode = '', effectDisposers = [];

/* ====== Playback state ====== */
var ready = false, playing = false, duration = 0, currentFrameTime = 0, draggingSeek = false;
var fpsSampleTime = 0, fpsSampleFrames = 0;
var rendering = false;

const FPS = 30;
const STUDIO_DB = 'mmd-viewer-studio', STUDIO_STORE = 'studio', STUDIO_KEY = 'current';
const SETTING_IDS = ['floorMode', 'fpsMode', 'pixelRatio', 'selfShadowMode', 'normalShadowMode', 'ambientLightLevel', 'directionalLightLevel', 'dirRotX', 'dirRotY', 'dirRotZ', 'backgroundColor', 'playbackSpeed', 'audioVolume', 'modelFpsLimit', 'physicsMode', 'ikMode', 'evalType', 'useDelta', 'physicsFps', 'substeps', 'glowMode', 'glowIntensity', 'glowBlur', 'bloomMode', 'bloomWeight', 'bloomThreshold', 'dofMode', 'dofFocus', 'dofAperture', 'renderFps', 'renderBitrate', 'gizmoMode'];

/* ====== Babylon init ====== */
function init() {
  canvas = el('c');
  engine = new BABYLON.Engine(canvas, true, { preserveDrawingBuffer: true, stencil: true }, true);
  BABYLONMMD.SdefInjector.OverrideEngineCreateEffect(engine);
  scene = new BABYLON.Scene(engine);
  applyBackground();
  scene.ambientColor = new BABYLON.Color3(0.3, 0.3, 0.3);

  arcCamera = new BABYLON.ArcRotateCamera('cam', -Math.PI / 2, Math.PI / 2.2, 35, new BABYLON.Vector3(0, 12, 0), scene);
  arcCamera.attachControl(canvas, true);
  arcCamera.wheelDeltaPercentage = 0.01;
  arcCamera.minZ = 0.1;
  arcCamera.maxZ = 2000;

  hemi = new BABYLON.HemisphericLight('hemi', new BABYLON.Vector3(0, 1, 0), scene);
  hemi.intensity = currentAmbientLight();
  dir = new BABYLON.DirectionalLight('dir', new BABYLON.Vector3(0.5, -1, 1), scene);
  dir.position = new BABYLON.Vector3(-30, 40, -30);
  dir.intensity = currentDirectionalLight();
  dir.autoCalcShadowZBounds = true;

  buildGrid();

  materialBuilder = BABYLONMMD.MmdStandardMaterialBuilder ? new BABYLONMMD.MmdStandardMaterialBuilder() : null;
  if (materialBuilder && BABYLONMMD.MmdMaterialRenderMethod) materialBuilder.renderMethod = BABYLONMMD.MmdMaterialRenderMethod.DepthWriteAlphaBlending;

  initPhysics();

  var _origCreateEffect = engine.createEffect.bind(engine);
  engine.createEffect = function(eName, eOpts, eUniforms, eSamplers, eDefines, eFallbacks, eOnCompiled, eOnError, eIndexParams, eLang, eKey) {
    var wrappedOnError = function(effect, err) {
      appendLog('[shader error] ' + (typeof eName === 'string' ? eName : (eName && eName.fragmentSource ? 'inline' : JSON.stringify(eName))) + ': ' + err);
      if (eOnError) eOnError(effect, err);
    };
    return _origCreateEffect(eName, eOpts, eUniforms, eSamplers, eDefines, eFallbacks, eOnCompiled, wrappedOnError, eIndexParams, eLang, eKey);
  };
  engine.runRenderLoop(function () { if (rendering) return; scene.render(); updateFps(performance.now()); });
  window.addEventListener('resize', function () { engine.resize(); });
  engine.resize();
}

function buildGrid() {
  if (grid) { grid.dispose(); grid = null; }
  var lines = [];
  for (var i = -20; i <= 20; i += 2) {
    lines.push([new BABYLON.Vector3(-20, 0, i), new BABYLON.Vector3(20, 0, i)]);
    lines.push([new BABYLON.Vector3(i, 0, -20), new BABYLON.Vector3(i, 0, 20)]);
  }
  grid = BABYLON.CreateLineSystem('grid', { lines: lines }, scene);
  grid.color = new BABYLON.Color3(0.28, 0.28, 0.32);
  grid.isPickable = false;
  grid.isVisible = floorEnabled();
}

/* ====== Physics (Bullet SPR via WASM) ====== */
async function initPhysics() {
  appendLog('physics init start');
  appendLog('SAB=' + (typeof SharedArrayBuffer !== 'undefined') + ' isolated=' + (typeof crossOriginIsolated !== 'undefined' ? crossOriginIsolated : '?'));
  try {
    wasmInstance = await BABYLONMMD.GetMmdWasmInstance(new BABYLONMMD.MmdWasmInstanceTypeSPR(), navigator.hardwareConcurrency);
    appendLog('wasm loaded');
    physicsRuntime = new BABYLONMMD.MultiPhysicsRuntime(wasmInstance);
    physicsRuntime.setGravity(new BABYLON.Vector3(0, -98, 0));
    physicsRuntime.fixedTimeStep = 1 / 60;
    physicsRuntime.maxSubSteps = 3;
    physicsRuntime.register(scene);
    physicsReady = true;
    applyEvalType();
    applyUseDelta();
    appendLog('physics ready (Bullet SPR)');
  } catch (e) {
    physicsReady = false;
    appendLog('physics failed: ' + (e && e.message ? e.message : String(e)));
  }
}

function physicsModeEnabled() { var v = el('physicsMode'); return v ? v.value === 'on' : true; }
function currentPhysicsFps() { return parseInt((el('physicsFps') || {}).value, 10) || 60; }
function currentSubsteps() { return parseInt((el('substeps') || {}).value, 10) || 3; }

function applyPhysicsStep() {
  if (!physicsRuntime) return;
  physicsRuntime.fixedTimeStep = 1 / currentPhysicsFps();
  physicsRuntime.maxSubSteps = currentSubsteps();
}

function applyEvalType() {
  if (!physicsRuntime || !BABYLONMMD.PhysicsRuntimeEvaluationType) return;
  var v = (el('evalType') || {}).value;
  physicsRuntime.evaluationType = v === 'buffered'
    ? BABYLONMMD.PhysicsRuntimeEvaluationType.Buffered
    : BABYLONMMD.PhysicsRuntimeEvaluationType.Immediate;
}

function applyUseDelta() {
  if (!physicsRuntime) return;
  physicsRuntime.useDeltaForWorldStep = (el('useDelta') || {}).value === 'on';
}

function currentModelFpsLimit() {
  var node = el('modelFpsLimit');
  if (!node || node.value === 'off') return 0;
  return parseInt(node.value, 10) || 0;
}

function clearModelFpsLimiterState() {
  for (var i = 0; i < characters.length; i++) {
    characters[i].limitedPoseStep = -1;
    characters[i].limitedPoseMatrices = null;
    characters[i].limitedPoseMorphs = null;
  }
}

function captureCharacterMorphs(ch) {
  var out = [];
  var meshes = ch.container && ch.container.meshes ? ch.container.meshes : [];
  for (var i = 0; i < meshes.length; i++) {
    var manager = meshes[i].morphTargetManager;
    if (!manager) continue;
    var item = { manager: manager, values: [] };
    for (var j = 0; j < manager.numTargets; j++) item.values.push(manager.getTarget(j).influence);
    out.push(item);
  }
  return out;
}

function restoreCharacterMorphs(items) {
  if (!items) return;
  for (var i = 0; i < items.length; i++) {
    var manager = items[i].manager;
    var values = items[i].values;
    for (var j = 0; j < values.length && j < manager.numTargets; j++) manager.getTarget(j).influence = values[j];
  }
}

function captureCharacterLimitedPose(ch, step) {
  if (!ch.model || !ch.model.worldTransformMatrices) return;
  if (!ch.limitedPoseMatrices || ch.limitedPoseMatrices.length !== ch.model.worldTransformMatrices.length) {
    ch.limitedPoseMatrices = new Float32Array(ch.model.worldTransformMatrices.length);
  }
  ch.limitedPoseMatrices.set(ch.model.worldTransformMatrices);
  ch.limitedPoseMorphs = captureCharacterMorphs(ch);
  ch.limitedPoseStep = step;
}

function restoreCharacterLimitedPose(ch) {
  if (!ch.model || !ch.model.worldTransformMatrices || !ch.limitedPoseMatrices) return;
  ch.model.worldTransformMatrices.set(ch.limitedPoseMatrices);
  restoreCharacterMorphs(ch.limitedPoseMorphs);
  if (ch.mesh && ch.mesh.metadata && ch.mesh.metadata.skeleton) ch.mesh.metadata.skeleton._markAsDirty();
}

function applyModelFpsLimit() {
  clearModelFpsLimiterState();
}

function ensureModelFpsLimiter() {
  if (!scene || modelFpsLimiterObserver) return;
  modelFpsLimiterObserver = scene.onBeforeRenderObservable.add(function () {
    var fps = currentModelFpsLimit();
    if (!fps || !mmdRuntime || (!playing && !rendering)) {
      clearModelFpsLimiterState();
      return;
    }
    var step = Math.floor((mmdRuntime.currentFrameTime / 30) * fps);
    for (var i = 0; i < characters.length; i++) {
      var ch = characters[i];
      if (ch.limitedPoseStep !== step || !ch.limitedPoseMatrices) captureCharacterLimitedPose(ch, step);
      else restoreCharacterLimitedPose(ch);
    }
  });
}


function cloneColorValue(v) {
  return v && v.clone ? v.clone() : v;
}

function setColorValue(obj, key, value) {
  if (!obj || !(key in obj) || !value) return;
  if (obj[key] && obj[key].copyFrom) obj[key].copyFrom(value);
  else obj[key] = cloneColorValue(value);
}

function markToonMaterialDirty(mat) {
  try { if (mat && mat.markDirty) mat.markDirty(); } catch (e) {}
  try { if (mat && mat._markAllSubMeshesAsDirty && BABYLON.Material) mat._markAllSubMeshesAsDirty(BABYLON.Material.AllDirtyFlag); } catch (e) {}
}

function rememberToonMaterialDefaults(mat) {
  if (!mat || typeof mat !== 'object') return null;
  var saved = toonMaterialDefaults.get(mat);
  if (saved) return saved;
  saved = {
    hasDisableLighting: 'disableLighting' in mat,
    disableLighting: mat.disableLighting,
    hasSpecularPower: 'specularPower' in mat,
    specularPower: mat.specularPower,
    hasSpecularColor: 'specularColor' in mat,
    specularColor: cloneColorValue(mat.specularColor),
    hasDiffuseColor: 'diffuseColor' in mat,
    diffuseColor: cloneColorValue(mat.diffuseColor),
    hasAlbedoColor: 'albedoColor' in mat,
    albedoColor: cloneColorValue(mat.albedoColor),
    hasEmissiveColor: 'emissiveColor' in mat,
    emissiveColor: cloneColorValue(mat.emissiveColor),
    hasAmbientColor: 'ambientColor' in mat,
    ambientColor: cloneColorValue(mat.ambientColor)
  };
  toonMaterialDefaults.set(mat, saved);
  return saved;
}

function restoreToonMaterial(mat) {
  var saved = toonMaterialDefaults.get(mat);
  if (!saved) return;
  if (saved.hasDisableLighting) mat.disableLighting = saved.disableLighting;
  if (saved.hasSpecularPower) mat.specularPower = saved.specularPower;
  if (saved.hasSpecularColor) setColorValue(mat, 'specularColor', saved.specularColor);
  if (saved.hasDiffuseColor) setColorValue(mat, 'diffuseColor', saved.diffuseColor);
  if (saved.hasAlbedoColor) setColorValue(mat, 'albedoColor', saved.albedoColor);
  if (saved.hasEmissiveColor) setColorValue(mat, 'emissiveColor', saved.emissiveColor);
  if (saved.hasAmbientColor) setColorValue(mat, 'ambientColor', saved.ambientColor);
  markToonMaterialDirty(mat);
}

function collectCharacterMaterials(ch) {
  var list = [];
  function add(mat) {
    if (!mat) return;
    if (mat.subMaterials && mat.subMaterials.length) {
      for (var s = 0; s < mat.subMaterials.length; s++) add(mat.subMaterials[s]);
      return;
    }
    if (list.indexOf(mat) < 0) list.push(mat);
  }
  var meshes = ch && ch.container && ch.container.meshes ? ch.container.meshes : [];
  for (var i = 0; i < meshes.length; i++) add(meshes[i].material);
  var mats = ch && ch.container && ch.container.materials ? ch.container.materials : [];
  for (var j = 0; j < mats.length; j++) add(mats[j]);
  var mmats = ch && ch.container && ch.container.multiMaterials ? ch.container.multiMaterials : [];
  for (var k = 0; k < mmats.length; k++) add(mmats[k]);
  return list;
}

function clampFlatToonBrightness(v) {
  var n = parseFloat(v);
  if (!isFinite(n)) n = 1;
  return Math.max(0, Math.min(5, n));
}

function toonBrightnessColor(src, brightness) {
  var c = src && typeof src.r === 'number' ? src : new BABYLON.Color3(1, 1, 1);
  if ((c.r + c.g + c.b) < 0.001) c = new BABYLON.Color3(1, 1, 1);
  return new BABYLON.Color3(c.r * brightness, c.g * brightness, c.b * brightness);
}

function applyFlatToonMaterial(mat, brightness) {
  var saved = rememberToonMaterialDefaults(mat) || {};
  var b = clampFlatToonBrightness(brightness);
  var base = saved.diffuseColor || saved.albedoColor || mat.diffuseColor || mat.albedoColor || new BABYLON.Color3(1, 1, 1);
  var color = toonBrightnessColor(base, b);
  if ('disableLighting' in mat) mat.disableLighting = true;
  if ('specularPower' in mat) mat.specularPower = 0;
  if ('specularColor' in mat) setColorValue(mat, 'specularColor', new BABYLON.Color3(0, 0, 0));
  if ('diffuseColor' in mat) setColorValue(mat, 'diffuseColor', color);
  if ('albedoColor' in mat) setColorValue(mat, 'albedoColor', color);
  if ('ambientColor' in mat) setColorValue(mat, 'ambientColor', color);
  if ('emissiveColor' in mat) setColorValue(mat, 'emissiveColor', color);
  markToonMaterialDirty(mat);
}

function applyToonModeToCharacter(ch) {
  if (!ch) return;
  var mode = ch.toonMode || 'off';
  var brightness = clampFlatToonBrightness(ch.flatToonBrightness == null ? 1 : ch.flatToonBrightness);
  var mats = collectCharacterMaterials(ch);
  for (var i = 0; i < mats.length; i++) {
    if (mode === 'flat') applyFlatToonMaterial(mats[i], brightness);
    else restoreToonMaterial(mats[i]);
  }
}

function syncCharacterToonModeControl() {
  var node = el('characterToonMode');
  if (!node) return;
  var ch = currentChar();
  node.disabled = !ch;
  node.value = ch && ch.toonMode ? ch.toonMode : 'off';
  syncCharacterToonBrightnessControl();
}

function syncCharacterToonBrightnessControl() {
  var range = el('flatToonBrightnessRange');
  var number = el('flatToonBrightness');
  if (!range || !number) return;
  var ch = currentChar();
  var v = ch ? clampFlatToonBrightness(ch.flatToonBrightness == null ? 1 : ch.flatToonBrightness) : 1;
  range.disabled = !ch;
  number.disabled = !ch;
  range.value = String(v);
  number.value = String(v);
}

function applyCharacterToonMode() {
  var ch = currentChar();
  if (!ch) return;
  var node = el('characterToonMode');
  ch.toonMode = node ? node.value : 'off';
  applyToonModeToCharacter(ch);
  renderCharacters();
}

function applyCharacterToonBrightness() {
  var ch = currentChar();
  if (!ch) return;
  var number = el('flatToonBrightness');
  var range = el('flatToonBrightnessRange');
  var v = clampFlatToonBrightness(number ? number.value : range ? range.value : 1);
  ch.flatToonBrightness = v;
  if (number) number.value = String(v);
  if (range) range.value = String(v);
  applyToonModeToCharacter(ch);
}

/* ====== Physics toggle (Bullet対応) ====== */
function applyIkModeTo(ch) {
  if (!ch.model) return;
  var val = el('ikMode').value === 'on' ? 1 : 0;
  var states = ch.model.ikSolverStates;
  for (var i = 0; i < states.length; i++) states[i] = val;
}

function applyIkMode() {
  for (var i = 0; i < characters.length; i++) applyIkModeTo(characters[i]);
}

function applyPhysicsModeTo(ch) {
  if (!ch.model) return;
  var on = physicsModeEnabled();
  var states = ch.model.rigidBodyStates;
  if (!states || states.length === 0) return;
  for (var i = 0; i < states.length; i++) states[i] = on ? 1 : 0;
  if (on && mmdRuntime) mmdRuntime.initializeMmdModelPhysics(ch.model);
}

function applyPhysicsMode() {
  for (var i = 0; i < characters.length; i++) applyPhysicsModeTo(characters[i]);
}

function initAllPhysics() {
  if (!mmdRuntime) return;
  for (var i = 0; i < characters.length; i++) if (characters[i].model) mmdRuntime.initializeMmdModelPhysics(characters[i].model);
}

function resetPhysics() {
  if (!ready || !mmdRuntime) return;
  initAllPhysics();
}

/* ====== FX (Glow / Bloom / DOF) ====== */
function fxNum(id, fallback) { var v = parseFloat((el(id) || {}).value); return isFinite(v) ? v : fallback; }
function fxOn(id) { return (el(id) || {}).value === 'on'; }
function applyGlow() {
  if (!scene) return;
  if (fxOn('glowMode')) {
    if (!glowLayer) {
      glowLayer = new BABYLON.GlowLayer('glow', scene, { mainTextureRatio: 0.5, mainTextureSamples: 4 });
      glowLayer.customEmissiveColorSelector = function (mesh, subMesh, material, result) {
        var sp = material && material.specularPower != null ? material.specularPower : 0;
        if (sp >= 100) {
          var d = material.diffuseColor || BABYLON.Color3.Black();
          var a = material.ambientColor || BABYLON.Color3.Black();
          result.set(Math.min(1, d.r + a.r), Math.min(1, d.g + a.g), Math.min(1, d.b + a.b), 1);
        } else {
          result.set(0, 0, 0, 0);
        }
      };
    }
    glowLayer.intensity = fxNum('glowIntensity', 1);
    glowLayer.blurKernelSize = fxNum('glowBlur', 32);
  } else if (glowLayer) {
    glowLayer.dispose();
    glowLayer = null;
  }
}

function ensurePipeline() {
  if (fxPipeline) return;
  fxPipeline = new BABYLON.DefaultRenderingPipeline('fxPipeline', true, scene, [scene.activeCamera]);
  fxPipeline.bloomEnabled = false;
  fxPipeline.depthOfFieldEnabled = false;
}

function applyBloom() {
  if (!scene) return;
  ensurePipeline();
  if (!fxPipeline) return;
  fxPipeline.bloomEnabled = fxOn('bloomMode');
  fxPipeline.bloomWeight = fxNum('bloomWeight', 0.6);
  fxPipeline.bloomThreshold = fxNum('bloomThreshold', 0.8);
}

function applyDof() {
  if (!scene) return;
  ensurePipeline();
  if (!fxPipeline) return;
  fxPipeline.depthOfFieldEnabled = fxOn('dofMode');
  fxPipeline.depthOfField.focusDistance = fxNum('dofFocus', 2000);
  fxPipeline.depthOfField.fStop = Math.max(0.1, fxNum('dofAperture', 0.1) * 10);
}

function getFxCameras() {
  var cameras = [];
  if (scene && scene.activeCamera) cameras.push(scene.activeCamera);
  if (arcCamera && cameras.indexOf(arcCamera) < 0) cameras.push(arcCamera);
  if (mmdCamNode && cameras.indexOf(mmdCamNode) < 0) cameras.push(mmdCamNode);
  return cameras;
}

function reattachPipelineCamera() {
  if (fxPipeline && scene.activeCamera) {
    fxPipeline.dispose();
    fxPipeline = null;
    if (fxOn('bloomMode') || fxOn('dofMode')) { applyBloom(); applyDof(); }
  }
}

function runEffectDisposers() {
  for (var i = 0; i < effectDisposers.length; i++) {
    try { effectDisposers[i](); } catch (e) { appendLog('effect dispose error: ' + (e && e.message ? e.message : String(e))); }
  }
  effectDisposers = [];
}

function exposeFilesToScene() {
  if (!scene) return;
  scene.metadata = scene.metadata || {};
  var map = {};
  for (var i = 0; i < folderFiles.length; i++) {
    var e = folderFiles[i];
    map[baseOf(e.path).toLowerCase()] = e.file;
    map[normPath(e.path).toLowerCase()] = e.file;
  }
  scene.metadata.files = map;
}

function applyEffectCode(code) {
  runEffectDisposers();
  if (!code || !code.trim()) return;
  exposeFilesToScene();
  try {
    var fn = new Function('scene', 'engine', 'activeCamera', 'mmdRuntime', 'characters', 'BABYLON', 'BABYLONMMD', 'onDispose', code);
    fn(scene, engine, scene ? scene.activeCamera : null, mmdRuntime, characters, BABYLON, BABYLONMMD, function (d) { if (typeof d === 'function') effectDisposers.push(d); });
  } catch (e) {
    appendLog('effect error: ' + (e && e.message ? e.message : String(e)) + (e && e.stack ? '\n' + e.stack : ''));
  }
}

function clearEffectCode() {
  runEffectDisposers();
  appliedEffectCode = '';
}

/* ====== Settings ====== */
function selectedModeOn(id, fallback) { var v = el(id); return v ? v.value === 'on' : fallback; }
function floorEnabled() { return selectedModeOn('floorMode', true); }
function fpsEnabled() { return selectedModeOn('fpsMode', true); }
function selfShadowEnabled() { return selectedModeOn('selfShadowMode', false); }
function normalShadowEnabled() { return selectedModeOn('normalShadowMode', false); }
function selectedFloat(id, fallback) { var v = el(id); var n = v ? parseFloat(v.value) : fallback; return n >= 0 ? n : fallback; }
function currentAmbientLight() { return selectedFloat('ambientLightLevel', 0.7); }
function currentDirectionalLight() { return selectedFloat('directionalLightLevel', 0.6); }
function currentPlaybackSpeed() { var v = parseFloat((el('playbackSpeed') || {}).value); return (v > 0 && v <= 10) ? v : 1; }
function currentAudioVolume() { var v = parseFloat((el('audioVolume') || {}).value); return isFinite(v) ? Math.max(0, Math.min(1, v)) : 1; }
function currentPixelRatio() { var v = (el('pixelRatio') || {}).value; if (v === 'device') return window.devicePixelRatio || 1; var n = parseFloat(v); return n > 0 ? n : 1; }

function currentBackgroundColor3() {
  var hex = (el('backgroundColor') || {}).value || '#262b31';
  var r = parseInt(hex.slice(1, 3), 16) / 255;
  var g = parseInt(hex.slice(3, 5), 16) / 255;
  var b = parseInt(hex.slice(5, 7), 16) / 255;
  return new BABYLON.Color3(r, g, b);
}

function applyBackground() {
  var c = currentBackgroundColor3();
  if (scene) scene.clearColor = new BABYLON.Color4(c.r, c.g, c.b, 1.0);
  updateShadowGroundMaterialColor();
}

function ensureShadowGenerator() {
  if (!shadowGenerator && dir) {
    shadowGenerator = new BABYLON.ShadowGenerator(1024, dir);
    shadowGenerator.useBlurExponentialShadowMap = true;
    shadowGenerator.blurKernel = 16;
    shadowGenerator.setDarkness(0.75);
  }
  return shadowGenerator;
}

function updateShadowGroundMaterialColor() {
  if (!shadowGround || !shadowGround.material) return;
  var c = currentBackgroundColor3();
  var mat = shadowGround.material;
  if ('primaryColor' in mat && mat.primaryColor && mat.primaryColor.copyFrom) mat.primaryColor.copyFrom(c);
  if ('diffuseColor' in mat && mat.diffuseColor && mat.diffuseColor.copyFrom) mat.diffuseColor.copyFrom(c);
  if ('ambientColor' in mat && mat.ambientColor && mat.ambientColor.copyFrom) mat.ambientColor.copyFrom(c);
  if ('reflectionColor' in mat && mat.reflectionColor && mat.reflectionColor.copyFrom) mat.reflectionColor.copyFrom(c);
}

function ensureShadowGround() {
  if (!shadowGround && scene) {
    shadowGround = BABYLON.MeshBuilder.CreateGround('shadowGround', { width: 200, height: 200 }, scene);
    shadowGround.position.y = -0.02;
    shadowGround.isPickable = false;
    shadowGround.receiveShadows = true;

    var mat;
    if (BABYLON.BackgroundMaterial) {
      mat = new BABYLON.BackgroundMaterial('shadowGroundMat', scene);
      mat.shadowOnly = true;
      mat.shadowLevel = 0.65;
      mat.specularColor = new BABYLON.Color3(0, 0, 0);
    } else {
      mat = new BABYLON.StandardMaterial('shadowGroundMat', scene);
      mat.specularColor = new BABYLON.Color3(0, 0, 0);
      mat.alpha = 1;
    }
    shadowGround.material = mat;
    updateShadowGroundMaterialColor();
  }
  return shadowGround;
}

function forEachCharacterMesh(callback) {
  for (var i = 0; i < characters.length; i++) {
    var meshes = characters[i].container ? characters[i].container.meshes : [];
    for (var j = 0; j < meshes.length; j++) {
      var mesh = meshes[j];
      if (mesh && mesh.getTotalVertices && mesh.getTotalVertices() > 0) callback(mesh, characters[i]);
    }
  }
}

function collectCharacterMeshes(ch) {
  var out = [];
  var meshes = ch && ch.container ? ch.container.meshes : [];
  for (var i = 0; i < meshes.length; i++) {
    var mesh = meshes[i];
    if (mesh && mesh.getTotalVertices && mesh.getTotalVertices() > 0) out.push(mesh);
  }
  return out;
}

function isRealShadowMesh(mesh) {
  if (!mesh || mesh === shadowGround || mesh === grid) return false;
  if (mesh.metadata && mesh.metadata.forceContactShadow) return false;
  return !!mesh.getTotalVertices && mesh.getTotalVertices() > 0;
}

function ensureForcedGroundShadowMaterial() {
  if (forcedGroundShadowMaterial || !scene) return forcedGroundShadowMaterial;
  forcedGroundShadowTexture = new BABYLON.DynamicTexture('forcedGroundShadowTex', { width: 512, height: 512 }, scene, true);
  forcedGroundShadowTexture.hasAlpha = true;
  var ctx = forcedGroundShadowTexture.getContext();
  ctx.clearRect(0, 0, 512, 512);
  var grad = ctx.createRadialGradient(256, 256, 8, 256, 256, 248);
  grad.addColorStop(0.0, 'rgba(0,0,0,0.62)');
  grad.addColorStop(0.28, 'rgba(0,0,0,0.42)');
  grad.addColorStop(0.62, 'rgba(0,0,0,0.16)');
  grad.addColorStop(1.0, 'rgba(0,0,0,0.0)');
  ctx.fillStyle = grad;
  ctx.fillRect(0, 0, 512, 512);
  forcedGroundShadowTexture.update(false);

  forcedGroundShadowMaterial = new BABYLON.StandardMaterial('forcedGroundShadowMat', scene);
  forcedGroundShadowMaterial.diffuseTexture = forcedGroundShadowTexture;
  forcedGroundShadowMaterial.opacityTexture = forcedGroundShadowTexture;
  forcedGroundShadowMaterial.useAlphaFromDiffuseTexture = true;
  forcedGroundShadowMaterial.diffuseColor = new BABYLON.Color3(0, 0, 0);
  forcedGroundShadowMaterial.emissiveColor = new BABYLON.Color3(0, 0, 0);
  forcedGroundShadowMaterial.specularColor = new BABYLON.Color3(0, 0, 0);
  forcedGroundShadowMaterial.disableLighting = true;
  forcedGroundShadowMaterial.alpha = 0.82;
  forcedGroundShadowMaterial.backFaceCulling = false;
  forcedGroundShadowMaterial.zOffset = -3;
  if (BABYLON.Material && BABYLON.Material.MATERIAL_ALPHABLEND != null) forcedGroundShadowMaterial.transparencyMode = BABYLON.Material.MATERIAL_ALPHABLEND;
  return forcedGroundShadowMaterial;
}

function ensureForcedGroundShadow(ch) {
  if (!ch || !scene) return null;
  var key = String(ch.id);
  if (forcedGroundShadows[key]) return forcedGroundShadows[key];
  var mesh = BABYLON.MeshBuilder.CreateGround('forcedGroundShadow_' + key, { width: 1, height: 1, subdivisions: 1 }, scene);
  mesh.isPickable = false;
  mesh.receiveShadows = false;
  mesh.alwaysSelectAsActiveMesh = true;
  mesh.renderingGroupId = 3;
  mesh.metadata = mesh.metadata || {};
  mesh.metadata.forceContactShadow = true;
  mesh.material = ensureForcedGroundShadowMaterial();
  mesh.isVisible = false;
  forcedGroundShadows[key] = mesh;
  return mesh;
}

function characterWorldBounds(ch) {
  var meshes = collectCharacterMeshes(ch);
  if (!meshes.length) return null;
  var min = new BABYLON.Vector3(Number.POSITIVE_INFINITY, Number.POSITIVE_INFINITY, Number.POSITIVE_INFINITY);
  var max = new BABYLON.Vector3(Number.NEGATIVE_INFINITY, Number.NEGATIVE_INFINITY, Number.NEGATIVE_INFINITY);
  for (var i = 0; i < meshes.length; i++) {
    var mesh = meshes[i];
    if (!mesh || !mesh.isEnabled() || !mesh.isVisible) continue;
    mesh.computeWorldMatrix(true);
    var box = mesh.getBoundingInfo().boundingBox;
    var bmin = box.minimumWorld;
    var bmax = box.maximumWorld;
    min.x = Math.min(min.x, bmin.x);
    min.y = Math.min(min.y, bmin.y);
    min.z = Math.min(min.z, bmin.z);
    max.x = Math.max(max.x, bmax.x);
    max.y = Math.max(max.y, bmax.y);
    max.z = Math.max(max.z, bmax.z);
  }
  if (!isFinite(min.x) || !isFinite(max.x)) return null;
  return { min: min, max: max };
}

function isStageLikeBounds(bounds) {
  if (!bounds) return true;
  var w = bounds.max.x - bounds.min.x;
  var h = bounds.max.y - bounds.min.y;
  var d = bounds.max.z - bounds.min.z;
  return w > 70 || d > 70 || h > 55;
}

function hideUnusedForcedGroundShadows(used) {
  for (var key in forcedGroundShadows) {
    if (!used[key]) forcedGroundShadows[key].isVisible = false;
  }
}

function updateForcedGroundShadows() {
  var used = {};
  if (!normalShadowEnabled()) {
    hideUnusedForcedGroundShadows(used);
    return;
  }
  for (var i = 0; i < characters.length; i++) {
    var ch = characters[i];
    var bounds = characterWorldBounds(ch);
    if (!bounds || isStageLikeBounds(bounds)) continue;
    var mesh = ensureForcedGroundShadow(ch);
    if (!mesh) continue;
    var w = Math.max(0.7, bounds.max.x - bounds.min.x);
    var d = Math.max(0.7, bounds.max.z - bounds.min.z);
    var h = Math.max(0.7, bounds.max.y - bounds.min.y);
    mesh.position.x = (bounds.min.x + bounds.max.x) * 0.5;
    mesh.position.y = bounds.min.y + 0.12;
    mesh.position.z = (bounds.min.z + bounds.max.z) * 0.5;
    mesh.scaling.x = Math.max(w * 1.55, h * 0.30, 1.2);
    mesh.scaling.z = Math.max(d * 1.55, h * 0.22, 1.0);
    mesh.rotation.x = 0;
    mesh.rotation.y = 0;
    mesh.rotation.z = 0;
    mesh.isVisible = true;
    used[String(ch.id)] = true;
  }
  hideUnusedForcedGroundShadows(used);
}

function ensureForcedGroundShadowUpdater() {
  if (!scene || forcedGroundShadowObserver) return;
  forcedGroundShadowObserver = scene.onBeforeRenderObservable.add(updateForcedGroundShadows);
}

function applyShadows() {
  if (!scene || !dir) return;
  var selfOn = selfShadowEnabled();
  var normalOn = normalShadowEnabled();
  var anyOn = selfOn || normalOn;
  scene.shadowsEnabled = anyOn;
  var ground = ensureShadowGround();
  var generator = ensureShadowGenerator();
  var map = generator ? generator.getShadowMap() : null;
  if (generator) {
    generator.bias = 0.0005;
    generator.normalBias = 0.02;
    generator.setDarkness(0.85);
  }
  if (map) map.renderList = [];
  var selected = currentChar();
  var casterMeshes = normalOn && selected ? collectCharacterMeshes(selected) : [];
  if (normalOn && casterMeshes.length === 0) {
    forEachCharacterMesh(function (mesh) { casterMeshes.push(mesh); });
  }
  for (var i = 0; map && i < casterMeshes.length; i++) map.renderList.push(casterMeshes[i]);

  var hasPmxReceiver = false;
  for (var s = 0; s < scene.meshes.length; s++) {
    var mesh = scene.meshes[s];
    if (!isRealShadowMesh(mesh)) continue;
    var isCaster = casterMeshes.indexOf(mesh) >= 0;
    if (normalOn && !isCaster) {
      mesh.receiveShadows = true;
      hasPmxReceiver = true;
    } else {
      mesh.receiveShadows = selfOn && isCaster;
    }
  }
  if (ground) {
    ground.receiveShadows = normalOn;
    ground.isVisible = normalOn && !hasPmxReceiver;
  }
  if (!anyOn && map) map.renderList = [];
  ensureForcedGroundShadowUpdater();
  updateForcedGroundShadows();
}

function applyView() {
  if (grid) grid.isVisible = floorEnabled();
  el('fps').style.display = fpsEnabled() ? 'block' : 'none';
  applyBackground();
  applyShadows();
}

function currentDirRotX() { var v = document.getElementById('dirRotX'); return v ? (parseFloat(v.value) || 0) : 0; }
function currentDirRotY() { var v = document.getElementById('dirRotY'); return v ? (parseFloat(v.value) || 0) : 0; }
function currentDirRotZ() { var v = document.getElementById('dirRotZ'); return v ? (parseFloat(v.value) || 0) : 0; }
function applyDirRotation() {
  if (!dir) return;
  var rad = Math.PI / 180;
  var mat = BABYLON.Matrix.RotationYawPitchRoll(currentDirRotY() * rad, currentDirRotX() * rad, currentDirRotZ() * rad);
  dir.direction = BABYLON.Vector3.TransformNormal(new BABYLON.Vector3(0, -1, 0), mat);
}

function applyLighting() {
  if (hemi) hemi.intensity = currentAmbientLight();
  if (dir) dir.intensity = currentDirectionalLight();
  applyDirRotation();
}

function applyPixelRatio() {
  if (!engine) return;
  var ratio = currentPixelRatio();
  engine.setHardwareScalingLevel(1.0 / ratio);
  engine.resize();
}

function applyPlaybackSpeed() {
  if (mmdRuntime) mmdRuntime.timeScale = currentPlaybackSpeed();
  if (audioPlayer) audioPlayer.playbackRate = currentPlaybackSpeed();
}

function applyAudioVolume() {
  if (audioPlayer) audioPlayer.volume = currentAudioVolume();
}

/* ====== MP4 utilities ====== */
function byteLength(list) {
  var n = 0;
  for (var i = 0; i < list.length; i++) n += list[i].byteLength;
  return n;
}

function bytesJoin(list) {
  var out = new Uint8Array(byteLength(list));
  var o = 0;
  for (var i = 0; i < list.length; i++) { out.set(list[i], o); o += list[i].byteLength; }
  return out;
}

function u8(n) { return new Uint8Array([n & 255]); }
function u16(n) { return new Uint8Array([(n >>> 8) & 255, n & 255]); }
function i16(n) { return u16(n & 65535); }
function u24(n) { return new Uint8Array([(n >>> 16) & 255, (n >>> 8) & 255, n & 255]); }
function u32(n) { return new Uint8Array([(n >>> 24) & 255, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]); }
function strBytes(s) { var a = new Uint8Array(s.length); for (var i = 0; i < s.length; i++) a[i] = s.charCodeAt(i) & 255; return a; }
function zeros(n) { return new Uint8Array(n); }
function fixed1616(n) { return u32(Math.round(n * 65536)); }
function fixed0230(n) { return u32(Math.round(n * 1073741824)); }

function mp4Box(type) {
  var parts = [u32(0), strBytes(type)];
  for (var i = 1; i < arguments.length; i++) parts.push(arguments[i]);
  var out = bytesJoin(parts);
  var size = u32(out.byteLength);
  out.set(size, 0);
  return out;
}

function mp4FullBox(type, version, flags) {
  var parts = [u8(version), u24(flags)];
  for (var i = 3; i < arguments.length; i++) parts.push(arguments[i]);
  return mp4Box.apply(null, [type].concat(parts));
}

function mp4Ftyp() {
  return mp4Box('ftyp', strBytes('isom'), u32(512), strBytes('isom'), strBytes('iso2'), strBytes('avc1'), strBytes('mp41'));
}

function mp4Mvhd(timescale, duration) {
  return mp4FullBox('mvhd', 0, 0, u32(0), u32(0), u32(timescale), u32(duration), fixed1616(1), u16(256), zeros(10), fixed1616(1), fixed1616(0), fixed0230(0), fixed1616(0), fixed1616(1), fixed0230(0), fixed1616(0), fixed1616(0), fixed0230(1), zeros(24), u32(2));
}

function mp4Tkhd(width, height, duration) {
  return mp4FullBox('tkhd', 0, 7, u32(0), u32(0), u32(1), u32(0), u32(duration), zeros(8), u16(0), u16(0), u16(0), u16(0), fixed1616(1), fixed1616(0), fixed0230(0), fixed1616(0), fixed1616(1), fixed0230(0), fixed1616(0), fixed1616(0), fixed0230(1), fixed1616(width), fixed1616(height));
}

function mp4Mdhd(timescale, duration) {
  return mp4FullBox('mdhd', 0, 0, u32(0), u32(0), u32(timescale), u32(duration), u16(21956), u16(0));
}

function mp4Hdlr() {
  return mp4FullBox('hdlr', 0, 0, u32(0), strBytes('vide'), zeros(12), strBytes('VideoHandler'), u8(0));
}

function mp4Vmhd() { return mp4FullBox('vmhd', 0, 1, u16(0), u16(0), u16(0), u16(0)); }
function mp4Dinf() { return mp4Box('dinf', mp4FullBox('dref', 0, 0, u32(1), mp4FullBox('url ', 0, 1))); }

function mp4Avc1(width, height, avcC) {
  var compressor = zeros(32);
  return mp4Box('avc1', zeros(6), u16(1), zeros(16), u16(width), u16(height), fixed1616(72), fixed1616(72), u32(0), u16(1), compressor, u16(24), i16(-1), mp4Box('avcC', avcC));
}

function mp4Stsd(width, height, avcC) { return mp4FullBox('stsd', 0, 0, u32(1), mp4Avc1(width, height, avcC)); }
function mp4Stts(count) { return mp4FullBox('stts', 0, 0, u32(1), u32(count), u32(1)); }
function mp4Stsc() { return mp4FullBox('stsc', 0, 0, u32(1), u32(1), u32(1), u32(1)); }

function mp4Stss(samples) {
  var parts = [u32(samples.length)];
  for (var i = 0; i < samples.length; i++) parts.push(u32(samples[i]));
  return mp4FullBox.apply(null, ['stss', 0, 0].concat(parts));
}

function mp4Stsz(sizes) {
  var parts = [u32(0), u32(sizes.length)];
  for (var i = 0; i < sizes.length; i++) parts.push(u32(sizes[i]));
  return mp4FullBox.apply(null, ['stsz', 0, 0].concat(parts));
}

function mp4Stco(offsets) {
  var parts = [u32(offsets.length)];
  for (var i = 0; i < offsets.length; i++) parts.push(u32(offsets[i]));
  return mp4FullBox.apply(null, ['stco', 0, 0].concat(parts));
}

function buildMp4(chunks, samples, opt) {
  var ftyp = mp4Ftyp();
  var mdatPayload = bytesJoin(chunks);
  var mdat = mp4Box('mdat', mdatPayload);
  var offsets = [];
  var o = ftyp.byteLength + 8;
  var sizes = [];
  var sync = [];
  for (var i = 0; i < samples.length; i++) {
    offsets.push(o);
    sizes.push(samples[i].size);
    if (samples[i].key) sync.push(i + 1);
    o += samples[i].size;
  }
  if (sync.length === 0) sync.push(1);
  var stbl = mp4Box('stbl', mp4Stsd(opt.width, opt.height, opt.avcC), mp4Stts(samples.length), mp4Stss(sync), mp4Stsc(), mp4Stsz(sizes), mp4Stco(offsets));
  var minf = mp4Box('minf', mp4Vmhd(), mp4Dinf(), stbl);
  var mdia = mp4Box('mdia', mp4Mdhd(opt.timescale, samples.length), mp4Hdlr(), minf);
  var trak = mp4Box('trak', mp4Tkhd(opt.width, opt.height, samples.length), mdia);
  var moov = mp4Box('moov', mp4Mvhd(opt.timescale, samples.length), trak);
  return bytesJoin([ftyp, mdat, moov]);
}

function downloadBlob(blob, name) {
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = name;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  setTimeout(function () { URL.revokeObjectURL(url); }, 1000);
}

function renderFileName(ext) {
  var d = new Date();
  var pad = function (n) { return String(n).padStart(2, '0'); };
  return 'mmd_render_' + d.getFullYear() + pad(d.getMonth() + 1) + pad(d.getDate()) + '_' + pad(d.getHours()) + pad(d.getMinutes()) + pad(d.getSeconds()) + ext;
}

function h264Codec(w, h) {
  var mbs = Math.ceil(w / 16) * Math.ceil(h / 16);
  var lvl = mbs <= 1620 ? 30 : mbs <= 3600 ? 31 : mbs <= 5120 ? 32 :
            mbs <= 8192 ? 40 : mbs <= 8704 ? 42 : mbs <= 22080 ? 50 :
            mbs <= 36864 ? 51 : 52;
  var ll = lvl.toString(16).toUpperCase();
  if (ll.length < 2) ll = '0' + ll;
  return 'avc1.6400' + ll;
}

async function renderMp4H264() {
  if (rendering) return;
  if (!ready || !mmdRuntime) { appendLog('[render] Not ready: ready=' + ready + ' mmdRuntime=' + !!mmdRuntime); setStatus('Not ready'); return; }
  if (!window.VideoEncoder || !window.VideoFrame) { appendLog('[render] VideoEncoder or VideoFrame not available'); setStatus('MP4 H.264 unsupported'); return; }
  rendering = true;
  var button = el('renderMp4');
  if (button) button.disabled = true;
  var savedFrame = currentFrameTime;
  var wasPlaying = playing;
  var fps = parseInt((el('renderFps') || {}).value, 10) || 30;
  var bitrate = parseInt((el('renderBitrate') || {}).value, 10) || 8000000;
  var frameDurationUs = Math.round(1000000 / fps);
  var frameCount = Math.max(1, Math.floor(duration / FPS * fps) + 1);
  var width = canvas.width & ~1;
  var height = canvas.height & ~1;
  var source = canvas;
  var encodeCanvas = canvas;
  var ctx = null;
  var chunks = [];
  var samples = [];
  var avcC = null;
  var encoderError = null;
  try {
    if (width <= 0 || height <= 0) { appendLog('[render] Size error: ' + width + 'x' + height); setStatus('Render size error'); return; }
    if (width !== canvas.width || height !== canvas.height) {
      encodeCanvas = document.createElement('canvas');
      encodeCanvas.width = width;
      encodeCanvas.height = height;
      ctx = encodeCanvas.getContext('2d', { alpha: false });
    }
    var config = { codec: h264Codec(width, height), width: width, height: height, bitrate: bitrate, framerate: fps, latencyMode: 'realtime', hardwareAcceleration: 'no-preference', avc: { format: 'avc' } };
    var support = await VideoEncoder.isConfigSupported(config).catch(function () { return null; });
    if (!support || !support.supported) {
      appendLog('[render] realtime config not supported, retry without latencyMode');
      delete config.latencyMode;
      support = await VideoEncoder.isConfigSupported(config).catch(function () { return null; });
    }
    if (!support || !support.supported) { appendLog('[render] H.264 config not supported: ' + JSON.stringify(config)); setStatus('MP4 H.264 unsupported'); return; }
    if (support.config) { support.config.avc = { format: 'avc' }; config = support.config; }
    var encoder = new VideoEncoder({
      output: function (chunk, metadata) {
        var data = new Uint8Array(chunk.byteLength);
        chunk.copyTo(data);
        chunks.push(data);
        samples.push({ size: data.byteLength, key: chunk.type === 'key' });
        if (metadata && metadata.decoderConfig && metadata.decoderConfig.description) avcC = new Uint8Array(metadata.decoderConfig.description);
      },
      error: function (e) {
        encoderError = e;
        appendLog('render encoder error: ' + (e && e.message ? e.message : String(e)));
      }
    });
    encoder.configure(config);
    if (wasPlaying) mmdRuntime.pauseAnimation();
    appendLog('[render] start ' + width + 'x' + height + ' ' + fps + 'fps ' + frameCount + 'frames ' + config.codec);
    setStatus('Rendering 0/' + frameCount);
    if (physicsReady && physicsModeEnabled()) initAllPhysics();
    for (var i = 0; i < frameCount; i++) {
      if (encoderError) throw encoderError;
      var frameTime = Math.min(duration, i * FPS / fps);
      currentFrameTime = frameTime;
      await mmdRuntime.seekAnimation(frameTime, true);
      scene.render();
      if (ctx) ctx.drawImage(source, 0, 0, width, height);
      var vf;
      try {
        vf = new VideoFrame(encodeCanvas, { timestamp: i * frameDurationUs, duration: frameDurationUs });
      } catch (e) {
        appendLog('[render] VideoFrame error at frame ' + i + ': ' + (e && e.message ? e.message : String(e)));
        throw e;
      }
      encoder.encode(vf, { keyFrame: i % fps === 0 });
      vf.close();
      while (encoder.encodeQueueSize > 2) {
        await new Promise(function (resolve) { setTimeout(resolve, 0); });
        if (encoderError) throw encoderError;
      }
      if (i % 10 === 0) {
        var pct = Math.round((i + 1) / frameCount * 100);
        appendLog('[render] ' + (i + 1) + '/' + frameCount + ' (' + pct + '%)');
        setStatus('Rendering ' + (i + 1) + '/' + frameCount);
        await new Promise(function (resolve) { setTimeout(resolve, 0); });
      }
    }
    appendLog('[render] flushing encoder (' + chunks.length + ' chunks)...');
    var flushDone = false;
    var flushPromise = encoder.flush().then(function () { flushDone = true; }).catch(function (e) { appendLog('[render] flush error: ' + (e && e.message ? e.message : String(e))); });
    var flushTimeout = new Promise(function (resolve) { setTimeout(resolve, 8000); });
    await Promise.race([flushPromise, flushTimeout]);
    if (!flushDone) appendLog('[render] flush timeout, proceeding with ' + chunks.length + ' chunks');
    try { encoder.close(); } catch (e) {}
    appendLog('[render] flush done, total ' + chunks.length + ' chunks');
    if (encoderError) throw encoderError;
    if (!avcC || chunks.length === 0) { appendLog('[render] MP4 build error: avcC=' + !!avcC + ' chunks=' + chunks.length); setStatus('MP4 build error'); return; }
    var mp4 = buildMp4(chunks, samples, { width: width, height: height, timescale: fps, avcC: avcC });
    try {
      downloadBlob(new Blob([mp4], { type: 'video/mp4' }), renderFileName('.mp4'));
    } catch (e) {
      appendLog('[render] download error (permission?): ' + (e && e.message ? e.message : String(e)));
      setStatus('Download error');
      return;
    }
    setStatus('Rendered MP4');
  } catch (e) {
    appendLog('render mp4 error: ' + (e && e.message ? e.message : String(e)) + (e && e.stack ? '\n' + e.stack : ''));
    setStatus('Render error');
  } finally {
    try {
      await mmdRuntime.seekAnimation(savedFrame, true);
      currentFrameTime = savedFrame;
      updateSeekUI(true);
      if (wasPlaying) await mmdRuntime.playAnimation();
    } catch (e) { appendLog('[render] restore error: ' + (e && e.message ? e.message : String(e))); }
    chunks.length = 0;
    samples.length = 0;
    if (button) button.disabled = false;
    rendering = false;
  }
}

function updateFps(now) {
  if (!fpsEnabled()) return;
  fpsSampleFrames++;
  if (!fpsSampleTime) { fpsSampleTime = now; return; }
  var elapsed = now - fpsSampleTime;
  if (elapsed >= 500) {
    el('fps').textContent = Math.round(fpsSampleFrames * 1000 / elapsed) + ' fps';
    fpsSampleTime = now;
    fpsSampleFrames = 0;
  }
}

/* ====== File utilities ====== */
function normPath(p) {
  var parts = String(p).replace(/\\/g, '/').split('/');
  var out = [];
  for (var i = 0; i < parts.length; i++) {
    var s = parts[i].trim();
    if (s === '' || s === '.') continue;
    if (s === '..') { out.pop(); continue; }
    out.push(s);
  }
  return out.join('/').toLowerCase();
}

function baseOf(name) { var n = String(name).replace(/\\/g, '/'); return n.substring(n.lastIndexOf('/') + 1).trim(); }
function stripExt(name) { var b = baseOf(name); var p = b.lastIndexOf('.'); return p > 0 ? b.substring(0, p) : b; }
function dirOf(p) { var n = normPath(p); var i = n.lastIndexOf('/'); return i < 0 ? '' : n.substring(0, i); }
function normName(s) { return String(s || '').replace(/\u0000/g, '').replace(/\s+/g, '').toLowerCase(); }
function extOk(name, exts) { var n = name.toLowerCase(); for (var i = 0; i < exts.length; i++) if (n.endsWith(exts[i])) return true; return false; }

function buildFileMaps(entries) {
  filePathMap = {}; fileBaseMap = {};
  for (var i = 0; i < entries.length; i++) {
    var entry = entries[i];
    var path = normPath(entry.path);
    var base = baseOf(path).toLowerCase();
    filePathMap[path] = entry;
    if (!fileBaseMap[base]) fileBaseMap[base] = [];
    fileBaseMap[base].push(entry);
  }
}

function sortEntries(entries) {
  entries.sort(function (a, b) { return normPath(a.path).localeCompare(normPath(b.path)); });
}

function removeFromFolder(entry) {
  var p = normPath(entry.path);
  for (var i = 0; i < folderFiles.length; i++) {
    if (normPath(folderFiles[i].path) === p) { folderFiles.splice(i, 1); break; }
  }
  buildFileMaps(folderFiles);
}

function revoke(list) {
  for (var i = 0; i < list.length; i++) URL.revokeObjectURL(list[i]);
  list.length = 0;
}

function readAscii(bytes, start, len) {
  var s = ''; var max = Math.min(bytes.length, start + len);
  for (var i = start; i < max; i++) { if (bytes[i] === 0) break; s += String.fromCharCode(bytes[i]); }
  return s;
}

function decodeName(bytes) {
  var sub = bytes.slice(); var end = sub.length;
  for (var i = 0; i < sub.length; i++) { if (sub[i] === 0) { end = i; break; } }
  sub = sub.slice(0, end);
  try { return new TextDecoder('shift_jis').decode(sub).trim(); } catch (e) {}
  var s = ''; for (var i = 0; i < sub.length; i++) s += String.fromCharCode(sub[i]); return s.trim();
}

function vmdLayout(view, offset) {
  if (offset + 4 > view.byteLength) return null;
  var bone = view.getUint32(offset, true); offset += 4;
  if (bone > 1000000) return null; offset += bone * 111;
  if (offset + 4 > view.byteLength) return null;
  var morph = view.getUint32(offset, true); offset += 4;
  if (morph > 1000000) return null; offset += morph * 23;
  if (offset + 4 > view.byteLength) return null;
  var camera = view.getUint32(offset, true); offset += 4;
  if (camera > 1000000) return null; offset += camera * 61;
  if (offset > view.byteLength) return null;
  return { bone: bone, morph: morph, camera: camera };
}

function analyzeVmd(buffer) {
  var bytes = new Uint8Array(buffer);
  var header = readAscii(bytes, 0, 30);
  if (header.indexOf('Vocaloid Motion Data') !== 0) return { valid: false, bone: 0, morph: 0, camera: 0, modelKey: '' };
  var modelName = decodeName(bytes.slice(30, 50));
  var view = new DataView(buffer);
  var layout = vmdLayout(view, 50) || vmdLayout(view, 40);
  if (!layout) return { valid: false, bone: 0, morph: 0, camera: 0, modelKey: normName(modelName) };
  return { valid: true, bone: layout.bone, morph: layout.morph, camera: layout.camera, modelKey: normName(modelName) };
}

async function inspectFolder(entries) {
  sortEntries(entries);
  buildFileMaps(entries);
  modelEntries = []; motionEntries = []; cameraEntries = []; audioEntries = [];
  for (var i = 0; i < entries.length; i++) {
    var entry = entries[i];
    if (extOk(entry.name, ['.pmx'])) modelEntries.push(entry);
    else if (extOk(entry.name, ['.mp3', '.wav'])) audioEntries.push(entry);
  }
  modelEntries.sort(function (a, b) { return normPath(a.path).localeCompare(normPath(b.path)); });
  var vmds = entries.filter(function (e) { return extOk(e.name, ['.vmd']); });
  for (var i = 0; i < vmds.length; i++) {
    try {
      var result = analyzeVmd(await vmds[i].file.arrayBuffer());
      vmds[i].modelKey = result.modelKey;
      if (result.valid && result.camera > 0) cameraEntries.push(vmds[i]);
      if (result.valid && (result.bone > 0 || result.morph > 0)) motionEntries.push(vmds[i]);
    } catch (e) {}
  }
}

function mergeFiles(entries) {
  var seen = {};
  for (var i = 0; i < folderFiles.length; i++) {
    var e = folderFiles[i];
    seen[normPath(e.path) + ':' + e.file.size + ':' + e.file.lastModified] = true;
  }
  for (var i = 0; i < entries.length; i++) {
    var e = entries[i];
    var key = normPath(e.path) + ':' + e.file.size + ':' + e.file.lastModified;
    if (!seen[key]) { seen[key] = true; folderFiles.push(e); }
  }
}

async function addSelectedFiles(files) {
  var entries = [];
  for (var i = 0; i < files.length; i++) {
    var file = files[i];
    entries.push({ file: file, path: file.webkitRelativePath || file.name, name: file.name, url: '' });
  }
  if (entries.length === 0) return;
  var prevCamEntry = (cameraSel !== 'free' && cameraEntries[cameraSel]) ? cameraEntries[cameraSel] : null;
  var prevAudioEntry = (audioSel >= 0 && audioEntries[audioSel]) ? audioEntries[audioSel] : null;
  mergeFiles(entries);
  if (!folderName) folderName = 'Folder';
  await inspectFolder(folderFiles);
  if (prevCamEntry) { var ci = cameraEntries.indexOf(prevCamEntry); if (ci >= 0) cameraSel = ci; }
  if (prevAudioEntry) { var ai = audioEntries.indexOf(prevAudioEntry); if (ai >= 0) audioSel = ai; }
  renderAll();
  setStatus(modelEntries.length > 0 ? '' : 'No PMX found');
}

async function addZipFile(file) {
  if (!window.JSZip) return;
  var zip = await window.JSZip.loadAsync(file, { decodeFileName: function (bytes) {
    try { return new TextDecoder('shift_jis').decode(bytes); } catch (e) { return new TextDecoder('utf-8').decode(bytes); }
  }});
  var entries = [];
  var names = Object.keys(zip.files);
  for (var i = 0; i < names.length; i++) {
    var zipEntry = zip.files[names[i]];
    if (zipEntry.dir) continue;
    var blob = await zipEntry.async('blob');
    entries.push({ file: new File([blob], baseOf(zipEntry.name), { type: blob.type }), path: zipEntry.name, name: baseOf(zipEntry.name), url: '' });
  }
  if (entries.length === 0) return;
  var prevCamEntry = (cameraSel !== 'free' && cameraEntries[cameraSel]) ? cameraEntries[cameraSel] : null;
  var prevAudioEntry = (audioSel >= 0 && audioEntries[audioSel]) ? audioEntries[audioSel] : null;
  mergeFiles(entries);
  if (!folderName) folderName = file.name;
  await inspectFolder(folderFiles);
  if (prevCamEntry) { var ci = cameraEntries.indexOf(prevCamEntry); if (ci >= 0) cameraSel = ci; }
  if (prevAudioEntry) { var ai = audioEntries.indexOf(prevAudioEntry); if (ai >= 0) audioSel = ai; }
  renderAll();
  setStatus(modelEntries.length > 0 ? '' : 'No PMX found');
}

function resetDetected() {
  folderName = ''; folderFiles = []; modelEntries = []; motionEntries = [];
  cameraEntries = []; audioEntries = [];
  filePathMap = {}; fileBaseMap = {};
  updateResetButton();
}

function currentChar() {
  for (var i = 0; i < characters.length; i++) if (characters[i].id === selectedCharId) return characters[i];
  return null;
}

function disposeMoveGizmos() {
  if (moveGizmo) {
    try { moveGizmo.attachedNode = null; } catch (e) {}
    try { moveGizmo.attachedMesh = null; } catch (e) {}
    try { moveGizmo.isEnabled = false; } catch (e) {}
    try { moveGizmo.dispose(); } catch (e) {}
    moveGizmo = null;
  }
  if (rotateGizmo) {
    try { rotateGizmo.attachedNode = null; } catch (e) {}
    try { rotateGizmo.attachedMesh = null; } catch (e) {}
    try { rotateGizmo.isEnabled = false; } catch (e) {}
    try { rotateGizmo.dispose(); } catch (e) {}
    rotateGizmo = null;
  }
  if (moveGizmoLayer) {
    try { moveGizmoLayer.dispose(); } catch (e) {}
    moveGizmoLayer = null;
  }
  moveGizmoDragBound = false;
  rotateGizmoDragBound = false;
}

function ensureMoveGizmos() {
  if (!scene || !BABYLON.UtilityLayerRenderer || !BABYLON.PositionGizmo || !BABYLON.RotationGizmo) return null;
  if (!moveGizmoLayer) moveGizmoLayer = new BABYLON.UtilityLayerRenderer(scene);
  if (!moveGizmo) {
    moveGizmo = new BABYLON.PositionGizmo(moveGizmoLayer);
    moveGizmo.scaleRatio = 1.1;
    moveGizmo.updateGizmoRotationToMatchAttachedMesh = false;
    moveGizmo.isEnabled = false;
  }
  if (!rotateGizmo) {
    rotateGizmo = new BABYLON.RotationGizmo(moveGizmoLayer);
    rotateGizmo.scaleRatio = 1.25;
    rotateGizmo.updateGizmoRotationToMatchAttachedMesh = false;
    rotateGizmo.isEnabled = false;
  }
  if (moveGizmo.onDragObservable && !moveGizmoDragBound) {
    moveGizmo.onDragObservable.add(syncTransformInputs);
    moveGizmoDragBound = true;
  }
  if (rotateGizmo.onDragObservable && !rotateGizmoDragBound) {
    rotateGizmo.onDragObservable.add(syncTransformInputs);
    rotateGizmoDragBound = true;
  }
  return true;
}

function attachMoveGizmoTo(ch) {
  var node = ch && ch.moveRoot ? ch.moveRoot : null;
  var on = !!node && gizmoModeEnabled();
  if (!on) {
    disposeMoveGizmos();
    return;
  }
  var ok = ensureMoveGizmos();
  if (!ok) return;
  moveGizmo.attachedNode = node;
  rotateGizmo.attachedNode = node;
  moveGizmo.isEnabled = true;
  rotateGizmo.isEnabled = true;
}

function updateMoveGizmo() {
  attachMoveGizmoTo(currentChar());
  syncTransformInputs();
}

function gizmoModeEnabled() { var v = el('gizmoMode'); return v ? v.value === 'on' : true; }

function applyGizmoMode() { updateMoveGizmo(); }

function syncTransformInputs() {
  var ch = currentChar();
  var ids = ['posX', 'posY', 'posZ', 'rotX', 'rotY', 'rotZ'];
  if (!ch || !ch.moveRoot) {
    for (var i = 0; i < ids.length; i++) { var n = el(ids[i]); if (n) n.value = '0'; }
    return;
  }
  var p = ch.moveRoot.position, r = ch.moveRoot.rotation, deg = 180 / Math.PI;
  if (el('posX')) el('posX').value = p.x.toFixed(2);
  if (el('posY')) el('posY').value = p.y.toFixed(2);
  if (el('posZ')) el('posZ').value = p.z.toFixed(2);
  if (el('rotX')) el('rotX').value = (r.x * deg).toFixed(1);
  if (el('rotY')) el('rotY').value = (r.y * deg).toFixed(1);
  if (el('rotZ')) el('rotZ').value = (r.z * deg).toFixed(1);
}

function applyTransformInputs() {
  var ch = currentChar();
  if (!ch || !ch.moveRoot) return;
  var rad = Math.PI / 180;
  var px = parseFloat((el('posX') || {}).value); if (!isFinite(px)) px = ch.moveRoot.position.x;
  var py = parseFloat((el('posY') || {}).value); if (!isFinite(py)) py = ch.moveRoot.position.y;
  var pz = parseFloat((el('posZ') || {}).value); if (!isFinite(pz)) pz = ch.moveRoot.position.z;
  var rx = parseFloat((el('rotX') || {}).value); if (!isFinite(rx)) rx = ch.moveRoot.rotation.x / rad;
  var ry = parseFloat((el('rotY') || {}).value); if (!isFinite(ry)) ry = ch.moveRoot.rotation.y / rad;
  var rz = parseFloat((el('rotZ') || {}).value); if (!isFinite(rz)) rz = ch.moveRoot.rotation.z / rad;
  ch.moveRoot.position.set(px, py, pz);
  ch.moveRoot.rotation.set(rx * rad, ry * rad, rz * rad);
}

function createMoveRootForCharacter(ch) {
  var root = new BABYLON.TransformNode('characterMoveRoot_' + ch.id, scene);
  var nodes = [];
  if (ch.container && ch.container.transformNodes) {
    for (var i = 0; i < ch.container.transformNodes.length; i++) nodes.push(ch.container.transformNodes[i]);
  }
  if (ch.container && ch.container.meshes) {
    for (var j = 0; j < ch.container.meshes.length; j++) nodes.push(ch.container.meshes[j]);
  }
  var roots = [];
  for (var k = 0; k < nodes.length; k++) {
    var node = nodes[k];
    if (node && node !== root && !node.parent) roots.push(node);
  }
  if (roots.length === 0 && ch.mesh) roots.push(ch.mesh);
  for (var r = 0; r < roots.length; r++) {
    if (roots[r].setParent) roots[r].setParent(root);
    else roots[r].parent = root;
  }
  ch.moveRoot = root;
}

/* ====== Build reference files for babylon-mmd ====== */
function buildReferenceFiles(modelEntry) {
  var modelPath = normPath(modelEntry.path);
  var modelDir = dirOf(modelPath);
  var out = [], rootFile = null;
  for (var i = 0; i < folderFiles.length; i++) {
    var entry = folderFiles[i];
    var entryPath = normPath(entry.path);
    var relPath;
    if (modelDir && entryPath.indexOf(modelDir + '/') === 0) {
      relPath = entryPath.substring(modelDir.length + 1);
    } else {
      relPath = entry.name;
    }
    var cloned = new File([entry.file], baseOf(relPath) || entry.name, { type: entry.file.type });
    Object.defineProperty(cloned, 'webkitRelativePath', { value: relPath, configurable: true });
    out.push(cloned);
    if (entryPath === modelPath) rootFile = cloned;
  }
  return { files: out, rootFile: rootFile };
}

/* ====== Scene management ====== */
function clearScene() {
  if (audioPlayer && mmdRuntime) { try { mmdRuntime.setAudioPlayer(null); } catch (e) {} }
  if (audioUrl) { URL.revokeObjectURL(audioUrl); audioUrl = null; }
  audioPlayer = null; audioSel = -1;
  if (mmdCamNode) {
    if (mmdRuntime) { try { mmdRuntime.removeAnimatable(mmdCamNode); } catch (e) {} }
    mmdCamNode.dispose();
    mmdCamNode = null;
  }
  cameraSel = 'free';
  scene.activeCamera = arcCamera;
  arcCamera.attachControl(canvas, true);
  attachMoveGizmoTo(null);
  for (var i = 0; i < characters.length; i++) {
    var c = characters[i];
    if (c.model && mmdRuntime) { try { mmdRuntime.destroyMmdModel(c.model); } catch (e) {} }
    if (c.container) { try { c.container.dispose(); } catch (e) {} }
    if (c.moveRoot) { c.moveRoot.dispose(); c.moveRoot = null; }
  }
  characters = []; selectedCharId = -1; charSeq = 0;
  applyShadows();
  if (mmdRuntime) { mmdRuntime.dispose(scene); mmdRuntime = null; }
  if (modelFpsLimiterObserver && scene) scene.onBeforeRenderObservable.remove(modelFpsLimiterObserver);
  modelFpsLimiterObserver = null;
  clearModelFpsLimiterState();
  reattachPipelineCamera();
  ready = false;
  playing = false;
  duration = 0;
  currentFrameTime = 0;
  el('play').disabled = true;
  updatePlayBtn();
  refreshSeekRange();
  updateResetButton();
}

function updateResetButton() {
  el('reset').disabled = folderFiles.length === 0 && characters.length === 0;
}

/* ====== Runtime / characters ====== */
function ensureRuntime() {
  if (mmdRuntime) return mmdRuntime;
  var mmdPhysics = physicsReady ? new BABYLONMMD.MmdBulletPhysics(physicsRuntime) : null;
  mmdRuntime = new BABYLONMMD.MmdRuntime(scene, mmdPhysics);
  mmdRuntime.register(scene);
  ensureModelFpsLimiter();
  mmdRuntime.timeScale = currentPlaybackSpeed();
  mmdRuntime.onAnimationTickObservable.add(function () {
    if (!draggingSeek) {
      currentFrameTime = mmdRuntime.currentFrameTime;
      updateSeekUI(false);
    }
  });
  mmdRuntime.onPlayAnimationObservable.add(function () { playing = true; updatePlayBtn(); });
  mmdRuntime.onPauseAnimationObservable.add(function () { playing = false; updatePlayBtn(); });
  return mmdRuntime;
}

function refreshDuration() {
  duration = mmdRuntime ? mmdRuntime.animationFrameTimeDuration : 0;
  refreshSeekRange();
}

function updateReady() {
  ready = !!mmdRuntime && (characters.length > 0 || !!mmdCamNode);
  el('play').disabled = !ready;
  if (!ready) { playing = false; updatePlayBtn(); }
  updateResetButton();
}

async function addCharacter(entry) {
  ensureRuntime();
  buildFileMaps(folderFiles);
  setStatus('Loading');
  try {
    var refs = buildReferenceFiles(entry);
    if (!refs.rootFile) { setStatus('PMX normalize error'); return; }
    var loaderOpts = { loggingEnabled: false, referenceFiles: refs.files };
    if (materialBuilder) loaderOpts.materialBuilder = materialBuilder;
    var result = await BABYLON.LoadAssetContainerAsync(refs.rootFile, scene, {
      pluginExtension: '.pmx',
      pluginOptions: { mmdmodel: loaderOpts }
    });
    result.addAllToScene();
    var mesh = result.meshes.length > 0 ? result.meshes[0] : null;
    if (!mesh) { result.dispose(); setStatus('Load error'); return; }
    var modelOpts = {
      buildPhysics: physicsReady ? {
        disableBidirectionalTransformation: true,
        disableOffsetForConstraintFrame: true
      } : false
    };
    if (BABYLONMMD.MmdStandardMaterialProxy) modelOpts.materialProxyConstructor = BABYLONMMD.MmdStandardMaterialProxy;
    var model = mmdRuntime.createMmdModel(mesh, modelOpts);
    var ch = { id: ++charSeq, entry: entry, container: result, model: model, mesh: mesh, motions: [], animHandle: null, moveRoot: null, toonMode: 'off', flatToonBrightness: 1 };
    createMoveRootForCharacter(ch);
    characters.push(ch);
    selectedCharId = ch.id;
    updateMoveGizmo();
    applyIkModeTo(ch);
    applyPhysicsModeTo(ch);
    applyToonModeToCharacter(ch);
    applyShadows();
    if (characters.length === 1 && cameraSel === 'free') fitCamera(result.meshes);
    refreshDuration();
    updateReady();
    renderAll();
    setStatus('');
  } catch (e) {
    appendLog('addCharacter error: ' + (e && e.message ? e.message : String(e)) + (e && e.stack ? '\n' + e.stack : ''));
    setStatus('Load error');
  }
}

function removeCharacter(id) {
  var idx = -1;
  for (var i = 0; i < characters.length; i++) if (characters[i].id === id) { idx = i; break; }
  if (idx < 0) return;
  var ch = characters[idx];
  if (selectedCharId === id) attachMoveGizmoTo(null);
  if (ch.model && mmdRuntime) { try { mmdRuntime.destroyMmdModel(ch.model); } catch (e) {} }
  if (ch.container) { try { ch.container.dispose(); } catch (e) {} }
  if (ch.moveRoot) { ch.moveRoot.dispose(); ch.moveRoot = null; }
  if (forcedGroundShadows[String(ch.id)]) {
    try { forcedGroundShadows[String(ch.id)].dispose(); } catch (e) {}
    delete forcedGroundShadows[String(ch.id)];
  }
  characters.splice(idx, 1);
  applyShadows();
  if (selectedCharId === id) selectedCharId = characters.length > 0 ? characters[0].id : -1;
  updateMoveGizmo();
  refreshDuration();
  updateReady();
  renderAll();
}

async function applyCharacterMotions(ch) {
  if (!ch.model) return;
  setStatus('Loading');
  try {
    if (ch.animHandle) { try { ch.model.destroyRuntimeAnimation(ch.animHandle); } catch (e) {} ch.animHandle = null; }
    if (ch.motions.length > 0) {
      var vmdLoader = new BABYLONMMD.VmdLoader(scene);
      var files = ch.motions.map(function (e) { return e.file; });
      var anim = await vmdLoader.loadAsync('motion_' + ch.id, files.length === 1 ? files[0] : files);
      ch.animHandle = ch.model.createRuntimeAnimation(anim);
      ch.model.setRuntimeAnimation(ch.animHandle);
    } else {
      ch.model.setRuntimeAnimation(null);
    }
    mmdRuntime.onAnimationDurationChangedObservable.notifyObservers();
    refreshDuration();
    if (mmdRuntime) {
      await mmdRuntime.seekAnimation(currentFrameTime, true);
      if (physicsReady && physicsModeEnabled() && ch.model) mmdRuntime.initializeMmdModelPhysics(ch.model);
    }
    setStatus('');
  } catch (e) {
    appendLog('applyCharacterMotions error: ' + (e && e.message ? e.message : String(e)));
    setStatus('Animation error');
  }
}

async function addMotionToSelected(entry) {
  var ch = currentChar();
  if (!ch) { setStatus('Select a character'); return; }
  ch.motions.push(entry);
  await applyCharacterMotions(ch);
  renderAll();
}

async function removeMotionFromChar(ch, idx) {
  ch.motions.splice(idx, 1);
  await applyCharacterMotions(ch);
  renderAll();
}

async function setCamera(sel) {
  ensureRuntime();
  if (mmdCamNode) {
    try { mmdRuntime.removeAnimatable(mmdCamNode); } catch (e) {}
    mmdCamNode.dispose();
    mmdCamNode = null;
  }
  if (sel === 'free') {
    cameraSel = 'free';
    scene.activeCamera = arcCamera;
    arcCamera.attachControl(canvas, true);
    reattachPipelineCamera();
    updateReady();
    return;
  }
  var idx = parseInt(sel, 10);
  if (!(idx >= 0 && idx < cameraEntries.length)) { cameraSel = 'free'; renderCameraSelect(); return; }
  cameraSel = idx;
  setStatus('Loading');
  try {
    var vmdLoader = new BABYLONMMD.VmdLoader(scene);
    var camAnim = await vmdLoader.loadAsync('camera', cameraEntries[idx].file);
    mmdCamNode = new BABYLONMMD.MmdCamera('mmdCam', new BABYLON.Vector3(0, 10, 0), scene);
    var camHandle = mmdCamNode.createRuntimeAnimation(camAnim);
    mmdCamNode.setRuntimeAnimation(camHandle);
    mmdRuntime.addAnimatable(mmdCamNode);
    arcCamera.detachControl();
    scene.activeCamera = mmdCamNode;
    reattachPipelineCamera();
    refreshDuration();
    updateReady();
    setStatus('');
  } catch (e) {
    appendLog('setCamera error: ' + (e && e.message ? e.message : String(e)));
    setStatus('Camera error');
    cameraSel = 'free';
    scene.activeCamera = arcCamera;
    arcCamera.attachControl(canvas, true);
    renderCameraSelect();
  }
}

async function setAudio(sel) {
  ensureRuntime();
  if (audioUrl) { URL.revokeObjectURL(audioUrl); audioUrl = null; }
  if (sel === 'none') {
    audioSel = -1;
    if (mmdRuntime) { try { await mmdRuntime.setAudioPlayer(null); } catch (e) {} }
    audioPlayer = null;
    return;
  }
  var idx = parseInt(sel, 10);
  if (!(idx >= 0 && idx < audioEntries.length)) { audioSel = -1; renderAudioSelect(); return; }
  audioSel = idx;
  setStatus('Loading');
  try {
    audioUrl = URL.createObjectURL(audioEntries[idx].file);
    audioPlayer = new BABYLONMMD.StreamAudioPlayer(scene);
    audioPlayer.source = audioUrl;
    audioPlayer.volume = currentAudioVolume();
    audioPlayer.playbackRate = currentPlaybackSpeed();
    await mmdRuntime.setAudioPlayer(audioPlayer);
    setStatus('');
  } catch (e) {
    appendLog('setAudio error: ' + (e && e.message ? e.message : String(e)));
    setStatus('Audio error');
    audioSel = -1;
    audioPlayer = null;
    renderAudioSelect();
  }
}

function fitCamera(meshes) {
  var min = null, max = null;
  for (var i = 0; i < meshes.length; i++) {
    var mesh = meshes[i];
    if (!mesh.getBoundingInfo) continue;
    mesh.computeWorldMatrix(true);
    var box = mesh.getBoundingInfo().boundingBox;
    var bmin = box.minimumWorld, bmax = box.maximumWorld;
    if (!isFinite(bmin.x) || !isFinite(bmax.x)) continue;
    if (!min) { min = bmin.clone(); max = bmax.clone(); } else {
      min = BABYLON.Vector3.Minimize(min, bmin);
      max = BABYLON.Vector3.Maximize(max, bmax);
    }
  }
  if (!min || !max) return;
  var center = min.add(max).scale(0.5);
  var size = max.subtract(min).length();
  var radius = Math.max(size * 1.2, 8);
  arcCamera.setTarget(center);
  arcCamera.radius = radius;
  arcCamera.alpha = -Math.PI / 2;
  arcCamera.beta = Math.PI / 2.2;
  arcCamera.maxZ = Math.max(radius * 20, 1000);
  arcCamera.lowerRadiusLimit = Math.max(radius * 0.02, 0.5);
  arcCamera.upperRadiusLimit = Math.max(radius * 8, 100);
}

/* ====== Playback ====== */
function refreshSeekRange() {
  var total = Math.max(0, Math.round(duration));
  el('seek').max = total; el('seek').disabled = total === 0;
  el('frame').max = total; el('frame').disabled = total === 0;
  el('frameTotal').textContent = '/ ' + total;
  updateSeekUI(true);
}

function updatePlayBtn() {
  var btn = el('play');
  if (!btn) return;
  var img = btn.querySelector('img');
  if (!img) { img = document.createElement('img'); btn.textContent = ''; btn.appendChild(img); }
  img.src = playing ? 'img/pause.svg' : 'img/play.svg';
  img.alt = playing ? 'Pause' : 'Play';
  btn.setAttribute('aria-label', playing ? 'Pause' : 'Play');
}

function updateSeekUI(force) {
  var fr = Math.round(currentFrameTime);
  if (!draggingSeek) el('seek').value = fr;
  if (force || document.activeElement !== el('frame')) el('frame').value = fr;
}

async function seekToFrame(fr) {
  if (!ready || !mmdRuntime) return;
  var total = Math.round(duration);
  fr = Math.max(0, Math.min(fr, total));
  var jumped = Math.abs(fr - currentFrameTime) > 60;
  currentFrameTime = fr;
  updateSeekUI(true);
  await mmdRuntime.seekAnimation(fr, true);
  clearModelFpsLimiterState();
  if (jumped && physicsReady && physicsModeEnabled()) {
    initAllPhysics();
  }
}

async function togglePlay() {
  if (!ready || !mmdRuntime) return;
  if (playing) {
    mmdRuntime.pauseAnimation();
  } else {
    clearModelFpsLimiterState();
    await mmdRuntime.playAnimation();
  }
}

/* ====== UI rendering ====== */
function makeItem(label, onSelect, onRemove, selected) {
  var item = document.createElement('span');
  item.className = selected ? 'item selected' : 'item';
  var name = document.createElement(onSelect ? 'button' : 'span');
  name.className = 'name'; name.textContent = label;
  if (onSelect) name.addEventListener('click', onSelect);
  item.appendChild(name);
  if (onRemove) {
    var rem = document.createElement('button');
    rem.className = 'remove'; rem.type = 'button'; rem.textContent = '×';
    rem.addEventListener('click', onRemove);
    item.appendChild(rem);
  }
  return item;
}

function renderFolder() {
  var box = el('folderList'); box.innerHTML = '';
  if (!folderName) return;
  box.appendChild(makeItem(folderName, null, function () {
    resetDetected(); clearScene(); revoke(runtimeUrls); renderAll(); setStatus('');
  }, false));
}

function renderModelPool() {
  var box = el('modelPool'); box.innerHTML = '';
  for (var i = 0; i < modelEntries.length; i++) {
    (function (entry, idx) {
      box.appendChild(makeItem(entry.name, function () {
        addCharacter(entry);
      }, function () {
        modelEntries.splice(idx, 1); removeFromFolder(entry); renderAll();
      }, false));
    })(modelEntries[i], i);
  }
}

function renderCharacters() {
  var box = el('characterList'); box.innerHTML = '';
  for (var i = 0; i < characters.length; i++) {
    (function (ch) {
      var wrap = document.createElement('div');
      wrap.className = ch.id === selectedCharId ? 'charRow selected' : 'charRow';
      var head = document.createElement('div'); head.className = 'charHead';
      var sel = document.createElement('button');
      sel.type = 'button'; sel.className = 'charName'; sel.textContent = ch.entry.name;
      sel.addEventListener('click', function () { selectedCharId = ch.id; updateMoveGizmo(); applyShadows(); renderCharacters(); });
      var rem = document.createElement('button');
      rem.type = 'button'; rem.className = 'charRemove'; rem.textContent = '×';
      rem.addEventListener('click', function () { removeCharacter(ch.id); });
      head.appendChild(sel); head.appendChild(rem);
      wrap.appendChild(head);
      var anims = document.createElement('div'); anims.className = 'charAnims';
      if (ch.motions.length === 0) {
        var none = document.createElement('span');
        none.className = 'charAnimEmpty'; none.textContent = '(no animation)';
        anims.appendChild(none);
      } else {
        for (var j = 0; j < ch.motions.length; j++) {
          (function (motion, mj) {
            var chip = document.createElement('span'); chip.className = 'animChip';
            var nm = document.createElement('span'); nm.textContent = motion.name;
            var x = document.createElement('button'); x.type = 'button'; x.textContent = '×';
            x.addEventListener('click', function () { removeMotionFromChar(ch, mj); });
            chip.appendChild(nm); chip.appendChild(x);
            anims.appendChild(chip);
          })(ch.motions[j], j);
        }
      }
      wrap.appendChild(anims);
      box.appendChild(wrap);
    })(characters[i]);
  }
  syncCharacterToonModeControl();
}

function renderMotionPool() {
  var box = el('motionPool'); box.innerHTML = '';
  for (var i = 0; i < motionEntries.length; i++) {
    (function (entry, idx) {
      box.appendChild(makeItem(entry.name, function () {
        addMotionToSelected(entry);
      }, function () {
        motionEntries.splice(idx, 1); removeFromFolder(entry); renderAll();
      }, false));
    })(motionEntries[i], i);
  }
}

function renderCameraSelect() {
  var s = el('cameraSelect'); if (!s) return; s.innerHTML = '';
  var o0 = document.createElement('option'); o0.value = 'free'; o0.textContent = 'None'; s.appendChild(o0);
  for (var i = 0; i < cameraEntries.length; i++) {
    var o = document.createElement('option'); o.value = String(i); o.textContent = cameraEntries[i].name; s.appendChild(o);
  }
  s.value = cameraSel === 'free' ? 'free' : (cameraSel < cameraEntries.length ? String(cameraSel) : 'free');
}

function renderAudioSelect() {
  var s = el('audioSelect'); if (!s) return; s.innerHTML = '';
  var o0 = document.createElement('option'); o0.value = 'none'; o0.textContent = 'None'; s.appendChild(o0);
  for (var i = 0; i < audioEntries.length; i++) {
    var o = document.createElement('option'); o.value = String(i); o.textContent = audioEntries[i].name; s.appendChild(o);
  }
  s.value = audioSel < 0 ? 'none' : (audioSel < audioEntries.length ? String(audioSel) : 'none');
}

function renderAll() {
  renderFolder(); renderModelPool(); renderCharacters(); renderMotionPool();
  renderCameraSelect(); renderAudioSelect(); updateResetButton();
}

/* ====== IndexedDB ====== */
function openStudioDb() {
  return new Promise(function (resolve, reject) {
    if (!window.indexedDB) { reject(new Error('No IndexedDB')); return; }
    var req = indexedDB.open(STUDIO_DB, 1);
    req.onupgradeneeded = function () { if (!req.result.objectStoreNames.contains(STUDIO_STORE)) req.result.createObjectStore(STUDIO_STORE); };
    req.onsuccess = function () { resolve(req.result); };
    req.onerror = function () { reject(req.error); };
  });
}

function writeStudioRecord(record) {
  return openStudioDb().then(function (db) {
    return new Promise(function (resolve, reject) {
      var tx = db.transaction(STUDIO_STORE, 'readwrite');
      var store = tx.objectStore(STUDIO_STORE);
      store.clear();
      store.put(record, STUDIO_KEY);
      tx.oncomplete = function () { db.close(); resolve(); };
      tx.onerror = function () { db.close(); reject(tx.error); };
    });
  });
}

function readStudioRecord() {
  return openStudioDb().then(function (db) {
    return new Promise(function (resolve, reject) {
      var tx = db.transaction(STUDIO_STORE, 'readonly');
      var req = tx.objectStore(STUDIO_STORE).get(STUDIO_KEY);
      req.onsuccess = function () { resolve(req.result || null); };
      tx.oncomplete = function () { db.close(); };
      tx.onerror = function () { db.close(); reject(tx.error); };
    });
  });
}

async function saveStudio() {
  if (folderFiles.length === 0) { setStatus('No files'); return; }
  try {
    await writeStudioRecord({
      entries: folderFiles.map(function (e) { return { file: e.file, path: e.path, name: e.name }; }),
      settings: collectSettings()
    });
    setStatus('Saved');
  } catch (e) { setStatus('Save failed'); }
}

async function restoreStudio() {
  var record;
  try { record = await readStudioRecord(); } catch (e) { setStatus('Restore failed'); return; }
  if (!record || !record.entries || record.entries.length === 0) { setStatus('No save'); return; }
  clearScene(); revoke(runtimeUrls); resetDetected();
  clearEffectCode();
  var codeBoxReset = el('codeBox'); if (codeBoxReset) codeBoxReset.value = '';
  var settings = record.settings || {};
  folderName = settings.folderName || 'Studio';
  for (var i = 0; i < record.entries.length; i++) {
    var rec = record.entries[i];
    if (rec.file) folderFiles.push({ file: rec.file, path: rec.path, name: rec.name, url: '' });
  }
  await inspectFolder(folderFiles);
  renderAll();
  await applySettings(settings);
  setStatus('Restored');
}

function collectControlValues() {
  var out = {};
  for (var i = 0; i < SETTING_IDS.length; i++) {
    var node = el(SETTING_IDS[i]);
    if (node) out[SETTING_IDS[i]] = node.value;
  }
  return out;
}

function collectSettings() {
  return {
    folderName: folderName || 'Studio',
    controls: collectControlValues(),
    cameraFree: cameraSel === 'free',
    cameraPath: (cameraSel !== 'free' && cameraEntries[cameraSel]) ? normPath(cameraEntries[cameraSel].path) : '',
    audioPath: (audioSel >= 0 && audioEntries[audioSel]) ? normPath(audioEntries[audioSel].path) : '',
    characters: characters.map(function (c) {
      return {
        modelPath: normPath(c.entry.path),
        position: c.moveRoot ? { x: c.moveRoot.position.x, y: c.moveRoot.position.y, z: c.moveRoot.position.z } : null,
        rotation: c.moveRoot ? { x: c.moveRoot.rotation.x, y: c.moveRoot.rotation.y, z: c.moveRoot.rotation.z } : null,
        toonMode: c.toonMode || 'off',
        flatToonBrightness: clampFlatToonBrightness(c.flatToonBrightness == null ? 1 : c.flatToonBrightness),
        motions: c.motions.map(function (m) { return normPath(m.path); }),
        selected: c.id === selectedCharId
      };
    }),
    effectCode: appliedEffectCode
  };
}

function applyControlValues(controls) {
  if (!controls) return;
  for (var id in controls) {
    if (!controls.hasOwnProperty(id)) continue;
    var node = el(id);
    if (node) node.value = controls[id];
    var range = el(id + 'Range');
    if (range) range.value = controls[id];
  }
}

async function applySettings(s) {
  if (!s) return;
  applyControlValues(s.controls);
  applyView();
  applyLighting();
  applyPixelRatio();
  applyPlaybackSpeed();
  applyAudioVolume();
  applyModelFpsLimit();
  applyPhysicsStep();
  applyEvalType();
  applyUseDelta();
  if (s.characters && s.characters.length > 0) {
    for (var ce = 0; ce < s.characters.length; ce++) {
      var crec = s.characters[ce];
      var ment = filePathMap[crec.modelPath];
      if (!ment) continue;
      var beforeLen = characters.length;
      await addCharacter(ment);
      if (characters.length <= beforeLen) continue;
      var ch = characters[characters.length - 1];
      if (ch.moveRoot && crec.position) ch.moveRoot.position.set(crec.position.x, crec.position.y, crec.position.z);
      if (ch.moveRoot && crec.rotation) ch.moveRoot.rotation.set(crec.rotation.x, crec.rotation.y, crec.rotation.z);
      ch.toonMode = crec.toonMode || 'off';
      ch.flatToonBrightness = clampFlatToonBrightness(crec.flatToonBrightness == null ? 1 : crec.flatToonBrightness);
      applyToonModeToCharacter(ch);
      if (crec.motions && crec.motions.length > 0) {
        ch.motions = [];
        for (var me = 0; me < crec.motions.length; me++) {
          var ment2 = filePathMap[crec.motions[me]];
          if (ment2) ch.motions.push(ment2);
        }
        await applyCharacterMotions(ch);
      }
      if (crec.selected) selectedCharId = ch.id;
    }
    updateMoveGizmo();
  }
  applyPhysicsMode();
  applyIkMode();
  if (s.cameraFree === false && s.cameraPath) {
    var ci = -1;
    for (var i = 0; i < cameraEntries.length; i++) if (normPath(cameraEntries[i].path) === s.cameraPath) { ci = i; break; }
    if (ci >= 0) await setCamera(String(ci));
  }
  if (s.audioPath) {
    var ai = -1;
    for (var j = 0; j < audioEntries.length; j++) if (normPath(audioEntries[j].path) === s.audioPath) { ai = j; break; }
    if (ai >= 0) await setAudio(String(ai));
  }
  applyGlow();
  applyBloom();
  applyDof();
  renderCameraSelect();
  renderAudioSelect();
  renderAll();
  if (s.effectCode) {
    appliedEffectCode = s.effectCode;
    var codeBox = el('codeBox'); if (codeBox) codeBox.value = appliedEffectCode;
    applyEffectCode(appliedEffectCode);
  } else {
    clearEffectCode();
    var codeBox2 = el('codeBox'); if (codeBox2) codeBox2.value = '';
  }
}

function projectFileName() {
  var d = new Date();
  var pad = function (n) { return String(n).padStart(2, '0'); };
  return 'mmd_project_' + d.getFullYear() + pad(d.getMonth() + 1) + pad(d.getDate()) + '_' + pad(d.getHours()) + pad(d.getMinutes()) + pad(d.getSeconds()) + '.json';
}

function exportProject() {
  try {
    var json = JSON.stringify(collectSettings(), null, 2);
    downloadBlob(new Blob([json], { type: 'application/json' }), projectFileName());
    setStatus('Exported');
  } catch (e) { appendLog('export error: ' + (e && e.message ? e.message : String(e))); setStatus('Export failed'); }
}

async function importProject(file) {
  setStatus('Loading');
  try {
    var text = await file.text();
    var s = JSON.parse(text);
    await applySettings(s);
    setStatus('Imported');
  } catch (e) {
    appendLog('import error: ' + (e && e.message ? e.message : String(e)));
    setStatus('Import failed');
  }
}

/* ====== Settings panel ====== */
function openMenu(name) {
  var panel = el('settingsPanel');
  var same = panel.classList.contains('open') && panel.getAttribute('data-menu') === name;
  document.querySelectorAll('.menuPage').forEach(function (p) { p.classList.remove('active'); });
  if (same) { panel.classList.remove('open'); panel.removeAttribute('data-menu'); return; }
  el(name + 'Menu').classList.add('active');
  panel.setAttribute('data-menu', name);
  panel.classList.add('open');
}

function syncRangeNumber(rangeId, numberId, callback) {
  var range = el(rangeId), number = el(numberId);
  range.addEventListener('input', function () { number.value = range.value; callback(); });
  number.addEventListener('input', function () { range.value = number.value; callback(); });
  number.addEventListener('change', function () { range.value = number.value; callback(); });
}

/* ====== Event listeners ====== */
el('toggle').addEventListener('click', function () { el('panel').classList.toggle('open'); });
el('fullscreen').addEventListener('click', function () {
  var d = document, active = d.fullscreenElement || d.webkitFullscreenElement;
  if (active) { (d.exitFullscreen || d.webkitExitFullscreen).call(d); }
  else { var r = d.documentElement; (r.requestFullscreen || r.webkitRequestFullscreen).call(r); }
});
el('dataToggle').addEventListener('click', function () { openMenu('data'); });
el('viewToggle').addEventListener('click', function () { openMenu('view'); });
el('playbackToggle').addEventListener('click', function () { openMenu('playback'); });
el('physicsToggle').addEventListener('click', function () { openMenu('physics'); });
el('fxToggle').addEventListener('click', function () { openMenu('fx'); });
el('renderToggle').addEventListener('click', function () { openMenu('render'); });

el('fileBtn').addEventListener('click', function () { el('fileInput').click(); });
el('zipBtn').addEventListener('click', function () { el('zipInput').click(); });
el('fileInput').addEventListener('change', function (e) {
  addSelectedFiles(Array.from(e.target.files)); e.target.value = '';
});
el('zipInput').addEventListener('change', function (e) {
  if (e.target.files[0]) addZipFile(e.target.files[0]); e.target.value = '';
});
el('cameraSelect').addEventListener('change', function (e) { setCamera(e.target.value); });
el('audioSelect').addEventListener('change', function (e) { setAudio(e.target.value); });
el('modelFpsLimit').addEventListener('change', applyModelFpsLimit);
el('characterToonMode').addEventListener('change', applyCharacterToonMode);
syncRangeNumber('flatToonBrightnessRange', 'flatToonBrightness', applyCharacterToonBrightness);
el('studioSave').addEventListener('click', saveStudio);
el('studioRestore').addEventListener('click', restoreStudio);
el('projectExport').addEventListener('click', exportProject);
el('projectImport').addEventListener('click', function () { el('projectImportInput').click(); });
el('projectImportInput').addEventListener('change', function (e) { if (e.target.files[0]) importProject(e.target.files[0]); e.target.value = ''; });
el('reset').addEventListener('click', function () { clearScene(); revoke(runtimeUrls); resetDetected(); renderAll(); setStatus(''); });

el('play').addEventListener('click', togglePlay);
el('seek').addEventListener('input', function (e) { draggingSeek = true; seekToFrame(parseInt(e.target.value, 10) || 0); });
el('seek').addEventListener('change', function (e) { draggingSeek = false; seekToFrame(parseInt(e.target.value, 10) || 0); });
el('seek').addEventListener('pointerup', function (e) { draggingSeek = false; seekToFrame(parseInt(e.target.value, 10) || 0); });
el('frame').addEventListener('input', function (e) { seekToFrame(parseInt(e.target.value, 10) || 0); });
el('frame').addEventListener('change', function (e) { seekToFrame(parseInt(e.target.value, 10) || 0); });

el('floorMode').addEventListener('change', applyView);
el('physicsMode').addEventListener('change', applyPhysicsMode);
el('backgroundColor').addEventListener('input', applyBackground);
el('fpsMode').addEventListener('change', applyView);
el('selfShadowMode').addEventListener('change', applyView);
el('normalShadowMode').addEventListener('change', applyView);
el('pixelRatio').addEventListener('change', applyPixelRatio);
syncRangeNumber('ambientLightLevelRange', 'ambientLightLevel', applyLighting);
syncRangeNumber('directionalLightLevelRange', 'directionalLightLevel', applyLighting);
syncRangeNumber('dirRotXRange', 'dirRotX', applyDirRotation);
syncRangeNumber('dirRotYRange', 'dirRotY', applyDirRotation);
syncRangeNumber('dirRotZRange', 'dirRotZ', applyDirRotation);
syncRangeNumber('playbackSpeedRange', 'playbackSpeed', applyPlaybackSpeed);
syncRangeNumber('audioVolumeRange', 'audioVolume', applyAudioVolume);

el('logBtn').addEventListener('click', function () { el('logPanel').classList.toggle('open'); });
el('logCopy').addEventListener('click', function () {
  var t = document.createElement('textarea');
  t.value = logBoxEl.textContent; document.body.appendChild(t); t.select();
  document.execCommand('copy'); document.body.removeChild(t);
});
el('ikMode').addEventListener('change', applyIkMode);
el('physicsReset').addEventListener('click', resetPhysics);
el('physicsFps').addEventListener('change', applyPhysicsStep);
el('evalType').addEventListener('change', applyEvalType);
el('useDelta').addEventListener('change', applyUseDelta);
el('glowMode').addEventListener('change', applyGlow);
syncRangeNumber('glowIntensityRange', 'glowIntensity', applyGlow);
syncRangeNumber('glowBlurRange', 'glowBlur', applyGlow);
el('bloomMode').addEventListener('change', applyBloom);
syncRangeNumber('bloomWeightRange', 'bloomWeight', applyBloom);
syncRangeNumber('bloomThresholdRange', 'bloomThreshold', applyBloom);
el('dofMode').addEventListener('change', applyDof);
syncRangeNumber('dofFocusRange', 'dofFocus', applyDof);
syncRangeNumber('dofApertureRange', 'dofAperture', applyDof);
syncRangeNumber('substepsRange', 'substeps', applyPhysicsStep);
el('renderMp4').addEventListener('click', renderMp4H264);
el('gizmoMode').addEventListener('change', applyGizmoMode);
['posX', 'posY', 'posZ', 'rotX', 'rotY', 'rotZ'].forEach(function (id) {
  var n = el(id); if (n) n.addEventListener('input', applyTransformInputs);
});
el('codeBtn').addEventListener('click', function () { el('codePanel').classList.toggle('open'); });
el('codeApply').addEventListener('click', function () { appliedEffectCode = el('codeBox').value || ''; applyEffectCode(appliedEffectCode); });
el('codeClear').addEventListener('click', function () { el('codeBox').value = ''; clearEffectCode(); });

/* ====== Start ====== */
init();
setStatus('');

})();
