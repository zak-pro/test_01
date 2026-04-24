(() => {
  const TILE_SIZE = 256;
  const DRAG_THRESHOLD_PX = 6;
  const SCALE_MIN = 0.5;
  const SCALE_MAX = 2;
  const MAX_TILE_CACHE = 4500;
  const WHEEL_EXP_FACTOR = 0.0011;
  const OUT_TIER_COOLDOWN_MS = 220;
  const RANDOM_POINTS_COUNT = 7;
  const INERTIA_DECAY_PER_FRAME = 0.92;
  const INERTIA_MIN_SPEED = 0.02;
  const INERTIA_STRENGTH = 0.5;

  const mapEl = document.getElementById("map");
  const tilesBaseEl = document.getElementById("tilesBase");
  const tilesIncomingEl = document.getElementById("tilesIncoming");
  const zoomReadout = document.getElementById("zoomReadout");
  const scaleReadout = document.getElementById("scaleReadout");
  const zoomReadoutMobile = document.getElementById("zoomReadoutMobile");
  const scaleReadoutMobile = document.getElementById("scaleReadoutMobile");
  const pointsSheetBackdrop = document.getElementById("pointsSheetBackdrop");
  const zoomInBtn = document.getElementById("zoomInBtn");
  const zoomOutBtn = document.getElementById("zoomOutBtn");
  const resetBtn = document.getElementById("resetBtn");
  const pointsLayerEl = document.getElementById("pointsLayer");
  const pointsListEl = document.getElementById("pointsList");
  const cursorCoordsEl = document.getElementById("cursorCoords");
  const mainEl = document.querySelector(".main");
  const pointsPanelToggle = document.getElementById("pointsPanelToggle");
  const mobilePointsMedia = window.matchMedia("(max-width: 768px)");

  if (!mapEl || !tilesBaseEl || !tilesIncomingEl || !pointsLayerEl || !pointsListEl) {
    return;
  }

  let mapW = 0;
  let mapH = 0;
  let z = 0;
  let minZ = 0;
  let maxZ = 18;
  let center = { x: 0, y: 0 };
  let displayScale = 1;

  let tileManifest = {};
  let zTransition = false;
  let transitionToken = 0;

  const tileCache = new Map();
  let cacheTick = 0;

  let pointerDown = false;
  let panPointerId = -1;
  let panActive = false;
  let pinchActive = false;
  let pinchLastDist = 0;
  let dragStartClient = { x: 0, y: 0 };
  let dragStartCenter = { x: 0, y: 0 };
  let lastPivot = { x: 0, y: 0 };
  let lastPanSampleTs = 0;
  let inertiaVx = 0;
  let inertiaVy = 0;
  let inertiaRaf = 0;
  let inertiaLastTs = 0;

  let wheelAccum = 0;
  let wheelRaf = 0;
  let points = [];
  let selectedPointIndex = -1;

  let outTierCooldown = false;
  let outTierCooldownTimer = null;

  let cursorCoordsVisible = false;
  let lastCursorClient = null;
  const CURSOR_COORDS_OFFSET_Y = 18;

  function clearWheelQueue() {
    wheelAccum = 0;
    if (wheelRaf) {
      cancelAnimationFrame(wheelRaf);
      wheelRaf = 0;
    }
  }

  function clearOutTierCooldown() {
    outTierCooldown = false;
    if (outTierCooldownTimer) {
      clearTimeout(outTierCooldownTimer);
      outTierCooldownTimer = null;
    }
  }

  function syncMobilePointsPanelUi() {
    if (!mainEl || !pointsPanelToggle) {
      return;
    }
    const narrow = mobilePointsMedia.matches;
    if (narrow) {
      const open = mainEl.classList.contains("main--points-open");
      pointsPanelToggle.setAttribute("aria-expanded", open ? "true" : "false");
      pointsPanelToggle.textContent = open ? "Свернуть список" : "Точки на карте";
      if (pointsSheetBackdrop) {
        pointsSheetBackdrop.setAttribute("aria-hidden", open ? "false" : "true");
      }
    } else {
      mainEl.classList.remove("main--points-open");
      pointsPanelToggle.setAttribute("aria-expanded", "true");
      pointsPanelToggle.textContent = "Точки на карте";
      if (pointsSheetBackdrop) {
        pointsSheetBackdrop.setAttribute("aria-hidden", "true");
      }
    }
  }

  function worldSize(zi) {
    return TILE_SIZE * 2 ** zi;
  }

  function normalizeManifest(raw) {
    const normalized = {};
    for (const [zKey, xObj] of Object.entries(raw || {})) {
      const zi = Number(zKey);
      if (!Number.isFinite(zi) || typeof xObj !== "object" || xObj === null) {
        continue;
      }
      normalized[zi] = {};
      for (const [xKey, yRaw] of Object.entries(xObj)) {
        const xi = Number(xKey);
        if (!Number.isFinite(xi)) {
          continue;
        }
        const yArr = Array.isArray(yRaw) ? yRaw : [yRaw];
        normalized[zi][xi] = new Set(yArr.map((y) => Number(y)).filter(Number.isFinite));
      }
    }
    return normalized;
  }

  function tileExists(zi, xi, yi) {
    const zd = tileManifest[zi];
    if (!zd) {
      return false;
    }
    const ys = zd[xi];
    return !!ys && ys.has(yi);
  }

  function findZoomBounds() {
    const keys = Object.keys(tileManifest)
      .map(Number)
      .filter(Number.isFinite);
    if (keys.length === 0) {
      return { min: 0, max: 18 };
    }
    return { min: Math.min(...keys), max: Math.max(...keys) };
  }

  function pickInitialView() {
    const bounds = findZoomBounds();
    minZ = bounds.min;
    maxZ = bounds.max;
    const prefer = 12;
    z = Math.min(Math.max(prefer, minZ), maxZ);

    const zd = tileManifest[z];
    if (!zd) {
      z = Math.min(Math.max(0, minZ), maxZ);
      const w = worldSize(z);
      center = { x: w / 2, y: w / 2 };
      return;
    }

    const xs = Object.keys(zd).map(Number).filter(Number.isFinite);
    if (xs.length === 0) {
      const w = worldSize(z);
      center = { x: w / 2, y: w / 2 };
      return;
    }

    const ys = [];
    for (const xi of xs) {
      for (const yi of zd[xi]) {
        ys.push(yi);
      }
    }
    if (ys.length === 0) {
      const w = worldSize(z);
      center = { x: w / 2, y: w / 2 };
      return;
    }

    const midX = (Math.min(...xs) + Math.max(...xs)) / 2;
    const midY = (Math.min(...ys) + Math.max(...ys)) / 2;
    center = { x: (midX + 0.5) * TILE_SIZE, y: (midY + 0.5) * TILE_SIZE };
  }

  function loadManifest() {
    if (window.TILE_MANIFEST) {
      tileManifest = normalizeManifest(window.TILE_MANIFEST);
    } else {
      tileManifest = {};
      minZ = 0;
      maxZ = 0;
      z = 0;
      center = { x: TILE_SIZE / 2, y: TILE_SIZE / 2 };
    }
    pickInitialView();
    clampCenter();
  }

  function clampCenter() {
    const w = worldSize(z);
    center.x = Math.max(0, Math.min(w, center.x));
    center.y = Math.max(0, Math.min(w, center.y));
  }

  function tilePath(zi, xi, yi) {
    return `./tiles/${zi}/${xi}/${yi}.png`;
  }

  function getTileKey(zi, xi, yi) {
    return `${zi}/${xi}/${yi}`;
  }

  function mapPivotFromClient(clientX, clientY) {
    const r = mapEl.getBoundingClientRect();
    return {
      x: Math.max(0, Math.min(r.width, clientX - r.left)),
      y: Math.max(0, Math.min(r.height, clientY - r.top)),
    };
  }

  function refreshCursorCoordsOverlay() {
    if (!cursorCoordsEl) {
      return;
    }
    if (!cursorCoordsVisible || !lastCursorClient || zTransition) {
      cursorCoordsEl.classList.remove("is-visible");
      return;
    }
    const r = mapEl.getBoundingClientRect();
    const cx = lastCursorClient.x;
    const cy = lastCursorClient.y;
    if (cx < r.left || cx >= r.right || cy < r.top || cy >= r.bottom) {
      cursorCoordsEl.classList.remove("is-visible");
      return;
    }
    measure();
    if (mapW === 0 || mapH === 0) {
      return;
    }
    const px = cx - r.left;
    const py = cy - r.top;
    const w = screenToWorld(px, py, center, displayScale);
    const wMax = worldSize(z);
    const wx = Math.max(0, Math.min(wMax, w.x));
    const wy = Math.max(0, Math.min(wMax, w.y));
    cursorCoordsEl.textContent = `${Math.round(wx)}, ${Math.round(wy)}`;
    cursorCoordsEl.style.left = `${px}px`;
    cursorCoordsEl.style.top = `${py + CURSOR_COORDS_OFFSET_Y}px`;
    cursorCoordsEl.classList.add("is-visible");
  }

  function screenToWorld(px, py, c, s) {
    return {
      x: c.x + (px - mapW / 2) / s,
      y: c.y + (py - mapH / 2) / s,
    };
  }

  function adjustCenterForScaleChange(px, py, sOld, sNew, c) {
    const w = screenToWorld(px, py, c, sOld);
    return {
      x: w.x - (px - mapW / 2) / sNew,
      y: w.y - (py - mapH / 2) / sNew,
    };
  }

  function getVisibleTileRange(zi, c, s) {
    const halfW = mapW / (2 * s);
    const halfH = mapH / (2 * s);
    const left = c.x - halfW;
    const top = c.y - halfH;
    const right = c.x + halfW;
    const bottom = c.y + halfH;
    const maxT = 2 ** zi - 1;
    let minX = Math.floor(left / TILE_SIZE);
    let maxX = Math.floor(right / TILE_SIZE);
    let minY = Math.floor(top / TILE_SIZE);
    let maxY = Math.floor(bottom / TILE_SIZE);
    minX = Math.max(0, minX);
    minY = Math.max(0, minY);
    maxX = Math.min(maxT, maxX);
    maxY = Math.min(maxT, maxY);
    return { minX, maxX, minY, maxY };
  }

  function updateReadouts() {
    const zt = `z ${z}`;
    const st = `×${displayScale.toFixed(3)}`;
    if (zoomReadout) {
      zoomReadout.textContent = zt;
    }
    if (scaleReadout) {
      scaleReadout.textContent = st;
    }
    if (zoomReadoutMobile) {
      zoomReadoutMobile.textContent = zt;
    }
    if (scaleReadoutMobile) {
      scaleReadoutMobile.textContent = st;
    }
  }

  function buildListItem(idx, wx, wy) {
    const item = document.createElement("button");
    item.type = "button";
    item.className =
      idx === selectedPointIndex ? "point-item point-item--active" : "point-item";
    item.dataset.pointIndex = String(idx);
    item.innerHTML = `<strong>Точка № ${idx + 1}</strong><br>Координаты: ${Math.round(wx)}, ${Math.round(wy)}`;
    return item;
  }

  function centerOnPointIndex(idx) {
    if (zTransition || idx < 0 || idx >= points.length) {
      return;
    }
    selectedPointIndex = idx;
    const world = worldSize(z);
    const p = points[idx];
    center.x = p.nx * world;
    center.y = p.ny * world;
    clampCenter();
    measure();
    renderBase();
    if (mainEl && mobilePointsMedia.matches) {
      mainEl.classList.remove("main--points-open");
      syncMobilePointsPanelUi();
    }
  }

  function renderPoints() {
    pointsLayerEl.innerHTML = "";
    pointsListEl.innerHTML = "";
    if (points.length === 0) {
      return;
    }

    const world = worldSize(z);
    for (let i = 0; i < points.length; i += 1) {
      const point = points[i];
      const wx = point.nx * world;
      const wy = point.ny * world;
      const sx = (wx - center.x) * displayScale + mapW / 2;
      const sy = (wy - center.y) * displayScale + mapH / 2;

      if (sx >= -60 && sx <= mapW + 220 && sy >= -30 && sy <= mapH + 30) {
        const marker = document.createElement("div");
        marker.className = "map-point";
        marker.style.left = `${sx}px`;
        marker.style.top = `${sy}px`;

        const dot = document.createElement("div");
        dot.className = "map-point-dot";
        marker.appendChild(dot);

        const label = document.createElement("div");
        label.className = "map-point-label";
        label.textContent = `Точка № ${i + 1} Координаты: ${Math.round(wx)}, ${Math.round(wy)}`;
        marker.appendChild(label);
        pointsLayerEl.appendChild(marker);
      }

      pointsListEl.appendChild(buildListItem(i, wx, wy));
    }
  }

  pointsListEl.addEventListener("click", (e) => {
    const btn = e.target.closest(".point-item");
    if (!btn || !pointsListEl.contains(btn)) {
      return;
    }
    const idx = Number(btn.dataset.pointIndex);
    if (!Number.isFinite(idx)) {
      return;
    }
    centerOnPointIndex(idx);
  });

  function generateRandomPoints() {
    points = [];
    selectedPointIndex = -1;
    const zd = tileManifest[z];
    if (!zd) {
      return;
    }

    const tiles = [];
    for (const [xKey, ySet] of Object.entries(zd)) {
      const xi = Number(xKey);
      if (!Number.isFinite(xi)) {
        continue;
      }
      for (const yi of ySet) {
        tiles.push({ xi, yi });
      }
    }
    if (tiles.length === 0) {
      return;
    }

    for (let i = 0; i < RANDOM_POINTS_COUNT; i += 1) {
      const tile = tiles[Math.floor(Math.random() * tiles.length)];
      const px = (tile.xi + Math.random()) * TILE_SIZE;
      const py = (tile.yi + Math.random()) * TILE_SIZE;
      const w = worldSize(z);
      points.push({ nx: px / w, ny: py / w });
    }
  }

  function pruneCache(activeKeys) {
    if (tileCache.size <= MAX_TILE_CACHE) {
      return;
    }
    const rows = [];
    for (const [k, v] of tileCache.entries()) {
      if (activeKeys.has(k)) {
        continue;
      }
      rows.push([k, v.lastUsed]);
    }
    rows.sort((a, b) => a[1] - b[1]);
    const over = tileCache.size - MAX_TILE_CACHE;
    for (let i = 0; i < over && i < rows.length; i += 1) {
      const k = rows[i][0];
      const v = tileCache.get(k);
      if (v && v.img.parentNode) {
        v.img.parentNode.removeChild(v.img);
      }
      tileCache.delete(k);
    }
  }

  function ensureTileImg(zi, xi, yi) {
    const key = getTileKey(zi, xi, yi);
    let entry = tileCache.get(key);
    if (entry) {
      entry.lastUsed = cacheTick;
      return entry.img;
    }
    const img = new Image();
    img.draggable = false;
    img.decoding = "async";
    img.alt = "";
    img.dataset.tileKey = key;
    img.src = tilePath(zi, xi, yi);
    entry = { img, lastUsed: cacheTick };
    tileCache.set(key, entry);
    return img;
  }

  function preloadTileDecode(zi, xi, yi) {
    return new Promise((resolve) => {
      const img = new Image();
      img.src = tilePath(zi, xi, yi);
      const done = () => resolve(true);
      img.onload = () => {
        if (img.decode) {
          img.decode().then(done).catch(done);
        } else {
          done();
        }
      };
      img.onerror = () => resolve(false);
    });
  }

  function layoutTile(img, zi, xi, yi, c, s) {
    const wx = xi * TILE_SIZE;
    const wy = yi * TILE_SIZE;
    const ts = TILE_SIZE * s;
    img.style.left = `${(wx - c.x) * s + mapW / 2}px`;
    img.style.top = `${(wy - c.y) * s + mapH / 2}px`;
    img.style.width = `${ts}px`;
    img.style.height = `${ts}px`;
  }

  function renderIntoLayer(layerEl, zi, c, s) {
    cacheTick += 1;
    const hasManifest = Object.keys(tileManifest).length > 0;
    const { minX, maxX, minY, maxY } = getVisibleTileRange(zi, c, s);
    const active = new Set();

    for (let xi = minX; xi <= maxX; xi += 1) {
      for (let yi = minY; yi <= maxY; yi += 1) {
        if (hasManifest && !tileExists(zi, xi, yi)) {
          continue;
        }
        const key = getTileKey(zi, xi, yi);
        active.add(key);
        const img = ensureTileImg(zi, xi, yi);
        layoutTile(img, zi, xi, yi, c, s);
        if (img.parentNode !== layerEl) {
          layerEl.appendChild(img);
        }
      }
    }

    for (const child of [...layerEl.children]) {
      const k = child.dataset.tileKey;
      if (k && !active.has(k)) {
        layerEl.removeChild(child);
      }
    }

    pruneCache(active);
  }

  function syncTileDatasetKeys(layerEl) {
    for (const child of layerEl.children) {
      if (child.dataset.tileKey) {
        continue;
      }
      for (const [k, v] of tileCache.entries()) {
        if (v.img === child) {
          child.dataset.tileKey = k;
          break;
        }
      }
    }
  }

  function stripDetachedFromLayer(layerEl) {
    for (const child of [...layerEl.children]) {
      layerEl.removeChild(child);
    }
  }

  function computeCenterAfterDiscreteZoom(ziFrom, ziTo, c, px, py, pivotScale) {
    const ratio = 2 ** (ziTo - ziFrom);
    const wvx = c.x + (px - mapW / 2) / pivotScale;
    const wvy = c.y + (py - mapH / 2) / pivotScale;
    const wNew = worldSize(ziTo);
    const nx = wvx * ratio - (px - mapW / 2);
    const ny = wvy * ratio - (py - mapH / 2);
    return {
      x: Math.max(0, Math.min(wNew, nx)),
      y: Math.max(0, Math.min(wNew, ny)),
    };
  }

  function measure() {
    mapW = mapEl.clientWidth;
    mapH = mapEl.clientHeight;
  }

  function renderCurrentView() {
    measure();
    renderIntoLayer(tilesBaseEl, z, center, displayScale);
    syncTileDatasetKeys(tilesBaseEl);
    updateReadouts();
    renderPoints();
    refreshCursorCoordsOverlay();
  }

  function stopInertia() {
    if (inertiaRaf) {
      cancelAnimationFrame(inertiaRaf);
      inertiaRaf = 0;
    }
    inertiaLastTs = 0;
    inertiaVx = 0;
    inertiaVy = 0;
  }

  function startInertia() {
    if (zTransition) {
      return;
    }
    inertiaVx *= INERTIA_STRENGTH;
    inertiaVy *= INERTIA_STRENGTH;
    if (Math.hypot(inertiaVx, inertiaVy) < INERTIA_MIN_SPEED) {
      stopInertia();
      return;
    }
    if (inertiaRaf) {
      return;
    }

    const step = (ts) => {
      if (pointerDown || zTransition) {
        stopInertia();
        return;
      }
      if (!inertiaLastTs) {
        inertiaLastTs = ts;
      }
      const dt = Math.min(34, ts - inertiaLastTs || 16.67);
      inertiaLastTs = ts;

      const prevX = center.x;
      const prevY = center.y;
      center = {
        x: center.x + inertiaVx * dt,
        y: center.y + inertiaVy * dt,
      };
      clampCenter();

      if (center.x === prevX) {
        inertiaVx = 0;
      }
      if (center.y === prevY) {
        inertiaVy = 0;
      }

      const decay = Math.pow(INERTIA_DECAY_PER_FRAME, dt / 16.67);
      inertiaVx *= decay;
      inertiaVy *= decay;

      renderCurrentView();

      if (Math.hypot(inertiaVx, inertiaVy) < INERTIA_MIN_SPEED) {
        stopInertia();
        return;
      }
      inertiaRaf = requestAnimationFrame(step);
    };

    inertiaRaf = requestAnimationFrame(step);
  }

  function renderBase() {
    measure();
    clampCenter();
    renderIntoLayer(tilesBaseEl, z, center, displayScale);
    syncTileDatasetKeys(tilesBaseEl);
    updateReadouts();
    renderPoints();
    refreshCursorCoordsOverlay();
  }

  function beginZTransition(deltaZ, px, py, pivotScale) {
    const newZ = z + deltaZ;
    if (newZ < minZ || newZ > maxZ) {
      displayScale = Math.min(SCALE_MAX, Math.max(SCALE_MIN, displayScale));
      renderBase();
      return;
    }

    zTransition = true;
    clearWheelQueue();
    transitionToken += 1;
    const token = transitionToken;
    const zoomedOut = deltaZ < 0;

    const newCenter = computeCenterAfterDiscreteZoom(z, newZ, center, px, py, pivotScale);
    const { minX, maxX, minY, maxY } = getVisibleTileRange(newZ, newCenter, 1);
    const hasManifest = Object.keys(tileManifest).length > 0;
    const jobs = [];

    for (let xi = minX; xi <= maxX; xi += 1) {
      for (let yi = minY; yi <= maxY; yi += 1) {
        if (hasManifest && !tileExists(newZ, xi, yi)) {
          continue;
        }
        jobs.push(preloadTileDecode(newZ, xi, yi));
      }
    }

    const finish = () => {
      if (token !== transitionToken) {
        return;
      }
      measure();
      stripDetachedFromLayer(tilesIncomingEl);
      renderIntoLayer(tilesIncomingEl, newZ, newCenter, 1);
      syncTileDatasetKeys(tilesIncomingEl);
      tilesIncomingEl.classList.add("is-ready");

      requestAnimationFrame(() => {
        if (token !== transitionToken) {
          return;
        }
        stripDetachedFromLayer(tilesBaseEl);
        while (tilesIncomingEl.firstChild) {
          tilesBaseEl.appendChild(tilesIncomingEl.firstChild);
        }
        tilesIncomingEl.classList.remove("is-ready");
        z = newZ;
        center = newCenter;
        displayScale = 1;
        clampCenter();
        zTransition = false;
        renderBase();
        if (zoomedOut) {
          clearWheelQueue();
          outTierCooldown = true;
          if (outTierCooldownTimer) {
            clearTimeout(outTierCooldownTimer);
          }
          outTierCooldownTimer = setTimeout(() => {
            outTierCooldown = false;
            outTierCooldownTimer = null;
          }, OUT_TIER_COOLDOWN_MS);
        }
      });
    };

    if (jobs.length === 0) {
      finish();
      return;
    }

    Promise.all(jobs).then(() => {
      if (token !== transitionToken) {
        return;
      }
      finish();
    });
  }

  function applyZoomScaleFactor(factor, px, py) {
    if (zTransition || !Number.isFinite(factor) || factor <= 0) {
      return;
    }
    measure();
    if (mapW === 0 || mapH === 0) {
      return;
    }

    const nextScale = displayScale * factor;

    if (nextScale >= SCALE_MAX && z < maxZ) {
      const sHold = Math.min(nextScale, SCALE_MAX);
      center = adjustCenterForScaleChange(px, py, displayScale, sHold, center);
      displayScale = sHold;
      clampCenter();
      renderBase();
      beginZTransition(1, px, py, displayScale);
      return;
    }

    if (nextScale <= SCALE_MIN && z > minZ) {
      const sHold = Math.max(nextScale, SCALE_MIN);
      center = adjustCenterForScaleChange(px, py, displayScale, sHold, center);
      displayScale = sHold;
      clampCenter();
      renderBase();
      beginZTransition(-1, px, py, displayScale);
      return;
    }

    const clamped = Math.min(SCALE_MAX, Math.max(SCALE_MIN, nextScale));
    center = adjustCenterForScaleChange(px, py, displayScale, clamped, center);
    displayScale = clamped;
    clampCenter();
    renderBase();
  }

  function applyWheelDelta(deltaY, px, py) {
    if (zTransition) {
      return;
    }
    if (deltaY < 0) {
      clearOutTierCooldown();
    } else if (outTierCooldown && deltaY > 0) {
      return;
    }
    const factor = Math.exp(-deltaY * WHEEL_EXP_FACTOR);
    applyZoomScaleFactor(factor, px, py);
  }

  function flushWheel() {
    wheelRaf = 0;
    if (wheelAccum === 0) {
      return;
    }
    const d = wheelAccum;
    wheelAccum = 0;
    applyWheelDelta(d, lastPivot.x, lastPivot.y);
  }

  function scheduleWheelFlush() {
    if (wheelRaf) {
      return;
    }
    wheelRaf = requestAnimationFrame(flushWheel);
  }

  mapEl.addEventListener("pointerenter", (e) => {
    cursorCoordsVisible = true;
    lastCursorClient = { x: e.clientX, y: e.clientY };
    refreshCursorCoordsOverlay();
  });

  mapEl.addEventListener("pointerleave", () => {
    cursorCoordsVisible = false;
    lastCursorClient = null;
    refreshCursorCoordsOverlay();
  });

  mapEl.addEventListener(
    "wheel",
    (e) => {
      stopInertia();
      lastPivot = mapPivotFromClient(e.clientX, e.clientY);
      e.preventDefault();
      wheelAccum += e.deltaY;
      scheduleWheelFlush();
    },
    { passive: false }
  );

  function cancelPanForPinch() {
    if (!pointerDown) {
      return;
    }
    const capId = panPointerId;
    pointerDown = false;
    panPointerId = -1;
    panActive = false;
    lastPanSampleTs = 0;
    mapEl.classList.remove("is-dragging", "is-pan-press");
    if (capId >= 0) {
      try {
        mapEl.releasePointerCapture(capId);
      } catch {
        /* noop */
      }
    }
  }

  mapEl.addEventListener("touchstart", (e) => {
    if (e.touches.length === 1) {
      pinchActive = false;
      pinchLastDist = 0;
    }
  });

  mapEl.addEventListener(
    "touchmove",
    (e) => {
      if (e.touches.length !== 2) {
        return;
      }
      const t0 = e.touches[0];
      const t1 = e.touches[1];
      const dist = Math.hypot(t1.clientX - t0.clientX, t1.clientY - t0.clientY);
      if (dist < 4) {
        return;
      }
      e.preventDefault();
      stopInertia();
      if (!pinchActive) {
        pinchActive = true;
        pinchLastDist = dist;
        cancelPanForPinch();
        return;
      }
      const factor = dist / pinchLastDist;
      if (!Number.isFinite(factor) || factor <= 0) {
        return;
      }
      pinchLastDist = dist;
      measure();
      const r = mapEl.getBoundingClientRect();
      const mx = (t0.clientX + t1.clientX) / 2 - r.left;
      const my = (t0.clientY + t1.clientY) / 2 - r.top;
      const px = Math.max(0, Math.min(mapW, mx));
      const py = Math.max(0, Math.min(mapH, my));
      if (factor > 1) {
        clearOutTierCooldown();
      } else if (outTierCooldown && factor < 1) {
        return;
      }
      applyZoomScaleFactor(factor, px, py);
    },
    { passive: false }
  );

  mapEl.addEventListener("touchend", (e) => {
    if (e.touches.length < 2) {
      pinchActive = false;
      pinchLastDist = 0;
    }
  });

  mapEl.addEventListener("touchcancel", (e) => {
    if (e.touches.length < 2) {
      pinchActive = false;
      pinchLastDist = 0;
    }
  });

  mapEl.addEventListener("gesturestart", (e) => {
    e.preventDefault();
  });
  mapEl.addEventListener("gesturechange", (e) => {
    e.preventDefault();
  });
  mapEl.addEventListener("gestureend", (e) => {
    e.preventDefault();
  });

  mapEl.addEventListener("pointermove", (e) => {
    lastCursorClient = { x: e.clientX, y: e.clientY };
    refreshCursorCoordsOverlay();
    lastPivot = mapPivotFromClient(e.clientX, e.clientY);
    if (pinchActive) {
      return;
    }
    if (!pointerDown || e.pointerId !== panPointerId) {
      return;
    }
    const dx = e.clientX - dragStartClient.x;
    const dy = e.clientY - dragStartClient.y;
    if (!panActive) {
      if (Math.hypot(dx, dy) < DRAG_THRESHOLD_PX) {
        return;
      }
      panActive = true;
      mapEl.classList.add("is-dragging");
    }
    if (zTransition) {
      return;
    }
    const nextCenter = {
      x: dragStartCenter.x - dx / displayScale,
      y: dragStartCenter.y - dy / displayScale,
    };
    const now = performance.now();
    if (lastPanSampleTs > 0) {
      const dt = now - lastPanSampleTs;
      if (dt > 0) {
        const vx = (nextCenter.x - center.x) / dt;
        const vy = (nextCenter.y - center.y) / dt;
        inertiaVx = inertiaVx * 0.7 + vx * 0.3;
        inertiaVy = inertiaVy * 0.7 + vy * 0.3;
      }
    }
    lastPanSampleTs = now;
    center = nextCenter;
    clampCenter();
    renderCurrentView();
  });

  mapEl.addEventListener("pointerdown", (e) => {
    if (e.button !== 0) {
      return;
    }
    if (!e.isPrimary) {
      return;
    }
    pointerDown = true;
    panPointerId = e.pointerId;
    panActive = false;
    stopInertia();
    lastPanSampleTs = 0;
    dragStartClient = { x: e.clientX, y: e.clientY };
    dragStartCenter = { ...center };
    lastPivot = mapPivotFromClient(e.clientX, e.clientY);
    mapEl.setPointerCapture(e.pointerId);
    mapEl.classList.add("is-pan-press");
  });

  mapEl.addEventListener("pointerup", (e) => {
    if (e.button !== 0) {
      return;
    }
    if (e.pointerId !== panPointerId) {
      return;
    }
    const shouldStartInertia = panActive;
    pointerDown = false;
    panPointerId = -1;
    panActive = false;
    lastPanSampleTs = 0;
    mapEl.classList.remove("is-dragging", "is-pan-press");
    if (shouldStartInertia) {
      startInertia();
    }
    try {
      mapEl.releasePointerCapture(e.pointerId);
    } catch {
      /* noop */
    }
  });

  mapEl.addEventListener("pointercancel", () => {
    pointerDown = false;
    panPointerId = -1;
    panActive = false;
    lastPanSampleTs = 0;
    stopInertia();
    mapEl.classList.remove("is-dragging", "is-pan-press");
  });

  pointsPanelToggle?.addEventListener("click", () => {
    if (!mainEl || !mobilePointsMedia.matches) {
      return;
    }
    mainEl.classList.toggle("main--points-open");
    syncMobilePointsPanelUi();
  });

  pointsSheetBackdrop?.addEventListener("click", () => {
    if (mainEl?.classList.contains("main--points-open")) {
      mainEl.classList.remove("main--points-open");
      syncMobilePointsPanelUi();
    }
  });

  mobilePointsMedia.addEventListener("change", () => {
    syncMobilePointsPanelUi();
    if (!zTransition) {
      renderBase();
    }
  });

  function zoomByButton(dir) {
    if (zTransition) {
      return;
    }
    measure();
    const px = lastPivot.x;
    const py = lastPivot.y;
    const synthetic = dir > 0 ? -240 : 240;
    applyWheelDelta(synthetic, px, py);
  }

  zoomInBtn.addEventListener("click", () => zoomByButton(1));
  zoomOutBtn.addEventListener("click", () => zoomByButton(-1));

  resetBtn.addEventListener("click", () => {
    transitionToken += 1;
    stopInertia();
    clearOutTierCooldown();
    clearWheelQueue();
    zTransition = false;
    selectedPointIndex = -1;
    stripDetachedFromLayer(tilesIncomingEl);
    tilesIncomingEl.classList.remove("is-ready");
    loadManifest();
    generateRandomPoints();
    displayScale = 1;
    renderBase();
  });

  window.addEventListener("resize", () => {
    syncMobilePointsPanelUi();
    if (!zTransition) {
      renderBase();
    }
  });

  window.addEventListener("keydown", (e) => {
    if (e.key === "+" || e.key === "=") {
      zoomByButton(1);
    } else if (e.key === "-" || e.key === "_") {
      zoomByButton(-1);
    } else if (e.key === "0") {
      resetBtn.click();
    } else if (e.key === "ArrowLeft") {
      if (!zTransition) {
        center.x -= 120 / displayScale;
        clampCenter();
        renderBase();
      }
    } else if (e.key === "ArrowRight") {
      if (!zTransition) {
        center.x += 120 / displayScale;
        clampCenter();
        renderBase();
      }
    } else if (e.key === "ArrowUp") {
      if (!zTransition) {
        center.y -= 120 / displayScale;
        clampCenter();
        renderBase();
      }
    } else if (e.key === "ArrowDown") {
      if (!zTransition) {
        center.y += 120 / displayScale;
        clampCenter();
        renderBase();
      }
    }
  });

  loadManifest();
  generateRandomPoints();
  measure();
  renderBase();
  syncMobilePointsPanelUi();

  window.addEventListener("load", () => {
    syncMobilePointsPanelUi();
    renderBase();
  });
})();

