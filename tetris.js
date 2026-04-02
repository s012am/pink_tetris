const COLS = 10;
const ROWS = 20;
const BLOCK = 40;

const COLORS = {
  I: '#f48fb1',
  O: '#ffd6e7',
  T: '#e91e63',
  S: '#ffc1e3',
  Z: '#f06292',
  J: '#ff80ab',
  L: '#ffb3c6',
};

const PIECES = {
  I: [[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]],
  O: [[1,1],[1,1]],
  T: [[0,1,0],[1,1,1],[0,0,0]],
  S: [[0,1,1],[1,1,0],[0,0,0]],
  Z: [[1,1,0],[0,1,1],[0,0,0]],
  J: [[1,0,0],[1,1,1],[0,0,0]],
  L: [[0,0,1],[1,1,1],[0,0,0]],
};

const PIECE_NAMES = Object.keys(PIECES);
const SCORE_TABLE = { 1: 100, 2: 300, 3: 500, 4: 800 };
const CLEAR_MSG   = { 1: 'SINGLE', 2: 'DOUBLE', 3: 'TRIPLE', 4: 'TETRIS!' };

// Timing constants
const DAS_MS           = 150;   // delay before auto-shift starts
const ARR_MS           = 50;    // interval during auto-shift
const LOCK_MS          = 400;   // lock delay duration
const MAX_LOCK_RESETS  = 15;    // max resets before forced lock
const CLEAR_ANIM_MS    = 220;   // line-clear flash duration

// Canvas
const boardCanvas     = document.getElementById('board');
const ctx             = boardCanvas.getContext('2d');
const nextCanvas      = document.getElementById('next-canvas');
const nctx            = nextCanvas.getContext('2d');
const boardWrapper    = document.getElementById('board-wrapper');
const boardContainerEl= document.getElementById('board-container');

const scoreEl = document.getElementById('score');
const levelEl = document.getElementById('level');
const bestEl  = document.getElementById('best');
const overlay = document.getElementById('overlay');
const startBtn = document.getElementById('start-btn');

// ── Audio (Web Audio API) ───────────────────────────────────────────────────
let audioCtx = null;
function getAC() {
  if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  return audioCtx;
}
function beep(freq, dur, type = 'sine', vol = 0.25, delay = 0) {
  try {
    const ac  = getAC();
    const osc = ac.createOscillator();
    const g   = ac.createGain();
    osc.connect(g); g.connect(ac.destination);
    osc.frequency.value = freq;
    osc.type = type;
    const t = ac.currentTime + delay;
    g.gain.setValueAtTime(vol, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + dur);
    osc.start(t); osc.stop(t + dur + 0.01);
  } catch (_) {}
}
const sndMove   = () => beep(600, 0.04, 'square', 0.07);
const sndRotate = () => beep(720, 0.06, 'sine',   0.11);
const sndLock   = () => beep(240, 0.12, 'square', 0.16);
const sndHard   = () => { beep(180, 0.08, 'square', 0.2); beep(240, 0.08, 'square', 0.2, 0.05); };
function sndClear(n) {
  if (n === 4) {
    [523,659,784,1047,1319,1568].forEach((f,i) => beep(f, 0.18, 'sine', 0.28, i*0.055));
  } else {
    [523,659,784,1047].slice(0, n).forEach((f,i) => beep(f, 0.15, 'sine', 0.22, i*0.065));
  }
}
function sndLevelUp() {
  [392,523,659,784,1047].forEach((f,i) => beep(f, 0.18, 'sine', 0.22, i*0.07));
}
function sndGameOver() {
  [440,370,300,220,160].forEach((f,i) => beep(f, 0.28, 'sawtooth', 0.18, i*0.14));
}

// ── Game state ──────────────────────────────────────────────────────────────
let board, current, next, score, level, lines, dropInterval;
let lastTime, gameOver, animId, swapped, combo;
let best = parseInt(localStorage.getItem('tetris_best') || '0');
bestEl.textContent = best;
const overlayHi = document.getElementById('overlay-hi');
if (overlayHi) overlayHi.textContent = best;

// DAS
let dasDir = 0, dasTimeout = null, arrInterval = null;

// Lock delay
let lockTimeout = null, lockResets = 0, onGround = false;

// Line clear animation
let clearAnimating = false, clearAnimRows = [], clearAnimStart = 0;

// Popup messages
let popups = [];

let dropCounter = 0;

// ── Board helpers ───────────────────────────────────────────────────────────
function createBoard() {
  return Array.from({ length: ROWS }, () => Array(COLS).fill(null));
}

function randomPiece() {
  const name = PIECE_NAMES[Math.floor(Math.random() * PIECE_NAMES.length)];
  return {
    name,
    color: COLORS[name],
    matrix: PIECES[name].map(r => [...r]),
    x: Math.floor(COLS / 2) - Math.floor(PIECES[name][0].length / 2),
    y: 0,
  };
}

function rotate(matrix) {
  const N = matrix.length, M = matrix[0].length;
  const res = Array.from({ length: M }, () => Array(N).fill(0));
  for (let r = 0; r < N; r++)
    for (let c = 0; c < M; c++)
      res[c][N - 1 - r] = matrix[r][c];
  return res;
}

function collides(piece, dx = 0, dy = 0, mat = null) {
  const m = mat || piece.matrix;
  for (let r = 0; r < m.length; r++) {
    for (let c = 0; c < m[r].length; c++) {
      if (!m[r][c]) continue;
      const nx = piece.x + c + dx;
      const ny = piece.y + r + dy;
      if (nx < 0 || nx >= COLS || ny >= ROWS) return true;
      if (ny >= 0 && board[ny][nx]) return true;
    }
  }
  return false;
}

function lock(piece) {
  piece.matrix.forEach((row, r) => {
    row.forEach((val, c) => {
      if (!val) return;
      const y = piece.y + r;
      if (y < 0) { gameOver = true; return; }
      board[y][piece.x + c] = piece.color;
    });
  });
}

function detectFullLines() {
  const full = [];
  for (let r = 0; r < ROWS; r++)
    if (board[r].every(c => c !== null)) full.push(r);
  return full;
}

function removeLines(rows) {
  [...rows].sort((a, b) => b - a).forEach(r => {
    board.splice(r, 1);
    board.unshift(Array(COLS).fill(null));
  });
}

// ── Scoring ─────────────────────────────────────────────────────────────────
function processScore(count) {
  const prevLevel = level;
  combo++;
  const comboBonus = combo > 1 ? (combo - 1) * 50 * level : 0;
  lines += count;
  score += (SCORE_TABLE[count] || 0) * level + comboBonus;
  level = Math.floor(lines / 10) + 1;
  dropInterval = Math.max(80, 1000 - (level - 1) * 90);
  updateUI();

  const msg = CLEAR_MSG[count] || '';
  addPopup(msg, count === 4 ? '#ff1493' : '#e91e63', 34);
  if (combo > 1) addPopup(`${combo}× COMBO  +${comboBonus}`, '#f06292', 22);

  sndClear(count);
  if (level > prevLevel) {
    addPopup(`LEVEL ${level}!`, '#ad1457', 26);
    sndLevelUp();
  }
}

function updateUI() {
  scoreEl.textContent = score;
  levelEl.textContent = level;
  if (score > best) {
    best = score;
    localStorage.setItem('tetris_best', best);
    bestEl.textContent = best;
  }
}

// ── Popups ──────────────────────────────────────────────────────────────────
function addPopup(text, color, size = 28) {
  popups.push({ text, color, alpha: 1.0, y: boardCanvas.height * 0.38 - popups.length * 42, size });
}

// ── Drawing ──────────────────────────────────────────────────────────────────
function drawBlock(context, x, y, color, size = BLOCK) {
  context.fillStyle = color;
  context.fillRect(x * size + 1, y * size + 1, size - 2, size - 2);
  context.fillStyle = 'rgba(255,255,255,0.35)';
  context.fillRect(x * size + 1, y * size + 1, size - 2, 4);
  context.fillRect(x * size + 1, y * size + 1, 4, size - 2);
  context.fillStyle = 'rgba(0,0,0,0.18)';
  context.fillRect(x * size + 1, y * size + size - 5, size - 2, 4);
  context.fillRect(x * size + size - 5, y * size + 1, 4, size - 2);
}

function drawGhost() {
  let dy = 0;
  while (!collides(current, 0, dy + 1)) dy++;
  if (dy === 0) return;
  ctx.globalAlpha = 0.18;
  current.matrix.forEach((row, r) => {
    row.forEach((val, c) => {
      if (val) drawBlock(ctx, current.x + c, current.y + r + dy, current.color);
    });
  });
  ctx.globalAlpha = 1;
}

function drawScene(ts) {
  // Background
  const dark = document.body.classList.contains('dark');
  ctx.fillStyle = dark ? '#0d0d1a' : '#fff0f5';
  ctx.fillRect(0, 0, boardCanvas.width, boardCanvas.height);

  // Grid
  ctx.strokeStyle = dark ? 'rgba(255,255,255,0.04)' : 'rgba(244,143,177,0.2)';
  ctx.lineWidth = 1;
  for (let r = 0; r < ROWS; r++) {
    ctx.beginPath(); ctx.moveTo(0, r * BLOCK); ctx.lineTo(COLS * BLOCK, r * BLOCK); ctx.stroke();
  }
  for (let c = 0; c < COLS; c++) {
    ctx.beginPath(); ctx.moveTo(c * BLOCK, 0); ctx.lineTo(c * BLOCK, ROWS * BLOCK); ctx.stroke();
  }

  // Board cells (with flash for clearing rows)
  board.forEach((row, r) => {
    if (clearAnimating && clearAnimRows.includes(r)) {
      const t     = Math.min(1, (ts - clearAnimStart) / CLEAR_ANIM_MS);
      const flash = Math.sin(t * Math.PI);
      ctx.globalAlpha = 0.5 + flash * 0.5;
      row.forEach((_, c) =>
        drawBlock(ctx, c, r, `hsl(340, ${80 + flash * 20}%, ${75 + flash * 20}%)`)
      );
      ctx.globalAlpha = 1;
    } else {
      row.forEach((color, c) => { if (color) drawBlock(ctx, c, r, color); });
    }
  });

  // Active piece + ghost
  if (!clearAnimating) {
    drawGhost();
    current.matrix.forEach((row, r) => {
      row.forEach((val, c) => {
        if (val) drawBlock(ctx, current.x + c, current.y + r, current.color);
      });
    });

    // Lock delay indicator
    if (onGround && lockTimeout !== null) {
      ctx.strokeStyle = 'rgba(233,30,99,0.5)';
      ctx.lineWidth = 2;
      current.matrix.forEach((row, r) => {
        row.forEach((val, c) => {
          if (val) ctx.strokeRect(
            (current.x + c) * BLOCK + 2, (current.y + r) * BLOCK + 2, BLOCK - 4, BLOCK - 4
          );
        });
      });
      ctx.lineWidth = 1;
    }
  }

  // Next preview
  const ns = 24;
  nctx.fillStyle = dark ? '#0d0d1a' : '#fff0f5';
  nctx.fillRect(0, 0, nextCanvas.width, nextCanvas.height);
  const nm = next.matrix;
  const ox = Math.floor((nextCanvas.width  / ns - nm[0].length) / 2);
  const oy = Math.floor((nextCanvas.height / ns - nm.length)    / 2);
  nm.forEach((row, r) => {
    row.forEach((val, c) => {
      if (!val) return;
      nctx.fillStyle = next.color;
      nctx.fillRect((ox + c) * ns + 1, (oy + r) * ns + 1, ns - 2, ns - 2);
      nctx.fillStyle = 'rgba(255,255,255,0.25)';
      nctx.fillRect((ox + c) * ns + 1, (oy + r) * ns + 1, ns - 2, 3);
    });
  });

  // Popups
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  popups = popups.filter(p => p.alpha > 0.01);
  popups.forEach(p => {
    p.alpha = Math.max(0, p.alpha - 0.014);
    p.y -= 0.7;
    ctx.globalAlpha = p.alpha;
    ctx.font = `${p.size}px 'Press Start 2P', 'Galmuri11', monospace`;
    ctx.fillStyle = 'rgba(255,255,255,0.8)';
    ctx.fillText(p.text, boardCanvas.width / 2 + 1, p.y + 1);
    ctx.fillStyle = p.color;
    ctx.fillText(p.text, boardCanvas.width / 2, p.y);
  });
  ctx.globalAlpha = 1;
  ctx.textAlign = 'left';
  ctx.textBaseline = 'alphabetic';
}

// ── Piece lifecycle ──────────────────────────────────────────────────────────
function spawnNext() {
  current   = next;
  next      = randomPiece();
  swapped   = false;
  onGround  = false;
  lockResets = 0;
  clearLockTimer();
  if (collides(current)) {
    gameOver = true;
    sndGameOver();
  }
}

// ── Lock delay ───────────────────────────────────────────────────────────────
function startLockTimer() {
  clearLockTimer();
  if (lockResets >= MAX_LOCK_RESETS) { doLock(); return; }
  lockTimeout = setTimeout(doLock, LOCK_MS);
}

function clearLockTimer() {
  if (lockTimeout) { clearTimeout(lockTimeout); lockTimeout = null; }
}

function doLock() {
  lockTimeout = null;
  lock(current);
  sndLock();
  const fullRows = detectFullLines();
  if (fullRows.length) {
    clearAnimating = true;
    clearAnimRows  = fullRows;
    clearAnimStart = performance.now();
    processScore(fullRows.length);
  } else {
    combo = 0;
    if (!gameOver) spawnNext();
  }
  onGround   = false;
  lockResets = 0;
}

// ── Game loop ────────────────────────────────────────────────────────────────
function gameLoop(ts = 0) {
  const showGameOver = () => {
    drawScene(ts);
    showGameOverOverlay();
  };

  if (gameOver) { showGameOver(); return; }

  const delta = ts - lastTime;
  lastTime = ts;

  if (clearAnimating) {
    if (ts - clearAnimStart >= CLEAR_ANIM_MS) {
      removeLines(clearAnimRows);
      clearAnimating = false;
      clearAnimRows  = [];
      if (gameOver) { showGameOver(); return; }
      if (board.every(row => row.every(c => c === null))) {
        const bonus = 1000 * level;
        score += bonus;
        updateUI();
        addPopup('ALL CLEAR!', '#ff1493', 28);
        addPopup(`+${bonus}`, '#e91e63', 22);
        beep(880, 0.1, 'sine', 0.3);
        beep(1100, 0.1, 'sine', 0.3, 0.1);
        beep(1320, 0.2, 'sine', 0.3, 0.2);
      }
      spawnNext();
    }
  } else {
    dropCounter += delta;
    if (dropCounter >= dropInterval) {
      dropCounter = 0;
      if (!collides(current, 0, 1)) {
        current.y++;
        if (onGround) { onGround = false; clearLockTimer(); }
      } else {
        if (!onGround) { onGround = true; startLockTimer(); }
      }
    }
  }

  drawScene(ts);
  animId = requestAnimationFrame(gameLoop);
}

// ── DAS movement ─────────────────────────────────────────────────────────────
function moveDir(dir) {
  if (gameOver || clearAnimating) return;
  if (!collides(current, dir, 0)) {
    current.x += dir;
    sndMove();
    if (onGround) { lockResets++; startLockTimer(); }
  }
}

function startDAS(dir) {
  if (dasDir === dir) return;
  stopDAS();
  dasDir = dir;
  moveDir(dir);
  dasTimeout = setTimeout(() => {
    arrInterval = setInterval(() => moveDir(dir), ARR_MS);
  }, DAS_MS);
}

function stopDAS(dir) {
  if (dir !== undefined && dasDir !== dir) return;
  dasDir = 0;
  if (dasTimeout)  { clearTimeout(dasTimeout);   dasTimeout  = null; }
  if (arrInterval) { clearInterval(arrInterval); arrInterval = null; }
}

// ── Actions ──────────────────────────────────────────────────────────────────
function tryRotate() {
  if (clearAnimating) return;
  const rotated = rotate(current.matrix);
  const kicks   = [0, -1, 1, -2, 2];
  for (const kick of kicks) {
    if (!collides(current, kick, 0, rotated)) {
      current.matrix  = rotated;
      current.x      += kick;
      sndRotate();
      if (onGround) { lockResets++; startLockTimer(); }
      return;
    }
  }
}

function hardDrop() {
  if (clearAnimating) return;
  let dropped = 0;
  while (!collides(current, 0, 1)) { current.y++; dropped++; }
  score += dropped * 2;
  updateUI();
  sndHard();
  clearLockTimer();
  doLock();
}

function swapWithNext() {
  if (swapped || clearAnimating) return;
  const prev = current;
  current    = next;
  current.x  = prev.x;
  current.y  = prev.y;
  if (collides(current)) { current = prev; return; }
  next      = randomPiece();
  swapped   = true;
  onGround  = false;
  lockResets = 0;
  clearLockTimer();
}

// ── Keyboard ─────────────────────────────────────────────────────────────────
document.addEventListener('keydown', e => {
  if (e.code === 'KeyR') { startGame(); return; }
  if (gameOver) return;

  switch (e.code) {
    case 'ArrowLeft':  if (!e.repeat) startDAS(-1); break;
    case 'ArrowRight': if (!e.repeat) startDAS(1);  break;
    case 'ArrowDown':
      if (!clearAnimating && !collides(current, 0, 1)) {
        current.y++;
        dropCounter = 0;
      }
      break;
    case 'ArrowUp':
    case 'KeyZ':  tryRotate();    break;
    case 'Space': hardDrop();     break;
    case 'KeyC':  swapWithNext(); break;
  }
  e.preventDefault();
});

document.addEventListener('keyup', e => {
  if (e.code === 'ArrowLeft')  stopDAS(-1);
  if (e.code === 'ArrowRight') stopDAS(1);
});

// ── Touch controls ───────────────────────────────────────────────────────────
let touchStartX = 0, touchStartY = 0, touchStartTime = 0;

boardCanvas.addEventListener('touchstart', e => {
  e.preventDefault();
  touchStartX    = e.touches[0].clientX;
  touchStartY    = e.touches[0].clientY;
  touchStartTime = Date.now();
}, { passive: false });

boardCanvas.addEventListener('touchend', e => {
  e.preventDefault();
  const dx    = e.changedTouches[0].clientX - touchStartX;
  const dy    = e.changedTouches[0].clientY - touchStartY;
  const dt    = Date.now() - touchStartTime;
  const absDx = Math.abs(dx);
  const absDy = Math.abs(dy);

  if (absDx < 12 && absDy < 12 && dt < 220) {
    tryRotate();
  } else if (absDx > absDy) {
    const steps = Math.max(1, Math.floor(absDx / (BLOCK * 0.75)));
    const dir   = dx > 0 ? 1 : -1;
    for (let i = 0; i < steps; i++) moveDir(dir);
  } else {
    if (dy > 40)  hardDrop();
    else if (dy < -40) tryRotate();
  }
}, { passive: false });

// ── Game lifecycle ────────────────────────────────────────────────────────────
function startGame() {
  stopDAS();
  clearLockTimer();

  board         = createBoard();
  score         = 0;
  level         = 1;
  lines         = 0;
  combo         = 0;
  dropInterval  = 1000;
  dropCounter   = 0;
  lastTime      = 0;
  gameOver      = false;
  swapped       = false;
  onGround      = false;
  lockResets    = 0;
  clearAnimating = false;
  clearAnimRows  = [];
  popups         = [];

  next = randomPiece();
  spawnNext();
  updateUI();
  hideOverlay();

  if (animId) cancelAnimationFrame(animId);
  animId = requestAnimationFrame(gameLoop);
}

const DECO_TOP = `
  <div class="deco-blocks">
    <div class="deco-row">
      <div class="db" style="--c:#f48fb1"></div><div class="db" style="--c:#f48fb1"></div><div class="db" style="--c:#f48fb1"></div><div class="db" style="--c:#f48fb1"></div><div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#ffc1e3"></div><div class="db" style="--c:#ffc1e3"></div><div class="db" style="--c:#ff80ab"></div>
    </div>
    <div class="deco-row">
      <div class="db" style="--c:#ffd6e7"></div><div class="db" style="--c:#ffd6e7"></div><div class="db" style="--c:#f06292"></div><div class="db" style="--c:#f06292"></div><div class="db" style="--c:#f06292"></div><div class="db" style="--c:#ffb3c6"></div><div class="db" style="--c:#ffb3c6"></div><div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#f48fb1"></div>
    </div>
  </div>`;

const DECO_BTM = `
  <div class="deco-blocks">
    <div class="deco-row">
      <div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#ffd6e7"></div><div class="db" style="--c:#ffd6e7"></div><div class="db" style="--c:#f48fb1"></div><div class="db" style="--c:#f48fb1"></div><div class="db" style="--c:#f06292"></div><div class="db" style="--c:#f06292"></div><div class="db" style="--c:#ff80ab"></div><div class="db" style="--c:#ff80ab"></div><div class="db" style="--c:#ffb3c6"></div>
    </div>
    <div class="deco-row">
      <div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#e91e63"></div><div class="db" style="--c:#ffc1e3"></div><div class="db" style="--c:#ffc1e3"></div><div class="db" style="--c:#f48fb1"></div><div class="db" style="--c:#f48fb1"></div><div class="db" style="--c:#f06292"></div><div class="db" style="--c:#ffd6e7"></div><div class="db" style="--c:#ffd6e7"></div>
    </div>
  </div>`;

function showGameOverOverlay() {
  const isNew = score > 0 && score >= best;
  overlay.innerHTML = `
    ${DECO_TOP}
    <div class="overlay-body">
      <h2>GAME OVER</h2>
      ${isNew ? '<div class="go-newbest">✦ NEW BEST ✦</div>' : ''}
      <div class="go-stats">
        <div class="go-stat">
          <span class="go-stat-label">SCORE</span>
          <span class="go-stat-value">${score}</span>
        </div>
        <div class="go-stat">
          <span class="go-stat-label">BEST</span>
          <span class="go-stat-value">${best}</span>
        </div>
        <div class="go-stat">
          <span class="go-stat-label">LEVEL</span>
          <span class="go-stat-value">${level}</span>
        </div>
        <div class="go-stat">
          <span class="go-stat-label">LINES</span>
          <span class="go-stat-value">${lines}</span>
        </div>
      </div>
      <button id="start-btn">▶ RETRY</button>
    </div>
    ${DECO_BTM}
  `;
  overlay.style.display = 'flex';
  document.getElementById('start-btn').addEventListener('click', startGame);
}

function hideOverlay() {
  overlay.style.display = 'none';
}

// ── Mobile: board scaling ────────────────────────────────────────────────────
function scaleBoard() {
  if (window.innerWidth > 620) {
    boardWrapper.style.width  = '400px';
    boardWrapper.style.height = '800px';
    boardContainerEl.style.transform = '';
    boardContainerEl.style.transformOrigin = '';
    return;
  }
  // 좌우 여백 48px 확보, 세로는 뷰포트의 55% 이하로 제한
  const maxByWidth  = (window.innerWidth - 48) / 400;
  const maxByHeight = (window.innerHeight * 0.55) / 800;
  const scale = Math.min(maxByWidth, maxByHeight);
  boardWrapper.style.width  = `${Math.round(400 * scale)}px`;
  boardWrapper.style.height = `${Math.round(800 * scale)}px`;
  boardContainerEl.style.transform = `scale(${scale})`;
  boardContainerEl.style.transformOrigin = 'top left';
}
scaleBoard();
window.addEventListener('resize', scaleBoard);

// ── Mobile: touch buttons ────────────────────────────────────────────────────
function setupMobileControls() {
  function holdBtn(id, action, delay = DAS_MS) {
    const btn = document.getElementById(id);
    if (!btn) return;
    let dasT = null, arrI = null;
    const release = e => { e.preventDefault(); clearTimeout(dasT); clearInterval(arrI); };
    btn.addEventListener('touchstart', e => {
      e.preventDefault();
      action();
      dasT = setTimeout(() => { arrI = setInterval(action, ARR_MS); }, delay);
    }, { passive: false });
    btn.addEventListener('touchend',   release, { passive: false });
    btn.addEventListener('touchcancel',release, { passive: false });
  }

  function tapBtn(id, action) {
    const btn = document.getElementById(id);
    if (!btn) return;
    btn.addEventListener('touchstart', e => { e.preventDefault(); action(); }, { passive: false });
  }

  holdBtn('mc-left',  () => moveDir(-1));
  holdBtn('mc-right', () => moveDir(1));
  holdBtn('mc-soft',  () => {
    if (!clearAnimating && !collides(current, 0, 1)) { current.y++; dropCounter = 0; }
  }, 200);
  tapBtn('mc-rotate', tryRotate);
  tapBtn('mc-hard',   hardDrop);
  tapBtn('mc-swap',   swapWithNext);
}
setupMobileControls();

// Initial start
startBtn.addEventListener('click', startGame);
document.addEventListener('keydown', e => {
  if (e.code === 'Space' && overlay.style.display !== 'none') startGame();
});
