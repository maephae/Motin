import { useState, useEffect, useRef, useCallback } from "react";

// ═══════════════════════════════════════════════════════════════════════
//  MATH ENGINE
// ═══════════════════════════════════════════════════════════════════════

function gcd(a, b) { while (b) { [a, b] = [b, a % b]; } return a; }
function modPow(base, exp, mod) {
  let r = 1n, b = BigInt(base) % BigInt(mod), e = BigInt(exp), m = BigInt(mod);
  while (e > 0n) { if (e % 2n === 1n) r = (r * b) % m; e >>= 1n; b = (b * b) % m; }
  return Number(r);
}
function setsEqual(a, b) { if (a.size !== b.size) return false; for (const v of a) if (!b.has(v)) return false; return true; }
function isSubset(small, big) { for (const v of small) if (!big.has(v)) return false; return true; }
function findCoprimes(x) { return Array.from({ length: x - 1 }, (_, i) => i + 1).filter(a => gcd(a, x) === 1); }
function cyclicSG(a, x) {
  const sg = new Set(); let b = 1;
  while (true) { const v = modPow(a, b, x); sg.add(v); if (v === 1) break; b++; if (b > x + 5) break; }
  return sg;
}
function closure(seeds, x) {
  const cur = new Set([...seeds, 1]); let changed = true;
  while (changed) {
    changed = false; const add = [];
    for (const a of cur) for (const b of cur) { const p = (a * b) % x; if (!cur.has(p)) { add.push(p); changed = true; } }
    add.forEach(v => cur.add(v));
  }
  return cur;
}
function findGenerators(sg, x) {
  const sg_ = sg instanceof Set ? sg : new Set(sg);
  const elems = [...sg_].filter(e => e !== 1).sort((a, b) => a - b);
  const singles = elems.filter(a => setsEqual(cyclicSG(a, x), sg_)).map(a => [a]);
  if (singles.length) return singles;
  const pairs = [];
  for (let i = 0; i < elems.length; i++)
    for (let j = i + 1; j < elems.length; j++) {
      const a = elems[i], b = elems[j];
      if (setsEqual(closure([a, b], x), sg_) && !setsEqual(cyclicSG(a, x), sg_) && !setsEqual(cyclicSG(b, x), sg_))
        pairs.push([a, b]);
    }
  if (pairs.length) return pairs;
  const triples = [];
  for (let i = 0; i < elems.length; i++)
    for (let j = i + 1; j < elems.length; j++)
      for (let k = j + 1; k < elems.length; k++) {
        const a = elems[i], b = elems[j], c = elems[k];
        if (setsEqual(closure([a, b, c], x), sg_) && !setsEqual(closure([a, b], x), sg_) && !setsEqual(closure([a, c], x), sg_) && !setsEqual(closure([b, c], x), sg_))
          triples.push([a, b, c]);
      }
  return triples;
}

function computeLattice(x) {
  const coprimes = findCoprimes(x);
  if (!coprimes.length) return { nodes: [], edges: [], maxLevel: 0, W: 400, H: 400 };
  const fullGroup = new Set(coprimes);
  const rawSGs = [new Set([1])];
  const addSG = sg => { if (!rawSGs.some(s => setsEqual(s, sg))) rawSGs.push(sg); };
  coprimes.forEach(a => addSG(cyclicSG(a, x)));
  addSG(fullGroup);
  for (let i = 0; i < coprimes.length; i++)
    for (let j = i + 1; j < coprimes.length; j++)
      addSG(closure([coprimes[i], coprimes[j]], x));
  const covered = new Set(); rawSGs.forEach(sg => sg.forEach(v => covered.add(v)));
  if (![...fullGroup].every(v => covered.has(v)))
    for (let i = 0; i < coprimes.length; i++)
      for (let j = i + 1; j < coprimes.length; j++)
        for (let k = j + 1; k < coprimes.length; k++)
          addSG(closure([coprimes[i], coprimes[j], coprimes[k]], x));

  const sgs = rawSGs.sort((a, b) => a.size - b.size);
  const n = sgs.length;
  const contains = Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) => i !== j && sgs[i].size < sgs[j].size && isSubset(sgs[i], sgs[j])));
  const edges = [];
  for (let i = 0; i < n; i++)
    for (let j = 0; j < n; j++)
      if (contains[i][j] && !Array.from({ length: n }, (_, k) => k).some(k => k !== i && k !== j && contains[i][k] && contains[k][j]))
        edges.push([i, j]);

  const uniqueSizes = [...new Set(sgs.map(s => s.size))].sort((a, b) => a - b);
  const levelMap = Object.fromEntries(uniqueSizes.map((s, i) => [s, i]));
  const rawLevels = sgs.map(s => levelMap[s.size]);
  const maxRawLevel = Math.max(...rawLevels);
  const depthFromBottom = new Array(n).fill(-1);
  const depthFromTop = new Array(n).fill(-1);
  { const q = []; depthFromBottom[0] = 0; q.push(0);
    while (q.length) { const cur = q.shift(); for (const [a, b] of edges) if (a === cur && depthFromBottom[b] === -1) { depthFromBottom[b] = depthFromBottom[cur] + 1; q.push(b); } } }
  { const q = []; depthFromTop[n - 1] = 0; q.push(n - 1);
    while (q.length) { const cur = q.shift(); for (const [a, b] of edges) if (b === cur && depthFromTop[a] === -1) { depthFromTop[a] = depthFromTop[cur] + 1; q.push(a); } } }
  sgs.forEach((_, i) => {
    if (depthFromBottom[i] === -1) depthFromBottom[i] = rawLevels[i];
    if (depthFromTop[i] === -1) depthFromTop[i] = maxRawLevel - rawLevels[i];
  });

  const levels = depthFromBottom;
  const maxLevel = Math.max(...levels);
  const byLevel = {};
  sgs.forEach((_, i) => { const lv = levels[i]; (byLevel[lv] = byLevel[lv] || []).push(i); });
  for (const lv of Object.keys(byLevel)) byLevel[lv].sort((a, b) => sgs[a].size - sgs[b].size);

  const maxNodesInLevel = Math.max(...Object.values(byLevel).map(arr => arr.length));
  const NODE_R = 26;
  const H_SPACING = Math.max(NODE_R * 3.8, 560 / Math.max(maxNodesInLevel + 1, 2));
  const V_SPACING = Math.max(NODE_R * 3.5, 480 / Math.max(maxLevel + 1, 2));
  const padX = 60, padY = 55;
  const W = Math.max(480, padX * 2 + H_SPACING * (maxNodesInLevel + 1));
  const H = Math.max(420, padY * 2 + V_SPACING * maxLevel);

  const posX = [], posY = [];
  for (let lv = 0; lv <= maxLevel; lv++) {
    const ns = byLevel[lv] || [];
    ns.forEach((ni, idx) => {
      posX[ni] = padX + (idx + 1) * (W - 2 * padX) / (ns.length + 1);
      posY[ni] = H - padY - lv * ((H - 2 * padY) / Math.max(maxLevel, 1));
    });
  }

  const nodes = sgs.map((sg, i) => {
    const gens = findGenerators(sg, x);
    const rank = gens.length > 0 ? gens[0].length : 0;
    const shape = rank <= 1 ? "circle" : rank === 2 ? "square" : "triangle";
    const multiGen = gens.length > 1;
    const shortLabel = sg.size === 1 ? "e" : gens.length > 0 ? "⟨" + gens[0].join(",") + "⟩" : "?";
    const genStrs = gens.map(t => "⟨" + t.join(",") + "⟩");
    const genAll = genStrs.length === 0 ? "∅" : genStrs.length === 1 ? genStrs[0] : genStrs.slice(0, -1).join(", ") + " or " + genStrs[genStrs.length - 1];
    return {
      id: i, elements: [...sg].sort((a, b) => a - b), order: sg.size,
      level: levels[i], x: posX[i], y: posY[i],
      generators: gens, genAll,
      isCyclic: rank === 1, rank, shape, multiGen, shortLabel,
      label: "{" + [...sg].sort((a, b) => a - b).join(", ") + "}",
    };
  });
  return { nodes, edges, maxLevel, byLevel, W, H, nodeR: NODE_R };
}

// ═══════════════════════════════════════════════════════════════════════
//  COLOR SYSTEM — keyed by subgroup ORDER
// ═══════════════════════════════════════════════════════════════════════

const ORDER_COLS = ["#16a34a","#0284c7","#7c3aed","#db2777","#ea580c","#ca8a04","#be123c","#0891b2","#65a30d","#9333ea"];
function buildOrderColorMap(nodes) {
  const orders = [...new Set(nodes.map(n => n.order))].sort((a, b) => a - b);
  const map = {};
  orders.forEach((o, i) => { map[o] = ORDER_COLS[i % ORDER_COLS.length]; });
  return map;
}
function orderColor(order, colorMap) { return colorMap[order] ?? "#9aaa88"; }

// ═══════════════════════════════════════════════════════════════════════
//  GROUP THEORY FACTS
// ═══════════════════════════════════════════════════════════════════════

function primeFactors(n) {
  const f = {}; let d = 2;
  while (d * d <= n) { while (n % d === 0) { f[d] = (f[d] || 0) + 1; n = Math.floor(n / d); } d++; }
  if (n > 1) f[n] = (f[n] || 0) + 1;
  return f;
}
function zStructureParts(n) {
  const f = primeFactors(n); const parts = [];
  for (const [p, k] of Object.entries(f)) {
    const pi = parseInt(p), ki = parseInt(k);
    if (pi === 2) { if (ki === 1) {} else if (ki === 2) parts.push(2); else { parts.push(2); parts.push(Math.pow(2, ki - 2)); } }
    else parts.push(Math.pow(pi, ki - 1) * (pi - 1));
  }
  return parts.sort((a, b) => b - a);
}
function formatZ(parts) { if (!parts.length) return "trivial"; return parts.map(p => "ℤ" + p).join(" × "); }
function groupExponent(coprimes, x) {
  function lcm(a, b) { return a / gcd(a, b) * b; }
  function elementOrder(a) { let o = 1, cur = a; while (cur !== 1) { cur = (cur * a) % x; o++; if (o > x) break; } return o; }
  return coprimes.reduce((acc, a) => lcm(acc, elementOrder(a)), 1);
}

// ═══════════════════════════════════════════════════════════════════════
//  PALETTE
// ═══════════════════════════════════════════════════════════════════════

const C = {
  bg:           "#F4F6F4",  // canvas background
  panelBg:      "#B7D0DE",  // panel background
  panelSurface: "#CADBDC",  // slightly lighter surface
  border:       "#93b5c8",
  borderHover:  "#6a9ab5",
  ink:          "#0B151E",
  inkMid:       "#1e3d54",
  inkFaint:     "#3a6278",
  selectedBg:   "#d0e4ee",
  selectedBord: "#4a88aa",
  statsRow:     "#c2d8e4",
  gridLine:     "#DEE7DC",
  paneHeader:   "#adc8d8",
};

// ═══════════════════════════════════════════════════════════════════════
//  SHARED COMPONENTS
// ═══════════════════════════════════════════════════════════════════════

// A draggable horizontal splitter bar between sub-panes
function HPSplitter({ onDrag }) {
  const dragging = useRef(false);
  const startY = useRef(0);
  const onMouseDown = (e) => {
    e.preventDefault(); dragging.current = true; startY.current = e.clientY;
    document.body.style.cursor = "row-resize"; document.body.style.userSelect = "none";
  };
  useEffect(() => {
    const onMove = (e) => { if (!dragging.current) return; onDrag(e.clientY - startY.current); startY.current = e.clientY; };
    const onUp = () => { if (dragging.current) { dragging.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; } };
    window.addEventListener("mousemove", onMove); window.addEventListener("mouseup", onUp);
    return () => { window.removeEventListener("mousemove", onMove); window.removeEventListener("mouseup", onUp); };
  }, [onDrag]);
  return (
    <div onMouseDown={onMouseDown} style={{
      height: 6, flexShrink: 0, cursor: "row-resize", background: C.border,
      display: "flex", alignItems: "center", justifyContent: "center", gap: 6,
      transition: "background 0.15s", position: "relative",
    }}
      onMouseEnter={e => e.currentTarget.style.background = C.borderHover}
      onMouseLeave={e => e.currentTarget.style.background = C.border}>
      {[-12, -4, 4, 12].map(x => (
        <div key={x} style={{ position: "absolute", left: `calc(50% + ${x}px)`, width: 3, height: 3, borderRadius: "50%", background: C.panelBg }} />
      ))}
    </div>
  );
}

// Pane: a titled scrollable section with a collapse toggle
function Pane({ title, children, height, style }) {
  return (
    <div style={{ display: "flex", flexDirection: "column", height, overflow: "hidden", flexShrink: 0, ...style }}>
      <div style={{ padding: "8px 14px", background: C.paneHeader, borderBottom: `1px solid ${C.border}`, flexShrink: 0 }}>
        <span style={{ fontSize: 9, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase" }}>{title}</span>
      </div>
      <div className="sky-scroll" style={{ flex: 1, overflowY: "auto", padding: "12px 14px" }}>
        {children}
      </div>
    </div>
  );
}

// Vertical panel collapse/expand toggle button
function CollapseBtn({ collapsed, onToggle, side }) {
  return (
    <button onClick={onToggle} title={collapsed ? `Expand ${side} panel` : `Collapse ${side} panel`}
      style={{
        position: "absolute", top: "50%", transform: "translateY(-50%)",
        [side === "left" ? "right" : "left"]: -18,
        width: 18, height: 44, zIndex: 20,
        background: C.border, border: "none", cursor: "pointer",
        borderRadius: side === "left" ? "0 4px 4px 0" : "4px 0 0 4px",
        display: "flex", alignItems: "center", justifyContent: "center",
        color: C.ink, fontSize: 10, padding: 0,
        transition: "background 0.15s",
      }}
      onMouseEnter={e => e.currentTarget.style.background = C.borderHover}
      onMouseLeave={e => e.currentTarget.style.background = C.border}>
      {side === "left" ? (collapsed ? "›" : "‹") : (collapsed ? "‹" : "›")}
    </button>
  );
}

// Vertical VSplitter between main panels
function VSplitter({ onMouseDown }) {
  const [hovered, setHovered] = useState(false);
  return (
    <div onMouseDown={onMouseDown}
      style={{ width: 6, flexShrink: 0, background: hovered ? C.borderHover : C.border, cursor: "col-resize", position: "relative", zIndex: 10, transition: "background 0.15s" }}
      onMouseEnter={() => setHovered(true)} onMouseLeave={() => setHovered(false)}>
      {[-16, -8, 0, 8, 16].map(dy => (
        <div key={dy} style={{ position: "absolute", top: `calc(50% + ${dy}px)`, left: "50%", transform: "translate(-50%, -50%)", width: 3, height: 3, borderRadius: "50%", background: C.panelBg }} />
      ))}
    </div>
  );
}

function StatPill({ label, value, accent }) {
  return (
    <div style={{ marginBottom: 8 }}>
      <div style={{ fontSize: 9, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 2 }}>{label}</div>
      <div style={{ fontSize: 16, fontWeight: "700", color: accent || C.ink, fontFamily: "'Courier New', monospace" }}>{value}</div>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  NODE RENDERING
// ═══════════════════════════════════════════════════════════════════════

function nodeGeometry(node, R) {
  if (node.shape === "circle") return { type: "circle", r: R };
  if (node.shape === "square") return { type: "rect", s: R * 1.65 };
  return { type: "triangle", h: R * 1.95 };
}

function ShapeOccluder({ node, R }) {
  const g = nodeGeometry(node, R);
  const fill = C.bg;
  if (g.type === "circle") return <circle cx={node.x} cy={node.y} r={g.r} fill={fill} />;
  if (g.type === "rect") return <rect x={node.x - g.s / 2} y={node.y - g.s / 2} width={g.s} height={g.s} rx={3} fill={fill} />;
  const h = g.h;
  return <polygon points={`${node.x},${node.y - h * 0.68} ${node.x - h * 0.72},${node.y + h * 0.46} ${node.x + h * 0.72},${node.y + h * 0.46}`} fill={fill} />;
}

function ShapeNode({ node, colorMap, isSelected, isAdjacent, onClick, dragMode, onDragStart }) {
  const col = orderColor(node.order, colorMap);
  const R = 26;
  const g = nodeGeometry(node, R);
  const dash = node.multiGen ? "5 3" : undefined;
  const sw = isSelected ? 2.5 : isAdjacent ? 2.2 : 1.8;
  const strokeCol = isSelected ? C.ink : col;
  const fill = isSelected ? col : C.bg;
  const textCol = isSelected ? "#ffffff" : C.ink;
  const lbl = node.shortLabel.length > 10 ? node.shortLabel.slice(0, 9) + "…" : node.shortLabel;

  let shapeEl;
  if (g.type === "circle") shapeEl = <circle cx={node.x} cy={node.y} r={g.r} fill={fill} stroke={strokeCol} strokeWidth={sw} strokeDasharray={dash} />;
  else if (g.type === "rect") shapeEl = <rect x={node.x - g.s / 2} y={node.y - g.s / 2} width={g.s} height={g.s} rx={3} fill={fill} stroke={strokeCol} strokeWidth={sw} strokeDasharray={dash} />;
  else { const h = g.h; shapeEl = <polygon points={`${node.x},${node.y - h * 0.68} ${node.x - h * 0.72},${node.y + h * 0.46} ${node.x + h * 0.72},${node.y + h * 0.46}`} fill={fill} stroke={strokeCol} strokeWidth={sw} strokeDasharray={dash} />; }

  return (
    <g data-node="true"
      style={{ cursor: dragMode ? "grab" : "pointer" }}
      onMouseDown={e => { if (dragMode) { e.preventDefault(); e.stopPropagation(); onDragStart(node.id, e); } }}
      onClick={() => { if (!dragMode) onClick(); }}>
      {shapeEl}
      <text x={node.x} y={node.y + 1} textAnchor="middle" dominantBaseline="middle"
        fontSize={9.5} fill={textCol} fontFamily="'Courier New', monospace" fontWeight="600"
        style={{ pointerEvents: "none", userSelect: "none" }}>{lbl}</text>
    </g>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  MAIN APP
// ═══════════════════════════════════════════════════════════════════════

const PRESETS = [8, 10, 12, 15, 18, 20, 24, 30, 36, 40];

export default function App() {
  // ── Group / lattice state ──────────────────────────────────────────
  const [inputVal, setInputVal] = useState("18");
  const [x, setX] = useState(18);
  const [baseLattice, setBaseLattice] = useState(null);
  const [nodePositions, setNodePositions] = useState({});
  const [selected, setSelected] = useState(null);
  const [dragMode, setDragMode] = useState(false);
  const [showArrows, setShowArrows] = useState(true);
  const [error, setError] = useState("");

  // ── Panel widths (px) ──────────────────────────────────────────────
  const [leftW, setLeftW] = useState(260);
  const [rightW, setRightW] = useState(300);
  const [leftCollapsed, setLeftCollapsed] = useState(false);
  const [rightCollapsed, setRightCollapsed] = useState(false);
  const leftWBeforeCollapse = useRef(260);
  const rightWBeforeCollapse = useRef(300);

  // ── Left sub-pane heights (px for top pane; bottom fills rest) ─────
  const [leftPane1H, setLeftPane1H] = useState(200); // Graph generation
  const [leftPane2H, setLeftPane2H] = useState(180); // Morphisms
  // pane 3 (Key) fills flex remainder

  // ── Right sub-pane heights ─────────────────────────────────────────
  const [rightPane1H, setRightPane1H] = useState(260); // Group Info
  const [rightPane2H, setRightPane2H] = useState(200); // Selected
  // pane 3 (All subgroups) fills remainder

  // ── Camera ──────────────────────────────────────────────────────────
  const [camera, setCamera] = useState({ tx: 0, ty: 0, scale: 1 });
  const cameraRef = useRef({ tx: 0, ty: 0, scale: 1 });
  useEffect(() => { cameraRef.current = camera; }, [camera]);

  const panelRef = useRef(null);
  const isPanning = useRef(false);
  const panStart = useRef({ mouseX: 0, mouseY: 0, tx: 0, ty: 0 });
  const svgRef = useRef(null);
  const containerRef = useRef(null);

  // ── Vertical panel splitters ───────────────────────────────────────
  const leftSplitDragging = useRef(false);
  const rightSplitDragging = useRef(false);
  const leftSplitStart = useRef(0);
  const rightSplitStart = useRef(0);

  // ── Compute lattice ────────────────────────────────────────────────
  useEffect(() => {
    try {
      const lat = computeLattice(x);
      setBaseLattice(lat);
      setNodePositions({});
      setSelected(null);
      setError("");
      requestAnimationFrame(() => {
        if (!panelRef.current || !lat.W || !lat.H) return;
        const r = panelRef.current.getBoundingClientRect();
        const scale = Math.min(1, Math.min(r.width / (lat.W + 80), r.height / (lat.H + 80)));
        setCamera({ tx: (r.width - lat.W * scale) / 2, ty: (r.height - lat.H * scale) / 2, scale });
      });
    } catch (e) { setError(e.message); }
  }, [x]);

  const lattice = baseLattice ? {
    ...baseLattice,
    nodes: baseLattice.nodes.map(n => ({ ...n, x: nodePositions[n.id]?.x ?? n.x, y: nodePositions[n.id]?.y ?? n.y }))
  } : null;

  // ── Node dragging ──────────────────────────────────────────────────
  const nodeDragging = useRef(null);
  const onNodeDragStart = useCallback((id, e) => {
    if (!lattice) return;
    const node = lattice.nodes.find(n => n.id === id);
    if (!node) return;
    e.stopPropagation();
    nodeDragging.current = { id, startMouseX: e.clientX, startMouseY: e.clientY, startNodeX: node.x, startNodeY: node.y };
    setSelected(id);
  }, [lattice]);

  // ── Pan ────────────────────────────────────────────────────────────
  const onCanvasMouseDown = useCallback((e) => {
    if (dragMode) return;
    if (e.target.closest && e.target.closest("g[data-node]")) return;
    e.preventDefault();
    isPanning.current = true;
    panStart.current = { mouseX: e.clientX, mouseY: e.clientY, tx: cameraRef.current.tx, ty: cameraRef.current.ty };
    document.body.style.cursor = "grabbing";
    document.body.style.userSelect = "none";
  }, [dragMode]);

  // ── Global mouse handlers ──────────────────────────────────────────
  useEffect(() => {
    const onMove = (e) => {
      if (isPanning.current) {
        const { mouseX, mouseY, tx, ty } = panStart.current;
        setCamera(prev => ({ ...prev, tx: tx + (e.clientX - mouseX), ty: ty + (e.clientY - mouseY) }));
      }
      if (nodeDragging.current) {
        const { id, startMouseX, startMouseY, startNodeX, startNodeY } = nodeDragging.current;
        const dx = (e.clientX - startMouseX) / cameraRef.current.scale;
        const dy = (e.clientY - startMouseY) / cameraRef.current.scale;
        setNodePositions(prev => ({ ...prev, [id]: { x: startNodeX + dx, y: startNodeY + dy } }));
      }
      if (leftSplitDragging.current) {
        const delta = e.clientX - leftSplitStart.current;
        leftSplitStart.current = e.clientX;
        setLeftW(w => Math.max(180, Math.min(500, w + delta)));
      }
      if (rightSplitDragging.current) {
        const delta = e.clientX - rightSplitStart.current;
        rightSplitStart.current = e.clientX;
        setRightW(w => Math.max(200, Math.min(520, w - delta)));
      }
    };
    const onUp = () => {
      if (isPanning.current) { isPanning.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
      nodeDragging.current = null;
      if (leftSplitDragging.current) { leftSplitDragging.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
      if (rightSplitDragging.current) { rightSplitDragging.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
    };
    window.addEventListener("mousemove", onMove); window.addEventListener("mouseup", onUp);
    return () => { window.removeEventListener("mousemove", onMove); window.removeEventListener("mouseup", onUp); };
  }, []);

  // ── Zoom ───────────────────────────────────────────────────────────
  const onWheel = useCallback((e) => {
    e.preventDefault();
    if (!panelRef.current) return;
    const rect = panelRef.current.getBoundingClientRect();
    const mx = e.clientX - rect.left, my = e.clientY - rect.top;
    const factor = e.deltaY < 0 ? 1.1 : 1 / 1.1;
    setCamera(prev => {
      const s = Math.min(5, Math.max(0.15, prev.scale * factor));
      return { tx: mx - (mx - prev.tx) * (s / prev.scale), ty: my - (my - prev.ty) * (s / prev.scale), scale: s };
    });
  }, []);
  useEffect(() => {
    const el = panelRef.current; if (!el) return;
    el.addEventListener("wheel", onWheel, { passive: false });
    return () => el.removeEventListener("wheel", onWheel);
  }, [onWheel]);

  // ── Panel collapse helpers ─────────────────────────────────────────
  const toggleLeft = () => {
    if (leftCollapsed) { setLeftW(leftWBeforeCollapse.current); setLeftCollapsed(false); }
    else { leftWBeforeCollapse.current = leftW; setLeftW(0); setLeftCollapsed(true); }
  };
  const toggleRight = () => {
    if (rightCollapsed) { setRightW(rightWBeforeCollapse.current); setRightCollapsed(false); }
    else { rightWBeforeCollapse.current = rightW; setRightW(0); setRightCollapsed(true); }
  };

  // ── Sub-pane height splitters ──────────────────────────────────────
  const onLeftSplit12 = useCallback((delta) => {
    setLeftPane1H(h => Math.max(80, h + delta));
  }, []);
  const onLeftSplit23 = useCallback((delta) => {
    setLeftPane2H(h => Math.max(80, h + delta));
  }, []);
  const onRightSplit12 = useCallback((delta) => {
    setRightPane1H(h => Math.max(100, h + delta));
  }, []);
  const onRightSplit23 = useCallback((delta) => {
    setRightPane2H(h => Math.max(80, h + delta));
  }, []);

  // ── Derived ────────────────────────────────────────────────────────
  const submit = (val) => {
    const n = parseInt(val ?? inputVal);
    if (isNaN(n) || n < 2 || n > 200) { setError("Enter 2–200"); return; }
    setError(""); setX(n);
  };

  const maxLevel = lattice?.maxLevel ?? 0;
  const fullNode = lattice?.nodes?.[lattice.nodes.length - 1] ?? null;
  const selectedNode = (lattice && selected !== null) ? lattice.nodes[selected] : null;
  const colorMap = lattice ? buildOrderColorMap(lattice.nodes) : {};

  const hlEdgeSet = new Set();
  const adjacentNodes = new Set();
  if (selected !== null && lattice) {
    lattice.edges.forEach(([a, b], i) => {
      if (a === selected || b === selected) { hlEdgeSet.add(i); adjacentNodes.add(a); adjacentNodes.add(b); }
    });
  }

  const indexVal = (selectedNode && fullNode && fullNode.order % selectedNode.order === 0)
    ? fullNode.order / selectedNode.order : "—";

  const actualLeftW = leftCollapsed ? 0 : leftW;
  const actualRightW = rightCollapsed ? 0 : rightW;

  // ═══════════════════════════════════════════════════════════════════
  //  RENDER
  // ═══════════════════════════════════════════════════════════════════

  return (
    <div ref={containerRef} style={{
      width: "100vw", height: "100vh", display: "flex", overflow: "hidden",
      fontFamily: "'Courier New', 'Lucida Console', monospace", background: C.bg,
    }}>
      <style>{`
        .sky-scroll::-webkit-scrollbar { width: 6px; height: 6px; }
        .sky-scroll::-webkit-scrollbar-track { background: ${C.panelBg}; }
        .sky-scroll::-webkit-scrollbar-thumb { background: ${C.border}; border-radius: 3px; }
        .sky-scroll::-webkit-scrollbar-thumb:hover { background: ${C.borderHover}; }
      `}</style>

      {/* ══════════════════════════════════════════════════════════════
          LEFT PANEL
      ══════════════════════════════════════════════════════════════ */}
      <div style={{
        width: actualLeftW, flexShrink: 0, height: "100%",
        display: "flex", flexDirection: "column",
        background: C.panelBg, overflow: "hidden",
        transition: leftSplitDragging.current ? "none" : "width 0.2s ease",
        position: "relative",
        borderRight: actualLeftW > 0 ? `1px solid ${C.border}` : "none",
      }}>
        {/* Collapse button */}
        <CollapseBtn collapsed={leftCollapsed} onToggle={toggleLeft} side="left" />

        {actualLeftW > 40 && <>
          {/* Pane 1: Graph Generation */}
          <Pane title="Graph Generation" height={leftPane1H}>
            <div style={{ fontSize: 10, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 10 }}>Group</div>
            <div style={{ display: "flex", gap: 6, alignItems: "center", marginBottom: 10 }}>
              <span style={{ color: C.inkMid, fontSize: 14 }}>U(</span>
              <input value={inputVal} onChange={e => setInputVal(e.target.value)}
                onKeyDown={e => e.key === "Enter" && submit()}
                style={{ background: C.bg, border: `1.5px solid ${C.borderHover}`, borderRadius: 4, color: C.ink, fontSize: 18, width: 64, padding: "4px 6px", textAlign: "center", fontFamily: "'Courier New', monospace", outline: "none" }} />
              <span style={{ color: C.inkMid, fontSize: 14 }}>)</span>
            </div>
            {error && <div style={{ color: "#f87171", fontSize: 11, marginBottom: 8 }}>{error}</div>}
            <button onClick={() => submit()} style={{
              width: "100%", background: C.ink, border: "none", borderRadius: 4,
              color: C.panelBg, fontSize: 10, letterSpacing: 3, textTransform: "uppercase",
              padding: "8px 0", cursor: "pointer", fontFamily: "'Courier New', monospace", marginBottom: 12,
            }}>Build Lattice</button>
            <div style={{ fontSize: 10, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 8 }}>Presets</div>
            <div style={{ display: "flex", flexWrap: "wrap", gap: 4, marginBottom: 12 }}>
              {PRESETS.map(n => (
                <button key={n} onClick={() => { setInputVal(String(n)); submit(String(n)); }}
                  style={{ background: x === n ? C.ink : C.panelSurface, border: `1px solid ${x === n ? C.ink : C.border}`, borderRadius: 3, color: x === n ? C.panelBg : C.inkMid, fontSize: 10, padding: "4px 8px", cursor: "pointer", fontFamily: "'Courier New', monospace" }}>
                  {n}
                </button>
              ))}
            </div>
            {/* Display options */}
            <div style={{ fontSize: 10, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 8 }}>Options</div>
            <label style={{ display: "flex", alignItems: "center", gap: 8, fontSize: 11, color: C.inkMid, cursor: "pointer", marginBottom: 6 }}>
              <input type="checkbox" checked={showArrows} onChange={e => setShowArrows(e.target.checked)}
                style={{ accentColor: C.ink }} />
              Show direction arrows
            </label>
            <label style={{ display: "flex", alignItems: "center", gap: 8, fontSize: 11, color: C.inkMid, cursor: "pointer" }}>
              <input type="checkbox" checked={dragMode} onChange={e => setDragMode(e.target.checked)}
                style={{ accentColor: C.ink }} />
              Node drag mode
            </label>
          </Pane>

          <HPSplitter onDrag={onLeftSplit12} />

          {/* Pane 2: Morphisms */}
          <Pane title="Morphisms" height={leftPane2H}>
            {selectedNode ? (
              <>
                <div style={{ fontSize: 10, color: C.inkMid, marginBottom: 8 }}>
                  Subgroups of <strong>{selectedNode.label}</strong>:
                </div>
                {lattice?.nodes.filter(n => {
                  // n is a subgroup of selectedNode if all elements of n are in selectedNode
                  const sElems = new Set(selectedNode.elements);
                  return n.id !== selectedNode.id && n.elements.every(e => sElems.has(e));
                }).sort((a, b) => a.order - b.order).map(n => {
                  const col = orderColor(n.order, colorMap);
                  return (
                    <div key={n.id} onClick={() => setSelected(n.id)}
                      style={{ background: C.selectedBg, border: `1px solid ${C.border}`, borderRadius: 4, padding: "5px 8px", marginBottom: 4, cursor: "pointer", fontSize: 10, color: C.ink }}>
                      <span style={{ color: col, fontWeight: 700 }}>|{n.order}|</span>
                      {" "}
                      <span style={{ fontFamily: "monospace" }}>{n.label}</span>
                    </div>
                  );
                })}
                <div style={{ marginTop: 10, fontSize: 10, color: C.inkFaint, letterSpacing: 1 }}>
                  Index [G:H] = {indexVal}
                </div>
                {selectedNode.isCyclic && (
                  <div style={{ marginTop: 6, fontSize: 10, color: C.inkMid }}>
                    Cyclic — isomorphic to ℤ{selectedNode.order}
                  </div>
                )}
              </>
            ) : (
              <div style={{ fontSize: 11, color: C.inkFaint, fontStyle: "italic" }}>
                Select a node to see subgroup relationships.
              </div>
            )}
          </Pane>

          <HPSplitter onDrag={onLeftSplit23} />

          {/* Pane 3: Key — fills remaining space */}
          <Pane title="Legend & Key" style={{ flex: 1 }}>
            {/* Shape key */}
            <div style={{ fontSize: 9, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 8 }}>Shapes</div>
            {[["circle", "Single generator"], ["square", "Pair generators"], ["triangle", "Triple generators"]].map(([shape, label]) => (
              <div key={shape} style={{ display: "flex", alignItems: "center", gap: 8, marginBottom: 6, fontSize: 11, color: C.inkMid }}>
                <svg width={18} height={18}>
                  {shape === "circle" && <circle cx={9} cy={9} r={7} fill="none" stroke={C.inkMid} strokeWidth={1.5} />}
                  {shape === "square" && <rect x={2} y={2} width={14} height={14} rx={2} fill="none" stroke={C.inkMid} strokeWidth={1.5} />}
                  {shape === "triangle" && <polygon points="9,2 16,16 2,16" fill="none" stroke={C.inkMid} strokeWidth={1.5} />}
                </svg>
                {label}
              </div>
            ))}
            <div style={{ borderTop: `1px solid ${C.border}`, margin: "8px 0" }} />
            <div style={{ display: "flex", alignItems: "center", gap: 8, marginBottom: 6, fontSize: 11, color: C.inkMid }}>
              <svg width={26} height={12}><line x1={0} y1={6} x2={26} y2={6} stroke={C.inkMid} strokeWidth={2} /></svg>
              One generating set
            </div>
            <div style={{ display: "flex", alignItems: "center", gap: 8, marginBottom: 12, fontSize: 11, color: C.inkMid }}>
              <svg width={26} height={12}><line x1={0} y1={6} x2={26} y2={6} stroke={C.inkMid} strokeWidth={2} strokeDasharray="5 3" /></svg>
              Multiple generating sets
            </div>
            {/* Order color key */}
            {lattice && colorMap && <>
              <div style={{ fontSize: 9, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 8 }}>Order Colors</div>
              {[...new Set(lattice.nodes.map(n => n.order))].sort((a, b) => a - b).map(ord => {
                const col = orderColor(ord, colorMap);
                const count = lattice.nodes.filter(n => n.order === ord).length;
                return (
                  <div key={ord} style={{ display: "flex", alignItems: "center", gap: 8, marginBottom: 5 }}>
                    <div style={{ width: 9, height: 9, borderRadius: "50%", background: col, flexShrink: 0 }} />
                    <span style={{ fontSize: 11, color: C.inkMid }}>Order {ord}</span>
                    <span style={{ fontSize: 10, color: C.inkFaint, marginLeft: "auto" }}>{count}×</span>
                  </div>
                );
              })}
            </>}
            {/* Arrow direction note */}
            {showArrows && (
              <div style={{ marginTop: 12, padding: "6px 8px", background: C.selectedBg, borderRadius: 4, border: `1px solid ${C.border}` }}>
                <div style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 2, textTransform: "uppercase", marginBottom: 3 }}>Arrows</div>
                <div style={{ fontSize: 11, color: C.inkMid }}>▷ on edge = child → parent (subset relation)</div>
              </div>
            )}
          </Pane>
        </>}
      </div>

      {/* Left vertical splitter */}
      <VSplitter onMouseDown={(e) => {
        e.preventDefault(); leftSplitDragging.current = true;
        leftSplitStart.current = e.clientX;
        document.body.style.cursor = "col-resize"; document.body.style.userSelect = "none";
        if (leftCollapsed) { setLeftCollapsed(false); setLeftW(leftWBeforeCollapse.current); }
      }} />

      {/* ══════════════════════════════════════════════════════════════
          CANVAS (center)
      ══════════════════════════════════════════════════════════════ */}
      <div ref={panelRef} style={{
        flex: 1, height: "100%", position: "relative", overflow: "hidden",
        background: C.bg,
        backgroundImage: `linear-gradient(to right, ${C.gridLine} 1px, transparent 1px), linear-gradient(to bottom, ${C.gridLine} 1px, transparent 1px)`,
        backgroundSize: `${32 * camera.scale}px ${32 * camera.scale}px`,
        backgroundPosition: `${camera.tx}px ${camera.ty}px`,
        cursor: dragMode ? "default" : "grab",
      }} onMouseDown={onCanvasMouseDown}>
        {/* Title */}
        <div style={{ position: "absolute", top: 12, left: 0, right: 0, textAlign: "center", pointerEvents: "none", zIndex: 2 }}>
          <span style={{ fontSize: 10, letterSpacing: 5, color: "#8a9a7a", textTransform: "uppercase" }}>
            U({x}) — Subgroup Lattice
          </span>
        </div>

        {lattice && lattice.nodes.length > 0 ? (
          <svg ref={svgRef} style={{ position: "absolute", inset: 0, width: "100%", height: "100%", overflow: "visible" }}>
            <defs>
              {/* Arrow marker for each active edge color — we use a generic one and color via stroke */}
              <marker id="arr" markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                <path d="M0,0 L0,6 L6,3 Z" fill={C.inkMid} opacity="0.6" />
              </marker>
              {/* Per-color arrow markers for highlighted edges */}
              {lattice && Object.entries(colorMap).map(([ord, col]) => (
                <marker key={ord} id={`arr-${ord}`} markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                  <path d="M0,0 L0,6 L6,3 Z" fill={col} />
                </marker>
              ))}
            </defs>

            <g transform={`translate(${camera.tx}, ${camera.ty}) scale(${camera.scale})`}>
              {/* ── EDGES ── */}
              {lattice.edges.map(([a, b], i) => {
                const na = lattice.nodes[a], nb = lattice.nodes[b];
                const hl = hlEdgeSet.has(i);
                // na is child (smaller subgroup), nb is parent (larger subgroup)
                const col = hl ? orderColor(na.order, colorMap) : "#9aaa88";
                const sw = hl ? 2.5 : 1.4;

                // Midpoint for arrow
                const mx = (na.x + nb.x) / 2;
                const my = (na.y + nb.y) / 2;

                // Arrow marker id: colored for highlighted, grey for normal
                const markerId = hl ? `arr-${na.order}` : "arr";

                return (
                  <g key={i}>
                    <line x1={na.x} y1={na.y} x2={nb.x} y2={nb.y}
                      stroke={col} strokeWidth={sw} opacity={hl ? 1 : 0.6} strokeLinecap="round" />
                    {showArrows && (
                      // Small arrowhead at midpoint pointing toward parent (nb)
                      // We draw a short invisible line segment at midpoint just to host the marker
                      <line
                        x1={mx - (nb.x - na.x) * 0.001}
                        y1={my - (nb.y - na.y) * 0.001}
                        x2={mx + (nb.x - na.x) * 0.001}
                        y2={my + (nb.y - na.y) * 0.001}
                        stroke={col} strokeWidth={sw} strokeLinecap="round"
                        markerEnd={`url(#${markerId})`}
                        opacity={hl ? 1 : 0.5}
                      />
                    )}
                  </g>
                );
              })}

              {/* ── OCCLUDER ── */}
              {lattice.nodes.map(node => <ShapeOccluder key={`occ-${node.id}`} node={node} R={26} />)}

              {/* ── NODES ── */}
              {lattice.nodes.map(node => (
                <ShapeNode key={node.id} node={node} colorMap={colorMap}
                  isSelected={selected === node.id}
                  isAdjacent={adjacentNodes.has(node.id) && selected !== node.id}
                  onClick={() => setSelected(selected === node.id ? null : node.id)}
                  dragMode={dragMode} onDragStart={onNodeDragStart} />
              ))}
            </g>
          </svg>
        ) : (
          <div style={{ position: "absolute", inset: 0, display: "flex", alignItems: "center", justifyContent: "center" }}>
            <div style={{ color: "#8a9a7a", fontSize: 12, letterSpacing: 3 }}>COMPUTING…</div>
          </div>
        )}

        {/* Bottom controls */}
        <div style={{ position: "absolute", bottom: 14, right: 14, zIndex: 3, display: "flex", gap: 6 }}>
          {Object.keys(nodePositions).length > 0 && (
            <button onClick={() => setNodePositions({})} style={{ background: C.bg, border: `1px solid ${C.border}`, borderRadius: 5, padding: "5px 9px", cursor: "pointer", fontSize: 9, color: C.inkMid, letterSpacing: 2, textTransform: "uppercase" }}>Reset nodes</button>
          )}
          <button onClick={() => {
            if (!panelRef.current || !baseLattice) return;
            const r = panelRef.current.getBoundingClientRect();
            const s = Math.min(1, Math.min(r.width / (baseLattice.W + 80), r.height / (baseLattice.H + 80)));
            setCamera({ tx: (r.width - baseLattice.W * s) / 2, ty: (r.height - baseLattice.H * s) / 2, scale: s });
          }} style={{ background: C.bg, border: `1px solid ${C.border}`, borderRadius: 5, padding: "5px 9px", cursor: "pointer", fontSize: 9, color: C.inkMid, letterSpacing: 2, textTransform: "uppercase" }}>
            {Math.round(camera.scale * 100)}% ↺
          </button>
        </div>
      </div>

      {/* Right vertical splitter */}
      <VSplitter onMouseDown={(e) => {
        e.preventDefault(); rightSplitDragging.current = true;
        rightSplitStart.current = e.clientX;
        document.body.style.cursor = "col-resize"; document.body.style.userSelect = "none";
        if (rightCollapsed) { setRightCollapsed(false); setRightW(rightWBeforeCollapse.current); }
      }} />

      {/* ══════════════════════════════════════════════════════════════
          RIGHT PANEL
      ══════════════════════════════════════════════════════════════ */}
      <div style={{
        width: actualRightW, flexShrink: 0, height: "100%",
        display: "flex", flexDirection: "column",
        background: C.panelBg, overflow: "hidden",
        transition: rightSplitDragging.current ? "none" : "width 0.2s ease",
        position: "relative",
        borderLeft: actualRightW > 0 ? `1px solid ${C.border}` : "none",
      }}>
        <CollapseBtn collapsed={rightCollapsed} onToggle={toggleRight} side="right" />

        {actualRightW > 40 && <>
          {/* Pane 1: Group Info */}
          <Pane title="Group Info" height={rightPane1H}>
            {lattice && fullNode ? (() => {
              const coprimes = findCoprimes(x);
              const zParts = zStructureParts(x);
              const expVal = groupExponent(coprimes, x);
              const stats = [
                [`|U(${x})|`, fullNode.order], ["φ(x)", fullNode.order],
                ["Subgroups", lattice.nodes.length], ["Levels", maxLevel + 1],
                ["Hasse edges", lattice.edges.length],
                ["Rank", fullNode.generators.length > 0 ? fullNode.generators[0].length : 1],
                ["Exponent", expVal], ["Abelian", "yes"],
              ];
              return (
                <>
                  <div style={{ marginBottom: 12, padding: "6px 8px", background: C.statsRow, borderRadius: 4, border: `1px solid ${C.border}` }}>
                    <div style={{ fontSize: 9, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 3 }}>Isomorphism Type</div>
                    <div style={{ fontSize: 14, fontWeight: "700", color: C.ink, fontFamily: "'Courier New', monospace", wordBreak: "break-all" }}>
                      U({x}) ≅ {formatZ(zParts)}
                    </div>
                  </div>
                  <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "6px 10px" }}>
                    {stats.map(([k, v]) => <StatPill key={k} label={k} value={String(v)} accent={k === "Abelian" ? "#4ade80" : k === "Rank" && v > 1 ? "#c084fc" : undefined} />)}
                  </div>
                </>
              );
            })() : <div style={{ color: C.inkFaint, fontSize: 11 }}>—</div>}
          </Pane>

          <HPSplitter onDrag={onRightSplit12} />

          {/* Pane 2: Selected Subgroup */}
          <Pane title="Selected Subgroup" height={rightPane2H}>
            {selectedNode ? (() => {
              const col = orderColor(selectedNode.order, colorMap);
              return (
                <>
                  <div style={{ fontSize: 12, color: C.ink, fontFamily: "'Courier New', monospace", marginBottom: 10, wordBreak: "break-all", lineHeight: 1.5 }}>
                    {selectedNode.label}
                  </div>
                  <div style={{ display: "grid", gridTemplateColumns: "repeat(3,1fr)", gap: "5px 8px", marginBottom: 10 }}>
                    {[["Order", selectedNode.order], ["Level", selectedNode.level], ["Index", indexVal]].map(([k, v]) => (
                      <div key={k}>
                        <div style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1, textTransform: "uppercase" }}>{k}</div>
                        <div style={{ fontSize: 14, color: col, fontWeight: "700", marginTop: 1 }}>{String(v)}</div>
                      </div>
                    ))}
                  </div>
                  <div style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 2, textTransform: "uppercase", marginBottom: 5 }}>
                    {selectedNode.isCyclic ? "Cyclic" : selectedNode.shape === "square" ? "Non-cyclic — pair gens" : selectedNode.shape === "triangle" ? "Non-cyclic — triple gens" : "Trivial"}
                  </div>
                  <div style={{ fontSize: 11, color: C.inkMid, lineHeight: 1.8, wordBreak: "break-all" }}>
                    {selectedNode.genAll}
                  </div>
                </>
              );
            })() : <div style={{ fontSize: 11, color: C.inkFaint, fontStyle: "italic" }}>Click a node to inspect it.</div>}
          </Pane>

          <HPSplitter onDrag={onRightSplit23} />

          {/* Pane 3: All Subgroups — fills rest */}
          <Pane title="All Subgroups" style={{ flex: 1 }}>
            {[...(lattice?.nodes ?? [])].sort((a, b) => a.order - b.order).map(node => {
              const col = orderColor(node.order, colorMap);
              const isSel = selected === node.id;
              return (
                <div key={node.id} onClick={() => setSelected(isSel ? null : node.id)} style={{
                  background: isSel ? C.selectedBg : "transparent",
                  border: `1px solid ${isSel ? C.selectedBord : C.border}`,
                  borderRadius: 4, padding: "6px 8px", marginBottom: 4,
                  cursor: "pointer", display: "flex", alignItems: "center", gap: 8,
                  transition: "background 0.1s, border-color 0.1s",
                }}>
                  <svg width={14} height={14} style={{ flexShrink: 0 }}>
                    {node.shape === "circle" && <circle cx={7} cy={7} r={5} fill="none" stroke={col} strokeWidth={1.5} strokeDasharray={node.multiGen ? "4 2" : undefined} />}
                    {node.shape === "square" && <rect x={1.5} y={1.5} width={11} height={11} rx={1.5} fill="none" stroke={col} strokeWidth={1.5} strokeDasharray={node.multiGen ? "4 2" : undefined} />}
                    {node.shape === "triangle" && <polygon points="7,1.5 13,12.5 1,12.5" fill="none" stroke={col} strokeWidth={1.5} strokeDasharray={node.multiGen ? "4 2" : undefined} />}
                  </svg>
                  <div style={{ flex: 1, minWidth: 0 }}>
                    <div style={{ fontSize: 10, color: C.ink, fontFamily: "'Courier New', monospace", whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>{node.label}</div>
                    <div style={{ fontSize: 9, color: C.inkFaint, marginTop: 1, whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>{node.genAll}</div>
                  </div>
                  <div style={{ flexShrink: 0, textAlign: "right" }}>
                    <div style={{ fontSize: 11, color: col, fontWeight: "700" }}>|{node.order}|</div>
                    <div style={{ fontSize: 9, color: C.inkFaint, textTransform: "uppercase" }}>{node.isCyclic ? "cyc" : node.order === 1 ? "triv" : "non"}</div>
                  </div>
                </div>
              );
            })}
          </Pane>
        </>}
      </div>
    </div>
  );
}
