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
//  COLOR SYSTEM
// ═══════════════════════════════════════════════════════════════════════

const ORDER_COLS = ["#16a34a","#0284c7","#7c3aed","#db2777","#ea580c","#ca8a04","#be123c","#0891b2","#65a30d","#9333ea"];
// Distinct accent colors for different lattices on the canvas
const LATTICE_ACCENTS = ["#0284c7","#16a34a","#7c3aed","#ea580c","#db2777","#ca8a04"];

function buildOrderColorMap(nodes) {
  const orders = [...new Set(nodes.map(n => n.order))].sort((a, b) => a - b);
  const map = {};
  orders.forEach((o, i) => { map[o] = ORDER_COLS[i % ORDER_COLS.length]; });
  return map;
}
function orderColor(order, colorMap) { return colorMap[order] ?? "#9aaa88"; }

// ═══════════════════════════════════════════════════════════════════════
//  PALETTE
// ═══════════════════════════════════════════════════════════════════════

const C = {
  bg:           "#F4F6F4",
  panelBg:      "#B7D0DE",
  panelSurface: "#CADBDC",
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
//  SHARED UI COMPONENTS
// ═══════════════════════════════════════════════════════════════════════

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
      display: "flex", alignItems: "center", justifyContent: "center",
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
        color: C.ink, fontSize: 10, padding: 0, transition: "background 0.15s",
      }}
      onMouseEnter={e => e.currentTarget.style.background = C.borderHover}
      onMouseLeave={e => e.currentTarget.style.background = C.border}>
      {side === "left" ? (collapsed ? "›" : "‹") : (collapsed ? "‹" : "›")}
    </button>
  );
}

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

// ═══════════════════════════════════════════════════════════════════════
//  SECTION — collapsible subheader system
// ═══════════════════════════════════════════════════════════════════════

const SECTION_DEPTH_STYLES = [
  { bg: "#9fbece", bgHover: "#93b5c8", fontSize: 9,  letterSpacing: 3,   fontWeight: "700", paddingY: 7 },
  { bg: "#adc8d8", bgHover: "#a0bece", fontSize: 9,  letterSpacing: 2.5, fontWeight: "600", paddingY: 6 },
  { bg: "#b8d2e0", bgHover: "#adc8d8", fontSize: 8,  letterSpacing: 2,   fontWeight: "500", paddingY: 5 },
];

function Section({ label, badge, accent, defaultOpen = true, depth = 0, children }) {
  const [open, setOpen] = useState(defaultOpen);
  const ds = SECTION_DEPTH_STYLES[Math.min(depth, 2)];
  return (
    <div style={{ width: "100%" }}>
      <div onClick={() => setOpen(o => !o)} style={{
        display: "flex", alignItems: "center",
        padding: `${ds.paddingY}px 10px`,
        background: ds.bg,
        borderLeft: accent ? `3px solid ${accent}` : `3px solid transparent`,
        borderBottom: `1px solid ${C.border}`,
        cursor: "pointer", userSelect: "none",
        transition: "background 0.13s", gap: 7,
      }}
        onMouseEnter={e => e.currentTarget.style.background = ds.bgHover}
        onMouseLeave={e => e.currentTarget.style.background = ds.bg}>
        <span style={{
          flex: 1, fontSize: ds.fontSize, letterSpacing: ds.letterSpacing,
          textTransform: "uppercase", fontWeight: ds.fontWeight,
          color: C.inkMid, fontFamily: "'Courier New', monospace",
          minWidth: 0, overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap",
        }}>{label}</span>
        {badge !== undefined && (
          <span style={{
            fontSize: 8, color: C.inkFaint,
            background: C.panelBg, border: `1px solid ${C.border}`,
            borderRadius: 3, padding: "1px 5px",
            fontFamily: "'Courier New', monospace", letterSpacing: 0.5, flexShrink: 0,
          }}>{badge}</span>
        )}
        <span style={{
          fontSize: 8, color: C.inkFaint, flexShrink: 0,
          transition: "transform 0.18s",
          transform: open ? "rotate(180deg)" : "rotate(0deg)",
          display: "inline-block", lineHeight: 1,
        }}>▼</span>
      </div>
      <div style={{ overflow: "hidden", maxHeight: open ? 4000 : 0, transition: "max-height 0.2s ease" }}>
        {children}
      </div>
    </div>
  );
}

function SectionRow({ label, value, accent, mono = true }) {
  return (
    <div style={{ display: "flex", alignItems: "baseline", gap: 8, padding: "5px 12px", borderBottom: `1px solid ${C.border}` }}>
      <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 2, textTransform: "uppercase", flexShrink: 0, minWidth: 56 }}>{label}</span>
      <span style={{ fontSize: 12, color: accent || C.ink, fontWeight: "600", fontFamily: mono ? "'Courier New', monospace" : "inherit", wordBreak: "break-all", lineHeight: 1.4 }}>{value}</span>
    </div>
  );
}

function SectionBody({ children, noPad = false }) {
  return (
    <div style={{ padding: noPad ? 0 : "8px 12px", borderBottom: `1px solid ${C.border}` }}>
      {children}
    </div>
  );
}

// Toggle row inside a Section
function SectionToggle({ label, checked, onChange }) {
  return (
    <div style={{ display: "flex", alignItems: "center", justifyContent: "space-between", padding: "6px 12px", borderBottom: `1px solid ${C.border}` }}>
      <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 2, textTransform: "uppercase" }}>{label}</span>
      <label style={{ display: "flex", alignItems: "center", gap: 6, cursor: "pointer" }}>
        <input type="checkbox" checked={checked} onChange={e => onChange(e.target.checked)}
          style={{ accentColor: C.inkMid, cursor: "pointer" }} />
        <span style={{ fontSize: 9, color: checked ? C.inkMid : C.inkFaint, letterSpacing: 1 }}>{checked ? "ON" : "OFF"}</span>
      </label>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  SUBGROUP LIST ROW — reusable in Legend & Key
// ═══════════════════════════════════════════════════════════════════════

function SubgroupRow({ node, colorMap, isSelected, onToggle }) {
  const col = orderColor(node.order, colorMap);
  return (
    <div onClick={onToggle} style={{
      background: isSelected ? C.selectedBg : "transparent",
      border: `1px solid ${isSelected ? C.selectedBord : C.border}`,
      borderRadius: 4, padding: "5px 8px", marginBottom: 3,
      cursor: "pointer", display: "flex", alignItems: "center", gap: 7,
      transition: "background 0.1s, border-color 0.1s",
    }}>
      <svg width={13} height={13} style={{ flexShrink: 0 }}>
        {node.shape === "circle"   && <circle cx={6.5} cy={6.5} r={5} fill="none" stroke={col} strokeWidth={1.5} strokeDasharray={node.multiGen ? "4 2" : undefined} />}
        {node.shape === "square"   && <rect x={1} y={1} width={11} height={11} rx={1.5} fill="none" stroke={col} strokeWidth={1.5} strokeDasharray={node.multiGen ? "4 2" : undefined} />}
        {node.shape === "triangle" && <polygon points="6.5,1 12.5,12 0.5,12" fill="none" stroke={col} strokeWidth={1.5} strokeDasharray={node.multiGen ? "4 2" : undefined} />}
      </svg>
      <div style={{ flex: 1, minWidth: 0 }}>
        <div style={{ fontSize: 10, color: C.ink, fontFamily: "'Courier New', monospace", whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>{node.label}</div>
        <div style={{ fontSize: 8, color: C.inkFaint, marginTop: 1, whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>{node.genAll}</div>
      </div>
      <div style={{ flexShrink: 0, textAlign: "right" }}>
        <div style={{ fontSize: 11, color: col, fontWeight: "700" }}>|{node.order}|</div>
        <div style={{ fontSize: 8, color: C.inkFaint, textTransform: "uppercase" }}>{node.isCyclic ? "cyc" : node.order === 1 ? "triv" : "non"}</div>
      </div>
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

// Module-level ref for click-vs-drag detection
const didDragRef = { current: false };

function ShapeNode({ node, colorMap, isSelected, isAdjacent, onToggleSelect, onMouseDown }) {
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
    <g data-node="true" style={{ cursor: isSelected ? "grab" : "pointer" }}
      onMouseDown={e => {
        didDragRef.current = false;
        if (isSelected) { onMouseDown(node.id, e); e.stopPropagation(); }
      }}
      onClick={e => { if (!didDragRef.current) onToggleSelect(node.id); e.stopPropagation(); }}>
      {shapeEl}
      <text x={node.x} y={node.y + 1} textAnchor="middle" dominantBaseline="middle"
        fontSize={9.5} fill={textCol} fontFamily="'Courier New', monospace" fontWeight="600"
        style={{ pointerEvents: "none", userSelect: "none" }}>{lbl}</text>
    </g>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  EPICENTER — alchemical sun ☉ — draggable lattice anchor
// ═══════════════════════════════════════════════════════════════════════

function Epicenter({ x, y, accent, onMouseDown }) {
  const R = 14;
  return (
    <g data-epicenter="true" style={{ cursor: "grab" }}
      onMouseDown={e => { e.preventDefault(); e.stopPropagation(); onMouseDown(e); }}>
      {/* outer circle */}
      <circle cx={x} cy={y} r={R} fill="none" stroke={accent} strokeWidth={1.5} opacity={0.7} />
      {/* inner dot */}
      <circle cx={x} cy={y} r={3} fill={accent} opacity={0.85} />
      {/* crosshair lines */}
      <line x1={x - R - 5} y1={y} x2={x - R + 3} y2={y} stroke={accent} strokeWidth={1} opacity={0.5} />
      <line x1={x + R - 3} y1={y} x2={x + R + 5} y2={y} stroke={accent} strokeWidth={1} opacity={0.5} />
      <line x1={x} y1={y - R - 5} x2={x} y2={y - R + 3} stroke={accent} strokeWidth={1} opacity={0.5} />
      <line x1={x} y1={y + R - 3} x2={x} y2={y + R + 5} stroke={accent} strokeWidth={1} opacity={0.5} />
    </g>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  LATTICE DATA HELPERS
// ═══════════════════════════════════════════════════════════════════════

let nextLatticeId = 1;
function makeLatticeEntry(xVal, canvasW, canvasH) {
  const base = computeLattice(xVal);
  // Default epicenter = center of canvas in world coords (will be set properly after mount)
  return {
    id: nextLatticeId++,
    x: xVal,
    base,          // raw computed lattice (node positions are relative to epicenter=0,0)
    nodePositions: {},  // per-node overrides relative to epicenter
    epicenter: { x: canvasW / 2, y: canvasH / 2 },
    showArrows: true,
    showEdges: true,
    showEpicenter: true,
  };
}

// Resolve a lattice entry's nodes with overrides, positioned relative to epicenter
function resolveNodes(entry) {
  return entry.base.nodes.map(n => ({
    ...n,
    x: (entry.nodePositions[n.id]?.x ?? n.x) + entry.epicenter.x - entry.base.W / 2,
    y: (entry.nodePositions[n.id]?.y ?? n.y) + entry.epicenter.y - entry.base.H / 2,
  }));
}

// ═══════════════════════════════════════════════════════════════════════
//  MAIN APP
// ═══════════════════════════════════════════════════════════════════════

const PRESETS = [8, 10, 12, 15, 18, 20, 24, 30, 36, 40];

export default function App() {
  // ── Lattice entries ────────────────────────────────────────────────
  // Each: { id, x, base, nodePositions, epicenter, showArrows, showEdges, showEpicenter }
  const [lattices, setLattices] = useState([]);
  const [inputVal, setInputVal] = useState("18");
  const [error, setError] = useState("");

  // ── Selection — keyed by `${latticeId}:${nodeId}` ─────────────────
  const [selectedIds, setSelectedIds] = useState(new Set());

  // ── Panel widths ───────────────────────────────────────────────────
  const [leftW, setLeftW] = useState(270);
  const [rightW, setRightW] = useState(310);
  const [leftCollapsed, setLeftCollapsed] = useState(false);
  const [rightCollapsed, setRightCollapsed] = useState(false);
  const leftWBeforeCollapse = useRef(270);
  const rightWBeforeCollapse = useRef(310);

  // ── Left pane heights ──────────────────────────────────────────────
  const [leftPane1H, setLeftPane1H] = useState(210);
  const [leftPane2H, setLeftPane2H] = useState(180);

  // ── Right pane heights ─────────────────────────────────────────────
  const [rightPane1H, setRightPane1H] = useState(280);

  // ── Camera ────────────────────────────────────────────────────────
  const [camera, setCamera] = useState({ tx: 0, ty: 0, scale: 1 });
  const cameraRef = useRef({ tx: 0, ty: 0, scale: 1 });
  useEffect(() => { cameraRef.current = camera; }, [camera]);

  const panelRef = useRef(null);
  const containerRef = useRef(null);

  // ── Splitter refs ─────────────────────────────────────────────────
  const leftSplitDragging = useRef(false);
  const rightSplitDragging = useRef(false);
  const leftSplitStart = useRef(0);
  const rightSplitStart = useRef(0);
  const isPanning = useRef(false);
  const panStart = useRef({ mouseX: 0, mouseY: 0, tx: 0, ty: 0 });

  // ── Node drag ────────────────────────────────────────────────────
  const nodeDragging = useRef(null);
  // { latticeId, startMouseX, startMouseY, startPositions: {nodeId: {x,y}}, startEpicenter: {x,y} }
  const epicenterDragging = useRef(null);
  // { latticeId, startMouseX, startMouseY, startEpicenter: {x,y} }
  const mouseDownPos = useRef(null);
  const didDrag = useRef(false);

  // ── Initial lattice on mount ──────────────────────────────────────
  useEffect(() => {
    const r = panelRef.current?.getBoundingClientRect();
    const cw = r?.width ?? 800, ch = r?.height ?? 600;
    const entry = makeLatticeEntry(18, cw, ch);
    setLattices([entry]);
  }, []);

  // ── Helpers to update a single lattice entry immutably ────────────
  const updateLattice = useCallback((id, patch) => {
    setLattices(prev => prev.map(l => l.id === id ? { ...l, ...patch } : l));
  }, []);

  // ── Add lattice ───────────────────────────────────────────────────
  const addLattice = useCallback((xVal) => {
    const n = parseInt(xVal);
    if (isNaN(n) || n < 2 || n > 200) { setError("Enter 2–200"); return; }
    setError("");
    const r = panelRef.current?.getBoundingClientRect();
    const cw = r?.width ?? 800, ch = r?.height ?? 600;
    // Offset each new lattice slightly so they don't stack exactly
    const offset = lattices.length * 40;
    const entry = makeLatticeEntry(n, cw, ch);
    entry.epicenter = { x: cw / 2 + offset, y: ch / 2 + offset };
    setLattices(prev => [...prev, entry]);
  }, [lattices.length]);

  // ── Remove lattice ────────────────────────────────────────────────
  const removeLattice = useCallback((id) => {
    setLattices(prev => prev.filter(l => l.id !== id));
    setSelectedIds(prev => {
      const next = new Set(prev);
      for (const k of next) { if (k.startsWith(`${id}:`)) next.delete(k); }
      return next;
    });
  }, []);

  // ── Node drag start ───────────────────────────────────────────────
  const onNodeMouseDown = useCallback((latticeId, nodeId, e) => {
    const key = `${latticeId}:${nodeId}`;
    if (!selectedIds.has(key)) return;
    e.preventDefault(); e.stopPropagation();
    didDrag.current = false; didDragRef.current = false;
    const entry = lattices.find(l => l.id === latticeId);
    if (!entry) return;
    const nodes = resolveNodes(entry);
    // Snapshot start positions of all selected nodes in this lattice
    const startPositions = {};
    for (const k of selectedIds) {
      const [lid, nid] = k.split(":").map(Number);
      if (lid !== latticeId) continue;
      const n = nodes.find(n => n.id === nid);
      if (n) {
        // Store positions relative to epicenter
        startPositions[nid] = {
          x: (entry.nodePositions[nid]?.x ?? entry.base.nodes[nid]?.x) ?? n.x - entry.epicenter.x + entry.base.W / 2,
          y: (entry.nodePositions[nid]?.y ?? entry.base.nodes[nid]?.y) ?? n.y - entry.epicenter.y + entry.base.H / 2,
        };
      }
    }
    nodeDragging.current = { latticeId, startMouseX: e.clientX, startMouseY: e.clientY, startPositions };
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
  }, [lattices, selectedIds]);

  // ── Epicenter drag start ──────────────────────────────────────────
  const onEpicenterMouseDown = useCallback((latticeId, e) => {
    e.preventDefault(); e.stopPropagation();
    didDrag.current = false; didDragRef.current = false;
    const entry = lattices.find(l => l.id === latticeId);
    if (!entry) return;
    epicenterDragging.current = {
      latticeId,
      startMouseX: e.clientX, startMouseY: e.clientY,
      startEpicenter: { ...entry.epicenter },
    };
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
  }, [lattices]);

  // ── Canvas mousedown (pan) ────────────────────────────────────────
  const onCanvasMouseDown = useCallback((e) => {
    if (e.target.closest && (e.target.closest("g[data-node]") || e.target.closest("g[data-epicenter]"))) return;
    e.preventDefault();
    didDrag.current = false; didDragRef.current = false;
    isPanning.current = true;
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
    panStart.current = { mouseX: e.clientX, mouseY: e.clientY, tx: cameraRef.current.tx, ty: cameraRef.current.ty };
    document.body.style.cursor = "grabbing";
    document.body.style.userSelect = "none";
  }, []);

  // ── Global mouse move/up ──────────────────────────────────────────
  useEffect(() => {
    const DRAG_THRESHOLD = 4;
    const onMove = (e) => {
      if (mouseDownPos.current) {
        const dx = e.clientX - mouseDownPos.current.x, dy = e.clientY - mouseDownPos.current.y;
        if (Math.sqrt(dx * dx + dy * dy) > DRAG_THRESHOLD) { didDrag.current = true; didDragRef.current = true; }
      }
      if (isPanning.current) {
        const { mouseX, mouseY, tx, ty } = panStart.current;
        setCamera(prev => ({ ...prev, tx: tx + (e.clientX - mouseX), ty: ty + (e.clientY - mouseY) }));
      }
      if (nodeDragging.current) {
        const { latticeId, startMouseX, startMouseY, startPositions } = nodeDragging.current;
        const dx = (e.clientX - startMouseX) / cameraRef.current.scale;
        const dy = (e.clientY - startMouseY) / cameraRef.current.scale;
        setLattices(prev => prev.map(l => {
          if (l.id !== latticeId) return l;
          const next = { ...l.nodePositions };
          Object.entries(startPositions).forEach(([nid, { x, y }]) => { next[nid] = { x: x + dx, y: y + dy }; });
          return { ...l, nodePositions: next };
        }));
      }
      if (epicenterDragging.current) {
        const { latticeId, startMouseX, startMouseY, startEpicenter } = epicenterDragging.current;
        const dx = (e.clientX - startMouseX) / cameraRef.current.scale;
        const dy = (e.clientY - startMouseY) / cameraRef.current.scale;
        setLattices(prev => prev.map(l =>
          l.id !== latticeId ? l : { ...l, epicenter: { x: startEpicenter.x + dx, y: startEpicenter.y + dy } }
        ));
      }
      if (leftSplitDragging.current) {
        const delta = e.clientX - leftSplitStart.current; leftSplitStart.current = e.clientX;
        setLeftW(w => Math.max(180, Math.min(500, w + delta)));
      }
      if (rightSplitDragging.current) {
        const delta = e.clientX - rightSplitStart.current; rightSplitStart.current = e.clientX;
        setRightW(w => Math.max(200, Math.min(520, w - delta)));
      }
    };
    const onUp = () => {
      if (isPanning.current && !didDrag.current) setSelectedIds(new Set());
      if (isPanning.current) { isPanning.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
      nodeDragging.current = null; epicenterDragging.current = null; mouseDownPos.current = null;
      if (leftSplitDragging.current) { leftSplitDragging.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
      if (rightSplitDragging.current) { rightSplitDragging.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
    };
    window.addEventListener("mousemove", onMove); window.addEventListener("mouseup", onUp);
    return () => { window.removeEventListener("mousemove", onMove); window.removeEventListener("mouseup", onUp); };
  }, []);

  // ── Zoom ──────────────────────────────────────────────────────────
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

  // ── Panel collapse ────────────────────────────────────────────────
  const toggleLeft = () => {
    if (leftCollapsed) { setLeftW(leftWBeforeCollapse.current); setLeftCollapsed(false); }
    else { leftWBeforeCollapse.current = leftW; setLeftW(0); setLeftCollapsed(true); }
  };
  const toggleRight = () => {
    if (rightCollapsed) { setRightW(rightWBeforeCollapse.current); setRightCollapsed(false); }
    else { rightWBeforeCollapse.current = rightW; setRightW(0); setRightCollapsed(true); }
  };

  const onLeftSplit12 = useCallback((delta) => setLeftPane1H(h => Math.max(80, h + delta)), []);
  const onLeftSplit23 = useCallback((delta) => setLeftPane2H(h => Math.max(80, h + delta)), []);
  const onRightSplit12 = useCallback((delta) => setRightPane1H(h => Math.max(100, h + delta)), []);

  // ── Toggle node selection ─────────────────────────────────────────
  const toggleNodeSelect = useCallback((latticeId, nodeId) => {
    const key = `${latticeId}:${nodeId}`;
    setSelectedIds(prev => { const next = new Set(prev); next.has(key) ? next.delete(key) : next.add(key); return next; });
  }, []);

  // ── Derived per-lattice data ──────────────────────────────────────
  const latticeViews = lattices.map((entry, idx) => {
    const nodes = resolveNodes(entry);
    const colorMap = buildOrderColorMap(nodes);
    const fullNode = nodes[nodes.length - 1] ?? null;
    const accent = LATTICE_ACCENTS[idx % LATTICE_ACCENTS.length];

    // Edge + adjacent highlight for this lattice
    const hlEdgeSet = new Set();
    const adjacentNodes = new Set();
    entry.base.edges.forEach(([a, b], i) => {
      const ka = `${entry.id}:${a}`, kb = `${entry.id}:${b}`;
      if (selectedIds.has(ka) || selectedIds.has(kb)) { hlEdgeSet.add(i); adjacentNodes.add(a); adjacentNodes.add(b); }
    });

    const coprimes = findCoprimes(entry.x);
    const zParts = zStructureParts(entry.x);
    const expVal = groupExponent(coprimes, entry.x);

    return { entry, nodes, colorMap, fullNode, accent, hlEdgeSet, adjacentNodes, coprimes, zParts, expVal };
  });

  // All selected nodes across all lattices (for right panel pane 2)
  const allSelectedNodes = latticeViews.flatMap(({ entry, nodes, colorMap, fullNode }) =>
    [...selectedIds]
      .filter(k => k.startsWith(`${entry.id}:`))
      .map(k => {
        const nodeId = parseInt(k.split(":")[1]);
        const node = nodes.find(n => n.id === nodeId);
        if (!node) return null;
        const indexVal = (fullNode && fullNode.order % node.order === 0) ? fullNode.order / node.order : "—";
        return { node, colorMap, latticeId: entry.id, latticeX: entry.x, indexVal };
      })
      .filter(Boolean)
  );

  // Primary node for Morphisms pane (last selected overall)
  const primarySel = allSelectedNodes[allSelectedNodes.length - 1] ?? null;

  const actualLeftW = leftCollapsed ? 0 : leftW;
  const actualRightW = rightCollapsed ? 0 : rightW;

  // ═════════════════════════════════════════════════════════════════
  //  RENDER
  // ═════════════════════════════════════════════════════════════════

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

      {/* ══════════════════════════════════════════════════════
          LEFT PANEL
      ══════════════════════════════════════════════════════ */}
      <div style={{
        width: actualLeftW, flexShrink: 0, height: "100%",
        display: "flex", flexDirection: "column",
        background: C.panelBg, overflow: "hidden",
        transition: leftSplitDragging.current ? "none" : "width 0.2s ease",
        position: "relative",
        borderRight: actualLeftW > 0 ? `1px solid ${C.border}` : "none",
      }}>
        <CollapseBtn collapsed={leftCollapsed} onToggle={toggleLeft} side="left" />

        {actualLeftW > 40 && <>
          {/* Pane 1: Graph Generation */}
          <Pane title="Graph Generation" height={leftPane1H}>
            <div style={{ fontSize: 10, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 8 }}>Add Lattice</div>
            <div style={{ display: "flex", gap: 6, alignItems: "center", marginBottom: 8 }}>
              <span style={{ color: C.inkMid, fontSize: 14 }}>U(</span>
              <input value={inputVal} onChange={e => setInputVal(e.target.value)}
                onKeyDown={e => e.key === "Enter" && addLattice(inputVal)}
                style={{ background: C.bg, border: `1.5px solid ${C.borderHover}`, borderRadius: 4, color: C.ink, fontSize: 18, width: 64, padding: "4px 6px", textAlign: "center", fontFamily: "'Courier New', monospace", outline: "none" }} />
              <span style={{ color: C.inkMid, fontSize: 14 }}>)</span>
            </div>
            {error && <div style={{ color: "#f87171", fontSize: 10, marginBottom: 6 }}>{error}</div>}
            <button onClick={() => addLattice(inputVal)} style={{
              width: "100%", background: C.ink, border: "none", borderRadius: 4,
              color: C.panelBg, fontSize: 10, letterSpacing: 3, textTransform: "uppercase",
              padding: "7px 0", cursor: "pointer", fontFamily: "'Courier New', monospace", marginBottom: 10,
            }}>Add Lattice</button>

            <div style={{ fontSize: 10, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 6 }}>Presets</div>
            <div style={{ display: "flex", flexWrap: "wrap", gap: 4, marginBottom: 10 }}>
              {PRESETS.map(n => (
                <button key={n} onClick={() => { setInputVal(String(n)); addLattice(String(n)); }}
                  style={{ background: C.panelSurface, border: `1px solid ${C.border}`, borderRadius: 3, color: C.inkMid, fontSize: 10, padding: "3px 7px", cursor: "pointer", fontFamily: "'Courier New', monospace" }}>
                  {n}
                </button>
              ))}
            </div>

            {/* Active lattices list */}
            {lattices.length > 0 && <>
              <div style={{ fontSize: 10, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", marginBottom: 6 }}>Active</div>
              {lattices.map((l, idx) => {
                const accent = LATTICE_ACCENTS[idx % LATTICE_ACCENTS.length];
                return (
                  <div key={l.id} style={{
                    display: "flex", alignItems: "center", gap: 6, marginBottom: 4,
                    padding: "5px 8px", borderRadius: 4, background: C.panelSurface,
                    border: `1px solid ${C.border}`, borderLeft: `3px solid ${accent}`,
                  }}>
                    <span style={{ fontSize: 11, color: C.ink, fontFamily: "'Courier New', monospace", flex: 1 }}>U({l.x})</span>
                    <span style={{ fontSize: 9, color: C.inkFaint }}>{l.base.nodes.length} subgroups</span>
                    <button onClick={() => removeLattice(l.id)} style={{
                      background: "none", border: "none", cursor: "pointer", color: C.inkFaint,
                      fontSize: 12, padding: "0 2px", lineHeight: 1,
                    }} title="Remove">×</button>
                  </div>
                );
              })}
            </>}

            <div style={{ fontSize: 10, color: C.inkFaint, marginTop: 6, lineHeight: 1.6 }}>
              Click nodes to select · drag selected to move
            </div>
          </Pane>

          <HPSplitter onDrag={onLeftSplit12} />

          {/* Pane 2: Morphisms */}
          <Pane title="Morphisms" height={leftPane2H}>
            {primarySel ? (() => {
              const { node, colorMap, latticeX, indexVal } = primarySel;
              const lv = latticeViews.find(lv => lv.entry.id === primarySel.latticeId);
              if (!lv) return null;
              return (
                <>
                  <div style={{ fontSize: 10, color: C.inkMid, marginBottom: 8 }}>
                    Subgroups of <strong style={{ fontFamily: "'Courier New', monospace" }}>{node.label}</strong>
                    <span style={{ color: C.inkFaint, fontSize: 9 }}> in U({latticeX})</span>
                  </div>
                  {lv.nodes.filter(n => {
                    const sElems = new Set(node.elements);
                    return n.id !== node.id && n.elements.every(e => sElems.has(e));
                  }).sort((a, b) => a.order - b.order).map(n => {
                    const col = orderColor(n.order, colorMap);
                    const key = `${lv.entry.id}:${n.id}`;
                    return (
                      <div key={n.id}
                        onClick={() => setSelectedIds(prev => { const next = new Set(prev); next.has(key) ? next.delete(key) : next.add(key); return next; })}
                        style={{ background: selectedIds.has(key) ? C.selectedBg : C.panelSurface, border: `1px solid ${selectedIds.has(key) ? C.selectedBord : C.border}`, borderRadius: 4, padding: "4px 8px", marginBottom: 3, cursor: "pointer", fontSize: 10, color: C.ink }}>
                        <span style={{ color: col, fontWeight: 700 }}>|{n.order}|</span>{" "}
                        <span style={{ fontFamily: "monospace" }}>{n.label}</span>
                      </div>
                    );
                  })}
                  <div style={{ marginTop: 8, fontSize: 10, color: C.inkFaint }}>Index [G:H] = {indexVal}</div>
                  {node.isCyclic && <div style={{ marginTop: 4, fontSize: 10, color: C.inkMid }}>Cyclic ≅ ℤ{node.order}</div>}
                </>
              );
            })() : (
              <div style={{ fontSize: 11, color: C.inkFaint, fontStyle: "italic" }}>Select a node to see subgroup relationships.</div>
            )}
          </Pane>

          <HPSplitter onDrag={onLeftSplit23} />

          {/* Pane 3: Legend & Key — fills rest */}
          <Pane title="Legend & Key" style={{ flex: 1 }}>
            <div style={{ margin: "-12px -14px" }}>
              {/* Shape legend */}
              <Section label="Shapes & Lines" depth={0} defaultOpen={false}>
                <SectionBody>
                  {[["circle", "Single generator"], ["square", "Pair generators"], ["triangle", "Triple generators"]].map(([shape, label]) => (
                    <div key={shape} style={{ display: "flex", alignItems: "center", gap: 8, marginBottom: 6, fontSize: 11, color: C.inkMid }}>
                      <svg width={18} height={18}>
                        {shape === "circle"   && <circle cx={9} cy={9} r={7} fill="none" stroke={C.inkMid} strokeWidth={1.5} />}
                        {shape === "square"   && <rect x={2} y={2} width={14} height={14} rx={2} fill="none" stroke={C.inkMid} strokeWidth={1.5} />}
                        {shape === "triangle" && <polygon points="9,2 16,16 2,16" fill="none" stroke={C.inkMid} strokeWidth={1.5} />}
                      </svg>
                      {label}
                    </div>
                  ))}
                  <div style={{ borderTop: `1px solid ${C.border}`, margin: "6px 0" }} />
                  <div style={{ display: "flex", alignItems: "center", gap: 8, marginBottom: 5, fontSize: 11, color: C.inkMid }}>
                    <svg width={26} height={12}><line x1={0} y1={6} x2={26} y2={6} stroke={C.inkMid} strokeWidth={2} /></svg>
                    One generating set
                  </div>
                  <div style={{ display: "flex", alignItems: "center", gap: 8, fontSize: 11, color: C.inkMid }}>
                    <svg width={26} height={12}><line x1={0} y1={6} x2={26} y2={6} stroke={C.inkMid} strokeWidth={2} strokeDasharray="5 3" /></svg>
                    Multiple generating sets
                  </div>
                </SectionBody>
              </Section>

              {/* Per-lattice subgroup lists */}
              {latticeViews.map(({ entry, nodes, colorMap, accent }) => (
                <Section key={entry.id} label={`U(${entry.x}) — Subgroups`} depth={0} accent={accent} defaultOpen={false} badge={nodes.length}>
                  <SectionBody noPad>
                    <div style={{ padding: "6px 8px" }}>
                      {[...nodes].sort((a, b) => a.order - b.order).map(node => {
                        const key = `${entry.id}:${node.id}`;
                        return (
                          <SubgroupRow key={node.id} node={node} colorMap={colorMap}
                            isSelected={selectedIds.has(key)}
                            onToggle={() => setSelectedIds(prev => { const next = new Set(prev); next.has(key) ? next.delete(key) : next.add(key); return next; })} />
                        );
                      })}
                    </div>
                  </SectionBody>
                </Section>
              ))}
            </div>
          </Pane>
        </>}
      </div>

      {/* Left splitter */}
      <VSplitter onMouseDown={(e) => {
        e.preventDefault(); leftSplitDragging.current = true; leftSplitStart.current = e.clientX;
        document.body.style.cursor = "col-resize"; document.body.style.userSelect = "none";
        if (leftCollapsed) { setLeftCollapsed(false); setLeftW(leftWBeforeCollapse.current); }
      }} />

      {/* ══════════════════════════════════════════════════════
          CANVAS
      ══════════════════════════════════════════════════════ */}
      <div ref={panelRef} style={{
        flex: 1, height: "100%", position: "relative", overflow: "hidden",
        background: C.bg,
        backgroundImage: `linear-gradient(to right, ${C.gridLine} 1px, transparent 1px), linear-gradient(to bottom, ${C.gridLine} 1px, transparent 1px)`,
        backgroundSize: `${32 * camera.scale}px ${32 * camera.scale}px`,
        backgroundPosition: `${camera.tx}px ${camera.ty}px`,
        cursor: "grab",
      }} onMouseDown={onCanvasMouseDown}>

        {lattices.length === 0 && (
          <div style={{ position: "absolute", inset: 0, display: "flex", alignItems: "center", justifyContent: "center", pointerEvents: "none" }}>
            <span style={{ fontSize: 11, letterSpacing: 4, color: C.inkFaint, textTransform: "uppercase" }}>Add a lattice to begin</span>
          </div>
        )}

        <svg style={{ position: "absolute", inset: 0, width: "100%", height: "100%", overflow: "visible" }}>
          <defs>
            <marker id="arr" markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
              <path d="M0,0 L0,6 L6,3 Z" fill={C.inkMid} opacity="0.6" />
            </marker>
            {latticeViews.flatMap(({ colorMap }) =>
              Object.entries(colorMap).map(([ord, col]) => (
                <marker key={`arr-${ord}-${col}`} id={`arr-${ord}`} markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                  <path d="M0,0 L0,6 L6,3 Z" fill={col} />
                </marker>
              ))
            )}
          </defs>

          <g transform={`translate(${camera.tx}, ${camera.ty}) scale(${camera.scale})`}>
            {latticeViews.map(({ entry, nodes, colorMap, accent, hlEdgeSet, adjacentNodes }) => (
              <g key={entry.id}>
                {/* Edges */}
                {entry.showEdges && entry.base.edges.map(([a, b], i) => {
                  const na = nodes[a], nb = nodes[b];
                  const hl = hlEdgeSet.has(i);
                  const col = hl ? orderColor(na.order, colorMap) : "#9aaa88";
                  const sw = hl ? 2.5 : 1.4;
                  const mx = (na.x + nb.x) / 2, my = (na.y + nb.y) / 2;
                  const markerId = hl ? `arr-${na.order}` : "arr";
                  return (
                    <g key={i}>
                      <line x1={na.x} y1={na.y} x2={nb.x} y2={nb.y} stroke={col} strokeWidth={sw} opacity={hl ? 1 : 0.6} strokeLinecap="round" />
                      {entry.showArrows && (
                        <line
                          x1={mx - (nb.x - na.x) * 0.001} y1={my - (nb.y - na.y) * 0.001}
                          x2={mx + (nb.x - na.x) * 0.001} y2={my + (nb.y - na.y) * 0.001}
                          stroke={col} strokeWidth={sw} strokeLinecap="round"
                          markerEnd={`url(#${markerId})`} opacity={hl ? 1 : 0.5} />
                      )}
                    </g>
                  );
                })}

                {/* Occluders */}
                {nodes.map(node => <ShapeOccluder key={`occ-${node.id}`} node={node} R={26} />)}

                {/* Nodes */}
                {nodes.map(node => {
                  const key = `${entry.id}:${node.id}`;
                  return (
                    <ShapeNode key={node.id} node={node} colorMap={colorMap}
                      isSelected={selectedIds.has(key)}
                      isAdjacent={adjacentNodes.has(node.id) && !selectedIds.has(key)}
                      onToggleSelect={nodeId => toggleNodeSelect(entry.id, nodeId)}
                      onMouseDown={(nodeId, e) => onNodeMouseDown(entry.id, nodeId, e)} />
                  );
                })}

                {/* Epicenter */}
                {entry.showEpicenter && (
                  <Epicenter
                    x={entry.epicenter.x} y={entry.epicenter.y}
                    accent={accent}
                    onMouseDown={(e) => onEpicenterMouseDown(entry.id, e)} />
                )}
              </g>
            ))}
          </g>
        </svg>

        {/* Zoom reset */}
        <div style={{ position: "absolute", bottom: 14, right: 14, zIndex: 3, display: "flex", gap: 6 }}>
          <button onClick={() => {
            if (!panelRef.current) return;
            const r = panelRef.current.getBoundingClientRect();
            setCamera({ tx: r.width / 4, ty: r.height / 4, scale: 0.75 });
          }} style={{ background: C.bg, border: `1px solid ${C.border}`, borderRadius: 5, padding: "5px 9px", cursor: "pointer", fontSize: 9, color: C.inkMid, letterSpacing: 2, textTransform: "uppercase" }}>
            {Math.round(camera.scale * 100)}% ↺
          </button>
        </div>
      </div>

      {/* Right splitter */}
      <VSplitter onMouseDown={(e) => {
        e.preventDefault(); rightSplitDragging.current = true; rightSplitStart.current = e.clientX;
        document.body.style.cursor = "col-resize"; document.body.style.userSelect = "none";
        if (rightCollapsed) { setRightCollapsed(false); setRightW(rightWBeforeCollapse.current); }
      }} />

      {/* ══════════════════════════════════════════════════════
          RIGHT PANEL
      ══════════════════════════════════════════════════════ */}
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
          {/* Pane 1: Group Info — one Section per lattice */}
          <Pane title="Group Info" height={rightPane1H}>
            {latticeViews.length === 0
              ? <div style={{ color: C.inkFaint, fontSize: 11 }}>No lattices added.</div>
              : <div style={{ margin: "-12px -14px" }}>
                  {latticeViews.map(({ entry, nodes, fullNode, colorMap, accent, coprimes, zParts, expVal }) => (
                    <Section key={entry.id} label={`U(${entry.x})`} depth={0} accent={accent} defaultOpen={latticeViews.length === 1}>
                      {/* Stats */}
                      <Section label="Stats" depth={1} defaultOpen={false}>
                        <SectionBody>
                          <div style={{ marginBottom: 8, padding: "5px 8px", background: C.statsRow, borderRadius: 4, border: `1px solid ${C.border}` }}>
                            <div style={{ fontSize: 8, letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", marginBottom: 2 }}>Isomorphism Type</div>
                            <div style={{ fontSize: 13, fontWeight: "700", color: C.ink, fontFamily: "'Courier New', monospace", wordBreak: "break-all" }}>
                              U({entry.x}) ≅ {formatZ(zParts)}
                            </div>
                          </div>
                        </SectionBody>
                        {fullNode && [
                          [`|U(${entry.x})|`, fullNode.order],
                          ["Subgroups", nodes.length],
                          ["Levels",    (entry.base.maxLevel ?? 0) + 1],
                          ["Hasse edges", entry.base.edges.length],
                          ["Rank",     fullNode.generators.length > 0 ? fullNode.generators[0].length : 1],
                          ["Exponent", expVal],
                          ["Abelian",  "yes"],
                        ].map(([k, v]) => <SectionRow key={k} label={k} value={String(v)} accent={k === "Abelian" ? "#4ade80" : undefined} />)}
                      </Section>

                      {/* Display controls */}
                      <Section label="Display" depth={1} defaultOpen={false}>
                        <SectionToggle label="Show Edges"
                          checked={entry.showEdges}
                          onChange={v => updateLattice(entry.id, { showEdges: v })} />
                        <SectionToggle label="Show Arrows"
                          checked={entry.showArrows}
                          onChange={v => updateLattice(entry.id, { showArrows: v })} />
                        <SectionToggle label="Show Epicenter ☉"
                          checked={entry.showEpicenter}
                          onChange={v => updateLattice(entry.id, { showEpicenter: v })} />
                        <SectionBody>
                          <div style={{ fontSize: 9, color: C.inkFaint, lineHeight: 1.6 }}>
                            Drag the ☉ marker on the canvas to move the entire lattice.
                          </div>
                        </SectionBody>
                      </Section>
                    </Section>
                  ))}
                </div>
            }
          </Pane>

          <HPSplitter onDrag={onRightSplit12} />

          {/* Pane 2: Selected nodes — fills rest */}
          <Pane title={`Selected${allSelectedNodes.length > 1 ? ` (${allSelectedNodes.length})` : ""}`} style={{ flex: 1 }}>
            {allSelectedNodes.length > 0
              ? <div style={{ margin: "-12px -14px" }}>
                  {allSelectedNodes.map(({ node, colorMap, latticeId, latticeX, indexVal }) => {
                    const col = orderColor(node.order, colorMap);
                    const cyclicLabel = node.order === 1 ? "Trivial" : node.isCyclic ? "Cyclic" : node.shape === "square" ? "Non-cyclic · pair gens" : "Non-cyclic · triple gens";
                    return (
                      <Section key={`${latticeId}:${node.id}`} label={node.shortLabel} badge={`ord ${node.order}`} accent={col} depth={0} defaultOpen={false}>
                        <Section label="Label & Style" depth={1} defaultOpen={false}>
                          <SectionRow label="Group" value={`U(${latticeX})`} />
                          <SectionRow label="Type" value={cyclicLabel} />
                          {node.isCyclic && <SectionRow label="Iso" value={`ℤ${node.order}`} accent={col} />}
                          <SectionBody>
                            <div style={{ fontSize: 11, color: C.ink, fontFamily: "'Courier New', monospace", wordBreak: "break-all", lineHeight: 1.5 }}>{node.label}</div>
                          </SectionBody>
                        </Section>
                        <Section label="Info" depth={1} defaultOpen={false}>
                          <Section label="Metrics" depth={2} defaultOpen={false}>
                            <SectionRow label="Order" value={String(node.order)} accent={col} />
                            <SectionRow label="Level" value={String(node.level)} />
                            <SectionRow label="Index" value={String(indexVal)} />
                          </Section>
                          <Section label="Elements" depth={2} defaultOpen={false} badge={node.elements.length}>
                            <SectionBody>
                              <div style={{ display: "flex", flexWrap: "wrap", gap: 4 }}>
                                {node.elements.map(el => (
                                  <span key={el} style={{ fontSize: 11, color: col, fontWeight: "700", fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "2px 7px", border: `1px solid ${C.border}` }}>{el}</span>
                                ))}
                              </div>
                            </SectionBody>
                          </Section>
                          <Section label="Generators" depth={2} defaultOpen={false} badge={node.generators.length}>
                            <SectionBody>
                              {node.generators.length === 0
                                ? <span style={{ fontSize: 11, color: C.inkFaint }}>∅ trivial</span>
                                : <div style={{ display: "flex", flexDirection: "column", gap: 4 }}>
                                    {node.generators.map((g, i) => (
                                      <div key={i} style={{ fontSize: 11, color: C.inkMid, fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "3px 8px", border: `1px solid ${C.border}` }}>⟨{g.join(", ")}⟩</div>
                                    ))}
                                  </div>
                              }
                            </SectionBody>
                          </Section>
                        </Section>
                      </Section>
                    );
                  })}
                </div>
              : <div style={{ fontSize: 11, color: C.inkFaint, fontStyle: "italic" }}>Click nodes to select them.</div>
            }
          </Pane>
        </>}
      </div>
    </div>
  );
}
