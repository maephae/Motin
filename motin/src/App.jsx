import { useState, useEffect, useRef, useCallback, useLayoutEffect } from "react";
import JSZip from 'jszip';

// ═══════════════════════════════════════════════════════════════════════
//  TABLE ENGINE
//  Every group is defined by { table: number[][], labels: string[] }
//  table[i][j] = index of the product of element i and element j
//  Identity is always index 0.
// ═══════════════════════════════════════════════════════════════════════

// ── SAVE / LOAD SYSTEM ────────────────────────────────────────────────

const SAVE_VERSION = "1.0.0";

function serializeCanvasState(state) {
  return {
    version: SAVE_VERSION,
    timestamp: new Date().toISOString(),
    lattices: state.lattices.map(l => ({
      id: l.id,
      label: l.label,
      kind: l.kind,
      param: l.param,
      param2: l.param2,         
      param3: l.param3,          
      epicenter: l.epicenter,
      nodePositions: l.nodePositions,
      showArrows: l.showArrows,
      showEdges: l.showEdges,
      showEpicenter: l.showEpicenter,
      isCollapsed: l.isCollapsed,
      _collapsedRepId: l._collapsedRepId,
      hasseLayout: l.hasseLayout,
      viewType: l.viewType || l.base?.viewType || "hasse",
      // ✅ Store the full base (nodes, edges, layout, table, labels)
      base: l.base,
    })),
    morphisms: state.morphisms,
    notes: state.notes,
    drawStrokes: state.drawStrokes,
    nodeCustomStyles: state.nodeCustomStyles,
    gridSettings: state.gridSettings,
    camera: state.camera,
  };
}

function deserializeCanvasState(data) {
  const lattices = data.lattices.map(savedLattice => ({
    ...savedLattice,
    // ✅ Use the stored base directly instead of rebuilding from catalog
    base: savedLattice.base || { nodes: [], edges: [], W: 400, H: 400 },
    nodePositions: savedLattice.nodePositions || {},
    epicenter: savedLattice.epicenter || { x: 400, y: 300 },
    id: savedLattice.id || Date.now() + Math.random(),
  }));
  
  return {
    lattices,
    morphisms: data.morphisms || [],
    notes: data.notes || [],
    drawStrokes: data.drawStrokes || [],
    nodeCustomStyles: data.nodeCustomStyles || {},
    gridSettings: data.gridSettings || { color: "#DEE7DC", size: 32, pattern: "lines" },
    camera: data.camera || { tx: 0, ty: 0, scale: 1 },
  };
}


// ── Generators ────────────────────────────────────────────────────────

function tableFromCyclic(n) {
  const table = Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) => (i + j) % n)
  );
  // Labels as [a]₀, [a]₁ ... but identity stays "e", exponent-style
  const SUB = "₀₁₂₃₄₅₆₇₈₉";
  const sub = x => String(x).split("").map(d => SUB[parseInt(d)] ?? d).join("");
  const labels = Array.from({ length: n }, (_, i) => i === 0 ? "e" : `a${sub(i)}`);
  return { table, labels };
}

function tableFromDihedral(n) {
  // Elements: r^0..r^(n-1), s·r^0..s·r^(n-1)  — index = rotation + flip*n
  // Product: (r^a · s^p)(r^b · s^q) = r^(a + (-1)^p · b) · s^(p+q)
  const order = 2 * n;
  const table = Array.from({ length: order }, (_, i) => {
    const [a, p] = [i % n, i < n ? 0 : 1];
    return Array.from({ length: order }, (_, j) => {
      const [b, q] = [j % n, j < n ? 0 : 1];
      const newRot = ((a + (p === 0 ? b : n - b)) % n + n) % n;
      const newFlip = (p + q) % 2;
      return newFlip === 0 ? newRot : n + newRot;
    });
  });
  const SUB = "₀₁₂₃₄₅₆₇₈₉";
  const sub = x => String(x).split("").map(d => SUB[parseInt(d)] ?? d).join("");
  const labels = [
    ...Array.from({ length: n }, (_, i) => i === 0 ? "e" : `r${sub(i)}`),
    ...Array.from({ length: n }, (_, i) => i === 0 ? "s" : `sr${sub(i)}`),
  ];
  return { table, labels };
}

function tableFromSymmetric(n) {
  // Build all permutations of [0..n-1], compose left-to-right: (f∘g)(x) = f(g(x))
  function permutations(arr) {
    if (arr.length <= 1) return [arr];
    return arr.flatMap((v, i) =>
      permutations([...arr.slice(0, i), ...arr.slice(i + 1)]).map(p => [v, ...p])
    );
  }
  const perms = permutations(Array.from({ length: n }, (_, i) => i));
  // put identity first
  const idIdx = perms.findIndex(p => p.every((v, i) => v === i));
  if (idIdx > 0) { const tmp = perms[0]; perms[0] = perms[idIdx]; perms[idIdx] = tmp; }
  // build lookup AFTER swap so identity is correctly at index 0
  const key = p => p.join(",");
  const lookup = new Map(perms.map((p, i) => [key(p), i]));
  const order = perms.length;
  const table = Array.from({ length: order }, (_, i) =>
    Array.from({ length: order }, (_, j) => {
      const composed = perms[i].map(x => perms[j][x]);
      return lookup.get(key(composed));
    })
  );
  const cycleNotation = p => {
    const visited = new Array(n).fill(false);
    const cycles = [];
    for (let i = 0; i < n; i++) {
      if (visited[i] || p[i] === i) { visited[i] = true; continue; }
      const cycle = [];
      let cur = i;
      while (!visited[cur]) { visited[cur] = true; cycle.push(cur + 1); cur = p[cur]; }
      if (cycle.length > 1) cycles.push(`(${cycle.join("")})`);
    }
    return cycles.length === 0 ? "e" : cycles.join("");
  };
  return { table, labels: perms.map(cycleNotation) };
}

function tableFromQuaternion() {
  // Q8 = {1,-1,i,-i,j,-j,k,-k} indices 0..7
  // Multiplication rules: i²=j²=k²=-1, ij=k, jk=i, ki=j, ji=-k, kj=-i, ik=-j
  // Row a, Col b => a*b
  // 0=1,1=-1,2=i,3=-i,4=j,5=-j,6=k,7=-k
  const table = [
    //  1   -1    i   -i    j   -j    k   -k
    [0,  1,  2,  3,  4,  5,  6,  7], // 1*x = x
    [1,  0,  3,  2,  5,  4,  7,  6], // -1*x
    [2,  3,  1,  0,  6,  7,  5,  4], // i*x:  i*1=i, i*-1=-i, i*i=-1, i*-i=1, i*j=k, i*-j=-k, i*k=-j, i*-k=j
    [3,  2,  0,  1,  7,  6,  4,  5], // -i*x
    [4,  5,  7,  6,  1,  0,  2,  3], // j*x:  j*1=j, j*-1=-j, j*i=-k, j*-i=k, j*j=-1, j*-j=1, j*k=i, j*-k=-i
    [5,  4,  6,  7,  0,  1,  3,  2], // -j*x
    [6,  7,  4,  5,  3,  2,  1,  0], // k*x:  k*1=k, k*-1=-k, k*i=j, k*-i=-j, k*j=-i, k*-j=i, k*k=-1, k*-k=1
    [7,  6,  5,  4,  2,  3,  0,  1], // -k*x
  ];
  return { table, labels: ["1","-1","i","-i","j","-j","k","-k"] };
}

function tableFromDirectProduct(g1, g2) {
  const { table: t1, labels: l1 } = g1;
  const { table: t2, labels: l2 } = g2;
  const n1 = t1.length, n2 = t2.length;
  const order = n1 * n2;
  const table = Array.from({ length: order }, (_, i) => {
    const [a, b] = [Math.floor(i / n2), i % n2];
    return Array.from({ length: order }, (_, j) => {
      const [c, d] = [Math.floor(j / n2), j % n2];
      return t1[a][c] * n2 + t2[b][d];
    });
  });
  const labels = Array.from({ length: order }, (_, i) =>
    `${l1[Math.floor(i / n2)]}×${l2[i % n2]}`
  );
  return { table, labels };
}

// U(n): multiplicative group mod n (elements coprime to n)
function tableFromUn(n) {
  function gcd(a, b) { while (b) { [a, b] = [b, a % b]; } return a; }
  const elems = Array.from({ length: n }, (_, i) => i + 1).filter(a => gcd(a, n) === 1);
  // Put identity (1) first
  const idIdx = elems.indexOf(1);
  if (idIdx > 0) { const tmp = elems[0]; elems[0] = elems[idIdx]; elems[idIdx] = tmp; }
  const lookup = new Map(elems.map((v, i) => [v, i]));
  const order = elems.length;
  const table = Array.from({ length: order }, (_, i) =>
    Array.from({ length: order }, (_, j) => lookup.get((elems[i] * elems[j]) % n))
  );
  return { table, labels: elems.map(String), elems };
}

// ── Single free element — one node, no edges, for annotation/placeholder use ──
function buildSingleElement(label = "a") {
  const lbl = label || "a";
  const W = 200, H = 200;
  const node = {
    id: 0, level: 0,
    x: W / 2, y: H / 2,
    label: lbl, shortLabel: lbl,
    order: 1, index: 1,
    elements: [lbl], elementIndices: [0],
    generators: [], generatorLabels: [], genAll: lbl,
    isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: true,
    viewType: "elements",
  };
  const table = [[0]];
  return { nodes: [node], edges: [], maxLevel: 0, byLevel: { 0: [0] }, W, H, nodeR: 26, kind: "Single", param: 1, table, labels: [lbl], viewType: "elements" };
}

// Parse a raw Cayley table (array of arrays of indices) with optional labels
function tableFromRaw(rawTable, rawLabels) {
  const n = rawTable.length;
  const labels = rawLabels ?? Array.from({ length: n }, (_, i) => i === 0 ? "e" : String(i));
  return { table: rawTable.map(row => [...row]), labels };
}

// ═══════════════════════════════════════════════════════════════════════
//  LATTICE ENGINE
//  All subgroup/normality/Hasse logic operates on table indices.
// ═══════════════════════════════════════════════════════════════════════

// Precompute inverse table: inv[i] = j where table[i][j] === 0 (identity)
function computeInverses(table) {
  const n = table.length;
  const inv = new Array(n);
  for (let i = 0; i < n; i++)
    for (let j = 0; j < n; j++)
      if (table[i][j] === 0) { inv[i] = j; break; }
  return inv;
}

// BFS closure: given seed indices, close under table multiplication
function getClosure(seeds, table) {
  const closure = new Set([0, ...seeds]); // 0 = identity
  const queue = [...closure];
  while (queue.length) {
    const a = queue.shift();
    for (const b of closure) {
      const ab = table[a][b];
      if (!closure.has(ab)) { closure.add(ab); queue.push(ab); }
      const ba = table[b][a];
      if (!closure.has(ba)) { closure.add(ba); queue.push(ba); }
    }
  }
  return closure;
}

// Fingerprint a subgroup as a sorted comma-joined string for dedup
function sgKey(sg) { return [...sg].sort((a, b) => a - b).join(","); }

// Find all subgroups via generator closure + dedup
function findAllSubgroups(table) {
  const n = table.length;
  const seen = new Map(); // key → Set

  const add = sg => {
    const k = sgKey(sg);
    if (!seen.has(k)) seen.set(k, sg);
  };

  // Trivial and full group
  add(new Set([0]));
  add(new Set(Array.from({ length: n }, (_, i) => i)));

  // Single-element closures
  for (let i = 1; i < n; i++) add(getClosure([i], table));

  // Two-element closures
  for (let i = 1; i < n; i++)
    for (let j = i + 1; j < n; j++)
      add(getClosure([i, j], table));

  // Three-element closures (needed for groups like S4 where rank-3 subgroups exist)
  // Only run if needed — gate on order to keep S3/D6 fast
  if (n > 12) {
    for (let i = 1; i < n; i++)
      for (let j = i + 1; j < n; j++)
        for (let k = j + 1; k < n; k++)
          add(getClosure([i, j, k], table));
  }

  // Sort by size
  return [...seen.values()].sort((a, b) => a.size - b.size);
}

// Check if sg is a normal subgroup: gHg⁻¹ ⊆ H for all g
function isNormal(sg, table, inv) {
  const n = table.length;
  for (let g = 0; g < n; g++) {
    for (const h of sg) {
      const conj = table[g][table[h][inv[g]]];
      if (!sg.has(conj)) return false;
    }
  }
  return true;
}

// Hasse cover: transitive reduction of containment on subgroups (sorted by size asc)
function buildHasseCover(subgroups) {
  const n = subgroups.length;
  const edges = [];

  // For each pair (i < j) where sgs[i] ⊂ sgs[j], check there's no k between them
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
      if (subgroups[i].size >= subgroups[j].size) continue;
      // Check subset
      let sub = true;
      for (const v of subgroups[i]) { if (!subgroups[j].has(v)) { sub = false; break; } }
      if (!sub) continue;
      // Check no intermediate k
      let covered = false;
      for (let k = i + 1; k < j; k++) {
        if (subgroups[k].size <= subgroups[i].size || subgroups[k].size >= subgroups[j].size) continue;
        let subik = true, subkj = true;
        for (const v of subgroups[i]) { if (!subgroups[k].has(v)) { subik = false; break; } }
        if (!subik) continue;
        for (const v of subgroups[k]) { if (!subgroups[j].has(v)) { subkj = false; break; } }
        if (subkj) { covered = true; break; }
      }
      if (!covered) edges.push([i, j]);
    }
  }
  return edges;
}

// Find generators of a subgroup (min generating set)
function findSubgroupGenerators(sg, table) {
  const elems = [...sg].filter(e => e !== 0).sort((a, b) => a - b);
  if (elems.length === 0) return [];
  // Try single generators
  for (const a of elems) {
    const cl = getClosure([a], table);
    if (cl.size === sg.size && [...cl].every(v => sg.has(v))) return [[a]];
  }
  // Try pairs
  const pairs = [];
  for (let i = 0; i < elems.length; i++)
    for (let j = i + 1; j < elems.length; j++) {
      const cl = getClosure([elems[i], elems[j]], table);
      if (cl.size === sg.size && [...cl].every(v => sg.has(v)))
        pairs.push([elems[i], elems[j]]);
    }
  if (pairs.length) return pairs;
  // Try triples
  const triples = [];
  for (let i = 0; i < elems.length; i++)
    for (let j = i + 1; j < elems.length; j++)
      for (let k = j + 1; k < elems.length; k++) {
        const cl = getClosure([elems[i], elems[j], elems[k]], table);
        if (cl.size === sg.size && [...cl].every(v => sg.has(v)))
          triples.push([elems[i], elems[j], elems[k]]);
      }
  return triples.length ? triples : [[...sg].filter(e => e !== 0)];
}

// ── Convert a { table, labels } group to the layout-ready node/edge format ──
function buildLatticeFromTable({ table, labels }, kind, param) {
  const inv = computeInverses(table);
  const subgroups = findAllSubgroups(table);
  const coverEdges = buildHasseCover(subgroups);
  const orderG = table.length;

  const rawNodes = subgroups.map((sg, i) => {
    const gens = findSubgroupGenerators(sg, table);
    const rank = gens.length > 0 ? gens[0].length : 0;
    const shape = rank <= 1 ? "circle" : rank === 2 ? "square" : "triangle";
    const multiGen = gens.length > 1;
    // Generator notation: ⟨a⟩ for the Hasse/subgroup view
    const genStrs = gens.map(t => "⟨" + t.map(idx => labels[idx]).join(", ") + "⟩");
    const genAll = genStrs.length === 0 ? "∅"
      : genStrs.length === 1 ? genStrs[0]
      : genStrs.slice(0, -1).join(", ") + " or " + genStrs[genStrs.length - 1];
    // shortLabel uses generator bracket notation ⟨·⟩ — this is the subgroup generated by
    const shortLabel = sg.size === 1 ? "{e}"
      : gens.length > 0 ? "⟨" + gens[0].map(idx => labels[idx]).join(", ") + "⟩"
      : "?";
    const elemArr = [...sg].sort((a, b) => a - b);
    const normal = isNormal(sg, table, inv);
    // Set notation {a, b, c} for the full element-set label
    return {
      label: "{" + elemArr.map(idx => labels[idx]).join(", ") + "}",
      shortLabel,
      order: sg.size,
      index: orderG / sg.size,
      elements: elemArr.map(idx => labels[idx]),
      elementIndices: elemArr,
      generators: gens,
      generatorLabels: gens.map(t => t.map(idx => labels[idx])),
      genAll,
      isCyclic: rank === 1 || sg.size === 1,
      rank: Math.max(rank, 1),
      shape,
      multiGen,
      isNormal: normal,
      viewType: "hasse",
    };
  });

  return { ...layoutLattice(rawNodes, coverEdges), kind, param, table, labels };
}

// ═══════════════════════════════════════════════════════════════════════
//  MORPHISM ENGINE — table-driven, works for any two groups
// ═══════════════════════════════════════════════════════════════════════

function checkHomomorphism(phi, tableG, tableH) {
  // phi: Map<labelG, labelH> — we need element-index maps
  // Returns { isHomo: bool, witness: [a,b] | null }
  for (const [aLbl, faLbl] of phi) {
    for (const [bLbl, fbLbl] of phi) {
      const a = phi._idxG?.get(aLbl);
      const b = phi._idxG?.get(bLbl);
      const fa = phi._idxH?.get(faLbl);
      const fb = phi._idxH?.get(fbLbl);
      if (a == null || b == null || fa == null || fb == null) continue;
      const ab = tableG[a][b];
      const fabLbl = [...phi][ab]?.[1]; // label of phi(a*b)
      const fafb = tableH[fa][fb];
      if (fabLbl == null) continue;
      const fabIdx = phi._idxH?.get(fabLbl);
      if (fabIdx == null || fabIdx !== fafb) return { isHomo: false, witness: [aLbl, bLbl] };
    }
  }
  return { isHomo: true, witness: null };
}

// ═══════════════════════════════════════════════════════════════════════
//  U(n) HELPERS  (kept for right-panel isomorphism display only)
// ═══════════════════════════════════════════════════════════════════════

function gcd(a, b) { while (b) { [a, b] = [b, a % b]; } return a; }
function setsEqual(a, b) { if (a.size !== b.size) return false; for (const v of a) if (!b.has(v)) return false; return true; }
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
function formatZ(parts) {
  if (!parts.length) return "trivial";
  const SUB = "₀₁₂₃₄₅₆₇₈₉";
  const sub = x => String(x).split("").map(d => SUB[parseInt(d)] ?? d).join("");
  return parts.map(p => "ℤ" + sub(p)).join(" × ");
}
function groupExponent(elems, n) {
  function lcm(a, b) { return a / gcd(a, b) * b; }
  function elementOrder(a) { let o = 1, cur = a; while (cur !== 1) { cur = (cur * a) % n; o++; if (o > n) break; } return o; }
  return elems.reduce((acc, a) => lcm(acc, elementOrder(a)), 1);
}

// ═══════════════════════════════════════════════════════════════════════
//  LAYOUT ENGINE  (unchanged from original)
// ═══════════════════════════════════════════════════════════════════════

function layoutLattice(rawNodes, coverEdges) {
  const n = rawNodes.length;
  if (n === 0) return { nodes: [], edges: [], maxLevel: 0, byLevel: {}, W: 400, H: 400, nodeR: 26 };

  const levels = new Array(n).fill(-1);
  levels[0] = 0;
  const q = [0];
  while (q.length) {
    const cur = q.shift();
    for (const [a, b] of coverEdges) {
      if (a === cur && levels[b] === -1) { levels[b] = levels[cur] + 1; q.push(b); }
    }
  }
  const maxReached = Math.max(...levels.filter(l => l >= 0));
  for (let i = 0; i < n; i++) if (levels[i] === -1) levels[i] = maxReached;

  const maxLevel = Math.max(...levels);
  const byLevel = {};
  rawNodes.forEach((_, i) => { const lv = levels[i]; (byLevel[lv] = byLevel[lv] || []).push(i); });

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

  const nodes = rawNodes.map((rn, i) => ({
    ...rn, id: i, level: levels[i], x: posX[i], y: posY[i],
  }));
  return { nodes, edges: coverEdges, maxLevel, byLevel, W, H, nodeR: NODE_R };
}

// ═══════════════════════════════════════════════════════════════════════
//  ALTERNATIVE VIEW BUILDERS
//  All return the same { nodes, edges, W, H, maxLevel, byLevel, nodeR,
//  kind, param, table, labels } shape as buildLatticeFromTable.
//  "element" views: one node per group element, structured layout.
//  "cayley" views: directed graph of generator actions.
// ═══════════════════════════════════════════════════════════════════════

// Shared: make a minimal node descriptor for an element view
// (not a subgroup — each node IS one element, shown in coset/element notation [a])
function mkElemNode(label, orderOfElem, idx) {
  return {
    label,
    // Element notation: [a] denotes the element/coset, distinct from ⟨a⟩ (subgroup generated)
    shortLabel: `[${label}]`,
    order: orderOfElem,
    index: 1,
    elements: [label],
    elementIndices: [idx],
    generators: [],
    generatorLabels: [],
    genAll: `[${label}]`,
    isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: false,
    viewType: "elements",
  };
}

// Compute the order of element at index i in the table
function elementOrder(i, table) {
  let cur = i, o = 1;
  while (cur !== 0) { cur = table[cur][i]; o++; if (o > table.length + 1) return -1; }
  return o;
}

// Place n nodes evenly around a circle of given radius, centered at (cx,cy)
function ringPositions(n, radius, cx, cy, offsetAngle = -Math.PI / 2) {
  return Array.from({ length: n }, (_, i) => {
    const a = offsetAngle + (2 * Math.PI * i) / n;
    return { x: cx + radius * Math.cos(a), y: cy + radius * Math.sin(a) };
  });
}

// ── Element ring for ℤₙ: n nodes in a circle, edges = generator action ──
function elementRingCyclic(n) {
  const { table, labels } = tableFromCyclic(n);
  const R = Math.max(100, n * 18);
  const W = R * 2 + 120, H = R * 2 + 120;
  const cx = W / 2, cy = H / 2;
  const pos = ringPositions(n, R, cx, cy);
  const nodes = labels.map((lbl, i) => ({
    ...mkElemNode(lbl, elementOrder(i, table), i),
    id: i, level: 0, x: pos[i].x, y: pos[i].y,
  }));
  // Edges: each element → next (generator r adds 1)
  const edges = Array.from({ length: n }, (_, i) => [i, (i + 1) % n]);
  return { nodes, edges, maxLevel: 0, byLevel: { 0: nodes.map((_, i) => i) }, W, H, nodeR: 26, kind: "Zn", param: n, table, labels, viewType: "elements" };
}

// ── Element layout for Dₙ: inner rotation ring + outer reflection ring ──
function elementRingDihedral(n) {
  const { table, labels } = tableFromDihedral(n);
  const order = 2 * n;
  const Rinner = Math.max(80, n * 16);
  const Router = Rinner + 80;
  const W = Router * 2 + 120, H = Router * 2 + 120;
  const cx = W / 2, cy = H / 2;
  const innerPos = ringPositions(n, Rinner, cx, cy);
  const outerPos = ringPositions(n, Router, cx, cy);
  const nodes = labels.map((lbl, i) => {
    const isFlip = i >= n;
    const pos = isFlip ? outerPos[i - n] : innerPos[i];
    return {
      ...mkElemNode(lbl, elementOrder(i, table), i),
      id: i, level: isFlip ? 1 : 0, x: pos.x, y: pos.y,
    };
  });
  // Rotation edges (inner ring cycle)
  const edges = [];
  for (let i = 0; i < n; i++) edges.push([i, (i + 1) % n]);
  // Reflection edges: each reflection → next reflection
  for (let i = 0; i < n; i++) edges.push([n + i, n + ((i + 1) % n)]);
  // Spokes: r^i ↔ s·r^i
  for (let i = 0; i < n; i++) edges.push([i, n + i]);
  return { nodes, edges, maxLevel: 1, byLevel: { 0: Array.from({ length: n }, (_, i) => i), 1: Array.from({ length: n }, (_, i) => n + i) }, W, H, nodeR: 26, kind: "Dihedral", param: n, table, labels, viewType: "elements" };
}

// ── Element layout for Sₙ: grid by (cycle_type_length, position) ──
function elementGridSymmetric(n) {
  const { table, labels } = tableFromSymmetric(n);
  const order = table.length;
  // Group elements by their order
  const byOrder = {};
  for (let i = 0; i < order; i++) {
    const o = elementOrder(i, table);
    (byOrder[o] = byOrder[o] || []).push(i);
  }
  const orderKeys = Object.keys(byOrder).map(Number).sort((a, b) => a - b);
  const SPACING = 64, PAD = 60;
  const maxInRow = Math.max(...orderKeys.map(o => byOrder[o].length));
  const W = Math.max(480, PAD * 2 + SPACING * maxInRow);
  const H = Math.max(300, PAD * 2 + SPACING * orderKeys.length);
  const nodes = new Array(order);
  orderKeys.forEach((o, row) => {
    const elems = byOrder[o];
    elems.forEach((idx, col) => {
      const x = PAD + (col + 0.5) * (W - 2 * PAD) / elems.length;
      const y = PAD + row * SPACING;
      nodes[idx] = { ...mkElemNode(labels[idx], o, idx), id: idx, level: row, x, y };
    });
  });
  const byLevel = {};
  orderKeys.forEach((o, row) => { byLevel[row] = byOrder[o]; });
  return { nodes, edges: [], maxLevel: orderKeys.length - 1, byLevel, W, H, nodeR: 26, kind: "Symmetric", param: n, table, labels, viewType: "elements" };
}

// ── Element layout for U(n): ring ordered by element value ──
function elementRingUn(n) {
  const g = tableFromUn(n);
  const { table, labels } = g;
  const order = table.length;
  const R = Math.max(100, order * 14);
  const W = R * 2 + 120, H = R * 2 + 120;
  const cx = W / 2, cy = H / 2;
  const pos = ringPositions(order, R, cx, cy);
  const nodes = labels.map((lbl, i) => ({
    ...mkElemNode(lbl, elementOrder(i, table), i),
    id: i, level: 0, x: pos[i].x, y: pos[i].y,
  }));
  return { nodes, edges: [], maxLevel: 0, byLevel: { 0: nodes.map((_, i) => i) }, W, H, nodeR: 26, kind: "Un", param: n, table, labels, viewType: "elements" };
}

// ── Element layout for Q₈: symmetric octagon ──
function elementRingQ8() {
  const { table, labels } = tableFromQuaternion();
  const R = 110;
  const W = R * 2 + 120, H = R * 2 + 120;
  const cx = W / 2, cy = H / 2;
  const pos = ringPositions(8, R, cx, cy);
  const nodes = labels.map((lbl, i) => ({
    ...mkElemNode(lbl, elementOrder(i, table), i),
    id: i, level: 0, x: pos[i].x, y: pos[i].y,
  }));
  // Edges between {1,-1} (opposite), i↔-i, j↔-j, k↔-k
  const edges = [[0,1],[2,3],[4,5],[6,7]];
  return { nodes, edges, maxLevel: 0, byLevel: { 0: [0,1,2,3,4,5,6,7] }, W, H, nodeR: 26, kind: "Q8", param: 8, table, labels, viewType: "elements" };
}

// ── Element layout for ℤₙ×ℤₘ: n×m grid ──
function elementGridZnZm(n, m) {
  const { table, labels } = tableFromDirectProduct(tableFromCyclic(n), tableFromCyclic(m));
  const order = n * m;
  const SPACING = 68, PAD = 50;
  const W = PAD * 2 + SPACING * m, H = PAD * 2 + SPACING * n;
  const nodes = labels.map((lbl, i) => {
    const row = Math.floor(i / m), col = i % m;
    return {
      ...mkElemNode(lbl, elementOrder(i, table), i),
      id: i, level: row,
      x: PAD + (col + 0.5) * SPACING,
      y: PAD + (row + 0.5) * SPACING,
    };
  });
  const byLevel = {};
  for (let r = 0; r < n; r++) byLevel[r] = Array.from({ length: m }, (_, c) => r * m + c);
  return { nodes, edges: [], maxLevel: n - 1, byLevel, W, H, nodeR: 26, kind: "ZnxZm", param: n, table, labels, viewType: "elements" };
}

// ── Cayley graph: directed edges for each generator, colored ──
// Returns same shape but edges carry { from, to, genIdx } (color in render)
function cayleyGraph(tableData, kind, param, genIndices) {
  const { table, labels } = tableData;
  const order = table.length;
  const R = Math.max(120, order * 14);
  const W = R * 2 + 120, H = R * 2 + 120;
  const cx = W / 2, cy = H / 2;
  const pos = ringPositions(order, R, cx, cy);
  const nodes = labels.map((lbl, i) => ({
    ...mkElemNode(lbl, elementOrder(i, table), i),
    id: i, level: 0, x: pos[i].x, y: pos[i].y,
  }));
  // One directed edge per element per generator: i → table[i][g]
  const edges = [];
  for (const g of genIndices) {
    for (let i = 0; i < order; i++) {
      const target = table[i][g];
      if (target !== i) edges.push([i, target]);
    }
  }
  return { nodes, edges, maxLevel: 0, byLevel: { 0: nodes.map((_, i) => i) }, W, H, nodeR: 26, kind, param, table, labels, viewType: "cayley" };
}

// ── Generalized quaternion group Q_{4n} ────────────────────────────────
// Presentation: <x, y | x^(2n)=e, y^2=x^n, yxy^{-1}=x^{-1}>
// Elements: x^0..x^(2n-1), y, x^1y..x^(2n-1)y  (total 4n)
// Multiplication rules (using 0-indexed exponents mod 2n):
//   x^i · x^j        = x^((i+j) mod 2n)
//   x^i · x^j·y      = x^((i+j) mod 2n)·y
//   x^i·y · x^j      = x^((i-j) mod 2n)·y
//   x^i·y · x^j·y    = x^((i-j+n) mod 2n)
function tableFromQ4n(n) {
  if (n < 2) n = 2;
  const twon = 2 * n, order = 4 * n;
  const table = Array.from({ length: order }, (_, a) => {
    const [ai, ay] = a < twon ? [a, 0] : [a - twon, 1];
    return Array.from({ length: order }, (_, b) => {
      const [bi, by] = b < twon ? [b, 0] : [b - twon, 1];
      if (!ay && !by) return ((ai + bi) % twon);
      if (!ay &&  by) return twon + ((ai + bi) % twon);
      if ( ay && !by) return twon + (((ai - bi) % twon + twon) % twon);
      return (((ai - bi + n) % twon) + twon) % twon;
    });
  });
  const SUP = "⁰¹²³⁴⁵⁶⁷⁸⁹";
  const sup = x => String(x).split("").map(d => SUP[parseInt(d)] ?? d).join("");
  let labels;
  if (n === 2) {
    // Q8: classical quaternion labels. x-coset: x^0=1, x^1=i, x^2=-1, x^3=-i
    // y-coset positions: y=j, x^1y=k, x^2y=-j, x^3y=-k  (derived from ij=k, etc.)
    labels = ["1", "i", "-1", "-i", "j", "k", "-j", "-k"];
  } else if (n === 3) {
    // Q12: dicyclic Dic3, classical a/b notation
    labels = [
      ...Array.from({ length: twon }, (_, i) => i === 0 ? "e" : "a" + sup(i)),
      ...Array.from({ length: twon }, (_, i) => i === 0 ? "b" : "a" + sup(i) + "b"),
    ];
  } else {
    // General Q_{4n}: x-coset, y-coset
    labels = [
      ...Array.from({ length: twon }, (_, i) => i === 0 ? "e" : "x" + sup(i)),
      ...Array.from({ length: twon }, (_, i) => i === 0 ? "y" : "x" + sup(i) + "y"),
    ];
  }
  return { table, labels };
}

function elementRingQ4n(n) {
  if (n < 2) n = 2;
  const { table, labels } = tableFromQ4n(n);
  const twon = 2 * n;
  const Rinner = Math.max(70, 20 * n), Router = Math.max(140, 35 * n);
  const W = Router * 2 + 120, H = Router * 2 + 120;
  const cx = W / 2, cy = H / 2;
  const innerPos = ringPositions(twon, Rinner, cx, cy);
  const outerPos = ringPositions(twon, Router, cx, cy);
  const nodes = labels.map((lbl, i) => {
    const isOuter = i >= twon;
    const pos = isOuter ? outerPos[i - twon] : innerPos[i];
    return { ...mkElemNode(lbl, elementOrder(i, table), i), id: i, level: isOuter ? 1 : 0, x: pos.x, y: pos.y };
  });
  const edges = [];
  for (let i = 0; i < twon; i++) edges.push([i, (i + 1) % twon]);
  for (let i = 0; i < twon; i++) edges.push([twon + i, twon + ((i + 1) % twon)]);
  for (let i = 0; i < twon; i++) edges.push([i, twon + i]);
  return {
    nodes, edges,
    maxLevel: 1,
    byLevel: { 0: Array.from({ length: twon }, (_, i) => i), 1: Array.from({ length: twon }, (_, i) => twon + i) },
    W, H, nodeR: 26, kind: "Q4n", param: n, table, labels, viewType: "elements",
  };
}

function tableFromQ12() {
  // Q12 = dicyclic group Dic3, order 12
  // Presentation: <a,x | a^6=e, x^2=a^3, xax^{-1}=a^{-1}>
  // Elements: a^0..a^5, x*a^0..x*a^5  (indices 0-5 pure rotations, 6-11 with x)
  // Multiply (a^i * x^p)(a^j * x^q):
  //   if p=0,q=0: a^(i+j mod 6)
  //   if p=0,q=1: a^i * x*a^j = x * a^(-i+j) = x*a^((j-i+6)%6)  -> index 6+(j-i+6)%6
  //   if p=1,q=0: x*a^i * a^j = x*a^(i+j mod 6)                  -> index 6+(i+j)%6
  //   if p=1,q=1: x*a^i * x*a^j = x*(a^(-i)*x)*a^j ... 
  //               = a^(-i) commutes with x gives a^i * a^(3) * a^(-j) under conjugation
  //               xax^-1=a^-1 => x*a^i = a^{-i}*x; so (x*a^i)(x*a^j)=a^{-i}*x^2*a^j=a^{-i}*a^3*a^j=a^{3-i+j mod 6}
  const order = 12, n = 6;
  const table = Array.from({ length: order }, (_, i) => {
    const [ai, pi] = i < n ? [i, 0] : [i - n, 1];
    return Array.from({ length: order }, (_, j) => {
      const [aj, pj] = j < n ? [j, 0] : [j - n, 1];
      if (pi === 0 && pj === 0) return (ai + aj) % n;
      if (pi === 0 && pj === 1) return n + ((aj - ai) % n + n) % n;
      if (pi === 1 && pj === 0) return n + (ai + aj) % n;
      // pi===1, pj===1
      return ((3 - ai + aj) % n + n) % n;
    });
  });
  const SUP = "⁰¹²³⁴⁵⁶⁷⁸⁹";
  const sup = x => String(x).split("").map(d => SUP[parseInt(d)] ?? d).join("");
  const labels = [
    ...Array.from({ length: n }, (_, i) => i === 0 ? "e" : `a${sup(i)}`),
    ...Array.from({ length: n }, (_, i) => i === 0 ? "x" : `xa${sup(i)}`),
  ];
  return { table, labels };
}

function elementRingQ12() {
  const { table, labels } = tableFromQ12();
  const order = 12, n = 6;
  const Rinner = 90, Router = 170;
  const W = Router * 2 + 120, H = Router * 2 + 120;
  const cx = W / 2, cy = H / 2;
  const innerPos = ringPositions(n, Rinner, cx, cy);
  const outerPos = ringPositions(n, Router, cx, cy);
  const nodes = labels.map((lbl, i) => {
    const isOuter = i >= n;
    const pos = isOuter ? outerPos[i - n] : innerPos[i];
    return { ...mkElemNode(lbl, elementOrder(i, table), i), id: i, level: isOuter ? 1 : 0, x: pos.x, y: pos.y };
  });
  const edges = [];
  for (let i = 0; i < n; i++) edges.push([i, (i + 1) % n]);
  for (let i = 0; i < n; i++) edges.push([n + i, n + ((i + 1) % n)]);
  for (let i = 0; i < n; i++) edges.push([i, n + i]);
  return { nodes, edges, maxLevel: 1, byLevel: { 0: Array.from({ length: n }, (_, i) => i), 1: Array.from({ length: n }, (_, i) => n + i) }, W, H, nodeR: 26, kind: "Q12", param: 12, table, labels, viewType: "elements" };
}

// ℤn × ℤm × ℤk: triple direct product
function tableFromTripleProduct(n, m, k) {
  const g1 = tableFromCyclic(n), g2 = tableFromCyclic(m), g3 = tableFromCyclic(k);
  const g12 = tableFromDirectProduct(g1, g2);
  return tableFromDirectProduct(g12, g3);
}

function elementGridZnZmZk(n, m, k) {
  const { table, labels } = tableFromTripleProduct(n, m, k);
  const order = n * m * k;
  const SPACING = 60, PAD = 50;
  // Lay out as n*m columns × k rows
  const cols = n * m, rows = k;
  const W = PAD * 2 + SPACING * cols, H = PAD * 2 + SPACING * rows;
  const nodes = labels.map((lbl, i) => {
    const row = Math.floor(i / cols), col = i % cols;
    return { ...mkElemNode(lbl, elementOrder(i, table), i), id: i, level: row, x: PAD + (col + 0.5) * SPACING, y: PAD + (row + 0.5) * SPACING };
  });
  const byLevel = {};
  for (let r = 0; r < rows; r++) byLevel[r] = Array.from({ length: cols }, (_, c) => r * cols + c);
  return { nodes, edges: [], maxLevel: rows - 1, byLevel, W, H, nodeR: 22, kind: "ZnZmZk", param: n, table, labels, viewType: "elements" };
}
function cayleyCyclic(n) {
  return cayleyGraph(tableFromCyclic(n), "Zn", n, [1]); // generator r₁
}
function tableFromAlternating(n) {
  // Aₙ = even permutations of [0..n-1]
  function permutations(arr) {
    if (arr.length <= 1) return [arr];
    return arr.flatMap((v, i) => permutations([...arr.slice(0, i), ...arr.slice(i + 1)]).map(p => [v, ...p]));
  }
  function parity(p) {
    const visited = new Array(p.length).fill(false);
    let swaps = 0;
    for (let i = 0; i < p.length; i++) {
      if (visited[i]) continue;
      let j = i, len = 0;
      while (!visited[j]) { visited[j] = true; j = p[j]; len++; }
      swaps += len - 1;
    }
    return swaps % 2 === 0 ? "even" : "odd";
  }
  const allPerms = permutations(Array.from({ length: n }, (_, i) => i));
  const evenPerms = allPerms.filter(p => parity(p) === "even");
  // identity first
  const idIdx = evenPerms.findIndex(p => p.every((v, i) => v === i));
  if (idIdx > 0) { const tmp = evenPerms[0]; evenPerms[0] = evenPerms[idIdx]; evenPerms[idIdx] = tmp; }
  const key = p => p.join(",");
  const lookup = new Map(evenPerms.map((p, i) => [key(p), i]));
  const order = evenPerms.length;
  const table = Array.from({ length: order }, (_, i) =>
    Array.from({ length: order }, (_, j) => {
      const composed = evenPerms[i].map(x => evenPerms[j][x]);
      return lookup.get(key(composed));
    })
  );
  const cycleNotation = p => {
    const visited = new Array(n).fill(false);
    const cycles = [];
    for (let i = 0; i < n; i++) {
      if (visited[i] || p[i] === i) { visited[i] = true; continue; }
      const cycle = [];
      let cur = i;
      while (!visited[cur]) { visited[cur] = true; cycle.push(cur + 1); cur = p[cur]; }
      if (cycle.length > 1) cycles.push(`(${cycle.join("")})`);
    }
    return cycles.length === 0 ? "e" : cycles.join("");
  };
  return { table, labels: evenPerms.map(cycleNotation) };
}

function elementGridAlternating(n) {
  const { table, labels } = tableFromAlternating(n);
  const order = table.length;
  const byOrder = {};
  for (let i = 0; i < order; i++) {
    const o = elementOrder(i, table);
    (byOrder[o] = byOrder[o] || []).push(i);
  }
  const orderKeys = Object.keys(byOrder).map(Number).sort((a, b) => a - b);
  const SPACING = 64, PAD = 60;
  const maxInRow = Math.max(...orderKeys.map(o => byOrder[o].length));
  const W = PAD * 2 + SPACING * maxInRow, H = PAD * 2 + SPACING * orderKeys.length;
  const nodes = [];
  orderKeys.forEach((o, row) => {
    byOrder[o].forEach((idx, col) => {
      nodes.push({
        ...mkElemNode(labels[idx], o, idx),
        id: idx, level: row,
        x: PAD + (col + (maxInRow - byOrder[o].length) / 2 + 0.5) * SPACING,
        y: PAD + (row + 0.5) * SPACING,
      });
    });
  });
  nodes.sort((a, b) => a.id - b.id);
  const byLevel = {};
  orderKeys.forEach((o, row) => { byLevel[row] = byOrder[o]; });
  return { nodes, edges: [], maxLevel: orderKeys.length - 1, byLevel, W, H, nodeR: 26, kind: "Alternating", param: n, table, labels, viewType: "elements" };
}

function cayleyDihedral(n) {
  return cayleyGraph(tableFromDihedral(n), "Dihedral", n, [1, n]); // r and s
}
//
//  LATTICE_CATEGORIES: category[] where category = {
//    key, label, groups: folder[]
//  }
//  folder = { key, label, desc, hasParam, ..., views: { key, label, build }[] }
// ═══════════════════════════════════════════════════════════════════════

// ── 3D shape projections (geometry catalog) ──────────────────────────
function project3D(pts3d, edges3d, scale = 180) {
  // Isometric-style projection: rotate ~35° around X, ~45° around Y
  const ax = 35 * Math.PI / 180, ay = 45 * Math.PI / 180;
  const pts2d = pts3d.map(([x, y, z]) => {
    const y1 = y * Math.cos(ax) - z * Math.sin(ax);
    const z1 = y * Math.sin(ax) + z * Math.cos(ax);
    const x2 = x * Math.cos(ay) + z1 * Math.sin(ay);
    const y2 = y1;
    return [x2, -y2]; // flip Y so +Y is up
  });
  const xs = pts2d.map(p => p[0]), ys = pts2d.map(p => p[1]);
  const minX = Math.min(...xs), maxX = Math.max(...xs);
  const minY = Math.min(...ys), maxY = Math.max(...ys);
  const W = 580, H = 520, PAD = 80;
  const scaleX = (W - PAD * 2) / Math.max(maxX - minX, 0.01);
  const scaleY = (H - PAD * 2) / Math.max(maxY - minY, 0.01);
  const sc = Math.min(scaleX, scaleY);
  const cx = (W - (maxX - minX) * sc) / 2, cy = (H - (maxY - minY) * sc) / 2;
  const nodes = pts2d.map(([px, py], i) => ({
    id: i, level: 0,
    x: cx + (px - minX) * sc,
    y: cy + (py - minY) * sc,
    label: `v${i + 1}`, shortLabel: `v${i+1}`,
    order: 1, index: 1, elements: [`v${i+1}`], elementIndices: [i],
    generators: [], generatorLabels: [], genAll: `v${i+1}`,
    isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: false,
    viewType: "geometry",
  }));
  const table = Array.from({ length: pts3d.length }, (_, i) => Array.from({ length: pts3d.length }, (_, j) => (i + j) % pts3d.length));
  const labels = nodes.map(n => n.label);
  return { nodes, edges: edges3d, maxLevel: 0, byLevel: { 0: nodes.map((_, i) => i) }, W, H, nodeR: 26, kind: "Geometry", param: pts3d.length, table, labels, viewType: "geometry" };
}

function buildShapeProjection(shape, param = 0) {
  const φ = (1 + Math.sqrt(5)) / 2; // golden ratio
  const shapes = {
    cube: {
      pts: [[-1,-1,-1],[ 1,-1,-1],[ 1, 1,-1],[-1, 1,-1],[-1,-1, 1],[ 1,-1, 1],[ 1, 1, 1],[-1, 1, 1]],
      edges: [[0,1],[1,2],[2,3],[3,0],[4,5],[5,6],[6,7],[7,4],[0,4],[1,5],[2,6],[3,7]],
    },
    tetrahedron: {
      pts: [[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],
      edges: [[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]],
    },
    octahedron: {
      pts: [[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]],
      edges: [[0,2],[0,3],[0,4],[0,5],[1,2],[1,3],[1,4],[1,5],[2,4],[2,5],[3,4],[3,5]],
    },
    dodecahedron: {
      pts: [
        [1,1,1],[1,1,-1],[1,-1,1],[1,-1,-1],[-1,1,1],[-1,1,-1],[-1,-1,1],[-1,-1,-1],
        [0,1/φ,φ],[0,1/φ,-φ],[0,-1/φ,φ],[0,-1/φ,-φ],
        [1/φ,φ,0],[1/φ,-φ,0],[-1/φ,φ,0],[-1/φ,-φ,0],
        [φ,0,1/φ],[φ,0,-1/φ],[-φ,0,1/φ],[-φ,0,-1/φ]
      ],
      edges: [[0,8],[0,12],[0,16],[1,9],[1,12],[1,17],[2,10],[2,13],[2,16],[3,11],[3,13],[3,17],[4,8],[4,14],[4,18],[5,9],[5,14],[5,19],[6,10],[6,15],[6,18],[7,11],[7,15],[7,19],[8,10],[9,11],[12,14],[13,15],[16,17],[18,19]],
    },
    icosahedron: {
      pts: [
        [0,1,φ],[0,1,-φ],[0,-1,φ],[0,-1,-φ],
        [1,φ,0],[1,-φ,0],[-1,φ,0],[-1,-φ,0],
        [φ,0,1],[φ,0,-1],[-φ,0,1],[-φ,0,-1]
      ],
      edges: [[0,2],[0,4],[0,6],[0,8],[0,10],[1,3],[1,4],[1,6],[1,9],[1,11],[2,5],[2,7],[2,8],[2,10],[3,5],[3,7],[3,9],[3,11],[4,6],[4,8],[4,9],[5,7],[5,8],[5,9],[6,10],[6,11],[7,10],[7,11],[8,9],[10,11]],
    },
  };
  if (shape === "prism") {
    const n = Math.max(3, param);
    const pts = [];
    const edges = [];
    for (let i = 0; i < n; i++) {
      const a = (i / n) * 2 * Math.PI;
      pts.push([Math.cos(a), Math.sin(a), -1]);
      pts.push([Math.cos(a), Math.sin(a),  1]);
    }
    for (let i = 0; i < n; i++) {
      edges.push([i*2, i*2+1]);                     // vertical
      edges.push([i*2, ((i+1)%n)*2]);               // top ring
      edges.push([i*2+1, ((i+1)%n)*2+1]);           // bottom ring
    }
    return project3D(pts, edges);
  }
  const s = shapes[shape];
  if (!s) return project3D([[0,0,0]], []);
  return project3D(s.pts, s.edges);
}

// ── Boolean lattice Bₙ (power set of {1..n}, ordered by inclusion) ─────
function buildBooleanLattice(n) {
  const total = 1 << n; // 2^n subsets
  const nodes = [];
  const edges = [];
  // Layout: levels = number of bits set (popcount)
  const byLevel = {};
  for (let mask = 0; mask < total; mask++) {
    const bits = mask.toString(2).split("").filter(b => b === "1").length;
    if (!byLevel[bits]) byLevel[bits] = [];
    byLevel[bits].push(mask);
  }
  const levels = n + 1;
  const W = Math.max(320, 90 * Math.max(...Object.values(byLevel).map(a => a.length)));
  const H = 80 + levels * 80;
  // Position nodes
  for (let level = 0; level < levels; level++) {
    const row = byLevel[level] ?? [];
    row.forEach((mask, i) => {
      const x = W / 2 + (i - (row.length - 1) / 2) * 80;
      const y = H - 40 - level * 80;
      // Label: {1,3} style
      const elems = [];
      for (let b = 0; b < n; b++) { if (mask & (1 << b)) elems.push(b + 1); }
      const lbl = elems.length === 0 ? "∅" : `{${elems.join(",")}}`;
      nodes.push({
        id: mask, level,
        x, y,
        label: lbl, shortLabel: lbl,
        order: elems.length + 1,
        index: 1, elements: elems.map(String), elementIndices: [mask],
        generators: [], generatorLabels: [], genAll: lbl,
        isCyclic: false, rank: 1, shape: "circle", multiGen: false, isNormal: false,
        viewType: "hasse",
      });
    });
  }
  // Edges: mask A → B if A ⊂ B and |B| = |A| + 1
  for (const nodeA of nodes) {
    for (const nodeB of nodes) {
      if (nodeB.level !== nodeA.level + 1) continue;
      if ((nodeA.id & nodeB.id) === nodeA.id) edges.push([nodeA.id, nodeB.id]);
    }
  }
  // Sort nodes array by id so indexing works
  nodes.sort((a, b) => a.id - b.id);
  // Remap edges to array indices
  const idToIdx = {};
  nodes.forEach((n, i) => { idToIdx[n.id] = i; });
  const indexedEdges = edges.map(([a, b]) => [idToIdx[a], idToIdx[b]]);
  nodes.forEach((node, i) => { node.id = i; }); // re-index by position
  const table = Array.from({ length: total }, (_, i) => Array.from({ length: total }, (_, j) => idToIdx[i | j] ?? 0));
  const labels = nodes.map(n => n.label);
  return { nodes, edges: indexedEdges, maxLevel: n, byLevel, W, H, nodeR: 26, kind: "Boolean", param: n, table, labels, viewType: "hasse" };
}

// ── Element-level Cayley spanning tree ──────────────────────────────
// Each node = one group element (like the element views).
// Edges = BFS tree from identity via generators, showing parent→child
// element relationships: e.g. e → a → a² → a³ for ℤ₄,
// or branching e → r, e → s for dihedral groups.
// Only works for groups with a meaningful generator set; falls back to
// the subgroup-level Hasse layout for groups where this isn't useful.
function buildElementTree(tableData, kind, param) {
  const { table, labels } = tableData;
  const order = table.length;

  // --- Find a minimal generator set for the whole group ---
  // Try generators of increasing size until we span the group
  function spansGroup(gens) {
    return getClosure(gens, table).size === order;
  }

  let genIndices = [];
  // Single generator first (cyclic)
  outer1: for (let i = 1; i < order; i++) {
    if (getClosure([i], table).size === order) { genIndices = [i]; break outer1; }
  }
  // If not cyclic, try pairs
  if (genIndices.length === 0) {
    outer2: for (let i = 1; i < order; i++)
      for (let j = i + 1; j < order; j++)
        if (spansGroup([i, j])) { genIndices = [i, j]; break outer2; }
  }
  // Fallback: first non-identity element plus its inverse
  if (genIndices.length === 0 && order > 1) genIndices = [1];

  // --- BFS from identity to build spanning tree ---
  const parent = new Array(order).fill(-1);   // parent[i] = index of parent element
  const depth  = new Array(order).fill(-1);
  const bfsOrder = [];
  depth[0] = 0;
  const queue = [0];
  while (queue.length) {
    const cur = queue.shift();
    bfsOrder.push(cur);
    for (const g of genIndices) {
      const child = table[cur][g];
      if (depth[child] === -1) {
        depth[child] = depth[cur] + 1;
        parent[child] = cur;
        queue.push(child);
      }
    }
  }

  const maxDepth = Math.max(...depth);

  // --- Tree layout: Reingold–Tilford-inspired (simple left-to-right BFS width) ---
  // Group nodes by depth level
  const byDepth = {};
  for (let i = 0; i < order; i++) {
    const d = depth[i] < 0 ? maxDepth : depth[i];
    (byDepth[d] = byDepth[d] || []).push(i);
  }

  const H_SPACING = 72, V_SPACING = 90;
  const maxInLevel = Math.max(...Object.values(byDepth).map(a => a.length));
  const W = Math.max(480, H_SPACING * (maxInLevel + 1));
  const H = Math.max(320, V_SPACING * (maxDepth + 1) + 80);
  const PAD_Y = 50;

  const posX = new Array(order);
  const posY = new Array(order);
  Object.entries(byDepth).forEach(([d, nodeNodes]) => {
    const count = nodeNodes.length;
    nodeNodes.forEach((idx, i) => {
      posX[idx] = W / 2 + (i - (count - 1) / 2) * H_SPACING;
      posY[idx] = PAD_Y + Number(d) * V_SPACING;
    });
  });

  // Build element-style node descriptors
  const colorByDepth = ["#16a34a","#0284c7","#7c3aed","#ea580c","#db2777","#ca8a04"];
  const nodes = labels.map((lbl, i) => ({
    id: i,
    label: lbl,
    shortLabel: lbl,
    order: elementOrder(i, table),
    index: 1,
    elements: [lbl],
    elementIndices: [i],
    generators: [],
    generatorLabels: [],
    genAll: lbl,
    isCyclic: true,
    rank: 1,
    shape: "circle",
    multiGen: false,
    isNormal: false,
    viewType: "tree",
    level: depth[i] < 0 ? maxDepth : depth[i],
    x: posX[i],
    y: posY[i],
    _depthColor: colorByDepth[(depth[i] < 0 ? maxDepth : depth[i]) % colorByDepth.length],
  }));

  // Edges = parent→child pairs in the BFS spanning tree
  const edges = [];
  for (let i = 1; i < order; i++) {
    if (parent[i] >= 0) edges.push([parent[i], i]);
  }

  const byLevel = {};
  Object.entries(byDepth).forEach(([d, arr]) => { byLevel[Number(d)] = arr; });

  return {
    nodes, edges,
    maxLevel: maxDepth,
    byLevel,
    W, H,
    nodeR: 26,
    kind, param, table, labels,
    viewType: "tree",
  };
}

// ── Zpx multiplication tree — Cayley spanning tree of (ℤ/pℤ)* ─────────
// Shows the multiplicative structure of the group: each node is a nonzero
// residue class, edges follow the minimal generator (a primitive root),
// forming a cycle 1 → g → g² → … → 1.
function buildZpxMultTree(p) {
  // Find all elements (not necessarily prime p — works for any n via tableFromUn)
  const { table, labels } = tableFromUn(p);
  return buildElementTree({ table, labels }, "Zpx", p);
}

// ── Modular flower — M_m: residue classes prime to m, orbit petals ────
// Each orbit under repeated multiplication by a primitive-ish generator
// becomes its own petal arc around a center hub.
// Hub = identity (1), petals arranged radially, nodes in each petal
// laid along an arc away from center.
function buildModularFlower(m) {
  if (m < 2) m = 2;
  // Compute U(m): elements coprime to m
  const elems = [];
  for (let i = 1; i < m; i++) {
    let g = i, mm = m;
    while (mm) { [g, mm] = [mm, g % mm]; }
    if (g === 1) elems.push(i);
  }
  const n = elems.length; // φ(m)
  if (n === 0) return buildSingleElement("∅");

  const idx = Object.fromEntries(elems.map((e, i) => [e, i]));

  // Cayley table under multiplication mod m
  const table = Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) => idx[(elems[i] * elems[j]) % m])
  );
  const labels = elems.map(String);

  // Find orbits: start from each generator, compute cyclic subgroup
  // Partition elements into orbits under the *action* of the group on itself
  // by multiplication — i.e. cyclic subgroups generated by each element.
  // We want distinct cyclic orbits: group elements by the subgroup they generate.
  const orbitOf = new Array(n).fill(-1);
  const orbits = []; // each orbit = array of element indices (in traversal order)

  // Always put identity (index 0, value 1) as its own "hub" (orbit -1)
  orbitOf[0] = -1; // hub special

  for (let start = 1; start < n; start++) {
    if (orbitOf[start] !== -1) continue;
    // Trace the cyclic subgroup generated by elems[start]
    const orbit = [];
    let cur = start;
    const visited = new Set();
    while (!visited.has(cur)) {
      visited.add(cur);
      orbit.push(cur);
      // next = cur * elems[start] mod m
      cur = table[cur][start];
    }
    const oid = orbits.length;
    orbit.forEach(i => { if (orbitOf[i] === -1) orbitOf[i] = oid; });
    orbits.push(orbit);
  }

  // Deduplicate orbits: two orbits that share the same set of elements are the same
  const seen = new Map();
  const uniqueOrbits = [];
  orbits.forEach(orb => {
    const key = [...orb].sort((a,b)=>a-b).join(',');
    if (!seen.has(key)) { seen.set(key, true); uniqueOrbits.push(orb); }
  });

  const numPetals = uniqueOrbits.length;
  const PETAL_INNER = 110;
  const PETAL_SPACING = 66;
  const NODE_R = 26;

  // Compute canvas size first so hub sits exactly at W/2, H/2 (epicenter lands on hub)
  const maxOrbitLen = Math.max(...uniqueOrbits.map(o => o.length), 1);
  const maxR = PETAL_INNER + (maxOrbitLen - 1) * PETAL_SPACING + NODE_R * 2;
  const W = Math.max(580, maxR * 2 + 120);
  const H = Math.max(520, maxR * 2 + 120);
  const CENTER_X = W / 2;
  const CENTER_Y = H / 2;

  const nodes = [];
  const edges = [];

  // Hub node = identity (element 1, index 0) — placed at canvas center
  nodes.push({
    id: 0,
    label: labels[0], shortLabel: labels[0],
    order: 1, index: 1,
    elements: [labels[0]], elementIndices: [0],
    generators: [], generatorLabels: [], genAll: labels[0],
    isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: true,
    viewType: "flower",
    x: CENTER_X, y: CENTER_Y,
    level: 0,
    _isHub: true,
  });

  // Layout petals radially
  uniqueOrbits.forEach((orb, pi) => {
    const angle = (2 * Math.PI * pi) / numPetals - Math.PI / 2;
    const cosA = Math.cos(angle), sinA = Math.sin(angle);

    orb.forEach((elemIdx, ni) => {
      const dist = PETAL_INNER + ni * PETAL_SPACING;
      const nx = CENTER_X + cosA * dist;
      const ny = CENTER_Y + sinA * dist;
      const nodeId = nodes.length;
      nodes.push({
        id: nodeId,
        label: labels[elemIdx], shortLabel: labels[elemIdx],
        order: (() => {
          let o = 1, cur = elemIdx;
          while (true) { cur = table[cur][elemIdx]; o++; if (cur === 0 || o > n + 1) break; }
          return o;
        })(),
        index: n,
        elements: [labels[elemIdx]], elementIndices: [elemIdx],
        generators: [], generatorLabels: [], genAll: labels[elemIdx],
        isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: false,
        viewType: "flower",
        x: nx, y: ny,
        level: ni + 1,
        _petalIdx: pi,
        _orbitPos: ni,
      });

      const prevId = ni === 0 ? 0 : nodeId - 1;
      edges.push([prevId, nodeId]);
    });
  });

  // Build byLevel
  const byLevel = {};
  nodes.forEach(nd => { (byLevel[nd.level] = byLevel[nd.level] || []).push(nd.id); });

  return {
    nodes, edges,
    maxLevel: Math.max(...nodes.map(n => n.level)),
    byLevel,
    W, H,
    nodeR: NODE_R,
    kind: "Modular", param: m, table, labels,
    viewType: "flower",
  };
}

// ── Binary tree of elements — left/right children by operation ────────
// Lays elements out as a complete binary tree rooted at identity.
// Level i: elements reachable in i generator applications.
// Left child = apply first generator, right child = apply inverse (or second gen).
function buildBinaryTree(tableData, kind, param) {
  const { table, labels } = tableData;
  const order = table.length;
  if (order === 0) return buildSingleElement("∅");

  // Find minimal generators
  let genIdx = [];
  for (let i = 1; i < order; i++) {
    if (getClosure([i], table).size === order) { genIdx = [i]; break; }
  }
  if (genIdx.length === 0) {
    for (let i = 1; i < order; i++)
      for (let j = i + 1; j < order; j++)
        if (getClosure([i, j], table).size === order) { genIdx = [i, j]; break; }
  }
  if (genIdx.length === 0) genIdx = [1];

  const g = genIdx[0];
  // Inverse of g
  let gInv = g;
  for (let i = 1; i < order; i++) { if (table[g][i] === 0) { gInv = i; break; } }
  const leftGen = g;
  const rightGen = genIdx[1] ?? gInv;

  // BFS to assign positions
  const visited = new Array(order).fill(false);
  const depth = new Array(order).fill(-1);
  const bfsQ = [0];
  const parent = new Array(order).fill(-1);
  const childSide = new Array(order).fill(0); // 0=root,1=left,2=right
  depth[0] = 0; visited[0] = true;

  while (bfsQ.length) {
    const cur = bfsQ.shift();
    for (const [side, gn] of [[1, leftGen], [2, rightGen]]) {
      const child = table[cur][gn];
      if (!visited[child]) {
        visited[child] = true;
        depth[child] = depth[cur] + 1;
        parent[child] = cur;
        childSide[child] = side;
        bfsQ.push(child);
      }
    }
  }

  const maxDepth = Math.max(...depth.filter(d => d >= 0));
  const H_SPACING = 64, V_SPACING = 88, PAD_Y = 50;
  const W = Math.max(480, H_SPACING * Math.pow(2, Math.min(maxDepth, 4)));
  const H = Math.max(320, PAD_Y * 2 + V_SPACING * maxDepth);

  // Compute x positions using tree layout (Reingold-Tilford approximation)
  const byDepth = {};
  for (let i = 0; i < order; i++) {
    const d = depth[i] < 0 ? maxDepth : depth[i];
    (byDepth[d] = byDepth[d] || []).push(i);
  }

  const posX = new Array(order);
  const posY = new Array(order);
  Object.entries(byDepth).forEach(([d, ids]) => {
    const count = ids.length;
    ids.forEach((idx, i) => {
      posX[idx] = W / 2 + (i - (count - 1) / 2) * H_SPACING;
      posY[idx] = PAD_Y + Number(d) * V_SPACING;
    });
  });

  const colorByDepth = ["#16a34a","#0284c7","#7c3aed","#ea580c","#db2777","#ca8a04","#0891b2","#65a30d"];
  const nodes = labels.map((lbl, i) => ({
    id: i, label: lbl, shortLabel: lbl,
    order: elementOrder(i, table), index: 1,
    elements: [lbl], elementIndices: [i],
    generators: [], generatorLabels: [], genAll: lbl,
    isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: false,
    viewType: "tree", level: depth[i] < 0 ? maxDepth : depth[i],
    x: posX[i], y: posY[i],
    _depthColor: colorByDepth[(depth[i] < 0 ? maxDepth : depth[i]) % colorByDepth.length],
  }));

  const edges = [];
  for (let i = 1; i < order; i++) {
    if (parent[i] >= 0) edges.push([parent[i], i]);
  }

  const byLevel = {};
  Object.entries(byDepth).forEach(([d, arr]) => { byLevel[Number(d)] = arr; });

  return { nodes, edges, maxLevel: maxDepth, byLevel, W, H, nodeR: 26, kind, param, table, labels, viewType: "tree" };
}

// ── Cycle graph — radial, petals that loop back to identity hub ────────
// Like the flower but edges form directed cycles: the last node in each
// orbit connects back to the hub (identity). Shared nodes (elements
// appearing in multiple orbits) get cross-edges between orbits.
function buildCycleGraph(n) {
  const { table, labels } = tableFromUn(n);
  const order = table.length;
  if (order === 0) return buildSingleElement("1");

  // Compute distinct cyclic subgroups (orbits under each generator)
  const seen = new Map();
  const orbits = [];
  for (let start = 1; start < order; start++) {
    const orbit = [];
    let cur = start;
    const vis = new Set();
    while (!vis.has(cur)) { vis.add(cur); orbit.push(cur); cur = table[cur][start]; }
    const key = [...orbit].sort((a,b)=>a-b).join(',');
    if (!seen.has(key)) { seen.set(key, orbit); orbits.push(orbit); }
  }

  const numPetals = orbits.length;
  const PETAL_INNER = 105;
  const PETAL_SPACING = 62;
  const NODE_R = 26;

  // Compute canvas size first so hub sits at W/2, H/2 (epicenter lands on hub)
  const maxOrbitLen2 = Math.max(...orbits.map(o => o.length), 1);
  const maxR = PETAL_INNER + (maxOrbitLen2 - 1) * PETAL_SPACING + NODE_R * 2;
  const W = Math.max(580, maxR * 2 + 120);
  const H = Math.max(520, maxR * 2 + 120);
  const CENTER_X = W / 2;
  const CENTER_Y = H / 2;

  const nodeMap = new Map(); // elemIdx → nodeId in nodes array
  const nodes = [];
  const edges = [];

  // Hub = identity at canvas center
  nodes.push({
    id: 0, label: labels[0], shortLabel: labels[0],
    order: 1, index: 1, elements: [labels[0]], elementIndices: [0],
    generators: [], generatorLabels: [], genAll: labels[0],
    isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: true,
    viewType: "flower", x: CENTER_X, y: CENTER_Y, level: 0, _isHub: true, _petalIdx: -1,
  });
  nodeMap.set(0, 0);

  orbits.forEach((orb, pi) => {
    const angle = (2 * Math.PI * pi) / numPetals - Math.PI / 2;
    const cosA = Math.cos(angle), sinA = Math.sin(angle);

    const orbitNodeNodes = [];
    orb.forEach((elemIdx, ni) => {
      let nodeId;
      if (nodeMap.has(elemIdx)) {
        nodeId = nodeMap.get(elemIdx);
      } else {
        const dist = PETAL_INNER + ni * PETAL_SPACING;
        nodeId = nodes.length;
        nodes.push({
          id: nodeId, label: labels[elemIdx], shortLabel: labels[elemIdx],
          order: elementOrder(elemIdx, table), index: order,
          elements: [labels[elemIdx]], elementIndices: [elemIdx],
          generators: [], generatorLabels: [], genAll: labels[elemIdx],
          isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: false,
          viewType: "flower", x: CENTER_X + cosA * dist, y: CENTER_Y + sinA * dist,
          level: ni + 1, _petalIdx: pi, _orbitPos: ni,
        });
        nodeMap.set(elemIdx, nodeId);
      }
      orbitNodeNodes.push(nodeId);
    });

    edges.push([0, orbitNodeNodes[0]]);
    for (let i = 0; i < orbitNodeNodes.length - 1; i++) edges.push([orbitNodeNodes[i], orbitNodeNodes[i+1]]);
    edges.push([orbitNodeNodes[orbitNodeNodes.length - 1], 0]);
  });

  const byLevel = {};
  nodes.forEach(nd => { (byLevel[nd.level] = byLevel[nd.level] || []).push(nd.id); });

  return { nodes, edges, maxLevel: Math.max(...nodes.map(nd => nd.level)), byLevel, W, H, nodeR: NODE_R, kind: "Zpx", param: n, table, labels, viewType: "flower" };
}

// ── Boolean binary fork tree — layered digraph 0..n levels ─────────────
// Each level l has 2^l nodes counted linearly 0..(2^l - 1).
// Node (l, p) forks to children (l+1, 2p) = "0-branch" and (l+1, 2p+1) = "1-branch".
// Labels show the binary path from root (e.g. "01" = right then left).
function buildBooleanTree(n) {
  const levels = n + 1;
  const V_GAP = 90, PAD_Y = 50, PAD_X = 40;
  // Width grows with bottom row: 2^n nodes
  const bottomCount = 1 << n;
  const H_GAP = Math.max(50, Math.min(90, 700 / Math.max(bottomCount, 1)));
  const W = Math.max(380, PAD_X * 2 + H_GAP * (bottomCount - 1));
  const H = PAD_Y * 2 + V_GAP * n;

  const colorByLevel = ["#16a34a","#0284c7","#7c3aed","#ea580c","#db2777","#ca8a04"];
  const nodes = [];
  const edges = [];
  const byLevel = {};

  // Build all nodes by level and position
  for (let lv = 0; lv < levels; lv++) {
    const count = 1 << lv; // 2^lv nodes at this level
    byLevel[lv] = [];
    for (let p = 0; p < count; p++) {
      const id = (1 << lv) + p - 1; // compact id: root=0, next row=1,2, then 3,4,5,6...
      const path = lv === 0 ? "ε" : p.toString(2).padStart(lv, "0"); // binary path string
      const x = W / 2 + (p - (count - 1) / 2) * H_GAP;
      const y = PAD_Y + lv * V_GAP;
      nodes.push({
        id, level: lv, x, y,
        label: path, shortLabel: path,
        order: lv + 1, index: 1,
        elements: [path], elementIndices: [id],
        generators: [], generatorLabels: [], genAll: path,
        isCyclic: lv === 0, rank: 1, shape: "circle", multiGen: false, isNormal: lv === 0,
        viewType: "tree",
        _depthColor: colorByLevel[lv % colorByLevel.length],
      });
      byLevel[lv].push(id);
    }
  }

  // Fork edges: node at (lv, p) → children (lv+1, 2p) and (lv+1, 2p+1)
  for (let lv = 0; lv < n; lv++) {
    const count = 1 << lv;
    for (let p = 0; p < count; p++) {
      const parentId = (1 << lv) + p - 1;
      const leftId  = (1 << (lv + 1)) + (2 * p)     - 1;
      const rightId = (1 << (lv + 1)) + (2 * p + 1) - 1;
      edges.push([parentId, leftId]);
      edges.push([parentId, rightId]);
    }
  }

  // Dummy table (Boolean ∨ operation mapped to node ids) 
  const total = nodes.length;
  const table = Array.from({ length: total }, (_, i) => Array.from({ length: total }, (_, j) => Math.max(i, j)));
  const labels = nodes.map(nd => nd.label);
  return { nodes, edges, maxLevel: n, byLevel, W, H, nodeR: 24, kind: "Boolean", param: n, table, labels, viewType: "tree" };
}

// ── Boolean grid — all 2ⁿ subsets in a square grid ────────────────────
// Arranged as a 2D grid where each row is a "level" (popcount),
// columns spread evenly. Nodes are connected to their cover relations.
function buildBooleanGrid(n) {
  const total = 1 << n;
  const cols = Math.ceil(Math.sqrt(total));
  const rows = Math.ceil(total / cols);
  const GAP = 80, PAD = 50;
  const W = PAD * 2 + (cols - 1) * GAP;
  const H = PAD * 2 + (rows - 1) * GAP;

  // Sort masks by popcount then value for a visually clean grid
  const sorted = Array.from({ length: total }, (_, i) => i)
    .sort((a, b) => {
      const pa = a.toString(2).split("").filter(x=>x==="1").length;
      const pb = b.toString(2).split("").filter(x=>x==="1").length;
      return pa !== pb ? pa - pb : a - b;
    });

  const idxOf = {};
  sorted.forEach((mask, i) => { idxOf[mask] = i; });

  const colorByLevel = ["#16a34a","#0284c7","#7c3aed","#ea580c","#db2777","#ca8a04"];
  const nodes = sorted.map((mask, i) => {
    const col = i % cols, row = Math.floor(i / cols);
    const bits = mask.toString(2).split("").filter(b=>b==="1").length;
    const elems = [];
    for (let b = 0; b < n; b++) if (mask & (1 << b)) elems.push(b + 1);
    const lbl = elems.length === 0 ? "∅" : `{${elems.join(",")}}`;
    return {
      id: i, level: bits,
      x: PAD + col * GAP, y: PAD + row * GAP,
      label: lbl, shortLabel: lbl,
      order: elems.length + 1, index: 1,
      elements: elems.map(String), elementIndices: [mask],
      generators: [], generatorLabels: [], genAll: lbl,
      isCyclic: false, rank: 1, shape: "circle", multiGen: false, isNormal: false,
      viewType: "elements",
      _depthColor: colorByLevel[bits % colorByLevel.length],
    };
  });

  // Cover edges: mask A covers B if B = A | (one bit) and |B| = |A| + 1
  const edges = [];
  for (let mask = 0; mask < total; mask++) {
    for (let b = 0; b < n; b++) {
      const child = mask | (1 << b);
      if (child !== mask) edges.push([idxOf[mask], idxOf[child]]);
    }
  }

  const byLevel = {};
  nodes.forEach(nd => { (byLevel[nd.level] = byLevel[nd.level] || []).push(nd.id); });
  const table = Array.from({ length: total }, (_, i) =>
    Array.from({ length: total }, (_, j) => idxOf[sorted[i] | sorted[j]] ?? 0));
  const labels = nodes.map(nd => nd.label);
  return { nodes, edges, maxLevel: n, byLevel, W, H, nodeR: 26, kind: "Boolean", param: n, table, labels, viewType: "elements" };
}

// ── Integer ring ℤₙ — circular arrangement ────────────────────────────
// Nodes 0..n-1 in a ring, edges connect consecutive integers.
// Colored by residue class (even/odd alternating for clarity).
function buildIntegerRing(n) {
  if (n < 2) n = 2;
  const R = Math.max(90, Math.min(200, 20 * n));
  const W = R * 2 + 120, H = R * 2 + 120;
  const cx = W / 2, cy = H / 2;
  const ORDER_COLS = ["#16a34a","#0284c7","#7c3aed","#db2777","#ea580c","#ca8a04","#be123c","#0891b2","#65a30d","#9333ea"];
  const nodes = Array.from({ length: n }, (_, i) => {
    const angle = (2 * Math.PI * i / n) - Math.PI / 2;
    return {
      id: i, level: 0,
      x: cx + R * Math.cos(angle),
      y: cy + R * Math.sin(angle),
      label: String(i), shortLabel: String(i),
      order: i === 0 ? 1 : n / gcd(i, n),
      index: 1, elements: [String(i)], elementIndices: [i],
      generators: [], generatorLabels: [], genAll: String(i),
      isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: true,
      viewType: "elements",
      _depthColor: ORDER_COLS[i % ORDER_COLS.length],
    };
  });
  const edges = Array.from({ length: n }, (_, i) => [i, (i + 1) % n]);
  const table = Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) => (i + j) % n));
  const labels = nodes.map(nd => nd.label);
  return { nodes, edges, maxLevel: 0, byLevel: { 0: nodes.map(nd => nd.id) }, W, H, nodeR: 26, kind: "IntRing", param: n, table, labels, viewType: "elements" };
}

// ── Linear chain 0 → 1 → … → n ────────────────────────────────────────
function buildLinearChain(n) {
  const GAP = 80, PAD = 50;
  const W = PAD * 2 + GAP * n;
  const H = 120;
  const cy = H / 2;
  const ORDER_COLS = ["#16a34a","#0284c7","#7c3aed","#db2777","#ea580c","#ca8a04","#be123c","#0891b2","#65a30d","#9333ea"];
  const nodes = Array.from({ length: n + 1 }, (_, i) => ({
    id: i, level: i,
    x: PAD + i * GAP, y: cy,
    label: String(i), shortLabel: String(i),
    order: i + 1, index: 1, elements: [String(i)], elementIndices: [i],
    generators: [], generatorLabels: [], genAll: String(i),
    isCyclic: i === 0, rank: 1, shape: "circle", multiGen: false, isNormal: i === 0,
    viewType: "elements",
    _depthColor: ORDER_COLS[i % ORDER_COLS.length],
  }));
  const edges = Array.from({ length: n }, (_, i) => [i, i + 1]);
  const total = n + 1;
  const table = Array.from({ length: total }, (_, i) =>
    Array.from({ length: total }, (_, j) => Math.min(i + j, n)));
  const labels = nodes.map(nd => nd.label);
  return { nodes, edges, maxLevel: n, byLevel: Object.fromEntries(nodes.map(nd => [nd.level, [nd.id]])), W, H, nodeR: 26, kind: "LinSeq", param: n, table, labels, viewType: "elements" };
}

// ── Factorization tree ──────────────────────────────────────────────────
// Root = n, children = prime factor decomposition level by level.
// Each composite node splits into its smallest prime factor p and n/p.
function buildFactorizationTree(n) {
  if (n < 2) n = 2;
  const ORDER_COLS = ["#16a34a","#0284c7","#7c3aed","#db2777","#ea580c","#ca8a04","#be123c","#0891b2","#65a30d","#9333ea"];

  // BFS: each node value splits into [smallestPrimeFactor, value/smallestPrimeFactor]
  // Stop when value is prime (leaf)
  function smallestPrime(x) {
    if (x < 2) return x;
    for (let i = 2; i * i <= x; i++) if (x % i === 0) return i;
    return x; // x is prime
  }
  function isPrime(x) { return x >= 2 && smallestPrime(x) === x; }

  const nodes = [];
  const edges = [];
  // nodeId → { value, level, pos }
  const queue = [{ value: n, level: 0, parentId: -1 }];
  const byLevel = {};
  const posAtLevel = {}; // level → count so far (for x positioning)

  while (queue.length) {
    const { value, level, parentId } = queue.shift();
    const id = nodes.length;
    if (!byLevel[level]) { byLevel[level] = []; posAtLevel[level] = 0; }
    const posInRow = posAtLevel[level]++;
    byLevel[level].push(id);

    nodes.push({
      id, level, value,
      x: 0, y: 0, // will be set after BFS
      label: String(value), shortLabel: String(value),
      order: value, index: 1, elements: [String(value)], elementIndices: [id],
      generators: [], generatorLabels: [], genAll: String(value),
      isCyclic: isPrime(value), rank: 1, shape: "circle", multiGen: false, isNormal: false,
      viewType: "tree",
      _depthColor: ORDER_COLS[level % ORDER_COLS.length],
      _isLeaf: isPrime(value) || value === 1,
    });

    if (parentId >= 0) edges.push([parentId, id]);

    if (!isPrime(value) && value > 1) {
      const p = smallestPrime(value);
      queue.push({ value: p,       level: level + 1, parentId: id });
      queue.push({ value: value/p, level: level + 1, parentId: id });
    }
  }

  // Now lay out positions
  const V_GAP = 90, H_GAP = 80, PAD = 50;
  const maxLevel = Math.max(...nodes.map(nd => nd.level));
  const H = PAD * 2 + V_GAP * maxLevel;
  const maxRowW = Math.max(...Object.values(byLevel).map(arr => arr.length));
  const W = Math.max(280, PAD * 2 + H_GAP * (maxRowW - 1));

  // Position by level row
  Object.entries(byLevel).forEach(([lv, ids]) => {
    const count = ids.length;
    ids.forEach((id, i) => {
      nodes[id].x = W / 2 + (i - (count - 1) / 2) * H_GAP;
      nodes[id].y = PAD + Number(lv) * V_GAP;
    });
  });

  const total = nodes.length;
  const table = Array.from({ length: total }, (_, i) => Array.from({ length: total }, (_, j) => Math.max(i, j)));
  const labels = nodes.map(nd => nd.label);
  return { nodes, edges, maxLevel, byLevel, W, H, nodeR: 26, kind: "FactTree", param: n, table, labels, viewType: "tree" };
}

// ═══════════════════════════════════════════════════════════════════════
//  MERMAID EXPORT
// ═══════════════════════════════════════════════════════════════════════

function generateMermaidFile(lattices, morphisms, notes = []) {
  let output = [];
  
  // ── Helpers ────────────────────────────────────────────────────────

  // ✅ FIXED: Include angle brackets < and > as unsafe
  const isUnsafe = (str) => /[[\]{}|"<>]/.test(str);
  const escapeQuotes = (str) => str.replace(/"/g, '""');
  
  const getLabelForMermaid = (label) => {
    if (!label) return 'e';
    const trimmed = label.trim();
    if (!trimmed) return 'e';
    if (isUnsafe(trimmed)) {
      return `"${escapeQuotes(trimmed)}"`;
    }
    return trimmed;
  };

  // Sanitize subgraph titles (remove characters that break Mermaid)
  const sanitizeSubgraphTitle = (title) => {
    if (!title) return 'Group';
    return title
      .replace(/[\[\]{}<>]/g, '')  // Remove brackets and braces
      .replace(/"/g, "'")           // Replace quotes with apostrophes
      .trim()
      .substring(0, 30) || 'Group';
  };

  const getSubgraphId = (label) => {
    if (!label) return 'G';
    return label
      .replace(/[₀₁₂₃₄₅₆₇₈₉]/g, '')
      .replace(/[^a-zA-Z0-9]/g, '_')
      .replace(/_+/g, '_')
      .replace(/^_|_$/g, '')
      .substring(0, 20) || 'G';
  };

  const nodeId = (latticeId, nodeId) => `N${latticeId}_${nodeId}`;

  const getNodeDef = (id, label, node) => {
    const safeLabel = getLabelForMermaid(label);
    if (node.order === 1) {
      return `${id}((${safeLabel}))`;
    } else if (node.isNormal) {
      return `${id}[${safeLabel}]`;
    } else if (node.shape === 'triangle') {
      return `${id}{{${safeLabel}}}`;
    } else {
      return `${id}((${safeLabel}))`;
    }
  };

  const orderClass = (order) => `order${order}`;

  const ORDER_COLS = [
    "#16a34a", "#0284c7", "#7c3aed", "#db2777", "#ea580c",
    "#ca8a04", "#be123c", "#0891b2", "#65a30d", "#9333ea"
  ];

  const getOrderColor = (order) => {
    const idx = (order - 1) % ORDER_COLS.length;
    return ORDER_COLS[idx];
  };

  // ─── HEADER ──────────────────────────────────────────────────────────
  output.push('%%{init: { "theme": "base", "themeVariables": { "primaryColor": "#B7D0DE", "primaryTextColor": "#0B151E", "primaryBorderColor": "#93b5c8", "lineColor": "#93b5c8", "tertiaryColor": "#F4F6F4", "fontFamily": "monospace" } } }%%');
  output.push('graph TB');
  output.push('');

  // ─── COLLECT ALL NODES FOR STYLING ────────────────────────────────
  const allNodes = new Map();

  // ─── GENERATE LATTICE SUBGRAPHS ────────────────────────────────────
  lattices.forEach((lattice) => {
    const base = lattice.base;
    if (!base || !base.nodes) return;

    const subgraphId = getSubgraphId(lattice.label || `G${lattice.id}`);
    const subgraphLabel = sanitizeSubgraphTitle(lattice.label || `Group ${lattice.id}`);
    
    output.push(`    subgraph ${subgraphId}["${subgraphLabel}"]`);

    base.nodes.forEach((node) => {
      const id = nodeId(lattice.id, node.id);
      const rawLabel = node.shortLabel || node.label || `n${node.id}`;
      const nodeDef = getNodeDef(id, rawLabel, node);
      
      allNodes.set(`${lattice.id}:${node.id}`, {
        id: id,
        label: rawLabel,
        isNormal: node.isNormal,
        order: node.order
      });

      output.push(`        ${nodeDef}`);
    });

    output.push(`    end`);
    output.push('');
  });

  // ─── GENERATE EDGES ─────────────────────────────────────────────────
  if (lattices.some(l => l.base?.edges?.length > 0)) {
    output.push('    %% Subgroup relationships');
    output.push('');
  }

  lattices.forEach((lattice) => {
    const base = lattice.base;
    if (!base || !base.edges) return;

    base.edges.forEach(([from, to]) => {
      const fromInfo = allNodes.get(`${lattice.id}:${from}`);
      const toInfo = allNodes.get(`${lattice.id}:${to}`);

      if (fromInfo && toInfo) {
        let style = '-->';
        if (fromInfo.isNormal && toInfo.isNormal) {
          style = '==>';
        } else if (fromInfo.isNormal || toInfo.isNormal) {
          style = '--o';
        }
        output.push(`    ${fromInfo.id} ${style} ${toInfo.id}`);
      }
    });
  });

  // ─── GENERATE MORPHISMS ────────────────────────────────────────────
  if (morphisms && morphisms.length > 0) {
    output.push('');
    output.push('    %% Morphisms');
    output.push('');

    morphisms.forEach((morphism) => {
      const morphName = getLabelForMermaid(morphism.name || 'phi');
      const seenPairs = new Set();
      
      morphism.strands.forEach((strand) => {
        const fromKey = `${strand.fromLatticeId}:${strand.fromNodeId}`;
        const toKey = `${strand.toLatticeId}:${strand.toNodeId}`;
        const pairKey = `${fromKey}->${toKey}`;
        
        if (seenPairs.has(pairKey)) return;
        seenPairs.add(pairKey);
        
        const fromInfo = allNodes.get(fromKey);
        const toInfo = allNodes.get(toKey);

        if (fromInfo && toInfo) {
          const safeLabel = getLabelForMermaid(morphName);
          output.push(`    ${fromInfo.id} -. "${safeLabel}" .-> ${toInfo.id}`);
        }
      });
    });
  }

  // ─── STYLING CLASSES ───────────────────────────────────────────────
  output.push('');
  output.push('    %% Node styling by order');
  
  const orders = new Set();
  for (const [key, info] of allNodes) {
    orders.add(info.order);
  }
  
  for (const order of orders) {
    const color = getOrderColor(order);
    const className = orderClass(order);
    output.push(`    classDef ${className} fill:${color},stroke:${color},color:#fff,stroke-width:1.5px;`);
  }
  
  for (const [key, info] of allNodes) {
    const className = orderClass(info.order);
    output.push(`    class ${info.id} ${className};`);
  }

  // ─── SPECIAL OVERRIDES ─────────────────────────────────────────────
  output.push('');
  output.push('    %% Special overrides');
  output.push('    classDef identity fill:#fbbf24,stroke:#ca8a04,color:#0B151E,stroke-width:2px;');
  output.push('    classDef normal fill:#4ade80,stroke:#16a34a,color:#0B151E,stroke-width:2px;');

  for (const [key, info] of allNodes) {
    if (info.order === 1) {
      output.push(`    class ${info.id} identity;`);
    } else if (info.isNormal) {
      output.push(`    class ${info.id} normal;`);
    }
  }

  // ─── LEGEND AND REFERENCE SECTION ──────────────────────────────────
  output.push('');
  output.push('    %% ============================================');
  output.push('    %% LEGEND AND REFERENCE');
  output.push('    %% ============================================');
  output.push('');

  // ---- Shape Key (only elements that appear) ----
  output.push('    subgraph Key["Shape Key"]');
  
  let hasIdentity = false;
  let hasNormal = false;
  let hasTriangle = false;
  let hasStandard = false;
  let hasBothNormal = false;
  let hasOneNormal = false;
  let hasMorphism = false;

  for (const [key, info] of allNodes) {
    if (info.order === 1) hasIdentity = true;
    if (info.isNormal) hasNormal = true;
  }

  for (const lattice of lattices) {
    if (lattice.base?.nodes?.some(n => n.shape === 'triangle')) {
      hasTriangle = true;
    }
    if (lattice.base?.nodes?.some(n => n.shape !== 'triangle' && n.order !== 1 && !n.isNormal)) {
      hasStandard = true;
    }
  }

  for (const lattice of lattices) {
    if (lattice.base?.edges) {
      for (const [from, to] of lattice.base.edges) {
        const fromInfo = allNodes.get(`${lattice.id}:${from}`);
        const toInfo = allNodes.get(`${lattice.id}:${to}`);
        if (fromInfo && toInfo) {
          if (fromInfo.isNormal && toInfo.isNormal) hasBothNormal = true;
          else if (fromInfo.isNormal || toInfo.isNormal) hasOneNormal = true;
        }
      }
    }
  }

  if (morphisms && morphisms.length > 0) hasMorphism = true;

  let keyEntries = [];
  if (hasIdentity) keyEntries.push('        L1(("e")) --> L1_label["Identity element"]');
  if (hasNormal) keyEntries.push('        L2["Normal"] --> L2_label["Normal subgroup (square)"]');
  if (hasTriangle) keyEntries.push('        L3{{"TriGen"}} --> L3_label["3-generator subgroup (diamond)"]');
  if (hasStandard) keyEntries.push('        L4(("Circle")) --> L4_label["Standard subgroup (circle)"]');
  if (hasBothNormal) keyEntries.push('        L5 ==o L5_label["Both normal (thick edge)"]');
  if (hasOneNormal) keyEntries.push('        L6 --o L6_label["One normal (circle tail)"]');
  if (hasMorphism) keyEntries.push('        L7 -. "phi" .-> L7_label["Morphism (dashed)"]');

  if (keyEntries.length === 0) {
    output.push('        KeyEmpty["No elements to display"]');
  } else {
    keyEntries.forEach(entry => output.push(entry));
  }

  for (let i = 1; i <= 7; i++) {
    output.push(`        style L${i}_label fill:transparent,stroke:none,color:#0B151E;`);
  }

  output.push('    end');
  output.push('');

  // ---- Graph Reference ----
  const graphsWithDesc = lattices.filter(l => l.description);
  if (graphsWithDesc.length > 0) {
    output.push('    subgraph GraphRef["Graph Reference"]');
    graphsWithDesc.forEach((lattice) => {
      const refId = `graph_${lattice.id}`;
      const safeLabel = getLabelForMermaid(lattice.label || `Group ${lattice.id}`);
      const safeDesc = getLabelForMermaid(lattice.description);
      output.push(`        ${refId}["${safeLabel}: ${safeDesc}"]`);
      output.push(`        style ${refId} fill:#f4f6f4,stroke:#93b5c8,stroke-dasharray:3 3,color:#0B151E,font-size:10px;`);
    });
    output.push('    end');
    output.push('');
  }

  // ---- Morphism Reference ----
  const morphsWithDesc = morphisms.filter(m => m.description);
  if (morphsWithDesc.length > 0) {
    output.push('    subgraph MorphRef["Morphism Reference"]');
    morphsWithDesc.forEach((morphism) => {
      const refId = `morph_${morphism.id}`;
      const safeName = getLabelForMermaid(morphism.name || 'phi');
      const safeDesc = getLabelForMermaid(morphism.description);
      output.push(`        ${refId}["${safeName}: ${safeDesc}"]`);
      output.push(`        style ${refId} fill:#e8f0fe,stroke:#6a9ab5,stroke-dasharray:2 2,color:#0B151E,font-size:10px;`);
    });
    output.push('    end');
    output.push('');
  }

  // ---- Canvas Notes Reference ----
  if (notes && notes.length > 0) {
    const nonEmptyNotes = notes.filter(n => n.text && n.text.trim().length > 0);
    if (nonEmptyNotes.length > 0) {
      output.push('    subgraph NoteRef["Canvas Notes"]');
      nonEmptyNotes.forEach((note, idx) => {
        const refId = `note_${idx}`;
        const safeNote = getLabelForMermaid(note.text.substring(0, 60));
        output.push(`        ${refId}["${safeNote}"]`);
        output.push(`        style ${refId} fill:#fff9e6,stroke:#ca8a04,stroke-dasharray:4 2,color:#0B151E;`);
      });
      output.push('    end');
      output.push('');
    }
  }

  // ─── FINAL ──────────────────────────────────────────────────────────
  return output.join('\n');
}
// ═══════════════════════════════════════════════════════════════════════
//  LATTICE_CATEGORIES
// ═══════════════════════════════════════════════════════════════════════

const LATTICE_CATEGORIES = [
  {
    key: "cyclic",
    label: "Cyclic",
    desc: "Cyclic and direct-product cyclic groups",
    groups: [
      {
        key: "Zn", label: "ℤₙ", desc: "Cyclic group of order n",
        hasParam: true, paramLabel: "n", paramDefault: 6, paramMin: 2, paramMax: 60,
        views: [
          { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromCyclic(n), "Zn", n) },
          { key: "tree",     label: "Tree",     build: n => buildElementTree(tableFromCyclic(n), "Zn", n) },
          { key: "binary",   label: "Binary",   build: n => buildBinaryTree(tableFromCyclic(n), "Zn", n) },
          { key: "elements", label: "Ring",     build: n => elementRingCyclic(n) },
        ],
      },
      {
        key: "ZnxZm", label: "ℤₙ×ℤₘ", desc: "Direct product of two cyclic groups",
        hasParam: true, paramLabel: "n", paramDefault: 4, paramMin: 2, paramMax: 8,
        hasParam2: true, paramLabel2: "m", paramDefault2: 3, paramMin2: 2, paramMax2: 8,
        views: [
          { key: "hasse",    label: "Hasse",    build: (n, m) => buildLatticeFromTable(tableFromDirectProduct(tableFromCyclic(n), tableFromCyclic(m ?? 2)), "ZnxZm", n) },
          { key: "tree",     label: "Tree",     build: (n, m) => buildElementTree(tableFromDirectProduct(tableFromCyclic(n), tableFromCyclic(m ?? 2)), "ZnxZm", n) },
          { key: "elements", label: "Grid",     build: (n, m) => elementGridZnZm(n, m ?? 2) },
        ],
      },
      {
        key: "ZnZmZk", label: "ℤₙ×ℤₘ×ℤₖ", desc: "Triple direct product of cyclic groups",
        hasParam: true,  paramLabel: "n",  paramDefault: 2, paramMin: 2, paramMax: 6,
        hasParam2: true, paramLabel2: "m", paramDefault2: 2, paramMin2: 2, paramMax2: 6,
        hasParam3: true, paramLabel3: "k", paramDefault3: 2, paramMin3: 2, paramMax3: 6,
        views: [
          { key: "hasse",    label: "Hasse",    build: (n, m, k) => buildLatticeFromTable(tableFromTripleProduct(n, m ?? 2, k ?? 2), "ZnZmZk", n) },
          { key: "tree",     label: "Tree",     build: (n, m, k) => buildElementTree(tableFromTripleProduct(n, m ?? 2, k ?? 2), "ZnZmZk", n) },
          { key: "elements", label: "Grid",     build: (n, m, k) => elementGridZnZmZk(n, m ?? 2, k ?? 2) },
        ],
      },
    ],
  },
  {
    key: "boolean",
    label: "Boolean",
    desc: "Power-set lattices Bₙ ordered by subset inclusion",
    groups: [
      {
        key: "Boolean", label: "Bₙ", desc: "Boolean lattice — all 2ⁿ subsets of {1…n} ordered by ⊆. B₁≅ℤ₂, B₂≅ℤ₂², B₃ has 8 nodes.",
        hasParam: true, paramLabel: "n", paramDefault: 3, paramMin: 1, paramMax: 5,
        views: [
          { key: "hasse",    label: "Hasse",    build: n => buildBooleanLattice(n) },
          { key: "tree",     label: "Tree",     build: n => buildBooleanTree(n) },
          { key: "grid",     label: "Grid",     build: n => buildBooleanGrid(n) },
        ],
      },
    ],
  },
  {
    key: "dihedral",
    label: "Dihedral & Symmetric",
    desc: "Symmetry groups of polygons and permutations",
    groups: [
      {
        key: "Dihedral", label: "Dₙ", desc: "Dihedral group of order 2n — symmetries of a regular n-gon",
        hasParam: true, paramLabel: "n", paramDefault: 4, paramMin: 2, paramMax: 12,
        views: [
          { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromDihedral(n), "Dihedral", n) },
          { key: "tree",     label: "Tree",     build: n => buildElementTree(tableFromDihedral(n), "Dihedral", n) },
          { key: "elements", label: "Rings",    build: n => elementRingDihedral(n) },
          { key: "cayley",   label: "Cayley",   build: n => cayleyDihedral(n) },
        ],
      },
      {
        key: "Symmetric", label: "Sₙ", desc: "Symmetric group — all permutations on n letters",
        hasParam: true, paramLabel: "n", paramDefault: 3, paramMin: 2, paramMax: 4,
        views: [
          { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromSymmetric(n), "Symmetric", n) },
          { key: "tree",     label: "Tree",     build: n => buildElementTree(tableFromSymmetric(n), "Symmetric", n) },
          { key: "elements", label: "Grid",     build: n => elementGridSymmetric(n) },
        ],
      },
      {
        key: "Alternating", label: "Aₙ", desc: "Alternating group — even permutations on n letters (index-2 subgroup of Sₙ)",
        hasParam: true, paramLabel: "n", paramDefault: 4, paramMin: 3, paramMax: 5,
        views: [
          { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromAlternating(n), "Alternating", n) },
          { key: "tree",     label: "Tree",     build: n => buildElementTree(tableFromAlternating(n), "Alternating", n) },
          { key: "elements", label: "Grid",     build: n => elementGridAlternating(n) },
        ],
      },
    ],
  },
  {
    key: "quaternion",
    label: "Quaternion Family",
    desc: "Quaternion and dicyclic groups",
    groups: [
      {
        key: "Q4n", label: "Q₄ₙ", desc: "Generalized quaternion group of order 4n. Presentation: ⟨x,y | x²ⁿ=e, y²=xⁿ, yxy⁻¹=x⁻¹⟩. Q₈ is n=2; Q₁₂ is n=3.",
        hasParam: true, paramLabel: "n", paramDefault: 2, paramMin: 2, paramMax: 12,
        views: [
          { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromQ4n(n), "Q4n", n) },
          { key: "tree",     label: "Tree",     build: n => buildElementTree(tableFromQ4n(n), "Q4n", n) },
          { key: "elements", label: "Rings",    build: n => elementRingQ4n(n) },
        ],
      },
    ],
  },
  {
    key: "modular",
    label: "Modular",
    desc: "Multiplicative groups mod n — units, subgroup lattices, orbit flowers and cycle graphs",
    groups: [
      {
        key: "Zpx", label: "ℤₙ*", desc: "Multiplicative group mod n: units coprime to n. Hasse shows subgroup lattice; Tree is a Cayley spanning tree; Ring shows elements radially; Flower groups elements into cyclic orbit petals; Cycle is a radial loop graph where each orbit closes back to 1.",
        hasParam: true, paramLabel: "n", paramDefault: 12, paramMin: 2, paramMax: 120,
        views: [
          { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromUn(n), "Un", n) },
          { key: "tree",     label: "Tree",     build: n => buildZpxMultTree(n) },
          { key: "elements", label: "Ring",     build: n => elementRingUn(n) },
          { key: "flower",   label: "Flower",   build: n => buildModularFlower(n) },
          { key: "cycle",    label: "Cycle",    build: n => buildCycleGraph(n) },
        ],
      },
    ],
  },
  {
    key: "geometry",
    label: "Geometry",
    desc: "3D shape projections with selectable symmetry nodes",
    groups: [
      {
        key: "Cube", label: "Cube", desc: "8 vertices of a cube — Oh symmetry projection",
        hasParam: false, paramDefault: null,
        views: [{ key: "shape", label: "Projection", build: () => buildShapeProjection("cube") }],
      },
      {
        key: "Tetrahedron", label: "Tetrahedron", desc: "4 vertices of a regular tetrahedron — Td symmetry",
        hasParam: false, paramDefault: null,
        views: [{ key: "shape", label: "Projection", build: () => buildShapeProjection("tetrahedron") }],
      },
      {
        key: "Octahedron", label: "Octahedron", desc: "6 vertices of a regular octahedron",
        hasParam: false, paramDefault: null,
        views: [{ key: "shape", label: "Projection", build: () => buildShapeProjection("octahedron") }],
      },
      {
        key: "Dodecahedron", label: "Dodecahedron", desc: "20 vertices of a regular dodecahedron",
        hasParam: false, paramDefault: null,
        views: [{ key: "shape", label: "Projection", build: () => buildShapeProjection("dodecahedron") }],
      },
      {
        key: "Icosahedron", label: "Icosahedron", desc: "12 vertices of a regular icosahedron",
        hasParam: false, paramDefault: null,
        views: [{ key: "shape", label: "Projection", build: () => buildShapeProjection("icosahedron") }],
      },
      {
        key: "Prism", label: "Prism (n)", desc: "2n vertices of a regular n-prism",
        hasParam: true, paramLabel: "n", paramDefault: 5, paramMin: 3, paramMax: 12,
        views: [{ key: "shape", label: "Projection", build: n => buildShapeProjection("prism", n) }],
      },
    ],
  },
  {
    key: "custom",
    label: "Custom",
    desc: "User-defined groups",
    groups: [
      {
        key: "Single", label: "Element", desc: "Place a single labelled element node — useful for annotations, diagrams, or placeholders.",
        hasParam: false, paramDefault: null, isSingle: true,
        views: [
          { key: "elements", label: "Node", build: (_, label) => buildSingleElement(label) },
        ],
      },
      {
        key: "IntRing", label: "ℤₙ Ring", desc: "Integers mod n as a ring: nodes 0..n-1 arranged in a circle, edges show additive structure.",
        hasParam: true, paramLabel: "n", paramDefault: 8, paramMin: 2, paramMax: 48,
        views: [
          { key: "ring", label: "Ring", build: n => buildIntegerRing(n) },
        ],
      },
      {
        key: "LinSeq", label: "Linear", desc: "Linear sequence 0 → 1 → 2 → … → n, useful as a number line or chain diagram.",
        hasParam: true, paramLabel: "n", paramDefault: 8, paramMin: 1, paramMax: 30,
        views: [
          { key: "chain", label: "Chain", build: n => buildLinearChain(n) },
        ],
      },
      {
        key: "FactTree", label: "Factor Tree", desc: "Divisibility tree for a chosen number: root = n, children = prime factors, branching shows factorization. Select a value to explore.",
        hasParam: true, paramLabel: "n", paramDefault: 12, paramMin: 2, paramMax: 120,
        views: [
          { key: "tree", label: "Tree", build: n => buildFactorizationTree(n) },
        ],
      },
      {
        key: "Raw", label: "Raw Table", desc: "Paste a custom Cayley table as JSON",
        hasParam: false, paramDefault: null, isRaw: true,
        views: [
          { key: "hasse", label: "Hasse", build: (_, rawData) => {
            if (!rawData) throw new Error("No table provided");
            return buildLatticeFromTable(tableFromRaw(rawData.table, rawData.labels), "Raw", rawData.table.length);
          }},
        ],
      },
    ],
  },
];

// Flat list of all groups (for param state init, legacy lookups)
const LATTICE_GROUPS = LATTICE_CATEGORIES.flatMap(c => c.groups);

// Flat catalog for legacy lookups (params init etc.)
const LATTICE_CATALOG = LATTICE_GROUPS;

// ═══════════════════════════════════════════════════════════════════════
//  MORPHISM ANALYSIS  (generalized — uses table indices from nodes)
// ═══════════════════════════════════════════════════════════════════════

function analyzeMorphism(strands, lattices, latticeViews) {
  if (!strands.length) return { isHomo: null, isInjective: null, isSurjective: null, kernel: [], image: [], strandLabels: [] };

  const strandLabels = strands.map(s => {
    const srcLV = latticeViews.find(lv => lv.entry.id === s.fromLatticeId);
    const tgtLV = latticeViews.find(lv => lv.entry.id === s.toLatticeId);
    const srcN = srcLV?.nodes.find(n => n.id === s.fromNodeId);
    const tgtN = tgtLV?.nodes.find(n => n.id === s.toNodeId);
    return {
      from: srcN ? `${srcN.shortLabel} ⊆ ${srcLV.entry.label}` : "?",
      to:   tgtN ? `${tgtN.shortLabel} ⊆ ${tgtLV.entry.label}` : "?",
      fromOrder: srcN?.order ?? 0,
      toOrder:   tgtN?.order ?? 0,
    };
  });

  // Build element-level map: source label → target label
  const elementMap = new Map();
  for (const s of strands) {
    const srcLV = latticeViews.find(lv => lv.entry.id === s.fromLatticeId);
    const tgtLV = latticeViews.find(lv => lv.entry.id === s.toLatticeId);
    if (!srcLV || !tgtLV) continue;
    const srcNode = srcLV.nodes.find(n => n.id === s.fromNodeId);
    const tgtNode = tgtLV.nodes.find(n => n.id === s.toNodeId);
    if (!srcNode || !tgtNode) continue;
    srcNode.elementIndices?.forEach((srcIdx, pos) => {
      const tgtIdx = tgtNode.elementIndices?.[pos % (tgtNode.elementIndices?.length ?? 1)];
      if (srcIdx != null && tgtIdx != null) {
        const k = `${s.fromLatticeId}:${srcIdx}`;
        if (!elementMap.has(k)) elementMap.set(k, { latticeId: s.toLatticeId, idx: tgtIdx, lbl: tgtLV.entry.base?.labels?.[tgtIdx] ?? String(tgtIdx) });
      }
    });
  }

  if (!elementMap.size) return { isHomo: null, isInjective: null, isSurjective: null, kernel: [], image: [], strandLabels };

  // Homomorphism check using Cayley tables
  const srcNodes = [...new Set(strands.map(s => s.fromLatticeId))];
  const tgtNodes = [...new Set(strands.map(s => s.toLatticeId))];
  let isHomo = null;

  if (srcNodes.length === 1 && tgtNodes.length === 1) {
    const srcEntry = lattices.find(l => l.id === srcNodes[0]);
    const tgtEntry = lattices.find(l => l.id === tgtNodes[0]);
    const tG = srcEntry?.base?.table;
    const tH = tgtEntry?.base?.table;

    if (tG && tH) {
      isHomo = true;
      outer: for (const [ka, va] of elementMap) {
        const a = parseInt(ka.split(":")[1]);
        for (const [kb, vb] of elementMap) {
          const b = parseInt(kb.split(":")[1]);
          const ab = tG[a]?.[b];
          if (ab == null) continue;
          const fabEntry = elementMap.get(`${srcNodes[0]}:${ab}`);
          if (!fabEntry) continue;
          const fafb = tH[va.idx]?.[vb.idx];
          if (fafb == null || fabEntry.idx !== fafb) { isHomo = false; break outer; }
        }
      }
    }
  }

  // Kernel: source elements mapping to identity (idx 0) in target
  const kernel = [...elementMap.entries()]
    .filter(([, v]) => v.idx === 0)
    .map(([k]) => {
      const [lid, idx] = k.split(":").map(Number);
      const lv = latticeViews.find(lv => lv.entry.id === lid);
      return lv?.entry.base?.labels?.[idx] ?? String(idx);
    });

  // Image: distinct target element labels reached
  const image = [...new Set([...elementMap.values()].map(v => v.lbl))];

  // Injectivity
  const seen = new Set();
  let isInjective = true;
  for (const v of elementMap.values()) {
    const key = `${v.latticeId}:${v.idx}`;
    if (seen.has(key)) { isInjective = false; break; }
    seen.add(key);
  }

  // Surjectivity
  const tgtElems = new Set();
  for (const s of strands) {
    const tgtLV = latticeViews.find(lv => lv.entry.id === s.toLatticeId);
    tgtLV?.nodes.find(n => n.id === s.toNodeId)?.elementIndices?.forEach(i => tgtElems.add(i));
  }
  const imageIdxSet = new Set([...elementMap.values()].map(v => v.idx));
  const isSurjective = tgtElems.size > 0 && [...tgtElems].every(e => imageIdxSet.has(e));

  return { isHomo, isInjective, isSurjective, kernel, image, strandLabels };
}

// ═══════════════════════════════════════════════════════════════════════
//  COLOR SYSTEM  (unchanged)
// ═══════════════════════════════════════════════════════════════════════

const ORDER_COLS = ["#16a34a","#0284c7","#7c3aed","#db2777","#ea580c","#ca8a04","#be123c","#0891b2","#65a30d","#9333ea"];
const LATTICE_ACCENTS = ["#0284c7","#16a34a","#7c3aed","#ea580c","#db2777","#ca8a04"];

function buildOrderColorMap(nodes) {
  const orders = [...new Set(nodes.map(n => n.order))].sort((a, b) => a - b);
  const map = {};
  orders.forEach((o, i) => { map[o] = ORDER_COLS[i % ORDER_COLS.length]; });
  return map;
}
function orderColor(order, colorMap) { return colorMap[order] ?? "#9aaa88"; }

const MORPHISM_COLORS = ["#f59e0b","#10b981","#ef4444","#8b5cf6","#06b6d4","#f97316","#ec4899","#84cc16"];

// ═══════════════════════════════════════════════════════════════════════
//  PALETTE  (unchanged)
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
//  SHARED UI COMPONENTS  (unchanged)
// ═══════════════════════════════════════════════════════════════════════

function HPSplitter({ onDrag, containerRef }) {
  const dragging = useRef(false);
  const startY = useRef(0);
  const onMouseDown = (e) => {
    e.preventDefault(); dragging.current = true; startY.current = e.clientY;
    document.body.style.cursor = "row-resize"; document.body.style.userSelect = "none";
  };
  useEffect(() => {
    const onMove = (e) => {
      if (!dragging.current) return;
      const delta = e.clientY - startY.current;
      startY.current = e.clientY;
      // Get the actual container height so flex delta maps 1:1 with pixels
      const h = containerRef?.current?.getBoundingClientRect().height ?? 600;
      onDrag(delta, h);
    };
    const onUp = () => { if (dragging.current) { dragging.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; } };
    window.addEventListener("mousemove", onMove); window.addEventListener("mouseup", onUp);
    return () => { window.removeEventListener("mousemove", onMove); window.removeEventListener("mouseup", onUp); };
  }, [onDrag, containerRef]);
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

function Pane({ title, children, flex, open, onToggle, scrollClass = "" }) {
  return (
    <div style={{
      display: "flex", flexDirection: "column",
      flex: open ? (flex ?? 1) : "0 0 auto",
      minHeight: 0, overflow: "hidden", flexShrink: open ? 1 : 0,
    }}>
      {/* Pane header — always visible */}
      <div onClick={onToggle} style={{
        padding: "9px 14px", background: C.paneHeader,
        borderBottom: `1px solid ${C.border}`, borderTop: `1px solid ${C.border}`,
        flexShrink: 0, cursor: "pointer", userSelect: "none",
        display: "flex", alignItems: "center", justifyContent: "space-between",
        transition: "background 0.13s",
      }}
        onMouseEnter={e => e.currentTarget.style.background = C.borderHover}
        onMouseLeave={e => e.currentTarget.style.background = C.paneHeader}>
        <span style={{ fontSize: 9, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase" }}>{title}</span>
        <span style={{ fontSize: 8, color: C.inkFaint, flexShrink: 0, transition: "transform 0.18s", display: "inline-block", transform: open ? "rotate(180deg)" : "rotate(0deg)" }}>▼</span>
      </div>
      {open && (
        <div className={`sky-scroll ${scrollClass}`} style={{ flex: 1, overflowY: "auto", padding: "12px 14px 32px", minHeight: 0 }}>
          {children}
        </div>
      )}
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

const SECTION_DEPTH_STYLES = [
  { bg: "#9fbece", bgHover: "#93b5c8", fontSize: 9,  letterSpacing: 3,   fontWeight: "700", paddingY: 7 },
  { bg: "#adc8d8", bgHover: "#a0bece", fontSize: 9,  letterSpacing: 2.5, fontWeight: "600", paddingY: 6 },
  { bg: "#b8d2e0", bgHover: "#adc8d8", fontSize: 8,  letterSpacing: 2,   fontWeight: "500", paddingY: 5 },
];

function Section({ label, badge, accent, defaultOpen = true, depth = 0, children, rightExtra }) {
  const [open, setOpen] = useState(defaultOpen);
  const [hovered, setHovered] = useState(false);
  const ds = SECTION_DEPTH_STYLES[Math.min(depth, 2)];
  return (
    <div style={{ width: "100%" }}>
      <div
        onClick={() => setOpen(o => !o)}
        onMouseEnter={() => setHovered(true)}
        onMouseLeave={() => setHovered(false)}
        style={{
          display: "flex", alignItems: "center",
          padding: `${ds.paddingY}px 10px`, background: ds.bg,
          borderLeft: accent ? `3px solid ${accent}` : `3px solid transparent`,
          borderBottom: `1px solid ${C.border}`,
          cursor: "pointer", userSelect: "none",
          transition: "background 0.13s", gap: 7,
        }}
        onMouseOver={e => e.currentTarget.style.background = ds.bgHover}
        onMouseOut={e => e.currentTarget.style.background = ds.bg}>
        <span style={{
          flex: 1, fontSize: ds.fontSize, letterSpacing: ds.letterSpacing,
          textTransform: "uppercase", fontWeight: ds.fontWeight,
          color: C.inkMid, fontFamily: "'Courier New', monospace",
          minWidth: 0, overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap",
        }}>{label}</span>
        {/* rightExtra — always visible */}
        {rightExtra && (
          <div style={{ display: "flex", alignItems: "center", gap: 4, flexShrink: 0 }}
            onClick={e => e.stopPropagation()}>
            {rightExtra}
          </div>
        )}
        {badge !== undefined && (
          <span style={{
            fontSize: 8, color: C.inkFaint, background: C.panelBg,
            border: `1px solid ${C.border}`, borderRadius: 3, padding: "1px 5px",
            fontFamily: "'Courier New', monospace", letterSpacing: 0.5, flexShrink: 0,
          }}>{badge}</span>
        )}
        <span style={{ fontSize: 8, color: C.inkFaint, flexShrink: 0, transition: "transform 0.18s", transform: open ? "rotate(180deg)" : "rotate(0deg)", display: "inline-block", lineHeight: 1 }}>▼</span>
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

function SectionToggle({ label, checked, onChange }) {
  return (
    <div style={{ display: "flex", alignItems: "center", justifyContent: "space-between", padding: "6px 12px", borderBottom: `1px solid ${C.border}` }}>
      <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 2, textTransform: "uppercase" }}>{label}</span>
      <label style={{ display: "flex", alignItems: "center", gap: 6, cursor: "pointer" }}>
        <input type="checkbox" checked={checked} onChange={e => onChange(e.target.checked)} style={{ accentColor: C.inkMid, cursor: "pointer" }} />
        <span style={{ fontSize: 9, color: checked ? C.inkMid : C.inkFaint, letterSpacing: 1 }}>{checked ? "ON" : "OFF"}</span>
      </label>
    </div>
  );
}

function SubgroupRow({ node, colorMap, isSelected, onToggle }) {
  const col = node._customColor ?? orderColor(node.order, colorMap);
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
        <div style={{ fontSize: 8, color: C.inkFaint, textTransform: "uppercase" }}>
          {node.isNormal ? "nml" : node.isCyclic ? "cyc" : node.order === 1 ? "triv" : "non"}
        </div>
      </div>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  SETTINGS MODAL
// ═══════════════════════════════════════════════════════════════════════

function SettingsModal({
  isOpen,
  onClose,
  gridSettings,
  setGridSettings,
  camera,
  setCamera,
  lattices,
  morphisms,
  notes,
  drawStrokes,
  nodeCustomStyles,
  onLoadState,
  panelRef,
}) {
  const [activeTab, setActiveTab] = useState('data');
  const [exportFormat, setExportFormat] = useState('mermaid');
  const [saveName, setSaveName] = useState(`lattice_${new Date().toISOString().slice(0,10)}`);

  const previewCanvasRef = useRef(null);
  const [previewCam, setPreviewCam] = useState({ x: 0, y: 0, k: 1 });
  const isPreviewPanning = useRef(false);
  const previewPanStart = useRef({ mouseX: 0, mouseY: 0, camX: 0, camY: 0 });

  // --- 1. SIMPLE BOUNDING BOX WITH TIGHT MARGINS ---
  const getLatticeBounds = () => {
    let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    let hasNodes = false;

    lattices.forEach((lattice) => {
      const base = lattice.base;
      if (!base || !base.nodes) return;
      const epicenter = lattice.epicenter || { x: 0, y: 0 };
      
      base.nodes.forEach((node) => {
        const wx = (node.x - base.W / 2) + epicenter.x;
        const wy = (node.y - base.H / 2) + epicenter.y;
        minX = Math.min(minX, wx);
        maxX = Math.max(maxX, wx);
        minY = Math.min(minY, wy);
        maxY = Math.max(maxY, wy);
        hasNodes = true;
      });
    });

    if (!hasNodes) {
      return { x: -200, y: -150, width: 400, height: 300 };
    }
    
    // Tight padding (5% of size, minimum 10px)
    const width = maxX - minX;
    const height = maxY - minY;
    const padX = Math.max(width * 0.05, 10);
    const padY = Math.max(height * 0.05, 10);
    
    return {
      x: minX - padX,
      y: minY - padY,
      width: width + padX * 2,
      height: height + padY * 2,
    };
  };

  // --- 2. COMPUTE FIT CAMERA ---
  const computeFitCamera = () => {
    const bounds = getLatticeBounds();
    const canvasW = 400, canvasH = 320;
    
    const scaleX = canvasW / bounds.width;
    const scaleY = canvasH / bounds.height;
    // Use 90% of the max scale to leave a small margin
    const scale = Math.min(scaleX, scaleY) * 0.9;
    
    const cx = bounds.x + bounds.width / 2;
    const cy = bounds.y + bounds.height / 2;
    
    return {
      k: Math.max(0.1, Math.min(3, scale)),
      x: canvasW / 2 - cx * scale,
      y: canvasH / 2 - cy * scale,
    };
  };

  // --- 3. DRAWING FUNCTION ---
  const drawPreview = useCallback(() => {
    const canvas = previewCanvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext('2d');
    const W = canvas.width, H = canvas.height;
    
    ctx.clearRect(0, 0, W, H);
    ctx.save();
    ctx.translate(previewCam.x, previewCam.y);
    ctx.scale(previewCam.k, previewCam.k);

    // Background
    ctx.fillStyle = '#F4F6F4';
    ctx.fillRect(-2000, -2000, 4000, 4000);

    // Grid (simplified for preview)
    if (gridSettings.pattern !== 'none') {
      ctx.strokeStyle = gridSettings.color;
      ctx.lineWidth = 0.5 / previewCam.k;
      const size = gridSettings.size;
      const startX = -2000 - (previewCam.x % (size * previewCam.k)) / previewCam.k;
      const startY = -2000 - (previewCam.y % (size * previewCam.k)) / previewCam.k;
      for (let x = startX; x < 4000; x += size) {
        ctx.beginPath();
        ctx.moveTo(x, -2000);
        ctx.lineTo(x, 2000);
        ctx.stroke();
      }
      for (let y = startY; y < 4000; y += size) {
        ctx.beginPath();
        ctx.moveTo(-2000, y);
        ctx.lineTo(2000, y);
        ctx.stroke();
      }
    }

    // Draw lattices
    lattices.forEach((lattice) => {
      const base = lattice.base;
      if (!base || !base.nodes) return;
      const epicenter = lattice.epicenter || { x: 0, y: 0 };

      if (lattice.showEdges && base.edges) {
        base.edges.forEach(([a, b]) => {
          const na = base.nodes[a], nb = base.nodes[b];
          if (!na || !nb) return;
          const x1 = (na.x - base.W / 2) + epicenter.x;
          const y1 = (na.y - base.H / 2) + epicenter.y;
          const x2 = (nb.x - base.W / 2) + epicenter.x;
          const y2 = (nb.y - base.H / 2) + epicenter.y;
          ctx.beginPath();
          ctx.moveTo(x1, y1);
          ctx.lineTo(x2, y2);
          ctx.strokeStyle = '#93b5c8';
          ctx.lineWidth = 1.5 / previewCam.k;
          ctx.stroke();
        });
      }

      base.nodes.forEach((node) => {
        const x = (node.x - base.W / 2) + epicenter.x;
        const y = (node.y - base.H / 2) + epicenter.y;
        const r = Math.max(4, 8 / previewCam.k);
        ctx.fillStyle = node.isNormal ? '#4ade80' : node.order === 1 ? '#fbbf24' : '#0284c7';
        ctx.beginPath();
        ctx.arc(x, y, r, 0, Math.PI * 2);
        ctx.fill();
        ctx.strokeStyle = '#0B151E';
        ctx.lineWidth = 0.8 / previewCam.k;
        ctx.stroke();
      });
    });

    ctx.restore();
  }, [lattices, gridSettings, previewCam]);

  // --- 4. INITIALIZE ON OPEN ---
  useEffect(() => {
    if (isOpen) {
      const newCam = computeFitCamera();
      setPreviewCam(newCam);
    }
  }, [isOpen]);

  // --- 5. DRAW WHENEVER ANYTHING CHANGES ---
  useEffect(() => {
    if (!isOpen) return;
    drawPreview();
  }, [drawPreview, isOpen]);

  // --- 6. PREVIEW INTERACTIONS ---
  const onPreviewWheel = (e) => {
    e.preventDefault();
    e.stopPropagation();
    const rect = previewCanvasRef.current.getBoundingClientRect();
    const mx = e.clientX - rect.left;
    const my = e.clientY - rect.top;
    const delta = e.deltaY > 0 ? 0.9 : 1.1;
    setPreviewCam(prev => ({
      k: Math.min(3, Math.max(0.1, prev.k * delta)),
      x: mx - (mx - prev.x) * delta,
      y: my - (my - prev.y) * delta,
    }));
  };

  const onPreviewMouseDown = (e) => {
    if (e.button !== 0) return;
    e.preventDefault();
    e.stopPropagation();
    isPreviewPanning.current = true;
    previewPanStart.current = {
      mouseX: e.clientX,
      mouseY: e.clientY,
      camX: previewCam.x,
      camY: previewCam.y,
    };
    document.body.style.cursor = 'grabbing';
  };

  useEffect(() => {
    const onMove = (e) => {
      if (!isPreviewPanning.current) return;
      const dx = e.clientX - previewPanStart.current.mouseX;
      const dy = e.clientY - previewPanStart.current.mouseY;
      setPreviewCam(prev => ({
        ...prev,
        x: previewPanStart.current.camX + dx,
        y: previewPanStart.current.camY + dy,
      }));
    };
    const onUp = () => {
      if (isPreviewPanning.current) {
        isPreviewPanning.current = false;
        document.body.style.cursor = '';
      }
    };
    window.addEventListener('mousemove', onMove);
    window.addEventListener('mouseup', onUp);
    return () => {
      window.removeEventListener('mousemove', onMove);
      window.removeEventListener('mouseup', onUp);
    };
  }, []);

  const resetPreviewView = () => {
    setPreviewCam(computeFitCamera());
  };

  // --- 7. PNG EXPORT (unchanged) ---
  const exportPNG = useCallback(async () => {
    const mainElement = panelRef?.current;
    if (!mainElement) return;
    const svg = mainElement.querySelector('svg');
    if (!svg) return;

    const clone = svg.cloneNode(true);
    clone.setAttribute('style', 'position:absolute;top:0;left:0;width:100%;height:100%;');

    const serializer = new XMLSerializer();
    let source = serializer.serializeToString(clone);
    if (!source.includes('xmlns')) {
      source = source.replace('<svg', '<svg xmlns="http://www.w3.org/2000/svg"');
    }
    const svgBlob = new Blob([
      `<?xml version="1.0" standalone="no"?>\r\n<!DOCTYPE svg PUBLIC "-//W3C//DTD SVG 1.1//EN" "http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd">\r\n`,
      source
    ], { type: 'image/svg+xml;charset=utf-8' });

    const url = URL.createObjectURL(svgBlob);
    const img = new Image();
    img.onload = () => {
      const bbox = svg.getBBox ? svg.getBBox() : { x: 0, y: 0, width: 800, height: 600 };
      const padding = 20;
      const scale = 2;
      const w = (bbox.width + padding * 2) * scale;
      const h = (bbox.height + padding * 2) * scale;

      const canvas = document.createElement('canvas');
      canvas.width = w;
      canvas.height = h;
      const ctx = canvas.getContext('2d');
      ctx.fillStyle = '#F4F6F4';
      ctx.fillRect(0, 0, w, h);
      const dx = (w - img.width * scale) / 2;
      const dy = (h - img.height * scale) / 2;
      ctx.drawImage(img, dx, dy, img.width * scale, img.height * scale);

      const link = document.createElement('a');
      link.download = `${saveName || 'lattice_diagram'}.png`;
      link.href = canvas.toDataURL('image/png');
      link.click();
      URL.revokeObjectURL(url);
    };
    img.src = url;
  }, [panelRef, saveName]);

  // --- 8. SAVE / LOAD ---
  const handleSave = useCallback(async (format) => {
    const state = {
      lattices,
      morphisms,
      notes,
      drawStrokes,
      nodeCustomStyles,
      gridSettings,
      camera,
    };
    if (format === 'mermaid') {
      const mermaid = generateMermaidFile(lattices, morphisms);
      const blob = new Blob([mermaid], { type: 'text/plain' });
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = `${saveName || 'lattice_diagram'}.mmd`;
      a.click();
      URL.revokeObjectURL(url);
    } else if (format === 'json' || format === 'state') {
      const serialized = serializeCanvasState(state);
      const json = JSON.stringify(serialized, null, 2);
      const blob = new Blob([json], { type: 'application/json' });
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = `${saveName || 'lattice_state'}.psinite`;
      a.click();
      URL.revokeObjectURL(url);
    }
  }, [lattices, morphisms, notes, drawStrokes, nodeCustomStyles, gridSettings, camera, saveName]);

  const handleLoad = useCallback(() => {
    const input = document.createElement('input');
    input.type = 'file';
    input.accept = '.psinite,.json';
    input.onchange = (e) => {
      const file = e.target.files[0];
      if (!file) return;
      const reader = new FileReader();
      reader.onload = (event) => {
        try {
          const data = JSON.parse(event.target.result);
          const restored = deserializeCanvasState(data);
          onLoadState(restored);
          onClose();
        } catch (err) {
          alert('Error loading file: ' + err.message);
        }
      };
      reader.readAsText(file);
    };
    input.click();
  }, [onLoadState, onClose]);

  if (!isOpen) return null;

  const tabs = [
    { id: 'data', label: 'Save/Export' },
    { id: 'info', label: 'Info' },
    { id: 'style', label: 'Style' },
  ];

  return (
    <div
      style={{
        position: "fixed",
        inset: 0,
        zIndex: 300,
        background: "rgba(11,21,30,0.35)",
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        backdropFilter: "blur(4px)",
      }}
      onClick={e => { if (e.target === e.currentTarget) onClose(); }}
    >
      <style>{`
        @keyframes fadeIn {
          from { opacity: 0; transform: scale(0.96); }
          to { opacity: 1; transform: scale(1); }
        }
        @keyframes slideIn {
          from { opacity: 0; transform: translateY(8px); }
          to { opacity: 1; transform: translateY(0); }
        }
      `}</style>

      <div style={{
        background: "#FFFFFF",
        borderRadius: 16,
        boxShadow: "0 24px 64px rgba(11,21,30,0.20), 0 0 0 1px rgba(11,21,30,0.04)",
        width: 820,
        maxWidth: "92vw",
        aspectRatio: "16 / 9",
        maxHeight: "85vh",
        display: "flex",
        flexDirection: "column",
        overflow: "hidden",
      }}>
        {/* Header */}
        <div style={{
          padding: "16px 24px",
          borderBottom: "1px solid #E8ECEE",
          display: "flex",
          alignItems: "center",
          justifyContent: "space-between",
          flexShrink: 0,
        }}>
          <div style={{ display: "flex", alignItems: "center", gap: 10 }}>
            <svg width="18" height="18" viewBox="0 0 18 18" fill="none">
              <rect x="2.5" y="2.5" width="5" height="5" rx="1" fill="#1e3d54" opacity="0.7"/>
              <rect x="10.5" y="2.5" width="5" height="5" rx="1" fill="#1e3d54" opacity="0.5"/>
              <rect x="2.5" y="10.5" width="5" height="5" rx="1" fill="#1e3d54" opacity="0.5"/>
              <rect x="10.5" y="10.5" width="5" height="5" rx="1" fill="#1e3d54" opacity="0.9"/>
            </svg>
            <span style={{
              fontSize: 13,
              fontWeight: "600",
              color: "#0B151E",
              fontFamily: "'Courier New', monospace",
              letterSpacing: 2,
            }}>SETTINGS</span>
          </div>
          <button
            onClick={onClose}
            style={{
              background: "none",
              border: "none",
              cursor: "pointer",
              color: "#3a6278",
              fontSize: 18,
              padding: "4px 8px",
              borderRadius: 4,
              transition: "background 0.1s",
            }}
            onMouseEnter={e => e.currentTarget.style.background = "#F4F6F4"}
            onMouseLeave={e => e.currentTarget.style.background = "transparent"}
          >
            ×
          </button>
        </div>

        {/* Main content */}
        <div style={{
          display: "flex",
          flex: 1,
          minHeight: 0,
          overflow: "hidden",
        }}>
          
          {/* Left: Interactive Preview */}
          <div style={{
            width: "45%",
            padding: "20px 16px 20px 20px",
            display: "flex",
            flexDirection: "column",
            borderRight: "1px solid #E8ECEE",
            background: "#FAFBFB",
            overflow: "hidden",
          }}>
            <div style={{
              fontSize: 9,
              letterSpacing: 2,
              color: "#3a6278",
              textTransform: "uppercase",
              marginBottom: 10,
              fontFamily: "'Courier New', monospace",
            }}>
              Preview <span style={{ fontWeight: 300, fontSize: 8 }}>(drag to pan • scroll to zoom)</span>
            </div>
            
            <div
              style={{
                flex: 1,
                background: "#FFFFFF",
                borderRadius: 8,
                border: "1px solid #DEE7DC",
                overflow: "hidden",
                position: "relative",
                minHeight: 0,
                cursor: "grab",
              }}
              onWheel={onPreviewWheel}
              onMouseDown={onPreviewMouseDown}
            >
              <canvas
                ref={previewCanvasRef}
                width={400}
                height={320}
                style={{
                  width: "100%",
                  height: "100%",
                  display: "block",
                }}
              />
              <button
                onClick={resetPreviewView}
                style={{
                  position: "absolute",
                  bottom: 8,
                  right: 8,
                  background: "rgba(255,255,255,0.85)",
                  border: "1px solid #DEE7DC",
                  borderRadius: 4,
                  padding: "2px 8px",
                  fontSize: 8,
                  fontFamily: "'Courier New', monospace",
                  color: "#3a6278",
                  cursor: "pointer",
                  backdropFilter: "blur(4px)",
                }}
              >
                Reset View
              </button>
            </div>
            
            <div style={{
              display: "flex",
              gap: 16,
              marginTop: 8,
              fontSize: 8,
              color: "#3a6278",
              fontFamily: "'Courier New', monospace",
              letterSpacing: 0.5,
            }}>
              <span>⎔ {lattices.length}</span>
              <span>⇢ {morphisms.length}</span>
              <span>▣ {notes.length}</span>
            </div>
          </div>

          {/* Right: Tabs */}
          <div style={{
            flex: 1,
            padding: "20px 20px 20px 16px",
            display: "flex",
            flexDirection: "column",
            minWidth: 0,
          }}>
            <div style={{
              display: "flex",
              gap: 4,
              marginBottom: 18,
              borderBottom: "1px solid #E8ECEE",
              paddingBottom: 12,
            }}>
              {tabs.map(tab => (
                <button
                  key={tab.id}
                  onClick={() => setActiveTab(tab.id)}
                  style={{
                    padding: "6px 14px",
                    borderRadius: 20,
                    fontSize: 9,
                    fontFamily: "'Courier New', monospace",
                    letterSpacing: 1,
                    textTransform: "uppercase",
                    background: activeTab === tab.id ? "#1e3d54" : "transparent",
                    color: activeTab === tab.id ? "#FFFFFF" : "#3a6278",
                    border: activeTab === tab.id ? "none" : "1px solid transparent",
                    cursor: "pointer",
                    transition: "all 0.15s",
                  }}
                >
                  {tab.label}
                </button>
              ))}
            </div>
            
            <div style={{
              flex: 1,
              overflowY: "auto",
              overflowX: "hidden",
              scrollbarGutter: "stable",
            }}>
              {/* DATA TAB */}
              {activeTab === 'data' && (
                <div style={{ display: "flex", flexDirection: "column", gap: 16 }}>
                  <div>
                    <div style={{ fontSize: 8, letterSpacing: 2, color: "#3a6278", textTransform: "uppercase", marginBottom: 4 }}>File Name</div>
                    <input
                      type="text"
                      value={saveName}
                      onChange={e => setSaveName(e.target.value)}
                      style={{
                        width: "100%",
                        padding: "6px 10px",
                        borderRadius: 6,
                        border: "1px solid #DEE7DC",
                        fontSize: 11,
                        fontFamily: "'Courier New', monospace",
                        background: "#FAFBFB",
                        color: "#0B151E",
                        outline: "none",
                      }}
                    />
                  </div>
                  
                  <div style={{ display: "flex", gap: 8 }}>
                    <button
                      onClick={() => handleSave('state')}
                      style={{
                        flex: 1,
                        padding: "8px 16px",
                        borderRadius: 6,
                        border: "none",
                        background: "#1e3d54",
                        color: "#FFFFFF",
                        fontSize: 9,
                        fontFamily: "'Courier New', monospace",
                        letterSpacing: 1.5,
                        textTransform: "uppercase",
                        cursor: "pointer",
                        transition: "background 0.15s",
                      }}
                    >
                      Save State
                    </button>
                    <button
                      onClick={handleLoad}
                      style={{
                        flex: 1,
                        padding: "8px 16px",
                        borderRadius: 6,
                        border: "1px solid #1e3d54",
                        background: "transparent",
                        color: "#1e3d54",
                        fontSize: 9,
                        fontFamily: "'Courier New', monospace",
                        letterSpacing: 1.5,
                        textTransform: "uppercase",
                        cursor: "pointer",
                        transition: "all 0.15s",
                      }}
                    >
                      Load State
                    </button>
                  </div>
                  
                  <hr style={{ borderColor: "#E8ECEE", margin: "4px 0" }} />

                  <div>
                    <div style={{ fontSize: 8, letterSpacing: 2, color: "#3a6278", textTransform: "uppercase", marginBottom: 6 }}>Export Format</div>
                    <div style={{ display: "flex", gap: 6, flexWrap: "wrap" }}>
                      {[
                        ['mermaid', 'Mermaid'],
                        ['json', 'JSON'],
                        ['png', 'PNG'],
                      ].map(([val, lbl]) => (
                        <button
                          key={val}
                          onClick={() => setExportFormat(val)}
                          style={{
                            padding: "5px 14px",
                            borderRadius: 6,
                            fontSize: 9,
                            cursor: "pointer",
                            letterSpacing: 1,
                            fontFamily: "'Courier New', monospace",
                            background: exportFormat === val ? "#1e3d54" : "transparent",
                            border: exportFormat === val ? "none" : "1px solid #DEE7DC",
                            color: exportFormat === val ? "#FFFFFF" : "#3a6278",
                            transition: "all 0.1s",
                          }}
                        >
                          {lbl}
                        </button>
                      ))}
                    </div>
                  </div>
                  
                  <button
                    onClick={exportFormat === 'png' ? exportPNG : () => handleSave(exportFormat)}
                    disabled={lattices.length === 0 && morphisms.length === 0}
                    style={{
                      padding: "8px 16px",
                      borderRadius: 6,
                      border: "none",
                      background: (lattices.length === 0 && morphisms.length === 0) ? "#DEE7DC" : "#16a34a",
                      color: (lattices.length === 0 && morphisms.length === 0) ? "#3a6278" : "#FFFFFF",
                      fontSize: 9,
                      fontFamily: "'Courier New', monospace",
                      letterSpacing: 1.5,
                      textTransform: "uppercase",
                      cursor: (lattices.length === 0 && morphisms.length === 0) ? "not-allowed" : "pointer",
                      transition: "background 0.15s",
                    }}
                  >
                    {exportFormat === 'mermaid' && 'Export Mermaid'}
                    {exportFormat === 'json' && 'Export JSON'}
                    {exportFormat === 'png' && 'Export PNG'}
                  </button>
                  
                  {exportFormat === 'mermaid' && (
                    <div style={{
                      background: "#F4F6F4",
                      borderRadius: 6,
                      padding: "10px 12px",
                      fontSize: 8,
                      color: "#3a6278",
                      lineHeight: 1.6,
                      fontFamily: "'Courier New', monospace",
                    }}>
                      <div style={{ marginBottom: 4, fontWeight: "600", letterSpacing: 1, textTransform: "uppercase" }}>
                        ℹ Mermaid Export
                      </div>
                      <div>Generates a Mermaid diagram showing all subgroup lattices and morphisms as a single graph.</div>
                    </div>
                  )}
                  {exportFormat === 'png' && (
                    <div style={{
                      background: "#F4F6F4",
                      borderRadius: 6,
                      padding: "10px 12px",
                      fontSize: 8,
                      color: "#3a6278",
                      lineHeight: 1.6,
                      fontFamily: "'Courier New', monospace",
                    }}>
                      <div style={{ marginBottom: 4, fontWeight: "600", letterSpacing: 1, textTransform: "uppercase" }}>
                        ℹ PNG Export
                      </div>
                      <div>Exports the current visible diagram as a high-resolution PNG.</div>
                    </div>
                  )}
                </div>
              )}

              {/* INFO TAB */}
              {activeTab === 'info' && (
                <div style={{ display: "flex", flexDirection: "column", gap: 20 }}>
                  <div>
                    <h3 style={{ fontSize: 11, letterSpacing: 2, color: "#1e3d54", textTransform: "uppercase", margin: "0 0 8px 0", fontFamily: "'Courier New', monospace" }}>
                      Keyboard Shortcuts
                    </h3>
                    <ul style={{ listStyle: "none", padding: 0, margin: 0, fontSize: 10, fontFamily: "'Courier New', monospace", color: "#3a6278", lineHeight: 2 }}>
                      <li><span style={{ background: "#E8ECEE", padding: "0 6px", borderRadius: 3 }}>Esc</span> Cancel active tools / Deselect</li>
                      <li><span style={{ background: "#E8ECEE", padding: "0 6px", borderRadius: 3 }}>Scroll</span> Zoom in/out on canvas</li>
                      <li><span style={{ background: "#E8ECEE", padding: "0 6px", borderRadius: 3 }}>Middle-click + Drag</span> Pan canvas</li>
                      <li><span style={{ background: "#E8ECEE", padding: "0 6px", borderRadius: 3 }}>Click Node</span> Select subgroup</li>
                      <li><span style={{ background: "#E8ECEE", padding: "0 6px", borderRadius: 3 }}>Drag Node</span> Move selected node(s)</li>
                    </ul>
                  </div>
                  <hr style={{ borderColor: "#E8ECEE" }} />
                  <div>
                    <h3 style={{ fontSize: 11, letterSpacing: 2, color: "#1e3d54", textTransform: "uppercase", margin: "0 0 8px 0", fontFamily: "'Courier New', monospace" }}>
                      About Psinite
                    </h3>
                    <p style={{ fontSize: 10, color: "#3a6278", lineHeight: 1.8, fontFamily: "'Courier New', monospace", margin: 0 }}>
                      A visual explorer for finite group theory. Build subgroup lattices, define morphisms,
                      and export diagrams for papers or presentations.
                    </p>
                    <p style={{ fontSize: 9, color: "#93b5c8", marginTop: 8 }}>
                      Version 1.0.0 · Built with React
                    </p>
                  </div>
                </div>
              )}

              {/* STYLE TAB */}
              {activeTab === 'style' && (
                <div style={{ display: "flex", flexDirection: "column", gap: 16 }}>
                  <div>
                    <div style={{ fontSize: 8, letterSpacing: 2, color: "#3a6278", textTransform: "uppercase", marginBottom: 8 }}>Canvas Grid</div>
                    <div style={{ display: "flex", gap: 6 }}>
                      {[["lines","Lines"],["dots","Dots"],["cross","Cross"],["none","None"]].map(([val, lbl]) => (
                        <button key={val} onClick={() => setGridSettings(g => ({ ...g, pattern: val }))}
                          style={{
                            padding: "5px 12px",
                            borderRadius: 6,
                            fontSize: 9,
                            cursor: "pointer",
                            letterSpacing: 1,
                            fontFamily: "'Courier New', monospace",
                            background: gridSettings.pattern === val ? "#1e3d54" : "transparent",
                            border: gridSettings.pattern === val ? "none" : "1px solid #DEE7DC",
                            color: gridSettings.pattern === val ? "#FFFFFF" : "#3a6278",
                            transition: "all 0.1s",
                          }}
                        >
                          {lbl}
                        </button>
                      ))}
                    </div>
                  </div>
                  
                  <div>
                    <div style={{ fontSize: 8, letterSpacing: 2, color: "#3a6278", textTransform: "uppercase", marginBottom: 6 }}>Size: {gridSettings.size}px</div>
                    <input
                      type="range"
                      min={16}
                      max={80}
                      value={gridSettings.size}
                      onChange={e => setGridSettings(g => ({ ...g, size: parseInt(e.target.value) }))}
                      style={{ width: "100%", accentColor: "#1e3d54", cursor: "pointer" }}
                    />
                  </div>
                  
                  <div>
                    <div style={{ fontSize: 8, letterSpacing: 2, color: "#3a6278", textTransform: "uppercase", marginBottom: 6 }}>Grid Color</div>
                    <div style={{ display: "flex", gap: 6, flexWrap: "wrap" }}>
                      {["#DEE7DC","#d4d4d8","#c7d2e8","#f3d8c0","#d4e8d4","#e8d4e8","#1e3d54"].map(col => (
                        <div key={col} onClick={() => setGridSettings(g => ({ ...g, color: col }))}
                          style={{
                            width: 22,
                            height: 22,
                            borderRadius: "50%",
                            cursor: "pointer",
                            background: col,
                            border: gridSettings.color === col ? "2.5px solid #1e3d54" : "1.5px solid #DEE7DC",
                            boxSizing: "border-box",
                            transition: "border 0.1s",
                          }}
                        />
                      ))}
                      <input
                        type="color"
                        value={gridSettings.color}
                        onChange={e => setGridSettings(g => ({ ...g, color: e.target.value }))}
                        style={{ width: 22, height: 22, borderRadius: "50%", border: "none", cursor: "pointer", padding: 0 }}
                      />
                    </div>
                  </div>
                  
                  <div style={{ borderTop: "1px solid #E8ECEE", paddingTop: 14 }}>
                    <div style={{ fontSize: 8, letterSpacing: 2, color: "#3a6278", textTransform: "uppercase", marginBottom: 6 }}>Camera Reset</div>
                    <button
                      onClick={() => setCamera({ tx: 0, ty: 0, scale: 1 })}
                      style={{
                        padding: "5px 12px",
                        borderRadius: 4,
                        border: "1px solid #DEE7DC",
                        background: "transparent",
                        cursor: "pointer",
                        fontSize: 9,
                        color: "#3a6278",
                        letterSpacing: 1,
                        fontFamily: "'Courier New', monospace",
                      }}
                    >
                      Reset Main View
                    </button>
                  </div>
                </div>
              )}
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  NODE RENDERING  (unchanged)
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

const didDragRef = { current: false };

function ShapeNode({ node, latticeId, colorMap, isSelected, isAdjacent, isDrawMode, onToggleSelect, onMouseDown }) {
  // Element/geometry views: B&W — color can't accurately represent order info for all layouts
  // Tree views: use depth color stored on the node
  // Flower views: color by petal index; hub is accent gold
  const PETAL_COLORS = ["#0284c7","#7c3aed","#db2777","#ea580c","#16a34a","#ca8a04","#be123c","#0891b2","#65a30d","#9333ea"];
  const isElemView = node.viewType === "elements" || node.viewType === "geometry";
  const isTreeView = node.viewType === "tree";
  const isFlowerView = node.viewType === "flower";
  const baseCol = isElemView ? C.inkMid
    : isTreeView ? (node._depthColor ?? C.inkMid)
    : isFlowerView ? (node._isHub ? "#ca8a04" : PETAL_COLORS[(node._petalIdx ?? 0) % PETAL_COLORS.length])
    : orderColor(node.order, colorMap);
  const col = node._customColor ?? baseCol;
  const R = (isFlowerView && node._isHub) ? 32 : 26;
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
  else {
    const h = g.h;
    shapeEl = <polygon points={`${node.x},${node.y - h * 0.68} ${node.x - h * 0.72},${node.y + h * 0.46} ${node.x + h * 0.72},${node.y + h * 0.46}`} fill={fill} stroke={strokeCol} strokeWidth={sw} strokeDasharray={dash} />;
  }

  return (
    <g data-node="true" data-lattice-id={String(latticeId)} data-node-id={String(node.id)}
      style={{ cursor: isDrawMode ? "crosshair" : isSelected ? "grab" : "pointer" }}
      onMouseDown={e => {
        didDragRef.current = false;
        if (isDrawMode) { onMouseDown(node.id, e); e.stopPropagation(); return; }
        if (isSelected) { onMouseDown(node.id, e); e.stopPropagation(); }
      }}
      onClick={e => {
        if (!isDrawMode && !didDragRef.current) onToggleSelect(node.id);
        e.stopPropagation();
      }}>
      {isDrawMode && <circle cx={node.x} cy={node.y} r={33} fill="none" stroke={C.inkFaint} strokeWidth={1} strokeDasharray="3 3" opacity={0.45} />}
      {shapeEl}
      <text x={node.x} y={node.y + 1} textAnchor="middle" dominantBaseline="middle"
        fontSize={9.5} fill={textCol} fontFamily="'Courier New', monospace" fontWeight="600"
        style={{ pointerEvents: "none", userSelect: "none" }}>{lbl}</text>
    </g>
  );
}

function Epicenter({ x, y, accent, onMouseDown, cameraScale }) {
  // Minimum 12px on screen; grows naturally with zoom but never shrinks below
  const minR = 12;
  const R = Math.max(minR / (cameraScale || 1), 14);
  return (
    <g data-epicenter="true" style={{ cursor: "grab" }}
      onMouseDown={e => { e.preventDefault(); e.stopPropagation(); onMouseDown(e); }}>
      <circle cx={x} cy={y} r={R} fill="none" stroke={accent} strokeWidth={Math.max(1, 1.5 / (cameraScale || 1))} opacity={0.7} />
      <circle cx={x} cy={y} r={Math.max(2, 3 / (cameraScale || 1))} fill={accent} opacity={0.85} />
      <line x1={x - R - 5} y1={y} x2={x - R + 3} y2={y} stroke={accent} strokeWidth={Math.max(0.8, 1 / (cameraScale || 1))} opacity={0.5} />
      <line x1={x + R - 3} y1={y} x2={x + R + 5} y2={y} stroke={accent} strokeWidth={Math.max(0.8, 1 / (cameraScale || 1))} opacity={0.5} />
      <line x1={x} y1={y - R - 5} x2={x} y2={y - R + 3} stroke={accent} strokeWidth={Math.max(0.8, 1 / (cameraScale || 1))} opacity={0.5} />
      <line x1={x} y1={y + R - 3} x2={x} y2={y + R + 5} stroke={accent} strokeWidth={Math.max(0.8, 1 / (cameraScale || 1))} opacity={0.5} />
    </g>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  LATTICE ENTRY HELPERS  (unchanged)
// ═══════════════════════════════════════════════════════════════════════

let nextLatticeId = 1;

function makeLatticeEntry(base, canvasW, canvasH, labelOverride, params = {}) {
  // Use a unique ID: timestamp + random + increment to be safe
  const id = Date.now() + Math.random() * 1000 + (nextLatticeId++);
  const arrowViews = new Set(["elements", "geometry", "cayley", "flower", "tree"]);
  const showArrows = !arrowViews.has(base.viewType);
  return {
    id,  // <-- now guaranteed unique even across loads
    label: labelOverride,
    kind: base.kind,
    param: params.param ?? base.param,
    param2: params.param2,
    param3: params.param3,
    base,
    nodePositions: {},
    epicenter: { x: canvasW / 2, y: canvasH / 2 },
    showArrows,
    showEdges: true,
    showEpicenter: true,
    hasseLayout: { genOffset: false, rankByOrder: false },
  };
}

function resolveNodes(entry) {
  const base = entry.base;

  // Collapsed: render a single representative node at the epicenter
  if (entry.isCollapsed) {
    const fullNode = base.nodes[base.nodes.length - 1] ?? base.nodes[0];
    const rep = {
      ...(fullNode ?? {}),
      id: 0,
      x: entry.epicenter.x,
      y: entry.epicenter.y,
      shortLabel: entry.label,
      label: entry.label,
      shape: "square",
      _isCollapsedRep: true,
    };
    return [rep];
  }

  const layout = entry.hasseLayout ?? {};
  const isHasse = base.viewType === "hasse" || base.viewType === "tree" || !base.viewType;

  // Compute adjusted positions from hasse layout options
  let adjustedX = null, adjustedY = null;

  if (isHasse && (layout.genOffset || layout.rankByOrder) && base.nodes.length > 0) {
    const nodes = base.nodes;
    const W = base.W, H = base.H;
    const padX = 60, padY = 55;

    // rankByOrder: re-assign Y based on element order instead of lattice level
    // genOffset: nudge X within each level based on generator count (rank)
    const orders = [...new Set(nodes.map(n => n.order))].sort((a, b) => a - b);
    const maxOrder = Math.max(...orders);
    const minOrder = Math.min(...orders);

    // Build level groups (by order if rankByOrder, otherwise use existing level)
    const byRank = {};
    nodes.forEach((n, i) => {
      const key = layout.rankByOrder ? n.order : n.level;
      (byRank[key] = byRank[key] || []).push(i);
    });
    const rankKeys = Object.keys(byRank).map(Number).sort((a, b) => a - b);
    const maxRank = rankKeys.length - 1;

    const NODE_R = 26;
    const H_SPACING = Math.max(NODE_R * 3.8, 560 / Math.max(Math.max(...rankKeys.map(k => byRank[k].length)) + 1, 2));
    const V_SPACING = Math.max(NODE_R * 3.5, (H - padY * 2) / Math.max(maxRank, 1));

    adjustedX = new Array(nodes.length);
    adjustedY = new Array(nodes.length);

    rankKeys.forEach((rk, rankIdx) => {
      const group = byRank[rk];
      // Sort within level by generator rank if genOffset, then apply sub-offset
      const sorted = layout.genOffset
        ? [...group].sort((a, b) => (nodes[a].rank ?? 1) - (nodes[b].rank ?? 1))
        : group;

      sorted.forEach((ni, idx) => {
        const baseX = padX + (idx + 1) * (W - 2 * padX) / (sorted.length + 1);
        // genOffset: within the same level, stagger by rank (generator count) slightly
        const genNudge = layout.genOffset
          ? ((nodes[ni].rank ?? 1) - 1) * NODE_R * 0.6
          : 0;
        adjustedX[ni] = baseX + genNudge;
        adjustedY[ni] = H - padY - rankIdx * V_SPACING;
      });
    });
  }

  return base.nodes.map((n, i) => ({
    ...n,
    x: (entry.nodePositions[n.id]?.x ?? (adjustedX ? adjustedX[i] : n.x)) + entry.epicenter.x - base.W / 2,
    y: (entry.nodePositions[n.id]?.y ?? (adjustedY ? adjustedY[i] : n.y)) + entry.epicenter.y - base.H / 2,
  }));
}

// ═══════════════════════════════════════════════════════════════════════
//  RAW TABLE IMPORT MODAL
// ═══════════════════════════════════════════════════════════════════════

function RawTableModal({ onSubmit, onClose }) {
  const [text, setText] = useState('{\n  "table": [[0,1,2],[1,2,0],[2,0,1]],\n  "labels": ["e","r","r²"]\n}');
  const [err, setErr] = useState("");
  const handleSubmit = () => {
    try {
      const parsed = JSON.parse(text);
      if (!Array.isArray(parsed.table)) throw new Error("table must be an array");
      setErr("");
      onSubmit(parsed);
    } catch (e) { setErr(String(e)); }
  };
  return (
    <div style={{
      position: "fixed", inset: 0, zIndex: 100,
      background: "rgba(0,0,0,0.45)", display: "flex", alignItems: "center", justifyContent: "center",
    }}>
      <div style={{
        background: C.panelBg, border: `1px solid ${C.border}`, borderRadius: 8,
        padding: 24, width: 420, maxWidth: "90vw", display: "flex", flexDirection: "column", gap: 12,
      }}>
        <div style={{ fontSize: 10, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase" }}>Paste Raw Cayley Table</div>
        <div style={{ fontSize: 9, color: C.inkFaint, lineHeight: 1.6 }}>
          JSON with <code>table</code> (index array) and optional <code>labels</code>. Identity must be index 0.
        </div>
        <textarea value={text} onChange={e => setText(e.target.value)}
          style={{
            width: "100%", height: 160, background: C.bg, border: `1px solid ${C.border}`,
            borderRadius: 4, color: C.ink, fontSize: 11, padding: 8, resize: "vertical",
            fontFamily: "'Courier New', monospace", outline: "none",
          }} />
        {err && <div style={{ color: "#f87171", fontSize: 10 }}>{err}</div>}
        <div style={{ display: "flex", gap: 8, justifyContent: "flex-end" }}>
          <button onClick={onClose} style={{ background: "none", border: `1px solid ${C.border}`, borderRadius: 4, padding: "6px 14px", cursor: "pointer", fontSize: 10, color: C.inkFaint, letterSpacing: 2 }}>Cancel</button>
          <button onClick={handleSubmit} style={{ background: C.ink, border: "none", borderRadius: 4, padding: "6px 14px", cursor: "pointer", fontSize: 10, color: C.panelBg, letterSpacing: 2 }}>Place</button>
        </div>
      </div>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  MAIN APP
// ═══════════════════════════════════════════════════════════════════════

export default function App() {
  // ── State ──────────────────────────────────────────────────────────
  const [lattices, setLattices] = useState([]);
  const [error, setError] = useState("");
  const [catalogParams, setCatalogParams] = useState(
    Object.fromEntries(
      LATTICE_GROUPS.filter(c => c.hasParam).map(c => [c.key, c.paramDefault])
    )
  );
  const [settingsOpen, setSettingsOpen] = useState(false);
  const [catalogParams2, setCatalogParams2] = useState(
    Object.fromEntries(
      LATTICE_GROUPS.filter(c => c.hasParam2).map(c => [c.key, c.paramDefault2])
    )
  );
  const [catalogParams3, setCatalogParams3] = useState(
    Object.fromEntries(
      LATTICE_GROUPS.filter(c => c.hasParam3).map(c => [c.key, c.paramDefault3])
    )
  );
  // Which view is selected per group folder key (defaults to first view = "hasse")
  const [selectedViews, setSelectedViews] = useState(
    Object.fromEntries(LATTICE_GROUPS.map(g => [g.key, g.views[0].key]))
  );
  const [placingLattice, setPlacingLattice] = useState(null);
  const [ghostMousePos, setGhostMousePos] = useState(null);
  // nodeCustomStyles: Map key `latticeId:nodeId` → { color?, labelAlias? }
  const [nodeCustomStyles, setNodeCustomStyles] = useState({});
  // Drawing toolbar collapse + last-used tool quick-toggle
  const [toolbarOpen, setToolbarOpen] = useState(true);
  const [lastDrawTool, setLastDrawTool] = useState("pen");
  const [showRawModal, setShowRawModal] = useState(false);
  const [singleElementLabel, setSingleElementLabel] = useState("a");
  const [selectedNodes, setSelectedNodes] = useState({}); // { latticeId: Set(nodeNodes) }
  const [selectedGraphId, setSelectedGraphId] = useState(null); // which lattice is "focused" in right panel
  const [confirmDeleteNodes, setConfirmDeleteNodes] = useState(new Set()); // lattice ids with delete confirm open
  const [morphisms, setMorphisms] = useState([]);
  const [selectedMorphismNodes, setSelectedMorphismNodes] = useState(new Set()); // radio/multi-select in morphism panel
  const [activeMorphismId, setActiveMorphismId] = useState(null);
  const [strandPreview, setStrandPreview] = useState(null);
  const strandDragging = useRef(null);
  const activeMorphismIdRef = useRef(null);
  useEffect(() => { activeMorphismIdRef.current = activeMorphismId; }, [activeMorphismId]);

  const [leftW, setLeftW] = useState(270);
  const [rightW, setRightW] = useState(310);
  const [leftCollapsed, setLeftCollapsed] = useState(false);
  const [rightCollapsed, setRightCollapsed] = useState(false);
  const leftWBeforeCollapse = useRef(270);
  const rightWBeforeCollapse = useRef(310);

  const [leftPane1Open, setLeftPane1Open] = useState(true);
  const [leftPane2Open, setLeftPane2Open] = useState(true);
  const [leftPane3Open, setLeftPane3Open] = useState(true);
  const [leftPane1Flex, setLeftPane1Flex] = useState(1.2);
  const [leftPane2Flex, setLeftPane2Flex] = useState(1);
  const [leftPane3Flex, setLeftPane3Flex] = useState(0.8);

  const [rightPane1Open, setRightPane1Open] = useState(true);
  const [rightPane2Open, setRightPane2Open] = useState(true);
  const [rightPane3Open, setRightPane3Open] = useState(true);
  const [rightPane1Flex, setRightPane1Flex] = useState(1.1);
  const [rightPane2Flex, setRightPane2Flex] = useState(1.4);
  const [rightPane3Flex, setRightPane3Flex] = useState(1.2);

  const [camera, setCamera] = useState({ tx: 0, ty: 0, scale: 1 });
  const cameraRef = useRef({ tx: 0, ty: 0, scale: 1 });
  useEffect(() => { cameraRef.current = camera; }, [camera]);

  const panelRef = useRef(null);
  const containerRef = useRef(null);
  const leftPanelRef = useRef(null);
  const rightPanelRef = useRef(null);

  const leftSplitDragging = useRef(false);
  const rightSplitDragging = useRef(false);
  const leftSplitStart = useRef(0);
  const rightSplitStart = useRef(0);
  const isPanning = useRef(false);
  const panStart = useRef({ mouseX: 0, mouseY: 0, tx: 0, ty: 0 });
  const nodeDragging = useRef(null);
  const epicenterDragging = useRef(null);
  const mouseDownPos = useRef(null);
  const didDrag = useRef(false);

  // ── Drawing system ────────────────────────────────────────────────
  const [drawTool, setDrawTool] = useState(null);
  const [drawColor, setDrawColor] = useState("#1e3d54");
  const [drawSize, setDrawSize] = useState(2);
  const [drawStrokes, setDrawStrokes] = useState([]);
  const [drawPermanent, setDrawPermanent] = useState(true);
  const [colorPopOpen, setColorPopOpen] = useState(false);
  const [drawMenuOpen, setDrawMenuOpen] = useState(false);
  const [drawMenuHovered, setDrawMenuHovered] = useState(null);
  const drawMenuLeaveTimer = useRef(null);
  const [drawLineStyle, setDrawLineStyle] = useState("plain"); // "plain"|"arrow-end"|"arrow-start"|"arrow-both"
  const [morphBtnOpen, setMorphBtnOpen] = useState(false);
  const [morphBtnHovered, setMorphBtnHovered] = useState(null);
  const drawPermRef = useRef(true);
  useEffect(() => { drawPermRef.current = drawPermanent; }, [drawPermanent]);
  const isDrawing = useRef(false);
  const currentStroke = useRef(null);
  const drawToolRef = useRef(null);
  useEffect(() => { drawToolRef.current = drawTool; }, [drawTool]);
  const drawLineStyleRef = useRef("plain");
  useEffect(() => { drawLineStyleRef.current = drawLineStyle; }, [drawLineStyle]);

  // ── Canvas grid settings ──────────────────────────────────────────
  const [gridSettings, setGridSettings] = useState({
    color: "#DEE7DC",
    size: 32,
    pattern: "lines", // "lines" | "dots" | "cross" | "none"
  });

  // ── Notes system ──────────────────────────────────────────────────
  const [notes, setNotes] = useState([]);
  const [editingNoteId, setEditingNoteId] = useState(null);
  const [collapsedNotes, setCollapsedNotes] = useState(new Set());
  const noteDragging = useRef(null); // { id, startMx, startMy, startX, startY }
  const editingNoteIdRef = useRef(null);
  useEffect(() => { editingNoteIdRef.current = editingNoteId; }, [editingNoteId]);

  const addNote = useCallback((worldX, worldY) => {
    const id = Date.now() + Math.random();
    setNotes(prev => [...prev, { id, x: worldX, y: worldY, text: "", w: 180, h: 90 }]);
    setEditingNoteId(id);
  }, []);

  const updateNote = useCallback((id, patch) => {
    setNotes(prev => prev.map(n => n.id === id ? { ...n, ...patch } : n));
  }, []);

  const removeNote = useCallback((id) => {
    setNotes(prev => prev.filter(n => n.id !== id));
    if (editingNoteId === id) setEditingNoteId(null);
  }, [editingNoteId]);

  // Canvas starts empty — user places graphs from the catalog

  // ── Helpers ───────────────────────────────────────────────────────
  const updateLattice = useCallback((id, patch) => {
    setLattices(prev => prev.map(l => l.id === id ? { ...l, ...patch } : l));
  }, []);
  const updateNodeDescription = useCallback((latticeId, nodeId, description) => {
    setLattices(prev => prev.map(l => {
      if (l.id !== latticeId) return l;
      const base = l.base;
      const updatedNodes = base.nodes.map(n => 
        n.id === nodeId ? { ...n, description } : n
      );
      return { ...l, base: { ...base, nodes: updatedNodes } };
    }));
  }, []);

  const updateLatticeDescription = useCallback((latticeId, description) => {
    setLattices(prev => prev.map(l => 
      l.id === latticeId ? { ...l, description } : l
    ));
  }, []);

  const placeLatticeAt = useCallback((base, label, worldX, worldY, params = {}) => {
  const r = panelRef.current?.getBoundingClientRect();
  const cw = r?.width ?? 800, ch = r?.height ?? 600;
  const entry = makeLatticeEntry(base, cw, ch, label, params); 
  entry.epicenter = { x: worldX, y: worldY };
  setLattices(prev => [...prev, entry]);
  setSelectedGraphId(entry.id);
}, []);

  const removeLattice = useCallback((id) => {
    setLattices(prev => prev.filter(l => l.id !== id));
    setSelectedNodes(prev => {
      const { [id]: _, ...rest } = prev;
      return rest;
    });
    setSelectedGraphId(prev => prev === id ? null : prev);
    setConfirmDeleteNodes(prev => { const next = new Set(prev); next.delete(id); return next; });
    // Purge strands that reference the deleted lattice
    setMorphisms(prev => prev.map(m => ({
      ...m,
      strands: m.strands.filter(s => s.fromLatticeId !== id && s.toLatticeId !== id),
    })));
  }, []);

  // Collapse an entire graph into a single representative node.
  // All incoming/outgoing morphism strands are re-routed to that node.
  const collapseGraphToNode = useCallback((latticeId) => {
    setLattices(prev => prev.map(l => l.id !== latticeId ? l : { ...l, isCollapsed: true }));
    // Save current strand endpoints, re-route to node 0 while collapsed
    setMorphisms(prev => prev.map(m => ({
      ...m,
      strands: m.strands.map(s => ({
        ...s,
        ...(s.fromLatticeId === latticeId ? { fromNodeId: 0, _savedFromNodeId: s._savedFromNodeId ?? s.fromNodeId } : {}),
        ...(s.toLatticeId   === latticeId ? { toNodeId:   0, _savedToNodeId:   s._savedToNodeId   ?? s.toNodeId   } : {}),
      })),
    })));
    setSelectedNodes({});
  }, []);

  const expandGraph = useCallback((latticeId) => {
    setLattices(prev => prev.map(l => l.id !== latticeId ? l : { ...l, isCollapsed: false }));
    // Restore saved strand endpoints
    setMorphisms(prev => prev.map(m => ({
      ...m,
      strands: m.strands.map(s => {
        const next = { ...s };
        if (s.fromLatticeId === latticeId && s._savedFromNodeId != null) {
          next.fromNodeId = s._savedFromNodeId; delete next._savedFromNodeId;
        }
        if (s.toLatticeId === latticeId && s._savedToNodeId != null) {
          next.toNodeId = s._savedToNodeId; delete next._savedToNodeId;
        }
        return next;
      }),
    })));
  }, []);

  // ── Node mouse-down (strand or drag) ─────────────────────────────
  const onNodeMouseDown = useCallback((latticeId, nodeId, e) => {
    console.log('🖱️ MouseDown on node:', { latticeId, nodeId });
    if (activeMorphismId !== null) {
      e.preventDefault(); e.stopPropagation();
      didDrag.current = false; didDragRef.current = false;
      const entry = lattices.find(l => l.id === latticeId);
      if (!entry) return;
      const nodes = resolveNodes(entry);
      const node = nodes.find(n => n.id === nodeId);
      if (!node) return;
      const cam = cameraRef.current;
      const rect = panelRef.current?.getBoundingClientRect();
      const sx = node.x * cam.scale + cam.tx;
      const sy = node.y * cam.scale + cam.ty;
      strandDragging.current = { fromLatticeId: latticeId, fromNodeId: nodeId };
      setStrandPreview({ x1: sx, y1: sy, x2: e.clientX - (rect?.left ?? 0), y2: e.clientY - (rect?.top ?? 0) });
      mouseDownPos.current = { x: e.clientX, y: e.clientY };
      return;
    }
    
    // Check if this specific node is selected
    const latticeSelection = selectedNodes[latticeId] || new Set();
    if (!latticeSelection.has(nodeId)) return;
    
    e.preventDefault(); e.stopPropagation();
    didDrag.current = false; didDragRef.current = false;
    const entry = lattices.find(l => l.id === latticeId);
    if (!entry) return;
    const nodes = resolveNodes(entry);
    const startPositions = {};
    
    // Iterate through all selected nodes across all lattices
    for (const [lid, nodeSet] of Object.entries(selectedNodes)) {
      const lidNum = Number(lid);
      if (lidNum !== latticeId) continue; // Only drag nodes from the same lattice
      
      for (const nid of nodeSet) {
        const n = nodes.find(n => n.id === nid);
        if (n) {
          startPositions[nid] = {
            x: entry.nodePositions[nid]?.x ?? (n.x - entry.epicenter.x + entry.base.W / 2),
            y: entry.nodePositions[nid]?.y ?? (n.y - entry.epicenter.y + entry.base.H / 2),
          };
        }
      }
    }
    
    nodeDragging.current = { latticeId, startMouseX: e.clientX, startMouseY: e.clientY, startPositions };
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
  }, [lattices, selectedNodes, activeMorphismId]);

  const onEpicenterMouseDown = useCallback((latticeId, e) => {
    e.preventDefault(); e.stopPropagation();
    didDrag.current = false; didDragRef.current = false;
    const entry = lattices.find(l => l.id === latticeId);
    if (!entry) return;
    setSelectedGraphId(latticeId);
    epicenterDragging.current = { latticeId, startMouseX: e.clientX, startMouseY: e.clientY, startEpicenter: { ...entry.epicenter } };
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
  }, [lattices]);

  const placingLatticeRef = useRef(null);
  useEffect(() => { placingLatticeRef.current = placingLattice; }, [placingLattice]);

  const onCanvasMouseDown = useCallback((e) => {
    // Middle mouse always pans regardless of active tool
    if (e.button === 1) {
      e.preventDefault();
      didDrag.current = false; didDragRef.current = false;
      isPanning.current = true;
      mouseDownPos.current = { x: e.clientX, y: e.clientY };
      panStart.current = { mouseX: e.clientX, mouseY: e.clientY, tx: cameraRef.current.tx, ty: cameraRef.current.ty };
      document.body.style.cursor = "grabbing";
      document.body.style.userSelect = "none";
      return;
    }

    if (e.target.closest && (e.target.closest("g[data-node]") || e.target.closest("g[data-epicenter]"))) return;
    // Note drag handled via note element's own onMouseDown — skip here if on a note
    if (e.target.closest && e.target.closest("[data-note]")) return;
    // Cancel button — skip placement
    if (e.target.closest && e.target.closest("[data-cancel]")) return;

    if (placingLatticeRef.current) {
      e.preventDefault();
      const rect = panelRef.current?.getBoundingClientRect();
      const cam = cameraRef.current;
      const worldX = (e.clientX - (rect?.left ?? 0) - cam.tx) / cam.scale;
      const worldY = (e.clientY - (rect?.top ?? 0) - cam.ty) / cam.scale;
      const { base, label, params } = placingLatticeRef.current;
      placeLatticeAt(base, label, worldX, worldY, params || {});
      setPlacingLattice(null);
      setGhostMousePos(null);
      return;
    }

    // ── Drawing tools ─────────────────────────────────────────────
    if (drawToolRef.current && drawToolRef.current !== "eraser") {
      e.preventDefault();
      const rect = panelRef.current?.getBoundingClientRect();
      const cam = cameraRef.current;
      const wx = (e.clientX - (rect?.left ?? 0) - cam.tx) / cam.scale;
      const wy = (e.clientY - (rect?.top ?? 0) - cam.ty) / cam.scale;
      const id = Date.now() + Math.random();
      const tool = drawToolRef.current;
      if (tool === "pen") {
        currentStroke.current = { id, tool, color: drawColor, size: drawSize, permanent: drawPermRef.current, points: [[wx, wy]] };
      } else {
        currentStroke.current = { id, tool, color: drawColor, size: drawSize, permanent: drawPermRef.current, x1: wx, y1: wy, x2: wx, y2: wy, lineStyle: drawLineStyleRef.current };
      }
      isDrawing.current = true;
      return;
    }
    if (drawToolRef.current === "eraser") {
      e.preventDefault();
      isDrawing.current = true;
      return;
    }

    e.preventDefault();
    didDrag.current = false; didDragRef.current = false;
    isPanning.current = true;
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
    panStart.current = { mouseX: e.clientX, mouseY: e.clientY, tx: cameraRef.current.tx, ty: cameraRef.current.ty };
    document.body.style.cursor = "grabbing";
    document.body.style.userSelect = "none";
  }, [placeLatticeAt, drawColor, drawSize]);

  // ── Global mouse move / up ────────────────────────────────────────
  useEffect(() => {
    const DRAG_THRESHOLD = 4;
    const onMove = (e) => {
      if (mouseDownPos.current) {
        const dx = e.clientX - mouseDownPos.current.x, dy = e.clientY - mouseDownPos.current.y;
        if (Math.sqrt(dx * dx + dy * dy) > DRAG_THRESHOLD) { didDrag.current = true; didDragRef.current = true; }
      }
      // Ghost preview tracking
      if (placingLatticeRef.current) {
        const rect = panelRef.current?.getBoundingClientRect();
        if (rect) setGhostMousePos({ x: e.clientX - rect.left, y: e.clientY - rect.top });
      }
      if (isPanning.current) {
        const { mouseX, mouseY, tx, ty } = panStart.current;
        setCamera(prev => ({ ...prev, tx: tx + (e.clientX - mouseX), ty: ty + (e.clientY - mouseY) }));
      }
      if (strandDragging.current) {
        const rect = panelRef.current?.getBoundingClientRect();
        setStrandPreview(prev => prev ? { ...prev, x2: e.clientX - (rect?.left ?? 0), y2: e.clientY - (rect?.top ?? 0) } : null);
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
      // ── Note dragging ──
      if (noteDragging.current) {
        const { id, startMx, startMy, startX, startY } = noteDragging.current;
        const dx = (e.clientX - startMx) / cameraRef.current.scale;
        const dy = (e.clientY - startMy) / cameraRef.current.scale;
        setNotes(prev => prev.map(n => n.id === id ? { ...n, x: startX + dx, y: startY + dy } : n));
      }
      // ── Drawing ──
      if (isDrawing.current && currentStroke.current) {
        const rect = panelRef.current?.getBoundingClientRect();
        const cam = cameraRef.current;
        const wx = (e.clientX - (rect?.left ?? 0) - cam.tx) / cam.scale;
        const wy = (e.clientY - (rect?.top ?? 0) - cam.ty) / cam.scale;
        const s = currentStroke.current;
        if (s.tool === "pen") {
          const updated = { ...s, points: [...s.points, [wx, wy]] };
          currentStroke.current = updated;
          setDrawStrokes(prev => {
            const idx = prev.findIndex(x => x.id === updated.id);
            return idx >= 0 ? prev.map((x, i) => i === idx ? updated : x) : [...prev, updated];
          });
        } else {
          const updated = { ...s, x2: wx, y2: wy };
          currentStroke.current = updated;
          setDrawStrokes(prev => {
            const idx = prev.findIndex(x => x.id === updated.id);
            return idx >= 0 ? prev.map((x, i) => i === idx ? updated : x) : [...prev, updated];
          });
        }
      }
      if (isDrawing.current && drawToolRef.current === "eraser") {
        const rect = panelRef.current?.getBoundingClientRect();
        const cam = cameraRef.current;
        const wx = (e.clientX - (rect?.left ?? 0) - cam.tx) / cam.scale;
        const wy = (e.clientY - (rect?.top ?? 0) - cam.ty) / cam.scale;
        const R = 16 / cam.scale;
        setDrawStrokes(prev => prev.filter(s => {
          if (s.tool === "pen") return !s.points.some(([px, py]) => Math.hypot(px - wx, py - wy) < R);
          const cx = (s.x1 + s.x2) / 2, cy = (s.y1 + s.y2) / 2;
          return Math.hypot(cx - wx, cy - wy) >= R;
        }));
      }
      if (leftSplitDragging.current) {
        const delta = e.clientX - leftSplitStart.current; leftSplitStart.current = e.clientX;
        setLeftW(w => { const next = w + delta; if (next < 60) { leftWBeforeCollapse.current = Math.max(w, 200); setLeftCollapsed(true); return 0; } setLeftCollapsed(false); return Math.min(500, next); });
      }
      if (rightSplitDragging.current) {
        const delta = e.clientX - rightSplitStart.current; rightSplitStart.current = e.clientX;
        setRightW(w => { const next = w - delta; if (next < 60) { rightWBeforeCollapse.current = Math.max(w, 220); setRightCollapsed(true); return 0; } setRightCollapsed(false); return Math.min(520, next); });
      }
    };
    const onUp = (e) => {
      if (strandDragging.current && activeMorphismIdRef.current !== null) {
        const { fromLatticeId, fromNodeId } = strandDragging.current;
        let el = e.target;
        while (el && el !== document.body) {
          if (el.getAttribute && el.getAttribute("data-node") === "true") break;
          el = el.parentElement;
        }
        if (el && el.getAttribute("data-node") === "true") {
          const rawLatticeId = el.getAttribute("data-lattice-id");
          const rawNodeId = el.getAttribute("data-node-id");
          
          // ✅ MUST use Number(), NOT parseInt()
          const toLatticeId = parseFloat(el.getAttribute("data-lattice-id"));
          const toNodeId = parseFloat(el.getAttribute("data-node-id"));

          console.log('🔍 Strand drop target:', {
            element: el,
            rawLatticeId,
            rawNodeId,
            parsedLatticeId: toLatticeId,
            parsedNodeId: toNodeId,
            isValid: !isNaN(toLatticeId) && !isNaN(toNodeId)
          });

          if (!isNaN(toLatticeId) && !isNaN(toNodeId) && !(toLatticeId === fromLatticeId && toNodeId === fromNodeId)) {
            const sid = Date.now() + Math.random();
            setMorphisms(prev => prev.map(m =>
              m.id !== activeMorphismIdRef.current ? m : {
                ...m, strands: [...m.strands, { id: sid, fromLatticeId, fromNodeId, toLatticeId, toNodeId }]
              }
            ));
          }
        }
        strandDragging.current = null;
        setStrandPreview(null);
      }
      // Commit finished stroke
      if (isDrawing.current && currentStroke.current && drawToolRef.current !== "eraser") {
        const s = currentStroke.current;
        const isPerm = drawPermRef.current;
        if (!isPerm) {
          // Temporary stroke: remove it immediately on mouse-up
          setDrawStrokes(prev => prev.filter(x => x.id !== s.id));
        } else if (s.tool === "pen" && s.points.length < 2) {
          // Tiny dot — remove
          setDrawStrokes(prev => prev.filter(x => x.id !== s.id));
        } else {
          // Permanent: finalize and keep
          const finalStroke = { ...s, permanent: true };
          setDrawStrokes(prev => {
            const idx = prev.findIndex(x => x.id === finalStroke.id);
            return idx >= 0 ? prev.map((x, i) => i === idx ? finalStroke : x) : [...prev, finalStroke];
          });
        }
        currentStroke.current = null;
      }
      isDrawing.current = false;
      noteDragging.current = null;

      if (isPanning.current && !didDrag.current) setSelectedNodes({});
      if (isPanning.current) { isPanning.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
      nodeDragging.current = null;
      epicenterDragging.current = null;
      mouseDownPos.current = null;
      if (leftSplitDragging.current) { leftSplitDragging.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
      if (rightSplitDragging.current) { rightSplitDragging.current = false; document.body.style.cursor = ""; document.body.style.userSelect = ""; }
    };
    window.addEventListener("mousemove", onMove);
    window.addEventListener("mouseup", onUp);
    return () => { window.removeEventListener("mousemove", onMove); window.removeEventListener("mouseup", onUp); };
  }, []);

  // ── Middle-mouse pan — fires even over nodes/SVG elements ─────────
  useEffect(() => {
    const onMiddleDown = (e) => {
      if (e.button !== 1) return;
      if (!panelRef.current?.contains(e.target)) return;
      e.preventDefault();
      didDrag.current = false; didDragRef.current = false;
      isPanning.current = true;
      mouseDownPos.current = { x: e.clientX, y: e.clientY };
      panStart.current = { mouseX: e.clientX, mouseY: e.clientY, tx: cameraRef.current.tx, ty: cameraRef.current.ty };
      document.body.style.cursor = "grabbing";
      document.body.style.userSelect = "none";
    };
    window.addEventListener("mousedown", onMiddleDown);
    return () => window.removeEventListener("mousedown", onMiddleDown);
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
    const el = panelRef.current;
    if (!el) return;
    el.addEventListener("wheel", onWheel, { passive: false });
    return () => el.removeEventListener("wheel", onWheel);
  }, [onWheel]);

  // ── Escape key — clears draw tool, editing note, placing ─────────
  useEffect(() => {
    const onKey = (e) => {
      if (e.key === "Escape") {
        if (drawTool) setLastDrawTool(drawTool);
        setDrawTool(null);
        setColorPopOpen(false);
        setDrawMenuOpen(false);
        setDrawMenuHovered(null);
        setMorphBtnOpen(false);
        setMorphBtnHovered(null);
        setDrawStrokes(prev => prev.filter(s => s.permanent));
        setEditingNoteId(null);
        setPlacingLattice(null);
        setGhostMousePos(null);
      }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, []);
  const toggleLeft = () => {
    if (leftCollapsed) { setLeftW(leftWBeforeCollapse.current); setLeftCollapsed(false); }
    else { leftWBeforeCollapse.current = leftW; setLeftW(0); setLeftCollapsed(true); }
  };
  const toggleRight = () => {
    if (rightCollapsed) { setRightW(rightWBeforeCollapse.current); setRightCollapsed(false); }
    else { rightWBeforeCollapse.current = rightW; setRightW(0); setRightCollapsed(true); }
  };

  const onLeftSplit12 = useCallback((delta, h) => {
    if (!leftPane1Open || !leftPane2Open) return;
    const ratio = delta / (h || 600);
    const totalFlex = leftPane1Flex + leftPane2Flex;
    setLeftPane1Flex(f => Math.max(0.1, f + ratio * totalFlex));
    setLeftPane2Flex(f => Math.max(0.1, f - ratio * totalFlex));
  }, [leftPane1Open, leftPane2Open, leftPane1Flex, leftPane2Flex]);
  const onLeftSplit23 = useCallback((delta, h) => {
    if (!leftPane2Open || !leftPane3Open) return;
    const ratio = delta / (h || 600);
    const totalFlex = leftPane2Flex + leftPane3Flex;
    setLeftPane2Flex(f => Math.max(0.1, f + ratio * totalFlex));
    setLeftPane3Flex(f => Math.max(0.1, f - ratio * totalFlex));
  }, [leftPane2Open, leftPane3Open, leftPane2Flex, leftPane3Flex]);
  const onRightSplit12 = useCallback((delta, h) => {
    if (!rightPane1Open || !rightPane2Open) return;
    const ratio = delta / (h || 600);
    const totalFlex = rightPane1Flex + rightPane2Flex;
    setRightPane1Flex(f => Math.max(0.1, f + ratio * totalFlex));
    setRightPane2Flex(f => Math.max(0.1, f - ratio * totalFlex));
  }, [rightPane1Open, rightPane2Open, rightPane1Flex, rightPane2Flex]);
  const onRightSplit23 = useCallback((delta, h) => {
    if (!rightPane2Open || !rightPane3Open) return;
    const ratio = delta / (h || 600);
    const totalFlex = rightPane2Flex + rightPane3Flex;
    setRightPane2Flex(f => Math.max(0.1, f + ratio * totalFlex));
    setRightPane3Flex(f => Math.max(0.1, f - ratio * totalFlex));
  }, [rightPane2Open, rightPane3Open, rightPane2Flex, rightPane3Flex]);

  const toggleNodeSelect = useCallback((latticeId, nodeId) => {
    setSelectedNodes(prev => {
      const latticeSelection = prev[latticeId] || new Set();
      const next = new Set(latticeSelection);
      if (next.has(nodeId)) {
        next.delete(nodeId);
      } else {
        next.add(nodeId);
      }
      if (next.size === 0) {
        const { [latticeId]: _, ...rest } = prev;
        return rest;
      }
      return { ...prev, [latticeId]: next };
    });
    setSelectedGraphId(latticeId);
  }, []);

  const isNodeSelected = useCallback((latticeId, nodeId) => {
    return selectedNodes[latticeId]?.has(nodeId) || false;
  }, [selectedNodes]);

  const handleLoadState = useCallback((restored) => {
    setLattices(restored.lattices);
    setMorphisms(restored.morphisms);
    setNotes(restored.notes);
    setDrawStrokes(restored.drawStrokes);
    setNodeCustomStyles(restored.nodeCustomStyles);
    setGridSettings(restored.gridSettings);
    setCamera(restored.camera);
    setSettingsOpen(false);
  }, []);

  // ── Derived views ─────────────────────────────────────────────────
  const latticeViews = lattices.map((entry, idx) => {
    const rawNodes = resolveNodes(entry);
    // Apply any custom style overrides (color, labelAlias)
    const nodes = rawNodes.map(n => {
      const style = nodeCustomStyles[`${entry.id}:${n.id}`];
      if (!style) return n;
      return {
        ...n,
        ...(style.color ? { _customColor: style.color } : {}),
        ...(style.labelAlias ? { shortLabel: style.labelAlias } : {}),
      };
    });
    const colorMap = buildOrderColorMap(nodes);
    // For stats: always use the real (non-collapsed) base for order/counts
    const statsBase = entry.base;
    const fullNode = entry.isCollapsed
      ? statsBase.nodes[statsBase.nodes.length - 1] ?? null
      : nodes[nodes.length - 1] ?? null;
    const accent = LATTICE_ACCENTS[idx % LATTICE_ACCENTS.length];
    const hlEdgeSet = new Set();
    const adjacentNodes = new Set();
    // Only highlight edges when not collapsed
    if (!entry.isCollapsed) {
      entry.base.edges.forEach(([a, b], i) => {
        const ka = `${entry.id}:${a}`, kb = `${entry.id}:${b}`;
        if (isNodeSelected(entry.id, a) || isNodeSelected(entry.id, b)) { hlEdgeSet.add(i); adjacentNodes.add(a); adjacentNodes.add(b); }
      });
    }
    const unElems = entry.base.labels?.map((l, i) => ({ i, v: parseInt(l) })).filter(x => !isNaN(x.v) && entry.kind === "Un");
    const zParts = entry.kind === "Un" ? zStructureParts(entry.param) : [];
    const expVal = entry.kind === "Un" && unElems ? groupExponent(unElems.map(x => x.v).filter(v => v > 0), entry.param) : "—";
    return { entry, nodes, colorMap, fullNode, statsBase, accent, hlEdgeSet, adjacentNodes, zParts, expVal };
  });

  const allSelectedNodes = latticeViews.flatMap(({ entry, nodes, colorMap, fullNode }) => {
    const latticeSelectedNodes = selectedNodes[entry.id] || new Set();
    return [...latticeSelectedNodes].map(nodeId => {
      const node = nodes.find(n => n.id === nodeId);
      if (!node) return null;
      const indexVal = (fullNode && fullNode.order % node.order === 0) ? fullNode.order / node.order : "—";
      return { node, colorMap, latticeId: entry.id, latticeLabel: entry.label, indexVal, entry };
    }).filter(Boolean);
  });

  const totalSelected = Object.values(selectedNodes).reduce((sum, set) => sum + set.size, 0);

  const actualLeftW = leftCollapsed ? 0 : leftW;
  const actualRightW = rightCollapsed ? 0 : rightW;

  // ═════════════════════════════════════════════════════════════════
  //  RENDER
  // ═════════════════════════════════════════════════════════════════

  return (
    <div ref={containerRef} style={{
      width: "100%", height: "100vh", display: "flex", overflow: "hidden",
      fontFamily: "'Courier New', 'Lucida Console', monospace", background: C.bg,
    }}>
      <style>{`
        .sky-scroll::-webkit-scrollbar { width: 6px; height: 6px; }
        .sky-scroll::-webkit-scrollbar-track { background: ${C.panelBg}; }
        .sky-scroll::-webkit-scrollbar-thumb { background: ${C.border}; border-radius: 3px; }
        .sky-scroll::-webkit-scrollbar-thumb:hover { background: ${C.borderHover}; }
        .sky-scroll-left { direction: rtl; }
        .sky-scroll-left > * { direction: ltr; }
      `}</style>

      {showRawModal && (
        <RawTableModal
          onClose={() => setShowRawModal(false)}
          onSubmit={(rawData) => {
            try {
              const group = LATTICE_GROUPS.find(g => g.key === "Raw");
              const base = group.views[0].build(null, rawData);
              setShowRawModal(false);
              setPlacingLattice({ key: "Raw", base, label: `Raw(${base.param})` });
            } catch (e) { setError(String(e)); setShowRawModal(false); }
          }}
        />
      )}

      {/* ── Settings Modal ── */}
      <SettingsModal
        isOpen={settingsOpen}
        onClose={() => setSettingsOpen(false)}
        gridSettings={gridSettings}
        setGridSettings={setGridSettings}
        camera={camera}
        setCamera={setCamera}
        lattices={lattices}
        morphisms={morphisms}
        notes={notes}
        drawStrokes={drawStrokes}
        nodeCustomStyles={nodeCustomStyles}
        onLoadState={handleLoadState}
      />

      {/* ══════════════════════════════════════════════════════
          LEFT PANEL
      ══════════════════════════════════════════════════════ */}
      <div ref={leftPanelRef} style={{
        width: actualLeftW, flexShrink: 0, height: "100%",
        display: "flex", flexDirection: "column",
        background: C.panelBg, overflow: "visible",
        transition: leftSplitDragging.current ? "none" : "width 0.2s ease",
        position: "relative",
        borderRight: actualLeftW > 0 ? `1px solid ${C.border}` : "none",
      }}>
        <CollapseBtn collapsed={leftCollapsed} onToggle={toggleLeft} side="left" panelTitle="Catalog" />

        {actualLeftW > 40 && (
          <div style={{ flex: 1, minHeight: 0, display: "flex", flexDirection: "column", overflow: "hidden", clipPath: "inset(0)" }}>
          {/* Pane 1: Graph Catalog (categories → groups → views) */}
          <Pane title="Graph Catalog" open={leftPane1Open} onToggle={() => setLeftPane1Open(o => !o)} flex={leftPane1Flex} scrollClass="sky-scroll-left">
            <div style={{ margin: "-12px -14px" }}>
              {LATTICE_CATEGORIES.map(category => (
                <Section key={category.key} label={category.label} depth={0} defaultOpen={false}
                  badge={`${category.groups.reduce((s, g) => s + g.views.length, 0)}`}>
                  <SectionBody>
                    <div style={{ fontSize: 8, color: C.inkFaint, letterSpacing: 1, lineHeight: 1.6 }}>{category.desc}</div>
                  </SectionBody>
                  {category.groups.map(group => {
                    const param  = catalogParams[group.key]  ?? group.paramDefault;
                    const param2 = catalogParams2[group.key] ?? group.paramDefault2;
                    const param3 = catalogParams3[group.key] ?? group.paramDefault3;
                    const activeViewKey = selectedViews[group.key] ?? group.views[0].key;
                    const isPlacing = placingLattice?.groupKey === group.key;

                    return (
                      <Section key={group.key} label={group.label} depth={1} defaultOpen={false}
                        badge={group.views.length > 1 ? `${group.views.length} views` : undefined}>

                        {/* Param inputs */}
                        {(group.hasParam || group.hasParam2 || group.hasParam3) && (
                          <SectionBody>
                            <div style={{ display: "flex", alignItems: "center", gap: 8, flexWrap: "wrap" }}>
                              {group.hasParam && (
                                <div style={{ display: "flex", alignItems: "center", gap: 4 }}>
                                  <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1 }}>{group.paramLabel}</span>
                                  <input type="number" value={param} min={group.paramMin} max={group.paramMax}
                                    onChange={e => setCatalogParams(prev => ({ ...prev, [group.key]: parseInt(e.target.value) || group.paramDefault }))}
                                    style={{ width: 44, background: C.bg, border: `1px solid ${C.borderHover}`, borderRadius: 3, color: C.ink, fontSize: 11, padding: "2px 5px", textAlign: "center", fontFamily: "'Courier New', monospace", outline: "none" }} />
                                </div>
                              )}
                              {group.hasParam2 && (
                                <div style={{ display: "flex", alignItems: "center", gap: 4 }}>
                                  <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1 }}>{group.paramLabel2}</span>
                                  <input type="number" value={param2} min={group.paramMin2} max={group.paramMax2}
                                    onChange={e => setCatalogParams2(prev => ({ ...prev, [group.key]: parseInt(e.target.value) || group.paramDefault2 }))}
                                    style={{ width: 44, background: C.bg, border: `1px solid ${C.borderHover}`, borderRadius: 3, color: C.ink, fontSize: 11, padding: "2px 5px", textAlign: "center", fontFamily: "'Courier New', monospace", outline: "none" }} />
                                </div>
                              )}
                              {group.hasParam3 && (
                                <div style={{ display: "flex", alignItems: "center", gap: 4 }}>
                                  <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1 }}>{group.paramLabel3}</span>
                                  <input type="number" value={param3} min={group.paramMin3} max={group.paramMax3}
                                    onChange={e => setCatalogParams3(prev => ({ ...prev, [group.key]: parseInt(e.target.value) || group.paramDefault3 }))}
                                    style={{ width: 44, background: C.bg, border: `1px solid ${C.borderHover}`, borderRadius: 3, color: C.ink, fontSize: 11, padding: "2px 5px", textAlign: "center", fontFamily: "'Courier New', monospace", outline: "none" }} />
                                </div>
                              )}
                            </div>
                          </SectionBody>
                        )}

                        {/* Single element label input */}
                        {group.isSingle && (
                          <SectionBody>
                            <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                              <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1, flexShrink: 0 }}>Label</span>
                              <input
                                value={singleElementLabel}
                                onChange={e => setSingleElementLabel(e.target.value.slice(0, 12))}
                                placeholder="a"
                                style={{ flex: 1, background: C.bg, border: `1px solid ${C.borderHover}`, borderRadius: 3, color: C.ink, fontSize: 11, padding: "2px 7px", fontFamily: "'Courier New', monospace", outline: "none" }}
                              />
                            </div>
                          </SectionBody>
                        )}

                        {/* View selector rows */}
                        {group.views.map(view => {
                          const isActiveView = activeViewKey === view.key;
                          const isThisPlacing = isPlacing && placingLattice?.viewKey === view.key;
                          return (
                            <div key={view.key} style={{
                              display: "flex", alignItems: "center", gap: 8,
                              padding: "6px 12px",
                              borderBottom: `1px solid ${C.border}`,
                              background: isThisPlacing ? C.selectedBg : isActiveView ? "rgba(0,0,0,0.04)" : "transparent",
                              transition: "background 0.1s",
                            }}>
                              <div onClick={() => setSelectedViews(prev => ({ ...prev, [group.key]: view.key }))}
                                style={{
                                  width: 9, height: 9, borderRadius: "50%", flexShrink: 0, cursor: "pointer",
                                  border: `2px solid ${C.inkMid}`,
                                  background: isActiveView ? C.inkMid : "transparent",
                                  transition: "background 0.15s",
                                }} />
                              <span style={{ flex: 1, fontSize: 10, color: isActiveView ? C.ink : C.inkFaint, fontFamily: "'Courier New', monospace", letterSpacing: 1 }}>
                                {view.label}
                              </span>
                              <button title={`Place ${group.label} — ${view.label}`}
                                onClick={() => {
                                  try {
                                    if (group.isRaw) { setShowRawModal(true); return; }
                                    const p  = group.hasParam  ? (param  || group.paramDefault)  : group.paramDefault;
                                    const p2 = group.hasParam2 ? (param2 || group.paramDefault2) : undefined;
                                    const p3 = group.hasParam3 ? (param3 || group.paramDefault3) : undefined;
                                    const base = group.isSingle ? view.build(null, singleElementLabel || "a") : view.build(p, p2, p3);
                                    const viewSuffix = view.key !== "hasse" ? ` [${view.label}]` : "";
                                    const SUB = "₀₁₂₃₄₅₆₇₈₉";
                                    const sub = x => String(x).split("").map(d => SUB[parseInt(d)] ?? d).join("");
                                    let lbl = group.isSingle ? (singleElementLabel || "a") : group.label;
                                    if (group.hasParam)  lbl = lbl.replace(/ₙ/g, sub(p));
                                    if (group.hasParam2) lbl = lbl.replace(/ₘ/g, sub(p2));
                                    if (group.hasParam3) lbl = lbl.replace(/ₖ/g, sub(p3));
                                    lbl = lbl + viewSuffix;
                                    setError("");
                                    setSelectedViews(prev => ({ ...prev, [group.key]: view.key }));
                                    setPlacingLattice({ groupKey: group.key, viewKey: view.key, base, label: lbl, params: {param: p, param2: p2, param3: p3}});
                                  } catch (err) { setError(String(err)); }
                                }}
                                style={{
                                  width: 22, height: 22, borderRadius: "50%", flexShrink: 0,
                                  background: isThisPlacing ? C.ink : C.panelSurface,
                                  border: `1.5px solid ${isThisPlacing ? C.ink : C.border}`,
                                  cursor: "pointer", display: "flex", alignItems: "center", justifyContent: "center",
                                  color: isThisPlacing ? C.panelBg : C.inkMid, fontSize: 11, lineHeight: 1,
                                  transition: "background 0.13s, border-color 0.13s",
                                }}
                                onMouseEnter={e => { if (!isThisPlacing) { e.currentTarget.style.background = C.borderHover; e.currentTarget.style.borderColor = C.borderHover; } }}
                                onMouseLeave={e => { if (!isThisPlacing) { e.currentTarget.style.background = C.panelSurface; e.currentTarget.style.borderColor = C.border; } }}
                              >☉</button>
                            </div>
                          );
                        })}

                        <SectionBody>
                          <div style={{ fontSize: 8, color: C.inkFaint, letterSpacing: 1, lineHeight: 1.6 }}>{group.desc}</div>
                        </SectionBody>
                      </Section>
                    );
                  })}
                </Section>
              ))}
            </div>
            {error && <div style={{ color: "#f87171", fontSize: 10, margin: "8px 14px 0" }}>{error}</div>}
          </Pane>

          {leftPane1Open && leftPane2Open && <HPSplitter onDrag={onLeftSplit12} containerRef={leftPanelRef} />}

          {/* Pane 2: Morphisms */}
          <Pane title="Morphisms" open={leftPane2Open} onToggle={() => setLeftPane2Open(o => !o)} flex={leftPane2Flex} scrollClass="sky-scroll-left">
            {morphisms.length === 0
              ? <div style={{ fontSize: 11, color: C.inkFaint, fontStyle: "italic", padding: "4px 0" }}>No morphisms yet. Use the Ψ button on the canvas to create one.</div>
              : <div style={{ margin: "-12px -14px" }}>

                  {/* Individual morphisms — with radio select on the header row */}
                  {morphisms.map(m => {
                    const isActive = activeMorphismId === m.id;
                    const isSelected = selectedMorphismNodes.has(m.id);
                    const analysis = analyzeMorphism(m.strands, lattices, latticeViews);

                    return (
                      <Section key={m.id} label={m.name} depth={0} accent={m.color}
                        badge={m.strands.length ? `${m.strands.length}s` : undefined}
                        defaultOpen={false}
                        rightExtra={
                          /* Radio/checkbox to select this morphism for compose */
                          <div title={isSelected ? "Deselect for compose" : "Select for compose"}
                            onClick={e => { e.stopPropagation(); setSelectedMorphismNodes(prev => { const next = new Set(prev); next.has(m.id) ? next.delete(m.id) : next.add(m.id); return next; }); }}
                            style={{
                              width: 14, height: 14, borderRadius: "50%", flexShrink: 0,
                              border: `2px solid ${m.color}`,
                              background: isSelected ? m.color : "transparent",
                              cursor: "pointer", transition: "background 0.15s",
                              marginRight: 4,
                            }} />
                        }>

                        {/* ── Style (rename + color + active + description) ── */}
                        <Section label="Style" depth={1} defaultOpen={false}>
                          <SectionBody>
                            <div style={{ display: "flex", flexDirection: "column", gap: 8 }}>
                              {/* Name row */}
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 8, letterSpacing: 1.5, color: C.inkFaint, textTransform: "uppercase", minWidth: 38, flexShrink: 0 }}>Name</span>
                                <input value={m.name}
                                  onChange={e => setMorphisms(prev => prev.map(mx => mx.id === m.id ? { ...mx, name: e.target.value } : mx))}
                                  style={{ flex: 1, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 3, color: C.ink, fontSize: 10, padding: "3px 6px", outline: "none", fontFamily: "'Courier New', monospace" }} />
                              </div>
                              {/* Color row */}
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 8, letterSpacing: 1.5, color: C.inkFaint, textTransform: "uppercase", minWidth: 38, flexShrink: 0 }}>Color</span>
                                <div style={{ display: "flex", gap: 5, flexWrap: "wrap" }}>
                                  {MORPHISM_COLORS.map(col => (
                                    <div key={col} onClick={() => setMorphisms(prev => prev.map(mx => mx.id === m.id ? { ...mx, color: col } : mx))}
                                      style={{ width: 16, height: 16, borderRadius: "50%", background: col, cursor: "pointer", flexShrink: 0,
                                        border: m.color === col ? `2.5px solid ${C.inkMid}` : `1.5px solid transparent`,
                                        boxSizing: "border-box", transition: "border 0.1s" }} />
                                  ))}
                                </div>
                              </div>
                              {/* Active toggle */}
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 8, letterSpacing: 1.5, color: C.inkFaint, textTransform: "uppercase", minWidth: 38, flexShrink: 0 }}>Active</span>
                                <div title={isActive ? "Deactivate morphism" : "Activate to draw strands"}
                                  onClick={() => setActiveMorphismId(isActive ? null : m.id)}
                                  style={{ width: 14, height: 14, borderRadius: "50%", flexShrink: 0,
                                    border: `2px solid ${m.color}`, background: isActive ? m.color : "transparent",
                                    cursor: "pointer", transition: "background 0.15s" }} />
                                {isActive && <span style={{ fontSize: 9, color: m.color, letterSpacing: 1, textTransform: "uppercase" }}>drawing strands</span>}
                              </div>
                            </div>
                          </SectionBody>
                          <SectionBody>
                            <textarea placeholder="Add notes about this morphism…"
                              value={m.description ?? ""}
                              onChange={e => setMorphisms(prev => prev.map(mx => mx.id === m.id ? { ...mx, description: e.target.value } : mx))}
                              style={{ width: "100%", minHeight: 56, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 3, color: C.ink, fontSize: 10, padding: "5px 7px", outline: "none", resize: "vertical", boxSizing: "border-box", fontFamily: "'Courier New', monospace", lineHeight: 1.5 }} />
                          </SectionBody>
                          <SectionBody>
                            <button onClick={() => { setMorphisms(prev => prev.filter(x => x.id !== m.id)); if (activeMorphismId === m.id) setActiveMorphismId(null); setSelectedMorphismNodes(prev => { const n = new Set(prev); n.delete(m.id); return n; }); }}
                              style={{ width: "100%", padding: "4px 0", background: "transparent", border: `1px solid #fca5a5`, borderRadius: 3, color: "#ef4444", fontSize: 9, letterSpacing: 1.5, textTransform: "uppercase", fontFamily: "'Courier New', monospace", cursor: "pointer" }}
                              onMouseEnter={e => { e.currentTarget.style.background = "#fef2f2"; }}
                              onMouseLeave={e => { e.currentTarget.style.background = "transparent"; }}>
                              Delete Morphism
                            </button>
                          </SectionBody>
                        </Section>

                        {m.strands.length > 0 && (
                          <Section label="Strands" depth={1} defaultOpen={false} badge={m.strands.length}>
                            {analysis.strandLabels.map((sl, i) => {
                              const strand = m.strands[i];
                              const srcLV = latticeViews.find(lv => lv.entry.id === strand.fromLatticeId);
                              const tgtLV = latticeViews.find(lv => lv.entry.id === strand.toLatticeId);
                              const srcNode = srcLV?.nodes.find(n => n.id === strand.fromNodeId);
                              const tgtNode = tgtLV?.nodes.find(n => n.id === strand.toNodeId);
                              return (
                                <div key={strand.id}>
                                  <div style={{ padding: "5px 12px", borderBottom: `1px solid ${C.border}`, display: "flex", alignItems: "center", gap: 6 }}>
                                    <div style={{ width: 7, height: 7, borderRadius: "50%", background: m.color, flexShrink: 0 }} />
                                    <div style={{ flex: 1, minWidth: 0 }}>
                                      <div style={{ fontSize: 10, color: C.ink, fontFamily: "'Courier New', monospace", whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>{sl.from}</div>
                                      <div style={{ fontSize: 9, color: C.inkFaint, marginTop: 1 }}>↓ {sl.to}</div>
                                    </div>
                                    <div style={{ display: "flex", alignItems: "center", gap: 4, flexShrink: 0 }}>
                                      <span style={{ fontSize: 9, color: C.inkFaint }}>{sl.fromOrder}→{sl.toOrder}</span>
                                      <button onClick={() => setMorphisms(prev => prev.map(mx =>
                                        mx.id !== m.id ? mx : { ...mx, strands: mx.strands.filter(s => s.id !== strand.id) }
                                      ))} style={{ background: "none", border: "none", cursor: "pointer", color: C.inkFaint, fontSize: 13, padding: "0 2px", lineHeight: 1 }}>×</button>
                                    </div>
                                  </div>
                                </div>
                              );
                            })}
                            {analysis.kernel.length > 0 && (
                              <Section label="Kernel" depth={2} defaultOpen={false} badge={analysis.kernel.length}>
                                <SectionBody>
                                  <div style={{ display: "flex", flexWrap: "wrap", gap: 3 }}>
                                    {analysis.kernel.map((el, i) => (
                                      <span key={i} style={{ fontSize: 10, color: C.inkMid, fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "1px 5px", border: `1px solid ${C.border}` }}>{el}</span>
                                    ))}
                                  </div>
                                </SectionBody>
                              </Section>
                            )}
                            {analysis.image.length > 0 && (
                              <Section label="Image" depth={2} defaultOpen={false} badge={analysis.image.length}>
                                <SectionBody>
                                  <div style={{ display: "flex", flexWrap: "wrap", gap: 3 }}>
                                    {analysis.image.map((el, i) => (
                                      <span key={i} style={{ fontSize: 10, color: m.color, fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "1px 5px", border: `1px solid ${C.border}` }}>{el}</span>
                                    ))}
                                  </div>
                                </SectionBody>
                              </Section>
                            )}
                          </Section>
                        )}
                      </Section>
                    );
                  })}

                  {/* ── Combine / Intersect selected morphisms ── */}
                  {(() => {
                    const selNodes = [...selectedMorphismNodes].filter(id => morphisms.some(m => m.id === id));
                    if (selNodes.length < 2) return null;
                    const selMorphisms = selNodes.map(id => morphisms.find(m => m.id === id)).filter(Boolean);

                    const doCombine = () => {
                      // Union: all strands from all selected morphisms
                      const strands = selMorphisms.flatMap(m => m.strands.map(s => ({ ...s, id: Date.now() + Math.random() })));
                      if (!strands.length) return;
                      const newId = Date.now();
                      const color = MORPHISM_COLORS[morphisms.length % MORPHISM_COLORS.length];
                      setMorphisms(prev => [...prev, { id: newId, name: selMorphisms.map(m => m.name).join("+"), color, strands, description: "" }]);
                      setActiveMorphismId(newId); setSelectedMorphismNodes(new Set());
                    };

                    const doIntersect = () => {
                      // Intersection: only strands present (same from+to pair) in ALL selected morphisms
                      const strandKey = s => `${s.fromLatticeId}:${s.fromNodeId}→${s.toLatticeId}:${s.toNodeId}`;
                      const sets = selMorphisms.map(m => new Set(m.strands.map(strandKey)));
                      const refStrands = selMorphisms[0].strands;
                      const shared = refStrands.filter(s => sets.slice(1).every(set => set.has(strandKey(s))));
                      if (!shared.length) return;
                      const newId = Date.now();
                      const color = MORPHISM_COLORS[morphisms.length % MORPHISM_COLORS.length];
                      setMorphisms(prev => [...prev, { id: newId, name: selMorphisms.map(m => m.name).join("∩"), color, strands: shared.map(s => ({ ...s, id: Date.now() + Math.random() })), description: "" }]);
                      setActiveMorphismId(newId); setSelectedMorphismNodes(new Set());
                    };

                    return (
                      <div style={{ borderTop: `1px solid ${C.border}`, padding: "10px 14px", display: "flex", flexDirection: "column", gap: 6 }}>
                        <div style={{ display: "flex", flexWrap: "wrap", gap: 4, marginBottom: 2 }}>
                          {selNodes.map(id => { const m = morphisms.find(x => x.id === id); return m ? (
                            <span key={id} style={{ padding: "2px 7px", borderRadius: 10, fontSize: 9, background: m.color, color: "#fff", fontFamily: "'Courier New', monospace" }}>{m.name}</span>
                          ) : null; })}
                        </div>
                        <div style={{ display: "flex", gap: 6 }}>
                          <button onClick={doCombine} style={{
                            flex: 1, padding: "5px 0", background: C.inkMid, border: "none", borderRadius: 4,
                            color: C.panelBg, fontSize: 9, letterSpacing: 1.5, textTransform: "uppercase",
                            fontFamily: "'Courier New', monospace", cursor: "pointer",
                          }}>Combine +</button>
                          <button onClick={doIntersect} style={{
                            flex: 1, padding: "5px 0", background: "transparent", border: `1px solid ${C.border}`, borderRadius: 4,
                            color: C.inkMid, fontSize: 9, letterSpacing: 1.5, textTransform: "uppercase",
                            fontFamily: "'Courier New', monospace", cursor: "pointer",
                          }}
                            onMouseEnter={e => e.currentTarget.style.background = C.selectedBg}
                            onMouseLeave={e => e.currentTarget.style.background = "transparent"}>Intersect ∩</button>
                        </div>
                      </div>
                    );
                  })()}


                </div>
            }
          </Pane>

          </div>
        )}

        {/* App name + settings — always pinned at bottom of left panel */}
        <div style={{
          flexShrink: 0, borderTop: `2px solid ${C.border}`,
          background: C.panelBg, padding: "7px 10px",
          display: "flex", alignItems: "center", gap: 8,
          minHeight: 38,
        }}>
          {actualLeftW > 40 && <>
            <svg width="16" height="16" viewBox="0 0 16 16" fill="none" style={{ flexShrink: 0 }}>
              <rect x="2" y="2" width="5" height="5" rx="1.2" fill={C.inkMid} opacity="0.7"/>
              <rect x="9" y="2" width="5" height="5" rx="1.2" fill={C.inkMid} opacity="0.5"/>
              <rect x="2" y="9" width="5" height="5" rx="1.2" fill={C.inkMid} opacity="0.5"/>
              <rect x="9" y="9" width="5" height="5" rx="1.2" fill={C.inkMid} opacity="0.9"/>
            </svg>
            <span style={{ fontSize: 9, letterSpacing: 3, fontWeight: "700", color: C.inkMid, textTransform: "uppercase", fontFamily: "'Courier New', monospace", flex: 1, whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>
              Psinite
            </span>
            <button onClick={() => setSettingsOpen(true)} title="Settings"
              style={{ width: 24, height: 24, borderRadius: 5, flexShrink: 0, background: "none", border: `1px solid ${C.border}`, cursor: "pointer", display: "flex", alignItems: "center", justifyContent: "center", transition: "background 0.1s" }}
              onMouseEnter={e => { e.currentTarget.style.background = C.selectedBg; }}
              onMouseLeave={e => { e.currentTarget.style.background = "none"; }}
            >
              <svg width="13" height="13" viewBox="0 0 13 13" fill="none">
                <circle cx="6.5" cy="6.5" r="2" stroke={C.inkMid} strokeWidth="1.2"/>
                <path d="M6.5 1.5V2.5M6.5 10.5V11.5M1.5 6.5H2.5M10.5 6.5H11.5M3 3L3.7 3.7M9.3 9.3L10 10M3 10L3.7 9.3M9.3 3.7L10 3" stroke={C.inkMid} strokeWidth="1.2" strokeLinecap="round"/>
              </svg>
            </button>
          </>}
        </div>
      </div>
      <VSplitter onMouseDown={(e) => {
        e.preventDefault(); leftSplitDragging.current = true; leftSplitStart.current = e.clientX;
        document.body.style.cursor = "col-resize"; document.body.style.userSelect = "none";
        if (leftCollapsed) { setLeftCollapsed(false); setLeftW(leftWBeforeCollapse.current); }
      }} />

      {/* ══════════════════════════════════════════════════════
          CANVAS
      ══════════════════════════════════════════════════════ */}
      <div ref={panelRef} style={{
        flex: 1, height: "100%", position: "relative", overflow: "hidden", background: C.bg,
        ...(gridSettings.pattern === "none" ? {} : gridSettings.pattern === "dots" ? {
          backgroundImage: `radial-gradient(circle, ${gridSettings.color} 1.5px, transparent 1.5px)`,
          backgroundSize: `${gridSettings.size * camera.scale}px ${gridSettings.size * camera.scale}px`,
          backgroundPosition: `${camera.tx}px ${camera.ty}px`,
        } : gridSettings.pattern === "cross" ? {
          backgroundImage: `linear-gradient(to right, ${gridSettings.color} 1px, transparent 1px), linear-gradient(to bottom, ${gridSettings.color} 1px, transparent 1px), linear-gradient(to right, transparent calc(50% - 0.5px), ${gridSettings.color} calc(50% - 0.5px), ${gridSettings.color} calc(50% + 0.5px), transparent calc(50% + 0.5px)), linear-gradient(to bottom, transparent calc(50% - 0.5px), ${gridSettings.color} calc(50% - 0.5px), ${gridSettings.color} calc(50% + 0.5px), transparent calc(50% + 0.5px))`,
          backgroundSize: `${gridSettings.size * camera.scale * 2}px ${gridSettings.size * camera.scale * 2}px`,
          backgroundPosition: `${camera.tx}px ${camera.ty}px`,
        } : {
          backgroundImage: `linear-gradient(to right, ${gridSettings.color} 1px, transparent 1px), linear-gradient(to bottom, ${gridSettings.color} 1px, transparent 1px)`,
          backgroundSize: `${gridSettings.size * camera.scale}px ${gridSettings.size * camera.scale}px`,
          backgroundPosition: `${camera.tx}px ${camera.ty}px`,
        }),
        cursor: placingLattice ? "crosshair" : drawTool === "eraser" ? "cell" : drawTool ? "crosshair" : "grab",
      }} onMouseDown={onCanvasMouseDown} onAuxClick={e => e.preventDefault()}>

        {placingLattice && (
          <div style={{ position: "absolute", inset: 0, zIndex: 20, pointerEvents: "none", display: "flex", alignItems: "flex-start", justifyContent: "center", paddingTop: 18 }}>
            <div style={{ background: C.ink, color: C.panelBg, borderRadius: 6, padding: "7px 16px", fontSize: 10, letterSpacing: 2.5, textTransform: "uppercase", fontFamily: "'Courier New', monospace", boxShadow: "0 2px 12px rgba(0,0,0,0.18)" }}>
              ☉ click to place {placingLattice.label}
            </div>
          </div>
        )}
        {placingLattice && (
          <div data-cancel="true" onClick={() => { setPlacingLattice(null); setGhostMousePos(null); }}
            style={{ position: "absolute", top: 16, left: 16, zIndex: 21, background: C.border, border: "none", borderRadius: 4, cursor: "pointer", padding: "4px 10px", fontSize: 9, color: C.ink, letterSpacing: 2, textTransform: "uppercase", fontFamily: "'Courier New', monospace" }}>cancel</div>
        )}

        {/* Ghost preview overlay */}
        {placingLattice && ghostMousePos && (() => {
          const cam = camera;
          const wx = (ghostMousePos.x - cam.tx) / cam.scale;
          const wy = (ghostMousePos.y - cam.ty) / cam.scale;
          const base = placingLattice.base;
          const offsetX = wx - base.W / 2;
          const offsetY = wy - base.H / 2;
          return (
            <svg style={{ position: "absolute", inset: 0, width: "100%", height: "100%", pointerEvents: "none", zIndex: 15, overflow: "visible" }}>
              <g transform={`translate(${cam.tx}, ${cam.ty}) scale(${cam.scale})`} opacity={0.38}>
                <g transform={`translate(${offsetX}, ${offsetY})`}>
                  {base.edges.map(([a, b], i) => {
                    const na = base.nodes[a], nb = base.nodes[b];
                    if (!na || !nb) return null;
                    return <line key={i} x1={na.x} y1={na.y} x2={nb.x} y2={nb.y} stroke="#4a88aa" strokeWidth={1.5} strokeLinecap="round" />;
                  })}
                  {base.nodes.map((node, i) => (
                    <g key={i}>
                      {node.shape === "circle"   && <circle cx={node.x} cy={node.y} r={26} fill="#B7D0DE" stroke="#4a88aa" strokeWidth={1.5} />}
                      {node.shape === "square"   && <rect x={node.x - 21} y={node.y - 21} width={42} height={42} rx={3} fill="#B7D0DE" stroke="#4a88aa" strokeWidth={1.5} />}
                      {node.shape === "triangle" && <polygon points={`${node.x},${node.y - 25} ${node.x - 22},${node.y + 18} ${node.x + 22},${node.y + 18}`} fill="#B7D0DE" stroke="#4a88aa" strokeWidth={1.5} />}
                    </g>
                  ))}
                </g>
              </g>
            </svg>
          );
        })()}

        {lattices.length === 0 && !placingLattice && (
          <div style={{ position: "absolute", inset: 0, display: "flex", alignItems: "center", justifyContent: "center", pointerEvents: "none" }}>
            <span style={{ fontSize: 11, letterSpacing: 4, color: C.inkFaint, textTransform: "uppercase" }}>Add a lattice to begin</span>
          </div>
        )}

        {/* Main SVG */}
        <svg style={{ position: "absolute", inset: 0, width: "100%", height: "100%", overflow: "visible" }}>
          <defs>
            <marker id="arr" markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
              <path d="M0,0 L0,6 L6,3 Z" fill={C.inkMid} opacity="0.6" />
            </marker>
            {latticeViews.map(({ entry, colorMap }) =>
              Object.entries(colorMap).map(([ord, col]) => (
                <marker key={`arr-${entry.id}-${ord}`} id={`arr-${entry.id}-${ord}`} markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                  <path d="M0,0 L0,6 L6,3 Z" fill={col} />
                </marker>
              ))
            )}
          </defs>

          <g transform={`translate(${camera.tx}, ${camera.ty}) scale(${camera.scale})`}>
            {latticeViews.map(({ entry, nodes, colorMap, accent, hlEdgeSet, adjacentNodes }) => (
              <g key={entry.id}>
                {entry.showEdges && !entry.isCollapsed && entry.base.edges.map(([a, b], i) => {
                  const na = nodes[a], nb = nodes[b];
                  if (!na || !nb) return null;
                  const hl = hlEdgeSet.has(i);
                  const col = hl ? orderColor(na.order, colorMap) : "#9aaa88";
                  const sw = hl ? 2.5 : 1.4;
                  const mx = (na.x + nb.x) / 2, my = (na.y + nb.y) / 2;
                  const markerId = hl ? `arr-${entry.id}-${na.order}` : "arr";
                  return (
                    <g key={i}>
                      <line x1={na.x} y1={na.y} x2={nb.x} y2={nb.y} stroke={col} strokeWidth={sw} opacity={hl ? 1 : 0.6} strokeLinecap="round" />
                      {entry.showArrows && (
                        <line x1={mx - (nb.x - na.x) * 0.001} y1={my - (nb.y - na.y) * 0.001}
                          x2={mx + (nb.x - na.x) * 0.001} y2={my + (nb.y - na.y) * 0.001}
                          stroke={col} strokeWidth={sw} strokeLinecap="round"
                          markerEnd={`url(#${markerId})`} opacity={hl ? 1 : 0.5} />
                      )}
                    </g>
                  );
                })}
                {nodes.map(node => <ShapeOccluder key={`occ-${entry.id}-${node.id}`} node={node} R={26} />)}
                {nodes.map(node => {
                  const key = `${entry.id}:${node.id}`;
                  return (
                    <ShapeNode key={key} node={node} latticeId={entry.id} colorMap={colorMap}
                      isSelected={isNodeSelected(entry.id, node.id)}
                      isAdjacent={adjacentNodes.has(node.id) && !isNodeSelected(entry.id, node.id)}
                      isDrawMode={activeMorphismId !== null}
                      onToggleSelect={nodeId => toggleNodeSelect(entry.id, nodeId)}
                      onMouseDown={(nodeId, e) => onNodeMouseDown(entry.id, nodeId, e)} />
                  );
                })}
                {entry.showEpicenter && (
                  <Epicenter x={entry.epicenter.x} y={entry.epicenter.y} accent={accent} cameraScale={camera.scale} onMouseDown={(e) => onEpicenterMouseDown(entry.id, e)} />
                )}
              </g>
            ))}
          </g>

          {/* ── Draw strokes layer (world-space, inside camera transform) ── */}
          <g transform={`translate(${camera.tx}, ${camera.ty}) scale(${camera.scale})`} style={{ pointerEvents: "none" }}>
            <defs>
              <marker id="draw-arrow-end" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
                <path d="M0,0 L0,6 L7,3 Z" fill={drawColor} />
              </marker>
              <marker id="draw-arrow-start" markerWidth="8" markerHeight="8" refX="1" refY="3" orient="auto-start-reverse">
                <path d="M0,0 L0,6 L7,3 Z" fill={drawColor} />
              </marker>
            </defs>
            {drawStrokes.map(s => {
              if (s.tool === "pen") {
                if (s.points.length < 2) return null;
                const d = "M " + s.points.map(([x, y]) => `${x},${y}`).join(" L ");
                return <path key={s.id} d={d} stroke={s.color} strokeWidth={s.size} fill="none" strokeLinecap="round" strokeLinejoin="round" />;
              }
              if (s.tool === "line") {
                const mEnd = s.lineStyle === "arrow-end" || s.lineStyle === "arrow-both" ? "url(#draw-arrow-end)" : undefined;
                const mStart = s.lineStyle === "arrow-start" || s.lineStyle === "arrow-both" ? "url(#draw-arrow-start)" : undefined;
                return <line key={s.id} x1={s.x1} y1={s.y1} x2={s.x2} y2={s.y2} stroke={s.color} strokeWidth={s.size} strokeLinecap="round" markerEnd={mEnd} markerStart={mStart} />;
              }
              if (s.tool === "rect") {
                const x = Math.min(s.x1, s.x2), y = Math.min(s.y1, s.y2);
                const w = Math.abs(s.x2 - s.x1), h = Math.abs(s.y2 - s.y1);
                return <rect key={s.id} x={x} y={y} width={w} height={h} stroke={s.color} strokeWidth={s.size} fill="none" rx={2} />;
              }
              if (s.tool === "circle") {
                const cx = (s.x1 + s.x2) / 2, cy = (s.y1 + s.y2) / 2;
                const rx = Math.abs(s.x2 - s.x1) / 2, ry = Math.abs(s.y2 - s.y1) / 2;
                return <ellipse key={s.id} cx={cx} cy={cy} rx={Math.max(rx, 1)} ry={Math.max(ry, 1)} stroke={s.color} strokeWidth={s.size} fill="none" />;
              }
              if (s.tool === "triangle") {
                const mx = (s.x1 + s.x2) / 2;
                const pts = `${mx},${s.y1} ${s.x2},${s.y2} ${s.x1},${s.y2}`;
                return <polygon key={s.id} points={pts} stroke={s.color} strokeWidth={s.size} fill="none" strokeLinejoin="round" />;
              }
              return null;
            })}
          </g>
        </svg>

          {/* ── Strand overlay — above all nodes ── */}
          <svg style={{ position: "absolute", inset: 0, width: "100%", height: "100%", pointerEvents: "none", overflow: "visible" }}>
          <defs>
            {morphisms.map(m => (
              <marker key={m.id} id={`sarr-${m.id}`} markerWidth="9" markerHeight="9" refX="7" refY="3.5" orient="auto">
                <path d="M0,0 L0,7 L8,3.5 Z" fill={m.color} opacity={activeMorphismId === m.id ? 1 : 0.38} />
              </marker>
            ))}
            <marker id="sarr-preview" markerWidth="9" markerHeight="9" refX="7" refY="3.5" orient="auto">
              <path d="M0,0 L0,7 L8,3.5 Z" fill={C.inkFaint} />
            </marker>
          </defs>

          {morphisms.flatMap(m => {
            const isActive = activeMorphismId === m.id;
            const isPanelSelected = selectedMorphismNodes.has(m.id);
            return m.strands.map(s => {
              const srcLV = latticeViews.find(lv => lv.entry.id === s.fromLatticeId);
              const tgtLV = latticeViews.find(lv => lv.entry.id === s.toLatticeId);
              if (!srcLV || !tgtLV) return null;
              const srcNode = srcLV.nodes.find(n => n.id === s.fromNodeId);
              const tgtNode = tgtLV.nodes.find(n => n.id === s.toNodeId);
              if (!srcNode || !tgtNode) return null;

              const cam = camera;
              const x1s = srcNode.x * cam.scale + cam.tx, y1s = srcNode.y * cam.scale + cam.ty;
              const x2s = tgtNode.x * cam.scale + cam.tx, y2s = tgtNode.y * cam.scale + cam.ty;
              const nodeR = 26 * cam.scale;

              // Direction and distance
              const dx = x2s - x1s, dy = y2s - y1s;
              const len = Math.sqrt(dx * dx + dy * dy) || 1;

              // Trim endpoints at node borders
              const x1 = x1s + (dx / len) * nodeR * 1.05;
              const y1 = y1s + (dy / len) * nodeR * 1.05;
              const x2 = x2s - (dx / len) * nodeR * 1.05;
              const y2 = y2s - (dy / len) * nodeR * 1.05;

              // Check if there is an edge between these two nodes (only if same lattice)
              let useArc = false;
              if (s.fromLatticeId === s.toLatticeId) {
                const edges = srcLV.entry.base.edges;
                const exists = edges.some(([a, b]) =>
                  (a === s.fromNodeId && b === s.toNodeId) ||
                  (a === s.toNodeId && b === s.fromNodeId)
                );
                if (exists) useArc = true;
              }

              let pathD;
              if (useArc) {
                // Quadratic bezier with control point offset perpendicular to the line
                const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
                // Scale arc offset based on distance (but cap it)
                const arc = Math.min(80, len * 0.25); // reduced offset for gentler curve
                const cpx = mx - (dy / len) * arc;
                const cpy = my + (dx / len) * arc;
                pathD = `M ${x1} ${y1} Q ${cpx} ${cpy} ${x2} ${y2}`;
              } else {
                pathD = `M ${x1} ${y1} L ${x2} ${y2}`;
              }

              // Determine styling
              const lit = isActive || isPanelSelected;
              const color = m.color;
              const width = lit ? 2.6 : 1.6;
              const opacity = lit ? 1 : 0.38;
              const dash = lit ? undefined : "6 4";

              return (
                <g key={`${m.id}-${s.id}`}>
                  {lit && (
                    <path
                      d={pathD}
                      stroke={color}
                      strokeWidth={isActive ? 7 : 5}
                      fill="none"
                      opacity={isActive ? 0.18 : 0.28}
                      strokeLinecap="round"
                    />
                  )}
                  <path
                    d={pathD}
                    stroke={color}
                    strokeWidth={width}
                    fill="none"
                    opacity={opacity}
                    strokeDasharray={dash}
                    markerEnd={`url(#sarr-${m.id})`}
                  />
                </g>
              );
            });
          })}

          {strandPreview && (() => {
            const { x1, y1, x2, y2 } = strandPreview;
            const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
            const dx = x2 - x1, dy = y2 - y1;
            const len = Math.sqrt(dx * dx + dy * dy) || 1;
            const arc = Math.min(70, len * 0.32);
            const cpx = mx - (dy / len) * arc, cpy = my + (dx / len) * arc;
            return <path d={`M ${x1} ${y1} Q ${cpx} ${cpy} ${x2} ${y2}`} stroke={C.inkFaint} strokeWidth={1.6} fill="none" strokeDasharray="7 4" opacity={0.65} markerEnd="url(#sarr-preview)" />;
          })()}
          </svg>

        {/* ── Notes layer ── */}
        {notes.map(note => {
          const sx = note.x * camera.scale + camera.tx;
          const sy = note.y * camera.scale + camera.ty;
          const sw = Math.max(140, note.w * camera.scale);
          const sh = Math.max(72, note.h * camera.scale);
          const isEditing = editingNoteId === note.id;
          const isCollapsed = collapsedNotes.has(note.id);
          const fs = Math.min(13, Math.max(9, 11 * camera.scale));
          const titleH = Math.max(22, 26 * camera.scale);
          return (
            <div key={note.id} data-note="true" style={{
              position: "absolute", left: sx, top: sy,
              width: isCollapsed ? titleH : sw,
              height: isCollapsed ? titleH : (isEditing ? Math.max(sh, 100) : sh),
              background: "#fff",
              border: `1.5px solid ${isEditing ? C.selectedBord : C.border}`,
              borderRadius: isCollapsed ? 8 : 5,
              boxShadow: isEditing
                ? `0 4px 18px rgba(11,21,30,0.16), 0 0 0 2px ${C.selectedBg}`
                : "0 2px 8px rgba(11,21,30,0.10)",
              zIndex: isEditing ? 15 : 10,
              cursor: isEditing ? "default" : "grab",
              display: "flex", flexDirection: isCollapsed ? "row" : "column",
              overflow: "hidden",
              transition: "width 0.15s ease, height 0.15s ease, box-shadow 0.15s, border-color 0.15s, border-radius 0.15s",
              userSelect: isEditing ? "text" : "none",
              fontFamily: "'Courier New', monospace",
            }}
              onMouseDown={e => {
                if (isEditing) return;
                e.preventDefault(); e.stopPropagation();
                noteDragging.current = { id: note.id, startMx: e.clientX, startMy: e.clientY, startX: note.x, startY: note.y };
              }}
              onDoubleClick={e => {
                e.stopPropagation();
                if (!isCollapsed) setEditingNoteId(note.id);
              }}
            >
              {isCollapsed ? (
                /* Collapsed pill — just the note icon, click to expand */
                <div
                  onMouseDown={e => e.stopPropagation()}
                  onClick={e => { e.stopPropagation(); setCollapsedNotes(prev => { const n = new Set(prev); n.delete(note.id); return n; }); }}
                  style={{ width: "100%", height: "100%", display: "flex", alignItems: "center", justifyContent: "center", cursor: "pointer" }}
                  title="Expand note"
                >
                  <svg width="14" height="14" viewBox="0 0 18 18" fill="none">
                    <rect x="2.5" y="2.5" width="13" height="13" rx="2" stroke={C.inkMid} strokeWidth="1.4"/>
                    <line x1="5.5" y1="7" x2="12.5" y2="7" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
                    <line x1="5.5" y1="9.5" x2="12.5" y2="9.5" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
                    <line x1="5.5" y1="12" x2="9.5" y2="12" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
                  </svg>
                </div>
              ) : (
                <>
                  {/* Title bar */}
                  <div style={{
                    height: titleH, background: C.paneHeader,
                    borderBottom: `1px solid ${C.border}`,
                    display: "flex", alignItems: "center", gap: 4,
                    padding: `0 ${Math.max(4, 5 * camera.scale)}px`,
                    flexShrink: 0, cursor: "grab",
                  }}>
                    {/* Collapse button */}
                    <button onMouseDown={e => e.stopPropagation()}
                      onClick={e => { e.stopPropagation(); if (isEditing) setEditingNoteId(null); setCollapsedNotes(prev => { const n = new Set(prev); n.add(note.id); return n; }); }}
                      style={{ background: "none", border: "none", cursor: "pointer", color: C.inkMid, lineHeight: 1, padding: "1px 3px", opacity: 0.5, transition: "opacity 0.1s", display: "flex", alignItems: "center", flexShrink: 0 }}
                      title="Collapse note"
                      onMouseEnter={e => e.currentTarget.style.opacity = "1"}
                      onMouseLeave={e => e.currentTarget.style.opacity = "0.5"}>
                      <svg width="10" height="10" viewBox="0 0 10 10" fill="none">
                        <rect x="1" y="1" width="8" height="8" rx="1.5" stroke={C.inkMid} strokeWidth="1.3"/>
                        <line x1="3" y1="5" x2="7" y2="5" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
                      </svg>
                    </button>
                    <span style={{ flex: 1, fontSize: Math.max(7, 8 * camera.scale), letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", userSelect: "none" }}>note</span>
                    <button onMouseDown={e => e.stopPropagation()}
                      onClick={e => { e.stopPropagation(); removeNote(note.id); }}
                      style={{ background: "none", border: "none", cursor: "pointer", color: C.inkMid, fontSize: Math.max(10, 13 * camera.scale), lineHeight: 1, padding: "0 2px", opacity: 0.5, transition: "opacity 0.1s" }}
                      onMouseEnter={e => e.currentTarget.style.opacity = "1"}
                      onMouseLeave={e => e.currentTarget.style.opacity = "0.5"}>×</button>
                  </div>
                  {/* Body */}
                  {isEditing ? (
                    <textarea autoFocus value={note.text}
                      onChange={e => updateNote(note.id, { text: e.target.value })}
                      onBlur={() => setEditingNoteId(null)}
                      onKeyDown={e => { if (e.key === "Escape") { setEditingNoteId(null); e.stopPropagation(); } }}
                      style={{
                        flex: 1, border: "none", outline: "none", resize: "none",
                        background: "transparent", padding: `${Math.max(4, 5 * camera.scale)}px ${Math.max(5, 7 * camera.scale)}px`,
                        fontSize: fs, fontFamily: "'Courier New', monospace",
                        color: C.inkMid, lineHeight: 1.6,
                      }}
                    />
                  ) : (
                    <div style={{
                      flex: 1, padding: `${Math.max(4, 5 * camera.scale)}px ${Math.max(5, 7 * camera.scale)}px`,
                      overflow: "hidden", fontSize: fs, color: C.inkMid,
                      lineHeight: 1.6, whiteSpace: "pre-wrap", wordBreak: "break-word",
                    }}>
                      {note.text || <span style={{ color: C.inkFaint, opacity: 0.6, fontStyle: "italic" }}>double-click to edit</span>}
                    </div>
                  )}
                </>
              )}
            </div>
          );
        })}

        {/* ── Draw toolbar — bottom right ── */}
        {(() => {
          const PALETTE = [
            ["#0B151E","#1e3d54","#3a6278","#93b5c8"],
            ["#ef4444","#f97316","#ca8a04","#16a34a"],
            ["#0284c7","#7c3aed","#db2777","#0891b2"],
          ];

          const menuOpen = drawMenuOpen;
          const setMenuOpen = setDrawMenuOpen;
          const hoveredItem = drawMenuHovered;
          const setHoveredItem = (val) => {
            if (drawMenuLeaveTimer.current) { clearTimeout(drawMenuLeaveTimer.current); drawMenuLeaveTimer.current = null; }
            if (val !== null) { setDrawMenuHovered(val); }
            else { drawMenuLeaveTimer.current = setTimeout(() => setDrawMenuHovered(null), 350); }
          };
          const isDrawActive = !!drawTool;

          const ICONS = {
            pen: (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><path d="M2 13L5.5 12L13.5 4C14.05 3.45 14.05 2.55 13.5 2C12.95 1.45 12.05 1.45 11.5 2L3.5 10L2 13Z" stroke={a?"#fff":C.inkMid} strokeWidth="1.4" strokeLinejoin="round"/><path d="M11.5 2L13.5 4" stroke={a?"#fff":C.inkMid} strokeWidth="1.4"/></svg>,
            line: (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><line x1="2" y1="14" x2="14" y2="2" stroke={a?"#fff":C.inkMid} strokeWidth="1.8" strokeLinecap="round"/></svg>,
            "arrow-end": (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><line x1="2" y1="14" x2="12" y2="4" stroke={a?"#fff":C.inkMid} strokeWidth="1.8" strokeLinecap="round"/><path d="M12 4L8 4.8L11.2 8Z" fill={a?"#fff":C.inkMid}/></svg>,
            "arrow-start": (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><line x1="4" y1="12" x2="14" y2="2" stroke={a?"#fff":C.inkMid} strokeWidth="1.8" strokeLinecap="round"/><path d="M4 12L4.8 8L8 11.2Z" fill={a?"#fff":C.inkMid}/></svg>,
            "arrow-both": (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><line x1="4" y1="12" x2="12" y2="4" stroke={a?"#fff":C.inkMid} strokeWidth="1.8" strokeLinecap="round"/><path d="M12 4L8 4.8L11.2 8Z" fill={a?"#fff":C.inkMid}/><path d="M4 12L4.8 8L8 11.2Z" fill={a?"#fff":C.inkMid}/></svg>,
            rect: (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><rect x="2.5" y="3.5" width="11" height="9" rx="1.5" stroke={a?"#fff":C.inkMid} strokeWidth="1.5"/></svg>,
            circle: (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><ellipse cx="8" cy="8" rx="5.5" ry="4" stroke={a?"#fff":C.inkMid} strokeWidth="1.5"/></svg>,
            triangle: (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><polygon points="8,2 14,14 2,14" stroke={a?"#fff":C.inkMid} strokeWidth="1.5" fill="none" strokeLinejoin="round"/></svg>,
            eraser: (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><path d="M2 11L6.5 3.5H9.5L14 11H2Z" fill={a?"#fff":"none"} stroke={a?"#fff":"#ef4444"} strokeWidth="1.3" strokeLinejoin="round"/><rect x="2" y="11" width="12" height="2.5" rx="1" fill={a?"rgba(255,255,255,0.3)":"#fecaca"} stroke={a?"#fff":"#ef4444"} strokeWidth="1.1"/><line x1="8" y1="3.5" x2="8" y2="11" stroke={a?"rgba(255,255,255,0.5)":"#fca5a5"} strokeWidth="1" strokeDasharray="2 1.5"/></svg>,
          };

          const activeIcon = () => {
            if (!drawTool) return null;
            if (drawTool === "line") return ICONS[drawLineStyle]?.(true) ?? ICONS.line(true);
            return ICONS[drawTool]?.(true) ?? ICONS.pen(true);
          };

          const handleSquareClick = () => {
            if (isDrawActive) {
              setDrawTool(null); setDrawStrokes(prev => prev.filter(s => s.permanent)); setMenuOpen(false);
            } else { setMenuOpen(o => !o); }
          };

          const selectTool = (toolKey, lineStyle) => {
            if (toolKey === "line" && lineStyle) setDrawLineStyle(lineStyle);
            setDrawTool(toolKey); setLastDrawTool(toolKey); setMenuOpen(false); setHoveredItem(null);
          };

          const menuItemBase = (hov) => ({
            display:"flex", alignItems:"center", gap:8, padding:"7px 12px",
            cursor:"pointer", borderRadius:6, userSelect:"none", position:"relative",
            background: hov ? C.selectedBg : "transparent", transition:"background 0.1s",
          });

          const subMenuBox = {
            position:"absolute", right:"calc(100% + 8px)", top:"50%", transform:"translateY(-50%)",
            background:"#fff", border:`1.5px solid ${C.border}`, borderRadius:8, padding:"6px",
            boxShadow:"0 4px 16px rgba(11,21,30,0.13)", minWidth:148, zIndex:25,
            display:"flex", flexDirection:"column", gap:3,
          };

          const subItem = (active, danger) => ({
            display:"flex", alignItems:"center", gap:8, padding:"6px 10px",
            cursor:"pointer", borderRadius:5, transition:"background 0.1s",
            background: active ? C.inkMid : "transparent",
          });

          const tabLabel = (txt, active) => (
            <span style={{ fontSize:10, fontFamily:"'Courier New', monospace", letterSpacing:0.8,
              color: active ? C.ink : C.inkFaint, fontWeight: active ? "600" : "400" }}>{txt}</span>
          );

          // Line style rows
          const lineStyles = [
            { key:"plain",      label:"Plain line" },
            { key:"arrow-end",  label:"Arrow →" },
            { key:"arrow-start",label:"Arrow ←" },
            { key:"arrow-both", label:"Arrow ↔" },
          ];
          // Shape rows
          const shapes = [
            { key:"rect",     label:"Rectangle" },
            { key:"circle",   label:"Ellipse" },
            { key:"triangle", label:"Triangle" },
          ];
          // Weight options
          const weights = [{sz:1,w:10,h:1.5},{sz:2,w:12,h:3},{sz:4,w:14,h:5}];

          return (
            <div style={{ position:"absolute", bottom:14, right:14, zIndex:14, display:"flex", flexDirection:"row", alignItems:"flex-end", gap:7 }}
              onMouseDown={e => e.stopPropagation()}>

              {/* Left mini buttons */}
              <div style={{ display:"flex", flexDirection:"column", gap:5, alignItems:"stretch" }}>
                <button title={drawPermanent?"Temporary strokes":"Permanent strokes"} onClick={() => setDrawPermanent(p=>!p)} style={{
                  width:48, height:28, borderRadius:5, background: drawPermanent?C.inkMid:"#fff",
                  border:`1.5px solid ${drawPermanent?C.inkMid:C.border}`,
                  cursor:"pointer", display:"flex", alignItems:"center", justifyContent:"center", gap:4,
                  boxShadow:"0 1px 4px rgba(11,21,30,0.10)", transition:"background 0.13s",
                }}
                  onMouseEnter={e=>{if(!drawPermanent){e.currentTarget.style.background=C.selectedBg;e.currentTarget.style.borderColor=C.selectedBord;}}}
                  onMouseLeave={e=>{if(!drawPermanent){e.currentTarget.style.background="#fff";e.currentTarget.style.borderColor=C.border;}}}>
                  <svg width="10" height="10" viewBox="0 0 12 12" fill="none">
                    {drawPermanent?<circle cx="6" cy="6" r="4.5" fill="#fff"/>:<circle cx="6" cy="6" r="4.5" stroke={C.inkFaint} strokeWidth="1.4"/>}
                  </svg>
                  <span style={{fontSize:7,letterSpacing:1.5,textTransform:"uppercase",fontFamily:"'Courier New', monospace",color:drawPermanent?"#fff":C.inkFaint}}>{drawPermanent?"perm":"temp"}</span>
                </button>
                <button title="Undo last stroke" onClick={()=>setDrawStrokes(prev=>{const li=[...prev].reverse().findIndex(s=>s.permanent);if(li===-1)return prev;return prev.filter((_,i)=>i!==prev.length-1-li);})}
                  disabled={!drawStrokes.some(s=>s.permanent)}
                  style={{
                    width:48, height:28, borderRadius:5, background:"#fff", border:`1.5px solid #fca5a5`,
                    cursor:"pointer", display:"flex", alignItems:"center", justifyContent:"center", gap:3,
                    boxShadow:"0 1px 4px rgba(11,21,30,0.08)", transition:"background 0.12s",
                    opacity:drawStrokes.some(s=>s.permanent)?1:0.35,
                  }}
                  onMouseEnter={e=>{if(drawStrokes.some(s=>s.permanent))e.currentTarget.style.background="#fef2f2";}}
                  onMouseLeave={e=>{e.currentTarget.style.background="#fff";}}>
                  <svg width="11" height="11" viewBox="0 0 14 14" fill="none"><path d="M2.5 7C2.5 4.5 4.5 2.5 7 2.5C9.5 2.5 11.5 4.5 11.5 7C11.5 9.5 9.5 11.5 7 11.5" stroke="#ef4444" strokeWidth="1.4" strokeLinecap="round"/><path d="M2.5 4.5V7H5" stroke="#ef4444" strokeWidth="1.4" strokeLinecap="round" strokeLinejoin="round"/></svg>
                  <span style={{fontSize:7,letterSpacing:1.5,textTransform:"uppercase",fontFamily:"'Courier New', monospace",color:"#ef4444"}}>undo</span>
                </button>
              </div>

              {/* Main button + popup */}
              <div style={{ position:"relative", display:"flex", flexDirection:"column", alignItems:"flex-end" }}>

                {/* Popup menu */}
                {menuOpen && !isDrawActive && (
                  <div style={{
                    position:"absolute", bottom:"calc(100% + 10px)", right:0,
                    background:"#fff", border:`1.5px solid ${C.border}`, borderRadius:12, padding:"8px",
                    boxShadow:"0 6px 24px rgba(11,21,30,0.16)", minWidth:152, zIndex:22,
                    display:"flex", flexDirection:"column", gap:2,
                  }}>

                    {/* ── Pen ── */}
                    <div style={menuItemBase(hoveredItem==="pen")}
                      onMouseEnter={()=>setHoveredItem("pen")} onMouseLeave={()=>setHoveredItem(null)}
                      onClick={()=>selectTool("pen")}>
                      {ICONS.pen(false)}{tabLabel("Pen", drawTool==="pen")}
                    </div>

                    {/* ── Plain line (no arrows) — quick access ── */}
                    <div style={menuItemBase(hoveredItem==="plain-line")}
                      onMouseEnter={()=>setHoveredItem("plain-line")} onMouseLeave={()=>setHoveredItem(null)}
                      onClick={()=>selectTool("line","plain")}>
                      <svg width="18" height="18" viewBox="0 0 18 18" fill="none">
                        <line x1="3" y1="9" x2="15" y2="9" stroke={C.inkMid} strokeWidth="1.6" strokeLinecap="round"/>
                      </svg>
                      {tabLabel("Line", drawTool==="line"&&drawLineStyle==="plain")}
                    </div>

                    {/* ── Arrow line (styled) ── */}
                    <div style={{...menuItemBase(hoveredItem==="line"), justifyContent:"space-between"}}
                      onMouseEnter={()=>setHoveredItem("line")} onMouseLeave={()=>setHoveredItem(null)}>
                      <div style={{display:"flex",alignItems:"center",gap:8}}>
                        {ICONS[drawLineStyle==="plain"?"arrow-end":drawLineStyle]?.(false) ?? ICONS.line(false)}
                        {tabLabel("Arrow", drawTool==="line"&&drawLineStyle!=="plain")}
                      </div>
                      <span style={{fontSize:9,color:C.inkFaint}}>‹</span>
                      {hoveredItem==="line" && (
                        <div style={subMenuBox}>
                          {lineStyles.filter(ls=>ls.key!=="plain").map(ls=>(
                            <div key={ls.key} style={subItem(drawTool==="line"&&drawLineStyle===ls.key)}
                              onClick={e=>{e.stopPropagation();selectTool("line",ls.key);}}
                              onMouseEnter={e=>{if(!(drawTool==="line"&&drawLineStyle===ls.key))e.currentTarget.style.background=C.selectedBg;}}
                              onMouseLeave={e=>{if(!(drawTool==="line"&&drawLineStyle===ls.key))e.currentTarget.style.background="transparent";}}>
                              {ICONS[ls.key]?.(drawTool==="line"&&drawLineStyle===ls.key)}
                              <span style={{fontSize:11,fontFamily:"'Courier New', monospace",letterSpacing:0.8,color:drawTool==="line"&&drawLineStyle===ls.key?"#fff":C.ink}}>{ls.label}</span>
                            </div>
                          ))}
                        </div>
                      )}
                    </div>

                    {/* ── Shape ── */}
                    <div style={{...menuItemBase(hoveredItem==="shape"), justifyContent:"space-between"}}
                      onMouseEnter={()=>setHoveredItem("shape")} onMouseLeave={()=>setHoveredItem(null)}>
                      <div style={{display:"flex",alignItems:"center",gap:8}}>
                        {ICONS.rect(false)}{tabLabel("Shape", ["rect","circle","triangle"].includes(drawTool))}
                      </div>
                      <span style={{fontSize:9,color:C.inkFaint}}>‹</span>
                      {hoveredItem==="shape" && (
                        <div style={subMenuBox}>
                          {shapes.map(sh=>(
                            <div key={sh.key} style={subItem(drawTool===sh.key)}
                              onClick={e=>{e.stopPropagation();selectTool(sh.key);}}
                              onMouseEnter={e=>{if(drawTool!==sh.key)e.currentTarget.style.background=C.selectedBg;}}
                              onMouseLeave={e=>{if(drawTool!==sh.key)e.currentTarget.style.background="transparent";}}>
                              {ICONS[sh.key]?.(drawTool===sh.key)}
                              <span style={{fontSize:11,fontFamily:"'Courier New', monospace",letterSpacing:0.8,color:drawTool===sh.key?"#fff":C.ink}}>{sh.label}</span>
                            </div>
                          ))}
                        </div>
                      )}
                    </div>

                    {/* ── Eraser ── */}
                    <div style={menuItemBase(hoveredItem==="eraser")}
                      onMouseEnter={()=>setHoveredItem("eraser")} onMouseLeave={()=>setHoveredItem(null)}
                      onClick={()=>selectTool("eraser")}>
                      {ICONS.eraser(false)}
                      <span style={{fontSize:10,fontFamily:"'Courier New', monospace",letterSpacing:0.8,color:"#ef4444",fontWeight:drawTool==="eraser"?"600":"400"}}>Eraser</span>
                    </div>

                    {/* divider */}
                    <div style={{height:1,background:C.border,margin:"4px 6px"}}/>

                    {/* ── Color tab ── */}
                    <div style={{...menuItemBase(hoveredItem==="color"), justifyContent:"space-between"}}
                      onMouseEnter={()=>setHoveredItem("color")} onMouseLeave={()=>setHoveredItem(null)}>
                      <div style={{display:"flex",alignItems:"center",gap:8}}>
                        <div style={{width:18,height:18,borderRadius:"50%",background:drawColor,border:`1.5px solid ${C.border}`,flexShrink:0,boxSizing:"border-box"}}/>
                        {tabLabel("Color", false)}
                      </div>
                      <span style={{fontSize:9,color:C.inkFaint}}>‹</span>
                      {hoveredItem==="color" && (
                        <div style={{...subMenuBox, padding:"12px", minWidth:172}} onClick={e=>e.stopPropagation()}>
                          <div style={{fontSize:8,letterSpacing:2.5,color:C.inkFaint,textTransform:"uppercase",marginBottom:8}}>Color</div>
                          {PALETTE.map((row,ri)=>(
                            <div key={ri} style={{display:"flex",gap:7,marginBottom:7}}>
                              {row.map(col=>(
                                <div key={col} onClick={()=>setDrawColor(col)} style={{
                                  width:22,height:22,borderRadius:"50%",cursor:"pointer",background:col,flexShrink:0,
                                  border:drawColor===col?`3px solid ${C.inkMid}`:`1.5px solid ${col==="#fff"?C.border:"transparent"}`,
                                  boxSizing:"border-box", boxShadow:drawColor===col?`0 0 0 1.5px #fff inset`:"none",
                                  transition:"border 0.1s",
                                }}/>
                              ))}
                            </div>
                          ))}
                          <div style={{borderTop:`1px solid ${C.border}`,paddingTop:8,display:"flex",alignItems:"center",gap:7}}>
                            <div style={{width:20,height:20,borderRadius:"50%",background:drawColor,border:`1.5px solid ${C.border}`,flexShrink:0}}/>
                            <input type="text" value={drawColor}
                              onChange={e=>{if(/^#[0-9a-fA-F]{0,6}$/.test(e.target.value))setDrawColor(e.target.value);}}
                              style={{flex:1,background:C.bg,border:`1px solid ${C.border}`,borderRadius:3,color:C.inkMid,fontSize:10,padding:"3px 6px",outline:"none",fontFamily:"'Courier New', monospace",letterSpacing:1}}/>
                          </div>
                        </div>
                      )}
                    </div>

                    {/* ── Weight tab ── */}
                    <div style={{...menuItemBase(hoveredItem==="weight"), justifyContent:"space-between"}}
                      onMouseEnter={()=>setHoveredItem("weight")} onMouseLeave={()=>setHoveredItem(null)}>
                      <div style={{display:"flex",alignItems:"center",gap:8}}>
                        <svg width="18" height="18" viewBox="0 0 18 18" fill="none">
                          <line x1="2" y1="9" x2="16" y2="9" stroke={C.inkMid} strokeWidth={drawSize===1?1.5:drawSize===2?3:5} strokeLinecap="round"/>
                        </svg>
                        {tabLabel("Weight", false)}
                      </div>
                      <span style={{fontSize:9,color:C.inkFaint}}>‹</span>
                      {hoveredItem==="weight" && (
                        <div style={{...subMenuBox, padding:"10px 12px", minWidth:150}} onClick={e=>e.stopPropagation()}>
                          <div style={{fontSize:8,letterSpacing:2.5,color:C.inkFaint,textTransform:"uppercase",marginBottom:8}}>Stroke Weight</div>
                          <div style={{display:"flex",gap:6,marginBottom:10}}>
                            {weights.map(({sz,w,h})=>(
                              <button key={sz} onClick={()=>setDrawSize(sz)} style={{
                                flex:1,height:34,borderRadius:6,cursor:"pointer",
                                background:drawSize===sz?C.selectedBg:"#fff",
                                border:`1.5px solid ${drawSize===sz?C.selectedBord:C.border}`,
                                display:"flex",alignItems:"center",justifyContent:"center",
                                transition:"background 0.1s",
                              }}
                                onMouseEnter={e=>{if(drawSize!==sz)e.currentTarget.style.background=C.selectedBg;}}
                                onMouseLeave={e=>{if(drawSize!==sz)e.currentTarget.style.background="#fff";}}>
                                <div style={{width:w,height:h,background:C.inkMid,borderRadius:h}}/>
                              </button>
                            ))}
                          </div>
                          <div style={{display:"flex",alignItems:"center",gap:7}}>
                            <input type="range" min={1} max={20} step={1} value={drawSize}
                              onChange={e=>setDrawSize(Number(e.target.value))}
                              style={{flex:1,accentColor:C.inkMid,cursor:"pointer"}}/>
                            <span style={{fontSize:9,color:C.inkFaint,fontFamily:"'Courier New',monospace",minWidth:18,textAlign:"right"}}>{drawSize}</span>
                          </div>
                        </div>
                      )}
                    </div>

                  </div>
                )}

                {/* Big square button */}
                <button title={isDrawActive?`Drawing: ${drawTool} — click to stop`:"Open drawing tools"}
                  onClick={handleSquareClick}
                  style={{
                    width:62, height:62, borderRadius:12, flexShrink:0,
                    background:isDrawActive?C.inkMid:"#fff",
                    border:`2px solid ${isDrawActive?C.inkMid:menuOpen?C.selectedBord:C.border}`,
                    cursor:"pointer", display:"flex", alignItems:"center", justifyContent:"center",
                    boxShadow:menuOpen||isDrawActive?"0 6px 20px rgba(11,21,30,0.20)":"0 2px 10px rgba(11,21,30,0.10)",
                    transition:"background 0.15s, border-color 0.15s, box-shadow 0.15s",
                    position:"relative",
                  }}
                  onMouseEnter={e=>{if(!isDrawActive){e.currentTarget.style.background=C.selectedBg;e.currentTarget.style.borderColor=C.selectedBord;}}}
                  onMouseLeave={e=>{if(!isDrawActive){e.currentTarget.style.background="#fff";e.currentTarget.style.borderColor=menuOpen?C.selectedBord:C.border;}}}>
                  {isDrawActive
                    ? (activeIcon() ?? ICONS.pen(true))
                    : <svg width="24" height="24" viewBox="0 0 20 20" fill="none">
                        <path d="M3 16L7 15L16 6C16.6 5.4 16.6 4.4 16 3.8C15.4 3.2 14.4 3.2 13.8 3.8L5 12.5L3 16Z" stroke={C.inkMid} strokeWidth="1.5" strokeLinejoin="round"/>
                        <path d="M13.8 3.8L16 6" stroke={C.inkMid} strokeWidth="1.5"/>
                      </svg>
                  }
                  {/* Color dot */}
                  <div style={{
                    position:"absolute", bottom:7, right:7,
                    width:9, height:9, borderRadius:"50%",
                    background:drawColor, border:"1.5px solid #fff", boxSizing:"border-box",
                    boxShadow:"0 1px 3px rgba(0,0,0,0.2)",
                  }}/>
                </button>

              </div>
            </div>
          );
        })()}

        {/* ── Ψ Morphism button — bottom left ── */}
        {(() => {
          const mOpen = morphBtnOpen;
          const mHov = morphBtnHovered;
          const hasActive = activeMorphismId !== null;
          const activeMorphism = morphisms.find(m => m.id === activeMorphismId);

          const handlePsiClick = () => {
            if (hasActive) {
              setActiveMorphismId(null);
              setMorphBtnOpen(false);
            } else {
              setMorphBtnOpen(o => !o);
            }
          };

          const createMorphism = () => {
            const id = Date.now();
            const color = MORPHISM_COLORS[morphisms.length % MORPHISM_COLORS.length];
            const newM = { id, name: `φ${morphisms.length + 1}`, color, strands: [] };
            setMorphisms(prev => [...prev, newM]);
            setActiveMorphismId(id);
            setMorphBtnOpen(false);
          };

          const menuItemBase = (hov) => ({
            display:"flex", alignItems:"center", gap:9, padding:"8px 13px",
            cursor:"pointer", borderRadius:7, userSelect:"none",
            background: hov ? C.selectedBg : "transparent", transition:"background 0.1s",
          });

          return (
            <div style={{ position:"absolute", bottom:14, left:14, zIndex:14, display:"flex", flexDirection:"row", alignItems:"flex-end", gap:7 }}
              onMouseDown={e => e.stopPropagation()}>

              {/* Main Ψ button + popup */}
              <div style={{ position:"relative", display:"flex", flexDirection:"column", alignItems:"flex-start" }}>

                {/* Popup */}
                {mOpen && !hasActive && (
                  <div style={{
                    position:"absolute", bottom:"calc(100% + 10px)", left:0,
                    background:"#fff", border:`1.5px solid ${C.border}`, borderRadius:12, padding:"8px",
                    boxShadow:"0 6px 24px rgba(11,21,30,0.16)", minWidth:180, zIndex:22,
                    display:"flex", flexDirection:"column", gap:3,
                  }}>
                    {/* New morphism */}
                    <div style={menuItemBase(mHov==="new")}
                      onMouseEnter={()=>setMorphBtnHovered("new")} onMouseLeave={()=>setMorphBtnHovered(null)}
                      onClick={createMorphism}>
                      <svg width="16" height="16" viewBox="0 0 16 16" fill="none">
                        <circle cx="8" cy="8" r="6.5" stroke={C.inkMid} strokeWidth="1.3"/>
                        <line x1="8" y1="4.5" x2="8" y2="11.5" stroke={C.inkMid} strokeWidth="1.5" strokeLinecap="round"/>
                        <line x1="4.5" y1="8" x2="11.5" y2="8" stroke={C.inkMid} strokeWidth="1.5" strokeLinecap="round"/>
                      </svg>
                      <span style={{fontSize:11,fontFamily:"'Courier New', monospace",letterSpacing:0.8,color:C.ink}}>New Morphism</span>
                    </div>

                    {morphisms.length > 0 && <div style={{height:1,background:C.border,margin:"3px 6px"}}/>}

                    {/* Existing morphisms */}
                    {morphisms.map(m => (
                      <div key={m.id}
                        style={{...menuItemBase(mHov===m.id), justifyContent:"space-between"}}
                        onMouseEnter={()=>setMorphBtnHovered(m.id)} onMouseLeave={()=>setMorphBtnHovered(null)}
                        onClick={()=>{ setActiveMorphismId(m.id); setMorphBtnOpen(false); setMorphBtnHovered(null); }}>
                        <div style={{display:"flex",alignItems:"center",gap:9}}>
                          <div style={{width:10,height:10,borderRadius:"50%",background:m.color,flexShrink:0,border:`1.5px solid ${m.color}`,boxSizing:"border-box"}}/>
                          <span style={{fontSize:11,fontFamily:"'Courier New', monospace",letterSpacing:0.8,color:C.ink}}>{m.name}</span>
                          {m.strands.length>0 && <span style={{fontSize:9,color:C.inkFaint,letterSpacing:0.5}}>{m.strands.length}s</span>}
                        </div>
                        <button onClick={e=>{e.stopPropagation();setMorphisms(prev=>prev.filter(x=>x.id!==m.id));if(activeMorphismId===m.id)setActiveMorphismId(null);}}
                          style={{background:"none",border:"none",cursor:"pointer",color:C.inkFaint,fontSize:14,padding:"0 2px",lineHeight:1}}>×</button>
                      </div>
                    ))}
                  </div>
                )}

                {/* The big Ψ button */}
                <button
                  title={hasActive ? `Morphism active: ${activeMorphism?.name ?? ""} — click to deactivate` : "Open morphism tools"}
                  onClick={handlePsiClick}
                  style={{
                    width:62, height:62, borderRadius:12, flexShrink:0,
                    background: hasActive ? activeMorphism?.color ?? C.inkMid : "#fff",
                    border:`2px solid ${hasActive ? activeMorphism?.color ?? C.inkMid : mOpen ? C.selectedBord : C.border}`,
                    cursor:"pointer", display:"flex", alignItems:"center", justifyContent:"center",
                    boxShadow: mOpen||hasActive ? "0 6px 20px rgba(11,21,30,0.20)" : "0 2px 10px rgba(11,21,30,0.10)",
                    transition:"background 0.15s, border-color 0.15s, box-shadow 0.15s",
                    position:"relative",
                  }}
                  onMouseEnter={e=>{if(!hasActive){e.currentTarget.style.background=C.selectedBg;e.currentTarget.style.borderColor=C.selectedBord;}}}
                  onMouseLeave={e=>{if(!hasActive){e.currentTarget.style.background="#fff";e.currentTarget.style.borderColor=mOpen?C.selectedBord:C.border;}}}>
                  {/* Ψ (Psi) Unicode */}
                  <span style={{
                    fontSize: hasActive ? 26 : 28,
                    fontWeight: "300",
                    color: hasActive ? "#fff" : "#1e3d54",
                    fontFamily: "serif",
                    lineHeight: 1,
                    userSelect: "none",
                    letterSpacing: 0,
                  }}>Ψ</span>
                  {/* Strand count badge */}
                  {morphisms.length > 0 && !hasActive && (
                    <div style={{
                      position:"absolute", top:6, right:6,
                      width:16, height:16, borderRadius:"50%",
                      background:MORPHISM_COLORS[0], border:"1.5px solid #fff",
                      display:"flex", alignItems:"center", justifyContent:"center",
                      fontSize:8, color:"#fff", fontFamily:"'Courier New', monospace", fontWeight:"700",
                    }}>{morphisms.length}</div>
                  )}
                  {/* Active morphism color dot */}
                  {hasActive && (
                    <div style={{
                      position:"absolute", bottom:7, right:7,
                      width:9, height:9, borderRadius:"50%",
                      background:"rgba(255,255,255,0.7)", border:"1.5px solid rgba(255,255,255,0.4)",
                      boxSizing:"border-box",
                    }}/>
                  )}
                </button>

              </div>

              {/* Dom / Rng buttons — appear to the RIGHT of Ψ when a morphism with strands is active */}
              {hasActive && activeMorphism && activeMorphism.strands.length > 0 && (() => {
                const domainKeys = new Set(activeMorphism.strands.map(s => `${s.fromLatticeId}:${s.fromNodeId}`));
                const rangeKeys  = new Set(activeMorphism.strands.map(s => `${s.toLatticeId}:${s.toNodeId}`));
                
                // Helper function to convert Set of "latticeId:nodeId" strings to selectedNodes object
                const convertKeysToSelectedNodes = (keys) => {
                  const result = {};
                  for (const key of keys) {
                    if (!key || typeof key !== 'string') continue;
                    const parts = key.split(':');
                    if (parts.length !== 2) continue;
                    const lid = Number(parts[0]);
                    const nid = Number(parts[1]);
                    if (isNaN(lid) || isNaN(nid)) continue; // Skip invalid entries
                    if (!result[lid]) result[lid] = new Set();
                    result[lid].add(nid);
                  }
                  return result;
                };
                
                return (
                  <div style={{ display: "flex", flexDirection: "column", gap: 5, marginBottom: 2 }}>
                    <button 
                      title="Select domain nodes" 
                      onClick={() => setSelectedNodes(convertKeysToSelectedNodes(domainKeys))}
                      style={{
                        width: 48, height: 26, borderRadius: 5, background: "#fff",
                        border: `1.5px solid ${activeMorphism.color}`,
                        cursor: "pointer", fontSize: 9, color: activeMorphism.color,
                        fontFamily: "'Courier New', monospace", letterSpacing: 1.5,
                        textTransform: "uppercase", fontWeight: "600",
                        boxShadow: "0 1px 4px rgba(11,21,30,0.10)", transition: "background 0.1s",
                      }}
                      onMouseEnter={e => e.currentTarget.style.background = C.selectedBg}
                      onMouseLeave={e => e.currentTarget.style.background = "#fff"}
                    >
                      Dom
                    </button>
                    <button 
                      title="Select range nodes" 
                      onClick={() => setSelectedNodes(convertKeysToSelectedNodes(rangeKeys))}
                      style={{
                        width: 48, height: 26, borderRadius: 5, background: "#fff",
                        border: `1.5px solid ${activeMorphism.color}`,
                        cursor: "pointer", fontSize: 9, color: activeMorphism.color,
                        fontFamily: "'Courier New', monospace", letterSpacing: 1.5,
                        textTransform: "uppercase", fontWeight: "600",
                        boxShadow: "0 1px 4px rgba(11,21,30,0.10)", transition: "background 0.1s",
                      }}
                      onMouseEnter={e => e.currentTarget.style.background = C.selectedBg}
                      onMouseLeave={e => e.currentTarget.style.background = "#fff"}
                    >
                      Rng
                    </button>
                  </div>
                );
              })()}

              {/* Active morphism hint */}
              {hasActive && (
                <div style={{
                  background:activeMorphism?.color ?? C.inkMid, color:"#fff",
                  borderRadius:7, padding:"5px 10px",
                  fontSize:9, fontFamily:"'Courier New', monospace", letterSpacing:1.5, textTransform:"uppercase",
                  boxShadow:"0 2px 8px rgba(11,21,30,0.15)", alignSelf:"flex-end", marginBottom:4,
                  maxWidth:130, lineHeight:1.4,
                }}>
                  ↗ drag nodes<br/>to link
                </div>
              )}
            </div>
          );
        })()}

        {/* Top-right controls: zoom reset + note button */}
        <div style={{ position: "absolute", top: 14, right: 14, zIndex: 3, display: "flex", alignItems: "center", gap: 6 }}
          onMouseDown={e => e.stopPropagation()}>
          {/* Zoom / reset — secondary, sits left of note */}
          <button onClick={() => {
            if (!panelRef.current) return;
            const r = panelRef.current.getBoundingClientRect();
            setCamera({ tx: r.width / 4, ty: r.height / 4, scale: 0.75 });
          }} style={{
            background: C.bg, border: `1px solid ${C.border}`, borderRadius: 5,
            padding: "5px 9px", cursor: "pointer", fontSize: 9, color: C.inkMid,
            letterSpacing: 2, textTransform: "uppercase",
          }}>
            {Math.round(camera.scale * 100)}% ↺
          </button>

          {/* Note button — primary corner button */}
          <button
            title="Add a note to the canvas"
            onClick={() => {
              if (!panelRef.current) return;
              const r = panelRef.current.getBoundingClientRect();
              const cam = cameraRef.current;
              // Place in current viewport center
              const wx = (r.width / 2 - cam.tx) / cam.scale;
              const wy = (r.height / 2 - cam.ty) / cam.scale;
              addNote(wx, wy);
            }}
            style={{
              width: 36, height: 36, borderRadius: 8, flexShrink: 0,
              background: "#fff", border: `1.5px solid ${C.border}`,
              cursor: "pointer", display: "flex", alignItems: "center", justifyContent: "center",
              boxShadow: "0 2px 8px rgba(11,21,30,0.10)",
              transition: "background 0.15s, border-color 0.15s",
            }}
            onMouseEnter={e => { e.currentTarget.style.background = C.selectedBg; e.currentTarget.style.borderColor = C.selectedBord; }}
            onMouseLeave={e => { e.currentTarget.style.background = "#fff"; e.currentTarget.style.borderColor = C.border; }}>
            <svg width="18" height="18" viewBox="0 0 18 18" fill="none">
              <rect x="2.5" y="2.5" width="13" height="13" rx="2" stroke={C.inkMid} strokeWidth="1.4"/>
              <line x1="5.5" y1="7" x2="12.5" y2="7" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
              <line x1="5.5" y1="9.5" x2="12.5" y2="9.5" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
              <line x1="5.5" y1="12" x2="9.5" y2="12" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
            </svg>
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
      <div ref={rightPanelRef} style={{
        width: actualRightW, flexShrink: 0, height: "100%",
        display: "flex", flexDirection: "column",
        background: C.panelBg, overflow: "visible",
        transition: rightSplitDragging.current ? "none" : "width 0.2s ease",
        position: "relative",
        borderLeft: actualRightW > 0 ? `1px solid ${C.border}` : "none",
      }}>
        <CollapseBtn collapsed={rightCollapsed} onToggle={toggleRight} side="right" panelTitle="Inspector" />

        {actualRightW > 40 && (
          <div style={{ flex: 1, minHeight: 0, display: "flex", flexDirection: "column", overflow: "hidden", clipPath: "inset(0)" }}>

          {/* Pane 1: Selected Graph */}
          <Pane title="Selected Graph" open={rightPane1Open} onToggle={() => setRightPane1Open(o => !o)} flex={rightPane1Flex} scrollClass="sky-scroll-right">
            {(() => {
              const activeLatticeNodes = new Set(allSelectedNodes.map(n => n.latticeId));
              const displayNodes = [...activeLatticeNodes];

              if (displayNodes.length === 0) return (
                <div style={{ color: C.inkFaint, fontSize: 11, fontStyle: "italic" }}>
                  {lattices.length === 0 ? "No graphs on canvas yet." : "Select a node to inspect a graph."}
                </div>
              );

              return (
                <div style={{ margin: "-12px -14px" }}>
                  {displayNodes.map(selId => {
                    const lv = latticeViews.find(v => v.entry.id === selId);
                    const l  = lattices.find(x => x.id === selId);
                    if (!l || !lv) return null;
                    const { entry, nodes, fullNode, colorMap, accent, zParts, expVal, statsBase } = lv;
                    const displayBase = statsBase ?? entry.base;
                    
                    return (
                      <Section key={selId} label={entry.label} depth={0} accent={accent} defaultOpen={false}
                        badge={entry.isCollapsed ? `⊙ ${displayBase.nodes.length}n` : `${displayBase.nodes.length}n`}>

                        {/* ── STYLE FOLDER ── */}
                        <Section label="Style" depth={1} defaultOpen={false}>
                          
                          {/* Rename Graph */}
                          <Section label="Rename" depth={2} defaultOpen={false}>
                            <SectionBody>
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 8, letterSpacing: 1.5, color: C.inkFaint, textTransform: "uppercase", minWidth: 38, flexShrink: 0 }}>Title</span>
                                <input 
                                  value={entry.label || ''}
                                  onChange={e => updateLattice(entry.id, { label: e.target.value || `Graph ${entry.id}` })}
                                  style={{ 
                                    flex: 1, 
                                    background: C.bg, 
                                    border: `1px solid ${C.border}`, 
                                    borderRadius: 3, 
                                    color: C.ink, 
                                    fontSize: 10, 
                                    padding: "3px 6px", 
                                    outline: "none", 
                                    fontFamily: "'Courier New', monospace" 
                                  }}
                                  placeholder="Enter graph name..."
                                />
                              </div>
                              <div style={{ fontSize: 8, color: C.inkFaint, marginTop: 4, letterSpacing: 0.5 }}>
                                Changes the display name only. The underlying group data remains intact.
                              </div>
                            </SectionBody>
                          </Section>

                          {/* Stats */}
                          <Section label="Stats" depth={2} defaultOpen={false}>
                            {entry.kind === "Un" ? (
                              <SectionRow label={`U(${entry.param})`} value={formatZ(zParts)} />
                            ) : (
                              <SectionRow label="Group" value={entry.label} />
                            )}
                            <SectionRow label="Kind"   value={l.kind} />
                            <SectionRow label="Nodes"  value={String(displayBase.nodes.length)} />
                            <SectionRow label="Edges"  value={String(displayBase.edges.length)} />
                            {fullNode && <>
                              <SectionRow label="|G|"    value={String(fullNode.order)} />
                              <SectionRow label="Levels" value={String((displayBase.maxLevel ?? 0) + 1)} />
                            </>}
                            {entry.kind === "Un" && <>
                              <SectionRow label="Exponent" value={String(expVal)} />
                              <SectionRow label="Abelian"  value="yes" />
                            </>}
                            {entry.isCollapsed && <SectionRow label="State" value="collapsed ⊙" />}
                          </Section>

                          {/* Lattice Notes */}
                          <Section label="Lattice Notes" depth={2} defaultOpen={false}>
                            <SectionBody>
                              <textarea
                                value={entry.description || ''}
                                onChange={e => updateLatticeDescription(entry.id, e.target.value)}
                                placeholder="Add a description for this lattice..."
                                style={{
                                  width: "100%",
                                  minHeight: 80,
                                  background: C.bg,
                                  border: `1px solid ${C.border}`,
                                  borderRadius: 3,
                                  color: C.ink,
                                  fontSize: 10,
                                  padding: "5px 7px",
                                  outline: "none",
                                  resize: "vertical",
                                  boxSizing: "border-box",
                                  fontFamily: "'Courier New', monospace",
                                  lineHeight: 1.5
                                }}
                              />
                            </SectionBody>
                          </Section>

                          {/* Display Toggles */}
                          <Section label="Display" depth={2} defaultOpen={false}>
                            <SectionToggle label="Show Edges"        checked={entry.showEdges}     onChange={v => updateLattice(entry.id, { showEdges: v })} />
                            <SectionToggle label="Show Arrows"       checked={entry.showArrows}    onChange={v => updateLattice(entry.id, { showArrows: v })} />
                            <SectionToggle label="Show Epicenter ☉"  checked={entry.showEpicenter} onChange={v => updateLattice(entry.id, { showEpicenter: v })} />
                            {(entry.base.viewType === "hasse" || !entry.base.viewType) && <>
                              <SectionToggle label="Gen. Offset (Hasse)"
                                checked={entry.hasseLayout?.genOffset ?? false}
                                onChange={v => updateLattice(entry.id, { hasseLayout: { ...(entry.hasseLayout ?? {}), genOffset: v } })} />
                              <SectionToggle label="Rank by Order"
                                checked={entry.hasseLayout?.rankByOrder ?? false}
                                onChange={v => updateLattice(entry.id, { hasseLayout: { ...(entry.hasseLayout ?? {}), rankByOrder: v } })} />
                            </>}
                            <SectionBody>
                              <div style={{ fontSize: 9, color: C.inkFaint, lineHeight: 1.6 }}>Drag the ☉ marker on the canvas to move the entire lattice.</div>
                            </SectionBody>
                          </Section>

                        </Section>

                        {/* ── SUBGROUPS ── */}
                        <Section label="Subgroups" depth={1} defaultOpen={false} badge={nodes.length}>
                          {/* Order color legend */}
                          <SectionBody>
                            <div style={{ display: "flex", flexWrap: "wrap", gap: 6 }}>
                              {Object.entries(colorMap).map(([ord, col]) => (
                                <div key={ord} style={{ display: "flex", alignItems: "center", gap: 4, fontSize: 10, color: C.inkMid }}>
                                  <div style={{ width: 11, height: 11, borderRadius: "50%", background: col, flexShrink: 0, border: `1.5px solid ${C.border}` }} />
                                  <span style={{ fontFamily: "'Courier New', monospace" }}>|H|={ord}</span>
                                </div>
                              ))}
                            </div>
                          </SectionBody>
                          <SectionBody noPad>
                            <div style={{ padding: "6px 8px" }}>
                              {[...nodes].sort((a, b) => a.order - b.order).map(node => {
                                return (
                                  <SubgroupRow 
                                    key={node.id} 
                                    node={node} 
                                    colorMap={colorMap}
                                    isSelected={isNodeSelected(l.id, node.id)}
                                    onToggle={() => toggleNodeSelect(l.id, node.id)} 
                                  />
                                );
                              })}
                            </div>
                          </SectionBody>
                        </Section>

                        {/* ── GRAPH ACTIONS ── */}
                        {(() => {
                          const confirmOpen = confirmDeleteNodes.has(l.id);
                          const setConfirmOpen = (v) => setConfirmDeleteNodes(prev => {
                            const next = new Set(prev);
                            v ? next.add(l.id) : next.delete(l.id);
                            return next;
                          });
                          return (
                            <SectionBody>
                              <div style={{ display: "flex", gap: 6 }}>
                                <button
                                  onClick={() => setConfirmOpen(!confirmOpen)}
                                  style={{
                                    flex: 1, padding: "5px 0", borderRadius: 4, cursor: "pointer",
                                    background: confirmOpen ? "#fef2f2" : "transparent",
                                    border: `1px solid #fca5a5`,
                                    color: "#ef4444", fontSize: 9, letterSpacing: 1.5,
                                    textTransform: "uppercase", fontFamily: "'Courier New', monospace",
                                    transition: "background 0.12s",
                                  }}
                                  onMouseEnter={e => { if (!confirmOpen) e.currentTarget.style.background = "#fff5f5"; }}
                                  onMouseLeave={e => { if (!confirmOpen) e.currentTarget.style.background = "transparent"; }}>
                                  🗑 Delete
                                </button>
                                {entry.isCollapsed ? (
                                  <button
                                    title="Expand graph back to full layout. Morphism strands restore to original endpoints."
                                    onClick={() => expandGraph(l.id)}
                                    style={{
                                      flex: 1, padding: "5px 0", borderRadius: 4, cursor: "pointer",
                                      background: C.selectedBg, border: `1px solid ${C.selectedBord}`,
                                      color: C.ink, fontSize: 9, letterSpacing: 1.5,
                                      textTransform: "uppercase", fontFamily: "'Courier New', monospace",
                                      transition: "background 0.12s",
                                    }}
                                    onMouseEnter={e => e.currentTarget.style.background = C.borderHover}
                                    onMouseLeave={e => e.currentTarget.style.background = C.selectedBg}>
                                    ⊙ Expand
                                  </button>
                                ) : (
                                  <button
                                    title="Collapse this graph to a single representative node. Strands re-route to it; expand to restore."
                                    onClick={() => collapseGraphToNode(l.id)}
                                    style={{
                                      flex: 1, padding: "5px 0", borderRadius: 4, cursor: "pointer",
                                      background: "transparent", border: `1px solid ${C.border}`,
                                      color: C.inkMid, fontSize: 9, letterSpacing: 1.5,
                                      textTransform: "uppercase", fontFamily: "'Courier New', monospace",
                                      transition: "background 0.12s",
                                    }}
                                    onMouseEnter={e => e.currentTarget.style.background = C.selectedBg}
                                    onMouseLeave={e => e.currentTarget.style.background = "transparent"}>
                                    ⊙ Collapse
                                  </button>
                                )}
                              </div>
                              {confirmOpen && (
                                <div style={{ marginTop: 7, padding: "8px", background: "#fef2f2", borderRadius: 4, border: `1px solid #fecaca`, display: "flex", flexDirection: "column", gap: 7 }}>
                                  <div style={{ fontSize: 9, color: "#991b1b", lineHeight: 1.5 }}>Remove <strong>{entry.label}</strong> from the canvas? This cannot be undone.</div>
                                  <div style={{ display: "flex", gap: 6 }}>
                                    <button onClick={() => { removeLattice(l.id); }} style={{
                                      flex: 1, padding: "5px 0", background: "#ef4444", border: "none", borderRadius: 4,
                                      color: "#fff", fontSize: 9, letterSpacing: 1.5, textTransform: "uppercase",
                                      fontFamily: "'Courier New', monospace", cursor: "pointer", fontWeight: "600",
                                    }}
                                      onMouseEnter={e => e.currentTarget.style.background = "#dc2626"}
                                      onMouseLeave={e => e.currentTarget.style.background = "#ef4444"}>
                                      Confirm
                                    </button>
                                    <button onClick={() => setConfirmOpen(false)} style={{
                                      flex: 1, padding: "5px 0", background: "transparent", border: `1px solid #fca5a5`,
                                      borderRadius: 4, color: "#ef4444", fontSize: 9, letterSpacing: 1.5,
                                      textTransform: "uppercase", fontFamily: "'Courier New', monospace", cursor: "pointer",
                                    }}>
                                      Cancel
                                    </button>
                                  </div>
                                </div>
                              )}
                            </SectionBody>
                          );
                        })()}

                      </Section>
                    );
                  })}
                </div>
              );
            })()}
          </Pane>

          {rightPane1Open && rightPane2Open && <HPSplitter onDrag={onRightSplit12} containerRef={rightPanelRef} />}

          {/* Pane 2: Selected Nodes */}
          <Pane title={`Selected Nodes${totalSelected > 0 ? ` (${totalSelected})` : ""}`} open={rightPane2Open} onToggle={() => setRightPane2Open(o => !o)} flex={rightPane2Flex} scrollClass="sky-scroll-right">
            {allSelectedNodes.length > 0
              ? <div style={{ margin: "-12px -14px" }}>
                  {allSelectedNodes.map(({ node, colorMap, latticeId, latticeLabel, indexVal, entry }) => {
                    const col = orderColor(node.order, colorMap);
                    const cyclicLabel = node.order === 1 ? "Trivial" : node.isCyclic ? "Cyclic" : node.shape === "square" ? "Non-cyclic · pair gens" : "Non-cyclic · triple gens";
                    return (
                      <Section key={`${latticeId}:${node.id}`} label={node.shortLabel} badge={`ord ${node.order}`} accent={col} depth={0} defaultOpen={false}>
                        <Section label="Label & Style" depth={1} defaultOpen={false}>
                          <SectionRow
                            label="Notation"
                            value={node.viewType === "elements" ? `[${node.elements[0]}] — element` : `⟨·⟩ — subgroup`}
                            accent={node.viewType === "elements" ? "#f97316" : "#0284c7"}
                          />
                          <SectionBody>
                            <div style={{ fontSize: 11, color: C.ink, fontFamily: "'Courier New', monospace", wordBreak: "break-all", lineHeight: 1.5 }}>{node.label}</div>
                          </SectionBody>
                          <SectionBody>
                            <div style={{ fontSize: 8, letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", marginBottom: 6 }}>Style Override</div>
                            <div style={{ display: "flex", flexDirection: "column", gap: 6 }}>
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1, minWidth: 36, flexShrink: 0 }}>Alias</span>
                                <input type="text" placeholder={node.shortLabel}
                                  value={nodeCustomStyles[`${latticeId}:${node.id}`]?.labelAlias ?? ""}
                                  onChange={e => setNodeCustomStyles(prev => ({
                                    ...prev, [`${latticeId}:${node.id}`]: { ...(prev[`${latticeId}:${node.id}`] ?? {}), labelAlias: e.target.value || undefined }
                                  }))}
                                  style={{ flex: 1, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 3, color: C.ink, fontSize: 10, padding: "3px 6px", outline: "none", fontFamily: "'Courier New', monospace" }} />
                              </div>
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1, minWidth: 36, flexShrink: 0 }}>Color</span>
                                <div style={{ display: "flex", gap: 5, flexWrap: "wrap" }}>
                                  {["#ef4444","#f97316","#ca8a04","#16a34a","#0284c7","#7c3aed","#db2777","#0891b2"].map(swatchCol => {
                                    const key = `${latticeId}:${node.id}`;
                                    const active = nodeCustomStyles[key]?.color === swatchCol;
                                    return (
                                      <div key={swatchCol}
                                        onClick={() => setNodeCustomStyles(prev => ({ ...prev, [key]: { ...(prev[key] ?? {}), color: active ? undefined : swatchCol } }))}
                                        style={{ width: 16, height: 16, borderRadius: "50%", cursor: "pointer", background: swatchCol, flexShrink: 0, border: active ? `2.5px solid ${C.ink}` : `1.5px solid transparent`, boxSizing: "border-box", boxShadow: active ? `0 0 0 1px #fff inset` : "none", transition: "border 0.1s" }} />
                                    );
                                  })}
                                  {nodeCustomStyles[`${latticeId}:${node.id}`]?.color && (
                                    <div onClick={() => setNodeCustomStyles(prev => { const next = { ...prev }; if (next[`${latticeId}:${node.id}`]) delete next[`${latticeId}:${node.id}`].color; return next; })}
                                      style={{ width: 16, height: 16, borderRadius: "50%", cursor: "pointer", background: C.bg, border: `1px solid ${C.border}`, display: "flex", alignItems: "center", justifyContent: "center", fontSize: 10, color: C.inkFaint }}>×</div>
                                  )}
                                </div>
                              </div>
                            </div>
                          </SectionBody>
                        </Section>
                        <Section label="Info" depth={1} defaultOpen={false}>

                          <Section label="Identity" depth={2} defaultOpen={false}>
                            <SectionRow label="Group"  value={latticeLabel} />
                            <SectionRow label="Type"   value={cyclicLabel} />
                            <SectionRow label="Normal" value={node.isNormal ? "yes ✓" : "no"} />
                            {node.isCyclic && node.order > 1 && (() => {
                              const SUB = "₀₁₂₃₄₅₆₇₈₉";
                              const sub = x => String(x).split("").map(d => SUB[parseInt(d)]??d).join("");
                              return <SectionRow label="Iso" value={`ℤ${sub(node.order)}`} accent={col} />;
                            })()}
                          </Section>
                          <Section label="Metrics" depth={2} defaultOpen={false}>
                            <SectionRow label="Order" value={String(node.order)} accent={col} />
                            <SectionRow label="Level" value={String(node.level)} />
                            <SectionRow label="Index" value={String(indexVal)} />
                          </Section>
                          <Section label="Elements" depth={2} defaultOpen={false} badge={node.elements.length}>
                            <SectionBody>
                              <div style={{ display: "flex", flexWrap: "wrap", gap: 4 }}>
                                {node.elements.map((el, i) => (
                                  <span key={i} style={{ fontSize: 11, color: col, fontWeight: "700", fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "2px 7px", border: `1px solid ${C.border}` }}>{el}</span>
                                ))}
                              </div>
                            </SectionBody>
                          </Section>
                          <Section label="Generators" depth={2} defaultOpen={false} badge={node.generators.length}>
                            <SectionBody>
                              {node.generators.length === 0
                                ? <span style={{ fontSize: 11, color: C.inkFaint }}>∅ trivial</span>
                                : <div style={{ display: "flex", flexDirection: "column", gap: 4 }}>
                                    {(node.generatorLabels ?? node.generators).map((g, i) => (
                                      <div key={i} style={{ fontSize: 11, color: C.inkMid, fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "3px 8px", border: `1px solid ${C.border}` }}>⟨{g.join(", ")}⟩</div>
                                    ))}
                                  </div>
                              }
                            </SectionBody>
                          </Section>
                          <Section label="Notes & Attributes" depth={1} defaultOpen={false}>
                              <SectionBody>
                                <div style={{ display: "flex", flexDirection: "column", gap: 8 }}>
                                  <div>
                                    <div style={{ fontSize: 8, letterSpacing: 1.5, color: C.inkFaint, textTransform: "uppercase", marginBottom: 4 }}>Node Description</div>
                                    <textarea 
                                      value={node.description || ''}
                                      onChange={e => {
                                        // You'll need to add this function
                                        updateNodeDescription(latticeId, node.id, e.target.value);
                                      }}
                                      placeholder="Add a description for this node..."
                                      style={{
                                        width: "100%",
                                        minHeight: 60,
                                        background: C.bg,
                                        border: `1px solid ${C.border}`,
                                        borderRadius: 3,
                                        color: C.ink,
                                        fontSize: 10,
                                        padding: "5px 7px",
                                        outline: "none",
                                        resize: "vertical",
                                        boxSizing: "border-box",
                                        fontFamily: "'Courier New', monospace",
                                        lineHeight: 1.5
                                      }}
                                    />
                                  </div>
                                </div>
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

          </div>
        )}
      </div>
    </div>
  );
}
