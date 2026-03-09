import { useState, useEffect, useRef, useCallback } from "react";

// ═══════════════════════════════════════════════════════════════════════
//  TABLE ENGINE
//  Every group is defined by { table: number[][], labels: string[] }
//  table[i][j] = index of the product of element i and element j
//  Identity is always index 0.
// ═══════════════════════════════════════════════════════════════════════

// ── Generators ────────────────────────────────────────────────────────

function tableFromCyclic(n) {
  const table = Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) => (i + j) % n)
  );
  const labels = Array.from({ length: n }, (_, i) => i === 0 ? "e" : `r${i}`);
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
  const labels = [
    ...Array.from({ length: n }, (_, i) => i === 0 ? "e" : `r${i}`),
    ...Array.from({ length: n }, (_, i) => i === 0 ? "s" : `sr${i}`),
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
  const table = [
    [0,1,2,3,4,5,6,7],
    [1,0,3,2,5,4,7,6],
    [2,3,0,1,6,7,4,5],
    [3,2,1,0,7,6,5,4],
    [4,5,7,6,0,1,3,2],
    [5,4,6,7,1,0,2,3],
    [6,7,5,4,2,3,1,0],
    [7,6,4,5,3,2,0,1],
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
    const genStrs = gens.map(t => "⟨" + t.map(idx => labels[idx]).join(",") + "⟩");
    const genAll = genStrs.length === 0 ? "∅"
      : genStrs.length === 1 ? genStrs[0]
      : genStrs.slice(0, -1).join(", ") + " or " + genStrs[genStrs.length - 1];
    const shortLabel = sg.size === 1 ? "e"
      : gens.length > 0 ? "⟨" + gens[0].map(idx => labels[idx]).join(",") + "⟩"
      : "?";
    const elemArr = [...sg].sort((a, b) => a - b);
    const normal = isNormal(sg, table, inv);
    return {
      label: "{" + elemArr.map(idx => labels[idx]).join(",") + "}",
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
function formatZ(parts) { if (!parts.length) return "trivial"; return parts.map(p => "ℤ" + p).join(" × "); }
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
// (not a subgroup — each node IS one element)
function mkElemNode(label, orderOfElem, idx) {
  return {
    label, shortLabel: label,
    order: orderOfElem,        // order of this element in the group
    index: 1,
    elements: [label],
    elementIndices: [idx],
    generators: [],
    generatorLabels: [],
    genAll: label,
    isCyclic: true, rank: 1, shape: "circle", multiGen: false, isNormal: false,
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

// ── Cayley helpers for each group type ──
function cayleyCyclic(n) {
  return cayleyGraph(tableFromCyclic(n), "Zn", n, [1]); // generator r₁
}
function cayleyDihedral(n) {
  return cayleyGraph(tableFromDihedral(n), "Dihedral", n, [1, n]); // r and s
}

// ═══════════════════════════════════════════════════════════════════════
//  CATALOG  (folder structure with multiple views per group)
//
//  LATTICE_GROUPS: folder[] where folder = {
//    key, label, desc,
//    hasParam, paramLabel, paramDefault, paramMin, paramMax,
//    hasParam2, paramLabel2, paramDefault2, paramMin2, paramMax2,
//    isRaw?,
//    views: { key, label, build(p, p2?) }[]
//  }
// ═══════════════════════════════════════════════════════════════════════

const LATTICE_GROUPS = [
  {
    key: "Zn", label: "ℤₙ", desc: "Cyclic group of order n",
    hasParam: true, paramLabel: "n", paramDefault: 6, paramMin: 2, paramMax: 60,
    views: [
      { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromCyclic(n), "Zn", n) },
      { key: "elements", label: "Ring",     build: n => elementRingCyclic(n) },
      { key: "cayley",   label: "Cayley",   build: n => cayleyCyclic(n) },
    ],
  },
  {
    key: "Dihedral", label: "Dₙ", desc: "Dihedral group of order 2n",
    hasParam: true, paramLabel: "n", paramDefault: 4, paramMin: 2, paramMax: 12,
    views: [
      { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromDihedral(n), "Dihedral", n) },
      { key: "elements", label: "Rings",    build: n => elementRingDihedral(n) },
      { key: "cayley",   label: "Cayley",   build: n => cayleyDihedral(n) },
    ],
  },
  {
    key: "Symmetric", label: "Sₙ", desc: "Symmetric group on n letters",
    hasParam: true, paramLabel: "n", paramDefault: 3, paramMin: 2, paramMax: 4,
    views: [
      { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromSymmetric(n), "Symmetric", n) },
      { key: "elements", label: "Grid",     build: n => elementGridSymmetric(n) },
    ],
  },
  {
    key: "Un", label: "U(n)", desc: "Multiplicative group mod n",
    hasParam: true, paramLabel: "n", paramDefault: 18, paramMin: 2, paramMax: 200,
    views: [
      { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromUn(n), "Un", n) },
      { key: "elements", label: "Ring",     build: n => elementRingUn(n) },
    ],
  },
  {
    key: "Q8", label: "Q₈", desc: "Quaternion group",
    hasParam: false, paramDefault: 8,
    views: [
      { key: "hasse",    label: "Hasse",    build: () => buildLatticeFromTable(tableFromQuaternion(), "Q8", 8) },
      { key: "elements", label: "Octagon",  build: () => elementRingQ8() },
    ],
  },
  {
    key: "ZnxZm", label: "ℤₙ×ℤₘ", desc: "Direct product of two cyclic groups",
    hasParam: true, paramLabel: "n", paramDefault: 3, paramMin: 2, paramMax: 8,
    hasParam2: true, paramLabel2: "m", paramDefault2: 2, paramMin2: 2, paramMax2: 8,
    views: [
      { key: "hasse",    label: "Hasse",    build: (n, m) => buildLatticeFromTable(tableFromDirectProduct(tableFromCyclic(n), tableFromCyclic(m ?? 2)), "ZnxZm", n) },
      { key: "elements", label: "Grid",     build: (n, m) => elementGridZnZm(n, m ?? 2) },
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
];

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
  const srcIds = [...new Set(strands.map(s => s.fromLatticeId))];
  const tgtIds = [...new Set(strands.map(s => s.toLatticeId))];
  let isHomo = null;

  if (srcIds.length === 1 && tgtIds.length === 1) {
    const srcEntry = lattices.find(l => l.id === srcIds[0]);
    const tgtEntry = lattices.find(l => l.id === tgtIds[0]);
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
          const fabEntry = elementMap.get(`${srcIds[0]}:${ab}`);
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

function Pane({ title, children, flex, open, onToggle, scrollClass = "" }) {
  return (
    <div style={{
      display: "flex", flexDirection: "column",
      flex: open ? (flex ?? 1) : "0 0 auto",
      minHeight: 0, overflow: "hidden", flexShrink: open ? 1 : 0,
    }}>
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
        <div className={`sky-scroll ${scrollClass}`} style={{ flex: 1, overflowY: "auto", padding: "12px 14px", minHeight: 0 }}>
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

function Section({ label, badge, accent, defaultOpen = true, depth = 0, children }) {
  const [open, setOpen] = useState(defaultOpen);
  const ds = SECTION_DEPTH_STYLES[Math.min(depth, 2)];
  return (
    <div style={{ width: "100%" }}>
      <div onClick={() => setOpen(o => !o)} style={{
        display: "flex", alignItems: "center",
        padding: `${ds.paddingY}px 10px`, background: ds.bg,
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
        <div style={{ fontSize: 8, color: C.inkFaint, textTransform: "uppercase" }}>
          {node.isNormal ? "nml" : node.isCyclic ? "cyc" : node.order === 1 ? "triv" : "non"}
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

function Epicenter({ x, y, accent, onMouseDown }) {
  const R = 14;
  return (
    <g data-epicenter="true" style={{ cursor: "grab" }}
      onMouseDown={e => { e.preventDefault(); e.stopPropagation(); onMouseDown(e); }}>
      <circle cx={x} cy={y} r={R} fill="none" stroke={accent} strokeWidth={1.5} opacity={0.7} />
      <circle cx={x} cy={y} r={3} fill={accent} opacity={0.85} />
      <line x1={x - R - 5} y1={y} x2={x - R + 3} y2={y} stroke={accent} strokeWidth={1} opacity={0.5} />
      <line x1={x + R - 3} y1={y} x2={x + R + 5} y2={y} stroke={accent} strokeWidth={1} opacity={0.5} />
      <line x1={x} y1={y - R - 5} x2={x} y2={y - R + 3} stroke={accent} strokeWidth={1} opacity={0.5} />
      <line x1={x} y1={y + R - 3} x2={x} y2={y + R + 5} stroke={accent} strokeWidth={1} opacity={0.5} />
    </g>
  );
}

// ═══════════════════════════════════════════════════════════════════════
//  LATTICE ENTRY HELPERS  (unchanged)
// ═══════════════════════════════════════════════════════════════════════

let nextLatticeId = 1;
function makeLatticeEntry(base, canvasW, canvasH, labelOverride) {
  return {
    id: nextLatticeId++,
    label: labelOverride,
    kind: base.kind,
    param: base.param,
    base,
    nodePositions: {},
    epicenter: { x: canvasW / 2, y: canvasH / 2 },
    showArrows: true,
    showEdges: true,
    showEpicenter: true,
  };
}

function resolveNodes(entry) {
  return entry.base.nodes.map(n => ({
    ...n,
    x: (entry.nodePositions[n.id]?.x ?? n.x) + entry.epicenter.x - entry.base.W / 2,
    y: (entry.nodePositions[n.id]?.y ?? n.y) + entry.epicenter.y - entry.base.H / 2,
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
  const [catalogParams2, setCatalogParams2] = useState(
    Object.fromEntries(
      LATTICE_GROUPS.filter(c => c.hasParam2).map(c => [c.key, c.paramDefault2])
    )
  );
  // Which view is selected per group folder key (defaults to first view = "hasse")
  const [selectedViews, setSelectedViews] = useState(
    Object.fromEntries(LATTICE_GROUPS.map(g => [g.key, g.views[0].key]))
  );
  const [placingLattice, setPlacingLattice] = useState(null);
  const [showRawModal, setShowRawModal] = useState(false);
  const [selectedIds, setSelectedIds] = useState(new Set());
  const [morphisms, setMorphisms] = useState([]);
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
  const [rightPane1Flex, setRightPane1Flex] = useState(1);
  const [rightPane2Flex, setRightPane2Flex] = useState(1.4);

  const [camera, setCamera] = useState({ tx: 0, ty: 0, scale: 1 });
  const cameraRef = useRef({ tx: 0, ty: 0, scale: 1 });
  useEffect(() => { cameraRef.current = camera; }, [camera]);

  const panelRef = useRef(null);
  const containerRef = useRef(null);

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
  const [drawTool, setDrawTool] = useState(null); // null | "pen" | "line" | "arrow" | "rect" | "eraser"
  const [drawColor, setDrawColor] = useState("#1e3d54");
  const [drawSize, setDrawSize] = useState(2);
  const [drawStrokes, setDrawStrokes] = useState([]);
  const [drawPermanent, setDrawPermanent] = useState(true);
  const [colorPopOpen, setColorPopOpen] = useState(false);
  const drawPermRef = useRef(true);
  useEffect(() => { drawPermRef.current = drawPermanent; }, [drawPermanent]);
  const isDrawing = useRef(false);
  const currentStroke = useRef(null); // { id, tool, color, size, permanent, points[] | x1,y1,x2,y2 }
  const drawToolRef = useRef(null);
  useEffect(() => { drawToolRef.current = drawTool; }, [drawTool]);

  // ── Notes system ──────────────────────────────────────────────────
  const [notes, setNotes] = useState([]);
  const [editingNoteId, setEditingNoteId] = useState(null);
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

  // ── Initial lattice ───────────────────────────────────────────────
  useEffect(() => {
    const r = panelRef.current?.getBoundingClientRect();
    const cw = r?.width ?? 800, ch = r?.height ?? 600;
    const group = LATTICE_GROUPS.find(g => g.key === "Un");
    const view = group.views.find(v => v.key === "hasse");
    const base = view.build(18);
    const entry = makeLatticeEntry(base, cw, ch, "U(18)");
    setLattices([entry]);
  }, []);

  // ── Helpers ───────────────────────────────────────────────────────
  const updateLattice = useCallback((id, patch) => {
    setLattices(prev => prev.map(l => l.id === id ? { ...l, ...patch } : l));
  }, []);

  const placeLatticeAt = useCallback((base, label, worldX, worldY) => {
    const r = panelRef.current?.getBoundingClientRect();
    const cw = r?.width ?? 800, ch = r?.height ?? 600;
    const entry = makeLatticeEntry(base, cw, ch, label);
    entry.epicenter = { x: worldX, y: worldY };
    setLattices(prev => [...prev, entry]);
  }, []);

  const removeLattice = useCallback((id) => {
    setLattices(prev => prev.filter(l => l.id !== id));
    setSelectedIds(prev => {
      const next = new Set(prev);
      for (const k of next) { if (k.startsWith(`${id}:`)) next.delete(k); }
      return next;
    });
  }, []);

  // ── Node mouse-down (strand or drag) ─────────────────────────────
  const onNodeMouseDown = useCallback((latticeId, nodeId, e) => {
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
    const key = `${latticeId}:${nodeId}`;
    if (!selectedIds.has(key)) return;
    e.preventDefault(); e.stopPropagation();
    didDrag.current = false; didDragRef.current = false;
    const entry = lattices.find(l => l.id === latticeId);
    if (!entry) return;
    const nodes = resolveNodes(entry);
    const startPositions = {};
    for (const k of selectedIds) {
      const [lid, nid] = k.split(":").map(Number);
      if (lid !== latticeId) continue;
      const n = nodes.find(n => n.id === nid);
      if (n) startPositions[nid] = {
        x: entry.nodePositions[nid]?.x ?? (n.x - entry.epicenter.x + entry.base.W / 2),
        y: entry.nodePositions[nid]?.y ?? (n.y - entry.epicenter.y + entry.base.H / 2),
      };
    }
    nodeDragging.current = { latticeId, startMouseX: e.clientX, startMouseY: e.clientY, startPositions };
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
  }, [lattices, selectedIds, activeMorphismId]);

  const onEpicenterMouseDown = useCallback((latticeId, e) => {
    e.preventDefault(); e.stopPropagation();
    didDrag.current = false; didDragRef.current = false;
    const entry = lattices.find(l => l.id === latticeId);
    if (!entry) return;
    epicenterDragging.current = { latticeId, startMouseX: e.clientX, startMouseY: e.clientY, startEpicenter: { ...entry.epicenter } };
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
  }, [lattices]);

  const placingLatticeRef = useRef(null);
  useEffect(() => { placingLatticeRef.current = placingLattice; }, [placingLattice]);

  const onCanvasMouseDown = useCallback((e) => {
    if (e.target.closest && (e.target.closest("g[data-node]") || e.target.closest("g[data-epicenter]"))) return;
    // Note drag handled via note element's own onMouseDown — skip here if on a note
    if (e.target.closest && e.target.closest("[data-note]")) return;

    if (placingLatticeRef.current) {
      e.preventDefault();
      const rect = panelRef.current?.getBoundingClientRect();
      const cam = cameraRef.current;
      const worldX = (e.clientX - (rect?.left ?? 0) - cam.tx) / cam.scale;
      const worldY = (e.clientY - (rect?.top ?? 0) - cam.ty) / cam.scale;
      const { base, label } = placingLatticeRef.current;
      placeLatticeAt(base, label, worldX, worldY);
      setPlacingLattice(null);
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
        currentStroke.current = { id, tool, color: drawColor, size: drawSize, permanent: drawPermRef.current, x1: wx, y1: wy, x2: wx, y2: wy };
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
          currentStroke.current = { ...s, points: [...s.points, [wx, wy]] };
          setDrawStrokes(prev => {
            const idx = prev.findIndex(x => x.id === s.id);
            const updated = { ...currentStroke.current };
            return idx >= 0 ? prev.map((x, i) => i === idx ? updated : x) : [...prev, updated];
          });
        } else {
          currentStroke.current = { ...s, x2: wx, y2: wy };
          setDrawStrokes(prev => {
            const idx = prev.findIndex(x => x.id === s.id);
            const updated = { ...currentStroke.current };
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
          const toLatticeId = parseInt(el.getAttribute("data-lattice-id"));
          const toNodeId = parseInt(el.getAttribute("data-node-id"));
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
        if (s.tool === "pen" && s.points.length < 2) {
          // tiny dot — remove
          setDrawStrokes(prev => prev.filter(x => x.id !== s.id));
        }
        currentStroke.current = null;
      }
      isDrawing.current = false;
      noteDragging.current = null;

      if (isPanning.current && !didDrag.current) setSelectedIds(new Set());
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
        setDrawTool(null);
        setColorPopOpen(false);
        setDrawStrokes(prev => prev.filter(s => s.permanent));
        setEditingNoteId(null);
        setPlacingLattice(null);
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

  const onLeftSplit12 = useCallback((delta) => {
    if (!leftPane1Open || !leftPane2Open) return;
    setLeftPane1Flex(f => Math.max(0.15, f + delta / 120));
    setLeftPane2Flex(f => Math.max(0.15, f - delta / 120));
  }, [leftPane1Open, leftPane2Open]);
  const onLeftSplit23 = useCallback((delta) => {
    if (!leftPane2Open || !leftPane3Open) return;
    setLeftPane2Flex(f => Math.max(0.15, f + delta / 120));
    setLeftPane3Flex(f => Math.max(0.15, f - delta / 120));
  }, [leftPane2Open, leftPane3Open]);
  const onRightSplit12 = useCallback((delta) => {
    if (!rightPane1Open || !rightPane2Open) return;
    setRightPane1Flex(f => Math.max(0.15, f + delta / 120));
    setRightPane2Flex(f => Math.max(0.15, f - delta / 120));
  }, [rightPane1Open, rightPane2Open]);

  const toggleNodeSelect = useCallback((latticeId, nodeId) => {
    const key = `${latticeId}:${nodeId}`;
    setSelectedIds(prev => { const next = new Set(prev); next.has(key) ? next.delete(key) : next.add(key); return next; });
  }, []);

  // ── Derived views ─────────────────────────────────────────────────
  const latticeViews = lattices.map((entry, idx) => {
    const nodes = resolveNodes(entry);
    const colorMap = buildOrderColorMap(nodes);
    const fullNode = nodes[nodes.length - 1] ?? null;
    const accent = LATTICE_ACCENTS[idx % LATTICE_ACCENTS.length];
    const hlEdgeSet = new Set();
    const adjacentNodes = new Set();
    entry.base.edges.forEach(([a, b], i) => {
      const ka = `${entry.id}:${a}`, kb = `${entry.id}:${b}`;
      if (selectedIds.has(ka) || selectedIds.has(kb)) { hlEdgeSet.add(i); adjacentNodes.add(a); adjacentNodes.add(b); }
    });
    // U(n) specific extras (for right-panel isomorphism display)
    const unElems = entry.base.labels?.map((l, i) => ({ i, v: parseInt(l) })).filter(x => !isNaN(x.v) && entry.kind === "Un");
    const zParts = entry.kind === "Un" ? zStructureParts(entry.param) : [];
    const expVal = entry.kind === "Un" && unElems ? groupExponent(unElems.map(x => x.v).filter(v => v > 0), entry.param) : "—";
    return { entry, nodes, colorMap, fullNode, accent, hlEdgeSet, adjacentNodes, zParts, expVal };
  });

  const allSelectedNodes = latticeViews.flatMap(({ entry, nodes, colorMap, fullNode }) =>
    [...selectedIds]
      .filter(k => k.startsWith(`${entry.id}:`))
      .map(k => {
        const nodeId = parseInt(k.split(":")[1]);
        const node = nodes.find(n => n.id === nodeId);
        if (!node) return null;
        const indexVal = (fullNode && fullNode.order % node.order === 0) ? fullNode.order / node.order : "—";
        return { node, colorMap, latticeId: entry.id, latticeLabel: entry.label, indexVal, entry };
      })
      .filter(Boolean)
  );

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
          <Pane title="Graph Generation" open={leftPane1Open} onToggle={() => setLeftPane1Open(o => !o)} flex={leftPane1Flex} scrollClass="sky-scroll-left">
            <div style={{ margin: "-12px -14px" }}>
              {LATTICE_GROUPS.map(group => {
                const param  = catalogParams[group.key]  ?? group.paramDefault;
                const param2 = catalogParams2[group.key] ?? group.paramDefault2;
                const activeViewKey = selectedViews[group.key] ?? group.views[0].key;
                const isPlacing = placingLattice?.groupKey === group.key;

                return (
                  <Section key={group.key} label={group.label} depth={0} defaultOpen={false}
                    badge={group.views.length > 1 ? `${group.views.length} views` : undefined}>

                    {/* Param inputs */}
                    {(group.hasParam || group.hasParam2) && (
                      <SectionBody>
                        <div style={{ display: "flex", alignItems: "center", gap: 8, flexWrap: "wrap" }}>
                          {group.hasParam && (
                            <div style={{ display: "flex", alignItems: "center", gap: 4 }}>
                              <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1 }}>{group.paramLabel}</span>
                              <input type="number" value={param} min={group.paramMin} max={group.paramMax}
                                onChange={e => setCatalogParams(prev => ({ ...prev, [group.key]: parseInt(e.target.value) || group.paramDefault }))}
                                style={{ width: 48, background: C.bg, border: `1px solid ${C.borderHover}`, borderRadius: 3, color: C.ink, fontSize: 11, padding: "2px 5px", textAlign: "center", fontFamily: "'Courier New', monospace", outline: "none" }} />
                            </div>
                          )}
                          {group.hasParam2 && (
                            <div style={{ display: "flex", alignItems: "center", gap: 4 }}>
                              <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1 }}>{group.paramLabel2}</span>
                              <input type="number" value={param2} min={group.paramMin2} max={group.paramMax2}
                                onChange={e => setCatalogParams2(prev => ({ ...prev, [group.key]: parseInt(e.target.value) || group.paramDefault2 }))}
                                style={{ width: 48, background: C.bg, border: `1px solid ${C.borderHover}`, borderRadius: 3, color: C.ink, fontSize: 11, padding: "2px 5px", textAlign: "center", fontFamily: "'Courier New', monospace", outline: "none" }} />
                            </div>
                          )}
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
                          {/* View select dot */}
                          <div onClick={() => setSelectedViews(prev => ({ ...prev, [group.key]: view.key }))}
                            style={{
                              width: 10, height: 10, borderRadius: "50%", flexShrink: 0, cursor: "pointer",
                              border: `2px solid ${C.inkMid}`,
                              background: isActiveView ? C.inkMid : "transparent",
                              transition: "background 0.15s",
                            }} />
                          <span style={{ flex: 1, fontSize: 11, color: isActiveView ? C.ink : C.inkFaint, fontFamily: "'Courier New', monospace", letterSpacing: 1 }}>
                            {view.label}
                          </span>
                          {/* ☉ place button */}
                          <button title={`Place ${group.label} — ${view.label}`}
                            onClick={() => {
                              try {
                                if (group.isRaw) { setShowRawModal(true); return; }
                                const p  = group.hasParam  ? (param  || group.paramDefault)  : group.paramDefault;
                                const p2 = group.hasParam2 ? (param2 || group.paramDefault2) : undefined;
                                const base = view.build(p, p2);
                                const viewSuffix = view.key !== "hasse" ? ` [${view.label}]` : "";
                                const numLabel = group.hasParam ? String(p) + (group.hasParam2 ? `×${p2}` : "") : "";
                                const lbl = `${group.label.replace("ₙ", numLabel).replace("n", numLabel)}${viewSuffix}`;
                                setError("");
                                setSelectedViews(prev => ({ ...prev, [group.key]: view.key }));
                                setPlacingLattice({ groupKey: group.key, viewKey: view.key, base, label: lbl });
                              } catch (err) { setError(String(err)); }
                            }}
                            style={{
                              width: 24, height: 24, borderRadius: "50%", flexShrink: 0,
                              background: isThisPlacing ? C.ink : C.panelSurface,
                              border: `1.5px solid ${isThisPlacing ? C.ink : C.border}`,
                              cursor: "pointer", display: "flex", alignItems: "center", justifyContent: "center",
                              color: isThisPlacing ? C.panelBg : C.inkMid, fontSize: 12, lineHeight: 1,
                              transition: "background 0.13s, border-color 0.13s",
                            }}
                            onMouseEnter={e => { if (!isThisPlacing) { e.currentTarget.style.background = C.borderHover; e.currentTarget.style.borderColor = C.borderHover; } }}
                            onMouseLeave={e => { if (!isThisPlacing) { e.currentTarget.style.background = C.panelSurface; e.currentTarget.style.borderColor = C.border; } }}
                          >☉</button>
                        </div>
                      );
                    })}

                    {/* Desc */}
                    <SectionBody>
                      <div style={{ fontSize: 8, color: C.inkFaint, letterSpacing: 1, lineHeight: 1.6 }}>{group.desc}</div>
                    </SectionBody>
                  </Section>
                );
              })}
            </div>

            {error && <div style={{ color: "#f87171", fontSize: 10, margin: "8px 0 0" }}>{error}</div>}

            {lattices.length > 0 && <>
              <div style={{ fontSize: 10, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase", margin: "12px 0 6px" }}>Active</div>
              {lattices.map((l, idx) => {
                const accent = LATTICE_ACCENTS[idx % LATTICE_ACCENTS.length];
                return (
                  <div key={l.id} style={{
                    display: "flex", alignItems: "center", gap: 6, marginBottom: 4,
                    padding: "5px 8px", borderRadius: 4, background: C.panelSurface,
                    border: `1px solid ${C.border}`, borderLeft: `3px solid ${accent}`,
                  }}>
                    <span style={{ fontSize: 11, color: C.ink, fontFamily: "'Courier New', monospace", flex: 1 }}>{l.label}</span>
                    <span style={{ fontSize: 9, color: C.inkFaint }}>{l.base.nodes.length} nodes</span>
                    <button onClick={() => removeLattice(l.id)} style={{ background: "none", border: "none", cursor: "pointer", color: C.inkFaint, fontSize: 12, padding: "0 2px", lineHeight: 1 }} title="Remove">×</button>
                  </div>
                );
              })}
            </>}
            <div style={{ fontSize: 10, color: C.inkFaint, marginTop: 8, lineHeight: 1.6 }}>Click ☉ to place · drag selected to move</div>
          </Pane>

          {leftPane1Open && leftPane2Open && <HPSplitter onDrag={onLeftSplit12} />}

          {/* Pane 2: Morphisms */}
          <Pane title="Morphisms" open={leftPane2Open} onToggle={() => setLeftPane2Open(o => !o)} flex={leftPane2Flex} scrollClass="sky-scroll-left">
            <div style={{ marginBottom: 10 }}>
              <button onClick={() => {
                const id = Date.now();
                const color = MORPHISM_COLORS[morphisms.length % MORPHISM_COLORS.length];
                setMorphisms(prev => [...prev, { id, name: `φ${morphisms.length + 1}`, color, strands: [] }]);
                setActiveMorphismId(id);
              }} style={{
                width: "100%", background: C.ink, border: "none", borderRadius: 4,
                color: C.panelBg, fontSize: 10, letterSpacing: 3, textTransform: "uppercase",
                padding: "7px 0", cursor: "pointer", fontFamily: "'Courier New', monospace",
              }}>+ New Morphism</button>
            </div>

            {morphisms.length === 0
              ? <div style={{ fontSize: 11, color: C.inkFaint, fontStyle: "italic" }}>No morphisms yet. Create one to start drawing connections.</div>
              : <div style={{ margin: "-12px -14px" }}>
                  {morphisms.map(m => {
                    const isActive = activeMorphismId === m.id;
                    const analysis = analyzeMorphism(m.strands, lattices, latticeViews);
                    return (
                      <Section key={m.id} label={m.name} depth={0} accent={m.color}
                        badge={m.strands.length ? `${m.strands.length} strand${m.strands.length > 1 ? "s" : ""}` : undefined}
                        defaultOpen={isActive}>
                        <SectionBody>
                          <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
                            <label style={{ display: "flex", alignItems: "center", gap: 6, cursor: "pointer", flex: 1 }}>
                              <div onClick={() => setActiveMorphismId(isActive ? null : m.id)} style={{
                                width: 14, height: 14, borderRadius: "50%", flexShrink: 0,
                                border: `2px solid ${m.color}`, background: isActive ? m.color : "transparent",
                                cursor: "pointer", transition: "background 0.15s",
                              }} />
                              <span style={{ fontSize: 10, color: isActive ? C.ink : C.inkFaint, letterSpacing: 1 }}>
                                {isActive ? "Drawing strands ↗" : "Activate to draw"}
                              </span>
                            </label>
                            <button onClick={() => {
                              setMorphisms(prev => prev.filter(x => x.id !== m.id));
                              if (activeMorphismId === m.id) setActiveMorphismId(null);
                            }} style={{ background: "none", border: "none", cursor: "pointer", color: C.inkFaint, fontSize: 13, padding: "0 2px", lineHeight: 1 }}>×</button>
                          </div>
                          {isActive && <div style={{ marginTop: 6, fontSize: 9, color: m.color, letterSpacing: 1.5, textTransform: "uppercase" }}>↗ drag from any node to another</div>}
                        </SectionBody>

                        {m.strands.length > 0 && (
                          <Section label="Strands" depth={1} defaultOpen={true} badge={m.strands.length}>
                            {analysis.strandLabels.map((sl, i) => (
                              <div key={m.strands[i].id} style={{ padding: "5px 12px", borderBottom: `1px solid ${C.border}`, display: "flex", alignItems: "center", gap: 6 }}>
                                <div style={{ width: 7, height: 7, borderRadius: "50%", background: m.color, flexShrink: 0 }} />
                                <div style={{ flex: 1, minWidth: 0 }}>
                                  <div style={{ fontSize: 10, color: C.ink, fontFamily: "'Courier New', monospace", whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>{sl.from}</div>
                                  <div style={{ fontSize: 9, color: C.inkFaint, marginTop: 1 }}>↓ {sl.to}</div>
                                </div>
                                <div style={{ display: "flex", alignItems: "center", gap: 4, flexShrink: 0 }}>
                                  <span style={{ fontSize: 9, color: C.inkFaint }}>{sl.fromOrder}→{sl.toOrder}</span>
                                  <button onClick={() => setMorphisms(prev => prev.map(mx =>
                                    mx.id !== m.id ? mx : { ...mx, strands: mx.strands.filter(s => s.id !== m.strands[i].id) }
                                  ))} style={{ background: "none", border: "none", cursor: "pointer", color: C.inkFaint, fontSize: 12, padding: "0 2px", lineHeight: 1 }}>×</button>
                                </div>
                              </div>
                            ))}
                          </Section>
                        )}

                        {m.strands.length > 0 && (
                          <Section label="Analysis" depth={1} defaultOpen={false}>
                            <SectionRow label="Homo?" value={analysis.isHomo === null ? "n/a" : analysis.isHomo ? "yes ✓" : "no ✗"}
                              accent={analysis.isHomo === true ? "#4ade80" : analysis.isHomo === false ? "#f87171" : undefined} />
                            <SectionRow label="Injective" value={analysis.isInjective === null ? "n/a" : analysis.isInjective ? "yes ✓" : "no ✗"}
                              accent={analysis.isInjective === true ? "#4ade80" : analysis.isInjective === false ? "#f87171" : undefined} />
                            <SectionRow label="Surjective" value={analysis.isSurjective === null ? "n/a" : analysis.isSurjective ? "yes ✓" : "no ✗"}
                              accent={analysis.isSurjective === true ? "#4ade80" : analysis.isSurjective === false ? "#f87171" : undefined} />
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
                </div>
            }
          </Pane>

          {leftPane2Open && leftPane3Open && <HPSplitter onDrag={onLeftSplit23} />}

          {/* Pane 3: Legend & Key */}
          <Pane title="Legend & Key" open={leftPane3Open} onToggle={() => setLeftPane3Open(o => !o)} flex={leftPane3Flex} scrollClass="sky-scroll-left">
            <div style={{ margin: "-12px -14px" }}>
              <Section label="Shapes & Lines" depth={0} defaultOpen={false}>
                <SectionBody>
                  {[["circle","Single generator"],["square","Pair generators"],["triangle","Triple generators"]].map(([shape, label]) => (
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
                  <div style={{ borderTop: `1px solid ${C.border}`, margin: "6px 0" }} />
                  <div style={{ display: "flex", alignItems: "center", gap: 8, fontSize: 11, color: C.inkMid }}>
                    <svg width={18} height={18}><circle cx={9} cy={9} r={7} fill="none" stroke="#4ade80" strokeWidth={2} /></svg>
                    Normal subgroup
                  </div>
                </SectionBody>
              </Section>
              {latticeViews.map(({ entry, nodes, colorMap, accent }) => (
                <Section key={entry.id} label={`${entry.label} — Subgroups`} depth={0} accent={accent} defaultOpen={false} badge={nodes.length}>
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
        flex: 1, height: "100%", position: "relative", overflow: "hidden", background: C.bg,
        backgroundImage: `linear-gradient(to right, ${C.gridLine} 1px, transparent 1px), linear-gradient(to bottom, ${C.gridLine} 1px, transparent 1px)`,
        backgroundSize: `${32 * camera.scale}px ${32 * camera.scale}px`,
        backgroundPosition: `${camera.tx}px ${camera.ty}px`,
        cursor: placingLattice ? "crosshair" : drawTool === "eraser" ? "cell" : drawTool ? "crosshair" : "grab",
      }} onMouseDown={onCanvasMouseDown}
        onDoubleClick={e => {
          if (drawTool) return;
          if (e.target.closest && (e.target.closest("g[data-node]") || e.target.closest("[data-note]"))) return;
          const rect = panelRef.current?.getBoundingClientRect();
          const cam = cameraRef.current;
          const wx = (e.clientX - (rect?.left ?? 0) - cam.tx) / cam.scale;
          const wy = (e.clientY - (rect?.top ?? 0) - cam.ty) / cam.scale;
          addNote(wx, wy);
        }}>

        {placingLattice && (
          <div style={{ position: "absolute", inset: 0, zIndex: 20, pointerEvents: "none", display: "flex", alignItems: "flex-start", justifyContent: "center", paddingTop: 18 }}>
            <div style={{ background: C.ink, color: C.panelBg, borderRadius: 6, padding: "7px 16px", fontSize: 10, letterSpacing: 2.5, textTransform: "uppercase", fontFamily: "'Courier New', monospace", boxShadow: "0 2px 12px rgba(0,0,0,0.18)" }}>
              ☉ click to place {placingLattice.label}
            </div>
          </div>
        )}
        {placingLattice && (
          <div onClick={() => setPlacingLattice(null)} style={{ position: "absolute", top: 16, right: 16, zIndex: 21, background: C.border, border: "none", borderRadius: 4, cursor: "pointer", padding: "4px 10px", fontSize: 9, color: C.ink, letterSpacing: 2, textTransform: "uppercase", fontFamily: "'Courier New', monospace" }}>cancel</div>
        )}

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
            {latticeViews.flatMap(({ colorMap }) =>
              Object.entries(colorMap).map(([ord, col]) => (
                <marker key={`arr-${ord}`} id={`arr-${ord}`} markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                  <path d="M0,0 L0,6 L6,3 Z" fill={col} />
                </marker>
              ))
            )}
            {morphisms.map(m => (
              <marker key={m.id} id={`arr-${m.id}`} markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                <path d="M0,0 L0,6 L6,3 Z" fill={m.color} />
              </marker>
            ))}
          </defs>

          <g transform={`translate(${camera.tx}, ${camera.ty}) scale(${camera.scale})`}>
            {latticeViews.map(({ entry, nodes, colorMap, accent, hlEdgeSet, adjacentNodes }) => (
              <g key={entry.id}>
                {entry.showEdges && entry.base.edges.map(([a, b], i) => {
                  const na = nodes[a], nb = nodes[b];
                  if (!na || !nb) return null;
                  const hl = hlEdgeSet.has(i);
                  const col = hl ? orderColor(na.order, colorMap) : "#9aaa88";
                  const sw = hl ? 2.5 : 1.4;
                  const mx = (na.x + nb.x) / 2, my = (na.y + nb.y) / 2;
                  const markerId = hl ? `arr-${na.order}` : "arr";
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
                {nodes.map(node => <ShapeOccluder key={`occ-${node.id}`} node={node} R={26} />)}
                {nodes.map(node => {
                  const key = `${entry.id}:${node.id}`;
                  return (
                    <ShapeNode key={node.id} node={node} latticeId={entry.id} colorMap={colorMap}
                      isSelected={selectedIds.has(key)}
                      isAdjacent={adjacentNodes.has(node.id) && !selectedIds.has(key)}
                      isDrawMode={activeMorphismId !== null}
                      onToggleSelect={nodeId => toggleNodeSelect(entry.id, nodeId)}
                      onMouseDown={(nodeId, e) => onNodeMouseDown(entry.id, nodeId, e)} />
                  );
                })}
                {entry.showEpicenter && (
                  <Epicenter x={entry.epicenter.x} y={entry.epicenter.y} accent={accent} onMouseDown={(e) => onEpicenterMouseDown(entry.id, e)} />
                )}
              </g>
            ))}
          </g>

          {/* ── Draw strokes layer (world-space, inside camera transform) ── */}
          <g transform={`translate(${camera.tx}, ${camera.ty}) scale(${camera.scale})`} style={{ pointerEvents: "none" }}>
            <defs>
              <marker id="draw-arrow" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
                <path d="M0,0 L0,6 L7,3 Z" fill={drawColor} />
              </marker>
            </defs>
            {drawStrokes.map(s => {
              const tempStyle = s.permanent ? {} : { strokeDasharray: "5 4", opacity: 0.65 };
              if (s.tool === "pen") {
                if (s.points.length < 2) return null;
                const d = "M " + s.points.map(([x, y]) => `${x},${y}`).join(" L ");
                return <path key={s.id} d={d} stroke={s.color} strokeWidth={s.size} fill="none" strokeLinecap="round" strokeLinejoin="round" {...tempStyle} />;
              }
              if (s.tool === "line") {
                return <line key={s.id} x1={s.x1} y1={s.y1} x2={s.x2} y2={s.y2} stroke={s.color} strokeWidth={s.size} strokeLinecap="round" {...tempStyle} />;
              }
              if (s.tool === "arrow") {
                return <line key={s.id} x1={s.x1} y1={s.y1} x2={s.x2} y2={s.y2} stroke={s.color} strokeWidth={s.size} strokeLinecap="round" markerEnd="url(#draw-arrow)" {...tempStyle} />;
              }
              if (s.tool === "rect") {
                const x = Math.min(s.x1, s.x2), y = Math.min(s.y1, s.y2);
                const w = Math.abs(s.x2 - s.x1), h = Math.abs(s.y2 - s.y1);
                return <rect key={s.id} x={x} y={y} width={w} height={h} stroke={s.color} strokeWidth={s.size} fill="none" rx={2} {...tempStyle} />;
              }
              return null;
            })}
          </g>
        </svg>

        {/* Strand overlay */}
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
            return m.strands.map(s => {
              const srcLV = latticeViews.find(lv => lv.entry.id === s.fromLatticeId);
              const tgtLV = latticeViews.find(lv => lv.entry.id === s.toLatticeId);
              if (!srcLV || !tgtLV) return null;
              const srcNode = srcLV.nodes.find(n => n.id === s.fromNodeId);
              const tgtNode = tgtLV.nodes.find(n => n.id === s.toNodeId);
              if (!srcNode || !tgtNode) return null;
              const cam = camera;
              const x1 = srcNode.x * cam.scale + cam.tx, y1 = srcNode.y * cam.scale + cam.ty;
              const x2 = tgtNode.x * cam.scale + cam.tx, y2 = tgtNode.y * cam.scale + cam.ty;
              const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
              const dx = x2 - x1, dy = y2 - y1;
              const len = Math.sqrt(dx * dx + dy * dy) || 1;
              const arc = Math.min(90, len * 0.38);
              const cpx = mx - (dy / len) * arc, cpy = my + (dx / len) * arc;
              const pathD = `M ${x1} ${y1} Q ${cpx} ${cpy} ${x2} ${y2}`;
              return (
                <g key={s.id}>
                  {isActive && <path d={pathD} stroke={m.color} strokeWidth={7} fill="none" opacity={0.18} strokeLinecap="round" />}
                  <path d={pathD} stroke={m.color} strokeWidth={isActive ? 2.6 : 1.6} fill="none"
                    opacity={isActive ? 1 : 0.38} strokeDasharray={isActive ? undefined : "6 4"}
                    markerEnd={`url(#sarr-${m.id})`} />
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
          const fs = Math.min(13, Math.max(9, 11 * camera.scale));
          return (
            <div key={note.id} data-note="true" style={{
              position: "absolute", left: sx, top: sy,
              width: sw, height: isEditing ? Math.max(sh, 100) : sh,
              background: "#fff",
              border: `1.5px solid ${isEditing ? C.selectedBord : C.border}`,
              borderRadius: 5,
              boxShadow: isEditing
                ? `0 4px 18px rgba(11,21,30,0.16), 0 0 0 2px ${C.selectedBg}`
                : "0 2px 8px rgba(11,21,30,0.10)",
              zIndex: isEditing ? 15 : 10,
              cursor: isEditing ? "default" : "grab",
              display: "flex", flexDirection: "column",
              overflow: "hidden",
              transition: "box-shadow 0.15s, border-color 0.15s",
              userSelect: isEditing ? "text" : "none",
              fontFamily: "'Courier New', monospace",
            }}
              onMouseDown={e => {
                if (isEditing) return;
                e.preventDefault(); e.stopPropagation();
                noteDragging.current = { id: note.id, startMx: e.clientX, startMy: e.clientY, startX: note.x, startY: note.y };
              }}
              onDoubleClick={e => { e.stopPropagation(); setEditingNoteId(note.id); }}
            >
              {/* Title bar — matches pane header style */}
              <div style={{
                height: Math.max(18, 22 * camera.scale),
                background: C.paneHeader,
                borderBottom: `1px solid ${C.border}`,
                display: "flex", alignItems: "center", justifyContent: "space-between",
                padding: `0 ${Math.max(4, 6 * camera.scale)}px`,
                flexShrink: 0, cursor: "grab",
              }}>
                <span style={{ fontSize: Math.max(7, 8 * camera.scale), letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", userSelect: "none" }}>note</span>
                <button onMouseDown={e => e.stopPropagation()}
                  onClick={e => { e.stopPropagation(); removeNote(note.id); }}
                  style={{ background: "none", border: "none", cursor: "pointer", color: C.inkMid, fontSize: Math.max(10, 13 * camera.scale), lineHeight: 1, padding: "0 2px", opacity: 0.5, transition: "opacity 0.1s" }}
                  onMouseEnter={e => e.currentTarget.style.opacity = "1"}
                  onMouseLeave={e => e.currentTarget.style.opacity = "0.5"}
                >×</button>
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
            </div>
          );
        })}

        {/* ── Draw toolbar — bottom left ── */}
        {(() => {
          // color palette used in both toolbar and popout
          const PALETTE = [
            ["#0B151E","#1e3d54","#3a6278","#93b5c8"],
            ["#ef4444","#f97316","#ca8a04","#16a34a"],
            ["#0284c7","#7c3aed","#db2777","#0891b2"],
          ];
          const toolBtnStyle = (active) => ({
            width: 30, height: 30, borderRadius: 5, flexShrink: 0,
            background: active ? C.inkMid : "#fff",
            border: `1.5px solid ${active ? C.inkMid : C.border}`,
            cursor: "pointer", color: active ? "#fff" : C.inkMid,
            fontSize: 13, display: "flex", alignItems: "center", justifyContent: "center",
            transition: "background 0.12s, border-color 0.12s",
            fontFamily: "'Courier New', monospace",
          });
          const sep = <div style={{ width: 1, height: 22, background: C.border, margin: "0 3px", flexShrink: 0 }} />;

          return (
            <div style={{ position: "absolute", bottom: 14, left: 14, zIndex: 14, display: "flex", flexDirection: "column", alignItems: "flex-start", gap: 6 }}>

              {/* Color pop-out panel — floats above toolbar */}
              {colorPopOpen && (
                <div style={{
                  background: "#fff",
                  border: `1.5px solid ${C.border}`,
                  borderRadius: 8,
                  padding: "10px 12px",
                  boxShadow: "0 4px 16px rgba(11,21,30,0.14)",
                  display: "flex", flexDirection: "column", gap: 8,
                }}>
                  <div style={{ fontSize: 8, letterSpacing: 2.5, color: C.inkFaint, textTransform: "uppercase" }}>Color</div>
                  {PALETTE.map((row, ri) => (
                    <div key={ri} style={{ display: "flex", gap: 7 }}>
                      {row.map(col => (
                        <div key={col} onClick={() => setDrawColor(col)} style={{
                          width: 20, height: 20, borderRadius: "50%", cursor: "pointer",
                          background: col, flexShrink: 0,
                          border: drawColor === col ? `3px solid ${C.inkMid}` : `1.5px solid ${col === "#fff" ? C.border : "transparent"}`,
                          boxSizing: "border-box",
                          boxShadow: drawColor === col ? `0 0 0 1.5px #fff inset` : "none",
                          transition: "border 0.1s, box-shadow 0.1s",
                        }} />
                      ))}
                    </div>
                  ))}
                  <div style={{ borderTop: `1px solid ${C.border}`, paddingTop: 7, display: "flex", alignItems: "center", gap: 6 }}>
                    <div style={{ width: 20, height: 20, borderRadius: "50%", background: drawColor, border: `1.5px solid ${C.border}`, flexShrink: 0 }} />
                    <input type="text" value={drawColor}
                      onChange={e => { if (/^#[0-9a-fA-F]{0,6}$/.test(e.target.value)) setDrawColor(e.target.value); }}
                      style={{
                        flex: 1, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 3,
                        color: C.inkMid, fontSize: 10, padding: "3px 6px", outline: "none",
                        fontFamily: "'Courier New', monospace", letterSpacing: 1,
                      }} />
                  </div>
                </div>
              )}

              {/* Main toolbar pill */}
              <div style={{
                display: "flex", alignItems: "center", gap: 4,
                background: "#fff",
                border: `1.5px solid ${C.border}`,
                borderRadius: 10,
                padding: "5px 8px",
                boxShadow: "0 2px 10px rgba(11,21,30,0.10)",
              }}>

                {/* Draw tools */}
                {[
                  { key: "pen",    icon: "✏",  title: "Freehand pen" },
                  { key: "line",   icon: "╱",  title: "Straight line" },
                  { key: "arrow",  icon: "→",  title: "Arrow" },
                  { key: "rect",   icon: "▭",  title: "Rectangle" },
                  { key: "eraser", icon: "◻",  title: "Eraser" },
                ].map(t => (
                  <button key={t.key} title={t.title}
                    onClick={() => {
                      const next = drawTool === t.key ? null : t.key;
                      if (!next) setDrawStrokes(prev => prev.filter(s => s.permanent));
                      setDrawTool(next);
                    }}
                    style={toolBtnStyle(drawTool === t.key)}
                    onMouseEnter={e => { if (drawTool !== t.key) { e.currentTarget.style.background = C.selectedBg; e.currentTarget.style.borderColor = C.selectedBord; } }}
                    onMouseLeave={e => { if (drawTool !== t.key) { e.currentTarget.style.background = "#fff"; e.currentTarget.style.borderColor = C.border; } }}
                  >{t.icon}</button>
                ))}

                {sep}

                {/* Color swatch button — opens pop-out */}
                <button title="Color" onClick={() => setColorPopOpen(o => !o)} style={{
                  width: 30, height: 30, borderRadius: 5, flexShrink: 0,
                  background: "#fff",
                  border: `1.5px solid ${colorPopOpen ? C.selectedBord : C.border}`,
                  cursor: "pointer", display: "flex", alignItems: "center", justifyContent: "center",
                  transition: "border-color 0.12s", padding: 5,
                }}>
                  <div style={{
                    width: 16, height: 16, borderRadius: "50%",
                    background: drawColor,
                    border: `1.5px solid ${C.border}`,
                    boxSizing: "border-box",
                  }} />
                </button>

                {sep}

                {/* Size picker — three line-weight options */}
                {[
                  { sz: 1, w: 10, h: 1.5 },
                  { sz: 2, w: 12, h: 3 },
                  { sz: 4, w: 14, h: 5 },
                ].map(({ sz, w, h }) => (
                  <button key={sz} title={`Weight ${sz}`} onClick={() => setDrawSize(sz)} style={{
                    width: 30, height: 30, borderRadius: 5, flexShrink: 0,
                    background: drawSize === sz ? C.selectedBg : "#fff",
                    border: `1.5px solid ${drawSize === sz ? C.selectedBord : C.border}`,
                    cursor: "pointer", display: "flex", alignItems: "center", justifyContent: "center",
                    transition: "background 0.1s, border-color 0.1s",
                  }}
                    onMouseEnter={e => { if (drawSize !== sz) { e.currentTarget.style.background = C.selectedBg; } }}
                    onMouseLeave={e => { if (drawSize !== sz) { e.currentTarget.style.background = "#fff"; } }}
                  >
                    <div style={{ width: w, height: h, background: C.inkMid, borderRadius: h }} />
                  </button>
                ))}

                {sep}

                {/* Permanent / Temporary toggle */}
                <button title={drawPermanent ? "Permanent — strokes stay" : "Temporary — strokes clear when tool is off"}
                  onClick={() => setDrawPermanent(p => !p)}
                  style={{
                    height: 30, borderRadius: 5, flexShrink: 0,
                    padding: "0 9px",
                    background: drawPermanent ? C.inkMid : "#fff",
                    border: `1.5px solid ${drawPermanent ? C.inkMid : C.border}`,
                    cursor: "pointer",
                    display: "flex", alignItems: "center", gap: 5,
                    transition: "background 0.15s, border-color 0.15s",
                  }}
                  onMouseEnter={e => { if (!drawPermanent) { e.currentTarget.style.background = C.selectedBg; e.currentTarget.style.borderColor = C.selectedBord; } }}
                  onMouseLeave={e => { if (!drawPermanent) { e.currentTarget.style.background = "#fff"; e.currentTarget.style.borderColor = C.border; } }}
                >
                  <span style={{ fontSize: 11, color: drawPermanent ? "#fff" : C.inkFaint }}>
                    {drawPermanent ? "⬤" : "○"}
                  </span>
                  <span style={{
                    fontSize: 8, letterSpacing: 2, textTransform: "uppercase",
                    fontFamily: "'Courier New', monospace",
                    color: drawPermanent ? "#fff" : C.inkFaint,
                  }}>
                    {drawPermanent ? "perm" : "temp"}
                  </span>
                </button>

                {sep}

                {/* Note button */}
                <button title="Add note · or double-click canvas"
                  onClick={() => {
                    const rect = panelRef.current?.getBoundingClientRect();
                    const cam = cameraRef.current;
                    const wx = ((rect?.width ?? 800) / 2 - cam.tx) / cam.scale;
                    const wy = ((rect?.height ?? 600) / 2 - cam.ty) / cam.scale;
                    addNote(wx, wy);
                  }}
                  style={toolBtnStyle(false)}
                  onMouseEnter={e => { e.currentTarget.style.background = C.selectedBg; e.currentTarget.style.borderColor = C.selectedBord; }}
                  onMouseLeave={e => { e.currentTarget.style.background = "#fff"; e.currentTarget.style.borderColor = C.border; }}
                >
                  <span style={{ fontSize: 12 }}>▤</span>
                </button>

                {/* Clear permanent strokes */}
                {drawStrokes.some(s => s.permanent) && (
                  <button title="Clear all permanent drawings"
                    onClick={() => setDrawStrokes(prev => prev.filter(s => !s.permanent))}
                    style={{
                      width: 30, height: 30, borderRadius: 5, flexShrink: 0,
                      background: "#fff", border: `1.5px solid #fca5a5`,
                      cursor: "pointer", color: "#ef4444", fontSize: 11,
                      display: "flex", alignItems: "center", justifyContent: "center",
                      transition: "background 0.12s",
                    }}
                    onMouseEnter={e => { e.currentTarget.style.background = "#fef2f2"; }}
                    onMouseLeave={e => { e.currentTarget.style.background = "#fff"; }}
                  >✕</button>
                )}
              </div>
            </div>
          );
        })()}

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
          {/* Pane 1: Group Info */}
          <Pane title="Group Info" open={rightPane1Open} onToggle={() => setRightPane1Open(o => !o)} flex={rightPane1Flex}>
            {latticeViews.length === 0
              ? <div style={{ color: C.inkFaint, fontSize: 11 }}>No lattices added.</div>
              : <div style={{ margin: "-12px -14px" }}>
                  {latticeViews.map(({ entry, nodes, fullNode, colorMap, accent, zParts, expVal }) => (
                    <Section key={entry.id} label={entry.label} depth={0} accent={accent} defaultOpen={latticeViews.length === 1}>
                      <Section label="Stats" depth={1} defaultOpen={false}>
                        <SectionBody>
                          <div style={{ marginBottom: 8, padding: "5px 8px", background: C.statsRow, borderRadius: 4, border: `1px solid ${C.border}` }}>
                            <div style={{ fontSize: 8, letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", marginBottom: 2 }}>
                              {entry.kind === "Un" ? "Isomorphism Type" : "Structure"}
                            </div>
                            <div style={{ fontSize: 13, fontWeight: "700", color: C.ink, fontFamily: "'Courier New', monospace", wordBreak: "break-all" }}>
                              {entry.kind === "Un" ? `U(${entry.param}) ≅ ${formatZ(zParts)}` : entry.label}
                            </div>
                          </div>
                        </SectionBody>
                        {fullNode && [
                          [`|G|`, fullNode.order],
                          ["Nodes", nodes.length],
                          ["Levels", (entry.base.maxLevel ?? 0) + 1],
                          ["Edges", entry.base.edges.length],
                          ...(entry.kind === "Un" ? [["Exponent", expVal], ["Abelian", "yes"]] : []),
                        ].map(([k, v]) => <SectionRow key={k} label={k} value={String(v)} accent={k === "Abelian" ? "#4ade80" : undefined} />)}
                      </Section>
                      <Section label="Display" depth={1} defaultOpen={false}>
                        <SectionToggle label="Show Edges" checked={entry.showEdges} onChange={v => updateLattice(entry.id, { showEdges: v })} />
                        <SectionToggle label="Show Arrows" checked={entry.showArrows} onChange={v => updateLattice(entry.id, { showArrows: v })} />
                        <SectionToggle label="Show Epicenter ☉" checked={entry.showEpicenter} onChange={v => updateLattice(entry.id, { showEpicenter: v })} />
                        <SectionBody>
                          <div style={{ fontSize: 9, color: C.inkFaint, lineHeight: 1.6 }}>Drag the ☉ marker on the canvas to move the entire lattice.</div>
                        </SectionBody>
                      </Section>
                    </Section>
                  ))}
                </div>
            }
          </Pane>

          {rightPane1Open && rightPane2Open && <HPSplitter onDrag={onRightSplit12} />}

          {/* Pane 2: Selected nodes */}
          <Pane title={`Selected${allSelectedNodes.length > 1 ? ` (${allSelectedNodes.length})` : ""}`} open={rightPane2Open} onToggle={() => setRightPane2Open(o => !o)} flex={rightPane2Flex}>
            {allSelectedNodes.length > 0
              ? <div style={{ margin: "-12px -14px" }}>
                  {allSelectedNodes.map(({ node, colorMap, latticeId, latticeLabel, indexVal, entry }) => {
                    const col = orderColor(node.order, colorMap);
                    const cyclicLabel = node.order === 1 ? "Trivial" : node.isCyclic ? "Cyclic" : node.shape === "square" ? "Non-cyclic · pair gens" : "Non-cyclic · triple gens";
                    return (
                      <Section key={`${latticeId}:${node.id}`} label={node.shortLabel} badge={`ord ${node.order}`} accent={col} depth={0} defaultOpen={false}>
                        <Section label="Label & Style" depth={1} defaultOpen={false}>
                          <SectionRow label="Group" value={latticeLabel} />
                          <SectionRow label="Type" value={cyclicLabel} />
                          <SectionRow label="Normal" value={node.isNormal ? "yes ✓" : "no"} accent={node.isNormal ? "#4ade80" : undefined} />
                          {node.isCyclic && node.order > 1 && <SectionRow label="Iso" value={`ℤ${node.order}`} accent={col} />}
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
                                      <div key={i} style={{ fontSize: 11, color: C.inkMid, fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "3px 8px", border: `1px solid ${C.border}` }}>
                                        ⟨{g.join(", ")}⟩
                                      </div>
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
