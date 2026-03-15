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
  const labels = [
    ...Array.from({ length: n }, (_, i) => i === 0 ? "e" : `a${i}`),
    ...Array.from({ length: n }, (_, i) => i === 0 ? "x" : `xa${i}`),
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
function cayleyDihedral(n) {
  return cayleyGraph(tableFromDihedral(n), "Dihedral", n, [1, n]); // r and s
}

// ═══════════════════════════════════════════════════════════════════════
//  CATALOG  (folder structure with categories)
//
//  LATTICE_CATEGORIES: category[] where category = {
//    key, label, groups: folder[]
//  }
//  folder = { key, label, desc, hasParam, ..., views: { key, label, build }[] }
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
          { key: "elements", label: "Ring",     build: n => elementRingCyclic(n) },
          { key: "cayley",   label: "Cayley",   build: n => cayleyCyclic(n) },
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
        key: "ZnZmZk", label: "ℤₙ×ℤₘ×ℤₖ", desc: "Triple direct product of cyclic groups",
        hasParam: true,  paramLabel: "n",  paramDefault: 2, paramMin: 2, paramMax: 6,
        hasParam2: true, paramLabel2: "m", paramDefault2: 2, paramMin2: 2, paramMax2: 6,
        hasParam3: true, paramLabel3: "k", paramDefault3: 2, paramMin3: 2, paramMax3: 6,
        views: [
          { key: "hasse",    label: "Hasse",    build: (n, m, k) => buildLatticeFromTable(tableFromTripleProduct(n, m ?? 2, k ?? 2), "ZnZmZk", n) },
          { key: "elements", label: "Grid",     build: (n, m, k) => elementGridZnZmZk(n, m ?? 2, k ?? 2) },
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
    ],
  },
  {
    key: "quaternion",
    label: "Quaternion Family",
    desc: "Quaternion and dicyclic groups",
    groups: [
      {
        key: "Q8", label: "Q₈", desc: "Quaternion group of order 8",
        hasParam: false, paramDefault: 8,
        views: [
          { key: "hasse",    label: "Hasse",    build: () => buildLatticeFromTable(tableFromQuaternion(), "Q8", 8) },
          { key: "elements", label: "Octagon",  build: () => elementRingQ8() },
        ],
      },
      {
        key: "Q12", label: "Q₁₂", desc: "Dicyclic group Dic₃ of order 12 — generalises Q₈",
        hasParam: false, paramDefault: 12,
        views: [
          { key: "hasse",    label: "Hasse",    build: () => buildLatticeFromTable(tableFromQ12(), "Q12", 12) },
          { key: "elements", label: "Rings",    build: () => elementRingQ12() },
        ],
      },
    ],
  },
  {
    key: "modular",
    label: "Modular",
    desc: "Multiplicative groups mod n",
    groups: [
      {
        key: "Un", label: "U(n)", desc: "Multiplicative group mod n",
        hasParam: true, paramLabel: "n", paramDefault: 18, paramMin: 2, paramMax: 200,
        views: [
          { key: "hasse",    label: "Hasse",    build: n => buildLatticeFromTable(tableFromUn(n), "Un", n) },
          { key: "elements", label: "Ring",     build: n => elementRingUn(n) },
        ],
      },
    ],
  },
  {
    key: "custom",
    label: "Custom",
    desc: "User-defined groups",
    groups: [
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
  const baseCol = orderColor(node.order, colorMap);
  const col = node._customColor ?? baseCol;
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
  const [selectedIds, setSelectedIds] = useState(new Set());
  const [morphisms, setMorphisms] = useState([]);
  const [morphismGroups, setMorphismGroups] = useState([]); // [{id, name, morphismIds:[]}]
  const [composeA, setComposeA] = useState(null);
  const [composeB, setComposeB] = useState(null);
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
  const [rightPane1Flex, setRightPane1Flex] = useState(0.9);
  const [rightPane2Flex, setRightPane2Flex] = useState(0.9);
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
  const [showSettingsModal, setShowSettingsModal] = useState(false);

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
    // Cancel button — skip placement
    if (e.target.closest && e.target.closest("[data-cancel]")) return;

    if (placingLatticeRef.current) {
      e.preventDefault();
      const rect = panelRef.current?.getBoundingClientRect();
      const cam = cameraRef.current;
      const worldX = (e.clientX - (rect?.left ?? 0) - cam.tx) / cam.scale;
      const worldY = (e.clientY - (rect?.top ?? 0) - cam.ty) / cam.scale;
      const { base, label } = placingLatticeRef.current;
      placeLatticeAt(base, label, worldX, worldY);
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
    const key = `${latticeId}:${nodeId}`;
    setSelectedIds(prev => { const next = new Set(prev); next.has(key) ? next.delete(key) : next.add(key); return next; });
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
    const fullNode = nodes[nodes.length - 1] ?? null;
    const accent = LATTICE_ACCENTS[idx % LATTICE_ACCENTS.length];
    const hlEdgeSet = new Set();
    const adjacentNodes = new Set();
    entry.base.edges.forEach(([a, b], i) => {
      const ka = `${entry.id}:${a}`, kb = `${entry.id}:${b}`;
      if (selectedIds.has(ka) || selectedIds.has(kb)) { hlEdgeSet.add(i); adjacentNodes.add(a); adjacentNodes.add(b); }
    });
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
      {showSettingsModal && (
        <div style={{ position: "fixed", inset: 0, zIndex: 200, background: "rgba(11,21,30,0.45)", display: "flex", alignItems: "center", justifyContent: "center" }}
          onClick={e => { if (e.target === e.currentTarget) setShowSettingsModal(false); }}>
          <div style={{ background: C.panelBg, border: `1.5px solid ${C.border}`, borderRadius: 12, padding: 0, width: 420, maxWidth: "92vw", boxShadow: "0 8px 40px rgba(11,21,30,0.22)", display: "flex", flexDirection: "column", overflow: "hidden" }}>
            {/* Header */}
            <div style={{ padding: "14px 18px", borderBottom: `1px solid ${C.border}`, display: "flex", alignItems: "center", gap: 8 }}>
              <svg width="14" height="14" viewBox="0 0 13 13" fill="none" style={{ flexShrink: 0 }}>
                <circle cx="6.5" cy="6.5" r="2" stroke={C.inkMid} strokeWidth="1.3"/>
                <path d="M6.5 1.5V2.5M6.5 10.5V11.5M1.5 6.5H2.5M10.5 6.5H11.5M3 3L3.7 3.7M9.3 9.3L10 10M3 10L3.7 9.3M9.3 3.7L10 3" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
              </svg>
              <span style={{ fontSize: 10, letterSpacing: 3, color: C.inkMid, textTransform: "uppercase", fontFamily: "'Courier New', monospace", fontWeight: "700", flex: 1 }}>Settings</span>
              <button onClick={() => setShowSettingsModal(false)} style={{ background: "none", border: "none", cursor: "pointer", color: C.inkFaint, fontSize: 16, lineHeight: 1, padding: "0 2px" }}>×</button>
            </div>

            <div style={{ padding: "16px 18px", display: "flex", flexDirection: "column", gap: 18 }}>
              {/* Grid section */}
              <div>
                <div style={{ fontSize: 8, letterSpacing: 2.5, color: C.inkFaint, textTransform: "uppercase", marginBottom: 10 }}>Canvas Grid</div>
                <div style={{ display: "flex", flexDirection: "column", gap: 10 }}>
                  {/* Pattern */}
                  <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
                    <span style={{ fontSize: 9, color: C.inkMid, minWidth: 52, letterSpacing: 1 }}>Pattern</span>
                    <div style={{ display: "flex", gap: 5 }}>
                      {[["lines","Lines"],["dots","Dots"],["cross","Cross"],["none","None"]].map(([val, lbl]) => (
                        <button key={val} onClick={() => setGridSettings(g => ({ ...g, pattern: val }))}
                          style={{ padding: "3px 9px", borderRadius: 4, fontSize: 9, cursor: "pointer", letterSpacing: 1, fontFamily: "'Courier New', monospace",
                            background: gridSettings.pattern === val ? C.inkMid : C.bg,
                            border: `1px solid ${gridSettings.pattern === val ? C.inkMid : C.border}`,
                            color: gridSettings.pattern === val ? C.panelBg : C.inkMid,
                            transition: "background 0.1s",
                          }}>{lbl}</button>
                      ))}
                    </div>
                  </div>
                  {/* Grid size */}
                  <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
                    <span style={{ fontSize: 9, color: C.inkMid, minWidth: 52, letterSpacing: 1 }}>Size</span>
                    <input type="range" min={16} max={80} value={gridSettings.size}
                      onChange={e => setGridSettings(g => ({ ...g, size: parseInt(e.target.value) }))}
                      style={{ flex: 1, accentColor: C.inkMid }} />
                    <span style={{ fontSize: 9, color: C.inkFaint, fontFamily: "'Courier New', monospace", minWidth: 24 }}>{gridSettings.size}</span>
                  </div>
                  {/* Grid color */}
                  <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
                    <span style={{ fontSize: 9, color: C.inkMid, minWidth: 52, letterSpacing: 1 }}>Color</span>
                    <div style={{ display: "flex", gap: 5, flexWrap: "wrap" }}>
                      {["#DEE7DC","#d4d4d8","#c7d2e8","#f3d8c0","#d4e8d4","#e8d4e8","#1e3d54"].map(col => (
                        <div key={col} onClick={() => setGridSettings(g => ({ ...g, color: col }))}
                          style={{ width: 18, height: 18, borderRadius: "50%", cursor: "pointer", background: col, border: gridSettings.color === col ? `2.5px solid ${C.ink}` : `1.5px solid ${C.border}`, boxSizing: "border-box", transition: "border 0.1s" }} />
                      ))}
                      <input type="color" value={gridSettings.color}
                        onChange={e => setGridSettings(g => ({ ...g, color: e.target.value }))}
                        style={{ width: 18, height: 18, borderRadius: "50%", border: "none", cursor: "pointer", padding: 0, background: "none" }} title="Custom color" />
                    </div>
                  </div>
                </div>
              </div>

              <div style={{ borderTop: `1px solid ${C.border}` }} />

              {/* Actions section */}
              <div>
                <div style={{ fontSize: 8, letterSpacing: 2.5, color: C.inkFaint, textTransform: "uppercase", marginBottom: 10 }}>Actions</div>
                <div style={{ display: "flex", flexDirection: "column", gap: 7 }}>
                  <button onClick={() => { setDrawStrokes([]); }}
                    style={{ display: "flex", alignItems: "center", gap: 8, padding: "8px 12px", borderRadius: 6, background: C.bg, border: `1px solid ${C.border}`, cursor: "pointer", textAlign: "left", transition: "background 0.1s" }}
                    onMouseEnter={e => e.currentTarget.style.background = C.selectedBg}
                    onMouseLeave={e => e.currentTarget.style.background = C.bg}>
                    <svg width="14" height="14" viewBox="0 0 14 14" fill="none">
                      <path d="M2 4H12M5 4V2.5H9V4M3 4L3.8 11.5H10.2L11 4" stroke={C.inkMid} strokeWidth="1.3" strokeLinejoin="round"/>
                    </svg>
                    <span style={{ fontSize: 10, color: C.inkMid, fontFamily: "'Courier New', monospace", letterSpacing: 1 }}>Clear all drawings</span>
                  </button>
                  <button onClick={() => { if (!panelRef.current) return; const r = panelRef.current.getBoundingClientRect(); setCamera({ tx: r.width / 4, ty: r.height / 4, scale: 0.75 }); }}
                    style={{ display: "flex", alignItems: "center", gap: 8, padding: "8px 12px", borderRadius: 6, background: C.bg, border: `1px solid ${C.border}`, cursor: "pointer", textAlign: "left", transition: "background 0.1s" }}
                    onMouseEnter={e => e.currentTarget.style.background = C.selectedBg}
                    onMouseLeave={e => e.currentTarget.style.background = C.bg}>
                    <svg width="14" height="14" viewBox="0 0 14 14" fill="none">
                      <path d="M2.5 7C2.5 4.5 4.5 2.5 7 2.5C9.5 2.5 11.5 4.5 11.5 7C11.5 9.5 9.5 11.5 7 11.5" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round"/>
                      <path d="M2.5 4.5V7H5" stroke={C.inkMid} strokeWidth="1.3" strokeLinecap="round" strokeLinejoin="round"/>
                    </svg>
                    <span style={{ fontSize: 10, color: C.inkMid, fontFamily: "'Courier New', monospace", letterSpacing: 1 }}>Reset camera view</span>
                  </button>
                  <button onClick={() => {
                    setLattices([]);
                    setDrawStrokes([]);
                    setNotes([]);
                    setMorphisms([]);
                    setSelectedIds(new Set());
                    setNodeCustomStyles({});
                    setGridSettings({ color: "#DEE7DC", size: 32, pattern: "lines" });
                    if (panelRef.current) { const r = panelRef.current.getBoundingClientRect(); setCamera({ tx: r.width / 4, ty: r.height / 4, scale: 0.75 }); }
                    setShowSettingsModal(false);
                  }}
                    style={{ display: "flex", alignItems: "center", gap: 8, padding: "8px 12px", borderRadius: 6, background: "#fef2f2", border: `1px solid #fca5a5`, cursor: "pointer", textAlign: "left", transition: "background 0.1s" }}
                    onMouseEnter={e => e.currentTarget.style.background = "#fee2e2"}
                    onMouseLeave={e => e.currentTarget.style.background = "#fef2f2"}>
                    <svg width="14" height="14" viewBox="0 0 14 14" fill="none">
                      <path d="M7 2C4.24 2 2 4.24 2 7s2.24 5 5 5 5-2.24 5-5" stroke="#ef4444" strokeWidth="1.3" strokeLinecap="round"/>
                      <path d="M10 2L12 4L10 6" stroke="#ef4444" strokeWidth="1.3" strokeLinecap="round" strokeLinejoin="round"/>
                    </svg>
                    <span style={{ fontSize: 10, color: "#ef4444", fontFamily: "'Courier New', monospace", letterSpacing: 1 }}>Reset entire workspace</span>
                  </button>
                </div>
              </div>
              <div style={{ borderTop: `1px solid ${C.border}` }} />

              {/* Shapes & Notation legend */}
              <div>
                <div style={{ fontSize: 8, letterSpacing: 2.5, color: C.inkFaint, textTransform: "uppercase", marginBottom: 10 }}>Shapes & Notation</div>
                <div style={{ display: "flex", flexDirection: "column", gap: 7 }}>
                  {[
                    ["circle",   "⟨a⟩",    "Cyclic / 1-generator"],
                    ["square",   "⟨a,b⟩",  "2-generator subgroup"],
                    ["triangle", "⟨a,b,c⟩","3-generator subgroup"],
                  ].map(([shape, notation, desc]) => (
                    <div key={shape} style={{ display: "flex", alignItems: "center", gap: 10 }}>
                      <svg width={16} height={16} style={{ flexShrink: 0 }}>
                        {shape === "circle"   && <circle cx={8} cy={8} r={6} fill="none" stroke={C.inkMid} strokeWidth={1.4}/>}
                        {shape === "square"   && <rect x={2} y={2} width={12} height={12} rx={1.5} fill="none" stroke={C.inkMid} strokeWidth={1.4}/>}
                        {shape === "triangle" && <polygon points="8,1 15,15 1,15" fill="none" stroke={C.inkMid} strokeWidth={1.4}/>}
                      </svg>
                      <span style={{ fontFamily: "'Courier New', monospace", fontSize: 10, color: "#0284c7", minWidth: 52 }}>{notation}</span>
                      <span style={{ fontSize: 9, color: C.inkFaint }}>{desc}</span>
                    </div>
                  ))}
                  <div style={{ borderTop: `1px solid ${C.border}`, paddingTop: 8, display: "flex", gap: 12, flexWrap: "wrap" }}>
                    {[
                      [<svg key="s" width={22} height={9}><line x1={0} y1={4.5} x2={22} y2={4.5} stroke={C.inkMid} strokeWidth={2}/></svg>, "1 gen. set"],
                      [<svg key="m" width={22} height={9}><line x1={0} y1={4.5} x2={22} y2={4.5} stroke={C.inkMid} strokeWidth={2} strokeDasharray="4 3"/></svg>, "multi gen."],
                      [<svg key="n" width={14} height={14}><circle cx={7} cy={7} r={5.5} fill="none" stroke="#4ade80" strokeWidth={2}/></svg>, "normal"],
                      [<span key="e" style={{ fontFamily: "'Courier New', monospace", fontSize: 10, color: "#f97316" }}>[a]</span>, "element"],
                    ].map(([icon, label], i) => (
                      <div key={i} style={{ display: "flex", alignItems: "center", gap: 5, fontSize: 9, color: C.inkFaint }}>{icon}{label}</div>
                    ))}
                  </div>
                </div>
              </div>
            </div>
            <div style={{ padding: "10px 18px", borderTop: `1px solid ${C.border}`, display: "flex", justifyContent: "flex-end" }}>
              <button onClick={() => setShowSettingsModal(false)}
                style={{ background: C.inkMid, border: "none", borderRadius: 6, padding: "6px 18px", cursor: "pointer", fontSize: 9, color: C.panelBg, letterSpacing: 2, textTransform: "uppercase", fontFamily: "'Courier New', monospace" }}>Done</button>
            </div>
          </div>
        </div>
      )}

      {/* ══════════════════════════════════════════════════════
          LEFT PANEL
      ══════════════════════════════════════════════════════ */}
      <div ref={leftPanelRef} style={{
        width: actualLeftW, flexShrink: 0, height: "100%",
        display: "flex", flexDirection: "column",
        background: C.panelBg, overflow: "hidden",
        transition: leftSplitDragging.current ? "none" : "width 0.2s ease",
        position: "relative",
        borderRight: actualLeftW > 0 ? `1px solid ${C.border}` : "none",
      }}>
        <CollapseBtn collapsed={leftCollapsed} onToggle={toggleLeft} side="left" />

        {actualLeftW > 40 && (
          <div style={{ flex: 1, minHeight: 0, display: "flex", flexDirection: "column", overflow: "hidden" }}>
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
                                    const base = view.build(p, p2, p3);
                                    const viewSuffix = view.key !== "hasse" ? ` [${view.label}]` : "";
                                    const numLabel = group.hasParam ? String(p) + (group.hasParam2 ? `×${p2}` : "") + (group.hasParam3 ? `×${p3}` : "") : "";
                                    const lbl = `${group.label.replace("ₙ", numLabel).replace("n", numLabel)}${viewSuffix}`;
                                    setError("");
                                    setSelectedViews(prev => ({ ...prev, [group.key]: view.key }));
                                    setPlacingLattice({ groupKey: group.key, viewKey: view.key, base, label: lbl });
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
            <div style={{ fontSize: 10, color: C.inkFaint, margin: "8px 14px", lineHeight: 1.6 }}>Click ☉ to stage · click canvas to place</div>
          </Pane>

          {leftPane1Open && leftPane2Open && <HPSplitter onDrag={onLeftSplit12} containerRef={leftPanelRef} />}

          {/* Pane 2: Morphisms */}
          <Pane title="Morphisms" open={leftPane2Open} onToggle={() => setLeftPane2Open(o => !o)} flex={leftPane2Flex} scrollClass="sky-scroll-left">
            {morphisms.length === 0
              ? <div style={{ fontSize: 11, color: C.inkFaint, fontStyle: "italic", padding: "4px 0" }}>No morphisms yet. Use the Ψ button on the canvas to create one.</div>
              : <div style={{ margin: "-12px -14px" }}>

                  {/* Individual morphisms */}
                  {morphisms.map(m => {
                    const isActive = activeMorphismId === m.id;
                    const analysis = analyzeMorphism(m.strands, lattices, latticeViews);
                    return (
                      <Section key={m.id} label={m.name} depth={0} accent={m.color}
                        badge={m.strands.length ? `${m.strands.length}s` : undefined}
                        defaultOpen={isActive}>
                        <SectionBody>
                          <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
                            {/* Rename input */}
                            <input
                              value={m.name}
                              onChange={e => setMorphisms(prev => prev.map(mx => mx.id === m.id ? { ...mx, name: e.target.value } : mx))}
                              style={{ flex: 1, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 3, color: C.ink, fontSize: 10, padding: "3px 6px", outline: "none", fontFamily: "'Courier New', monospace" }}
                            />
                            {/* Color dot = active toggle */}
                            <div title={isActive ? "Deactivate" : "Activate to draw strands"}
                              onClick={() => setActiveMorphismId(isActive ? null : m.id)} style={{
                              width: 14, height: 14, borderRadius: "50%", flexShrink: 0,
                              border: `2px solid ${m.color}`, background: isActive ? m.color : "transparent",
                              cursor: "pointer", transition: "background 0.15s",
                            }} />
                            <button onClick={() => { setMorphisms(prev => prev.filter(x => x.id !== m.id)); if (activeMorphismId === m.id) setActiveMorphismId(null); }}
                              style={{ background: "none", border: "none", cursor: "pointer", color: C.inkFaint, fontSize: 13, padding: "0 2px", lineHeight: 1 }}>×</button>
                          </div>
                          {isActive && <div style={{ marginTop: 5, fontSize: 9, color: m.color, letterSpacing: 1.5, textTransform: "uppercase" }}>↗ drag nodes on canvas to link</div>}
                        </SectionBody>

                        {m.strands.length > 0 && (
                          <Section label="Strands" depth={1} defaultOpen={false} badge={m.strands.length}>
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

                  {/* ── Compose / Combine ── */}
                  {morphisms.length >= 2 && (
                    <Section label="Compose" depth={0} defaultOpen={false}
                      badge="∘"
                      style={{ borderTop: `2px solid ${C.border}` }}>
                      <SectionBody>
                        <div style={{ fontSize: 9, color: C.inkFaint, lineHeight: 1.6, marginBottom: 8 }}>
                          Compose two morphisms φ∘ψ — the target of ψ must overlap the source of φ.
                        </div>
                      {(() => {
                          const cA = composeA ?? morphisms[0]?.id ?? null;
                          const cB = composeB ?? morphisms[1]?.id ?? null;
                          const sel = (id, set) => (
                            <select value={id ?? ""} onChange={e => set(Number(e.target.value))} style={{
                              flex: 1, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 3,
                              color: C.ink, fontSize: 10, padding: "3px 5px", fontFamily: "'Courier New', monospace", outline: "none",
                            }}>
                              {morphisms.map(m => <option key={m.id} value={m.id}>{m.name}</option>)}
                            </select>
                          );
                          return (
                            <div style={{ display: "flex", flexDirection: "column", gap: 7 }}>
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 9, color: C.inkFaint, minWidth: 12 }}>φ</span>
                                {sel(cA, setComposeA)}
                              </div>
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 9, color: C.inkFaint, minWidth: 12 }}>∘ψ</span>
                                {sel(cB, setComposeB)}
                              </div>
                              <button onClick={() => {
                                if (!cA || !cB || cA === cB) return;
                                const phi = morphisms.find(m => m.id === cA);
                                const psi = morphisms.find(m => m.id === cB);
                                if (!phi || !psi) return;
                                const composed = [];
                                for (const s1 of psi.strands) {
                                  for (const s2 of phi.strands) {
                                    if (s2.fromNodeId === s1.toNodeId && s2.fromLatticeId === s1.toLatticeId) {
                                      composed.push({ id: Date.now() + Math.random(), fromNodeId: s1.fromNodeId, fromLatticeId: s1.fromLatticeId, toNodeId: s2.toNodeId, toLatticeId: s2.toLatticeId });
                                    }
                                  }
                                }
                                if (composed.length === 0) return;
                                const newId = Date.now();
                                const color = MORPHISM_COLORS[morphisms.length % MORPHISM_COLORS.length];
                                setMorphisms(prev => [...prev, { id: newId, name: `${phi.name}∘${psi.name}`, color, strands: composed }]);
                                setActiveMorphismId(newId);
                              }} style={{
                                background: C.inkMid, border: "none", borderRadius: 4, color: C.panelBg,
                                fontSize: 9, letterSpacing: 2, textTransform: "uppercase",
                                padding: "5px 0", cursor: "pointer", fontFamily: "'Courier New', monospace", width: "100%",
                              }}>Compose φ∘ψ</button>
                            </div>
                          );
                        })()}
                      </SectionBody>
                    </Section>
                  )}

                  {/* ── Mapping Groups ── */}
                  <Section label="Mapping Groups" depth={0} defaultOpen={false} badge={morphismGroups.length || undefined}>
                    <SectionBody>
                      <div style={{ fontSize: 9, color: C.inkFaint, lineHeight: 1.6, marginBottom: 8 }}>
                        Associate multiple morphisms into a named mapping group (e.g. a commutative diagram or functor family).
                      </div>
                      {/* Existing groups */}
                      {morphismGroups.map(g => (
                        <div key={g.id} style={{ marginBottom: 8, background: C.bg, borderRadius: 5, border: `1px solid ${C.border}`, padding: "7px 9px" }}>
                          <div style={{ display: "flex", alignItems: "center", gap: 6, marginBottom: 5 }}>
                            <input value={g.name}
                              onChange={e => setMorphismGroups(prev => prev.map(x => x.id === g.id ? { ...x, name: e.target.value } : x))}
                              style={{ flex: 1, background: "transparent", border: "none", borderBottom: `1px solid ${C.border}`, color: C.ink, fontSize: 10, padding: "1px 3px", outline: "none", fontFamily: "'Courier New', monospace" }} />
                            <button onClick={() => setMorphismGroups(prev => prev.filter(x => x.id !== g.id))}
                              style={{ background: "none", border: "none", cursor: "pointer", color: C.inkFaint, fontSize: 13, padding: "0 2px", lineHeight: 1 }}>×</button>
                          </div>
                          <div style={{ display: "flex", flexWrap: "wrap", gap: 4 }}>
                            {morphisms.map(m => {
                              const included = g.morphismIds.includes(m.id);
                              return (
                                <div key={m.id} onClick={() => setMorphismGroups(prev => prev.map(x => x.id !== g.id ? x : {
                                  ...x, morphismIds: included ? x.morphismIds.filter(id => id !== m.id) : [...x.morphismIds, m.id]
                                }))} style={{
                                  padding: "2px 8px", borderRadius: 4, cursor: "pointer", fontSize: 9,
                                  fontFamily: "'Courier New', monospace", letterSpacing: 0.5,
                                  background: included ? m.color : C.panelBg,
                                  color: included ? "#fff" : C.inkFaint,
                                  border: `1.5px solid ${included ? m.color : C.border}`,
                                  transition: "all 0.12s",
                                }}>{m.name}</div>
                              );
                            })}
                          </div>
                          {g.morphismIds.length > 0 && (
                            <div style={{ marginTop: 5, fontSize: 9, color: C.inkFaint }}>
                              {g.morphismIds.map(id => morphisms.find(m => m.id === id)?.name).filter(Boolean).join(" · ")}
                            </div>
                          )}
                        </div>
                      ))}
                      <button onClick={() => {
                        const id = Date.now();
                        setMorphismGroups(prev => [...prev, { id, name: `Group ${prev.length + 1}`, morphismIds: [] }]);
                      }} style={{
                        width: "100%", background: C.panelBg, border: `1.5px dashed ${C.border}`, borderRadius: 5,
                        color: C.inkFaint, fontSize: 9, letterSpacing: 2, textTransform: "uppercase",
                        padding: "6px 0", cursor: "pointer", fontFamily: "'Courier New', monospace",
                        transition: "border-color 0.1s, color 0.1s",
                      }}
                        onMouseEnter={e => { e.currentTarget.style.borderColor = C.inkMid; e.currentTarget.style.color = C.inkMid; }}
                        onMouseLeave={e => { e.currentTarget.style.borderColor = C.border; e.currentTarget.style.color = C.inkFaint; }}>
                        + New Group
                      </button>
                    </SectionBody>
                  </Section>

                </div>
            }
          </Pane>

          {/* Left panel settings footer */}
          <div style={{
            flexShrink: 0, borderTop: `1px solid ${C.border}`,
            background: C.paneHeader, padding: "6px 10px",
            display: "flex", alignItems: "center", gap: 6,
          }}>
            <svg width="12" height="12" viewBox="0 0 12 12" fill="none" style={{ flexShrink: 0, opacity: 0.5 }}>
              <circle cx="6" cy="6" r="4.5" stroke={C.inkMid} strokeWidth="1.2"/>
              <circle cx="6" cy="6" r="1.5" fill={C.inkMid}/>
            </svg>
            <span style={{ fontSize: 8, letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", flex: 1 }}>Canvas</span>
            <button onClick={() => { if (!panelRef.current) return; const r = panelRef.current.getBoundingClientRect(); setCamera({ tx: r.width / 4, ty: r.height / 4, scale: 0.75 }); }}
              style={{ background: "none", border: `1px solid ${C.border}`, borderRadius: 4, padding: "2px 7px", cursor: "pointer", fontSize: 8, color: C.inkMid, letterSpacing: 1, fontFamily: "'Courier New', monospace" }}
              title="Reset camera">↺ reset</button>
            <button onClick={() => setSelectedIds(new Set())}
              style={{ background: "none", border: `1px solid ${C.border}`, borderRadius: 4, padding: "2px 7px", cursor: "pointer", fontSize: 8, color: C.inkMid, letterSpacing: 1, fontFamily: "'Courier New', monospace" }}
              title="Clear selection">✕ sel</button>
          </div>
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
              Lattice Lab
            </span>
            <button onClick={() => setShowSettingsModal(true)} title="Settings"
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
          <div data-cancel="true" onClick={() => { setPlacingLattice(null); setGhostMousePos(null); }}
            style={{ position: "absolute", top: 16, right: 16, zIndex: 21, background: C.border, border: "none", borderRadius: 4, cursor: "pointer", padding: "4px 10px", fontSize: 9, color: C.ink, letterSpacing: 2, textTransform: "uppercase", fontFamily: "'Courier New', monospace" }}>cancel</div>
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
          const setHoveredItem = setDrawMenuHovered;
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
            eraser: (a) => <svg width="18" height="18" viewBox="0 0 16 16" fill="none"><path d="M3 13H13" stroke={a?"#fff":"#ef4444"} strokeWidth="1.4" strokeLinecap="round"/><path d="M2 10L6 4L13 8L9 14" stroke={a?"#fff":"#ef4444"} strokeWidth="1.4" strokeLinejoin="round"/><path d="M6 4L9 14" stroke={a?"#fff":"#ef4444"} strokeWidth="1" opacity="0.5"/></svg>,
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
            <div style={{ position:"absolute", bottom:14, right:14, zIndex:14, display:"flex", flexDirection:"row", alignItems:"flex-end", gap:7 }}>

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

                    {/* ── Line ── */}
                    <div style={{...menuItemBase(hoveredItem==="line"), justifyContent:"space-between"}}
                      onMouseEnter={()=>setHoveredItem("line")} onMouseLeave={()=>setHoveredItem(null)}>
                      <div style={{display:"flex",alignItems:"center",gap:8}}>
                        {ICONS[drawLineStyle]?.(false) ?? ICONS.line(false)}
                        {tabLabel("Line", drawTool==="line")}
                      </div>
                      <span style={{fontSize:9,color:C.inkFaint}}>‹</span>
                      {hoveredItem==="line" && (
                        <div style={subMenuBox}>
                          {lineStyles.map(ls=>(
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
                        <div style={{...subMenuBox, padding:"10px 12px", minWidth:130}} onClick={e=>e.stopPropagation()}>
                          <div style={{fontSize:8,letterSpacing:2.5,color:C.inkFaint,textTransform:"uppercase",marginBottom:8}}>Stroke Weight</div>
                          <div style={{display:"flex",gap:6}}>
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
            <div style={{ position:"absolute", bottom:14, left:14, zIndex:14, display:"flex", flexDirection:"row", alignItems:"flex-end", gap:7 }}>

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
                  {/* Ψ (Psi) symbol */}
                  <svg width="30" height="30" viewBox="0 0 30 30" fill="none">
                    <path d="M15 4 C15 4 8 6 8 14 C8 19 11 22 15 23 C19 22 22 19 22 14 C22 6 15 4 15 4Z"
                      stroke={hasActive?"#fff":"#1e3d54"} strokeWidth="1.8" fill="none" strokeLinecap="round" strokeLinejoin="round"/>
                    <line x1="15" y1="23" x2="15" y2="28" stroke={hasActive?"#fff":"#1e3d54"} strokeWidth="1.8" strokeLinecap="round"/>
                    <line x1="11" y1="26" x2="19" y2="26" stroke={hasActive?"#fff":"#1e3d54"} strokeWidth="1.8" strokeLinecap="round"/>
                    <line x1="15" y1="4" x2="15" y2="12" stroke={hasActive?"#fff":"#1e3d54"} strokeWidth="1.8" strokeLinecap="round"/>
                  </svg>
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

        {/* Zoom reset — top right */}
        <div style={{ position: "absolute", top: 14, right: 14, zIndex: 3, display: "flex", gap: 6 }}>
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
      <div ref={rightPanelRef} style={{
        width: actualRightW, flexShrink: 0, height: "100%",
        display: "flex", flexDirection: "column",
        background: C.panelBg, overflow: "hidden",
        transition: rightSplitDragging.current ? "none" : "width 0.2s ease",
        position: "relative",
        borderLeft: actualRightW > 0 ? `1px solid ${C.border}` : "none",
      }}>
        <CollapseBtn collapsed={rightCollapsed} onToggle={toggleRight} side="right" />

        {actualRightW > 40 && (
          <div style={{ flex: 1, minHeight: 0, display: "flex", flexDirection: "column", overflow: "hidden" }}>

          {/* Pane 0: Graph Data */}
          <Pane title="Graph Data" open={rightPane1Open} onToggle={() => setRightPane1Open(o => !o)} flex={rightPane1Flex} scrollClass="sky-scroll-right">
            {lattices.length === 0
              ? <div style={{ color: C.inkFaint, fontSize: 11, fontStyle: "italic" }}>No graphs on canvas yet.</div>
              : <div style={{ margin: "-12px -14px" }}>
                  {lattices.map((l, idx) => {
                    const accent = LATTICE_ACCENTS[idx % LATTICE_ACCENTS.length];
                    const lv = latticeViews.find(v => v.entry.id === l.id);
                    return (
                      <Section key={l.id} label={l.label} depth={0} accent={accent} defaultOpen={lattices.length === 1} badge={`${l.base.nodes.length}n`}>
                        <SectionBody>
                          <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
                            <div style={{ flex: 1 }}>
                              <div style={{ fontSize: 8, color: C.inkFaint, letterSpacing: 1.5, textTransform: "uppercase", marginBottom: 2 }}>Kind · Nodes · Edges</div>
                              <div style={{ fontSize: 11, color: C.ink, fontFamily: "'Courier New', monospace" }}>{l.kind} · {l.base.nodes.length} · {l.base.edges.length}</div>
                            </div>
                            <button onClick={() => removeLattice(l.id)}
                              style={{ background: "none", border: `1px solid #fca5a5`, borderRadius: 4, cursor: "pointer", color: "#ef4444", fontSize: 11, padding: "2px 7px", flexShrink: 0 }}
                              title="Remove graph">✕</button>
                          </div>
                        </SectionBody>
                        {lv && (
                          <Section label="Order Colors" depth={1} defaultOpen={false}>
                            <SectionBody>
                              <div style={{ display: "flex", flexWrap: "wrap", gap: 6 }}>
                                {Object.entries(lv.colorMap).map(([ord, col]) => (
                                  <div key={ord} style={{ display: "flex", alignItems: "center", gap: 4, fontSize: 10, color: C.inkMid }}>
                                    <div style={{ width: 11, height: 11, borderRadius: "50%", background: col, flexShrink: 0, border: `1.5px solid ${C.border}` }} />
                                    <span style={{ fontFamily: "'Courier New', monospace" }}>|H|={ord}</span>
                                  </div>
                                ))}
                              </div>
                            </SectionBody>
                          </Section>
                        )}
                        {lv && (
                          <Section label="Subgroups" depth={1} defaultOpen={false} badge={lv.nodes.length}>
                            <SectionBody noPad>
                              <div style={{ padding: "6px 8px" }}>
                                {[...lv.nodes].sort((a, b) => a.order - b.order).map(node => {
                                  const key = `${l.id}:${node.id}`;
                                  return (
                                    <SubgroupRow key={node.id} node={node} colorMap={lv.colorMap}
                                      isSelected={selectedIds.has(key)}
                                      onToggle={() => setSelectedIds(prev => { const next = new Set(prev); next.has(key) ? next.delete(key) : next.add(key); return next; })} />
                                  );
                                })}
                              </div>
                            </SectionBody>
                          </Section>
                        )}
                      </Section>
                    );
                  })}
                </div>
            }
          </Pane>

          {rightPane1Open && rightPane2Open && <HPSplitter onDrag={onRightSplit12} containerRef={rightPanelRef} />}

          {/* Pane 1: Group Info */}
          <Pane title="Group Info" open={rightPane2Open} onToggle={() => setRightPane2Open(o => !o)} flex={rightPane2Flex} scrollClass="sky-scroll-right">
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

          {rightPane2Open && rightPane3Open && <HPSplitter onDrag={onRightSplit23} containerRef={rightPanelRef} />}

          {/* Pane 2: Selected nodes */}
          <Pane title={`Selected${allSelectedNodes.length > 1 ? ` (${allSelectedNodes.length})` : ""}`} open={rightPane3Open} onToggle={() => setRightPane3Open(o => !o)} flex={rightPane3Flex}>
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
                          {/* Notation context */}
                          <SectionRow
                            label="Notation"
                            value={node.viewType === "elements" ? `[${node.elements[0]}] — element` : `⟨·⟩ — subgroup`}
                            accent={node.viewType === "elements" ? "#f97316" : "#0284c7"}
                          />
                          <SectionBody>
                            <div style={{ fontSize: 11, color: C.ink, fontFamily: "'Courier New', monospace", wordBreak: "break-all", lineHeight: 1.5 }}>{node.label}</div>
                          </SectionBody>
                          {/* Style overrides */}
                          <SectionBody>
                            <div style={{ fontSize: 8, letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", marginBottom: 6 }}>Style Override</div>
                            <div style={{ display: "flex", flexDirection: "column", gap: 6 }}>
                              {/* Label alias */}
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1, minWidth: 36, flexShrink: 0 }}>Alias</span>
                                <input
                                  type="text"
                                  placeholder={node.shortLabel}
                                  value={nodeCustomStyles[`${latticeId}:${node.id}`]?.labelAlias ?? ""}
                                  onChange={e => setNodeCustomStyles(prev => ({
                                    ...prev,
                                    [`${latticeId}:${node.id}`]: { ...(prev[`${latticeId}:${node.id}`] ?? {}), labelAlias: e.target.value || undefined }
                                  }))}
                                  style={{ flex: 1, background: C.bg, border: `1px solid ${C.border}`, borderRadius: 3, color: C.ink, fontSize: 10, padding: "3px 6px", outline: "none", fontFamily: "'Courier New', monospace" }}
                                />
                              </div>
                              {/* Color override */}
                              <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                                <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1, minWidth: 36, flexShrink: 0 }}>Color</span>
                                <div style={{ display: "flex", gap: 5, flexWrap: "wrap" }}>
                                  {["#ef4444","#f97316","#ca8a04","#16a34a","#0284c7","#7c3aed","#db2777","#0891b2"].map(swatchCol => {
                                    const key = `${latticeId}:${node.id}`;
                                    const active = nodeCustomStyles[key]?.color === swatchCol;
                                    return (
                                      <div key={swatchCol}
                                        onClick={() => setNodeCustomStyles(prev => ({
                                          ...prev,
                                          [key]: { ...(prev[key] ?? {}), color: active ? undefined : swatchCol }
                                        }))}
                                        style={{
                                          width: 16, height: 16, borderRadius: "50%", cursor: "pointer",
                                          background: swatchCol, flexShrink: 0,
                                          border: active ? `2.5px solid ${C.ink}` : `1.5px solid transparent`,
                                          boxSizing: "border-box",
                                          boxShadow: active ? `0 0 0 1px #fff inset` : "none",
                                          transition: "border 0.1s",
                                        }} />
                                    );
                                  })}
                                  {nodeCustomStyles[`${latticeId}:${node.id}`]?.color && (
                                    <div onClick={() => setNodeCustomStyles(prev => {
                                      const next = { ...prev };
                                      if (next[`${latticeId}:${node.id}`]) { delete next[`${latticeId}:${node.id}`].color; }
                                      return next;
                                    })} style={{ width: 16, height: 16, borderRadius: "50%", cursor: "pointer", background: C.bg, border: `1px solid ${C.border}`, display: "flex", alignItems: "center", justifyContent: "center", fontSize: 10, color: C.inkFaint }}>×</div>
                                  )}
                                </div>
                              </div>
                            </div>
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

          {/* Right panel settings footer */}
          <div style={{
            flexShrink: 0, borderTop: `1px solid ${C.border}`,
            background: C.paneHeader, padding: "6px 10px",
            display: "flex", alignItems: "center", gap: 6,
          }}>
            <svg width="12" height="12" viewBox="0 0 12 12" fill="none" style={{ flexShrink: 0, opacity: 0.5 }}>
              <path d="M6 1.5L7.2 4H10L7.8 5.8L8.6 8.5L6 7L3.4 8.5L4.2 5.8L2 4H4.8Z" stroke={C.inkMid} strokeWidth="1.1" strokeLinejoin="round"/>
            </svg>
            <span style={{ fontSize: 8, letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", flex: 1 }}>Selection</span>
            {Object.keys(nodeCustomStyles).length > 0 && (
              <button onClick={() => setNodeCustomStyles({})}
                style={{ background: "none", border: `1px solid ${C.border}`, borderRadius: 4, padding: "2px 7px", cursor: "pointer", fontSize: 8, color: C.inkMid, letterSpacing: 1, fontFamily: "'Courier New', monospace" }}
                title="Clear all style overrides">✕ styles</button>
            )}
            <button onClick={() => setSelectedIds(new Set())}
              style={{ background: "none", border: `1px solid ${C.border}`, borderRadius: 4, padding: "2px 7px", cursor: "pointer", fontSize: 8, color: C.inkMid, letterSpacing: 1, fontFamily: "'Courier New', monospace" }}
              title="Deselect all">✕ sel</button>
          </div>
          </div>
        )}

        {/* Right panel bottom bar — always pinned */}
        <div style={{
          flexShrink: 0, borderTop: `2px solid ${C.border}`,
          background: C.panelBg, padding: "7px 10px",
          display: "flex", alignItems: "center", gap: 6,
          minHeight: 38,
        }}>
          {actualRightW > 40 && (
            <span style={{ fontSize: 8, letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", fontFamily: "'Courier New', monospace" }}>
              {allSelectedNodes.length > 0 ? `${allSelectedNodes.length} selected` : "no selection"}
            </span>
          )}
        </div>
      </div>
    </div>
  );
}
