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
//  GENERIC LATTICE LAYOUT ENGINE
//  Takes a list of {id, label, shortLabel, order, elements, generators,
//  genAll, isCyclic, rank, shape, multiGen} nodes and a list of
//  cover-relation edges [i,j] (i covered by j), computes x/y layout.
// ═══════════════════════════════════════════════════════════════════════

function layoutLattice(rawNodes, coverEdges) {
  const n = rawNodes.length;
  if (n === 0) return { nodes: [], edges: [], maxLevel: 0, byLevel: {}, W: 400, H: 400, nodeR: 26 };

  // BFS from node 0 (assumed bottom) to assign levels
  const levels = new Array(n).fill(-1);
  levels[0] = 0;
  const q = [0];
  while (q.length) {
    const cur = q.shift();
    for (const [a, b] of coverEdges) {
      if (a === cur && levels[b] === -1) { levels[b] = levels[cur] + 1; q.push(b); }
    }
  }
  // Any unreached nodes get level by reverse BFS from top
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
    ...rn,
    id: i, level: levels[i], x: posX[i], y: posY[i],
  }));
  return { nodes, edges: coverEdges, maxLevel, byLevel, W, H, nodeR: NODE_R };
}

// Helper: make a node descriptor from raw parts
function mkNode(label, shortLabel, order, elements = [], generators = [], isCyclic = true, rank = 1, multiGen = false) {
  const shape = rank <= 1 ? "circle" : rank === 2 ? "square" : "triangle";
  const genStrs = generators.map(t => Array.isArray(t) ? "⟨" + t.join(",") + "⟩" : "⟨" + t + "⟩");
  const genAll = genStrs.length === 0 ? "∅" : genStrs.length === 1 ? genStrs[0]
    : genStrs.slice(0, -1).join(", ") + " or " + genStrs[genStrs.length - 1];
  return { label, shortLabel, order, elements, generators, genAll, isCyclic, rank, shape, multiGen };
}

// ── ℤₙ — Cyclic group: subgroup lattice = divisors of n, ordered by divisibility ──
function computeCyclicLattice(n) {
  const divs = [];
  for (let d = 1; d <= n; d++) if (n % d === 0) divs.push(d);
  divs.sort((a, b) => a - b);
  const idx = d => divs.indexOf(d);
  // Nodes: one per divisor d, representing the unique subgroup of order d
  const nodes = divs.map(d => {
    const gen = d === 1 ? [] : [n / d]; // generator of subgroup of order d in ℤₙ
    return mkNode(
      d === 1 ? "{0}" : `ℤ${d}`,
      d === 1 ? "0" : `ℤ${d}`,
      d, [], gen.length ? [gen] : [], d > 1, gen.length ? 1 : 0
    );
  });
  // Edges: d₁ → d₂ if d₁|d₂ and no d₃ with d₁|d₃|d₂ strictly between
  const edges = [];
  for (let i = 0; i < divs.length; i++)
    for (let j = i + 1; j < divs.length; j++) {
      if (divs[j] % divs[i] === 0) {
        const hasMiddle = divs.some((d, k) => k !== i && k !== j && divs[j] % d === 0 && d % divs[i] === 0);
        if (!hasMiddle) edges.push([i, j]);
      }
    }
  return { ...layoutLattice(nodes, edges), kind: "Zn", param: n };
}

// ── Div(n) — Divisibility poset of integers up to n ──
function computeDivPoset(n) {
  const nums = Array.from({ length: n }, (_, i) => i + 1);
  const nodes = nums.map(k => mkNode(String(k), String(k), k, [k], [[k]], true, 1));
  const edges = [];
  for (let i = 0; i < n; i++)
    for (let j = i + 1; j < n; j++) {
      if (nums[j] % nums[i] === 0) {
        const hasMiddle = nums.some((d, k) => k !== i && k !== j && nums[j] % d === 0 && d % nums[i] === 0);
        if (!hasMiddle) edges.push([i, j]);
      }
    }
  return { ...layoutLattice(nodes, edges), kind: "Div", param: n };
}

// ── Bool(n) — Boolean lattice 2^[n]: subsets of {1..n} ordered by inclusion ──
function computeBoolLattice(n) {
  const N = 1 << n;
  const nodes = [];
  for (let mask = 0; mask < N; mask++) {
    const els = [];
    for (let b = 0; b < n; b++) if (mask & (1 << b)) els.push(b + 1);
    const lbl = els.length === 0 ? "∅" : "{" + els.join(",") + "}";
    nodes.push(mkNode(lbl, lbl, els.length, els, els.length ? [els] : [], true, Math.max(els.length, 1)));
  }
  // Edges: mask1 → mask2 if mask2 = mask1 | (1<<k) for some k (cover = add one element)
  const edges = [];
  for (let i = 0; i < N; i++)
    for (let b = 0; b < n; b++) {
      if (!(i & (1 << b))) {
        const j = i | (1 << b);
        edges.push([i, j]);
      }
    }
  return { ...layoutLattice(nodes, edges), kind: "Bool", param: n };
}

// ── BinTree(n) — Complete binary tree poset, depth 0..n ──
function computeBinTree(n) {
  // Nodes: indexed by BFS order. Root = 0, children of k = 2k+1, 2k+2
  const total = (1 << (n + 1)) - 1;
  const nodes = [];
  const depth = i => Math.floor(Math.log2(i + 1));
  for (let i = 0; i < total; i++) {
    const d = depth(i);
    const pos = i - ((1 << d) - 1) + 1; // 1-indexed position in level
    const lbl = `(${d},${pos})`;
    nodes.push(mkNode(lbl, lbl, d + 1, [i], [[i]], true, 1));
  }
  // Edges: parent → child (parent of i is floor((i-1)/2))
  const edges = [];
  for (let i = 1; i < total; i++) {
    edges.push([Math.floor((i - 1) / 2), i]);
  }
  return { ...layoutLattice(nodes, edges), kind: "BinTree", param: n };
}

// ── Dₙ — Dihedral group: subgroups laid out by inclusion ──
function computeDihedralLattice(n) {
  // Subgroups of D_n (order 2n):
  // - For each d|n: cyclic subgroup ⟨r^(n/d)⟩ of order d
  // - For each d|n, for each k=0..d-1: dihedral subgroup D_d generated by r^(n/d) and s·r^k·(some coset)
  //   Actually for D_n: subgroups are ⟨r^d⟩ for d|n (cyclic, order n/d) and ⟨r^d, s·r^k⟩ for d|n, k=0..d-1 (dihedral, order 2n/d)
  //   But we'll simplify: list the distinct subgroups by isomorphism type and containment.
  const divs = [];
  for (let d = 1; d <= n; d++) if (n % d === 0) divs.push(d);
  const nodes = [];
  const nodeIndex = {};

  // Trivial
  nodes.push(mkNode("{e}", "e", 1, ["e"], [], false, 0));
  nodeIndex["C1"] = 0;

  // Cyclic subgroups ⟨r^k⟩ for each d|n, d>1: order d, one each
  divs.filter(d => d > 1).forEach(d => {
    const i = nodes.length;
    nodeIndex[`C${d}`] = i;
    nodes.push(mkNode(`ℤ${d}`, `ℤ${d}`, d, [], [[`r^${n/d}`]], true, 1));
  });

  // Dihedral subgroups D_d for each d|n: order 2d (d≥1), n/d copies but we label by d
  // For simplicity show one representative per order
  divs.forEach(d => {
    const i = nodes.length;
    nodeIndex[`D${d}`] = i;
    const lbl = d === 1 ? "ℤ₂" : `D${d}`;
    const shortLbl = d === 1 ? "ℤ₂" : `D${d}`;
    nodes.push(mkNode(lbl, shortLbl, 2 * d, [], [[`r^${n/d}`, "s"]], false, 2));
  });

  // Full group D_n
  const topIdx = nodes.length;
  nodes.push(mkNode(`D${n}`, `D${n}`, 2 * n, [], [["r", "s"]], false, 2));

  // Edges — containment:
  const edges = [];
  // C1 ⊂ Cd for each prime-order step in divisibility
  // C1 ⊂ D1
  edges.push([nodeIndex["C1"], nodeIndex["D1"]]);
  // C1 ⊂ Cp for each prime p|n
  divs.filter(d => d > 1).forEach(d => {
    const isMinCyclic = !divs.some(d2 => d2 > 1 && d2 < d && d % d2 === 0);
    if (isMinCyclic) edges.push([nodeIndex["C1"], nodeIndex[`C${d}`]]);
  });

  // Cyclic containment: Cd ⊂ Ce if d|e (cover only)
  divs.filter(d => d > 1).forEach(d => {
    divs.filter(e => e > d && e % d === 0).forEach(e => {
      const hasMiddle = divs.some(m => m !== d && m !== e && e % m === 0 && m % d === 0);
      if (!hasMiddle) edges.push([nodeIndex[`C${d}`], nodeIndex[`C${e}`]]);
    });
  });

  // Cyclic ⊂ Dihedral: Cd ⊂ Dd
  divs.filter(d => d > 1).forEach(d => edges.push([nodeIndex[`C${d}`], nodeIndex[`D${d}`]]));
  // D1 = ℤ₂ is covered by D_d for smallest d
  // Dihedral containment: Dd ⊂ De if d|e (cover only)
  divs.forEach(d => {
    divs.filter(e => e > d && e % d === 0).forEach(e => {
      const hasMiddle = divs.some(m => m !== d && m !== e && e % m === 0 && m % d === 0);
      if (!hasMiddle) edges.push([nodeIndex[`D${d}`], nodeIndex[`D${e}`]]);
    });
  });

  // All maximal subgroups → full group
  const maxNodes = new Set(nodes.map((_, i) => i));
  maxNodes.delete(topIdx);
  for (const [, j] of edges) maxNodes.delete(j); // non-roots in edge targets still ok... better:
  // Just connect maximal elements to top
  const pointedTo = new Set(edges.map(([, b]) => b));
  const reachableFromTop = new Set();
  // Find all nodes that eventually reach top - instead just connect "maximal" ones
  // Maximal = not pointed to by anything that isn't the top
  const below = new Set(edges.filter(([, b]) => b !== topIdx).map(([a]) => a).concat(edges.filter(([, b]) => b !== topIdx).map(([, b]) => b)));
  // Simpler: Cn ⊂ Dn, and Dn is top when n=n
  // Cn → topIdx, Dn → topIdx
  if (nodeIndex[`C${n}`] !== undefined) edges.push([nodeIndex[`C${n}`], topIdx]);
  edges.push([nodeIndex[`D${n}`], topIdx]); // D_n = full group, skip self-loop guard
  // Remove duplicates
  const edgeSet = new Set(edges.map(([a,b]) => `${a}:${b}`));
  const cleanEdges = [...edgeSet].map(s => s.split(":").map(Number));

  return { ...layoutLattice(nodes, cleanEdges), kind: "Dihedral", param: n };
}

// ── Q₈ — Quaternion group: fixed subgroup lattice ──
function computeQuaternionLattice() {
  // Q8 = {±1, ±i, ±j, ±k}, order 8
  // Subgroups: {1}, {±1}, {±1,±i}, {±1,±j}, {±1,±k}, Q8
  const nodes = [
    mkNode("{1}",       "1",    1, ["1"],                 [],             false, 0),
    mkNode("{±1}",      "±1",   2, ["1","-1"],            [["-1"]],        true,  1),
    mkNode("{±1,±i}",   "⟨i⟩",  4, ["1","-1","i","-i"],   [["i"]],         true,  1),
    mkNode("{±1,±j}",   "⟨j⟩",  4, ["1","-1","j","-j"],   [["j"]],         true,  1),
    mkNode("{±1,±k}",   "⟨k⟩",  4, ["1","-1","k","-k"],   [["k"]],         true,  1),
    mkNode("Q₈",        "Q₈",   8, ["1","-1","i","-i","j","-j","k","-k"], [["i","j"]], false, 2),
  ];
  const edges = [
    [0, 1],  // {1} ⊂ {±1}
    [1, 2], [1, 3], [1, 4], // {±1} ⊂ ⟨i⟩,⟨j⟩,⟨k⟩
    [2, 5], [3, 5], [4, 5], // ⟨i⟩,⟨j⟩,⟨k⟩ ⊂ Q8
  ];
  return { ...layoutLattice(nodes, edges), kind: "Q8", param: 8 };
}

// ── S₃ — Symmetric group on 3 elements ──
function computeS3Lattice() {
  const nodes = [
    mkNode("{e}",               "e",      1,  ["e"],              [],                    false, 0),
    mkNode("{e,(12)}",          "⟨(12)⟩", 2,  ["e","(12)"],      [["(12)"]],             true,  1),
    mkNode("{e,(13)}",          "⟨(13)⟩", 2,  ["e","(13)"],      [["(13)"]],             true,  1),
    mkNode("{e,(23)}",          "⟨(23)⟩", 2,  ["e","(23)"],      [["(23)"]],             true,  1),
    mkNode("{e,(123),(132)}",   "⟨(123)⟩",3,  ["e","(123)","(132)"], [["(123)"]],        true,  1),
    mkNode("S₃",                "S₃",     6,  ["e","(12)","(13)","(23)","(123)","(132)"],
           [["(12)","(123)"]], false, 2),
  ];
  const edges = [
    [0,1],[0,2],[0,3],[0,4],
    [1,5],[2,5],[3,5],[4,5],
  ];
  return { ...layoutLattice(nodes, edges), kind: "S3", param: 3 };
}

// ── S₄ — Symmetric group on 4 elements ──
function computeS4Lattice() {
  // Key subgroups of S₄ (simplified / representative set)
  const nodes = [
    mkNode("{e}",           "e",         1,  [],  [],              false, 0), // 0
    mkNode("ℤ₂ (transpos)","⟨(12)⟩",   2,  [],  [["(12)"]],      true,  1), // 1
    mkNode("ℤ₂ (transpos)","⟨(13)⟩",   2,  [],  [["(13)"]],      true,  1), // 2
    mkNode("ℤ₂ (transpos)","⟨(14)⟩",   2,  [],  [["(14)"]],      true,  1), // 3
    mkNode("ℤ₂ (transpos)","⟨(23)⟩",   2,  [],  [["(23)"]],      true,  1), // 4
    mkNode("ℤ₂ (transpos)","⟨(24)⟩",   2,  [],  [["(24)"]],      true,  1), // 5
    mkNode("ℤ₂ (transpos)","⟨(34)⟩",   2,  [],  [["(34)"]],      true,  1), // 6
    mkNode("ℤ₂ (dbl-transp)","⟨(12)(34)⟩",2,[],[["(12)(34)"]],  true,  1), // 7
    mkNode("ℤ₂ (dbl-transp)","⟨(13)(24)⟩",2,[],[["(13)(24)"]],  true,  1), // 8
    mkNode("ℤ₂ (dbl-transp)","⟨(14)(23)⟩",2,[],[["(14)(23)"]],  true,  1), // 9
    mkNode("ℤ₃",           "⟨(123)⟩",  3,  [],  [["(123)"]],     true,  1), // 10
    mkNode("ℤ₃",           "⟨(124)⟩",  3,  [],  [["(124)"]],     true,  1), // 11
    mkNode("ℤ₃",           "⟨(134)⟩",  3,  [],  [["(134)"]],     true,  1), // 12
    mkNode("ℤ₃",           "⟨(234)⟩",  3,  [],  [["(234)"]],     true,  1), // 13
    mkNode("V₄ (Klein)",   "V₄",        4,  [],  [["(12)(34)","(13)(24)"]], false, 2), // 14
    mkNode("ℤ₄",           "⟨(1234)⟩", 4,  [],  [["(1234)"]],    true,  1), // 15
    mkNode("ℤ₄",           "⟨(1243)⟩", 4,  [],  [["(1243)"]],    true,  1), // 16
    mkNode("ℤ₄",           "⟨(1324)⟩", 4,  [],  [["(1324)"]],    true,  1), // 17
    mkNode("D₂≅V₄",        "D₂",        4,  [],  [["(12)","(34)"]], false, 2), // 18
    mkNode("D₂≅V₄",        "D₂",        4,  [],  [["(13)","(24)"]], false, 2), // 19
    mkNode("D₂≅V₄",        "D₂",        4,  [],  [["(14)","(23)"]], false, 2), // 20
    mkNode("A₄",           "A₄",        12, [],  [["(12)(34)","(123)"]], false, 2), // 21
    mkNode("D₄",           "D₄",        8,  [],  [["(1234)","(13)"]], false, 2),  // 22
    mkNode("D₄",           "D₄",        8,  [],  [["(1243)","(12)"]], false, 2),  // 23
    mkNode("D₄",           "D₄",        8,  [],  [["(1324)","(14)"]], false, 2),  // 24
    mkNode("S₄",           "S₄",        24, [],  [["(12)","(1234)"]], false, 2), // 25
  ];
  const edges = [
    // e → order-2
    [0,1],[0,2],[0,3],[0,4],[0,5],[0,6],[0,7],[0,8],[0,9],
    // e → order-3
    [0,10],[0,11],[0,12],[0,13],
    // order-2 double transpositions → V₄
    [7,14],[8,14],[9,14],
    // order-2 → D₂ variants
    [1,18],[6,18],[7,18],
    [2,19],[5,19],[8,19],
    [3,20],[4,20],[9,20],
    // order-2 transpositions → ℤ₄ (via containment in D₄)
    [1,15],[2,15],[3,16],[5,16],[4,17],[6,17],
    // V₄ → A₄
    [14,21],
    // order-3 → A₄
    [10,21],[11,21],[12,21],[13,21],
    // D₂ variants → D₄
    [18,22],[15,22],
    [19,23],[16,23],
    [20,24],[17,24],
    // V₄ → D₄ (V₄ normal in D₄)
    [14,22],[14,23],[14,24],
    // → S₄
    [21,25],[22,25],[23,25],[24,25],
  ];
  return { ...layoutLattice(nodes, edges), kind: "S4", param: 4 };
}

// ── Registry of all lattice types ──
const LATTICE_CATALOG = [
  {
    key: "Un",    label: "U(n)",      symbol: "U",
    desc: "Multiplicative group mod n",
    hasParam: true, paramLabel: "n", paramDefault: 18, paramMin: 2, paramMax: 200,
    build: n => {
      const base = computeLattice(n);
      return { ...base, kind: "Un", param: n };
    },
  },
  {
    key: "Zn",    label: "ℤₙ",        symbol: "ℤ",
    desc: "Cyclic group of order n",
    hasParam: true, paramLabel: "n", paramDefault: 12, paramMin: 2, paramMax: 100,
    build: computeCyclicLattice,
  },
  {
    key: "Div",   label: "Div(n)",    symbol: "D",
    desc: "Divisibility lattice of integers 1…n",
    hasParam: true, paramLabel: "n", paramDefault: 12, paramMin: 2, paramMax: 30,
    build: computeDivPoset,
  },
  {
    key: "Bool",  label: "𝟐ⁿ",        symbol: "B",
    desc: "Boolean lattice — power set of n elements",
    hasParam: true, paramLabel: "n", paramDefault: 3, paramMin: 1, paramMax: 5,
    build: computeBoolLattice,
  },
  {
    key: "BinTree", label: "Tree(n)", symbol: "T",
    desc: "Complete binary tree of depth n",
    hasParam: true, paramLabel: "n (depth)", paramDefault: 3, paramMin: 1, paramMax: 5,
    build: computeBinTree,
  },
  {
    key: "Dihedral", label: "Dₙ",    symbol: "D",
    desc: "Dihedral group of order 2n",
    hasParam: true, paramLabel: "n", paramDefault: 6, paramMin: 2, paramMax: 12,
    build: computeDihedralLattice,
  },
  {
    key: "Q8",    label: "Q₈",        symbol: "Q",
    desc: "Quaternion group",
    hasParam: false, paramDefault: 8,
    build: computeQuaternionLattice,
  },
  {
    key: "S3",    label: "S₃",        symbol: "S",
    desc: "Symmetric group on 3 letters",
    hasParam: false, paramDefault: 3,
    build: computeS3Lattice,
  },
  {
    key: "S4",    label: "S₄",        symbol: "S",
    desc: "Symmetric group on 4 letters",
    hasParam: false, paramDefault: 4,
    build: computeS4Lattice,
  },
];

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
//  MORPHISM COLORS & MATH
// ═══════════════════════════════════════════════════════════════════════

const MORPHISM_COLORS = ["#f59e0b","#10b981","#ef4444","#8b5cf6","#06b6d4","#f97316","#ec4899","#84cc16"];

/**
 * analyzeMorphism — takes a list of strands (using the new from/to fields) and
 * returns homomorphism properties as well as a list of label objects for the UI.
 */
function analyzeMorphism(strands, lattices, latticeViews) {
  if (!strands.length) return { isHomo: null, isInjective: null, isSurjective: null, kernel: [], image: [], strandLabels: [] };

  // ---- Build human‑readable labels for each strand ----
  const strandLabels = strands.map(s => {
    const srcLV = latticeViews.find(lv => lv.entry.id === s.fromLatticeId);
    const tgtLV = latticeViews.find(lv => lv.entry.id === s.toLatticeId);
    const srcN = srcLV?.nodes.find(n => n.id === s.fromNodeId);
    const tgtN = tgtLV?.nodes.find(n => n.id === s.toNodeId);
    return {
      from: srcN ? `${srcN.shortLabel} ⊆ U(${srcLV.entry.x})` : "?",
      to:   tgtN ? `${tgtN.shortLabel} ⊆ U(${tgtLV.entry.x})` : "?",
      fromOrder: srcN?.order ?? 0,
      toOrder:   tgtN?.order ?? 0,
    };
  });

  // ---- Build a map from source lattice‑element → target lattice‑element ----
  const elementMap = new Map(); // key `${latticeId}:${elem}` → { latticeId, el }
  for (const s of strands) {
    const srcLV = latticeViews.find(lv => lv.entry.id === s.fromLatticeId);
    const tgtLV = latticeViews.find(lv => lv.entry.id === s.toLatticeId);
    if (!srcLV || !tgtLV) continue;
    const srcNode = srcLV.nodes.find(n => n.id === s.fromNodeId);
    const tgtNode = tgtLV.nodes.find(n => n.id === s.toNodeId);
    if (!srcNode || !tgtNode) continue;
    srcNode.elements.forEach((el, i) => {
      const k = `${s.fromLatticeId}:${el}`;
      if (!elementMap.has(k))
        elementMap.set(k, { latticeId: s.toLatticeId, el: tgtNode.elements[i % tgtNode.elements.length] });
    });
  }
  if (!elementMap.size) return { isHomo: null, isInjective: null, isSurjective: null, kernel: [], image: [], strandLabels };

  // ---- Homomorphism check (only when all strands belong to a single source & single target) ----
  const srcIds = [...new Set(strands.map(s => s.fromLatticeId))];
  const tgtIds = [...new Set(strands.map(s => s.toLatticeId))];
  let isHomo = null;
  if (srcIds.length === 1 && tgtIds.length === 1) {
    const srcLattice = lattices.find(l => l.id === srcIds[0]);
    const tgtLattice = lattices.find(l => l.id === tgtIds[0]);
    if (srcLattice && tgtLattice) {
      const xSrc = srcLattice.x;
      const xTgt = tgtLattice.x;
      isHomo = true;
      const domainElems = [...elementMap.keys()].map(k => parseInt(k.split(":")[1]));
      outer: for (const a of domainElems) {
        for (const b of domainElems) {
          const ab = (a * b) % xSrc;
          const fa = elementMap.get(`${srcIds[0]}:${a}`)?.el;
          const fb = elementMap.get(`${srcIds[0]}:${b}`)?.el;
          const fab = elementMap.get(`${srcIds[0]}:${ab}`)?.el;
          if (fa == null || fb == null || fab == null || fab !== (fa * fb) % xTgt) {
            isHomo = false;
            break outer;
          }
        }
      }
    }
  }

  // ---- Kernel (domain elements sent to the identity 1 in the target) ----
  const kernel = [...elementMap.entries()]
    .filter(([, v]) => v.el === 1)
    .map(([k]) => parseInt(k.split(":")[1]))
    .sort((a, b) => a - b);

  // ---- Image (set of target elements reached) ----
  const image = [...new Set([...elementMap.values()].map(v => v.el))].sort((a, b) => a - b);

  // ---- Injectivity ----
  const seen = new Set();
  let isInjective = true;
  for (const v of elementMap.values()) {
    const key = `${v.latticeId}:${v.el}`;
    if (seen.has(key)) { isInjective = false; break; }
    seen.add(key);
  }

  // ---- Surjectivity ----
  const tgtElems = new Set();
  for (const s of strands) {
    const tgtLV = latticeViews.find(lv => lv.entry.id === s.toLatticeId);
    tgtLV?.nodes.find(n => n.id === s.toNodeId)?.elements.forEach(e => tgtElems.add(e));
  }
  const isSurjective = tgtElems.size > 0 && [...tgtElems].every(e => image.includes(e));

  return { isHomo, isInjective, isSurjective, kernel, image, strandLabels };
}

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

function Pane({ title, children, flex, open, onToggle, scrollClass = "" }) {
  return (
    <div style={{
      display: "flex", flexDirection: "column",
      flex: open ? (flex ?? 1) : "0 0 auto",
      minHeight: 0, overflow: "hidden", flexShrink: open ? 1 : 0,
    }}>
      <div
        onClick={onToggle}
        style={{
          padding: "9px 14px", background: C.paneHeader,
          borderBottom: `1px solid ${C.border}`,
          borderTop: `1px solid ${C.border}`,
          flexShrink: 0, cursor: "pointer", userSelect: "none",
          display: "flex", alignItems: "center", justifyContent: "space-between",
          transition: "background 0.13s",
        }}
        onMouseEnter={e => e.currentTarget.style.background = C.borderHover}
        onMouseLeave={e => e.currentTarget.style.background = C.paneHeader}
      >
        <span style={{ fontSize: 9, letterSpacing: 3, color: C.inkFaint, textTransform: "uppercase" }}>{title}</span>
        <span style={{
          fontSize: 8, color: C.inkFaint, flexShrink: 0,
          transition: "transform 0.18s", display: "inline-block",
          transform: open ? "rotate(180deg)" : "rotate(0deg)",
        }}>▼</span>
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

// Module-level ref for click‑vs‑drag detection
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
        if (isDrawMode) {
          onMouseDown(node.id, e);
          e.stopPropagation();
          return;
        }
        if (isSelected) {
          onMouseDown(node.id, e);
          e.stopPropagation();
        }
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
function makeLatticeEntry(base, canvasW, canvasH, labelOverride) {
  return {
    id: nextLatticeId++,
    x: base.param,          // kept for legacy display (U(n) uses this)
    label: labelOverride,   // display label e.g. "U(18)", "ℤ₁₂", "Q₈"
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
  const [lattices, setLattices] = useState([]);
  const [inputVal, setInputVal] = useState("18");
  const [error, setError] = useState("");
  // Catalog param state: { [catalogKey]: paramValue }
  const [catalogParams, setCatalogParams] = useState(
    Object.fromEntries(LATTICE_CATALOG.filter(c => c.hasParam).map(c => [c.key, c.paramDefault]))
  );
  // Placing mode: user clicks canvas to drop a pending lattice
  const [placingLattice, setPlacingLattice] = useState(null); // { base, label } | null

  // ── Selection — keyed by `${latticeId}:${nodeId}` ─────────────────
  const [selectedIds, setSelectedIds] = useState(new Set());

  // ── Morphisms ──────────────────────────────────────────────────────
  const [morphisms, setMorphisms] = useState([]);
  const [activeMorphismId, setActiveMorphismId] = useState(null);
  const [strandPreview, setStrandPreview] = useState(null); // { x1,y1,x2,y2 }
  const strandDragging = useRef(null); // { fromLatticeId, fromNodeId }
  const activeMorphismIdRef = useRef(null);
  useEffect(() => { activeMorphismIdRef.current = activeMorphismId; }, [activeMorphismId]);

  // ── Panel widths ───────────────────────────────────────────────────
  const [leftW, setLeftW] = useState(270);
  const [rightW, setRightW] = useState(310);
  const [leftCollapsed, setLeftCollapsed] = useState(false);
  const [rightCollapsed, setRightCollapsed] = useState(false);
  const leftWBeforeCollapse = useRef(270);
  const rightWBeforeCollapse = useRef(310);

  // ── Left pane open/flex state ─────────────────────────────────────
  const [leftPane1Open, setLeftPane1Open] = useState(true);
  const [leftPane2Open, setLeftPane2Open] = useState(true);
  const [leftPane3Open, setLeftPane3Open] = useState(true);
  const [leftPane1Flex, setLeftPane1Flex] = useState(1.2);
  const [leftPane2Flex, setLeftPane2Flex] = useState(1);
  const [leftPane3Flex, setLeftPane3Flex] = useState(0.8);

  // ── Right pane open/flex state ────────────────────────────────────
  const [rightPane1Open, setRightPane1Open] = useState(true);
  const [rightPane2Open, setRightPane2Open] = useState(true);
  const [rightPane1Flex, setRightPane1Flex] = useState(1);
  const [rightPane2Flex, setRightPane2Flex] = useState(1.4);

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
  // { latticeId, startMouseX, startMouseY, startPositions: {nodeId: {x,y}} }
  const epicenterDragging = useRef(null);
  const mouseDownPos = useRef(null);
  const didDrag = useRef(false);

  // ── Initial lattice on mount ──────────────────────────────────────
  useEffect(() => {
    const r = panelRef.current?.getBoundingClientRect();
    const cw = r?.width ?? 800, ch = r?.height ?? 600;
    const cat = LATTICE_CATALOG.find(c => c.key === "Un");
    const base = cat.build(18);
    const entry = makeLatticeEntry(base, cw, ch, "U(18)");
    setLattices([entry]);
  }, []);

  // ── Helpers to update a single lattice entry immutably ────────────
  const updateLattice = useCallback((id, patch) => {
    setLattices(prev => prev.map(l => l.id === id ? { ...l, ...patch } : l));
  }, []);

  // ── Place a lattice at a canvas world position ────────────────────
  const placeLatticeAt = useCallback((base, label, worldX, worldY) => {
    const r = panelRef.current?.getBoundingClientRect();
    const cw = r?.width ?? 800, ch = r?.height ?? 600;
    const entry = makeLatticeEntry(base, cw, ch, label);
    entry.epicenter = { x: worldX, y: worldY };
    setLattices(prev => [...prev, entry]);
  }, []);

  // ── Add U(n) lattice (legacy quick-add, places with offset) ───────
  const addLattice = useCallback((xVal) => {
    const n = parseInt(xVal);
    if (isNaN(n) || n < 2 || n > 200) { setError("Enter 2–200"); return; }
    setError("");
    const r = panelRef.current?.getBoundingClientRect();
    const cw = r?.width ?? 800, ch = r?.height ?? 600;
    const offset = lattices.length * 40;
    const cat = LATTICE_CATALOG.find(c => c.key === "Un");
    const base = cat.build(n);
    const entry = makeLatticeEntry(base, cw, ch, `U(${n})`);
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

  // ── Node mouse‑down (handles both normal dragging and strand start) ─────
  const onNodeMouseDown = useCallback((latticeId, nodeId, e) => {
    // ── Strand‑draw mode ─────────────────────
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
      const offsetX = rect?.left ?? 0;
      const offsetY = rect?.top ?? 0;
      const sx = node.x * cam.scale + cam.tx;
      const sy = node.y * cam.scale + cam.ty;
      strandDragging.current = { fromLatticeId: latticeId, fromNodeId: nodeId };
      setStrandPreview({ x1: sx, y1: sy, x2: e.clientX - offsetX, y2: e.clientY - offsetY });
      mouseDownPos.current = { x: e.clientX, y: e.clientY };
      return;
    }

    // ── Normal node dragging ─────────────────
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
        x: (entry.nodePositions[nid]?.x ?? entry.base.nodes[nid]?.x) ?? n.x - entry.epicenter.x + entry.base.W / 2,
        y: (entry.nodePositions[nid]?.y ?? entry.base.nodes[nid]?.y) ?? n.y - entry.epicenter.y + entry.base.H / 2,
      };
    }
    nodeDragging.current = { latticeId, startMouseX: e.clientX, startMouseY: e.clientY, startPositions };
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
  }, [lattices, selectedIds, activeMorphismId]);

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
  const placingLatticeRef = useRef(null);
  useEffect(() => { placingLatticeRef.current = placingLattice; }, [placingLattice]);

  const onCanvasMouseDown = useCallback((e) => {
    if (e.target.closest && (e.target.closest("g[data-node]") || e.target.closest("g[data-epicenter]"))) return;
    // ── Placement mode: drop lattice at click point ───────────────
    if (placingLatticeRef.current) {
      e.preventDefault();
      const rect = panelRef.current?.getBoundingClientRect();
      const cam = cameraRef.current;
      const canvasX = e.clientX - (rect?.left ?? 0);
      const canvasY = e.clientY - (rect?.top ?? 0);
      const worldX = (canvasX - cam.tx) / cam.scale;
      const worldY = (canvasY - cam.ty) / cam.scale;
      const { base, label } = placingLatticeRef.current;
      placeLatticeAt(base, label, worldX, worldY);
      setPlacingLattice(null);
      return;
    }
    e.preventDefault();
    didDrag.current = false; didDragRef.current = false;
    isPanning.current = true;
    mouseDownPos.current = { x: e.clientX, y: e.clientY };
    panStart.current = { mouseX: e.clientX, mouseY: e.clientY, tx: cameraRef.current.tx, ty: cameraRef.current.ty };
    document.body.style.cursor = "grabbing";
    document.body.style.userSelect = "none";
  }, [placeLatticeAt]);

  // ── Global mouse move / up (panning, node drag, epicenter drag, strand draw) ─────
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
        // update preview line (canvas-space, not window-space)
        const rect = panelRef.current?.getBoundingClientRect();
        const offsetX = rect?.left ?? 0;
        const offsetY = rect?.top ?? 0;
        setStrandPreview(prev => prev ? { ...prev, x2: e.clientX - offsetX, y2: e.clientY - offsetY } : null);
      }
      if (nodeDragging.current) {
        const { latticeId, startMouseX, startMouseY, startPositions } = nodeDragging.current;
        const dx = (e.clientX - startMouseX) / cameraRef.current.scale;
        const dy = (e.clientY - startMouseY) / cameraRef.current.scale;
        setLattices(prev => prev.map(l => {
          if (l.id !== latticeId) return l;
          const next = { ...l.nodePositions };
          Object.entries(startPositions).forEach(([nid, { x, y }]) => {
            next[nid] = { x: x + dx, y: y + dy };
          });
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
        setLeftW(w => {
          const next = w + delta;
          if (next < 60) { leftWBeforeCollapse.current = Math.max(w, 200); setLeftCollapsed(true); return 0; }
          setLeftCollapsed(false);
          return Math.min(500, next);
        });
      }
      if (rightSplitDragging.current) {
        const delta = e.clientX - rightSplitStart.current; rightSplitStart.current = e.clientX;
        setRightW(w => {
          const next = w - delta;
          if (next < 60) { rightWBeforeCollapse.current = Math.max(w, 220); setRightCollapsed(true); return 0; }
          setRightCollapsed(false);
          return Math.min(520, next);
        });
      }
    };

    const onUp = (e) => {
      // ---- commit a strand if we were drawing one ----
      if (strandDragging.current && activeMorphismIdRef.current !== null) {
        const { fromLatticeId, fromNodeId } = strandDragging.current;
        // Walk up to find a node element under mouse
        let el = e.target;
        while (el && el !== document.body) {
          if (el.getAttribute && el.getAttribute("data-node") === "true") break;
          el = el.parentElement;
        }
        if (el && el.getAttribute("data-node") === "true") {
          const toLatticeId = parseInt(el.getAttribute("data-lattice-id"));
          const toNodeId = parseInt(el.getAttribute("data-node-id"));
          if (!isNaN(toLatticeId) && !isNaN(toNodeId) &&
              !(toLatticeId === fromLatticeId && toNodeId === fromNodeId)) {
            const sid = Date.now() + Math.random();
            setMorphisms(prev => prev.map(m =>
              m.id !== activeMorphismIdRef.current ? m : {
                ...m,
                strands: [...m.strands, { id: sid, fromLatticeId, fromNodeId, toLatticeId, toNodeId }]
              }
            ));
          }
        }
        strandDragging.current = null;
        setStrandPreview(null);
      }

      if (isPanning.current && !didDrag.current) setSelectedIds(new Set());
      if (isPanning.current) {
        isPanning.current = false;
        document.body.style.cursor = "";
        document.body.style.userSelect = "";
      }
      nodeDragging.current = null;
      epicenterDragging.current = null;
      mouseDownPos.current = null;
      if (leftSplitDragging.current) {
        leftSplitDragging.current = false;
        document.body.style.cursor = "";
        document.body.style.userSelect = "";
      }
      if (rightSplitDragging.current) {
        rightSplitDragging.current = false;
        document.body.style.cursor = "";
        document.body.style.userSelect = "";
      }
    };

    window.addEventListener("mousemove", onMove);
    window.addEventListener("mouseup", onUp);
    return () => {
      window.removeEventListener("mousemove", onMove);
      window.removeEventListener("mouseup", onUp);
    };
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

  // ── Panel collapse ────────────────────────────────────────────────
  const toggleLeft = () => {
    if (leftCollapsed) { setLeftW(leftWBeforeCollapse.current); setLeftCollapsed(false); }
    else { leftWBeforeCollapse.current = leftW; setLeftW(0); setLeftCollapsed(true); }
  };
  const toggleRight = () => {
    if (rightCollapsed) { setRightW(rightWBeforeCollapse.current); setRightCollapsed(false); }
    else { rightWBeforeCollapse.current = rightW; setRightW(0); setRightCollapsed(true); }
  };

  // ── Left splitter flex adjusters (drag between panes)
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

  // ── Toggle node selection ─────────────────────────────────────────
  const toggleNodeSelect = useCallback((latticeId, nodeId) => {
    const key = `${latticeId}:${nodeId}`;
    setSelectedIds(prev => { const next = new Set(prev); next.has(key) ? next.delete(key) : next.add(key); return next; });
  }, []);

  // ── Derived per‑lattice data ──────────────────────────────────────
  const latticeViews = lattices.map((entry, idx) => {
    const nodes = resolveNodes(entry);
    const colorMap = buildOrderColorMap(nodes);
    const fullNode = nodes[nodes.length - 1] ?? null;
    const accent = LATTICE_ACCENTS[idx % LATTICE_ACCENTS.length];

    // Edge + adjacent highlight
    const hlEdgeSet = new Set();
    const adjacentNodes = new Set();
    entry.base.edges.forEach(([a, b], i) => {
      const ka = `${entry.id}:${a}`, kb = `${entry.id}:${b}`;
      if (selectedIds.has(ka) || selectedIds.has(kb)) {
        hlEdgeSet.add(i);
        adjacentNodes.add(a);
        adjacentNodes.add(b);
      }
    });

    const coprimes = findCoprimes(entry.x);
    const zParts = zStructureParts(entry.x);
    const expVal = groupExponent(coprimes, entry.x);
    return { entry, nodes, colorMap, fullNode, accent, hlEdgeSet, adjacentNodes, coprimes, zParts, expVal };
  });

  // Fast lookup of any node by its “latticeId:nodeId” key (for strands)
  const nodeLookup = {};
  latticeViews.forEach(v => {
    v.nodes.forEach(n => {
      nodeLookup[`${v.entry.id}:${n.id}`] = n;
    });
  });

  // All selected nodes across all lattices (for right‑hand pane)
  const allSelectedNodes = latticeViews.flatMap(({ entry, nodes, colorMap, fullNode }) =>
    [...selectedIds]
      .filter(k => k.startsWith(`${entry.id}:`))
      .map(k => {
        const nodeId = parseInt(k.split(":")[1]);
        const node = nodes.find(n => n.id === nodeId);
        if (!node) return null;
        const indexVal = (fullNode && fullNode.order % node.order === 0) ? fullNode.order / node.order : "—";
        return { node, colorMap, latticeId: entry.id, latticeLabel: entry.label ?? `U(${entry.x})`, indexVal };
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
            {/* Catalog list */}
            <div style={{ margin: "-12px -14px" }}>
              {LATTICE_CATALOG.map(cat => {
                const param = catalogParams[cat.key] ?? cat.paramDefault;
                const isPlacing = placingLattice?.key === cat.key;
                return (
                  <div key={cat.key} style={{
                    borderBottom: `1px solid ${C.border}`,
                    padding: "8px 12px",
                    background: isPlacing ? C.selectedBg : "transparent",
                  }}>
                    {/* Row: label + param input + place button */}
                    <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
                      <span style={{
                        flex: 1, fontSize: 13, color: C.ink,
                        fontFamily: "'Courier New', monospace", fontWeight: "600",
                      }}>{cat.label}</span>
                      {cat.hasParam && (
                        <div style={{ display: "flex", alignItems: "center", gap: 3 }}>
                          <span style={{ fontSize: 9, color: C.inkFaint, letterSpacing: 1 }}>{cat.paramLabel}</span>
                          <input
                            type="number"
                            value={param}
                            min={cat.paramMin} max={cat.paramMax}
                            onChange={e => setCatalogParams(prev => ({ ...prev, [cat.key]: parseInt(e.target.value) || cat.paramDefault }))}
                            style={{
                              width: 44, background: C.bg, border: `1px solid ${C.borderHover}`,
                              borderRadius: 3, color: C.ink, fontSize: 11, padding: "2px 4px",
                              textAlign: "center", fontFamily: "'Courier New', monospace", outline: "none",
                            }}
                          />
                        </div>
                      )}
                      {/* ☉ place button */}
                      <button
                        title="Place on canvas"
                        onClick={() => {
                          try {
                            const p = cat.hasParam ? (param || cat.paramDefault) : cat.paramDefault;
                            const base = cat.build(p);
                            const lbl = cat.hasParam ? `${cat.label.replace("n", p)}` : cat.label;
                            setPlacingLattice({ key: cat.key, base, label: lbl });
                          } catch (err) { setError(String(err)); }
                        }}
                        style={{
                          width: 28, height: 28, borderRadius: "50%", flexShrink: 0,
                          background: isPlacing ? C.ink : C.panelSurface,
                          border: `1.5px solid ${isPlacing ? C.ink : C.border}`,
                          cursor: "pointer", display: "flex", alignItems: "center", justifyContent: "center",
                          color: isPlacing ? C.panelBg : C.inkMid, fontSize: 13, lineHeight: 1,
                          transition: "background 0.13s, border-color 0.13s",
                        }}
                        onMouseEnter={e => { if (!isPlacing) { e.currentTarget.style.background = C.borderHover; e.currentTarget.style.borderColor = C.borderHover; } }}
                        onMouseLeave={e => { if (!isPlacing) { e.currentTarget.style.background = C.panelSurface; e.currentTarget.style.borderColor = C.border; } }}
                      >☉</button>
                    </div>
                    <div style={{ fontSize: 8, color: C.inkFaint, letterSpacing: 1, marginTop: 3 }}>{cat.desc}</div>
                  </div>
                );
              })}
            </div>

            {error && <div style={{ color: "#f87171", fontSize: 10, margin: "8px 0" }}>{error}</div>}

            {/* Active lattices list */}
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
                    <button onClick={() => removeLattice(l.id)} style={{
                      background: "none", border: "none", cursor: "pointer", color: C.inkFaint,
                      fontSize: 12, padding: "0 2px", lineHeight: 1,
                    }} title="Remove">×</button>
                  </div>
                );
              })}
            </>}

            <div style={{ fontSize: 10, color: C.inkFaint, marginTop: 8, lineHeight: 1.6 }}>
              Click ☉ to place · drag selected to move
            </div>
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

                        {/* activation toggle */}
                        <SectionBody>
                          <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
                            <label style={{ display: "flex", alignItems: "center", gap: 6, cursor: "pointer", flex: 1 }}>
                              <div onClick={() => setActiveMorphismId(isActive ? null : m.id)}
                                style={{
                                  width: 14, height: 14, borderRadius: "50%", flexShrink: 0,
                                  border: `2px solid ${m.color}`,
                                  background: isActive ? m.color : "transparent",
                                  cursor: "pointer", transition: "background 0.15s",
                                }} />
                              <span style={{ fontSize: 10, color: isActive ? C.ink : C.inkFaint, letterSpacing: 1 }}>
                                {isActive ? "Drawing strands ↗" : "Activate to draw"}
                              </span>
                            </label>
                            <button onClick={() => {
                              setMorphisms(prev => prev.filter(x => x.id !== m.id));
                              if (activeMorphismId === m.id) setActiveMorphismId(null);
                            }} style={{ background: "none", border: "none", cursor: "pointer", color: C.inkFaint, fontSize: 13, padding: "0 2px", lineHeight: 1 }} title="Delete morphism">×</button>
                          </div>
                          {isActive && (
                            <div style={{ marginTop: 6, fontSize: 9, color: m.color, letterSpacing: 1.5, textTransform: "uppercase" }}>
                              ↗ drag from any node to another
                            </div>
                          )}
                        </SectionBody>

                        {/* strand list */}
                        {m.strands.length > 0 && (
                          <Section label="Strands" depth={1} defaultOpen={true} badge={m.strands.length}>
                            {analysis.strandLabels.map((sl, i) => (
                              <div key={m.strands[i].id} style={{ padding: "5px 12px", borderBottom: `1px solid ${C.border}`, display: "flex", alignItems: "center", gap: 6 }}>
                                <div style={{ width: 7, height: 7, borderRadius: "50%", background: m.color, flexShrink: 0 }} />
                                <div style={{ flex: 1, minWidth: 0 }}>
                                  <div style={{ fontSize: 10, color: C.ink, fontFamily: "'Courier New', monospace", whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>
                                    {sl.from}
                                  </div>
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

                        {/* analysis panel */}
                        {m.strands.length > 0 && (
                          <Section label="Analysis" depth={1} defaultOpen={false}>
                            <SectionRow label="Homo?" value={
                              analysis.isHomo === null ? "n/a" : analysis.isHomo ? "yes ✓" : "no ✗"
                            } accent={analysis.isHomo === true ? "#4ade80" : analysis.isHomo === false ? "#f87171" : undefined} />
                            <SectionRow label="Injective" value={
                              analysis.isInjective === null ? "n/a" : analysis.isInjective ? "yes ✓" : "no ✗"
                            } accent={analysis.isInjective === true ? "#4ade80" : analysis.isInjective === false ? "#f87171" : undefined} />
                            <SectionRow label="Surjective" value={
                              analysis.isSurjective === null ? "n/a" : analysis.isSurjective ? "yes ✓" : "no ✗"
                            } accent={analysis.isSurjective === true ? "#4ade80" : analysis.isSurjective === false ? "#f87171" : undefined} />
                            {analysis.kernel.length > 0 && (
                              <Section label="Kernel" depth={2} defaultOpen={false} badge={analysis.kernel.length}>
                                <SectionBody>
                                  <div style={{ display: "flex", flexWrap: "wrap", gap: 3 }}>
                                    {analysis.kernel.map(el => (
                                      <span key={el} style={{ fontSize: 10, color: C.inkMid, fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "1px 5px", border: `1px solid ${C.border}` }}>{el}</span>
                                    ))}
                                  </div>
                                </SectionBody>
                              </Section>
                            )}
                            {analysis.image.length > 0 && (
                              <Section label="Image" depth={2} defaultOpen={false} badge={analysis.image.length}>
                                <SectionBody>
                                  <div style={{ display: "flex", flexWrap: "wrap", gap: 3 }}>
                                    {analysis.image.map(el => (
                                      <span key={el} style={{ fontSize: 10, color: m.color, fontFamily: "'Courier New', monospace", background: C.panelBg, borderRadius: 3, padding: "1px 5px", border: `1px solid ${C.border}` }}>{el}</span>
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

              {/* Per‑lattice subgroup lists */}
              {latticeViews.map(({ entry, nodes, colorMap, accent }) => (
                <Section key={entry.id} label={`${entry.label ?? "U("+entry.x+")"} — Subgroups`} depth={0} accent={accent} defaultOpen={false} badge={nodes.length}>
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
        cursor: placingLattice ? "crosshair" : "grab",
      }} onMouseDown={onCanvasMouseDown}>

        {/* Placement mode overlay */}
        {placingLattice && (
          <div style={{
            position: "absolute", inset: 0, zIndex: 20, pointerEvents: "none",
            display: "flex", alignItems: "flex-start", justifyContent: "center",
            paddingTop: 18,
          }}>
            <div style={{
              background: C.ink, color: C.panelBg, borderRadius: 6,
              padding: "7px 16px", fontSize: 10, letterSpacing: 2.5,
              textTransform: "uppercase", fontFamily: "'Courier New', monospace",
              boxShadow: "0 2px 12px rgba(0,0,0,0.18)",
            }}>
              ☉ click to place {placingLattice.label}
            </div>
          </div>
        )}
        {placingLattice && (
          <div onClick={() => setPlacingLattice(null)} style={{
            position: "absolute", top: 16, right: 16, zIndex: 21,
            background: C.border, border: "none", borderRadius: 4, cursor: "pointer",
            padding: "4px 10px", fontSize: 9, color: C.ink, letterSpacing: 2,
            textTransform: "uppercase", fontFamily: "'Courier New', monospace",
          }}>cancel</div>
        )}

        {lattices.length === 0 && !placingLattice && (
          <div style={{ position: "absolute", inset: 0, display: "flex", alignItems: "center", justifyContent: "center", pointerEvents: "none" }}>
            <span style={{ fontSize: 11, letterSpacing: 4, color: C.inkFaint, textTransform: "uppercase" }}>Add a lattice to begin</span>
          </div>
        )}

        {/* Main SVG – lattice nodes + regular edges */}
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
            {/* marker for each morphism – used by the straight‑line version (kept for compatibility) */}
            {morphisms.map(m => (
              <marker key={m.id} id={`arr-${m.id}`} markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                <path d="M0,0 L0,6 L6,3 Z" fill={m.color} />
              </marker>
            ))}
          </defs>

          <g transform={`translate(${camera.tx}, ${camera.ty}) scale(${camera.scale})`}>
            {latticeViews.map(({ entry, nodes, colorMap, accent, hlEdgeSet, adjacentNodes }) => (
              <g key={entry.id}>
                {/* regular edges */}
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

                {/* occluders */}
                {nodes.map(node => <ShapeOccluder key={`occ-${node.id}`} node={node} R={26} />)}

                {/* nodes */}
                {nodes.map(node => {
                  const key = `${entry.id}:${node.id}`;
                  return (
                    <ShapeNode key={node.id}
                      node={node}
                      latticeId={entry.id}
                      colorMap={colorMap}
                      isSelected={selectedIds.has(key)}
                      isAdjacent={adjacentNodes.has(node.id) && !selectedIds.has(key)}
                      isDrawMode={activeMorphismId !== null}
                      onToggleSelect={nodeId => toggleNodeSelect(entry.id, nodeId)}
                      onMouseDown={(nodeId, e) => onNodeMouseDown(entry.id, nodeId, e)} />
                  );
                })}

                {/* epicenter */}
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

        {/* ── STRAND OVERLAY (curved paths, screen‑space) ── */}
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

          {/* committed strands */}
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
                  {isActive && (
                    <path d={pathD} stroke={m.color} strokeWidth={7} fill="none" opacity={0.18} strokeLinecap="round" />
                  )}
                  <path
                    d={pathD}
                    stroke={m.color}
                    strokeWidth={isActive ? 2.6 : 1.6}
                    fill="none"
                    opacity={isActive ? 1 : 0.38}
                    strokeDasharray={isActive ? undefined : "6 4"}
                    markerEnd={`url(#sarr-${m.id})`}
                  />
                </g>
              );
            });
          })}

          {/* live preview while dragging */}
          {strandPreview && (() => {
            const { x1, y1, x2, y2 } = strandPreview;
            const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
            const dx = x2 - x1, dy = y2 - y1;
            const len = Math.sqrt(dx * dx + dy * dy) || 1;
            const arc = Math.min(70, len * 0.32);
            const cpx = mx - (dy / len) * arc, cpy = my + (dx / len) * arc;
            return (
              <path d={`M ${x1} ${y1} Q ${cpx} ${cpy} ${x2} ${y2}`}
                stroke={C.inkFaint} strokeWidth={1.6} fill="none"
                strokeDasharray="7 4" opacity={0.65}
                markerEnd="url(#sarr-preview)" />
            );
          })()}
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
          {/* Pane 1: Group Info */}
          <Pane title="Group Info" open={rightPane1Open} onToggle={() => setRightPane1Open(o => !o)} flex={rightPane1Flex}>
            {latticeViews.length === 0
              ? <div style={{ color: C.inkFaint, fontSize: 11 }}>No lattices added.</div>
              : <div style={{ margin: "-12px -14px" }}>
                  {latticeViews.map(({ entry, nodes, fullNode, colorMap, accent, coprimes, zParts, expVal }) => (
                    <Section key={entry.id} label={entry.label ?? `U(${entry.x})`} depth={0} accent={accent} defaultOpen={latticeViews.length === 1}>
                      {/* Stats */}
                      <Section label="Stats" depth={1} defaultOpen={false}>
                        <SectionBody>
                          <div style={{ marginBottom: 8, padding: "5px 8px", background: C.statsRow, borderRadius: 4, border: `1px solid ${C.border}` }}>
                            <div style={{ fontSize: 8, letterSpacing: 2, color: C.inkFaint, textTransform: "uppercase", marginBottom: 2 }}>
                              {entry.kind === "Un" ? "Isomorphism Type" : "Structure"}
                            </div>
                            <div style={{ fontSize: 13, fontWeight: "700", color: C.ink, fontFamily: "'Courier New', monospace", wordBreak: "break-all" }}>
                              {entry.kind === "Un" ? `U(${entry.x}) ≅ ${formatZ(zParts)}` : entry.label}
                            </div>
                          </div>
                        </SectionBody>
                        {fullNode && [
                          [`|${entry.label}|`, fullNode.order],
                          ["Nodes", nodes.length],
                          ["Levels",    (entry.base.maxLevel ?? 0) + 1],
                          ["Edges", entry.base.edges.length],
                          ...(entry.kind === "Un" ? [
                            ["Rank",     fullNode.generators.length > 0 ? fullNode.generators[0].length : 1],
                            ["Exponent", expVal],
                            ["Abelian",  "yes"],
                          ] : []),
                        ].map(([k, v]) => <SectionRow key={k} label={k} value={String(v)} accent={k === "Abelian" ? "#4ade80" : undefined} />)}
                      </Section>

                      {/* Display toggles */}
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

          {rightPane1Open && rightPane2Open && <HPSplitter onDrag={onRightSplit12} />}

          {/* Pane 2: Selected nodes */}
          <Pane title={`Selected${allSelectedNodes.length > 1 ? ` (${allSelectedNodes.length})` : ""}`} open={rightPane2Open} onToggle={() => setRightPane2Open(o => !o)} flex={rightPane2Flex}>
            {allSelectedNodes.length > 0
              ? <div style={{ margin: "-12px -14px" }}>
                  {allSelectedNodes.map(({ node, colorMap, latticeId, latticeLabel, indexVal }) => {
                    const col = orderColor(node.order, colorMap);
                    const cyclicLabel = node.order === 1 ? "Trivial" : node.isCyclic ? "Cyclic" : node.shape === "square" ? "Non‑cyclic · pair gens" : "Non‑cyclic · triple gens";
                    return (
                      <Section key={`${latticeId}:${node.id}`} label={node.shortLabel} badge={`ord ${node.order}`} accent={col} depth={0} defaultOpen={false}>
                        <Section label="Label & Style" depth={1} defaultOpen={false}>
                          <SectionRow label="Group" value={latticeLabel} />
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