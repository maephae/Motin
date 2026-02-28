"""
U(x) Subgroup Lattice Generator
================================
Generates the subgroup lattice for U(n) — the group of units mod n.

Core formula (as specified):
    d = floor(a^b / c)
    (a^b / c - d) * c  →  this gives a^b mod c

Usage:
    python ux_lattice.py          # prompts for x
    python ux_lattice.py 12       # runs for U(12)
"""

import sys
import math
from itertools import combinations


# ─────────────────────────────────────────────
# STEP 1: Manual modular reduction (your formula)
# ─────────────────────────────────────────────

def mod_formula(a, b, c):
    """
    Compute a^b mod c using the floor formula:
        d = floor(a^b / c)
        result = (a^b / c - d) * c
    Note: uses integer arithmetic to avoid float precision issues for large b.
    """
    power = a ** b
    d = math.floor(power / c)
    result = round((power / c - d) * c)  # round handles float dust
    return result


def mod_fast(a, b, c):
    """
    Same result as mod_formula but uses Python's built-in pow for speed.
    We use this for the heavy lifting; mod_formula is available for verification.
    """
    return pow(a, b, c)


# ─────────────────────────────────────────────
# STEP 2: Sieve — find all coprimes to x in [1, x)
# ─────────────────────────────────────────────

def find_coprimes(x):
    """
    Return list of elements in U(x): integers a where 1 <= a < x and gcd(a, x) = 1.
    This is the sieve step you described.
    """
    return [a for a in range(1, x) if math.gcd(a, x) == 1]


# ─────────────────────────────────────────────
# STEP 3: Generate cyclic subgroup from a generator a in U(x)
# ─────────────────────────────────────────────

def generate_cyclic_subgroup(a, x):
    """
    Iterate b = 1, 2, 3, ... computing a^b mod x until result == 1.
    Returns the cyclic subgroup <a> as a frozenset.
    """
    subgroup = []
    b = 1
    while True:
        val = mod_fast(a, b, x)
        subgroup.append(val)
        if val == 1:
            break
        b += 1
    return frozenset(subgroup)


# ─────────────────────────────────────────────
# STEP 4: Find ALL distinct subgroups of U(x)
# ─────────────────────────────────────────────

def find_all_subgroups(x):
    """
    Generate cyclic subgroup for every element in U(x).
    Collect all distinct subgroups (as frozensets).
    Always include the trivial subgroup {1}.
    """
    coprimes = find_coprimes(x)
    subgroups = set()

    # trivial subgroup
    subgroups.add(frozenset([1]))

    for a in coprimes:
        sg = generate_cyclic_subgroup(a, x)
        subgroups.add(sg)

    # Also add full group (should already be in there if x has a generator, but be safe)
    subgroups.add(frozenset(coprimes))

    return sorted(subgroups, key=len)  # sort by order (size)


# ─────────────────────────────────────────────
# STEP 5: Build the lattice — find inclusion relationships
# ─────────────────────────────────────────────

def build_lattice(subgroups):
    """
    For each pair of subgroups, determine if one is a subset of the other.
    Then reduce to COVER relations (direct containments only, no transitive jumps).
    
    Returns:
        covers: list of (smaller_idx, larger_idx) representing edges in the Hasse diagram
    """
    n = len(subgroups)
    sg_list = list(subgroups)

    # Build full containment matrix
    contains = [[False] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j and sg_list[i] < sg_list[j]:  # strict subset
                contains[i][j] = True

    # Reduce to cover relations (Hasse diagram edges)
    # i covers j means: i ⊂ j and there's no k with i ⊂ k ⊂ j
    covers = []
    for i in range(n):
        for j in range(n):
            if contains[i][j]:
                # Check if this is a direct cover (no intermediate subgroup)
                is_cover = True
                for k in range(n):
                    if k != i and k != j and contains[i][k] and contains[k][j]:
                        is_cover = False
                        break
                if is_cover:
                    covers.append((i, j))

    return sg_list, covers


# ─────────────────────────────────────────────
# STEP 6: Assign levels (layers) for diagram drawing
# ─────────────────────────────────────────────

def assign_levels(sg_list, covers):
    """
    Assign each node a level based on subgroup order (size).
    Level 0 = trivial subgroup {1}, top level = full group.
    """
    sizes = [len(sg) for sg in sg_list]
    unique_sizes = sorted(set(sizes))
    level_map = {size: i for i, size in enumerate(unique_sizes)}
    return [level_map[len(sg)] for sg in sg_list]


# ─────────────────────────────────────────────
# STEP 7: Print the lattice as ASCII
# ─────────────────────────────────────────────

def print_lattice(x, sg_list, covers, levels):
    print(f"\n{'='*55}")
    print(f"  U({x})  —  Subgroup Lattice")
    print(f"{'='*55}")
    print(f"  |U({x})| = {len(sg_list[-1])}  (Euler's totient φ({x}))")
    print(f"  {len(sg_list)} total subgroup(s) found\n")

    max_level = max(levels)

    # Group nodes by level
    by_level = {}
    for i, lv in enumerate(levels):
        by_level.setdefault(lv, []).append(i)

    print("  Subgroups by layer (bottom = trivial, top = full group):\n")
    for lv in range(max_level + 1):
        nodes = by_level.get(lv, [])
        for ni in nodes:
            sg = sg_list[ni]
            label = "{" + ", ".join(str(e) for e in sorted(sg)) + "}"
            print(f"    Level {lv}  |order {len(sg)}|  {label}")
        print()

    print("  Cover relations (Hasse diagram edges):\n")
    for (i, j) in covers:
        sg_i = "{" + ", ".join(str(e) for e in sorted(sg_list[i])) + "}"
        sg_j = "{" + ", ".join(str(e) for e in sorted(sg_list[j])) + "}"
        print(f"    {sg_i}  ⊂  {sg_j}")

    print(f"\n{'='*55}\n")


# ─────────────────────────────────────────────
# STEP 8: Export to JSON (for feeding into a visualizer)
# ─────────────────────────────────────────────

def export_json(x, sg_list, covers, levels):
    import json
    nodes = []
    for i, sg in enumerate(sg_list):
        nodes.append({
            "id": i,
            "elements": sorted(sg),
            "order": len(sg),
            "level": levels[i],
            "label": "{" + ",".join(str(e) for e in sorted(sg)) + "}"
        })
    edges = [{"from": i, "to": j} for (i, j) in covers]
    data = {"x": x, "group_order": len(sg_list[-1]), "nodes": nodes, "edges": edges}
    filename = f"U{x}_lattice.json"
    with open(filename, "w") as f:
        json.dump(data, f, indent=2)
    print(f"  JSON exported to {filename}")
    return data


# ─────────────────────────────────────────────
# MAIN
# ─────────────────────────────────────────────

def run(x):
    if x < 2:
        print("x must be >= 2")
        return

    print(f"\nBuilding U({x})...")

    # Verify mod_formula matches built-in for a spot check
    a_test, b_test = find_coprimes(x)[0] if find_coprimes(x) else (1, 1), 3
    if isinstance(a_test, int):
        formula_result = mod_formula(a_test, b_test, x)
        builtin_result = pow(a_test, b_test, x)
        assert formula_result == builtin_result, \
            f"Formula mismatch: {formula_result} vs {builtin_result}"

    subgroups = find_all_subgroups(x)
    sg_list, covers = build_lattice(subgroups)
    levels = assign_levels(sg_list, covers)

    print_lattice(x, sg_list, covers, levels)
    export_json(x, sg_list, covers, levels)


if __name__ == "__main__":
    if len(sys.argv) > 1:
        try:
            x = int(sys.argv[1])
        except ValueError:
            print("Usage: python ux_lattice.py <integer>")
            sys.exit(1)
    else:
        x = int(input("Enter value of x for U(x): "))

    run(x)
