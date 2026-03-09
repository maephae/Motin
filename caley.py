import itertools
import networkx as nx

# ==========================================
# 1. DYNAMIC CAYLEY TABLE GENERATORS
# ==========================================

def generate_cyclic_table(n):
    """Generates C_n. Order: n."""
    return [[(i + j) % n for j in range(n)] for i in range(n)], [f"r^{i}" for i in range(n)]

def generate_dihedral_table(n):
    """Generates D_n (Symmetries of n-gon). Order: 2n."""
    order = 2 * n
    table = [[0] * order for _ in range(order)]
    labels = [f"r^{i}s^{j}" for j in range(2) for i in range(n)]
    for idx1 in range(order):
        for idx2 in range(order):
            i1, j1 = idx1 % n, idx1 // n
            i2, j2 = idx2 % n, idx2 // n
            new_i = (i1 + i2) % n if j1 == 0 else (i1 - i2) % n
            new_j = (j1 + j2) % 2
            table[idx1][idx2] = new_i + (new_j * n)
    return table, labels

def generate_symmetric_table(n):
    """Generates S_n (Permutations). Order: n!."""
    perms = list(itertools.permutations(range(n)))
    p_to_idx = {p: i for i, p in enumerate(perms)}
    order = len(perms)
    table = [[0] * order for _ in range(order)]
    for i in range(order):
        for j in range(order):
            composed = tuple(perms[i][perms[j][k]] for k in range(n))
            table[i][j] = p_to_idx[composed]
    return table, perms

def generate_direct_product(table1, table2):
    """Combines two groups G and H into G x H. Order: |G|*|H|."""
    n1, n2 = len(table1), len(table2)
    order = n1 * n2
    table = [[0] * order for _ in range(order)]
    for i in range(order):
        for j in range(order):
            # Decode: element = (g, h)
            g1, h1 = i // n2, i % n2
            g2, h2 = j // n2, j % n2
            # Multiply components separately
            res_g = table1[g1][g2]
            res_h = table2[h1][h2]
            # Encode back
            table[i][j] = res_g * n2 + res_h
    return table

# ==========================================
# 2. SUBGROUP & LATTICE LOGIC
# ==========================================

def get_closure(elements, table):
    """Finds the smallest subgroup containing 'elements' (The 'Mote')."""
    closure = set(elements) | {0}
    added = True
    while added:
        added = False
        current = list(closure)
        for i in current:
            for j in current:
                res = table[i][j]
                if res not in closure:
                    closure.add(res)
                    added = True
    return frozenset(closure)

def find_all_subgroups(table):
    """Systematically discovers the entire subgroup lattice."""
    subgroups = {get_closure([i], table) for i in range(len(table))}
    added = True
    while added:
        added = False
        current = list(subgroups)
        for s1 in current:
            for s2 in current:
                new_sg = get_closure(set(s1) | set(s2), table)
                if new_sg not in subgroups:
                    subgroups.add(new_sg)
                    added = True
    return sorted(list(subgroups), key=len)

def build_hasse_mote(subgroups):
    """Constructs the Hasse diagram (removes redundant edges)."""
    raw_graph = nx.DiGraph()
    for i, sg in enumerate(subgroups):
        raw_graph.add_node(i, size=len(sg))
        for j, other in enumerate(subgroups):
            if i != j and sg.issubset(other):
                raw_graph.add_edge(i, j)
    # Transitive reduction makes it a Hasse Diagram
    return nx.transitive_reduction(raw_graph)

# ==========================================
# 4. ADVANCED & EXOTIC GENERATORS
# ==========================================

def generate_quaternion_table():
    """
    Generates the Quaternion Group Q8. Order: 8.
    Elements: 1, -1, i, -i, j, -j, k, -k
    Mapping: 0:1, 1:-1, 2:i, 3:-i, 4:j, 5:-j, 6:k, 7:-k
    """
    # Multiplication rules for i, j, k
    # 0=1, 1=-1, 2=i, 3=-i, 4=j, 5=-j, 6=k, 7=-k
    table = [
        [0,1,2,3,4,5,6,7], # 1
        [1,0,3,2,5,4,7,6], # -1
        [2,3,1,0,6,7,5,4], # i
        [3,2,0,1,7,6,4,5], # -i
        [4,5,7,6,1,0,2,3], # j
        [5,4,6,7,0,1,3,2], # -j
        [6,7,4,5,3,2,1,0], # k
        [7,6,5,4,2,3,0,1]  # -k
    ]
    labels = ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]
    return table, labels

def generate_units_mod_n(n):
    """
    Generates the group of units (Z/nZ)*. 
    Elements are integers coprime to n. Operation is multiplication mod n.
    Very useful for number theory morphisms.
    """
    import math
    elements = [i for i in range(1, n) if math.gcd(i, n) == 1]
    order = len(elements)
    e_to_idx = {e: i for i, e in enumerate(elements)}
    
    table = [[0] * order for _ in range(order)]
    for i in range(order):
        for j in range(order):
            res = (elements[i] * elements[j]) % n
            table[i][j] = e_to_idx[res]
            
    return table, [str(e) for e in elements]

def generate_boolean_algebra_group(n):
    """
    Generates the group (P(S), Δ) where Δ is symmetric difference.
    This is isomorphic to (Z2)^n. 
    Great for CS-focused morphisms and bit-manipulation logic.
    """
    order = 2**n
    table = [[0] * order for _ in range(order)]
    # Symmetric difference is equivalent to XOR on bitstrings
    for i in range(order):
        for j in range(order):
            table[i][j] = i ^ j
    
    labels = [bin(i)[2:].zfill(n) for i in range(order)]
    return table, labels

# ==========================================
# 3. EXAMPLE EXECUTION
# ==========================================
def print_cayley_table(table, labels, title="Cayley Table", limit=16):
    """Prints a formatted version of the table. Limit prevents console flooding."""
    print(f"\n--- {title} (Order: {len(table)}) ---")
    size = min(len(table), limit)
    
    # Header
    header = "      " + " ".join(f"{labels[i]:>5}" for i in range(size))
    print(header)
    print("-" * len(header))
    
    for i in range(size):
        row = f"{labels[i]:>5} | " + " ".join(f"{labels[table[i][j]]:>5}" for j in range(size))
        print(row)
    
    if len(table) > limit:
        print(f"... and {len(table) - limit} more rows/columns.")

# --- RUNNING THE EXAMPLE ---
if __name__ == "__main__":
    # 1. Generate Base Quaternion Q8
    q8_table, q8_labels = generate_quaternion_table()
    print_cayley_table(q8_table, q8_labels, "Base Q8 Table")

    # 2. Generate Q8 x Q8 (Order 64)
    print("\nComputing Q8 x Q8...")
    q64_table = generate_direct_product(q8_table, q8_table)
    
    # Generate labels for the product: (g1, h1)
    q64_labels = [f"({l1},{l2})" for l1 in q8_labels for l2 in q8_labels]
    
    # Show the top-left corner of the 64x64 table
    print_cayley_table(q64_table, q64_labels, "Direct Product Q8 x Q8 (Top 16x16 Snippet)")

    # 3. Analyze the Mote Structure
    print("\nScanning for Subgroups (this may take a moment for Order 64)...")
    subgroups = find_all_subgroups(q64_table)
    print(f"Total Motes (subgroups) found in Q8 x Q8: {len(subgroups)}")