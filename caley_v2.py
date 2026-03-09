import itertools
import networkx as nx
import numpy as np
import json

# ==========================================
# 1. THE GENERATORS (The Mote Library)
# ==========================================

def generate_cyclic_table(n):
    return [[(i + j) % n for j in range(n)] for i in range(n)], [f"r{i}" for i in range(n)]

def generate_dihedral_table(n):
    order = 2 * n
    table = [[0] * order for _ in range(order)]
    labels = [f"r{i}s{j}" for j in range(2) for i in range(n)]
    for idx1 in range(order):
        for idx2 in range(order):
            i1, j1 = idx1 % n, idx1 // n
            i2, j2 = idx2 % n, idx2 // n
            new_i = (i1 + i2) % n if j1 == 0 else (i1 - i2) % n
            new_j = (j1 + j2) % 2
            table[idx1][idx2] = new_i + (new_j * n)
    return table, labels

def generate_symmetric_table(n):
    perms = list(itertools.permutations(range(n)))
    p_to_idx = {p: i for i, p in enumerate(perms)}
    order = len(perms)
    table = [[0] * order for _ in range(order)]
    for i in range(order):
        for j in range(order):
            composed = tuple(perms[i][perms[j][k]] for k in range(n))
            table[i][j] = p_to_idx[composed]
    return table, [str(p) for p in perms]

def generate_quaternion_table():
    table = [
        [0,1,2,3,4,5,6,7], [1,0,3,2,5,4,7,6], [2,3,1,0,6,7,5,4], [3,2,0,1,7,6,4,5],
        [4,5,7,6,1,0,2,3], [5,4,6,7,0,1,3,2], [6,7,4,5,3,2,1,0], [7,6,5,4,2,3,0,1]
    ]
    labels = ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]
    return table, labels

def generate_gl_np_table(n, p):
    all_entries = list(itertools.product(range(p), repeat=n*n))
    matrices = []
    for entry_set in all_entries:
        mat = np.array(entry_set).reshape(n, n)
        if int(round(np.linalg.det(mat))) % p != 0:
            matrices.append(tuple(map(tuple, mat)))
    order = len(matrices)
    mat_to_idx = {m: i for i, m in enumerate(matrices)}
    table = [[0] * order for _ in range(order)]
    for i in range(order):
        m1 = np.array(matrices[i])
        for j in range(order):
            m2 = np.array(matrices[j])
            res = (m1 @ m2) % p
            table[i][j] = mat_to_idx[tuple(map(tuple, res))]
    return table, [str(m) for m in matrices]

def generate_direct_product(table1, table2):
    n1, n2 = len(table1), len(table2)
    order = n1 * n2
    table = [[0] * order for _ in range(order)]
    for i in range(order):
        for j in range(order):
            g1, h1 = i // n2, i % n2
            g2, h2 = j // n2, j % n2
            table[i][j] = table1[g1][g2] * n2 + table2[h1][h2]
    return table

# ==========================================
# 2. LOGIC ENGINE (Closures & Lattices)
# ==========================================

def get_closure(elements, table):
    closure = set(elements) | {0}
    added = True
    while added:
        added = False
        curr = list(closure)
        for i in curr:
            for j in curr:
                if table[i][j] not in closure:
                    closure.add(table[i][j]); added = True
    return frozenset(closure)

def find_all_subgroups(table):
    subgroups = {get_closure([i], table) for i in range(len(table))}
    added = True
    while added:
        added = False
        curr = list(subgroups)
        for s1 in curr:
            for s2 in curr:
                new_sg = get_closure(set(s1) | set(s2), table)
                if new_sg not in subgroups:
                    subgroups.add(new_sg); added = True
    return sorted(list(subgroups), key=len)

def build_hasse_mote(subgroups):
    G = nx.DiGraph()
    for i, sg in enumerate(subgroups):
        G.add_node(i, size=len(sg))
        for j, other in enumerate(subgroups):
            if i != j and sg.issubset(other):
                G.add_edge(i, j)
    return nx.transitive_reduction(G)

# ==========================================
# 3. MORPHISM TOOLS (Checking Mappings)
# ==========================================

def is_homomorphism(mapping, t1, t2):
    """Checks if phi(a*b) == phi(a)*phi(b) for all a,b in G."""
    for a in range(len(t1)):
        for b in range(len(t1)):
            if mapping[t1[a][b]] != t2[mapping[a]][mapping[b]]:
                return False, (a, b)
    return True, None

def find_kernel(mapping):
    """Returns the set of indices in the source that map to identity (0)."""
    return [src_idx for src_idx, target_idx in mapping.items() if target_idx == 0]

def export_mote_canvas(group_name, table, labels, subgroups):
    """
    Translates the mathematical structure into a JSON object 
    ready for a whiteboard/canvas rendering.
    """
    hasse = build_hasse_mote(subgroups)
    
    # Calculate positions
    layers = {}
    for node in hasse.nodes():
        order = len(subgroups[node])
        layers.setdefault(order, []).append(node)
    
    sorted_orders = sorted(layers.keys())
    pos = {}
    for y_idx, order in enumerate(sorted_orders):
        nodes_in_layer = layers[order]
        width = len(nodes_in_layer)
        for x_idx, node in enumerate(nodes_in_layer):
            pos[node] = {"x": (x_idx - (width - 1) / 2) * 150, "y": -y_idx * 100}

    # Build the Mote List
    nodes = []
    order_g = len(table)
    
    for i, sg in enumerate(subgroups):
        # Check Normality: gH == Hg for all g in G
        is_normal = True
        for g in range(order_g):
            left_coset = {table[g][h] for h in sg}
            right_coset = {table[h][g] for h in sg}
            if left_coset != right_coset:
                is_normal = False
                break
        
        nodes.append({
            "id": f"mote-{i}",
            "label": f"H{i}" if i > 0 else "e",
            "order": len(sg),
            "index": order_g // len(sg),
            "elements": [labels[idx] for idx in sg],
            "isNormal": is_normal,
            "position": pos[i]
        })

    # Build Edge List
    edges = []
    for u, v in hasse.edges():
        edges.append({
            "id": f"edge-{u}-{v}",
            "source": f"mote-{u}",
            "target": f"mote-{v}",
            "type": "inclusion"
        })

    canvas_json = {
        "groupName": group_name,
        "totalOrder": order_g,
        "motes": nodes,
        "links": edges
    }
    
    return canvas_json

# Example Usage
if __name__ == "__main__":
    t, l = generate_dihedral_table(3) # S3
    s = find_all_subgroups(t)
    canvas = export_mote_canvas("Symmetric Group S3", t, l, s)
    print(json.dumps(canvas, indent=2))