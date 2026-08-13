import graphviz
import os
os.environ["PATH"] += os.pathsep + r"C:\Program Files\Graphviz\bin"

# Or specify the path when creating the Digraph
dot = graphviz.Digraph('GroupDiagram', format='png', 
                       engine='dot', 
                       directory='.', 
                       executable=r'C:\Program Files\Graphviz\bin\dot.exe')
def create_diagram():
    # Create a Digraph object
    dot = graphviz.Digraph('GroupDiagram', format='png')
    dot.attr(rankdir='TB', splines='ortho')
    dot.attr('node', shape='box', style='filled', fontname='monospace', fontsize='10')
    dot.attr('edge', fontname='monospace', fontsize='9')

    # ===== Subgraph Q42 =====
    with dot.subgraph(name='cluster_Q') as c:
        c.attr(label='Q42', color='#93b5c8', fontcolor='#0B151E')
        
        # Nodes
        c.node('Q0', '{e}', shape='doublecircle', fillcolor='#fbbf24', color='#ca8a04', fontcolor='#0B151E', penwidth='2')
        c.node('Q1', '<-1>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        c.node('Q2', '<i>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        c.node('Q3', '<j>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        c.node('Q4', '<k>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        c.node('Q5', '<i,j>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        
        # Normal subgroup inclusions - set edge attributes individually
        c.edge('Q0', 'Q1', penwidth='2', color='#93b5c8')
        c.edge('Q1', 'Q2', penwidth='2', color='#93b5c8')
        c.edge('Q1', 'Q3', penwidth='2', color='#93b5c8')
        c.edge('Q1', 'Q4', penwidth='2', color='#93b5c8')
        c.edge('Q2', 'Q5', penwidth='2', color='#93b5c8')
        c.edge('Q3', 'Q5', penwidth='2', color='#93b5c8')
        c.edge('Q4', 'Q5', penwidth='2', color='#93b5c8')

    # ===== Subgraph Tree =====
    with dot.subgraph(name='cluster_Tree') as c:
        c.attr(label='Z4xZ3 Tree', color='#93b5c8', fontcolor='#0B151E')
        
        # Node definitions with order colours
        c.node('T0', 'e×e', shape='circle', fillcolor='#fbbf24', color='#ca8a04', fontcolor='#0B151E', penwidth='2')
        c.node('T1', 'e×a1', shape='circle', fillcolor='#7c3aed', fontcolor='#ffffff')
        c.node('T2', 'e×a2', shape='circle', fillcolor='#7c3aed', fontcolor='#ffffff')
        c.node('T3', 'a1×e', shape='circle', fillcolor='#db2777', fontcolor='#ffffff')
        c.node('T4', 'a1×a1', shape='circle', fillcolor='#0284c7', fontcolor='#ffffff')
        c.node('T5', 'a1×a2', shape='circle', fillcolor='#0284c7', fontcolor='#ffffff')
        c.node('T6', 'a2×e', shape='circle', fillcolor='#0284c7', fontcolor='#ffffff')
        c.node('T7', 'a2×a1', shape='circle', fillcolor='#ca8a04', fontcolor='#ffffff')
        c.node('T8', 'a2×a2', shape='circle', fillcolor='#ca8a04', fontcolor='#ffffff')
        c.node('T9', 'a3×e', shape='circle', fillcolor='#db2777', fontcolor='#ffffff')
        c.node('T10', 'a3×a1', shape='circle', fillcolor='#0284c7', fontcolor='#ffffff')
        c.node('T11', 'a3×a2', shape='circle', fillcolor='#0284c7', fontcolor='#ffffff')
        
        # Edge path
        c.edge('T9', 'T1', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T10', 'T2', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T2', 'T3', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T0', 'T4', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T1', 'T5', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T5', 'T6', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T3', 'T7', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T4', 'T8', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T8', 'T9', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T6', 'T10', penwidth='1', color='#93b5c8', arrowhead='normal')
        c.edge('T7', 'T11', penwidth='1', color='#93b5c8', arrowhead='normal')

    # ===== Subgraph G =====
    with dot.subgraph(name='cluster_G') as c:
        c.attr(label='Z4xZ3', color='#93b5c8', fontcolor='#0B151E')
        
        c.node('G0', '{e}', shape='doublecircle', fillcolor='#fbbf24', color='#ca8a04', fontcolor='#0B151E', penwidth='2')
        c.node('G1', '<a2×e>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        c.node('G2', '<e×a1>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        c.node('G3', '<a1×e>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        c.node('G4', '<a2×a1>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        c.node('G5', '<a1×a1>', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E', penwidth='2')
        
        # Normal subgroup inclusions
        c.edge('G0', 'G1', penwidth='2', color='#93b5c8')
        c.edge('G0', 'G2', penwidth='2', color='#93b5c8')
        c.edge('G1', 'G3', penwidth='2', color='#93b5c8')
        c.edge('G1', 'G4', penwidth='2', color='#93b5c8')
        c.edge('G2', 'G4', penwidth='2', color='#93b5c8')
        c.edge('G3', 'G5', penwidth='2', color='#93b5c8')
        c.edge('G4', 'G5', penwidth='2', color='#93b5c8')

    # ===== Morphisms =====
    dot.edge('Q2', 'T8', label='phi1', style='dashed', penwidth='1', color='#93b5c8', arrowhead='vee')
    dot.edge('Q3', 'T9', label='phi1', style='dashed', penwidth='1', color='#93b5c8', arrowhead='vee')
    dot.edge('Q4', 'T1', label='phi1', style='dashed', penwidth='1', color='#93b5c8', arrowhead='vee')
    dot.edge('T10', 'G1', label='phi2', style='dashed', penwidth='1', color='#93b5c8', arrowhead='vee')
    dot.edge('T2', 'G0', label='phi2', style='dashed', penwidth='1', color='#93b5c8', arrowhead='vee')
    dot.edge('T3', 'G2', label='phi2', style='dashed', penwidth='1', color='#93b5c8', arrowhead='vee')

    # ===== Legend =====
    with dot.subgraph(name='cluster_legend') as c:
        c.attr(label='Shape Key', color='#93b5c8', fontcolor='#0B151E', style='dashed')
        
        c.node('L0', 'e', shape='doublecircle', fillcolor='#fbbf24', color='#ca8a04', fontcolor='#0B151E')
        c.node('L1', 'Normal', shape='box', fillcolor='#4ade80', color='#16a34a', fontcolor='#0B151E')
        c.node('L2', 'Standard', shape='circle', fillcolor='#db2777', fontcolor='#ffffff')
        c.node('L3', 'Thick edge', shape='plaintext', style='solid', fontcolor='#0B151E')
        c.node('L4', 'Morphism', shape='plaintext', style='dashed', fontcolor='#0B151E')
        
        # Invisible edges for layout
        c.edge('L0', 'L1', style='invis')
        c.edge('L1', 'L2', style='invis')
        c.edge('L2', 'L3', style='invis')
        c.edge('L3', 'L4', style='invis')

    return dot

# Use the function
if __name__ == "__main__":
    dot = create_diagram()
    dot.render('group_diagram', view=True)  # Saves as group_diagram.png and opens it