#! /usr/bin/env python3

from pickle import FALSE, TRUE
import networkx as nx

G = nx.DiGraph(nx.drawing.nx_pydot.read_dot("import_graph.dot"))

children = {}
indirect = {}

for i in G.nodes:
    children[i] = set()
    indirect[i] = set()

for e in G.edges:
    children[e[1]].add(e[0])

done = 1
while (done > 0):
    done = 0
    for e in G.edges:
        for i in children[e[0]]:
            if not i in indirect[e[1]]:
                indirect[e[1]].add(i)
                done = done + 1
            if not i in children[e[1]]:
                children[e[1]].add(i)
                done = done + 1
    print (done)

edge_list = []

for e in G.edges:
    if e[0] in indirect[e[1]]:
        edge_list.append(e)

G.remove_edges_from(edge_list)

nx.drawing.nx_pydot.write_dot (G, "import_graph.clean.dot")
