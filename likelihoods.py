"""Anything with l:string has a longer explanation in notes.md."""

import networkx as nx # l:nx_reference
import re
from argparse import ArgumentParser
from collections import Counter

def make_graph(path) -> nx.DiGraph:
    G = nx.nx_agraph.read_dot(path) # l:read_dot
    G.remove_edges_from(nx.selfloop_edges(G)) #l:remove_edges
    for node in G:
         label = G.nodes[node]["label"]
         x = re.search(r'x\s*=\s*(\d+)', label).group(1) # pyright: ignore # l:re
         G.nodes[node]["x"] = int(x)
    G.root = [n for n, deg in G.in_degree() if deg == 0][0] # l:root
    return G

def weight_edges(G: nx.DiGraph, inc_weight=1.0): # l:weight_edges
    """Assigns a probability weight to the every outbound edge of a node. 

    inc_weight is relative weight of increment transitions normalized to a `get` transition."""

    for n in G:
        total = 0
        edges = [] # l:we:alias
        for edge in G.out_edges(n):
            data_alias = G.get_edge_data(*edge) # l:we:alias
            if data_alias['label'] == "Inc": # type: ignore 
                v = inc_weight
            else: 
                v = 1.0
            total += v
            edges.append((data_alias, v))
        for alias, weight in edges: 
            alias['weight'] = weight / total # l:we:cache
        if edges:
            assert abs(sum([alias["weight"] for alias, _ in edges]) - 1) < 1e-2 # l:we:assert

def set_likelihoods(G):
    nx.set_node_attributes(G, None, "likelihood") # l:set_likelihood
    for n in G: 
        G.nodes[n]["likelihood"] = get_likelihood(G, n)

def get_likelihood(G, n): # l:get_likelihood
    if n == G.root: # root node l:root
        return 1
    if l := G.nodes[n].get("likelihood"):
        return l

    likelihood = 0
    for source in G.predecessors(n):
        likelihood += get_likelihood(G, source)*G[source][n]['weight'] # l:gl:recursion
    return likelihood


def main(path=r"./graphs/2_threads.dot", weight=1): 
    G = make_graph(path)
    weight_edges(G, weight)
    set_likelihoods(G)
    terminals = [n for n, deg in G.out_degree() if deg == 0] # l:terminals
    out = Counter()
    for t in terminals:
        out[G.nodes[t]["x"]] += get_likelihood(G, t)
    print(out)

def parse_args(): # l:parse_args
    parser = ArgumentParser()
    parser.add_argument("file", help="graph file to process. Should be a graphviz dotfile")
    parser.add_argument("-w", "--weight", type=int, default=1, help="print output STDOUT instead of modifying originally file.")
    # TODO format flag
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    out = main(args.file, args.weight)
