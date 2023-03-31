import networkx as nx
import re
from argparse import ArgumentParser
from collections import Counter

def make_graph(path) -> nx.DiGraph:
    G = nx.nx_agraph.read_dot(path)
    G.remove_edges_from(nx.selfloop_edges(G))
    for node in G:
         label = G.nodes[node]["label"]
         x = re.search(r'x\s*=\s*(\d+)', label).group(1) # pyright: ignore
         G.nodes[node]["x"] = int(x)
    G.root = [n for n, deg in G.in_degree() if deg == 0][0]
    return G

def weight_edges(G: nx.DiGraph, inc_weight=1):
    for n in G:
        total = 0
        edges = []
        for edge in G.out_edges(n):
            if G.get_edge_data(*edge)['label'] == "Inc": # type: ignore
                v = inc_weight
            else: 
                v = 1
            total += v
            edges.append((edge, v))
        for alias, weight in edges:
            G.get_edge_data(*alias)['weight'] = weight / total
        assert sum([G[n][x]["weight"] for x in G.neighbors(n)]) - 1 < 1e-2


def get_likelihood(G, n, force=False):
    if n == G.root: # root node
        return 1
    if (l := G.nodes[n].get("likelihood")) and not force:
        return l

    likelihood = 0
    for source in G.predecessors(n):
        likelihood += get_likelihood(G, source, force)*G[source][n]['weight']
    return likelihood

def set_likelihoods(G):
    for n in G: 
        l = get_likelihood(G, n)
        G.nodes[n]["likelihood"] = l

def main(path=r"./graphs/2_threads.dot", weight=1):
    G = make_graph(path)
    weight_edges(G, weight)
    set_likelihoods(G)
    out = Counter()
    terminals = [n for n, deg in G.out_degree() if deg == 0]
    for t in terminals:
        out[G.nodes[t]["x"]] += get_likelihood(G, t)
    print(out)

def parse_args():
    parser = ArgumentParser()
    parser.add_argument("file", help="graph file to process. Should be a graphviz dotfile")
    parser.add_argument("-w", "--weight", type=int, default=1, help="print output STDOUT instead of modifying originally file.")
    # TODO format flag
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    out = main(args.file, args.weight)
