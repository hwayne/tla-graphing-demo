## Likelihoods

### Overview

Todo.

### l:nx\_reference

[NetworkX](https://networkx.org/documentation/stable/reference/introduction.html) is a graph analysis library for Python. The graph is represented by a dict of dict of dicts: `G[n]` generates all nodes reachable from `n`, `G[n][p]` is the edge between `n` and `p`, and the edge itself is a dictionary of the edge's attributes. You get attributes of the node itself with `G.nodes[n]`.

<details><summary>Used methods</summary>

* [DiGraph](https://networkx.org/documentation/stable/reference/classes/digraph.html)
* [selfloop_edges](https://networkx.org/documentation/stable/reference/generated/networkx.classes.function.selfloop_edges.html)
* [out_edges](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.out_edges.html#networkx.DiGraph.out_edges)
* [read_dot](https://networkx.org/documentation/stable/reference/generated/networkx.drawing.nx_agraph.read_dot.html#networkx.drawing.nx_agraph.read_dot)
* [get_edge_data](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.get_edge_data.html#networkx.DiGraph.get_edge_data)
* [remove_edges_from](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.remove_edges_from.html#networkx.DiGraph.remove_edges_from)
* [in_degree](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.in_degree.html#digraph-in-degree)
* [out_degree](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.out_degree.html#networkx.DiGraph.out_degree)
* [nodes](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.nodes.html#networkx.DiGraph.nodes)
* [edges](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.edges.html#networkx.DiGraph.edges)
* [predecessors](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.predecessors.html#networkx.DiGraph.predecessors)
* [set_node_attributes](https://networkx.org/documentation/stable/reference/generated/networkx.classes.function.set_node_attributes.html#set-node-attributes)

</details>

### l:read\_dot (7)

This is the performance bottleneck of the script, probably something like 90% of the time is spent here. If you want to try doing multiple analyses of the same graph, you can read the dotfile just once and use [DiGraph.copy](https://networkx.org/documentation/stable/reference/classes/generated/networkx.DiGraph.copy.html#networkx.DiGraph.copy) to make new copies.

### l:remove\_edges (8)

The TLA+ spec has self-loops from each `Done` state to itself, in order to prevent the algorithm completion counting as a [deadlock](https://learntla.com/core/concurrency.html#index-5).  But those make analyzing the graph annoying so we remove them.

### l:label (11, 21)

The TLA+ dump natively uses the node label to include all of the state variables and the edge label to store the action name:

```gv
2870009878292733134 [label="/\\ x = 0\n/\\ pc = <<\"Get\", \"Inc\">>\n/\\ tmp = <<0, 0>>"];
8830631066581796563 -> 2870009878292733134 [label="Get",color="black",fontcolor="black"];
```

The only way to extract the label is with a regex.

### l:root (13, 43)

Each graph has only one starting state so only one root. I attach it to the graph out of pure convenience so I can later use it in `get_likelihood` (13). I have *no idea* why pyright doesn't complain about this.

### l:weight\_edges (16)

The probability of each edge being taken from a given state. Not all transitions are equally likely, as some represent a thread getting interrupted, which is comparatively less likely. Computing this is *real annoying* though, so instead we assume that the history doesn't matter. Given the *subgraph*

```
          Z
          |
        [inc]
          v
Y -[get]> A -[inc]> B
          |
        [get]
          v
          C
```

The probabilities of `A -> B` and `A -> C` are independent of if we got to A via Z or if we got there via Y. Instead, we roughly mimic the path dependence by saying that `inc` transitions are more likely than `get` transitions. The parameter `inc_weight` is how much more likely an `inc` transition is.

We define the probability of a given transition `T` as the total weight of all outbound transitions divided by the local weight of `T`. So if `inc_weight=1`, then the weight of `A -[inc]> B` and `A -[get]> c` are both `0.5`. If `inc_weight=2`, it's instead `2/3` and `1/3`. Note the sum should always be 1.

If you want to make a `get` *more* likely than an `inc`, just choose `inc_weight < 1`.


#### l:we:alias (27, 33)

This is my favorite little bit of the code. `G.out_edges` returns an *iterator* over the outbound edges, so is consumed in the for loop. We only know the total weight after iterating through all of them. By storing each alias after iterating through it, we can save an extra call to `G.out_edges`.

Honestly it probably doesn't save *that* much time. I just like using dangerous features in scripts. Hurrah for aliasing!

#### l:we:cache (33)

Calculating the weight is expensive and we might need to look up the weight a whole bunch of times so might as well add it to the edge data.

#### l:we:assert (34)

Doesn't always add up to exactly 1 due to floating point errors, so we only check it's within 0.02. We need the `if edges:` conditional because this check only applies if there are outbound edges, ie `n` isn't a terminal state. Ideally I'd be able to write this as `assert edges => blah blah blah` but programming languages never seem to have an implication operator :(

### l:set\_likelihood (38)

Since we're caching the likelihoods in the node attributes, we need to blow them all away if we want to recalculate the likelihoods, say with a different `inc_weight`. 

We don't actually recalculate the likelihoods in the script, so the line isn't strictly necessary. I added it in case you want to play around with the graphs some more.

### l:get\_likelihood (42)

The likelihood of reaching a state is the sum of the likelihoods of prior states, times the probability of the edges from it. Let's look at a diagram again:

```
    (0.5) B -[get]> D
          |
        [get]
          v
A -[get]> C 
(0.25)    
```

B has a likelihood of 50%, A of 25%. B has a 50% chance of transitioning to C and a 50% chance of transitioning to D, A has a 100% chance of transitioning to C. So the likelihood of C is `0.5*0.5 + 0.25 * 1 = 0.5`.

This only works because the state graphs are acyclic. If we had cycles we'd need to model this as a [stochastic matrix](https://en.wikipedia.org/wiki/Stochastic_matrix) and that's not fun.


#### l:gl:recursion (42)

This potentially does unnecessary work when no nodes have assigned likelihoods. First, if a node has multiple predecessors, you'll have redundant calculations.

```
A -> B -> D
|         ^
v         |
C --------+
```

`get_likelihood(_, D)` calls `gl(_, B)` and `gl(_, C)`, which *both* call `gl(_, A)`. This means we're calculating the likelihood of `A` twice. If `B` and `C` already have assigned likelihoods, then this problem goes away.

You still have inefficiencies in computing the whole graph, though. If `set_likelihoods` iterates `A, B, C, D`, then we compute A once, B once, C once, D once. If instead it iterates `D, C, B, A`, we compute D once, C twice, B twice, and A four times. Right now it's not a big slowdown compared to the overhead of importing a graphviz file, but I can imagine it'd add up for really big graphs. The solution would be to [topologically sort](https://docs.python.org/3/library/graphlib.html) the graph.

### l:terminals (58)

The terminal states of the graph are the ones with no outbound edges. Since every behavior ends in a terminal state, their likelihoods sum up to 1. Note we had to remove the self loops in `make_graph` to properly find them. 

While pyright didn't complain about `G.root`, it does complain if I try to do the same with `G.terminals`. Fortunately I only need it here so no biggie.

### l:parse\_args (TODO)

This is a pattern I use in a lot of my scripts:

```py
def main(args):
    # actual code goes here

def parse_args(): # l:parse_args
    parser = ArgumentParser()
    # add a bunch of arguments
    parser.add_argument("arg1")
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    out = main(args)
```

I like this because it's easier to import into other python files and the poke at in the REPL.
