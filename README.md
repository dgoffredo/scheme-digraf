![Chicken Scheme digraph module](digraf.jpg)

scheme-digraf
=============
Yet another directed graph data structure in Chicken Scheme

Why
---
I encountered small headaches using the existing eggs, and since my work with
Chicken is a side project whose main goal is my learning Scheme, what the hell.

What
----
`digraf` is a misspelled record type with accompanying methods for working with
the vertices and edges of a directed graph.  Adding and removing vertices and
edges is efficient even for large graphs, as is querying the predecessors and
successors of a vertex.

More
----
Right now there are no tests and no examples, but there is an overview in the
code.
