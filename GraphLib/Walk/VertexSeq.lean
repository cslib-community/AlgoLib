/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Walk.VertexSeq.Basic
import GraphLib.Walk.VertexSeq.Predicates
import GraphLib.Walk.VertexSeq.Append
import GraphLib.Walk.VertexSeq.MapZip
import GraphLib.Walk.VertexSeq.Subseq
import GraphLib.Walk.VertexSeq.Erase
import GraphLib.Walk.VertexSeq.Edges
import GraphLib.Walk.VertexSeq.Index
import GraphLib.Util.List

/-!
# Vertex sequences

A `VertexSeq α` is a non-empty inductive sequence of vertices, with a
`singleton` base case and a right-extending `cons`. It is the underlying
carrier for walks, paths and cycles in the graph theory library.

This file defines nothing itself: it is an *umbrella* module that merely
re-exports (imports) the `VertexSeq` development, which is split across
`GraphLib/Walk/VertexSeq/`:

* `Basic` — the carrier, `length`/`head`/`tail`/`toList`, membership/subset,
  and `dropHead`/`dropTail`.
* `Predicates` — `nodup`, `nonstalling`, `closed`.
* `Append` — `append`, `reverse` and their laws.
* `MapZip` — `map`, `foldl`, `foldr`, `zip`, `any`, `all` and the `Functor`
  instance.
* `Subseq` — `prefixUntil`, `suffixFrom`, `takeWhile`, `dropWhile`, `splitAt`.
* `Erase` — `loopErase`, `cycleErase`.
* `Edges` — `edges`, `arcs` (the traversed edges/arcs, as lists).
* `Index` — `GetElem` and `insert`.
The umbrella also imports `GraphLib.Util.List`, whose
`GraphLib.List.commonPrefix` finds where two paths diverge without extending
Mathlib's root `List` namespace.

Downstream files should keep importing this umbrella; the split is internal.

## Module dependency graph

The acyclic spine is `Basic ← Predicates ← Append ← Subseq ← Erase ← Edges`, with
`Index` branching off `Basic` and `MapZip` off `Predicates` (its `nodup`/
`nonstalling` preservation lemmas need the predicates). `GraphLib.Util.List` is
free-standing: it imports only Mathlib.
```text
        Basic                 Util.List
       ╱     ╲                (free-standing)
  Predicates  Index
   ╱      ╲
Append    MapZip
  │
Subseq
  │
Erase
  │
Edges
```
This umbrella imports all eight leaves and the list utility.
-/
