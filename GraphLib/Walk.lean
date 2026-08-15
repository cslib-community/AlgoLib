/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.VertexSeq
import GraphLib.Walk.SimpleWalk
import GraphLib.Walk.SimplePath
import GraphLib.Walk.SimpleCycle
import GraphLib.Walk.SimpleDiCycle
import GraphLib.Walk.Walk
import GraphLib.Walk.Trail
import GraphLib.Walk.Path
import GraphLib.Walk.Circuit
import GraphLib.Walk.Cycle
import GraphLib.Walk.InSimpleGraph
import GraphLib.Walk.InSimpleDiGraph
import GraphLib.Walk.InGraph
import GraphLib.Walk.InDiGraph
import GraphLib.Walk.Coverage

/-!
# Walk foundation

Declaration-free umbrella for graph-independent traversal data, the preserved simple-walk spine,
all four realization layers, and Eulerian/Hamiltonian coverage specifications.
-/
