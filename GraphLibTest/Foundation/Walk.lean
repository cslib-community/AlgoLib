/-
Copyright (c) 2026 Weixuan Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Theory.MooreBound

/-!
# Validated simple-spine regression checks

These checks freeze the declarations used by the relocated
`VertexSeq → SimpleWalk → SimplePath → SimpleCycle → Girth → MooreBound` chain.
-/

namespace GraphLib

open scoped GraphLib

variable {α : Type*}

#check GraphLib.List.commonPrefix
#check GraphLib.List.commonPrefix_split
#check GraphLib.List.commonPrefix_ne_nil

#check GraphLib.Set.ncard_biUnion_finset_eq_sum
#check GraphLib.Set.mul_ncard_le_ncard_of_children

#check VertexSeq.singleton
#check VertexSeq.cons
#check VertexSeq.suffixFrom
#check VertexSeq.eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one

#check SimplePath.singleton
#check SimplePath.append
#check SimplePath.extendTail
#check SimplePath.vertices
#check SimplePath.head
#check SimplePath.tail
#check SimplePath.length

#check SimpleGraph.IsVertexSeqIn.iff_edges
#check SimpleGraph.IsSimpleWalkIn.append
#check SimpleGraph.IsSimpleWalkIn.toSimpleGraph_le
#check SimpleGraph.IsSimpleWalkIn.of_toSimpleGraph_le
#check SimpleGraph.IsSimpleWalkIn.iff_toSimpleGraph_le
#check SimpleGraph.IsSimplePathIn.singleton
#check SimpleGraph.IsSimplePathIn.extendTail
#check SimpleGraph.IsSimplePathIn.exists_longer_of_adj_not_mem

#check SimpleCycle.ofPathClosing
#check SimpleCycle.ofInternallyDisjointPaths
#check SimpleCycle.ofTwoPaths
#check SimpleCycle.length_ofTwoPaths
#check SimpleCycle.head_ofTwoPaths_mem_left
#check SimpleCycle.edges_ofTwoPaths_subset

#check SimpleGraph.IsSimpleCycleIn.ofPathClosing
#check SimpleGraph.IsSimpleCycleIn.ofTwoPaths
#check SimpleGraph.IsSimpleCycleIn.exists_length_le_succ_of_adj_mem
#check SimpleGraph.IsSimpleCycleIn.exists_length_le_add_of_two_paths

#check SimpleGraph.girth
#check SimpleGraph.mooreBound_odd
#check SimpleGraph.mooreBound_even

example (v : α) : (SimplePath.singleton v).vertices = VertexSeq.singleton v := rfl
example (v : α) : (SimplePath.singleton v).head = v := rfl
example (v : α) : (SimplePath.singleton v).tail = v := rfl
example (v : α) : (SimplePath.singleton v).length = 0 := rfl

example (p : SimplePath α) (v : α) (h : v ∉ p.vertices) :
    (p.extendTail v h).vertices = p.vertices.cons v := rfl
example (p : SimplePath α) (v : α) (h : v ∉ p.vertices) :
    (p.extendTail v h).tail = v := rfl

end GraphLib
