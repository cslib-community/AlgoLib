/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai
-/
import Mathlib.Data.Sym.Sym2
import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.Notation  -- for `s [μ]→ t`

/-!
-/

namespace GraphLib
variable {α β : Type*}

structure SimpleGraph (α : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  Adj : α → α → Prop
  symm : Std.Symm Adj := by grind
  loopless : Std.Irrefl Adj := by grind
  left_mem_of_adj : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet := by grind

theorem SimpleGraph.adj_symm (G : SimpleGraph α) : Symmetric G.Adj :=
  fun _ _ h => G.symm.symm _ _ h

def SimpleGraph.edgeSet (G : SimpleGraph α) : Set (Sym2 α) :=
  Sym2.fromRel (G.adj_symm)

structure SimpleDiGraph (α : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  Adj : α → α → Prop
  loopless : Std.Irrefl Adj := by grind
  mem_of_adj : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet ∧ y ∈ vertexSet := by grind

def SimpleDiGraph.edgeSet (G : SimpleDiGraph α) : Set (α × α) :=  {p | G.Adj p.1 p.2}

structure DiGraph (α β : Type*) extends Cslib.LTS α β where
  vertexSet : Set α
  incidence : ∀ ⦃x l y⦄, Tr x l y → x ∈ vertexSet ∧ y ∈ vertexSet := by grind

def DiGraph.edgeSet (G : DiGraph α β) : Set (α × β × α) :=
  {(n, l, n') | G.Tr n l n'}

end GraphLib
