module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Mathlib multigraph semantic adapter for the Hierholzer benchmark

This file spells the frozen graph meanings without changing Mathlib's `Graph` foundation.
-/

@[expose] public section

set_option autoImplicit false

namespace Benchmarks.Hierholzer.Mathlib

open Set
open scoped Graph

universe u v

variable {α : Type u} {ε : Type v}

/-- The actual mathematical vertices of a Mathlib multigraph. -/
abbrev Vertex (G : Graph α ε) := {x // x ∈ V(G)}

/-- The actual mathematical edges of a Mathlib multigraph. -/
abbrev Edge (G : Graph α ε) := {e // e ∈ E(G)}

/-- The frozen actual-edge link relation. -/
def Link (G : Graph α ε) (e : Edge G) (x y : Vertex G) : Prop :=
  G.IsLink e.1 x.1 y.1

/-- The frozen actual-edge incidence relation. -/
def Inc (G : Graph α ε) (e : Edge G) (x : Vertex G) : Prop :=
  ∃ y : Vertex G, Link G e x y

/-- The frozen loop-at-a-vertex relation. -/
def Loop (G : Graph α ε) (e : Edge G) (x : Vertex G) : Prop :=
  Link G e x x

/-- The frozen loop-corrected degree: loops contribute twice. -/
noncomputable def degree (G : Graph α ε) (x : Vertex G) : Nat :=
  Set.ncard {e : Edge G | Inc G e x} + Set.ncard {e : Edge G | Loop G e x}

/-- One graph step, retaining the existence of an actual mathematical edge. -/
def Step (G : Graph α ε) (x y : Vertex G) : Prop :=
  ∃ e : Edge G, Link G e x y

/-- Frozen reachability: reflexive-transitive closure of actual-edge steps. -/
def Reachable (G : Graph α ε) : Vertex G → Vertex G → Prop :=
  Relation.ReflTransGen (Step G)

@[simp] theorem link_symm {G : Graph α ε} {e : Edge G} {x y : Vertex G} :
    Link G e x y ↔ Link G e y x := by
  exact Graph.isLink_comm

theorem link_left_inc {G : Graph α ε} {e : Edge G} {x y : Vertex G}
    (h : Link G e x y) : Inc G e x :=
  ⟨y, h⟩

theorem link_right_inc {G : Graph α ε} {e : Edge G} {x y : Vertex G}
    (h : Link G e x y) : Inc G e y :=
  ⟨x, (link_symm.mp h)⟩

end Benchmarks.Hierholzer.Mathlib
