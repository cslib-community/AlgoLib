/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weixuan Yuan
-/
import GraphLib.Walk.InSimpleGraph
import GraphLib.Graph.Degree
import GraphLib.Theory.Coloring.Bipartite
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card

/-!
# Girth

The girth of a simple graph is the length of its shortest simple cycle.  We use
`WithTop ℕ`, so acyclic graphs have girth `⊤`.

The realized-cycle predicates `SimpleGraph.IsSimpleCycleIn`, `HasSimpleCycle`
and `IsAcyclic` live in `GraphLib.Walk.InSimpleGraph`.

## Main definitions

* `SimpleGraph.girth G` — the least length of a simple cycle in `G`, or `⊤`.

## Main results

* `SimpleGraph.girth.ge_iff` / `SimpleGraph.girth.le_iff` — the lower- and
  upper-bound characterizations; nearly everything else is a corollary of these.
* `SimpleGraph.girth.eq_top_iff_isAcyclic` — infinite girth is acyclicity.
* `SimpleGraph.girth.exists_cycle` — a finite girth is attained by some cycle.
* `SimpleGraph.girth.ne_top_of_two_le_degree` — minimum degree two forces a cycle.
* `SimpleGraph.girth.even_of_isBipartite` — the girth of a bipartite graph is
  even. The basic bipartite colouring API lives in
  `GraphLib.Theory.Coloring.Bipartite`; only this girth
  corollary depends on the girth development, so it lives here.

## Implementation notes

`girth` is defined as a nested infimum `⨅ c, ⨅ _ : G.IsSimpleCycleIn c, c.length`
over `ℕ∞`. The empty-index convention makes the girth of an acyclic graph `⊤`
automatically, and the infimum API (`le_iInf`, `iInf₂_le`) drives the basic
lemmas below; see `girth.ge_iff` for the workhorse characterization.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## Girth -/

/-- The girth of a simple graph: the length of a shortest simple cycle, or `⊤`
when there is no simple cycle. -/
noncomputable def girth (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (c : SimpleCycle α) (_ : G.IsSimpleCycleIn c), (c.length : ℕ∞)

namespace girth

/-! ## Lower bounds -/

/-- Characterization of lower bounds for the girth: `n ≤ girth` iff `n` bounds the
length of every simple cycle in `G`. This is the workhorse behind the lemmas
below. -/
@[grind =] lemma ge_iff (G : SimpleGraph α) {n : ℕ∞} : n ≤ G.girth ↔
    ∀ c : SimpleCycle α, G.IsSimpleCycleIn c → n ≤ c.length := by
  simp [girth, le_iInf_iff]

/-- Every simple cycle in `G` gives an upper bound on the girth. -/
@[grind →] lemma le_length (G : SimpleGraph α) {c : SimpleCycle α}
    (hc : G.IsSimpleCycleIn c) : G.girth ≤ c.length :=
  iInf₂_le c hc

/-- If `n` is strictly below the girth, every realized simple cycle has length
strictly greater than `n`. -/
lemma lt_cycle_length (G : SimpleGraph α) {c : SimpleCycle α}
    (hc : G.IsSimpleCycleIn c) {n : ℕ} (h : (n : ℕ∞) < G.girth) :
    n < c.length := by
  have h' : (n : ℕ∞) < (c.length : ℕ∞) := h.trans_le (le_length G hc)
  exact_mod_cast h'

/-- The girth is at least three. This is true also for acyclic graphs, where the
girth is `⊤`. -/
@[grind! .] lemma three_le (G : SimpleGraph α) : (3 : ℕ∞) ≤ G.girth :=
  (ge_iff G).2 fun c _ => by exact_mod_cast c.2.1

/-! ## Infinite girth and acyclicity -/

/-- A simple graph is acyclic exactly when its girth is infinite. -/
@[grind =] lemma eq_top_iff_isAcyclic (G : SimpleGraph α) :
    G.girth = ⊤ ↔ G.IsAcyclic := by
  simp [girth, iInf_eq_top, IsAcyclic, HasSimpleCycle]

/-- A graph with no simple cycle has infinite girth. -/
lemma eq_top_of_isAcyclic (G : SimpleGraph α) (hG : G.IsAcyclic) :
    G.girth = ⊤ :=
  (eq_top_iff_isAcyclic G).2 hG

/-- A simple graph has finite girth exactly when it contains a simple cycle. -/
@[grind =] lemma ne_top_iff_hasSimpleCycle (G : SimpleGraph α) :
    G.girth ≠ ⊤ ↔ G.HasSimpleCycle := by
  rw [← not_iff_not]
  simp [eq_top_iff_isAcyclic, IsAcyclic]

/-! ## Attainment -/

/-- When the girth is finite, it is attained: some simple cycle in `G` has length
equal to the girth. -/
lemma exists_cycle (G : SimpleGraph α) (h : G.girth ≠ ⊤) :
    ∃ c : SimpleCycle α, G.IsSimpleCycleIn c ∧ (c.length : ℕ∞) = G.girth := by
  classical
  obtain ⟨c₀, hc₀⟩ := (ne_top_iff_hasSimpleCycle G).1 h
  have hex : ∃ n : ℕ, ∃ c : SimpleCycle α, G.IsSimpleCycleIn c ∧ c.length = n :=
    ⟨c₀.length, c₀, hc₀, rfl⟩
  obtain ⟨c, hc, hlen⟩ := Nat.find_spec hex
  refine ⟨c, hc, le_antisymm ?_ (le_length G hc)⟩
  rw [ge_iff]
  intro c' hc'
  rw [hlen]
  exact_mod_cast Nat.find_min' hex ⟨c', hc', rfl⟩

/-- A realized simple cycle whose length is minimal among all realized simple
cycles attains the girth. -/
lemma eq_length_of_minimal (G : SimpleGraph α) {c : SimpleCycle α}
    (hc : G.IsSimpleCycleIn c)
    (hmin : ∀ c' : SimpleCycle α, G.IsSimpleCycleIn c' → c.length ≤ c'.length) :
    G.girth = c.length := by
  refine le_antisymm (le_length G hc) ?_
  rw [ge_iff]; intro c' hc'
  exact_mod_cast hmin c' hc'

/-! ## Upper bounds -/

/-- A realized simple cycle of length at most `n` gives the upper bound
`girth ≤ n`. -/
@[grind →] lemma le_of_length_le (G : SimpleGraph α) {c : SimpleCycle α}
    (hc : G.IsSimpleCycleIn c) {n : ℕ∞} (hlen : (c.length : ℕ∞) ≤ n) :
    G.girth ≤ n :=
  (le_length G hc).trans hlen

/-- Upper bounds for the girth by a natural number: `girth ≤ n` exactly when `G`
contains a realized simple cycle of length at most `n`. The bound is stated over
`ℕ`, since for the bound `⊤` the right-hand side would fail on acyclic graphs.
This is the upper-bound companion of `ge_iff`. -/
@[grind =] lemma le_iff (G : SimpleGraph α) {n : ℕ} :
    G.girth ≤ n ↔ ∃ c : SimpleCycle α, G.IsSimpleCycleIn c ∧ c.length ≤ n := by
  constructor
  · intro h
    have hfin : G.girth ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top n) h
    obtain ⟨c, hc, hlen⟩ := exists_cycle G hfin
    refine ⟨c, hc, ?_⟩
    have hle : (c.length : ℕ∞) ≤ (n : ℕ∞) := hlen.symm ▸ h
    exact_mod_cast hle
  · rintro ⟨c, hc, hlen⟩
    exact le_of_length_le G hc (by exact_mod_cast hlen)

/-- If `G` has finite girth, then its girth is at most the number of vertices. -/
lemma le_ncard_vertexSet (G : SimpleGraph α) (hV : V(G).Finite)
    (hG : G.girth ≠ ⊤) : G.girth ≤ V(G).ncard := by
  obtain ⟨c, hc, hlen⟩ := exists_cycle G hG
  rw [← hlen]
  exact_mod_cast IsSimpleCycleIn.length_le_ncard_vertexSet G hV hc

/-! ## Finiteness from a degree bound -/

/-- A finite nonempty simple graph with every vertex of degree at least two has
finite girth. -/
lemma ne_top_of_two_le_degree (G : SimpleGraph α) [Finite V(G)]
    (hne : V(G).Nonempty)
    (hdeg : ∀ v : α, v ∈ V(G) → 2 ≤ G.degree v) :
    G.girth ≠ ⊤ := by
  classical
  have hV : V(G).Finite := G.vertexSet_finite
  let P : ℕ → Prop :=
    fun n => ∃ p : SimplePath α, G.IsSimplePathIn p ∧ p.length = n
  obtain ⟨v, hv⟩ := hne
  have hP0 : P 0 :=
    ⟨SimplePath.singleton v, IsSimplePathIn.singleton G hv, rfl⟩
  let L := Nat.findGreatest P V(G).ncard
  have hPL : P L :=
    Nat.findGreatest_spec (P := P) (m := 0) (n := V(G).ncard)
      (Nat.zero_le _) hP0
  obtain ⟨p, hp, hplen⟩ := hPL
  have hmax : ∀ q : SimplePath α, G.IsSimplePathIn q → q.length ≤ L := by
    intro q hq
    have hq_bound : q.length ≤ V(G).ncard := by
      have := IsSimplePathIn.length_succ_le_ncard_vertexSet G hV hq
      omega
    by_contra hnot
    have hlt : L < q.length := Nat.lt_of_not_ge hnot
    exact (Nat.findGreatest_is_greatest (P := P) hlt hq_bound) ⟨q, hq, rfl⟩
  -- Extending the maximal path `p` by a fresh neighbour of its tail is
  -- impossible: it would produce a realized path of length `L + 1 > L`.
  have hcontra : ∀ y : α, G.Adj p.tail y → y ∉ p.vertices → False := by
    intro y hadj hy_not
    obtain ⟨q, hq, hq_length⟩ := IsSimplePathIn.exists_longer_of_adj_not_mem G hp hadj hy_not
    have hq_max := hmax q hq
    rw [hq_length, hplen] at hq_max
    omega
  have htail_mem : p.tail ∈ V(G) := SimpleGraph.IsSimpleWalkIn.tail_mem G hp
  have htail_deg : 1 < (G.neighborSet p.tail).ncard := by
    have htwo := hdeg p.tail htail_mem
    rw [G.ncard_neighborSet_eq_degree]
    exact lt_of_lt_of_le Nat.one_lt_two htwo
  by_cases hzero : p.length = 0
  · -- `p` is a single vertex, so any neighbour of `p.tail` is fresh.
    obtain ⟨y, hy, _⟩ := Set.exists_ne_of_one_lt_ncard htail_deg p.tail
    refine (hcontra y hy ?_).elim
    intro hymem
    have hlen : p.vertices.length = 0 := hzero
    exact hy.ne (by grind)
  · -- Pick a neighbour `y` of `p.tail` other than the second-to-last vertex.
    let prev : α := p.vertices.dropTail.tail
    obtain ⟨y, hy, hy_ne_prev⟩ := Set.exists_ne_of_one_lt_ncard htail_deg prev
    by_cases hy_mem : y ∈ p.vertices
    · -- `y` lies on `p`, so the suffix from `y` closes into a cycle.
      have hq_len : 2 ≤ (p.vertices.suffixFrom y hy_mem).length := by
        by_contra hlt
        have hle : (p.vertices.suffixFrom y hy_mem).length ≤ 1 := by
          change ¬ 2 ≤ (p.vertices.suffixFrom y hy_mem).length at hlt
          omega
        rcases VertexSeq.eq_tail_or_eq_penultimate_of_length_suffixFrom_le_one
            p.vertices hy_mem hzero hle with htail | hprev
        · exact hy.ne htail.symm
        · exact hy_ne_prev hprev
      obtain ⟨c, hc, _⟩ :=
        IsSimpleCycleIn.exists_length_le_succ_of_adj_mem G hp hy_mem hy hq_len
      exact (ne_top_iff_hasSimpleCycle G).2 ⟨c, hc⟩
    · -- `y` is fresh, contradicting maximality.
      exact (hcontra y hy hy_mem).elim

/-! ## Subgraphs -/

/-- Passing to a subgraph can only increase the girth. -/
@[grind →] lemma le_of_subgraph (G H : SimpleGraph α)
    (hsub : H ≤ G) : G.girth ≤ H.girth := by
  by_cases hH : H.girth = ⊤
  · rw [hH]; exact le_top
  · obtain ⟨c, hc, hlen⟩ := exists_cycle H hH
    rw [← hlen]
    exact le_length G (IsSimpleCycleIn.mono G H hc hsub)

/-! ## Edge-free graphs -/

/-- An edge-free graph has infinite girth. -/
lemma eq_top_of_no_edges (G : SimpleGraph α) (hE : E(G) = ∅) :
    G.girth = ⊤ := eq_top_of_isAcyclic G (isAcyclic_of_no_edges G hE)

/-! ## Girth of bipartite graphs -/

/-- The girth of a bipartite graph is even. Here `Even (⊤ : ℕ∞)` holds, so this
single statement also covers the acyclic case where the girth is `⊤`. -/
theorem even_of_isBipartite (G : SimpleGraph α) (hG : G.IsBipartite) :
    Even G.girth := by
  by_cases h : G.girth = ⊤
  · rw [h]; exact ⟨⊤, by simp⟩
  · obtain ⟨c, hc, hlen⟩ := exists_cycle G h
    obtain ⟨r, hr⟩ := IsBipartite.even_length_of_isSimpleCycleIn G hG hc
    exact ⟨(r : ℕ∞), by rw [← hlen, hr, Nat.cast_add]⟩

end girth

end SimpleGraph

end GraphLib
