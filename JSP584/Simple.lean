/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Mathlib
import JSP584.Core

/-!
# JSP-000584 — every 4-regular graph plus an edge has a 3-regular subgraph

Alon–Friedland–Kalai, *Every 4-regular graph plus an edge contains a 3-regular
subgraph*, J. Combin. Theory Ser. B **37** (1984), 92–93.

**Scope.**  This file treats *simple* graphs.  The paper allows multiple edges,
and multiple edges are what make the "plus an edge" hypothesis necessary (an odd
cycle with every edge doubled is 4-regular with no 3-regular subgraph).  For
simple graphs Taškinov's theorem already gives a 3-regular subgraph without the
extra edge, so the statements here are a *special case*.  The faithful
multigraph formalization is in `Jsp.JSP000584Multi`; this file is the simple-graph
specialisation, kept because it is stated directly in `mathlib`'s `SimpleGraph`
API.

The algebraic content lives in `Jsp.JSP000584Core` (via `mathlib`'s
`char_dvd_card_solutions_of_fintype_sum_lt`); here it is transported to
graphs.  A *3-regular subgraph* is recorded as a nonempty set `S` of edges of
`G` meeting every vertex in either `0` or exactly `3` edges — that is precisely
the edge set of a 3-regular subgraph, supported on the vertices of positive
`S`-degree.
-/

open Finset SimpleGraph

namespace JSP584

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Alon–Friedland–Kalai, `p = 3`.**  A graph of maximum degree at most `5`
with more than `2 * |V|` edges contains a nonempty 3-regular subgraph. -/
theorem exists_three_regular_edge_set
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 5)
    (hcard : 2 * Fintype.card V < G.edgeFinset.card) :
    ∃ S : Finset (Sym2 V), S.Nonempty ∧ S ⊆ G.edgeFinset ∧
      ∀ v : V, (G.incidenceFinset v ∩ S).card = 0 ∨ (G.incidenceFinset v ∩ S).card = 3 := by
  classical
  -- Index the Chevalley–Warning variables by the edges of `G`.
  let inc : V → Finset ↥G.edgeFinset := fun v => Finset.univ.filter fun e => v ∈ (e : Sym2 V)
  have hE : Fintype.card ↥G.edgeFinset = G.edgeFinset.card := Fintype.card_coe _
  obtain ⟨T, hTne, hT⟩ :=
    exists_nonempty_inter_card_mod_three inc (by rw [hE]; exact hcard)
  refine ⟨T.image Subtype.val, ?_, ?_, ?_⟩
  · exact hTne.image _
  · intro e he
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
    exact t.2
  · -- Transport each incidence count along the injection `Subtype.val`.
    intro v
    have bridge : (G.incidenceFinset v ∩ T.image Subtype.val).card = (inc v ∩ T).card := by
      rw [← Finset.card_image_of_injective (inc v ∩ T) Subtype.val_injective]
      congr 1
      ext e
      simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.incidenceFinset_eq_filter, inc]
      constructor
      · rintro ⟨⟨he, hve⟩, t, ht, rfl⟩
        exact ⟨t, ⟨hve, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hve, ht⟩, rfl⟩
        exact ⟨⟨t.2, hve⟩, t, ht, rfl⟩
    -- The count is a multiple of three and at most the degree, hence `0` or `3`.
    have hmod : (G.incidenceFinset v ∩ T.image Subtype.val).card % 3 = 0 := by
      rw [bridge]; exact hT v
    have hle : (G.incidenceFinset v ∩ T.image Subtype.val).card ≤ 5 := by
      refine le_trans (Finset.card_le_card Finset.inter_subset_left) ?_
      rw [SimpleGraph.card_incidenceFinset_eq_degree]
      exact hdeg v
    omega

section AddEdge

variable {s t : V}

omit [DecidableEq V] in
/-- A single added edge contributes at most one to any degree. -/
theorem degree_edge_le_one (v : V) [DecidableRel (SimpleGraph.edge s t).Adj] :
    (SimpleGraph.edge s t).degree v ≤ 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj] at ha hb
  obtain ⟨ha1, -⟩ := ha
  obtain ⟨hb1, -⟩ := hb
  rcases ha1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hb1 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp_all

-- `Fintype (G ⊔ H).edgeSet` is reachable both through `fintypeEdgeSet` and
-- through `fintypeEdgeSetSup`.  Disabling the latter for this declaration keeps
-- a single instance path, so the statement and the proof agree definitionally.
attribute [-instance] SimpleGraph.fintypeEdgeSetSup in
/-- **JSP-000584 (Alon–Friedland–Kalai 1984).**  Every 4-regular graph plus an
edge contains a nonempty 3-regular subgraph. -/
theorem exists_three_regular_of_four_regular_add_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (SimpleGraph.edge s t).Adj]
    (hreg : G.IsRegularOfDegree 4) (hst : s ≠ t) (hns : ¬G.Adj s t) :
    ∃ S : Finset (Sym2 V), S.Nonempty ∧ S ⊆ (G ⊔ SimpleGraph.edge s t).edgeFinset ∧
      ∀ v : V, ((G ⊔ SimpleGraph.edge s t).incidenceFinset v ∩ S).card = 0 ∨
               ((G ⊔ SimpleGraph.edge s t).incidenceFinset v ∩ S).card = 3 := by
  -- maximum degree at most five
  have hdeg : ∀ v, (G ⊔ SimpleGraph.edge s t).degree v ≤ 5 := by
    intro v
    have hsub : (G ⊔ SimpleGraph.edge s t).neighborFinset v
        = G.neighborFinset v ∪ (SimpleGraph.edge s t).neighborFinset v :=
      SimpleGraph.neighborFinset_sup v
    have hun := Finset.card_union_le (G.neighborFinset v) ((SimpleGraph.edge s t).neighborFinset v)
    have h1 : (G.neighborFinset v).card = 4 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg.degree_eq v
    have h2 : ((SimpleGraph.edge s t).neighborFinset v).card ≤ 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact degree_edge_le_one v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hsub]
    omega
  -- The handshake lemma turns 4-regularity into an edge count.  The `Fintype`
  -- instance is taken as a parameter: `Fintype (G ⊔ edge s t).edgeSet` is
  -- reachable both via `fintypeEdgeSet` and via `fintypeEdgeSetSup`, and
  -- generalising lets unification pick whichever the application needs.
  have hcard : ∀ inst : Fintype (G ⊔ SimpleGraph.edge s t).edgeSet,
      2 * Fintype.card V < (@SimpleGraph.edgeFinset V (G ⊔ SimpleGraph.edge s t) inst).card := by
    intro inst
    have hplus : (@SimpleGraph.edgeFinset V (G ⊔ SimpleGraph.edge s t) inst).card
        = G.edgeFinset.card + 1 := G.card_edgeFinset_sup_edge hns hst
    have hshake : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    have hsum : ∑ _v : V, 4 = 4 * Fintype.card V := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
    rw [Finset.sum_congr rfl fun v _ => hreg.degree_eq v, hsum] at hshake
    omega
  exact exists_three_regular_edge_set (G ⊔ SimpleGraph.edge s t) hdeg (hcard _)

/-- The conclusion is not degenerate: a nonempty `S` really forces a vertex of
`S`-degree exactly `3`, so the subgraph produced is genuinely 3-regular and
nonempty. -/
theorem exists_incidence_card_eq_three
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset (Sym2 V)}
    (hne : S.Nonempty) (hsub : S ⊆ G.edgeFinset)
    (h : ∀ v, (G.incidenceFinset v ∩ S).card = 0 ∨ (G.incidenceFinset v ∩ S).card = 3) :
    ∃ v, (G.incidenceFinset v ∩ S).card = 3 := by
  obtain ⟨e, he⟩ := hne
  have heG : e ∈ G.edgeSet := by simpa using hsub he
  induction e using Sym2.ind with
  | h a b =>
    refine ⟨a, (h a).resolve_left fun h0 => ?_⟩
    have hmem : s(a, b) ∈ G.incidenceFinset a ∩ S := by
      rw [Finset.mem_inter, SimpleGraph.mem_incidenceFinset]
      exact ⟨⟨heG, Sym2.mem_mk_left a b⟩, he⟩
    exact Finset.card_ne_zero_of_mem hmem h0

/-- Instance-free restatement.  `edgeFinset` and `incidenceFinset` each carry a
`Fintype` argument that can be synthesised by more than one route, which makes
the form above awkward to apply with `exact`.  Phrasing the conclusion with
`edgeSet` membership and a plain `Finset.filter` removes every such argument. -/
theorem exists_three_regular_of_four_regular_add_edge'
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 4) (hst : s ≠ t) (hns : ¬G.Adj s t) :
    ∃ S : Finset (Sym2 V), S.Nonempty ∧ (∀ e ∈ S, e ∈ (G ⊔ SimpleGraph.edge s t).edgeSet) ∧
      ∀ v : V, (S.filter fun e => v ∈ e).card = 0 ∨ (S.filter fun e => v ∈ e).card = 3 := by
  classical
  obtain ⟨S, hS, hsub, h⟩ := exists_three_regular_of_four_regular_add_edge G hreg hst hns
  refine ⟨S, hS, fun e he => by simpa using hsub he, fun v => ?_⟩
  have key : (G ⊔ SimpleGraph.edge s t).incidenceFinset v ∩ S = S.filter fun e => v ∈ e := by
    ext e
    rw [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_incidenceFinset]
    constructor
    · rintro ⟨⟨-, hv⟩, hmem⟩; exact ⟨hmem, hv⟩
    · rintro ⟨hmem, hv⟩; exact ⟨⟨by simpa using hsub hmem, hv⟩, hmem⟩
  have hv := h v
  rwa [key] at hv

end AddEdge

end JSP584
