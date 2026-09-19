/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Mathlib
import JSP584.Core

/-!
# JSP-000584 — Alon–Friedland–Kalai for loopless multigraphs

Alon–Friedland–Kalai, *Every 4-regular graph plus an edge contains a 3-regular
subgraph*, J. Combin. Theory Ser. B **37** (1984), 92–93.

The companion paper (*Regular subgraphs of almost regular graphs*, JCTB **37**
(1984), 79–91) states on p. 79 that "all graphs considered are finite,
undirected, and contain no loops… Note that we **allow multiple edges**", and on
p. 80 that the "plus one edge" hypothesis cannot be dropped, the obstruction
being an odd cycle with every edge doubled.  Multiple edges are therefore
essential to the statement, and this file works with loopless multigraphs.

A multigraph is modelled by its incidence map `ends : E → Sym2 V` sending each
edge to its unordered pair of endpoints; looplessness is `¬ (ends e).IsDiag`.
Parallel edges are exactly distinct `e₁ ≠ e₂` with `ends e₁ = ends e₂`, which
this model permits.

A *3-regular subgraph* is recorded as a nonempty set `S` of edges meeting every
vertex in `0` or exactly `3` edges; see `Jsp.JSP000584` for why this is the
same thing as a 3-regular subgraph.
-/

open Finset

-- `[Fintype V]` does not appear in the *types* below (degrees are counts over `E`),
-- but the handshake argument sums over `V`, so the hypothesis is genuinely used.
set_option linter.unusedFintypeInType false

namespace JSP584

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Degree of `v` in the multigraph `ends`. -/
abbrev mdeg (ends : E → Sym2 V) (v : V) : ℕ := (univ.filter fun e => v ∈ ends e).card

/-- Degree of `v` inside a chosen edge set `S`. -/
abbrev mdegOn (ends : E → Sym2 V) (S : Finset E) (v : V) : ℕ := (S.filter fun e => v ∈ ends e).card

/-- **Alon–Friedland–Kalai, `p = 3`, multigraph form.**  A loopless multigraph of
maximum degree at most `5` with more than `2 * |V|` edges contains a nonempty
3-regular subgraph. -/
theorem exists_three_regular_multigraph (ends : E → Sym2 V)
    (hdeg : ∀ v, mdeg ends v ≤ 5) (hcard : 2 * Fintype.card V < Fintype.card E) :
    ∃ S : Finset E, S.Nonempty ∧ ∀ v, mdegOn ends S v = 0 ∨ mdegOn ends S v = 3 := by
  classical
  obtain ⟨S, hS, h⟩ :=
    exists_nonempty_inter_card_mod_three (fun v => univ.filter fun e => v ∈ ends e) hcard
  refine ⟨S, hS, fun v => ?_⟩
  -- state everything on the *same* syntactic term so `omega` sees one atom
  have h2 : ((univ.filter fun e => v ∈ ends e) ∩ S) = S.filter fun e => v ∈ ends e := by
    ext e; simp [and_comm]
  have h1 : (S.filter fun e => v ∈ ends e).card % 3 = 0 := by rw [← h2]; exact h v
  have h3 : (S.filter fun e => v ∈ ends e).card ≤ 5 :=
    le_trans (card_le_card (monotone_filter_left _ (subset_univ S))) (hdeg v)
  change (S.filter fun e => v ∈ ends e).card = 0 ∨ (S.filter fun e => v ∈ ends e).card = 3
  omega

/-- Handshake lemma for the incidence model: a loopless edge has two endpoints. -/
theorem sum_mdeg_eq_twice (ends : E → Sym2 V) (hnd : ∀ e, ¬ (ends e).IsDiag) :
    ∑ v, mdeg ends v = 2 * Fintype.card E := by
  classical
  calc ∑ v, mdeg ends v = ∑ v, ∑ e, if v ∈ ends e then 1 else 0 :=
        Finset.sum_congr rfl fun v _ => card_filter _ _
    _ = ∑ e, ∑ v, if v ∈ ends e then 1 else 0 := Finset.sum_comm
    _ = ∑ _e : E, 2 := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← card_filter]
        have hne := hnd e
        revert hne
        refine Sym2.ind (fun a b hab => ?_) (ends e)
        rw [Sym2.mk_isDiag_iff] at hab
        have hpair : (univ.filter fun v => v ∈ s(a, b)) = {a, b} := by ext v; simp [Sym2.mem_iff]
        rw [hpair, card_pair hab]
    _ = 2 * Fintype.card E := by
        rw [Finset.sum_const, card_univ, smul_eq_mul, Nat.mul_comm]

/-- **AFK (1.1), general form.**  A loopless multigraph whose degrees are all `4`
or `5`, with at least one vertex of degree `5`, contains a 3-regular subgraph. -/
theorem exists_three_regular_multigraph_type45 (ends : E → Sym2 V)
    (hnd : ∀ e, ¬ (ends e).IsDiag)
    (hlo : ∀ v, 4 ≤ mdeg ends v) (hhi : ∀ v, mdeg ends v ≤ 5)
    (hex : ∃ v, mdeg ends v = 5) :
    ∃ S : Finset E, S.Nonempty ∧ ∀ v, mdegOn ends S v = 0 ∨ mdegOn ends S v = 3 := by
  classical
  refine exists_three_regular_multigraph ends hhi ?_
  have hsum := sum_mdeg_eq_twice ends hnd
  obtain ⟨w, hw⟩ := hex
  have h4 : ∑ _v : V, (4 : ℕ) = 4 * Fintype.card V := by
    rw [Finset.sum_const, card_univ, smul_eq_mul, Nat.mul_comm]
  have hlt : ∑ _v : V, (4 : ℕ) < ∑ v, mdeg ends v :=
    Finset.sum_lt_sum (fun v _ => hlo v) ⟨w, mem_univ _, by omega⟩
  omega

/-- Adding one edge `s(a, b)` is modelled by extending the index type by `Unit`. -/
abbrev addEdge (ends : E → Sym2 V) (a b : V) : E ⊕ Unit → Sym2 V :=
  Sum.elim ends fun _ => s(a, b)

omit [Fintype V] in
theorem mdeg_addEdge (ends : E → Sym2 V) (a b : V) (v : V) :
    mdeg (addEdge ends a b) v = mdeg ends v + (if v ∈ s(a, b) then 1 else 0) := by
  classical
  simp only [mdeg, card_filter, Fintype.sum_sum_type, addEdge, Sum.elim_inl, Sum.elim_inr]
  congr 1


/-- **JSP-000584, exactly as the paper states it.**  Every 4-regular loopless
multigraph plus one edge contains a nonempty 3-regular subgraph. -/
theorem exists_three_regular_of_four_regular_multigraph_add_edge
    (ends : E → Sym2 V) (hnd : ∀ e, ¬ (ends e).IsDiag)
    (hreg : ∀ v, mdeg ends v = 4) {a b : V} (hab : a ≠ b) :
    ∃ S : Finset (E ⊕ Unit), S.Nonempty ∧
      ∀ v, mdegOn (addEdge ends a b) S v = 0 ∨ mdegOn (addEdge ends a b) S v = 3 := by
  classical
  refine exists_three_regular_multigraph_type45 (addEdge ends a b) ?_ ?_ ?_ ⟨a, ?_⟩
  · rintro (e | ⟨⟩)
    · exact hnd e
    · simpa [addEdge, Sym2.mk_isDiag_iff] using hab
  · intro v; rw [mdeg_addEdge, hreg v]; split <;> omega
  · intro v; rw [mdeg_addEdge, hreg v]; split <;> omega
  · rw [mdeg_addEdge, hreg a]; simp

end JSP584
