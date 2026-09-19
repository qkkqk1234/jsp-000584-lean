/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Mathlib

/-!
# JSP-000584 — the Chevalley–Warning core

Abstract heart of Alon–Friedland–Kalai, *Every 4-regular graph plus an edge
contains a 3-regular subgraph* (J. Combin. Theory Ser. B 37 (1984), 92–93).

No graph theory appears here: we only need an incidence assignment
`inc : V → Finset E`.  If there are more than `2 * |V|` edges, then some
nonempty set of edges meets every `inc v` in a multiple of three elements.
-/

open MvPolynomial

namespace JSP584

/-- Squaring in `ZMod 3` is the indicator of being nonzero. -/
theorem sq_eq_indicator (a : ZMod 3) : a ^ 2 = if a ≠ 0 then 1 else 0 := by
  revert a; decide

/-- **Chevalley–Warning core.**  With more than `2 * |V|` edges available, some
nonempty edge set meets every incidence set in a multiple of three elements. -/
theorem exists_nonempty_inter_card_mod_three
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (inc : V → Finset E) (hcard : 2 * Fintype.card V < Fintype.card E) :
    ∃ S : Finset E, S.Nonempty ∧ ∀ v : V, ((inc v) ∩ S).card % 3 = 0 := by
  classical
  -- For each vertex, the quadratic form `∑_{e ∋ v} x_e ^ 2` over `ZMod 3`.
  let f : V → MvPolynomial E (ZMod 3) := fun v => ∑ e ∈ inc v, (X e) ^ 2
  -- Each `f v` has total degree at most two.
  have hdeg : ∀ v, (f v).totalDegree ≤ 2 := by
    intro v
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun e _ => ?_)
    calc (X e ^ 2 : MvPolynomial E (ZMod 3)).totalDegree
        ≤ 2 * (X e : MvPolynomial E (ZMod 3)).totalDegree := totalDegree_pow _ _
      _ ≤ 2 := by simp [totalDegree_X]
  -- Hence the degrees sum to less than the number of variables.
  have hsum : (∑ v, (f v).totalDegree) < Fintype.card E := by
    have hle : (∑ v, (f v).totalDegree) ≤ 2 * Fintype.card V := by
      calc (∑ v, (f v).totalDegree) ≤ ∑ _v : V, 2 := Finset.sum_le_sum fun v _ => hdeg v
        _ = Fintype.card V * 2 := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        _ = 2 * Fintype.card V := Nat.mul_comm _ _
    omega
  -- Chevalley–Warning: the number of common zeros is divisible by three.
  have hdvd := char_dvd_card_solutions_of_fintype_sum_lt (K := ZMod 3) 3 hsum
  -- The all-zero assignment is a common zero, so the solution set is nonempty.
  have hzero : ∀ v : V, eval (fun _ : E => (0 : ZMod 3)) (f v) = 0 := by
    intro v; simp [f]
  have hpos : 0 < Fintype.card { x : E → ZMod 3 // ∀ v, eval x (f v) = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨_, hzero⟩⟩
  -- Divisibility by three plus nonemptiness forces a second, nonzero solution.
  have hthree : 3 ≤ Fintype.card { x : E → ZMod 3 // ∀ v, eval x (f v) = 0 } :=
    Nat.le_of_dvd hpos hdvd
  obtain ⟨⟨x, hx⟩, hne⟩ :=
    Fintype.exists_ne_of_one_lt_card (by omega) (⟨_, hzero⟩ :
      { x : E → ZMod 3 // ∀ v, eval x (f v) = 0 })
  refine ⟨Finset.univ.filter fun e => x e ≠ 0, ?_, ?_⟩
  · -- nonempty, because `x` is not the zero assignment
    rw [Finset.filter_nonempty_iff]
    by_contra hcon
    push Not at hcon
    exact hne (Subtype.ext (funext fun e => hcon e (Finset.mem_univ e)))
  · -- every incidence set meets it in a multiple of three
    intro v
    -- unfold the evaluation into an honest sum of squares
    have hv : ∑ e ∈ inc v, (x e) ^ 2 = 0 := by
      have := hx v
      simpa [f, map_sum] using this
    -- over `ZMod 3` that sum counts the support
    have hfil : (inc v).filter (fun e => x e ≠ 0)
        = inc v ∩ Finset.univ.filter fun e => x e ≠ 0 := by
      ext e; simp
    have step : ((((inc v).filter fun e => x e ≠ 0).card : ℕ) : ZMod 3)
        = ∑ e ∈ inc v, (x e) ^ 2 := by
      rw [← Finset.sum_boole]
      exact (Finset.sum_congr rfl fun e _ => sq_eq_indicator (x e)).symm
    have hcount : (((inc v ∩ Finset.univ.filter fun e => x e ≠ 0).card : ℕ) : ZMod 3) = 0 := by
      rw [← hfil, step, hv]
    have hd : (3 : ℕ) ∣ (inc v ∩ Finset.univ.filter fun e => x e ≠ 0).card :=
      (ZMod.natCast_eq_zero_iff _ 3).mp hcount
    omega

end JSP584
