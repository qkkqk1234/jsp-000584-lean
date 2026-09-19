/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP584.Simple
import JSP584.Multigraph

/-!
# JSP-000584 — audit

Axiom audit, plus a machine-checked witness showing the hypotheses of the
simple-graph corollary are satisfiable, so the statement is not vacuous.
-/

open SimpleGraph

namespace JSP584Audit

/-- The octahedron `K_{2,2,2}` on `Fin 6`: `a ~ b` iff `a % 3 ≠ b % 3`.
It is 4-regular and has non-adjacent vertices, e.g. `0` and `3`. -/
def Oct : SimpleGraph (Fin 6) where
  Adj a b := (a : ℕ) % 3 ≠ (b : ℕ) % 3
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel Oct.Adj := fun a b => inferInstanceAs (Decidable ((a:ℕ) % 3 ≠ (b:ℕ) % 3))

/-! Smallest possible witness: no 4-regular simple graph exists on `≤ 4` vertices,
and on `5` vertices the only one is `K₅`, which has no non-adjacent pair. -/

theorem oct_regular : Oct.IsRegularOfDegree 4 := by
  unfold SimpleGraph.IsRegularOfDegree
  decide

theorem oct_nonadj : ¬ Oct.Adj 0 3 := by decide

theorem oct_ne : (0 : Fin 6) ≠ 3 := by decide

/-- The hypotheses are satisfiable, so `exists_three_regular_of_four_regular_add_edge`
is not vacuously true. -/
theorem witness :
    ∃ S : Finset (Sym2 (Fin 6)), S.Nonempty ∧
      (∀ e ∈ S, e ∈ (Oct ⊔ SimpleGraph.edge 0 3).edgeSet) ∧
      ∀ v : Fin 6, (S.filter fun e => v ∈ e).card = 0 ∨ (S.filter fun e => v ∈ e).card = 3 :=
  JSP584.exists_three_regular_of_four_regular_add_edge' Oct oct_regular oct_ne oct_nonadj

end JSP584Audit

-- Core (Chevalley–Warning)
#print axioms JSP584.sq_eq_indicator
#print axioms JSP584.exists_nonempty_inter_card_mod_three

-- Multigraph: the faithful Alon–Friedland–Kalai statement
#print axioms JSP584.exists_three_regular_multigraph
#print axioms JSP584.sum_mdeg_eq_twice
#print axioms JSP584.exists_three_regular_multigraph_type45
#print axioms JSP584.exists_three_regular_of_four_regular_multigraph_add_edge

-- Simple graphs: specialisation
#print axioms JSP584.exists_three_regular_edge_set
#print axioms JSP584.exists_three_regular_of_four_regular_add_edge
#print axioms JSP584.exists_three_regular_of_four_regular_add_edge'
#print axioms JSP584.exists_incidence_card_eq_three

-- Non-vacuity witness
#print axioms JSP584Audit.witness
