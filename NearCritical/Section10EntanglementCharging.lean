module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-! Section10 lem.nw.overlap: deterministic edge charging to intersecting local
pieces. Actual cube/tube/exit geometry must instantiate the raw piece data. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
variable {E I : Type*} [Fintype I]

/-- The indices of local pieces that actually share a physical edge. -/
def intersectingPieceIndices (P Q : I → Finset E) : Finset I :=
  Finset.univ.filter (fun i => (P i ∩ Q i).Nonempty)

/-- Distinct cube/tube blocks cannot create a common edge. Hence every common
edge of paths covered by the pieces belongs to a matching intersecting pair. -/
theorem common_edges_subset_matching_pieces (γ γ' : Finset E) (P Q : I → Finset E)
    (hγ : γ ⊆ Finset.univ.biUnion P) (hγ' : γ' ⊆ Finset.univ.biUnion Q)
    (hcross : ∀ i j, i ≠ j → Disjoint (P i) (Q j)) :
    γ ∩ γ' ⊆ (intersectingPieceIndices P Q).biUnion (fun i => P i ∩ Q i) := by
  intro e he
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (hγ (Finset.mem_inter.mp he).1)
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (hγ' (Finset.mem_inter.mp he).2)
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hcross i j hne) hi hj
  subst j
  have hePQ : e ∈ P i ∩ Q i := Finset.mem_inter.mpr ⟨hi,hj⟩
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨e,hePQ⟩⟩,hePQ⟩

/-- Charging requires no disjointness between matching intersections: summing
piece cardinalities is an upper bound even if a common edge is charged twice. -/
theorem common_edges_card_le_matching_sum (γ γ' : Finset E) (P Q : I → Finset E)
    (hγ : γ ⊆ Finset.univ.biUnion P) (hγ' : γ' ⊆ Finset.univ.biUnion Q)
    (hcross : ∀ i j, i ≠ j → Disjoint (P i) (Q j)) :
    (γ ∩ γ').card ≤ ∑ i ∈ intersectingPieceIndices P Q, (P i ∩ Q i).card := by
  exact (Finset.card_le_card (common_edges_subset_matching_pieces γ γ' P Q hγ hγ' hcross)).trans
    Finset.card_biUnion_le

/-- Uniform local piece budgets give the source form: a length budget times the
number of entanglement locations. The overlap conclusion is derived. -/
theorem common_edges_card_le_budget_times_entanglements (γ γ' : Finset E)
    (P Q : I → Finset E) {B : ℝ}
    (hγ : γ ⊆ Finset.univ.biUnion P) (hγ' : γ' ⊆ Finset.univ.biUnion Q)
    (hcross : ∀ i j, i ≠ j → Disjoint (P i) (Q j))
    (hbudget : ∀ i, ((P i).card:ℝ) ≤ B) :
    ((γ ∩ γ').card:ℝ) ≤ B*((intersectingPieceIndices P Q).card:ℝ) := by
  have hc := common_edges_card_le_matching_sum γ γ' P Q hγ hγ' hcross
  have hcr : ((γ ∩ γ').card:ℝ) ≤
      ∑ i ∈ intersectingPieceIndices P Q, ((P i ∩ Q i).card:ℝ) := by
    exact_mod_cast hc
  calc
    _ ≤ ∑ i ∈ intersectingPieceIndices P Q, ((P i ∩ Q i).card:ℝ) := hcr
    _ ≤ ∑ i ∈ intersectingPieceIndices P Q, B := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (P i ∩ Q i).card ≤ (P i).card :=
        Finset.card_le_card Finset.inter_subset_left
      have hir : ((P i ∩ Q i).card:ℝ) ≤ ((P i).card:ℝ) := by exact_mod_cast hi
      exact hir.trans (hbudget i)
    _ = _ := by simp [mul_comm]

end NearCritical.Section10
