module

public import NearCritical.FiniteTwoPhaseSlabModel
public import NearCritical.TwoPhaseSlabDistanceBounds

/-! Actual geometry of the p-variable mask in the two-phase slab. Membership
is the geometric mask predicate, never inferred from a rate equality. Both
physical endpoints are checked in S_(0,n); no cutoff convexity is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set

/-- Positively indexed lattice bonds increase each coordinate by zero or one. -/
lemma twoPhase_bond_height_step {d : ℕ} (e : Bond d) (i : Fin d) :
    e.1 i ≤ bondTip e i ∧ bondTip e i ≤ e.1 i+1 := by
  by_cases h : i = e.2
  · subst i
    simp [bondTip]
  · simp [bondTip,Function.update_of_ne h]

/-- A geometrically p-variable bond with both endpoints in the actual slab
must start at or below the interface. This includes the p=q case. -/
lemma finiteTwoPhaseVariableMask_base_height_le {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (e : internalBondSet U)
    (he : e ∈ finiteTwoPhaseVariableMask U i m n)
    (hbase : e.val.1 ∈ finiteHeightSlab i 0 n)
    (htip : bondTip e.val ∈ finiteHeightSlab i 0 n) :
    e.val.1 i ≤ m := by
  have hmask := (mem_finiteTwoPhaseVariableMask U i m n e).mp he
  have hstep := (twoPhase_bond_height_step e.val i).1
  change 0 ≤ e.val.1 i ∧ e.val.1 i ≤ n at hbase
  change 0 ≤ bondTip e.val i ∧ bondTip e.val i ≤ n at htip
  by_contra h
  apply hmask
  change (m+1 ≤ e.val.1 i ∧ e.val.1 i ≤ n) ∧
    (m+1 ≤ bondTip e.val i ∧ bondTip e.val i ≤ n)
  exact ⟨⟨by omega,hbase.2⟩,⟨by omega,htip.2⟩⟩

/-- BOTH physical endpoints of a slab-supported p-variable bond lie in the
actual bounded layer range, including interface-crossing bonds. -/
lemma finiteTwoPhaseVariableMask_endpoints_in_lower_slab {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (e : internalBondSet U)
    (he : e ∈ finiteTwoPhaseVariableMask U i m n)
    (hbase : e.val.1 ∈ finiteHeightSlab i 0 n)
    (htip : bondTip e.val ∈ finiteHeightSlab i 0 n) :
    e.val.1 ∈ finiteHeightSlab i 0 (min n (m+1)) ∧
      bondTip e.val ∈ finiteHeightSlab i 0 (min n (m+1)) := by
  have hbaseM := finiteTwoPhaseVariableMask_base_height_le U i m n e he hbase htip
  have hstep := (twoPhase_bond_height_step e.val i).2
  change 0 ≤ e.val.1 i ∧ e.val.1 i ≤ n at hbase
  change 0 ≤ bondTip e.val i ∧ bondTip e.val i ≤ n at htip
  change (0 ≤ e.val.1 i ∧ e.val.1 i ≤ min n (m+1)) ∧
    (0 ≤ bondTip e.val i ∧ bondTip e.val i ≤ min n (m+1))
  exact ⟨⟨hbase.1,le_min hbase.2 (by omega)⟩,
    ⟨htip.1,le_min htip.2 (by omega)⟩⟩

/-- The truncated-distance exponential gauge costs exp(c) across BOTH actual
bond orientations. This is physical nearest-neighbor geometry, independent of
bond openness, mask membership, and the rates assigned to the two phases. -/
lemma twoPhase_bond_weighted_edge_bounds {d : ℕ} (e : Bond d) (i : Fin d)
    (m k j : ℤ) {c s : ℝ} (hc : 0 ≤ c) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (Real.exp (c*s*twoPhaseSlabDistance m k j) *
      (Real.exp (-c*s*twoPhaseSlabDistance m k (e.1 i)) *
        Real.exp (-c*s*twoPhaseSlabDistance m (bondTip e i) j)) ≤ Real.exp c) ∧
    (Real.exp (c*s*twoPhaseSlabDistance m k j) *
      (Real.exp (-c*s*twoPhaseSlabDistance m k (bondTip e i)) *
        Real.exp (-c*s*twoPhaseSlabDistance m (e.1 i) j)) ≤ Real.exp c) := by
  obtain ⟨hmono,hstep⟩ := twoPhase_bond_height_step e i
  have hab : e.1 i ≤ bondTip e i+1 ∧ bondTip e i ≤ e.1 i+1 := ⟨by omega,hstep⟩
  exact ⟨twoPhaseSlabDistance_weighted_edge_bound m k j (e.1 i) (bondTip e i) hab hc hs0 hs1,
    twoPhaseSlabDistance_weighted_edge_bound m k j (bondTip e i) (e.1 i) hab.symm hc hs0 hs1⟩

end NearCritical
