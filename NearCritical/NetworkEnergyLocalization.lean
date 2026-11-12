module

public import NearCritical.NetworkPivotal

/-! Quenched two-face energy localization on old-configuration two-arm events,
the consequence following lem.two_arm (the relaxed-domain version of the
localization discussed in eq.intro.step2).
Every boundary-access premise is discharged from a positive edge's nonzero
harmonic voltage drop. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open Set Finset
open scoped Classical
variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

theorem IsHarmonic.energyTerm_eq_zero_of_not_two_arm {a : E → ℝ} {u : V → ℝ}
    {low high : Set V} {lo hi : ℝ} (hu : G.IsHarmonic a (low ∪ high) u)
    (ha : ∀ e, 0 ≤ a e) (hlohi : lo ≤ hi)
    (hlow : ∀ v ∈ low, u v = lo) (hhigh : ∀ v ∈ high, u v = hi) (e : E)
    (hn : ¬(G.DisjointBoundaryConnections a (G.tail e) low (G.head e) high ∨
      G.DisjointBoundaryConnections a (G.tail e) high (G.head e) low)) :
    a e * (G.gradient u e) ^ 2 = 0 := by
  by_cases he : a e = 0
  · simp [he]
  by_cases hg : G.gradient u e = 0
  · simp [hg]
  have hpos : 0 < a e := lt_of_le_of_ne (ha e) (Ne.symm he)
  have hpaths := hu.edge_nonzero_both_reach_boundary G ha e hpos hg
  have hne : u (G.tail e) ≠ u (G.head e) := by
    intro h
    exact hg (by simp [gradient, h])
  exact False.elim (hn (hu.two_arm G ha hlohi hlow hhigh hpaths.1 hpaths.2 hne))

/-- For any harmonic potential with two constant Dirichlet faces, the full
energy is supported on old-configuration opposite-face disjoint connections. -/
theorem IsHarmonic.energy_localized {a : E → ℝ} {u : V → ℝ}
    {low high : Set V} {lo hi : ℝ} (hu : G.IsHarmonic a (low ∪ high) u)
    (ha : ∀ e, 0 ≤ a e) (hlohi : lo ≤ hi)
    (hlow : ∀ v ∈ low, u v = lo) (hhigh : ∀ v ∈ high, u v = hi) :
    G.energy a u = ∑ e, a e * (G.gradient u e) ^ 2 *
      (if G.DisjointBoundaryConnections a (G.tail e) low (G.head e) high ∨
          G.DisjointBoundaryConnections a (G.tail e) high (G.head e) low then 1 else 0) := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : G.DisjointBoundaryConnections a (G.tail e) low (G.head e) high ∨
      G.DisjointBoundaryConnections a (G.tail e) high (G.head e) low
  · simp [ht]
  · rw [hu.energyTerm_eq_zero_of_not_two_arm G ha hlohi hlow hhigh e ht]
    simp

/-- Binary version for any minimizer of the source's two-face Dirichlet data. -/
theorem IsMinimizer.binary_energy_localized {low high : Set V} {data u : V → ℝ}
    {lo hi : ℝ} (η : E → Bool)
    (hu : G.IsMinimizer (binaryWeights η) (low ∪ high) data u)
    (hlohi : lo ≤ hi) (hlow : ∀ v ∈ low, data v = lo) (hhigh : ∀ v ∈ high, data v = hi) :
    G.energy (binaryWeights η) u = ∑ e, binaryWeights η e * (G.gradient u e) ^ 2 *
      (if G.binaryTwoArm low high η e then 1 else 0) := by
  have hlow_u : ∀ v ∈ low, u v = lo := by
    intro v hv
    exact (hu.1 v (Or.inl hv)).trans (hlow v hv)
  have hhigh_u : ∀ v ∈ high, u v = hi := by
    intro v hv
    exact (hu.1 v (Or.inr hv)).trans (hhigh v hv)
  refine ((hu.isHarmonic G).energy_localized G (binaryWeights_nonneg η)
    hlohi hlow_u hhigh_u).trans ?_
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : G.DisjointBoundaryConnections (binaryWeights η) (G.tail e) low (G.head e) high ∨
      G.DisjointBoundaryConnections (binaryWeights η) (G.tail e) high (G.head e) low
  · have hb : G.binaryTwoArm low high η e := ht
    simp only [ite_eq_left ht, ite_eq_left hb]
  · have hb : ¬G.binaryTwoArm low high η e := ht
    simp only [ite_eq_right ht, ite_eq_right hb]

/-- The localized sum equals the actual variational conductance, for every
same-data minimizer; no canonical-selection premise is required. -/
theorem IsMinimizer.binaryConductance_eq_localized_energy {low high : Set V} {data u : V → ℝ}
    {lo hi : ℝ} (η : E → Bool)
    (hu : G.IsMinimizer (binaryWeights η) (low ∪ high) data u)
    (hlohi : lo ≤ hi) (hlow : ∀ v ∈ low, data v = lo) (hhigh : ∀ v ∈ high, data v = hi) :
    G.binaryConductance (low ∪ high) data η =
      ∑ e, binaryWeights η e * (G.gradient u e) ^ 2 *
        (if G.binaryTwoArm low high η e then 1 else 0) := by
  rw [binaryConductance, hu.conductance_eq G (binaryWeights_nonneg η)]
  exact hu.binary_energy_localized G η hlohi hlow hhigh

/-- Selected-minimizer form used directly by the finite expectation calculus. -/
theorem binaryConductance_localized [Fintype V] {low high : Set V} {data : V → ℝ}
    {lo hi : ℝ} (hlohi : lo ≤ hi) (hlow : ∀ v ∈ low, data v = lo)
    (hhigh : ∀ v ∈ high, data v = hi) (η : E → Bool) :
    G.binaryConductance (low ∪ high) data η =
      ∑ e, binaryWeights η e *
        (G.gradient (G.binaryMinimizer (low ∪ high) data η) e) ^ 2 *
        (if G.binaryTwoArm low high η e then 1 else 0) :=
  (G.binaryMinimizer_spec (low ∪ high) data η).binaryConductance_eq_localized_energy
    G η hlohi hlow hhigh

/-- A uniform voltage-gradient bound converts localized energy into a count
of old-configuration two-arm edges. This is the deterministic part of the aa
estimate; no probability or high-dimensional estimate is assumed here. -/
theorem IsMinimizer.binaryConductance_le_twoArm_count {low high : Set V} {data u : V → ℝ}
    {lo hi : ℝ} (η : E → Bool)
    (hu : G.IsMinimizer (binaryWeights η) (low ∪ high) data u)
    (hlohi : lo ≤ hi) (hlow : ∀ v ∈ low, data v = lo) (hhigh : ∀ v ∈ high, data v = hi)
    (H : ℝ) (hgrad : ∀ e, |G.gradient u e| ≤ H) :
    G.binaryConductance (low ∪ high) data η ≤
      H ^ 2 * ∑ e, (if G.binaryTwoArm low high η e then (1 : ℝ) else 0) := by
  rw [hu.binaryConductance_eq_localized_energy G η hlohi hlow hhigh, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases ht : G.binaryTwoArm low high η e
  · simp only [ite_eq_left ht, mul_one]
    calc
      binaryWeights η e * (G.gradient u e) ^ 2 ≤ (G.gradient u e) ^ 2 := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (binaryWeights_le_one η e) (sq_nonneg (G.gradient u e))
      _ ≤ H ^ 2 := sq_le_sq.mpr ((hgrad e).trans (le_abs_self H))
  · simp only [ite_eq_right ht, mul_zero]
    exact le_rfl

/-- Selected-minimizer version for the finite expectation upper-bound calculus. -/
theorem binaryConductance_le_twoArm_count [Fintype V] {low high : Set V} {data : V → ℝ}
    {lo hi : ℝ} (hlohi : lo ≤ hi) (hlow : ∀ v ∈ low, data v = lo)
    (hhigh : ∀ v ∈ high, data v = hi) (η : E → Bool) (H : ℝ)
    (hgrad : ∀ e, |G.gradient (G.binaryMinimizer (low ∪ high) data η) e| ≤ H) :
    G.binaryConductance (low ∪ high) data η ≤
      H ^ 2 * ∑ e, (if G.binaryTwoArm low high η e then (1 : ℝ) else 0) :=
  (G.binaryMinimizer_spec (low ∪ high) data η).binaryConductance_le_twoArm_count
    G η hlohi hlow hhigh H hgrad

end NearCritical.Network
