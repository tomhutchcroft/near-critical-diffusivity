module

public import NearCritical.TwoPhaseSlab

/-! The truncated height distance loses at most one unit across a physical
nearest-neighbor edge. This loss is retained in the weighted Russo bound. -/
@[expose] public section
noncomputable section
namespace NearCritical

lemma twoPhaseSlabDistance_nearby_le_one (m a b : ℤ)
    (hab : a ≤ b+1 ∧ b ≤ a+1) : twoPhaseSlabDistance m a b ≤ 1 := by
  have ha : (a-m).toNat ≤ (b-m).toNat+1 := by omega
  have hb : (b-m).toNat ≤ (a-m).toNat+1 := by omega
  have haR : ((a-m).toNat : ℝ) ≤ ((b-m).toNat : ℝ)+1 := by exact_mod_cast ha
  have hbR : ((b-m).toNat : ℝ) ≤ ((a-m).toNat : ℝ)+1 := by exact_mod_cast hb
  unfold twoPhaseSlabDistance
  apply abs_le.mpr
  constructor <;> linarith

/-- Two connection factors may use opposite endpoints of the tested edge.
The usual triangle inequality therefore has an explicit one-unit loss. -/
lemma twoPhaseSlabDistance_cross_edge (m k j a b : ℤ)
    (hab : a ≤ b+1 ∧ b ≤ a+1) :
    twoPhaseSlabDistance m k j ≤
      twoPhaseSlabDistance m k a + twoPhaseSlabDistance m b j + 1 := by
  have h1 := twoPhaseSlabDistance_triangle m k j a
  have h2 := twoPhaseSlabDistance_triangle m a j b
  have h3 := twoPhaseSlabDistance_nearby_le_one m a b hab
  linarith

/-- The source exponential gauge pays exp(c) across either physical
orientation when its square-root gap is in [0,1]. -/
lemma twoPhaseSlabDistance_weighted_edge_bound (m k j a b : ℤ)
    (hab : a ≤ b+1 ∧ b ≤ a+1) {c s : ℝ}
    (hc : 0 ≤ c) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (c*s*twoPhaseSlabDistance m k j) *
      (Real.exp (-c*s*twoPhaseSlabDistance m k a) *
        Real.exp (-c*s*twoPhaseSlabDistance m b j)) ≤ Real.exp c := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (twoPhaseSlabDistance_cross_edge m k j a b hab)
    (mul_nonneg hc hs0)
  have hcs := mul_le_mul_of_nonneg_left hs1 hc
  nlinarith

end NearCritical
