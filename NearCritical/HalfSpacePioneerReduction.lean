module

public import NearCritical.HalfSpaceLastVisitBK
public import NearCritical.HalfSpaceTranslation

/-! Exact source pioneer reduction in the new half-space argument. All
quantities are actual infinite-law probabilities and extended nonnegative sums. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Source theta^H_n, with H_{-n}={height>=n}. -/
def halfSpaceArmProbability {d : ℕ} (p : unitInterval) (i : Fin d) (n : ℤ) : ℝ≥0∞ :=
  percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {z | n ≤ z i})

/-- Source psi_p(H_m): boundary connection mass in H_m={height>=-m}.
The definition is a genuine nonnegative sum, without a finiteness assumption. -/
def halfSpacePioneerMass {d : ℕ} (p : unitInterval) (i : Fin d) (m : ℤ) : ℝ≥0∞ :=
  ∑' u : Vertex d, if u i = -m then
    percolation d p (connectionToSetEvent {z | -m ≤ z i} 0 {u}) else 0

/-- Translate each prefix by its endpoint and reverse the connection; then
reindex u→-u to obtain the literal pioneer sum. -/
theorem halfSpace_prefix_sum {d : ℕ} (p : unitInterval) (i : Fin d) (l : ℤ) :
    (∑' u : Vertex d, if u i = l then
      percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {u}) else 0) =
      halfSpacePioneerMass p i l := by
  rw [← (Equiv.neg (Vertex d)).tsum_eq]
  unfold halfSpacePioneerMass
  apply tsum_congr
  intro u
  simp only [Equiv.neg_apply]
  have hcond : (-u) i = l ↔ u i = -l := by
    change -u i = l ↔ u i = -l
    omega
  by_cases hu : u i = -l
  · rw [ite_eq_left (hcond.mpr hu), ite_eq_left hu]
    simpa only [Pi.neg_apply, neg_neg, hu] using halfSpace_prefix_probability p i (-u)
  · simp only [ite_eq_right (mt hcond.mp hu), ite_eq_right hu]

/-- Source Step1's new probability product reduction, before applying cited
pioneer and critical-arm bounds. No product estimate is assumed as a premise. -/
theorem halfSpace_arm_le_pioneer_mul {d : ℕ} (p : unitInterval) (i : Fin d)
    (l n : ℤ) (hl : 0 ≤ l) (hln : l ≤ n) :
    halfSpaceArmProbability p i n ≤
      halfSpacePioneerMass p i l * halfSpaceArmProbability p i (n - l) := by
  calc
    _ ≤ ∑' u : Vertex d, if u i = l then
        percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {u}) *
          percolation d p (connectionToSetEvent {z | l ≤ z i} u {z | n ≤ z i})
        else 0 := halfSpace_arm_last_height_bk p i 0 l n 0 hl hl hln
    _ = (∑' u : Vertex d, if u i = l then
        percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {u}) else 0) *
        halfSpaceArmProbability p i (n - l) := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro u
      by_cases hu : u i = l
      · rw [ite_eq_left hu, ite_eq_left hu, halfSpace_suffix_probability p i l n u hu]
        rfl
      · simp only [ite_eq_right hu, zero_mul]
    _ = _ := by rw [halfSpace_prefix_sum]

end NearCritical
