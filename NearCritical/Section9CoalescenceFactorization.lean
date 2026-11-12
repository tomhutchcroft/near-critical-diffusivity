module

public import NearCritical.Section9CoalescenceRestrictedBound
public import NearCritical.Section9CoalescenceMass

@[expose] public section
namespace NearCritical
open scoped Classical

/-- The two pivot sums factor at each fixed branch vertex. The excluded
diagonal can be restored for an upper bound on the nonnegative diagram. -/
theorem section9_case_three_factorization {d : ℕ}
    (P : Finset (Vertex d × Vertex d)) (R B : Finset (Vertex d))
    (a b : (Vertex d × Vertex d) → ℝ)
    (ha : ∀ e ∈ P, 0 ≤ a e) (hb : ∀ e ∈ P, 0 ≤ b e) :
    (∑ ef ∈ (P.product P).filter (fun ef => ef.1 ≠ ef.2),
      a ef.1 * (b ef.2 * ∑ z ∈ B, ∑ u ∈ R,
        section9RightArm R ef.1.2 u * (section9RightArm R u ef.2.2 * section9RightArm R z u))) ≤
    ∑ z ∈ B, ∑ u ∈ R,
      (∑ e ∈ P, a e * section9RightArm R e.2 u) *
      ((∑ f ∈ P, b f * section9RightArm R u f.2) * section9RightArm R z u) := by
  have hArm (v w : Vertex d) : 0 ≤ section9RightArm R v w :=
    MeasureTheory.measureReal_nonneg
  calc
    _ ≤ ∑ ef ∈ P.product P, a ef.1 * (b ef.2 * ∑ z ∈ B, ∑ u ∈ R,
        section9RightArm R ef.1.2 u * (section9RightArm R u ef.2.2 * section9RightArm R z u)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ef hef _
      obtain ⟨he, hf⟩ := Finset.mem_product.mp hef
      exact mul_nonneg (ha _ he) (mul_nonneg (hb _ hf)
        (Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun u _ =>
          mul_nonneg (hArm _ _) (mul_nonneg (hArm _ _) (hArm _ _))))
    _ = ∑ ef ∈ P.product P, ∑ z ∈ B, ∑ u ∈ R,
        (a ef.1 * section9RightArm R ef.1.2 u) *
          ((b ef.2 * section9RightArm R u ef.2.2) * section9RightArm R z u) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ef _ => Finset.sum_congr rfl fun z _ =>
        Finset.sum_congr rfl fun u _ => by ring
    _ = ∑ z ∈ B, ∑ u ∈ R, ∑ ef ∈ P.product P,
        (a ef.1 * section9RightArm R ef.1.2 u) *
          ((b ef.2 * section9RightArm R u ef.2.2) * section9RightArm R z u) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_comm
    _ = _ := by
      simp only [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun u _ => Finset.sum_comm

/-- Quantitative summation after factoring the pivots, separating the
two long-arm estimates from the three finite quadratic masses. -/
theorem section9_factored_diagram_le {d : ℕ}
    (P : Finset (Vertex d × Vertex d)) (R B : Finset (Vertex d))
    (a b : (Vertex d × Vertex d) → ℝ) (A C M N H : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hb : ∀ e ∈ P, 0 ≤ b e)
    (haA : ∀ e ∈ P, a e ≤ A) (hbC : ∀ e ∈ P, b e ≤ C)
    (hMsum : ∀ u ∈ R, ∑ e ∈ P, section9RightArm R e.2 u ≤ M)
    (hNsum : ∀ u ∈ R, ∑ e ∈ P, section9RightArm R u e.2 ≤ N)
    (hHsum : ∀ z ∈ B, ∑ u ∈ R, section9RightArm R z u ≤ H) :
    (∑ z ∈ B, ∑ u ∈ R,
      (∑ e ∈ P, a e * section9RightArm R e.2 u) *
      ((∑ f ∈ P, b f * section9RightArm R u f.2) * section9RightArm R z u)) ≤
        (B.card : ℝ) * ((A * M) * (C * N) * H) := by
  have hArm (v w : Vertex d) : 0 ≤ section9RightArm R v w :=
    MeasureTheory.measureReal_nonneg
  calc
    _ ≤ ∑ z ∈ B, ∑ u ∈ R, ((A * M) * (C * N)) * section9RightArm R z u := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro u hu
      have hleft : (∑ e ∈ P, a e * section9RightArm R e.2 u) ≤ A * M := by
        calc
          _ ≤ ∑ e ∈ P, A * section9RightArm R e.2 u :=
            Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_right (haA e he) (hArm _ _)
          _ ≤ _ := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hMsum u hu) hA
      have hright : (∑ f ∈ P, b f * section9RightArm R u f.2) ≤ C * N := by
        calc
          _ ≤ ∑ f ∈ P, C * section9RightArm R u f.2 :=
            Finset.sum_le_sum fun f hf => mul_le_mul_of_nonneg_right (hbC f hf) (hArm _ _)
          _ ≤ _ := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hNsum u hu) hC
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hleft hright
          (Finset.sum_nonneg fun f hf => mul_nonneg (hb f hf) (hArm _ _))
          (mul_nonneg hA hM)) (hArm _ _)
    _ ≤ ∑ _z ∈ B, ((A * M) * (C * N)) * H := by
      apply Finset.sum_le_sum
      intro z hz
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hHsum z hz) (mul_nonneg (mul_nonneg hA hM) (mul_nonneg hC hN))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end NearCritical
