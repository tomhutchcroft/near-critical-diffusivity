module
public import NearCritical.Section8EnergyKernelIdentity
public import NearCritical.Section8SourceFRD

/-! RD inputs for the actual ERE weights in the natural-power variance API. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance Set MeasureTheory
open scoped Classical BigOperators

private theorem variance_scale_power (E n : ℕ) :
    (n : ℝ)^((4 : ℝ)-((E+7 : ℕ) : ℝ)) = 1/(n : ℝ)^(E+3) := by
  have he : (4 : ℝ)-((E+7 : ℕ) : ℝ) = -((E+3 : ℕ) : ℝ) := by push_cast; ring
  rw [he,Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_natCast,one_div]

/-- The actual ERE1 weighted annulus sum supplies the capstone's RD denominator. -/
theorem energy1_RD_capstone_input {E : ℕ} (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper (E+7) C)
    (arm : ∀ j : Fin (E+7), HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin (E+7), SlabBoundarySecondMomentUpper j B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n c r : ℕ, 1 ≤ n → 5*c ≤ n → 1 ≤ r →
      ∀ x w : Vertex (E+7), x ∈ cubeBoundary n → w ∈ sourceRD n c →
      (∑ y ∈ (cube n : Finset (Vertex (E+7))),
        energyOneWeight (cube (3*n/4)) r x y *
          (percolation (E+7) (criticalPoint (E+7))).real
            (connectionToSetEvent
              (heartAnnulus (centeredBox (E+7) n) (centeredBox (E+7) c) : Set (Vertex (E+7))) w {y})) ≤
        K*((sourceR c w : ℝ)+1)/((n : ℝ)^(E+3)*(sParam c w : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := source_F1_RD_upper (k := E+6) (by omega) C A B hC hA hB panis arm second
  refine ⟨K,hK,?_⟩
  intro n c r hn hcn hr x w hx hw
  rw [energyOneWeight_sum_eq_literal (by omega : 2 ≤ E+7)]
  rw [← sourceAnnulus_eq_heartAnnulus (E+6) n c]
  have hh := hbound n c r hn hcn hr x w hx hw
  rw [variance_scale_power E n] at hh
  convert hh using 1 <;> ring

/-- The actual ERE2 weighted annulus sum supplies the capstone's RD denominator. -/
theorem energy2_RD_capstone_input {E : ℕ} (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper (E+7) C)
    (arm : ∀ j : Fin (E+7), HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin (E+7), SlabBoundarySecondMomentUpper j B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n c r : ℕ, 1 ≤ n → 5*c ≤ n → 1 ≤ r →
      ∀ x w : Vertex (E+7), x ∈ cubeBoundary n → w ∈ sourceRD n c →
      (∑ y ∈ (cube n : Finset (Vertex (E+7))),
        energyTwoWeight (cubeBoundary n) r x y *
          (percolation (E+7) (criticalPoint (E+7))).real
            (connectionToSetEvent
              (heartAnnulus (centeredBox (E+7) n) (centeredBox (E+7) c) : Set (Vertex (E+7))) w {y})) ≤
        K*((sourceR c w : ℝ)+1)/((n : ℝ)^(E+3)*(sParam c w : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := source_F2_RD_upper (k := E+6) (by omega) C A B hC hA hB panis arm second
  refine ⟨K,hK,?_⟩
  intro n c r hn hcn hr x w hx hw
  rw [energyTwoWeight_sum_eq_literal (by omega : 4 ≤ E+7)]
  rw [← sourceAnnulus_eq_heartAnnulus (E+6) n c]
  have hh := hbound n c r hn hcn hr x w hx hw
  rw [variance_scale_power E n] at hh
  convert hh using 1 <;> ring

end NearCritical.Section8
