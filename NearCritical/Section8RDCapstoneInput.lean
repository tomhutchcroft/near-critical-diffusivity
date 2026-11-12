module
public import NearCritical.Section8SourceRDEstimate
public import NearCritical.AppendixFRDSums

/-! The actual boundary-to-RD probability input of the variance capstone. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance Set MeasureTheory
open scoped Classical

/-- The capstone's `htxRD`, for the actual retained-boundary annulus probability.
All cited probabilistic inputs remain explicit and the constant precedes the radii. -/
theorem annulus_RD_capstone_input {E : ℕ} (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper (E+7) C)
    (arm : ∀ j : Fin (E+7), HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin (E+7), SlabBoundarySecondMomentUpper j B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n c : ℕ, 1 ≤ n → 5*c ≤ n →
      ∀ x u : Vertex (E+7), x ∈ cubeBoundary n → u ∈ sourceRD n c →
      (percolation (E+7) (criticalPoint (E+7))).real
        (connectionToSetEvent
          (heartAnnulus (centeredBox (E+7) n) (centeredBox (E+7) c) : Set (Vertex (E+7))) u {x}) ≤
        K*((sourceR c u : ℝ)+1)/((n : ℝ)^(E+6)*(sParam c u : ℝ)) := by
  obtain ⟨K,hK,hrd⟩ := source_RD_connection_upper (k := E+6) C A B hC hA hB panis arm second
  refine ⟨K,hK,?_⟩
  intro n c hn hcn x u hx hu
  have hxN : linfDist 0 x = n := (Finset.mem_filter.mp hx).2
  have hxR : latticeDistance 0 x = (n : ℝ) := by
    rw [← linfDist_cast_eq_latticeDistance,hxN]
  have hxAnn : x ∈ sourceAnnulus n c :=
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,by rw [hxN]; omega⟩
  have hout : 3*(n : ℝ)/4 ≤ latticeDistance 0 x := by
    rw [hxR]
    linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hh := hrd n c hn hcn x u hxAnn hu hout
  rw [hxR,sub_self,add_zero,mul_one] at hh
  have he : (1 : ℝ)-((E+7 : ℕ) : ℝ) = -((E+6 : ℕ) : ℝ) := by push_cast; ring
  rw [he,Real.rpow_neg (Nat.cast_nonneg n),Real.rpow_natCast] at hh
  rw [← sourceAnnulus_eq_heartAnnulus (E+6) n c,
    connectionToSetEvent_singleton_symm _ u x]
  convert hh using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

end NearCritical.Section8
