module

public import NearCritical.ProfileLowDensityBK
public import NearCritical.ProfileORParameter
public import NearCritical.ProfileORProjection
public import NearCritical.ORDisjointOccurrence

/-! Finite profile BK under a common upper rate strictly below one.
The two probabilities on the right are both under the original profile. -/
@[expose] public section
noncomputable section
namespace NearCritical.BK
open Set MeasureTheory ProbabilityTheory

/-- Finite BK for rates under any uniform P<1. The endpoint-one case and
infinite-coordinate extension are separate obligations. -/
theorem finite_bernoulliProfile_bk_of_uniform_lt_one {E : Type*} [Fintype E]
    (r : E → unitInterval) (P : unitInterval) (hP : (P : ℝ) < 1)
    (hr : ∀ e, r e ≤ P) (A B : Set (E → Bool))
    (hA : Increasing A) (hB : Increasing B) :
    (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real (occurrenceEvent A B) ≤
      (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real A *
        (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real B := by
  classical
  obtain ⟨m, _hm, q, hq⟩ := exists_common_or_parameters r P hP hr
  let μ := Measure.pi (fun ej : E × Fin m ↦ bernoulliMeasure true false (q ej.1))
  have hsub := orProject_preimage_occurrence_subset m hA hB
  have hmono : μ.real ((orProject m) ⁻¹' occurrenceEvent A B) ≤
      μ.real (occurrenceEvent ((orProject m) ⁻¹' A) ((orProject m) ⁻¹' B)) :=
    measureReal_mono hsub (measure_ne_top μ _)
  have hBK := finite_bernoulliProfile_bk_le_half (fun ej : E × Fin m ↦ q ej.1)
    (fun ej ↦ (hq ej.1).1) ((orProject m) ⁻¹' A) ((orProject m) ⁻¹' B)
    (increasing_preimage_orProject m hA) (increasing_preimage_orProject m hB)
  have h := hmono.trans hBK
  change (Measure.pi (fun ej : E × Fin m ↦ bernoulliMeasure true false (q ej.1))).real
      ((orProject m) ⁻¹' occurrenceEvent A B) ≤ _ at h
  rw [measureReal_orProject_profile m r q (fun e ↦ (hq e).2),
    measureReal_orProject_profile m r q (fun e ↦ (hq e).2),
    measureReal_orProject_profile m r q (fun e ↦ (hq e).2)] at h
  exact h

end NearCritical.BK
