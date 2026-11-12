module

public import NearCritical.SplitCrossNodeSites
public import NearCritical.SplitCrossSummedOverlap
public import NearCritical.Section10FaceCountUpper

/-! Each far terminal is on the corresponding signed face of the common
envelope. Summing over it costs only the cited face first moment. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 MeasureTheory
open scoped Classical

theorem farLegFaceCore_subset_envelope_face {d t : ℕ} (ht : 64 ≤ t)
    (f : Fin d × Bool) (pl : Bool) :
    farLegFaceCore t f pl ⊆ signedCubeFace d ((t - 1) / 2 + t) f := by
  intro y hy
  have hT := farLegFaceCore_subset_target ht f pl hy
  have ⟨hb, hH⟩ := Finset.mem_filter.mp hT
  have hEnv : y ∈ centeredBox d ((t - 1) / 2 + t) :=
    splitBeyond_subset_splitEnvelope t f pl hb
  apply Finset.mem_filter.mpr
  refine ⟨hEnv, ?_⟩
  obtain ⟨i, pos⟩ := f
  cases pos <;> simp [faceHeight] at hH ⊢ <;> omega

theorem farLegFaceCore_connection_mass_le {d t : ℕ} (ht : 64 ≤ t)
    {B : ℝ} (hB : BoxFaceFirstMoment d B)
    (U : Finset (Vertex d)) (hU : U ⊆ splitEnvelope d t) (u : Vertex d) (hu : u ∈ U)
    (f : Fin d × Bool) (pl : Bool) :
    (∑ y ∈ farLegFaceCore t f pl,
      restrictedConnectionReal (criticalPoint d) (U : Set (Vertex d)) u y) ≤ B := by
  have hU' : (U : Set (Vertex d)) ⊆ (splitEnvelope d t : Set (Vertex d)) := Finset.coe_subset.mpr hU
  calc
    _ ≤ ∑ y ∈ farLegFaceCore t f pl,
        restrictedConnectionReal (criticalPoint d) (splitEnvelope d t : Set (Vertex d)) u y := by
      apply Finset.sum_le_sum
      intro y _
      exact measureReal_mono (connectionToSetEvent_mono hU' subset_rfl u) (measure_ne_top _ _)
    _ ≤ ∑ y ∈ signedCubeFace d ((t - 1) / 2 + t) f,
        restrictedConnectionReal (criticalPoint d) (splitEnvelope d t : Set (Vertex d)) u y :=
      Finset.sum_le_sum_of_subset_of_nonneg (farLegFaceCore_subset_envelope_face ht f pl)
        (fun _ _ _ => measureReal_nonneg)
    _ ≤ B := hB ((t - 1) / 2 + t) u (hU hu) f

end NearCritical.SplitCrossDirect
