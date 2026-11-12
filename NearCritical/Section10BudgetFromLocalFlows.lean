module

public import NearCritical.Section10TranslatedCoupledBudget
public import NearCritical.Section10SemanticRule

/-! A finite observation of the good event and its energy bound gives
an admissible coupled cube flow budget. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- Select one issued flow per finite bit pattern on the good event.
The upper bound on its energy and the good event itself are unchanged
when taking the representative of a pattern. -/
theorem translatedCoupledCubeFlowBudget_of_local_flows {d r : ℕ}
    (p q : unitInterval) (aC : Vertex d) (i : Fin d) (a C : ℝ)
    (R : Finset (LBond d))
    (W E : Configuration d × Configuration d → ℝ)
    (hW : IsLocal R W) (hE : IsLocal R E) (hE₀ : ∀ z, 0 ≤ E z) :
    let U := translateSites aC (centeredBox d r)
    let μ := (percolation d p).prod (percolation d q)
    (∀ e : IssuedBond U, ∀ b : Bool, (b,e.val) ∈ R) →
    (a ≤ ∫ z, (if (1/2:ℝ) ≤ W z then (1:ℝ) else 0) ∂μ) →
    (∫ z, E z ∂μ) ≤ C * cubeFlowNormalization d r *
      (chemicalCorrelationScale d (orParameter p q) : ℝ)^6 →
    (∀ z, (1/2:ℝ) ≤ W z →
      ∃ θ : IssuedBond U → ℝ,
        Network.FlowSupported (domainWeights (sprinkleOrConfiguration z.1 z.2)) θ ∧
        (issuedNetwork U).IsBoundaryUnitFlow (negativeFace U i) (positiveFace U i) θ ∧
        Network.flowEnergy (domainWeights (sprinkleOrConfiguration z.1 z.2)) θ ≤ E z) →
    translatedCoupledCubeFlowBudget p q aC i r a C := by
  intro U μ hR hprob henergy hflow
  let sample (b : R → Bool) := gluePair (T := ∅) b (fun _ => false)
  have hsample (b : R → Bool) : R.restrict (layerVal (sample b)) = b := by
    funext e
    change layerVal (sample b) e.val = b e
    rw [show sample b = gluePair (T := ∅) b (fun _ => false) from rfl, layerVal_gluePair,
      dif_pos e.property]
  have hread (f : Configuration d × Configuration d → ℝ) (hf : IsLocal R f)
      (z : Configuration d × Configuration d) :
      f (sample (R.restrict (layerVal z))) = f z := by
    obtain ⟨g,hg⟩ := hf
    rw [hg, hsample, ← hg]
  let orb (b : R → Bool) :=
    (issuedBondSet U).restrict (sprinkleOrConfiguration (sample b).1 (sample b).2)
  have horb (z : Configuration d × Configuration d) :
      orb (R.restrict (layerVal z)) = (issuedBondSet U).restrict (sprinkleOrConfiguration z.1 z.2) := by
    funext e
    have hbits (b : Bool) :
        layerVal (sample (R.restrict (layerVal z))) (b,e.val) = layerVal z (b,e.val) :=
      congrFun (hsample (R.restrict (layerVal z))) ⟨(b,e.val),hR e b⟩
    change (layerVal (sample (R.restrict (layerVal z))) (false,e.val) ||
      layerVal (sample (R.restrict (layerVal z))) (true,e.val)) =
      (layerVal z (false,e.val) || layerVal z (true,e.val))
    rw [hbits false, hbits true]
  let A : Set (R → Bool) := {b | (1/2:ℝ) ≤ W (sample b)}
  let θ (b : R → Bool) : IssuedBond U → ℝ :=
    if hb : b ∈ A then Classical.choose (hflow (sample b) hb) else 0
  have hθ (b : R → Bool) (hb : b ∈ A) :
      Network.FlowSupported (cubeFlowWeights (orb b)) (θ b) ∧
      (issuedNetwork U).IsBoundaryUnitFlow (negativeFace U i) (positiveFace U i) (θ b) ∧
      Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) ≤ E (sample b) := by
    have ht : θ b = Classical.choose (hflow (sample b) hb) := dif_pos hb
    rw [ht]
    exact Classical.choose_spec (hflow (sample b) hb)
  refine ⟨R,orb,θ,A,horb,fun b hb => ⟨(hθ b hb).1,(hθ b hb).2.1⟩,?_,?_⟩
  · refine le_trans hprob (le_of_eq ?_)
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun z => ?_
    have ha : R.restrict (layerVal z) ∈ A ↔ (1/2:ℝ) ≤ W z := by
      change (1/2:ℝ) ≤ W (sample (R.restrict (layerVal z))) ↔ _
      rw [hread W hW]
    simp only [ha]
  · refine (integral_mono
        ((show IsLocal R (fun z => if R.restrict (layerVal z) ∈ A then
          Network.flowEnergy (cubeFlowWeights (orb (R.restrict (layerVal z))))
            (θ (R.restrict (layerVal z))) else 0)
          from ⟨fun b => if b ∈ A then Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) else 0,
            fun _ => rfl⟩).integrable p q)
        (hE.integrable p q) ?_).trans henergy
    intro z
    change (if R.restrict (layerVal z) ∈ A then
      Network.flowEnergy (cubeFlowWeights (orb (R.restrict (layerVal z))))
        (θ (R.restrict (layerVal z))) else 0) ≤ E z
    by_cases hb : R.restrict (layerVal z) ∈ A
    · rw [if_pos hb, ← hread E hE z]
      exact (hθ _ hb).2.2
    · rw [if_neg hb]
      exact hE₀ z

end NearCritical.Section10
