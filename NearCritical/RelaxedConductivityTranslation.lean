module
public import NearCritical.TransverseConductivityTranslation

/-! Arbitrary lattice translations of the actual relaxed Dirichlet problem.
Unlike the transverse special case, translated coordinate data change by a
constant, which is carried in the competitor and removed from its energy. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

lemma relaxed_conductance_translation_le {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (ω : Configuration d) :
    (issuedNetwork (translateSites a U)).conductance (domainWeights ω)
      (twoFaceBoundary _ i) (coordinateData i) ≤
    (issuedNetwork U).conductance (domainWeights (translateConfiguration a ω))
      (twoFaceBoundary U i) (coordinateData i) := by
  obtain ⟨v,hv,he⟩ := exists_global_relaxed_minimizer U (translateConfiguration a ω) i
  let w : Vertex d → ℝ := fun x => v (-a+x)+(a i:ℝ)
  have hadm : Network.admissible (twoFaceBoundary (translateSites a U) i)
      (coordinateData i) (fun x => w x.val) := by
    intro x hx
    have hax : a+(-a+x.val) ∈ sitesPlus (translateSites a U) := by simpa only [add_neg_cancel_left] using x.property
    have hold : -a+x.val ∈ sitesPlus U := by
      have hax' : a+(-a+x.val) ∈ translateSites a (sitesPlus U) := by
        simpa only [sitesPlus_translate] using hax
      exact (mem_translateSites a (sitesPlus U) _).mp hax'
    have hface : (⟨a+(-a+x.val),hax⟩ : DomainVertex (translateSites a U)) ∈
        twoFaceBoundary _ i := by simpa using hx
    have h := hv ⟨-a+x.val,hold⟩ ((twoFaceBoundary_translate_iff a U i _ hold hax).mp hface)
    dsimp [w,coordinateData]
    rw [h]
    simp [coordinateData]
  calc
    _ ≤ issuedEnergy (translateSites a U) ω w := by
      rw [issuedEnergy_eq_network]
      exact (issuedNetwork _).conductance_le_energy (domainWeights_nonneg ω) hadm
    _ = issuedEnergy U (translateConfiguration a ω) (fun x => v x+(a i:ℝ)) := by
      rw [issuedEnergy_translate]
      congr 1
      funext x
      simp [w]
    _ = issuedEnergy U (translateConfiguration a ω) v := issuedEnergy_add_const _ _ _ _
    _ = _ := he

/-- Actual relaxed conductivity is covariant under ALL translations, including
shifts normal to its two faces. -/
theorem relaxedConductivity_translation {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (ω : Configuration d) :
    relaxedConductivity (translateSites a U) i ω =
      relaxedConductivity U i (translateConfiguration a ω) := by
  have hle := relaxed_conductance_translation_le a U i ω
  have hge := relaxed_conductance_translation_le (-a) (translateSites a U) i
    (translateConfiguration a ω)
  rw [translateSites_neg_cancel,translateConfiguration_neg_cancel] at hge
  unfold relaxedConductivity
  rw [card_translateSites]
  exact congrArg (fun r : ℝ => r/U.card) (le_antisymm hle hge)

/-- Genuine actual-law stationarity, not an assumed affine-boundary convention. -/
theorem annealedRelaxed_translation {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (p : unitInterval) :
    annealedRelaxed (translateSites a U) i (p:ℝ) = annealedRelaxed U i (p:ℝ) := by
  rw [annealedRelaxed_eq_integral,annealedRelaxed_eq_integral]
  simp_rw [relaxedConductivity_translation a U i]
  have hm := measurable_translateConfiguration a
  have hf := (integrable_relaxedConductivity U i p).aestronglyMeasurable
  rw [← percolation_map_translation p a] at hf
  rw [← integral_map hm.aemeasurable hf,percolation_map_translation]

end NearCritical
