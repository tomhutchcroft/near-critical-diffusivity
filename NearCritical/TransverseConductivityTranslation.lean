module

public import NearCritical.ConductivityTranslation

/-! Actual relaxed Dirichlet covariance for translations parallel to its faces.
This is the stationarity needed for the mixed-grid boundary comparison. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory

lemma twoFaceBoundary_translate_iff {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (x : Vertex d)
    (hx : x ∈ sitesPlus U) (hax : a+x ∈ sitesPlus (translateSites a U)) :
    (⟨a+x,hax⟩ : DomainVertex (translateSites a U)) ∈ twoFaceBoundary _ i ↔
      (⟨x,hx⟩ : DomainVertex U) ∈ twoFaceBoundary U i := by
  classical
  change (a+x ∈ boundarySites (sitesPlus (translateSites a U)) ∧
      ((∀ y ∈ sitesPlus (translateSites a U), y i ≤ (a+x) i) ∨
       (∀ y ∈ sitesPlus (translateSites a U), (a+x) i ≤ y i))) ↔ _
  rw [sitesPlus_translate, boundarySites_translate_mem]
  constructor
  · rintro ⟨hb, ht | ht⟩
    · refine ⟨hb, Or.inl ?_⟩
      intro y hy
      have h := ht (a+y) ((mem_translateSites a (sitesPlus U) y).mpr hy)
      simpa only [Pi.add_apply, add_le_add_iff_left] using h
    · refine ⟨hb, Or.inr ?_⟩
      intro y hy
      have h := ht (a+y) ((mem_translateSites a (sitesPlus U) y).mpr hy)
      simpa only [Pi.add_apply, add_le_add_iff_left] using h
  · rintro ⟨hb, ht | ht⟩
    · refine ⟨hb, Or.inl ?_⟩
      intro y hy
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
      simpa only [Pi.add_apply, add_le_add_iff_left] using ht z hz
    · refine ⟨hb, Or.inr ?_⟩
      intro y hy
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
      simpa only [Pi.add_apply, add_le_add_iff_left] using ht z hz

lemma exists_global_relaxed_minimizer {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (i : Fin d) :
    ∃ v : Vertex d → ℝ,
      (∀ x : DomainVertex U, x ∈ twoFaceBoundary U i → v x.val = coordinateData i x) ∧
      issuedEnergy U ω v = (issuedNetwork U).conductance (domainWeights ω)
        (twoFaceBoundary U i) (coordinateData i) := by
  classical
  obtain ⟨u,hu⟩ := exists_relaxed_minimizer U i ω
  let v : Vertex d → ℝ := fun x => if hx : x ∈ sitesPlus U then u ⟨x,hx⟩ else (x i : ℝ)
  have hr : (fun x : DomainVertex U => v x.val) = u := by
    funext x
    simp [v,x.property]
  refine ⟨v, ?_, ?_⟩
  · intro x hx
    simpa [v,x.property] using hu.1 x hx
  · rw [issuedEnergy_eq_network,hr]
    exact (Network.IsMinimizer.conductance_eq _ (domainWeights_nonneg ω) hu).symm

lemma relaxed_conductance_transverse_translation_le {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (ha : a i = 0) (ω : Configuration d) :
    (issuedNetwork (translateSites a U)).conductance (domainWeights ω)
      (twoFaceBoundary _ i) (coordinateData i) ≤
    (issuedNetwork U).conductance (domainWeights (translateConfiguration a ω))
      (twoFaceBoundary U i) (coordinateData i) := by
  obtain ⟨v,hv,he⟩ := exists_global_relaxed_minimizer U (translateConfiguration a ω) i
  let w : Vertex d → ℝ := fun x => v (-a+x)
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
    simpa [w,coordinateData,ha] using h
  calc
    _ ≤ issuedEnergy (translateSites a U) ω w := by
      rw [issuedEnergy_eq_network]
      exact (issuedNetwork _).conductance_le_energy (domainWeights_nonneg ω) hadm
    _ = issuedEnergy U (translateConfiguration a ω) v := by
      rw [issuedEnergy_translate]
      congr 1
      funext x
      simp [w]
    _ = _ := he

theorem relaxedConductivity_transverse_translation {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (ha : a i = 0) (ω : Configuration d) :
    relaxedConductivity (translateSites a U) i ω =
      relaxedConductivity U i (translateConfiguration a ω) := by
  have hle := relaxed_conductance_transverse_translation_le a U i ha ω
  have hge := relaxed_conductance_transverse_translation_le (-a) (translateSites a U) i
    (by simp [ha]) (translateConfiguration a ω)
  rw [translateSites_neg_cancel,translateConfiguration_neg_cancel] at hge
  unfold relaxedConductivity
  rw [card_translateSites]
  exact congrArg (fun r : ℝ => r / U.card) (le_antisymm hle hge)

lemma integrable_relaxedConductivity {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) : Integrable (relaxedConductivity U i) (percolation d p) := by
  change Integrable (fun ω => relaxedConductivity U i ω) (percolation d p)
  simp_rw [relaxedConductivity_restrict]
  exact percolation_cylinder_integrable d p (issuedBondSet U) (localRelaxedConductivity U i)

theorem annealedRelaxed_transverse_translation {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (ha : a i = 0) (p : unitInterval) :
    annealedRelaxed (translateSites a U) i (p : ℝ) = annealedRelaxed U i (p : ℝ) := by
  rw [annealedRelaxed_eq_integral,annealedRelaxed_eq_integral]
  simp_rw [relaxedConductivity_transverse_translation a U i ha]
  have hm := measurable_translateConfiguration a
  have hf := (integrable_relaxedConductivity U i p).aestronglyMeasurable
  rw [← percolation_map_translation p a] at hf
  rw [← integral_map hm.aemeasurable hf,percolation_map_translation]

end NearCritical
