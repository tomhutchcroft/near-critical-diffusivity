module

public import NearCritical.CoarseCubeIndependence

/-! Common actual cube-event probability q in source eq.nw.weights.
Literal pre-goodness must still be identified with the local template. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

lemma translateBond_mem_internalBondSet {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (e : Bond d) :
    translateBond a e ∈ internalBondSet (translateSites a U) ↔ e ∈ internalBondSet U := by
  rw [mem_internalBondSet,mem_internalBondSet,bondTip_translate]
  change (a+e.1 ∈ translateSites a U ∧ a+bondTip e ∈ translateSites a U) ↔ _
  simp only [mem_translateSites]

/-- Read a translated local bit assignment in the original bond coordinates. -/
def translateInternalBits {d : ℕ} (a : Vertex d) (U : Finset (Vertex d))
    (η : internalBondSet (translateSites a U) → Bool) : internalBondSet U → Bool :=
  fun e => η ⟨translateBond a e.val,(translateBond_mem_internalBondSet a U e.val).2 e.property⟩

/-- A single source local predicate transported to the translated cube. -/
def translatedCubeTemplate {d : ℕ} (a : Vertex d) (U : Finset (Vertex d))
    (A : Set (internalBondSet U → Bool)) : Set (internalBondSet (translateSites a U) → Bool) :=
  translateInternalBits a U ⁻¹' A

lemma translateInternalBits_restrict {d : ℕ} (a : Vertex d) (U : Finset (Vertex d))
    (ω : Configuration d) :
    translateInternalBits a U ((internalBondSet (translateSites a U)).restrict ω) =
      (internalBondSet U).restrict (translateConfiguration a ω) := rfl

/-- The source q is independent of the cube location under the actual product law. -/
theorem nestCubeProbability_template_translation {d : ℕ} (p : unitInterval)
    (a : Vertex d) (U : Finset (Vertex d)) (A : Set (internalBondSet U → Bool)) :
    nestCubeProbability p (internalBondSet (translateSites a U)) (translatedCubeTemplate a U A) =
      nestCubeProbability p (internalBondSet U) A := by
  have hm : MeasurableSet {ω : Configuration d | (internalBondSet U).restrict ω∈A} :=
    (Finset.measurable_restrict _) (Set.toFinite A).measurableSet
  have he : {ω : Configuration d | (internalBondSet (translateSites a U)).restrict ω ∈
      translatedCubeTemplate a U A} = translateConfiguration a ⁻¹'
        {ω : Configuration d | (internalBondSet U).restrict ω∈A} := by
    ext ω
    rfl
  unfold nestCubeProbability
  rw [he,← map_measureReal_apply (measurable_translateConfiguration a) hm,
    percolation_map_translation]

/-- Exact normalized weight transport, including the same common normalizer. -/
theorem nestCubeWeight_template_translation {d : ℕ} (p : unitInterval)
    (a : Vertex d) (U : Finset (Vertex d)) (A : Set (internalBondSet U → Bool))
    (ω : Configuration d) :
    nestCubeWeight p (internalBondSet (translateSites a U)) (translatedCubeTemplate a U A) ω =
      nestCubeWeight p (internalBondSet U) A (translateConfiguration a ω) := by
  classical
  simp only [nestCubeWeight]
  rw [nestCubeProbability_template_translation]
  simp only [translatedCubeTemplate,Set.mem_preimage,translateInternalBits_restrict]

/-- Source-style product mean with one actual q for all translated coarse cubes.
Neither block independence nor equality of their probabilities is a premise. -/
theorem percolation_coarseTemplateWeight_mean {d t r : ℕ} (p : unitInterval)
    (hsmall : r<t) (route : Finset (Fin d → ℕ))
    (A : Set (internalBondSet (centeredBox d r) → Bool))
    (hq : 0<nestCubeProbability p (internalBondSet (centeredBox d r)) A) :
    (∫ ω : Configuration d, ∏ a∈route, nestCubeWeight p (internalBondSet (centeredBox d r)) A
      (translateConfiguration (chemicalCoarseCenter t a) ω) ∂percolation d p)=1 := by
  let templates := fun a : Fin d → ℕ =>
    translatedCubeTemplate (chemicalCoarseCenter t a) (centeredBox d r) A
  have hp (a : Fin d → ℕ) : 0<nestCubeProbability p (chemicalCoarseInternalBonds d t r a) (templates a) := by
    change 0<nestCubeProbability p (internalBondSet (translateSites _ _)) (translatedCubeTemplate _ _ A)
    rwa [nestCubeProbability_template_translation]
  have h := percolation_coarseCubeWeight_mean p hsmall route templates (fun a _ => hp a)
  simpa only [chemicalCoarseInternalBonds,templates,nestCubeWeight_template_translation] using h

/-- Explicit indicator-over-common-q form of omega_Gamma's mean. -/
theorem percolation_coarseTemplate_common_q {d t r : ℕ} (p : unitInterval)
    (hsmall : r<t) (route : Finset (Fin d → ℕ))
    (A : Set (internalBondSet (centeredBox d r) → Bool))
    (hq : 0<nestCubeProbability p (internalBondSet (centeredBox d r)) A) :
    (∫ ω : Configuration d, ∏ a∈route,
      (if (internalBondSet (centeredBox d r)).restrict
        (translateConfiguration (chemicalCoarseCenter t a) ω)∈A
        then (nestCubeProbability p (internalBondSet (centeredBox d r)) A)⁻¹ else 0)
      ∂percolation d p)=1 := by
  classical
  simpa only [nestCubeWeight] using percolation_coarseTemplateWeight_mean p hsmall route A hq

end NearCritical
