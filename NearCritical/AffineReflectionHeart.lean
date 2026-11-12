module
public import NearCritical.AffineReflectionDeleted
public import NearCritical.Section9ConditionalLaw

/-! Reflection of actual heart clusters and their reveal atoms. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

theorem measurable_affineReflectConfiguration {d : ℕ} (c : Vertex d) :
    Measurable (affineReflectConfiguration c) :=
  measurable_invertConfiguration.comp (measurable_translateConfiguration c)

theorem percolation_map_affineReflection {d : ℕ} (p : unitInterval) (c : Vertex d) :
    (percolation d p).map (affineReflectConfiguration c) = percolation d p := by
  change (percolation d p).map (invertConfiguration ∘ translateConfiguration c) = _
  rw [← Measure.map_map measurable_invertConfiguration (measurable_translateConfiguration c),
    percolation_map_translation,percolation_map_inversion]

private theorem reflect_mem_image {d : ℕ} (c : Vertex d)
    (S : Finset (Vertex d)) (x : Vertex d) :
    affineReflection c x ∈ S.image (affineReflection c) ↔ x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hx
    exact (affineReflection c).injective heq ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

private def reflectRestrictedIso {d : ℕ} (c : Vertex d) (ω : Configuration d)
    (Q : Finset (Vertex d)) :
    restrictedGraph (affineReflectConfiguration c ω) (Q : Set (Vertex d)) ≃g
      restrictedGraph ω ((Q.image (affineReflection c) : Finset (Vertex d)) : Set (Vertex d)) where
  toEquiv := affineReflection c
  map_rel_iff' := by
    intro x y
    change ((openGraph ω).Adj (affineReflection c x) (affineReflection c y) ∧
      affineReflection c x ∈ Q.image (affineReflection c) ∧
      affineReflection c y ∈ Q.image (affineReflection c)) ↔ _
    have ha : (openGraph (affineReflectConfiguration c ω)).Adj x y ↔
        (openGraph ω).Adj (affineReflection c x) (affineReflection c y) := by
      simpa only [affineReflectConfiguration,affineReflection,Equiv.coe_fn_mk,sub_eq_add_neg] using
        (openGraph_invert_adj (translateConfiguration c ω) x y).trans
          (openGraph_translate_adj c ω (-x) (-y))
    rw [← ha,reflect_mem_image,reflect_mem_image]
    rfl

private theorem reflect_finiteBoxCluster {d : ℕ} (c : Vertex d) (ω : Configuration d)
    (Q : Finset (Vertex d)) (root : Vertex d) :
    (finiteBoxCluster (affineReflectConfiguration c ω) Q root).image (affineReflection c) =
      finiteBoxCluster ω (Q.image (affineReflection c)) (affineReflection c root) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxQ,hr⟩ := (mem_finiteBoxCluster _ _ _ _).mp hx
    exact (mem_finiteBoxCluster _ _ _ _).mpr
      ⟨Finset.mem_image.mpr ⟨x,hxQ,rfl⟩,(reflectRestrictedIso c ω Q).reachable_iff.mpr hr⟩
  · intro hy
    obtain ⟨hyQ,hr⟩ := (mem_finiteBoxCluster _ _ _ _).mp hy
    obtain ⟨x,hxQ,rfl⟩ := Finset.mem_image.mp hyQ
    exact Finset.mem_image.mpr ⟨x,(mem_finiteBoxCluster _ _ _ _).mpr
      ⟨hxQ,(reflectRestrictedIso c ω Q).reachable_iff.mp hr⟩,rfl⟩

/-- Actual unions of heart-touching components transform, including hearts
with roots outside the domain. No stationarity of conditional laws is assumed. -/
theorem affineReflection_heartClusterUnion {d : ℕ} (c : Vertex d) (ω : Configuration d)
    (Q H : Finset (Vertex d)) :
    (heartClusterUnion (affineReflectConfiguration c ω) Q H).image (affineReflection c) =
      heartClusterUnion ω (Q.image (affineReflection c)) (H.image (affineReflection c)) := by
  ext y
  simp only [heartClusterUnion,Finset.mem_image,Finset.mem_biUnion]
  constructor
  · rintro ⟨x,⟨root,hroot,hx⟩,rfl⟩
    refine ⟨affineReflection c root,⟨root,hroot,rfl⟩,?_⟩
    rw [← reflect_finiteBoxCluster c ω Q root]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  · rintro ⟨_,⟨root,hroot,rfl⟩,hy⟩
    rw [← reflect_finiteBoxCluster c ω Q root] at hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x,⟨root,hroot,hx⟩,rfl⟩

/-- Pullback of the actual reveal atom, with every heart and cluster reflected. -/
theorem affineReflection_reveal_preimage {d : ℕ} (c : Vertex d)
    (Q H Q₃ H₃ F F₃ : Finset (Vertex d)) :
    (affineReflectConfiguration c) ⁻¹' section9RevealEvent Q H Q₃ H₃ F F₃ =
      section9RevealEvent (Q.image (affineReflection c)) (H.image (affineReflection c))
        (Q₃.image (affineReflection c)) (H₃.image (affineReflection c))
        (F.image (affineReflection c)) (F₃.image (affineReflection c)) := by
  ext ω
  change (_ = F ∧ _ = F₃) ↔ (_ = _ ∧ _ = _)
  rw [← affineReflection_heartClusterUnion c ω Q H,
    ← affineReflection_heartClusterUnion c ω Q₃ H₃]
  simp only [Finset.image_inj (affineReflection c).injective]

/-- Exact transport of actual revealed probabilities, including zero reveal
atoms. The conditioning event and the tested event are both reflected. -/
theorem affineReflection_revealed_probability {d : ℕ} (p : unitInterval) (c : Vertex d)
    (Q H Q₃ H₃ F F₃ : Finset (Vertex d)) (hH : H ⊆ Q) (hH₃ : H₃ ⊆ Q₃)
    (A : Set (Configuration d)) (hA : MeasurableSet A) :
    section9RevealedLaw p (Q.image (affineReflection c)) (H.image (affineReflection c))
      (Q₃.image (affineReflection c)) (H₃.image (affineReflection c))
      (F.image (affineReflection c)) (F₃.image (affineReflection c))
      (affineReflectConfiguration c ⁻¹' A) =
        section9RevealedLaw p Q H Q₃ H₃ F F₃ A := by
  let E := section9RevealEvent Q H Q₃ H₃ F F₃
  let E' := section9RevealEvent (Q.image (affineReflection c)) (H.image (affineReflection c))
    (Q₃.image (affineReflection c)) (H₃.image (affineReflection c))
    (F.image (affineReflection c)) (F₃.image (affineReflection c))
  have hm : MeasurableSet E := measurableSet_section9RevealEvent Q H Q₃ H₃ F F₃ hH hH₃
  have hevent : affineReflectConfiguration c ⁻¹' E = E' :=
    affineReflection_reveal_preimage c Q H Q₃ H₃ F F₃
  have hm' : MeasurableSet E' := by
    rw [← hevent]
    exact hm.preimage (measurable_affineReflectConfiguration c)
  have hpre (S : Set (Configuration d)) (hS : MeasurableSet S) :
      percolation d p (affineReflectConfiguration c ⁻¹' S) = percolation d p S := by
    rw [← Measure.map_apply (measurable_affineReflectConfiguration c) hS,
      percolation_map_affineReflection]
  have hE : percolation d p E' = percolation d p E := by
    rw [← hevent]
    exact hpre E hm
  have hEA : percolation d p (E' ∩ affineReflectConfiguration c ⁻¹' A) =
      percolation d p (E ∩ A) := by
    rw [← hevent,← Set.preimage_inter]
    exact hpre (E ∩ A) (hm.inter hA)
  change ProbabilityTheory.cond (percolation d p) E' (affineReflectConfiguration c ⁻¹' A) =
    ProbabilityTheory.cond (percolation d p) E A
  rw [ProbabilityTheory.cond_apply hm',ProbabilityTheory.cond_apply hm,hE,hEA]

end NearCritical
