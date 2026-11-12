module

public import NearCritical.TranslationInvariance
public import NearCritical.IssuedPartition
public import NearCritical.LatticeFullConductivity

/-! Translation of the actual issued-edge Dirichlet problem. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory

def translateSites {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) : Finset (Vertex d) :=
  U.image (fun x => a + x)

lemma mem_translateSites {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) (x : Vertex d) :
    a + x ∈ translateSites a U ↔ x ∈ U := by
  classical
  simp [translateSites]

lemma card_translateSites {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) :
    (translateSites a U).card = U.card := by
  classical
  exact Finset.card_image_of_injective _ (add_right_injective a)

lemma sitesPlus_translate {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) :
    sitesPlus (translateSites a U) = translateSites a (sitesPlus U) := by
  classical
  ext x
  simp only [sitesPlus, translateSites, mem_union, mem_image, mem_biUnion]
  constructor
  · rintro (h | ⟨y, ⟨z,hz,rfl⟩,j,hj,rfl⟩)
    · obtain ⟨y,hy,rfl⟩ := h
      exact ⟨y, Or.inl hy, rfl⟩
    · exact ⟨bondTip (z,j), Or.inr ⟨z,hz,j,hj,rfl⟩,
        (bondTip_translate a (z,j)).symm⟩
  · rintro ⟨y,hy,rfl⟩
    rcases hy with hy | ⟨z,hz,j,hj,rfl⟩
    · exact Or.inl ⟨y,hy,rfl⟩
    · exact Or.inr ⟨a+z, ⟨z,hz,rfl⟩,j,hj,bondTip_translate a (z,j)⟩

lemma boundarySites_translate_mem {d : ℕ} (a : Vertex d) (S : Finset (Vertex d))
    (x : Vertex d) :
    a+x ∈ boundarySites (translateSites a S) ↔ x ∈ boundarySites S := by
  classical
  simp only [boundarySites, mem_filter, mem_translateSites]
  constructor
  · rintro ⟨hx,y,hy,hxy⟩
    refine ⟨hx, -a+y, ?_, ?_⟩
    · intro hm
      apply hy
      have := (mem_translateSites a S (-a+y)).2 hm
      simpa using this
    · have h := (openGraph_translate_adj a (fun _ => true) x (-a+y)).2
      have hc : translateConfiguration a (fun _ => true) = (fun _ => true) := rfl
      rw [hc] at h
      exact h (by simpa using hxy)
  · rintro ⟨hx,y,hy,hxy⟩
    refine ⟨hx,a+y, (fun hm => hy ((mem_translateSites a S y).1 hm)), ?_⟩
    apply (openGraph_translate_adj a (fun _ => true) x y).1
    change (openGraph (fun _ => true)).Adj x y
    exact hxy

lemma issuedBondSet_translate {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) :
    issuedBondSet (translateSites a U) = (issuedBondSet U).image (translateBond a) := by
  classical
  ext e
  simp only [issuedBondSet, Finset.product_eq_sprod, mem_product, mem_univ, and_true, translateSites, mem_image]
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨(x,e.2),hx,by simp [translateBond,he]⟩
  · rintro ⟨e,he,rfl⟩
    exact ⟨e.1,he,rfl⟩

lemma issuedEnergy_translate {d : ℕ} (a : Vertex d) (U : Finset (Vertex d))
    (ω : Configuration d) (v : Vertex d → ℝ) :
    issuedEnergy (translateSites a U) ω v =
      issuedEnergy U (translateConfiguration a ω) (fun x => v (a+x)) := by
  classical
  unfold issuedEnergy
  rw [issuedBondSet_translate, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e he
    rw [bondTip_translate]
    rfl
  · exact fun e he f hf h => (translateBond a).injective h


lemma translateSites_neg_cancel {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) :
    translateSites (-a) (translateSites a U) = U := by
  classical
  ext x
  simpa using (mem_translateSites (-a) (translateSites a U) (a+x)).trans
    (mem_translateSites a U x)

lemma translateConfiguration_neg_cancel {d : ℕ} (a : Vertex d) (ω : Configuration d) :
    translateConfiguration (-a) (translateConfiguration a ω) = ω := by
  funext e
  simp [translateConfiguration, translateBond]

lemma conductance_le_global_energy {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (g v : Vertex d → ℝ)
    (hv : ∀ x ∈ boundarySites (sitesPlus U), v x = g x) :
    (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (fun x => g x.val) ≤
      issuedEnergy U ω v := by
  rw [issuedEnergy_eq_network]
  exact (issuedNetwork U).conductance_le_energy (domainWeights_nonneg ω)
    (fun x hx => hv x.val hx)

lemma exists_global_dirichlet_minimizer {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (g : Vertex d → ℝ) :
    ∃ v : Vertex d → ℝ, (∀ x ∈ boundarySites (sitesPlus U), v x = g x) ∧
      issuedEnergy U ω v =
        (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (fun x => g x.val) := by
  classical
  obtain ⟨u,hu⟩ := (issuedNetwork U).exists_minimizer (domainWeights_nonneg ω)
    (fullBoundary U) (fun x => g x.val)
  let v : Vertex d → ℝ := fun x => if hx : x ∈ sitesPlus U then u ⟨x,hx⟩ else g x
  have hr : (fun x : DomainVertex U => v x.val) = u := by
    funext x
    simp [v,x.property]
  refine ⟨v,?_,?_⟩
  · intro x hx
    have hm := (Finset.mem_filter.mp hx).1
    simpa [v,hm] using hu.1 ⟨x,hm⟩ hx
  · rw [issuedEnergy_eq_network,hr]
    exact (Network.IsMinimizer.conductance_eq (issuedNetwork U)
      (domainWeights_nonneg ω) hu).symm

lemma dirichlet_conductance_translation_le {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (ω : Configuration d) (g : Vertex d → ℝ) :
    (issuedNetwork (translateSites a U)).conductance (domainWeights ω)
      (fullBoundary _) (fun x => g x.val) ≤
    (issuedNetwork U).conductance (domainWeights (translateConfiguration a ω))
      (fullBoundary U) (fun x => g (a+x.val)) := by
  obtain ⟨v,hv,he⟩ := exists_global_dirichlet_minimizer U (translateConfiguration a ω)
    (fun x => g (a+x))
  let w : Vertex d → ℝ := fun x => v (-a+x)
  have hw : ∀ x ∈ boundarySites (sitesPlus (translateSites a U)), w x = g x := by
    intro x hx
    rw [sitesPlus_translate] at hx
    have hx' : a+(-a+x) ∈ boundarySites (translateSites a (sitesPlus U)) := by simpa using hx
    have h := hv (-a+x) ((boundarySites_translate_mem a (sitesPlus U) (-a+x)).1 hx')
    simpa [w] using h
  calc
    _ ≤ issuedEnergy (translateSites a U) ω w := conductance_le_global_energy _ _ _ _ hw
    _ = issuedEnergy U (translateConfiguration a ω) v := by
      rw [issuedEnergy_translate]
      congr 1
      funext x
      simp [w]
    _ = _ := he

/-- Covariance of the full Dirichlet variational problem for arbitrary data. -/
theorem dirichlet_conductance_translation {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (ω : Configuration d) (g : Vertex d → ℝ) :
    (issuedNetwork (translateSites a U)).conductance (domainWeights ω)
      (fullBoundary _) (fun x => g x.val) =
    (issuedNetwork U).conductance (domainWeights (translateConfiguration a ω))
      (fullBoundary U) (fun x => g (a+x.val)) := by
  apply le_antisymm (dirichlet_conductance_translation_le a U ω g)
  obtain ⟨v,hv,he⟩ := exists_global_dirichlet_minimizer (translateSites a U) ω g
  have ha : ∀ x ∈ boundarySites (sitesPlus U), v (a+x) = g (a+x) := by
    intro x hx
    apply hv
    rw [sitesPlus_translate]
    exact (boundarySites_translate_mem a (sitesPlus U) x).2 hx
  calc
    _ ≤ issuedEnergy U (translateConfiguration a ω) (fun x => v (a+x)) :=
      conductance_le_global_energy _ _ _ _ ha
    _ = issuedEnergy (translateSites a U) ω v := (issuedEnergy_translate a U ω v).symm
    _ = _ := he


lemma issuedEnergy_add_const {d : ℕ} (U : Finset (Vertex d)) (ω : Configuration d)
    (v : Vertex d → ℝ) (c : ℝ) :
    issuedEnergy U ω (fun x => v x+c) = issuedEnergy U ω v := by
  classical
  unfold issuedEnergy
  apply Finset.sum_congr rfl
  intro e he
  congr 2
  ring

lemma dirichlet_conductance_add_const_le {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (g : Vertex d → ℝ) (c : ℝ) :
    (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (fun x => g x.val+c) ≤
      (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (fun x => g x.val) := by
  obtain ⟨v,hv,he⟩ := exists_global_dirichlet_minimizer U ω g
  calc
    _ ≤ issuedEnergy U ω (fun x => v x+c) :=
      conductance_le_global_energy U ω (fun x => g x+c) (fun x => v x+c)
        (fun x hx => by rw [hv x hx])
    _ = issuedEnergy U ω v := issuedEnergy_add_const U ω v c
    _ = _ := he

lemma dirichlet_conductance_add_const {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (g : Vertex d → ℝ) (c : ℝ) :
    (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (fun x => g x.val+c) =
      (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (fun x => g x.val) := by
  apply le_antisymm (dirichlet_conductance_add_const_le U ω g c)
  have h := dirichlet_conductance_add_const_le U ω (fun x => g x+c) (-c)
  simpa only [add_neg_cancel_right] using h

/-- Coordinate conductivity has exact quenched translation covariance. -/
theorem fullConductivity_translation {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (ω : Configuration d) :
    fullConductivity (translateSites a U) i ω =
      fullConductivity U i (translateConfiguration a ω) := by
  have h := dirichlet_conductance_translation a U ω (fun x => (x i : ℝ))
  have hg : (fun x : DomainVertex U => ((a+x.val) i : ℝ)) =
      (fun x : DomainVertex U => (x.val i : ℝ)+(a i : ℝ)) := by
    funext x
    simp [add_comm]
  rw [hg, dirichlet_conductance_add_const U (translateConfiguration a ω)
    (fun x => (x i : ℝ)) (a i : ℝ)] at h
  unfold fullConductivity
  rw [card_translateSites]
  exact congrArg (fun r : ℝ => r / U.card) h

/-- Stationarity is proved under the actual infinite Bernoulli product law. -/
theorem annealedFull_translation {d : ℕ} (a : Vertex d)
    (U : Finset (Vertex d)) (i : Fin d) (p : unitInterval) :
    annealedFull (translateSites a U) i (p : ℝ) = annealedFull U i (p : ℝ) := by
  rw [annealedFull_eq_integral, annealedFull_eq_integral]
  simp_rw [fullConductivity_translation]
  have hm := measurable_translateConfiguration a
  have hf := (integrable_fullConductivity U i p).aestronglyMeasurable
  rw [← percolation_map_translation p a] at hf
  rw [← integral_map hm.aemeasurable hf, percolation_map_translation]

end NearCritical
