module

public import NearCritical.ConductivityTranslation
public import NearCritical.LatticePermutation

/-! Coordinate-permutation covariance of the issued-edge Dirichlet problem
(symmetry adapter, axis half).

For a finite vertex set `U` invariant under the coordinate permutation `σ`:

* `fullConductivity_perm`: `fullConductivity U i (permConfiguration σ ω) =
  fullConductivity U (σ i) ω`;
* `annealedFull_perm`: `annealedFull U i p = annealedFull U (σ i) p`;
* `annealedFull_centeredBox_axis`: the annealed conductivity of a centered box
  is the same along every axis.

The proof follows `ConductivityTranslation.lean`: transport a global Dirichlet
minimizer and compare energies bond by bond.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory

variable {d : ℕ}

lemma perm_symm_invariant (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) : ∀ x, permVertex σ.symm x ∈ U ↔ x ∈ U := by
  intro x
  have h := hU (permVertex σ.symm x)
  rw [permVertex_apply_symm] at h
  exact h.symm

lemma sitesPlus_perm_mem (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) {x : Vertex d} (hx : x ∈ sitesPlus U) :
    permVertex σ x ∈ sitesPlus U := by
  classical
  obtain hx | hx := mem_union.mp hx
  · exact base_mem_sitesPlus ((hU x).2 hx)
  · obtain ⟨z, hz, hx⟩ := mem_biUnion.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    rw [permVertex_bondTip]
    exact tip_mem_sitesPlus ((hU z).2 hz) (σ j)

lemma sitesPlus_perm_iff (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) (x : Vertex d) :
    permVertex σ x ∈ sitesPlus U ↔ x ∈ sitesPlus U := by
  constructor
  · intro h
    have h' := sitesPlus_perm_mem σ.symm (perm_symm_invariant σ hU) h
    rwa [permVertex_symm_apply] at h'
  · exact sitesPlus_perm_mem σ hU

lemma boundarySites_perm_mem (σ : Equiv.Perm (Fin d)) {S : Finset (Vertex d)}
    (hS : ∀ x, permVertex σ x ∈ S ↔ x ∈ S) {x : Vertex d} (hx : x ∈ boundarySites S) :
    permVertex σ x ∈ boundarySites S := by
  classical
  simp only [boundarySites, mem_filter] at hx ⊢
  obtain ⟨hxS, y, hy, hxy⟩ := hx
  refine ⟨(hS x).2 hxS, permVertex σ y, fun hm => hy ((hS y).1 hm), ?_⟩
  have h := (openGraph_perm_adj σ (fun _ => true) x y).1
  have hc : permConfiguration σ (fun _ : Bond d => true) = (fun _ => true) := rfl
  rw [hc] at h
  exact h hxy

lemma issuedBondSet_perm (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) :
    (issuedBondSet U).image (permBond σ) = issuedBondSet U := by
  classical
  ext e
  simp only [issuedBondSet, Finset.product_eq_sprod, mem_product, mem_univ, and_true, mem_image]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (hU f.1).2 hf
  · intro he
    refine ⟨(permBond σ).symm e, ?_, by simp⟩
    exact (perm_symm_invariant σ hU e.1).2 he

lemma issuedEnergy_perm (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) (ω : Configuration d) (v : Vertex d → ℝ) :
    issuedEnergy U (permConfiguration σ ω) (fun x => v (permVertex σ x)) =
      issuedEnergy U ω v := by
  classical
  have h : ∑ e ∈ (issuedBondSet U).image (permBond σ),
        (if ω e then (1 : ℝ) else 0) * (v (bondTip e) - v e.1) ^ 2 =
      ∑ e ∈ issuedBondSet U, (if ω (permBond σ e) then (1 : ℝ) else 0) *
        (v (bondTip (permBond σ e)) - v (permBond σ e).1) ^ 2 :=
    Finset.sum_image (fun e _ f _ h => (permBond σ).injective h)
  rw [issuedBondSet_perm σ hU] at h
  unfold issuedEnergy
  rw [h]
  apply Finset.sum_congr rfl
  intro e _
  beta_reduce
  rw [permVertex_bondTip]
  rfl

lemma permConfiguration_symm_cancel (σ : Equiv.Perm (Fin d)) (ω : Configuration d) :
    permConfiguration σ.symm (permConfiguration σ ω) = ω := by
  funext e
  simp [permConfiguration, permBond, permVertex_apply_symm]

lemma dirichlet_conductance_perm_le (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) (ω : Configuration d) (g : Vertex d → ℝ) :
    (issuedNetwork U).conductance (domainWeights (permConfiguration σ ω)) (fullBoundary U)
        (fun x => g (permVertex σ x.val)) ≤
      (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (fun x => g x.val) := by
  obtain ⟨v, hv, he⟩ := exists_global_dirichlet_minimizer U ω g
  calc
    _ ≤ issuedEnergy U (permConfiguration σ ω) (fun x => v (permVertex σ x)) :=
      conductance_le_global_energy U (permConfiguration σ ω) (fun x => g (permVertex σ x))
        (fun x => v (permVertex σ x))
        (fun x hx => hv _ (boundarySites_perm_mem σ (sitesPlus_perm_iff σ hU) hx))
    _ = issuedEnergy U ω v := issuedEnergy_perm σ hU ω v
    _ = _ := he

theorem dirichlet_conductance_perm (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) (ω : Configuration d) (g : Vertex d → ℝ) :
    (issuedNetwork U).conductance (domainWeights (permConfiguration σ ω)) (fullBoundary U)
        (fun x => g (permVertex σ x.val)) =
      (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (fun x => g x.val) := by
  apply le_antisymm (dirichlet_conductance_perm_le σ hU ω g)
  have h := dirichlet_conductance_perm_le σ.symm (perm_symm_invariant σ hU)
    (permConfiguration σ ω) (fun x => g (permVertex σ x))
  simpa only [permConfiguration_symm_cancel, permVertex_apply_symm] using h

/-- Quenched coordinate-permutation covariance of the full conductivity. -/
theorem fullConductivity_perm (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) (i : Fin d) (ω : Configuration d) :
    fullConductivity U i (permConfiguration σ ω) = fullConductivity U (σ i) ω := by
  have h := dirichlet_conductance_perm σ hU ω (fun y => (y (σ i) : ℝ))
  have hg : (fun x : DomainVertex U => ((permVertex σ x.val) (σ i) : ℝ)) =
      coordinateData i := by
    funext x
    simp [permVertex, coordinateData]
  rw [hg] at h
  unfold fullConductivity
  exact congrArg (fun r : ℝ => r / U.card) h

/-- The annealed conductivity of a permutation-invariant set does not depend
on the axis within an orbit. -/
theorem annealedFull_perm (σ : Equiv.Perm (Fin d)) {U : Finset (Vertex d)}
    (hU : ∀ x, permVertex σ x ∈ U ↔ x ∈ U) (i : Fin d) (p : unitInterval) :
    annealedFull U i (p : ℝ) = annealedFull U (σ i) (p : ℝ) := by
  rw [annealedFull_eq_integral, annealedFull_eq_integral]
  have h : ∀ ω, fullConductivity U (σ i) ω = fullConductivity U i (permConfiguration σ ω) :=
    fun ω => (fullConductivity_perm σ hU i ω).symm
  simp_rw [h]
  have hm := measurable_permConfiguration (d := d) σ
  have hf := (integrable_fullConductivity U i p).aestronglyMeasurable
  rw [← percolation_map_perm σ p] at hf
  rw [← integral_map hm.aemeasurable hf, percolation_map_perm]

lemma centeredBox_perm (σ : Equiv.Perm (Fin d)) (r : ℕ) (x : Vertex d) :
    permVertex σ x ∈ centeredBox d r ↔ x ∈ centeredBox d r := by
  rw [mem_centeredBox, mem_centeredBox]
  constructor
  · intro h j
    have hj := h (σ j)
    simpa [permVertex] using hj
  · intro h j
    exact h (σ.symm j)

/-- **Isotropy of the annealed conductivity of a centered box.** -/
theorem annealedFull_centeredBox_axis (r : ℕ) (i j : Fin d) (p : unitInterval) :
    annealedFull (centeredBox d r) i (p : ℝ) = annealedFull (centeredBox d r) j (p : ℝ) := by
  have h := annealedFull_perm (Equiv.swap i j) (centeredBox_perm (Equiv.swap i j) r) i p
  rwa [Equiv.swap_apply_left] at h

end NearCritical
