module

public import NearCritical.Bernoulli
public import NearCritical.Minimizer
public import Mathlib.Data.Fintype.Pi

/-! The paper's issued edges E⁺(U), enlarged vertex set U⁺, and the two distinct
Dirichlet boundary conditions. Energies use precisely one positive-coordinate
edge for each base point of U and each coordinate. -/
@[expose] public section
namespace NearCritical
open Finset

noncomputable def sitesPlus {d : ℕ} (U : Finset (Vertex d)) : Finset (Vertex d) := by
  classical
  exact U ∪ U.biUnion (fun x ↦ univ.image (fun i : Fin d ↦ bondTip (x, i)))

lemma base_mem_sitesPlus {d : ℕ} {U : Finset (Vertex d)} {x : Vertex d} (hx : x ∈ U) :
    x ∈ sitesPlus U := by
  classical
  exact mem_union_left _ hx

lemma tip_mem_sitesPlus {d : ℕ} {U : Finset (Vertex d)} {x : Vertex d}
    (hx : x ∈ U) (i : Fin d) : bondTip (x, i) ∈ sitesPlus U := by
  classical
  exact mem_union_right _ (mem_biUnion.mpr ⟨x, hx, mem_image.mpr ⟨i, mem_univ i, rfl⟩⟩)

abbrev DomainVertex {d : ℕ} (U : Finset (Vertex d)) := ↥(sitesPlus U)
noncomputable def issuedBondSet {d : ℕ} (U : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact U.product univ

abbrev IssuedBond {d : ℕ} (U : Finset (Vertex d)) := ↥(issuedBondSet U)

def issuedBond {d : ℕ} {U : Finset (Vertex d)} (e : IssuedBond U) : Bond d := e.val

noncomputable def issuedNetwork {d : ℕ} (U : Finset (Vertex d)) :
    Network (DomainVertex U) (IssuedBond U) where
  tail e := ⟨e.val.1, base_mem_sitesPlus (mem_product.mp e.property).1⟩
  head e := ⟨bondTip (issuedBond e), tip_mem_sitesPlus (mem_product.mp e.property).1 e.val.2⟩

/-- The inner vertex boundary of the enlarged vertex support. -/
noncomputable def boundarySites {d : ℕ} (S : Finset (Vertex d)) : Finset (Vertex d) := by
  classical
  exact S.filter (fun x ↦ ∃ y, y ∉ S ∧ (openGraph (fun _ ↦ true)).Adj x y)

noncomputable def fullBoundary {d : ℕ} (U : Finset (Vertex d)) : Set (DomainVertex U) :=
  {x | x.val ∈ boundarySites (sitesPlus U)}

/-- The union of the two extreme-coordinate faces in equation `eq.def.TopBottom`.
The boundary is taken in U⁺, as in the source, not in U. -/
noncomputable def twoFaceBoundary {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    Set (DomainVertex U) :=
  {x | x ∈ fullBoundary U ∧
    ((∀ y ∈ sitesPlus U, y i ≤ x.val i) ∨ (∀ y ∈ sitesPlus U, x.val i ≤ y i))}

lemma twoFaceBoundary_subset {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    twoFaceBoundary U i ⊆ fullBoundary U := fun _ hx ↦ hx.1

def coordinateData {d : ℕ} {U : Finset (Vertex d)} (i : Fin d) (x : DomainVertex U) : ℝ :=
  (x.val i : ℝ)

def domainWeights {d : ℕ} {U : Finset (Vertex d)} (ω : Configuration d) : IssuedBond U → ℝ :=
  fun e ↦ if ω (issuedBond e) then 1 else 0

lemma domainWeights_nonneg {d : ℕ} {U : Finset (Vertex d)} (ω : Configuration d) (e : IssuedBond U) :
    0 ≤ domainWeights ω e := by
  unfold domainWeights
  split <;> norm_num

/-- Full Dirichlet conductivity (the A₁₁ quantity of Section 3). -/
noncomputable def fullConductivity {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) : ℝ :=
  (issuedNetwork U).conductance (domainWeights ω) (fullBoundary U) (coordinateData i) / U.card

/-- Two-face conductivity (the relaxed quantity a(U) of `eq.def.aU`). -/
noncomputable def relaxedConductivity {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) : ℝ :=
  (issuedNetwork U).conductance (domainWeights ω) (twoFaceBoundary U i) (coordinateData i) / U.card

/-- The quenched boundary-relaxation comparison on the actual lattice domains. -/
theorem relaxedConductivity_le_full {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) : relaxedConductivity U i ω ≤ fullConductivity U i ω := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg U.card)
  exact (issuedNetwork U).conductance_boundary_mono (domainWeights_nonneg ω)
    (twoFaceBoundary_subset U i) (coordinateData i)

/-- Existence of the minimizer used in equation `eq.def.aU`. -/
theorem exists_relaxed_minimizer {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) :
    ∃ u, (issuedNetwork U).IsMinimizer (domainWeights ω) (twoFaceBoundary U i) (coordinateData i) u := by
  classical
  exact (issuedNetwork U).exists_minimizer (domainWeights_nonneg ω) _ _

/-- Odd-side boxes: radius r corresponds to the paper's side length 2r+1. -/
noncomputable def centeredBox (d r : ℕ) : Finset (Vertex d) := by
  classical
  exact Fintype.piFinset (fun _ : Fin d ↦ Finset.Icc (-(r : ℤ)) (r : ℤ))

lemma mem_centeredBox {d r : ℕ} {x : Vertex d} :
    x ∈ centeredBox d r ↔ ∀ i, -(r : ℤ) ≤ x i ∧ x i ≤ (r : ℤ) := by
  classical
  simp [centeredBox, Fintype.mem_piFinset]

lemma sitesPlus_coordinate_bounds {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {lo hi : ℤ} (hU : ∀ x ∈ U, lo ≤ x i ∧ x i ≤ hi) :
    ∀ y ∈ sitesPlus U, lo ≤ y i ∧ y i ≤ hi + 1 := by
  classical
  intro y hy
  obtain hy | hy := mem_union.mp hy
  · exact ⟨(hU y hy).1, (hU y hy).2.trans (by omega)⟩
  · obtain ⟨x, hx, hy⟩ := mem_biUnion.mp hy
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    have hb := hU x hx
    by_cases hij : i = j
    · subst j
      simp only [bondTip, Function.update_self]
      omega
    · simp only [bondTip, Function.update_of_ne hij]
      omega

/-- The maximum-principle gradient bound for the paper's odd-side cubes. -/
theorem exists_box_relaxed_minimizer_bounded (d r : ℕ) (i : Fin d) (ω : Configuration d) :
    ∃ u, (issuedNetwork (centeredBox d r)).IsMinimizer (domainWeights ω)
      (twoFaceBoundary (centeredBox d r) i) (coordinateData i) u ∧
      ∀ e, |(issuedNetwork (centeredBox d r)).gradient u e| ≤ (2 * (r : ℝ) + 1) := by
  classical
  have hb : ∀ x : DomainVertex (centeredBox d r),
      coordinateData i x ∈ Set.Icc (-(r : ℝ)) ((r : ℝ) + 1) := by
    intro x
    have hx := sitesPlus_coordinate_bounds (centeredBox d r) i
      (fun y hy ↦ (mem_centeredBox.mp hy) i) x.val x.property
    constructor
    · dsimp only [coordinateData]
      exact_mod_cast hx.1
    · dsimp only [coordinateData]
      exact_mod_cast hx.2
  obtain ⟨u, hu, hbound⟩ := (issuedNetwork (centeredBox d r)).exists_minimizer_in_Icc
    (domainWeights_nonneg ω) (twoFaceBoundary (centeredBox d r) i) (coordinateData i)
    (show -(r : ℝ) ≤ (r : ℝ) + 1 by have := Nat.cast_nonneg (α := ℝ) r; linarith) (fun x _ ↦ hb x)
  refine ⟨u, hu, ?_⟩
  intro e
  have h := (issuedNetwork (centeredBox d r)).gradient_abs_le_of_range hbound e
  linarith

end NearCritical
