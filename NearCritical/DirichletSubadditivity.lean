module

public import NearCritical.RectangleBoundary

/-! Actual minimizer gluing on disjoint lattice rectangles. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

/-- Extend the correction to the prescribed global data by zero off U+. -/
def extendDirichletCorrection {d : ℕ} (U : Finset (Vertex d))
    (g : Vertex d → ℝ) (u : DomainVertex U → ℝ) (x : Vertex d) : ℝ :=
  if hx : x ∈ sitesPlus U then u ⟨x,hx⟩ - g x else 0

lemma extendDirichletCorrection_boundary {d : ℕ} {U : Finset (Vertex d)}
    {g : Vertex d → ℝ} {u : DomainVertex U → ℝ}
    (hu : Network.admissible (fullBoundary U) (fun x => g x.val) u)
    {x : Vertex d} (hx : x ∈ boundarySites (sitesPlus U)) :
    extendDirichletCorrection U g u x = 0 := by
  classical
  have hm : x ∈ sitesPlus U := (Finset.mem_filter.mp hx).1
  simp only [extendDirichletCorrection, dite_eq_left hm]
  exact sub_eq_zero.mpr (hu ⟨x,hm⟩ hx)

/-- Full-boundary Dirichlet conductances are subadditive under a finite disjoint
rectangle partition. The boundary data may be any one global function. -/
theorem rectangle_dirichlet_subadditivity {d : ℕ} {I : Type*}
    (s : Finset I) (lo hi : I → Vertex d)
    (hd : (s : Set I).PairwiseDisjoint (fun j => latticeRectangle (lo j) (hi j)))
    (ω : Configuration d) (g : Vertex d → ℝ) :
    (issuedNetwork (s.biUnion (fun j => latticeRectangle (lo j) (hi j)))).conductance
      (domainWeights ω) (fullBoundary _) (fun x => g x.val) ≤
      ∑ j ∈ s, (issuedNetwork (latticeRectangle (lo j) (hi j))).conductance
        (domainWeights ω) (fullBoundary _) (fun x => g x.val) := by
  classical
  let U := fun j => latticeRectangle (lo j) (hi j)
  let T := s.biUnion U
  choose u hu using fun j : I =>
    (issuedNetwork (U j)).exists_minimizer (domainWeights_nonneg ω)
      (fullBoundary (U j)) (fun x => g x.val)
  let v : Vertex d → ℝ := fun x =>
    g x + ∑ j ∈ s, extendDirichletCorrection (U j) g (u j) x
  have hrestrict (j : I) (hj : j ∈ s) (x : DomainVertex (U j)) : v x.val = u j x := by
    have hsum : (∑ k ∈ s, extendDirichletCorrection (U k) g (u k) x.val) =
        extendDirichletCorrection (U j) g (u j) x.val := by
      apply Finset.sum_eq_single j
      · intro k hk hkj
        by_cases hxk : x.val ∈ sitesPlus (U k)
        · apply extendDirichletCorrection_boundary (hu k).1
          exact rectangle_overlap_mem_boundary
            (hd hk hj hkj) hxk x.property
        · simp [extendDirichletCorrection, hxk]
      · exact fun h => (h hj).elim
    dsimp only [v]
    rw [hsum]
    simp [extendDirichletCorrection, x.property]
  have hadm : Network.admissible (fullBoundary T) (fun x => g x.val)
      (fun x => v x.val) := by
    intro x hx
    change v x.val = g x.val
    dsimp only [v]
    have hzero : (∑ j ∈ s, extendDirichletCorrection (U j) g (u j) x.val) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hxj : x.val ∈ sitesPlus (U j)
      · apply extendDirichletCorrection_boundary (hu j).1
        exact boundarySites_of_subset
          (sitesPlus_mono (Finset.subset_biUnion_of_mem U hj)) hxj hx
      · simp [extendDirichletCorrection, hxj]
    rw [hzero, add_zero]
  calc
    _ ≤ (issuedNetwork T).energy (domainWeights ω) (fun x => v x.val) :=
      (issuedNetwork T).conductance_le_energy (domainWeights_nonneg ω) hadm
    _ = issuedEnergy T ω v := (issuedEnergy_eq_network T ω v).symm
    _ = ∑ j ∈ s, issuedEnergy (U j) ω v := issuedEnergy_biUnion s U hd ω v
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [issuedEnergy_eq_network]
      have he : (fun x : DomainVertex (U j) => v x.val) = u j :=
        funext (hrestrict j hj)
      rw [he]
      exact (Network.IsMinimizer.conductance_eq (issuedNetwork (U j))
        (domainWeights_nonneg ω) (hu j)).symm

/-- Source volume-weighted coordinate conductivity inequality for nonempty
rectangles, including the vacuous empty partition. -/
theorem fullConductivity_rectangle_subadditivity {d : ℕ} {I : Type*}
    (s : Finset I) (lo hi : I → Vertex d)
    (hvalid : ∀ j ∈ s, ∀ k, lo j k ≤ hi j k)
    (hd : (s : Set I).PairwiseDisjoint (fun j => latticeRectangle (lo j) (hi j)))
    (ω : Configuration d) (i : Fin d) :
    fullConductivity (s.biUnion (fun j => latticeRectangle (lo j) (hi j))) i ω ≤
      ∑ j ∈ s, ((latticeRectangle (lo j) (hi j)).card : ℝ) /
        (s.biUnion (fun j => latticeRectangle (lo j) (hi j))).card *
        fullConductivity (latticeRectangle (lo j) (hi j)) i ω := by
  classical
  let U := fun j => latticeRectangle (lo j) (hi j)
  let T := s.biUnion U
  have hb := rectangle_dirichlet_subadditivity s lo hi hd ω (fun x => (x i : ℝ))
  change fullConductivity T i ω ≤ ∑ j ∈ s, ((U j).card : ℝ) / T.card *
    fullConductivity (U j) i ω
  calc
    _ ≤ (∑ j ∈ s, (issuedNetwork (U j)).conductance (domainWeights ω)
        (fullBoundary (U j)) (coordinateData i)) / T.card :=
      div_le_div_of_nonneg_right hb (Nat.cast_nonneg T.card)
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hn : (U j).Nonempty := ⟨lo j, mem_latticeRectangle.mpr
        (fun k => ⟨le_rfl, hvalid j hj k⟩)⟩
      have hc : ((U j).card : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr hn))
      unfold fullConductivity
      by_cases ht : (T.card : ℝ) = 0
      · simp [ht]
      · field_simp

end NearCritical
