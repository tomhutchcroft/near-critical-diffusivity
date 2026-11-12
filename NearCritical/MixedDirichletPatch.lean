module

public import NearCritical.InterfaceRectangularPatch

/-! Actual mixed local minimizers for the boundary-layer patch. The remaining
outer-boundary condition is expressed purely as membership in local faces. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

def mixedBoundary {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (full : Bool) :
    Set (DomainVertex U) := if full then fullBoundary U else twoFaceBoundary U i

theorem fullConductivity_mixed_rectangular_patch_le {d : ℕ} {I : Type*}
    [DecidableEq I] (s : Finset I) (lo hi : I → Vertex d)
    (hv : ∀ j ∈ s, ∀ k, lo j k ≤ hi j k)
    (hd : (s : Set I).PairwiseDisjoint (fun j => latticeRectangle (lo j) (hi j)))
    (owner : Vertex d → I) (full : I → Bool)
    (ω : Configuration d) (i : Fin d) (L : ℕ) (hL : 0 < L)
    (hwidth : ∀ j ∈ s, ∀ k, k ≠ i → (Icc (lo j k) (hi j k)).card = L)
    (a b : ℝ) (hab : a ≤ b)
    (ho : ∀ j ∈ s, ∀ x ∈ latticeRectangle (lo j) (hi j), owner x = j)
    (hiowner : ∀ j ∈ s, ∀ x ∈ latticeRectangle (lo j) (hi j),
      owner (bondTip (x,i)) = owner x)
    (hT : (s.biUnion (fun j => latticeRectangle (lo j) (hi j))).Nonempty)
    (hcoord : ∀ x ∈ sitesPlus (s.biUnion (fun j => latticeRectangle (lo j) (hi j))),
      (x i : ℝ) ∈ Set.Icc a b)
    (hfaces : ∀ (x : DomainVertex (s.biUnion (fun j => latticeRectangle (lo j) (hi j)))),
      x ∈ fullBoundary _ → ∀ _hj : owner x.val ∈ s,
      ∀ hx : x.val ∈ sitesPlus (latticeRectangle (lo (owner x.val)) (hi (owner x.val))),
      (⟨x.val,hx⟩ : DomainVertex _) ∈
        mixedBoundary _ i (full (owner x.val))) :
    fullConductivity (s.biUnion (fun j => latticeRectangle (lo j) (hi j))) i ω ≤
      (∑ j ∈ s, ((latticeRectangle (lo j) (hi j)).card : ℝ) *
        (if full j then fullConductivity (latticeRectangle (lo j) (hi j)) i ω
          else relaxedConductivity (latticeRectangle (lo j) (hi j)) i ω)) /
        (s.biUnion (fun j => latticeRectangle (lo j) (hi j))).card +
          (b-a)^2 * (d-1 : ℕ) / L := by
  classical
  let U := fun j => latticeRectangle (lo j) (hi j)
  let T := s.biUnion U
  have hloc : ∀ j : s, ∃ u : DomainVertex (U j.val) → ℝ,
      (issuedNetwork (U j.val)).IsMinimizer (domainWeights ω)
        (mixedBoundary (U j.val) i (full j.val)) (coordinateData i) u ∧
      ∀ x, u x ∈ Set.Icc a b := by
    intro j
    apply (issuedNetwork (U j.val)).exists_minimizer_in_Icc (domainWeights_nonneg ω)
      _ _ hab
    intro x _
    exact hcoord x.val (sitesPlus_mono (subset_biUnion_of_mem U j.property) x.property)
  choose u hu using hloc
  let fallback : Vertex d → ℝ := Network.clamp a b hab (fun x => (x i : ℝ))
  let v : I → Vertex d → ℝ := fun j x =>
    if hj : j ∈ s then
      if hx : x ∈ sitesPlus (U j) then u ⟨j,hj⟩ ⟨x,hx⟩ else fallback x
    else fallback x
  have hvrange : ∀ j x, v j x ∈ Set.Icc a b := by
    intro j x
    dsimp only [v]
    split_ifs with hj hx
    · exact (hu ⟨j,hj⟩).2 ⟨x,hx⟩
    · exact Network.clamp_mem a b hab _ x
    · exact Network.clamp_mem a b hab _ x
  have hboundary : ∀ x : DomainVertex T, x ∈ fullBoundary T →
      patchedPotential owner v x.val = coordinateData i x := by
    intro x hx
    have hf : fallback x.val = coordinateData i x :=
      Network.clamp_eq hab (hcoord x.val x.property)
    dsimp only [patchedPotential, v]
    split_ifs with hj hlocal
    · exact (hu ⟨owner x.val,hj⟩).1.1 _ (hfaces x hx hj hlocal)
    · exact hf
    · exact hf
  have henergy : ∀ j ∈ s, issuedEnergy (U j) ω (v j) =
      ((U j).card : ℝ) * (if full j then fullConductivity (U j) i ω
        else relaxedConductivity (U j) i ω) := by
    intro j hj
    have hr : (fun x : DomainVertex (U j) => v j x.val) = u ⟨j,hj⟩ := by
      funext x
      simp only [v, dite_eq_left hj, dite_eq_left x.property]
    rw [issuedEnergy_eq_network, hr,
      ← Network.IsMinimizer.conductance_eq _ (domainWeights_nonneg ω) (hu ⟨j,hj⟩).1]
    have hn : (U j).Nonempty := ⟨lo j, mem_latticeRectangle.mpr
      (fun k => ⟨le_rfl, hv j hj k⟩)⟩
    have hc : ((U j).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (card_pos.mpr hn)
    cases full j <;>
      simp [mixedBoundary, fullConductivity, relaxedConductivity, mul_div_cancel₀, hc]
  have hp := fullConductivity_rectangular_patch_le s lo hi hv hd owner v ω i L hL
    hwidth a b hab ho hiowner (fun j _ x _ => hvrange (owner x) x) hT hboundary
  have hsum : (∑ j ∈ s, issuedEnergy (U j) ω (v j)) =
      ∑ j ∈ s, ((U j).card : ℝ) * (if full j then fullConductivity (U j) i ω
        else relaxedConductivity (U j) i ω) := sum_congr rfl henergy
  change fullConductivity T i ω ≤
    (∑ j ∈ s, issuedEnergy (U j) ω (v j)) / T.card + (b-a)^2 * (d-1 : ℕ) / L at hp
  rw [hsum] at hp
  exact hp

end NearCritical
