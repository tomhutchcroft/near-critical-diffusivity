module

public import NearCritical.InterfaceRectangleCount
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The normalized interface cost for rectangular patches. The actual tiling,
local potentials and outer boundary data remain explicit geometric inputs. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

theorem fullConductivity_rectangular_patch_le {d : ℕ} {I : Type*} [DecidableEq I]
    (s : Finset I) (lo hi : I → Vertex d)
    (hv : ∀ j ∈ s, ∀ k, lo j k ≤ hi j k)
    (hd : (s : Set I).PairwiseDisjoint (fun j => latticeRectangle (lo j) (hi j)))
    (owner : Vertex d → I) (v : I → Vertex d → ℝ)
    (ω : Configuration d) (i : Fin d) (L : ℕ) (hL : 0 < L)
    (hwidth : ∀ j ∈ s, ∀ k, k ≠ i → (Icc (lo j k) (hi j k)).card = L)
    (a b : ℝ) (hab : a ≤ b)
    (ho : ∀ j ∈ s, ∀ x ∈ latticeRectangle (lo j) (hi j), owner x = j)
    (hiowner : ∀ j ∈ s, ∀ x ∈ latticeRectangle (lo j) (hi j),
      owner (bondTip (x,i)) = owner x)
    (hrange : ∀ j ∈ s, ∀ x ∈ sitesPlus (latticeRectangle (lo j) (hi j)),
      a ≤ patchedPotential owner v x ∧ patchedPotential owner v x ≤ b)
    (hT : (s.biUnion (fun j => latticeRectangle (lo j) (hi j))).Nonempty)
    (hboundary : ∀ x : DomainVertex (s.biUnion (fun j => latticeRectangle (lo j) (hi j))),
      x ∈ fullBoundary (s.biUnion (fun j => latticeRectangle (lo j) (hi j))) →
      patchedPotential owner v x.val = coordinateData i x) :
    fullConductivity (s.biUnion (fun j => latticeRectangle (lo j) (hi j))) i ω ≤
      (∑ j ∈ s, issuedEnergy (latticeRectangle (lo j) (hi j)) ω (v j)) /
        (s.biUnion (fun j => latticeRectangle (lo j) (hi j))).card +
          (b-a)^2 * (d-1 : ℕ) / L := by
  classical
  let U := fun j => latticeRectangle (lo j) (hi j)
  let T := s.biUnion U
  have hc : (∑ j ∈ s, (interfaceBonds (U j) owner).card) * L ≤ (d-1) * T.card := by
    rw [sum_mul, card_biUnion hd, mul_sum]
    exact sum_le_sum (fun j hj => card_interfaceBonds_rectangle_mul_width_le
      (lo j) (hi j) (hv j hj) owner j i L (hwidth j hj) (ho j hj) (hiowner j hj))
  have hcR : (∑ j ∈ s, ((interfaceBonds (U j) owner).card : ℝ)) * (L : ℝ) ≤
      (d-1 : ℕ) * (T.card : ℝ) := by exact_mod_cast hc
  have ht : (0 : ℝ) < T.card := by exact_mod_cast card_pos.mpr hT
  have hl : (0 : ℝ) < L := by exact_mod_cast hL
  have hratio : (∑ j ∈ s, ((interfaceBonds (U j) owner).card : ℝ)) / T.card ≤
      (d-1 : ℕ) / (L : ℝ) := (div_le_div_iff₀ ht hl).mpr hcR
  calc
    _ ≤ ((∑ j ∈ s, issuedEnergy (U j) ω (v j)) +
        (b-a)^2 * ∑ j ∈ s, ((interfaceBonds (U j) owner).card : ℝ)) / T.card :=
      fullConductivity_patch_partition_le s U hd owner v ω i a b hab ho hrange hboundary
    _ = (∑ j ∈ s, issuedEnergy (U j) ω (v j)) / T.card +
        (b-a)^2 * ((∑ j ∈ s, ((interfaceBonds (U j) owner).card : ℝ)) / T.card) := by ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hratio (sq_nonneg (b-a))

end NearCritical
