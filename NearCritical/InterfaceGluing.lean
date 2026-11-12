module

public import NearCritical.IssuedPartition
public import Mathlib.Tactic.Linarith

/-! The interface energy cost in the boundary comparison of Section 3.
The geometry and number of interfaces are kept explicit. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

/-- Issued edges whose endpoints are assigned to different tiles. -/
def interfaceBonds {d : ℕ} {I : Type*} [DecidableEq I]
    (U : Finset (Vertex d)) (owner : Vertex d → I) : Finset (Bond d) := by
  classical
  exact (issuedBondSet U).filter (fun e => owner (bondTip e) ≠ owner e.1)

def patchedPotential {d : ℕ} {I : Type*} (owner : Vertex d → I)
    (v : I → Vertex d → ℝ) (x : Vertex d) : ℝ := v (owner x) x

/-- On a tile, every edge except an interface has exactly its original energy.
At an interface the common potential range gives a squared-height bound. -/
theorem issuedEnergy_patch_le {d : ℕ} {I : Type*} [DecidableEq I]
    (U : Finset (Vertex d)) (owner : Vertex d → I) (v : I → Vertex d → ℝ)
    (j : I) (ω : Configuration d) (a b : ℝ) (_hab : a ≤ b)
    (howner : ∀ x ∈ U, owner x = j)
    (hrange : ∀ x ∈ sitesPlus U, a ≤ patchedPotential owner v x ∧
      patchedPotential owner v x ≤ b) :
    issuedEnergy U ω (patchedPotential owner v) ≤ issuedEnergy U ω (v j) +
      (b - a)^2 * (interfaceBonds U owner).card := by
  classical
  have he : ∀ e ∈ issuedBondSet U,
      (if ω e then (1 : ℝ) else 0) *
          (patchedPotential owner v (bondTip e) - patchedPotential owner v e.1)^2 ≤
      (if ω e then (1 : ℝ) else 0) * (v j (bondTip e) - v j e.1)^2 +
        (if owner (bondTip e) ≠ owner e.1 then (b-a)^2 else 0) := by
    intro e he
    have hx := (mem_product.mp he).1
    have ho := howner e.1 hx
    by_cases hc : owner (bondTip e) = owner e.1
    · simp [patchedPotential, hc, ho]
    · have ht := hrange (bondTip e) (tip_mem_sitesPlus hx e.2)
      have hb := hrange e.1 (base_mem_sitesPlus hx)
      have hs : (patchedPotential owner v (bondTip e) -
          patchedPotential owner v e.1)^2 ≤ (b-a)^2 := by
        nlinarith [sq_nonneg (b-a - (patchedPotential owner v (bondTip e) -
          patchedPotential owner v e.1)),
          sq_nonneg (b-a + (patchedPotential owner v (bondTip e) -
          patchedPotential owner v e.1))]
      rw [ite_eq_left hc]
      cases ω e <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_mul,
        one_mul] <;> nlinarith [sq_nonneg (v j (bondTip e) - v j e.1)]
  calc
    _ ≤ ∑ e ∈ issuedBondSet U,
        ((if ω e then (1 : ℝ) else 0) * (v j (bondTip e) - v j e.1)^2 +
          (if owner (bondTip e) ≠ owner e.1 then (b-a)^2 else 0)) :=
      sum_le_sum he
    _ = _ := by
      rw [sum_add_distrib]
      congr 1
      rw [← sum_filter]
      simp [interfaceBonds, mul_comm]

/-- The patch estimate on an arbitrary disjoint finite tiling. No agreement of
neighboring local potentials is required. -/
theorem issuedEnergy_patch_partition_le {d : ℕ} {I : Type*} [DecidableEq I]
    (s : Finset I) (U : I → Finset (Vertex d))
    (hd : (s : Set I).PairwiseDisjoint U)
    (owner : Vertex d → I) (v : I → Vertex d → ℝ)
    (ω : Configuration d) (a b : ℝ) (hab : a ≤ b)
    (howner : ∀ j ∈ s, ∀ x ∈ U j, owner x = j)
    (hrange : ∀ j ∈ s, ∀ x ∈ sitesPlus (U j),
      a ≤ patchedPotential owner v x ∧ patchedPotential owner v x ≤ b) :
    issuedEnergy (s.biUnion U) ω (patchedPotential owner v) ≤
      (∑ j ∈ s, issuedEnergy (U j) ω (v j)) +
        (b-a)^2 * ∑ j ∈ s, ((interfaceBonds (U j) owner).card : ℝ) := by
  classical
  rw [issuedEnergy_biUnion s U hd]
  calc
    _ ≤ ∑ j ∈ s, (issuedEnergy (U j) ω (v j) +
        (b-a)^2 * (interfaceBonds (U j) owner).card) :=
      sum_le_sum (fun j hj => issuedEnergy_patch_le (U j) owner v j ω a b hab
        (howner j hj) (hrange j hj))
    _ = _ := by rw [sum_add_distrib, mul_sum]

/-- If the patch has the full outer boundary data, the same explicit interface
cost bounds the actual full-Dirichlet finite-volume conductivity. -/
theorem fullConductivity_patch_partition_le {d : ℕ} {I : Type*} [DecidableEq I]
    (s : Finset I) (U : I → Finset (Vertex d))
    (hd : (s : Set I).PairwiseDisjoint U)
    (owner : Vertex d → I) (v : I → Vertex d → ℝ)
    (ω : Configuration d) (i : Fin d) (a b : ℝ) (hab : a ≤ b)
    (howner : ∀ j ∈ s, ∀ x ∈ U j, owner x = j)
    (hrange : ∀ j ∈ s, ∀ x ∈ sitesPlus (U j),
      a ≤ patchedPotential owner v x ∧ patchedPotential owner v x ≤ b)
    (hboundary : ∀ x : DomainVertex (s.biUnion U), x ∈ fullBoundary (s.biUnion U) →
      patchedPotential owner v x.val = coordinateData i x) :
    fullConductivity (s.biUnion U) i ω ≤
      ((∑ j ∈ s, issuedEnergy (U j) ω (v j)) +
        (b-a)^2 * ∑ j ∈ s, ((interfaceBonds (U j) owner).card : ℝ)) /
          (s.biUnion U).card := by
  have he := (issuedNetwork (s.biUnion U)).conductance_le_energy
    (domainWeights_nonneg ω) hboundary
  rw [← issuedEnergy_eq_network] at he
  exact div_le_div_of_nonneg_right
    (he.trans (issuedEnergy_patch_partition_le s U hd owner v ω a b hab howner hrange))
    (Nat.cast_nonneg _)

end NearCritical
