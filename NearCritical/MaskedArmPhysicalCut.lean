module

public import NearCritical.MaskedArmCutMass

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- The finite upper cut in physical coordinates is dominated by the
normalized two-phase pioneer mass at the strict upper bulk layer. -/
theorem maskedWaterCube_upper_cut_mass_le {d : ℕ} (i : Fin d)
    (r R : ℕ) (δ : ℝ) (p q : unitInterval) (x : Vertex d) :
    let U := waterCube d i r R
    let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
    let n : ℤ := (2*r+1 : ℤ)-m-1
    (∑ y ∈ U.filter (fun y => y i+(r : ℤ)=n),
      bulkPercolation U i (2*(r : ℝ)+1) δ p q
        (connectionToSetEvent ((U : Set (Vertex d)) ∩
          finiteHeightSlab i (-(r : ℤ)) (n-r)) x {y})) ≤
      twoPhaseSlabPioneerMass i p q m n (x i+(r : ℤ)) n := by
  dsimp only
  let U := waterCube d i r R
  let n : ℤ := (2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1
  let a : Vertex d := Pi.single i (-(r : ℤ))
  have ha : a i = -(r : ℤ) := Pi.single_eq_same i _
  let E : Vertex d ≃ Vertex d := Equiv.addLeft a
  let D : Set (Vertex d) := (U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)
  let S : Set (Vertex d) := E ⁻¹' D
  let W := U.filter (fun y => y i+(r : ℤ)=n)
  have hU : ∀ z ∈ S, a+z ∈ U := fun _ hz => hz.1
  have hS : S ⊆ finiteHeightSlab i 0 n := by
    intro z hz
    have hz' : -(r : ℤ) ≤ (a+z) i ∧ (a+z) i ≤ n-r := hz.2
    simp only [Pi.add_apply, ha] at hz'
    exact ⟨by omega, by omega⟩
  have hD : (fun z => a+z) '' S = D := E.surjective.image_preimage D
  have hcoord (y : Vertex d) : E.symm y i = y i+(r : ℤ) := by
    have h := congrFun (E.apply_symm_apply y) i
    change (a+E.symm y) i = y i at h
    simp only [Pi.add_apply, ha] at h
    omega
  have hj : ∀ y ∈ W.map E.symm.toEmbedding, y i = n := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact (hcoord v).trans (Finset.mem_filter.mp hv).2
  have h := maskedWaterCube_translated_cut_mass_le i r R δ p q a (E.symm x)
    ha n (W.map E.symm.toEmbedding) hj S hU hS
  rw [hD, Finset.sum_map] at h
  have he (y : Vertex d) : a+E.symm y = y := E.apply_symm_apply y
  simpa only [Equiv.toEmbedding_apply, he, hcoord, W, U, D, n] using h

end NearCritical
