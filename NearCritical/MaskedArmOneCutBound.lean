module

public import NearCritical.MaskedWaterCubeArmReduction
public import NearCritical.MaskedArmSuffixCut

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- Pull the uniform suffix bound out of the actual one-cut probability sum. -/
theorem maskedWaterCube_one_cut_bound {d : ℕ} {Co : ℝ}
    (ordinary : OrdinaryArmWindowInput d Co) (i : Fin d) (r R : ℕ) (δ : ℝ)
    (p q P : unitInterval) (hqp : q ≤ p) (hP : (P : ℝ) < 1) (hpP : p ≤ P)
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ)+(((2*r+1 : ℕ) : ℝ)^2)⁻¹)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (n : ℤ) (hn : 0 ≤ n) (hxn : x.val i+(r : ℤ) ≤ n) (hnH : n < 2*(r : ℤ)+1) :
    let U := waterCube d i r R
    let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
    μ.real (latticeBoundaryConnectionEvent U x (positiveFace U i)) ≤
      (∑ v ∈ U.filter (fun v => v i+(r : ℤ)=n),
        μ.real (connectionToSetEvent
          ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) x.val {v})) *
        (Co/(2*(r : ℝ)+1-(n : ℝ))^2) := by
  dsimp only
  refine (maskedWaterCube_one_cut_probability_le i r R δ p q P hP hpP
    (hqp.trans hpP) x hx n hn hxn hnH).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro v hv
  obtain ⟨hvU, hvn⟩ := Finset.mem_filter.mp hv
  exact mul_le_mul_of_nonneg_left
    (maskedWaterCube_suffix_at_cut ordinary p q hqp i r R δ _ v hvU n hnH hvn hp)
    measureReal_nonneg

/-- At two cuts the same suffix estimate factors out of the inner sum.
The middle sum still depends on the lower cut vertex. -/
theorem maskedWaterCube_two_cut_bound {d : ℕ} {Co : ℝ}
    (ordinary : OrdinaryArmWindowInput d Co) (i : Fin d) (r R : ℕ) (δ : ℝ)
    (p q P : unitInterval) (hqp : q ≤ p) (hP : (P : ℝ) < 1) (hpP : p ≤ P)
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ)+(((2*r+1 : ℕ) : ℝ)^2)⁻¹)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (m n : ℤ) (hm : 0 ≤ m) (hxm : x.val i+(r : ℤ) ≤ m)
    (hmn : m ≤ n) (hnH : n < 2*(r : ℤ)+1) :
    let U := waterCube d i r R
    let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
    let A := fun u => connectionToSetEvent
      ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (m-r)) x.val {u}
    let B := fun u v => connectionToSetEvent
      ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) u {v}
    μ.real (latticeBoundaryConnectionEvent U x (positiveFace U i)) ≤
      (∑ u ∈ U.filter (fun u => u i+(r : ℤ)=m),
        μ.real (A u) * (∑ v ∈ U.filter (fun v => v i+(r : ℤ)=n), μ.real (B u v))) *
        (Co/(2*(r : ℝ)+1-(n : ℝ))^2) := by
  dsimp only
  refine (maskedWaterCube_two_cuts_probability_le i r R δ p q P hP hpP
    (hqp.trans hpP) x hx m n hm hxm hmn hnH).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro v hv
  obtain ⟨hvU, hvn⟩ := Finset.mem_filter.mp hv
  exact mul_le_mul_of_nonneg_left
    (maskedWaterCube_suffix_at_cut ordinary p q hqp i r R δ _ v hvU n hnH hvn hp)
    (mul_nonneg measureReal_nonneg measureReal_nonneg)

end NearCritical
