module

public import NearCritical.MaskedArmOneCutBound
public import NearCritical.MaskedArmPrefixMass
public import NearCritical.MaskedArmRealMass

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Combine the actual three-segment bound with homogeneous and two-phase
pioneer mass envelopes at the two cuts. -/
theorem maskedWaterCube_three_segment_le {d : ℕ} {Co A B : ℝ}
    (ordinary : OrdinaryArmWindowInput d Co) (hCo : 0 ≤ Co)
    (i : Fin d) (r R : ℕ) (δ : ℝ) (p q P : unitInterval)
    (hqp : q ≤ p) (hP : (P : ℝ) < 1) (hpP : p ≤ P)
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ)+(((2*r+1 : ℕ) : ℝ)^2)⁻¹)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
    let n : ℤ := (2*r+1 : ℤ)-m-1
    0 ≤ m → x.val i+(r : ℤ) ≤ m → m ≤ n → n < 2*(r : ℤ)+1 →
    slabPioneerMass p i 0 m (x.val i+(r : ℤ)) m ≤ ENNReal.ofReal A →
    twoPhaseSlabPioneerMass i p q m n m n ≤ ENNReal.ofReal B →
    (bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).real
      (latticeBoundaryConnectionEvent (waterCube d i r R) x
        (positiveFace (waterCube d i r R) i)) ≤ A*B*(Co/(2*(r : ℝ)+1-(n : ℝ))^2) := by
  dsimp only
  intro hm hxm hmn hnH hprefix hmiddle
  let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
  let n : ℤ := (2*r+1 : ℤ)-m-1
  let U := waterCube d i r R
  let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
  let W := U.filter (fun u => u i+(r : ℤ)=m)
  let V := U.filter (fun v => v i+(r : ℤ)=n)
  let f := fun u => μ.real (connectionToSetEvent
    ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (m-r)) x.val {u})
  let g := fun u v => μ.real (connectionToSetEvent
    ((U : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) u {v})
  have hf : (∑ u ∈ W, f u) ≤ A :=
    maskedWaterCube_lower_cut_real_le i r R δ p q hqp x.val m hA hprefix
  have hg (u : Vertex d) (hu : u ∈ W) : (∑ v ∈ V, g u v) ≤ B := by
    have hu' : u i+(r : ℤ) = m := (Finset.mem_filter.mp hu).2
    apply maskedWaterCube_upper_cut_real_le i r R δ p q u hB
    simpa only [hu', m, n] using hmiddle
  refine (maskedWaterCube_two_cut_bound ordinary i r R δ p q P hqp hP hpP
    hp x hx m n hm hxm hmn hnH).trans ?_
  apply mul_le_mul_of_nonneg_right _ (div_nonneg hCo (sq_nonneg _))
  calc
    (∑ u ∈ W, f u * (∑ v ∈ V, g u v)) ≤ ∑ u ∈ W, f u * B :=
      Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hg u hu) measureReal_nonneg
    _ ≤ A*B := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hf hB

end NearCritical
