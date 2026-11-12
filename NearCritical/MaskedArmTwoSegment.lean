module

public import NearCritical.MaskedArmOneCutBound
public import NearCritical.MaskedArmUpperCutDecay

@[expose] public section
namespace NearCritical
open MeasureTheory

/-- The two-segment estimate with the mixed slab bound substituted at the
actual strict upper cut. -/
theorem maskedWaterCube_two_segment_decay {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (r R : ℕ) (δ : ℝ) (p q P : unitInterval)
      (x : DomainVertex (waterCube d i r R)),
      let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
      let n : ℤ := (2*r+1 : ℤ)-m-1
      let k := x.val i+(r : ℤ)
      x.val ∈ waterCube d i r R → 0 ≤ m → 0 ≤ n → 0 ≤ k → k ≤ n →
      q ≤ p → q ≤ criticalPoint d → (P : ℝ) < 1 → p ≤ P →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+(((2*r+1 : ℕ) : ℝ)^2)⁻¹ →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(((m : ℝ)+1)*((n : ℝ)+1)) →
      (bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).real
        (latticeBoundaryConnectionEvent (waterCube d i r R) x
          (positiveFace (waterCube d i r R) i)) ≤
        C*Real.exp (-C⁻¹*twoPhaseSlabDistance m k n*
          Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))) *
          (Co/(2*(r : ℝ)+1-(n : ℝ))^2) := by
  obtain ⟨C, ε, hC, hε, hdecay⟩ :=
    maskedWaterCube_upper_cut_decay i hB hb hpc hpc1 pioneers
  refine ⟨C, ε, hC, hε, ?_⟩
  intro r R δ p q P x
  dsimp only
  intro hx hm hn hk hkn hqp hq hP hpP hp hwindow
  let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
  let n : ℤ := (2*r+1 : ℤ)-m-1
  have hnH : n < 2*(r : ℤ)+1 := by dsimp [n, m]; omega
  refine (maskedWaterCube_one_cut_bound ordinary i r R δ p q P hqp hP hpP
    hp x hx n hn hkn hnH).trans ?_
  exact mul_le_mul_of_nonneg_right
    (hdecay r R δ p q x.val hm hn hk hkn hq hwindow)
    (div_nonneg hCo (sq_nonneg _))

end NearCritical
