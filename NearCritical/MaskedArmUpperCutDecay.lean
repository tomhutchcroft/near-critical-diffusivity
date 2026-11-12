module

public import NearCritical.MaskedArmRealMass
public import NearCritical.TwoPhaseSlabNearCritical

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- The upper-cut sum inherits exponential decay with no remaining-height
factor, since the target plane is the top of the normalized slab. -/
theorem maskedWaterCube_upper_cut_decay {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (r R : ℕ) (δ : ℝ) (p q : unitInterval) (x : Vertex d),
      let U := waterCube d i r R
      let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
      let n : ℤ := (2*r+1 : ℤ)-m-1
      let k := x i+(r : ℤ)
      0 ≤ m → 0 ≤ n → 0 ≤ k → k ≤ n → q ≤ criticalPoint d →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(((m : ℝ)+1)*((n : ℝ)+1)) →
      (∑ y ∈ U.filter (fun y => y i+(r : ℤ)=n),
        (bulkPercolation U i (2*(r : ℝ)+1) δ p q).real
          (connectionToSetEvent ((U : Set (Vertex d)) ∩
            finiteHeightSlab i (-(r : ℤ)) (n-r)) x {y})) ≤
        C*Real.exp (-C⁻¹*twoPhaseSlabDistance m k n*
          Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))) := by
  obtain ⟨C, ε, hC, hε, hmass⟩ :=
    twoPhaseSlabPioneerMass_nearCritical i hB hb hpc hpc1 pioneers
  refine ⟨C, ε, hC, hε, ?_⟩
  intro r R δ p q x
  dsimp only
  intro hm hn hk hkn hq hp
  let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
  let n : ℤ := (2*r+1 : ℤ)-m-1
  let k := x i+(r : ℤ)
  have hm' : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  have hmR : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hm'
  have hnR : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hn'
  have hp' : (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/((m.toNat+1 : ℝ)*(n.toNat+1 : ℝ)) := by
    simpa only [hmR, hnR] using hp
  have h := hmass q hq m.toNat n.toNat p hp'
    k (Finset.mem_Icc.mpr ⟨hk, by rw [hn']; exact hkn⟩)
    n (Finset.mem_Icc.mpr ⟨hn, by rw [hn']⟩)
  rw [hm', hn', hnR, show (n : ℝ)+1-(n : ℝ) = 1 by ring, mul_one] at h
  exact maskedWaterCube_upper_cut_real_le i r R δ p q x (by positivity) h

end NearCritical
