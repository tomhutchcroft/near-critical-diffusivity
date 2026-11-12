module

public import NearCritical.HalfSlabNearCriticalBound
public import NearCritical.MaskedArmPrefixMass
public import NearCritical.MaskedArmCutBounds

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- The homogeneous prefix mass supplies the ratio of starting depth plus
one to lower cut height plus one. The shifted window covers a cut at zero. -/
theorem maskedArm_prefix_envelope {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (H : ℕ) (m k : ℤ) (p : unitInterval), 0 ≤ k → k ≤ m → m < (H : ℤ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(H : ℝ)^2 →
        slabPioneerMass p i 0 m k m ≤ ENNReal.ofReal (C*(((k : ℝ)+1)/((m : ℝ)+1))) := by
  obtain ⟨ε, C, c, hε, hC, hc, hend, hmass⟩ :=
    slabPioneerMass_half_boundary_ratio_of_weighted i hB hb hpc hpc1 pioneers
  refine ⟨ε, C, hε, hC, hend, ?_⟩
  intro H m k p hk hkm hmH hp
  have hm : 0 ≤ m := hk.trans hkm
  have hmN : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  have hmR : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hmN
  have hNR : (m.toNat : ℝ)+1 ≤ (H : ℝ) := by
    rw [hmR]
    exact_mod_cast (show m+1 ≤ (H : ℤ) by omega)
  have hNpos : 0 < (m.toNat : ℝ)+1 := by positivity
  have hp' : (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(m.toNat+1 : ℝ)^2 :=
    hp.trans (add_le_add_right (div_le_div_of_nonneg_left hε.le (sq_pos_of_pos hNpos)
      ((sq_le_sq₀ hNpos.le (hNpos.le.trans hNR)).mpr hNR)) _)
  have h := hmass m.toNat p hp' k (Finset.mem_Icc.mpr ⟨hk, by simpa only [hmN] using hkm⟩)
  rw [hmN, hmR] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hmR0 : 0 ≤ (m : ℝ) := by exact_mod_cast hm
  have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hexp : Real.exp (-c*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((m : ℝ)-(k : ℝ))) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
      (sub_nonneg.mpr hkmR)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
    (show 0 ≤ C*(((k : ℝ)+1)/((m : ℝ)+1)) by positivity)

/-- The same depth ratio bounds the actual finite lower-cut probability sum. -/
theorem maskedWaterCube_lower_cut_depth_ratio {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (r R : ℕ) (δ : ℝ) (p q : unitInterval) (x : Vertex d) (m : ℤ),
        q ≤ p → 0 ≤ x i+(r : ℤ) → x i+(r : ℤ) ≤ m → m < 2*(r : ℤ)+1 →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(2*(r : ℝ)+1)^2 →
        let U := waterCube d i r R
        (∑ y ∈ U.filter (fun y => y i+(r : ℤ)=m),
          (bulkPercolation U i (2*(r : ℝ)+1) δ p q).real
            (connectionToSetEvent ((U : Set (Vertex d)) ∩
              finiteHeightSlab i (-(r : ℤ)) (m-r)) x {y})) ≤
          C*(((x i : ℝ)+(r : ℝ)+1)/((m : ℝ)+1)) := by
  obtain ⟨ε, C, hε, hC, hend, hmass⟩ :=
    maskedArm_prefix_envelope i hB hb hpc hpc1 pioneers
  refine ⟨ε, C, hε, hC, hend, ?_⟩
  intro r R δ p q x m hqp hk hkm hmH hp
  have hmass' := hmass (2*r+1) m (x i+(r : ℤ)) p hk hkm
    (by exact_mod_cast hmH) (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using hp)
  have hkR : 0 ≤ (x i : ℝ)+(r : ℝ) := by exact_mod_cast hk
  have hmR : 0 ≤ (m : ℝ) := by exact_mod_cast hk.trans hkm
  apply maskedWaterCube_lower_cut_real_le i r R δ p q hqp x m (by positivity)
  simpa only [Int.cast_add, Int.cast_natCast] using hmass'

/-- Rounding the lower cut down still leaves its shifted height at least
half the bulk thickness. -/
theorem maskedArm_prefix_scale_le {δ C : ℝ} {H : ℕ} {k : ℤ}
    (hδ : 0 < δ) (hH : 0 < H) (hC : 0 ≤ C) (hk : 0 ≤ k) :
    let m : ℤ := ⌊δ*(H : ℝ)/2⌋
    C*(((k : ℝ)+1)/((m : ℝ)+1)) ≤ (2*C/δ)*((k : ℝ)+1)/(H : ℝ) := by
  dsimp only
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hcut := (maskedArm_cut_rounding δ H hδ.le).2.2.1
  have hpos : 0 < δ*(H : ℝ)/2 := by positivity
  calc
    _ ≤ C*(((k : ℝ)+1)/(δ*(H : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hpos hcut) hC
    _ = _ := by field_simp <;> ring

end NearCritical
