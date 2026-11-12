module

public import NearCritical.MaskedArmCutBounds

@[expose] public section
namespace NearCritical

/-- The rounded upper cut preserves macroscopic exponential decay for
both the lower cut start and every start above it in the lower half. -/
theorem maskedArm_middle_exp_le {δ a s : ℝ} {H : ℕ} {k : ℤ}
    (ha : 0 ≤ a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hk : 2*k ≤ (H : ℤ))
    (hmk : ⌊δ*(H : ℝ)/2⌋ ≤ k)
    (hkn : k ≤ (H : ℤ)-⌊δ*(H : ℝ)/2⌋-1) :
    let m : ℤ := ⌊δ*(H : ℝ)/2⌋
    let n : ℤ := (H : ℤ)-m-1
    Real.exp (-a*twoPhaseSlabDistance m k n*s) ≤
      Real.exp a*Real.exp (-(a*(1-δ)/2)*(H : ℝ)*s) := by
  dsimp only
  let m : ℤ := ⌊δ*(H : ℝ)/2⌋
  let n : ℤ := (H : ℤ)-m-1
  have hmn : m ≤ n := hmk.trans hkn
  have hnR : ((n-m).toNat : ℝ) = (n : ℝ)-(m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hmn)
  have hkR : ((k-m).toNat : ℝ) = (k : ℝ)-(m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hmk)
  have hd : twoPhaseSlabDistance m k n = (n : ℝ)-(k : ℝ) := by
    have hle : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    rw [twoPhaseSlabDistance, hnR, hkR, show
      (n : ℝ)-(m : ℝ)-((k : ℝ)-(m : ℝ)) = (n : ℝ)-(k : ℝ) by ring,
      abs_of_nonneg (sub_nonneg.mpr hle)]
  have hgap : (1-δ)*(H : ℝ)/2-1 ≤ twoPhaseSlabDistance m k n := by
    rw [hd]
    exact maskedArm_upper_cut_separation δ H k hk
  have h := maskedArm_exp_one_layer_loss ha hs0 hs1 hgap
  change Real.exp (-a*twoPhaseSlabDistance m k n*s) ≤
    Real.exp a*Real.exp (-(a*(1-δ)/2)*(H : ℝ)*s)
  rwa [show -a*s*twoPhaseSlabDistance m k n = -a*twoPhaseSlabDistance m k n*s by ring,
    show -a*s*((1-δ)*(H : ℝ)/2) = -(a*(1-δ)/2)*(H : ℝ)*s by ring] at h

/-- One constant absorbs the finite range of small heights and normalizes
the exponential rate at large heights. -/
theorem maskedArm_close_scales {A c H₀ : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hH₀ : 1 ≤ H₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H k s u : ℝ}, 0 < H → 0 ≤ k → 0 ≤ s → s ≤ 1 →
      u ≤ 1 →
      (H₀ ≤ H → u ≤ A*(k+1)/H^3*Real.exp (-c*H*s)) →
      u ≤ C*(k+1)/H^3*Real.exp (-H*s/C) := by
  have hH₀pos : 0 < H₀ := zero_lt_one.trans_le hH₀
  let M := H₀^3*Real.exp H₀
  let C := 1+A+1/c+M
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcinv : 0 ≤ 1/c := by positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hMC : M ≤ C := by dsimp [C]; linarith
  have hrate : 1/C ≤ c := by
    apply (div_le_iff₀ hC).mpr
    have h : 1/c ≤ C := by dsimp [C]; linarith
    have h' := (div_le_iff₀ hc).mp h
    simpa only [mul_comm] using h'
  refine ⟨C,hC,?_⟩
  intro H k s u hH hk hs hs1 hu hlarge
  have hkp : 0 ≤ k+1 := by linarith
  by_cases hcut : H₀ ≤ H
  · apply (hlarge hcut).trans
    refine mul_le_mul ?_ ?_ (Real.exp_nonneg _) (by positivity)
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hkp) (by positivity)
    · apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hrate (mul_nonneg hH.le hs)
      calc
        -c*H*s = -(c*(H*s)) := by ring
        _ ≤ -((1/C)*(H*s)) := neg_le_neg h
        _ = -H*s/C := by ring
  · apply hu.trans
    have hHH₀ : H ≤ H₀ := (lt_of_not_ge hcut).le
    have hexp : Real.exp (-H₀) ≤ Real.exp (-H*s/C) := by
      apply Real.exp_le_exp.mpr
      have hHs : H*s ≤ H₀ := (mul_le_of_le_one_right hH.le hs1).trans hHH₀
      have hCC := mul_le_mul_of_nonneg_left hC1 hH₀pos.le
      have hdiv : H*s/C ≤ H₀ := (div_le_iff₀ hC).mpr (by linarith)
      rw [show -H*s/C = -(H*s/C) by ring]
      exact neg_le_neg hdiv
    have hHpow : H^3 ≤ H₀^3 := pow_le_pow_left₀ hH.le hHH₀ 3
    have hcancel : M*Real.exp (-H₀) = H₀^3 := by
      rw [show M = H₀^3*Real.exp H₀ from rfl, mul_assoc,
        ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hprod : H^3 ≤ C*Real.exp (-H*s/C) := calc
      H^3 ≤ H₀^3 := hHpow
      _ = M*Real.exp (-H₀) := hcancel.symm
      _ ≤ _ := mul_le_mul hMC hexp (Real.exp_nonneg _) hC.le
    have hnorm : 1 ≤ C*Real.exp (-H*s/C)/H^3 := by
      apply (le_div_iff₀ (pow_pos hH 3)).mpr
      simpa only [one_mul] using hprod
    refine hnorm.trans ?_
    have hbase := mul_le_mul_of_nonneg_left
      (show 1 ≤ k+1 by linarith) (show 0 ≤ C*Real.exp (-H*s/C)/H^3 by positivity)
    convert hbase using 1 <;> ring

end NearCritical
