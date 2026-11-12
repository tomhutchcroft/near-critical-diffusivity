module

public import NearCritical.ExternalHalfSpaceComparison

/-! Uniform critical-window constant for the imported finite exploration/entropy
argument. Critical-point interior is an explicit input;
no all-dimensional critical-point theorem is asserted. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open MeasureTheory

/-- The source window uniformly separates the Bernoulli denominator from zero. -/
theorem entropic_window_denominator {r p : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hlo : r/2 ≤ p) (hhi : p ≤ (r+1)/2) :
    (r/2) * ((1-r)/2) ≤ p * (1-p) := by
  apply mul_le_mul hlo
  · linarith
  · linarith
  · linarith

/-- Factor the parameter difference and uniform window constant out of the
refined entropy square root. -/
theorem entropic_window_sqrt_bound {r p q M C N : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hlo : r/2 ≤ p) (hhi : p ≤ (r+1)/2)
    (hqp : q ≤ p) (hM : 0 ≤ M) (hC : 0 ≤ C) (hN : 0 ≤ N) :
    3 * Real.sqrt (M * (((q-p)^2 / (p*(1-p))) * (N*C))) ≤
      (3 * Real.sqrt (N / ((r/2)*((1-r)/2)))) * (p-q) * Real.sqrt (M*C) := by
  have hden0 : 0 < (r/2)*((1-r)/2) :=
    mul_pos (div_pos hr (by norm_num)) (div_pos (sub_pos.mpr hr1) (by norm_num))
  have hden := entropic_window_denominator hr hr1 hlo hhi
  have hratio : N / (p*(1-p)) ≤ N / ((r/2)*((1-r)/2)) :=
    div_le_div_of_nonneg_left hN hden0 hden
  have hbudget : M * (((q-p)^2 / (p*(1-p))) * (N*C)) ≤
      (p-q)^2 * ((N / ((r/2)*((1-r)/2))) * (M*C)) := by
    calc
      _ = (p-q)^2 * ((N / (p*(1-p))) * (M*C)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hratio (mul_nonneg hM hC)) (sq_nonneg _)
  have hfactor : Real.sqrt ((p-q)^2 * ((N / ((r/2)*((1-r)/2))) * (M*C))) =
      (p-q) * (Real.sqrt (N / ((r/2)*((1-r)/2))) * Real.sqrt (M*C)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sub_nonneg.mpr hqp),
      Real.sqrt_mul (div_nonneg hN hden0.le)]
  calc
    _ ≤ 3 * Real.sqrt ((p-q)^2 * ((N / ((r/2)*((1-r)/2))) * (M*C))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbudget) (by norm_num)
    _ = _ := by rw [hfactor]; ring

/-- Candidate discharge of the named finite-domain standard comparison input,
using imported finite exploration/entropy and explicit actual pc interior.
The same positive constant works before all heights, cutoffs and parameters. -/
theorem finiteHalfSpaceEntropicInput_of_pc_interior {d : ℕ} (i : Fin d)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1) :
    ∃ E : ℝ, 0 < E ∧ FiniteHalfSpaceEntropicInput i E := by
  let r : ℝ := criticalPoint d
  let N : ℝ := (2*d : ℕ)
  let E : ℝ := 3 * Real.sqrt (N / ((r/2)*((1-r)/2)))
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hd
  have hden : 0 < (r/2)*((1-r)/2) :=
    mul_pos (div_pos hpc (by norm_num)) (div_pos (sub_pos.mpr hpc1) (by norm_num))
  have hE : 0 < E := mul_pos (by norm_num) (Real.sqrt_pos.mpr (div_pos hN hden))
  refine ⟨E, hE, ?_⟩
  intro p q k n R _hn _hk hR hqlo hqp hphi
  have hq0 : 0 < (q : ℝ) := by linarith
  have hp0 : 0 < (p : ℝ) := hq0.trans hqp
  have hp1 : (p : ℝ) < 1 := by linarith
  have hq1 : (q : ℝ) < 1 := hqp.trans hp1
  have hplo : r/2 ≤ (p : ℝ) := by dsimp [r]; linarith
  have hraw := finiteHalfSpace_entropic_budget i q p ⟨hq0,hq1⟩ ⟨hp0,hp1⟩ k n R hR
  rw [max_comm] at hraw
  have hM : 0 ≤ max (finiteHalfSpaceArmProbability i p k n R)
      (finiteHalfSpaceArmProbability i q k n R) :=
    le_trans measureReal_nonneg (le_max_left _ _)
  have hroot := entropic_window_sqrt_bound (r := r) (p := (p : ℝ)) (q := (q : ℝ))
    (M := max (finiteHalfSpaceArmProbability i p k n R) (finiteHalfSpaceArmProbability i q k n R))
    (C := finiteHalfSpaceClusterSum i q k R) (N := N)
    hpc hpc1 hplo hphi hqp.le hM (finiteHalfSpaceClusterSum_nonneg i q k R) hN.le
  have hdiff : finiteHalfSpaceArmProbability i p k n R - finiteHalfSpaceArmProbability i q k n R ≤
      |finiteHalfSpaceArmProbability i q k n R - finiteHalfSpaceArmProbability i p k n R| := by
    have h := neg_le_abs (finiteHalfSpaceArmProbability i q k n R - finiteHalfSpaceArmProbability i p k n R)
    linarith
  exact hdiff.trans (hraw.trans hroot)

end NearCritical.External
