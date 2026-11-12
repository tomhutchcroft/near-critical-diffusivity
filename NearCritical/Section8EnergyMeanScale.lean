module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! The finite-scale error in the two conditional regularity-energy means. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8

/-- For positive integer exponent, an inverse power is uniformly small
beyond a single integer threshold. -/
theorem exists_inv_nat_pow_threshold {k : ℕ} (hk : 1 ≤ k) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → K / (N : ℝ) ^ k ≤ ε := by
  obtain ⟨m, hm⟩ := exists_nat_ge (K / ε)
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro N hN
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_left 1 m).trans hN
  have hKN : K ≤ ε * (N : ℝ) := by
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast (le_max_right 1 m).trans hN
    have h := (div_le_iff₀ hε).mp (hm.trans hmN)
    linarith
  have hp : (N : ℝ) ≤ (N : ℝ) ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ hN₁ hk
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN₁
  exact (div_le_iff₀ (pow_pos hNpos _)).mpr (hKN.trans (mul_le_mul_of_nonneg_left hp hε.le))

/-- The shared inner remainder decays like `N^(7-d)` after division by
the lower heart-hitting rate. The constant is uniform in the cutoff `r`. -/
theorem energyMean_inner_remainder_le {k N H L : ℕ} (hk : 7 ≤ k) (hN : 1 ≤ N)
    (hH : H ≤ N) (hL : L ≤ N) (K a ρ : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hρ : 0 < ρ) :
    (K * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
      ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)))) /
        (a * ρ ^ (k - 3) / (N : ℝ) ^ 3) ≤
      (K * ((3 : ℝ) ^ k + (2 : ℝ) ^ (k - 1)) * (2 : ℝ) ^ (2 * k - 3) /
        (a * ρ ^ (k - 3))) / (N : ℝ) ^ (k - 6) := by
  let n : ℝ := N
  let m := 2 * k - 3
  let B : ℝ := (3 : ℝ) ^ k + (2 : ℝ) ^ (k - 1)
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast hN
  have hn : 0 < n := zero_lt_one.trans_le hn1
  have hH' : (H : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hH
  have hL' : (L : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hL
  have hmass₁ : (2 * (H : ℝ) + 1) ^ k ≤ (3 : ℝ) ^ k * n ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hmass₂ : ((L : ℝ) + 1) ^ (k - 1) ≤ (2 : ℝ) ^ (k - 1) * n ^ k := by
    calc
      _ ≤ (2 * n) ^ (k - 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (2 : ℝ) ^ (k - 1) * n ^ (k - 1) := by rw [mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by omega)) (by positivity)
  have hmass : (2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1) ≤ B * n ^ k := by
    rw [show B * n ^ k = (3 : ℝ) ^ k * n ^ k + (2 : ℝ) ^ (k - 1) * n ^ k by dsimp [B]; ring]
    exact add_le_add hmass₁ hmass₂
  have hm : (5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ) = -(m : ℝ) := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 3 ≤ 2 * k)]
    push_cast
    ring
  have hpow : (n / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)) = (2 : ℝ) ^ m / n ^ m := by
    rw [hm, Real.rpow_neg (by positivity), Real.rpow_natCast, div_pow, inv_div]
  change (K * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
    (n / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)))) / (a * ρ ^ (k - 3) / n ^ 3) ≤ _
  rw [hpow]
  calc
    _ ≤ (K * ((B * n ^ k) * ((2 : ℝ) ^ m / n ^ m))) / (a * ρ ^ (k - 3) / n ^ 3) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmass (by positivity)) hK) (by positivity)
    _ = _ := by
      change (K * ((B * n ^ k) * ((2 : ℝ) ^ m / n ^ m))) / (a * ρ ^ (k - 3) / n ^ 3) =
        (K * B * (2 : ℝ) ^ m / (a * ρ ^ (k - 3))) / n ^ (k - 6)
      have hsplit : n ^ m = n ^ k * n ^ (k - 6) * n ^ 3 := by
        rw [← pow_add, ← pow_add]
        congr 1
        dsimp [m]
        omega
      rw [hsplit]
      field_simp [hn.ne', ha.ne', hρ.ne'] <;> ring

/-- A cube radius at least `r²` makes the normalized inner remainder no
larger than the cutoff power required in the variance estimate. -/
theorem energyMean_cutoff_power_le_scale {k r N : ℕ} (hk : 7 ≤ k)
    (hr : 1 ≤ r) (hscale : r ^ 2 ≤ N) :
    (r : ℝ) ^ (k - 5) ≤ (N : ℝ) ^ (k - 6) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hscale' : (r : ℝ) ^ 2 ≤ N := by exact_mod_cast hscale
  calc
    _ ≤ (r : ℝ) ^ (2 * (k - 6)) := pow_le_pow_right₀ hr1 (by omega)
    _ = ((r : ℝ) ^ 2) ^ (k - 6) := by rw [pow_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hscale' _

end NearCritical.Section8
