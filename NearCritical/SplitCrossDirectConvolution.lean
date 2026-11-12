module

public import NearCritical.Section8Convolution
public import NearCritical.Section8HigherEnergy

/-! A lattice convolution for the direct proof of `SplitCrossInput`.

`fourth_green_convolution_le`: for `d ≥ 7`, every finite set `s` and vertices
`c, e`,

  `Σ_{y ∈ s} max(1,|c-y|)^(4-d) · max(1,|e-y|)^(2-d) ≤ C_d · max(1,|c-e|)^(6-d)`,

in the supremum distance `latticeDistance`. It is the convolution of the
fourth-order kernel (itself the convolution of two Green kernels) with a Green
kernel. Proof: three regions (`y` within `2M` of `e`; `y` within `M` of `c`;
`y` farther than `2M` from `e`), using the existing ball sums
`sum_green_ball_le`, `sum_fourth_green_ball_le` and the tail sum
`sum_power_tail_ball_le`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open scoped BigOperators

variable {d : ℕ}

/-- `(D/2)^γ ≤ 2^d D^γ` for `D ≥ 1` and `-d ≤ γ ≤ 0`. -/
lemma half_rpow_le {D γ : ℝ} (hD : 1 ≤ D) (hγ : -(d : ℝ) ≤ γ) :
    (D / 2) ^ γ ≤ (2 : ℝ) ^ d * D ^ γ := by
  have hD0 : 0 ≤ D := by linarith
  rw [Real.div_rpow hD0 (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
    mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hD0 _)
  calc (2 : ℝ) ^ (-γ) ≤ (2 : ℝ) ^ ((d : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 : ℝ) ^ d := Real.rpow_natCast 2 d

/-- Pointwise three-region bound. -/
lemma conv_pointwise3 {α β : ℝ} (hα : α ≤ 0) (hβ : β ≤ 0) {k L R D M : ℝ}
    (hD : D = max 1 k) (hM : D ≤ M) (hL0 : 0 ≤ L) (hkLR : k ≤ L + R) (hRkL : R ≤ k + L) :
    (max 1 L) ^ α * (max 1 R) ^ β ≤
      (D / 2) ^ α * (if R ≤ 2 * M then (max 1 R) ^ β else 0) +
      (D / 2) ^ β * (if L ≤ M then (max 1 L) ^ α else 0) +
      (2 : ℝ) ^ (-α) * (if 2 * M < R then (max 1 R) ^ (α + β) else 0) := by
  have hD1 : 1 ≤ D := hD ▸ le_max_left _ _
  have hkD : k ≤ D := hD ▸ le_max_right _ _
  have hDpos : 0 < D / 2 := by linarith
  have h1L : (0 : ℝ) < max 1 L := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1R : (0 : ℝ) < max 1 R := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hLα : 0 ≤ (max 1 L) ^ α := Real.rpow_nonneg h1L.le _
  have hRβ : 0 ≤ (max 1 R) ^ β := Real.rpow_nonneg h1R.le _
  by_cases hR : R ≤ 2 * M
  · rw [if_pos hR, if_neg (not_lt.mpr hR), mul_zero, add_zero]
    by_cases hLD : D / 2 ≤ L
    · have hLle : (max 1 L) ^ α ≤ (D / 2) ^ α :=
        Real.rpow_le_rpow_of_nonpos hDpos (hLD.trans (le_max_right _ _)) hα
      have h2 : 0 ≤ (D / 2) ^ β * (if L ≤ M then (max 1 L) ^ α else 0) :=
        mul_nonneg (Real.rpow_nonneg hDpos.le _) (by split_ifs <;> [exact hLα; exact le_rfl])
      nlinarith [mul_le_mul_of_nonneg_right hLle hRβ]
    · have hLlt : L < D / 2 := not_le.mp hLD
      have hLM : L ≤ M := by linarith
      rw [if_pos hLM]
      have hRge : D / 2 ≤ max 1 R := by
        rcases le_total k 1 with hk | hk
        · have : D = 1 := by rw [hD]; exact max_eq_left hk
          rw [this]
          exact le_trans (by norm_num) (le_max_left _ _)
        · have : D = k := by rw [hD]; exact max_eq_right hk
          have : D / 2 ≤ R := by linarith
          exact this.trans (le_max_right _ _)
      have hRle : (max 1 R) ^ β ≤ (D / 2) ^ β :=
        Real.rpow_le_rpow_of_nonpos hDpos hRge hβ
      have h1 : 0 ≤ (D / 2) ^ α * (max 1 R) ^ β :=
        mul_nonneg (Real.rpow_nonneg hDpos.le _) hRβ
      nlinarith [mul_le_mul_of_nonneg_left hRle hLα]
  · have hR' : 2 * M < R := not_le.mp hR
    rw [if_neg hR, if_pos hR', mul_zero, zero_add]
    have hRpos : 1 ≤ R := by linarith
    have hmaxR : max 1 R = R := max_eq_right hRpos
    have hLge : R / 2 ≤ L := by linarith
    have hLle : (max 1 L) ^ α ≤ (R / 2) ^ α :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (hLge.trans (le_max_right _ _)) hα
    have hsplit : (R / 2) ^ α = (2 : ℝ) ^ (-α) * R ^ α := by
      rw [Real.div_rpow (by linarith) (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num), mul_comm]
    have h2 : 0 ≤ (D / 2) ^ β * (if L ≤ M then (max 1 L) ^ α else 0) :=
      mul_nonneg (Real.rpow_nonneg hDpos.le _) (by split_ifs <;> [exact hLα; exact le_rfl])
    rw [hmaxR] at hRβ ⊢
    have hadd : R ^ (α + β) = R ^ α * R ^ β := Real.rpow_add (by linarith) _ _
    rw [hadd]
    have hmain : (max 1 L) ^ α * R ^ β ≤ (2 : ℝ) ^ (-α) * R ^ α * R ^ β := by
      rw [← hsplit]
      exact mul_le_mul_of_nonneg_right hLle hRβ
    nlinarith [hmain]

/-- The constant of `fourth_green_convolution_le`. -/
def convConst (d : ℕ) : ℝ := (2 : ℝ) ^ d * 107 * (1 + 2 * (d : ℝ) * 3 ^ (d - 1))

lemma convConst_nonneg (d : ℕ) : 0 ≤ convConst d := by
  unfold convConst
  positivity

set_option maxHeartbeats 1600000 in
/-- **Convolution of the fourth-order kernel with the Green kernel.** -/
theorem fourth_green_convolution_le (hd : 7 ≤ d) (s : Finset (Vertex d)) (c e : Vertex d) :
    ∑ y ∈ s, (max 1 (latticeDistance c y)) ^ ((4 : ℝ) - (d : ℝ)) *
      (max 1 (latticeDistance e y)) ^ ((2 : ℝ) - (d : ℝ)) ≤
      convConst d * (max 1 (latticeDistance c e)) ^ ((6 : ℝ) - (d : ℝ)) := by
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = (4 : ℝ) - (d : ℝ) := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (2 : ℝ) - (d : ℝ) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = max 1 (latticeDistance c e) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = Nat.floor D + 1 := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * (d : ℝ) * 3 ^ (d - 1) := ⟨_, rfl⟩
  rw [← hαdef, ← hβdef, ← hDdef]
  have hdR : (7 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hα : α ≤ 0 := by rw [hαdef]; linarith
  have hβ : β ≤ 0 := by rw [hβdef]; linarith
  have hD1 : 1 ≤ D := hDdef ▸ le_max_left _ _
  have hDpos : 0 < D := by linarith
  have hMge : D ≤ (M : ℝ) := by
    rw [hMdef]
    push_cast
    exact (Nat.lt_floor_add_one D).le
  have hMle : (M : ℝ) ≤ 2 * D := by
    rw [hMdef]
    push_cast
    have := Nat.floor_le hDpos.le
    linarith
  have hM1 : 1 ≤ M := by rw [hMdef]; omega
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  -- pointwise bound and regrouping
  have hpt : ∀ y ∈ s, (max 1 (latticeDistance c y)) ^ α * (max 1 (latticeDistance e y)) ^ β ≤
      (D / 2) ^ α * (if latticeDistance e y ≤ 2 * (M : ℝ) then
          (max 1 (latticeDistance e y)) ^ β else 0) +
      (D / 2) ^ β * (if latticeDistance c y ≤ (M : ℝ) then
          (max 1 (latticeDistance c y)) ^ α else 0) +
      (2 : ℝ) ^ (-α) * (if 2 * (M : ℝ) < latticeDistance e y then
          (max 1 (latticeDistance e y)) ^ (α + β) else 0) := by
    intro y _
    have hk : latticeDistance c e ≤ latticeDistance c y + latticeDistance e y := by
      simpa only [latticeDistance_comm y e] using latticeDistance_triangle c y e
    have hR : latticeDistance e y ≤ latticeDistance c e + latticeDistance c y := by
      simpa only [latticeDistance_comm e c] using latticeDistance_triangle e c y
    exact conv_pointwise3 hα hβ hDdef hMge dist_nonneg hk hR
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter] at hsum
  -- the three sums
  have hS1 : ∑ y ∈ s.filter (fun y => latticeDistance e y ≤ 2 * (M : ℝ)),
      (max 1 (latticeDistance e y)) ^ β ≤ (1 + K) * 25 * D ^ 2 := by
    have h := Section8.sum_green_ball_le (by omega : 2 ≤ d) (2 * M)
      (s.filter (fun y => latticeDistance e y ≤ 2 * (M : ℝ))) e
      (fun y hy => by
        have := (Finset.mem_filter.mp hy).2
        push_cast
        exact this)
    rw [← hβdef, ← hKdef] at h
    push_cast at h
    have hsq : (2 * (M : ℝ) + 1) ^ 2 ≤ 25 * D ^ 2 := by nlinarith
    have hD2 : (1 : ℝ) ≤ 25 * D ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hK0]
  have hS2 : ∑ y ∈ s.filter (fun y => latticeDistance c y ≤ (M : ℝ)),
      (max 1 (latticeDistance c y)) ^ α ≤ (1 + K) * 81 * D ^ 4 := by
    have h := Section8.sum_fourth_green_ball_le (by omega : 2 ≤ d) M
      (s.filter (fun y => latticeDistance c y ≤ (M : ℝ))) c
      (fun y hy => (Finset.mem_filter.mp hy).2)
    rw [← hαdef, ← hKdef] at h
    have h4 : ((M : ℝ) + 1) ^ 4 ≤ 81 * D ^ 4 := by
      have h3 : (M : ℝ) + 1 ≤ 3 * D := by linarith
      have h0 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
      calc ((M : ℝ) + 1) ^ 4 ≤ (3 * D) ^ 4 := pow_le_pow_left₀ h0 h3 4
        _ = 81 * D ^ 4 := by ring
    have hK1 : 0 ≤ 1 + K := by linarith
    calc _ ≤ (1 + K) * ((M : ℝ) + 1) ^ 4 := h
      _ ≤ (1 + K) * (81 * D ^ 4) := mul_le_mul_of_nonneg_left h4 hK1
      _ = _ := by ring
  have hS3 : ∑ y ∈ s.filter (fun y => 2 * (M : ℝ) < latticeDistance e y),
      (max 1 (latticeDistance e y)) ^ (α + β) ≤ K * D ^ ((6 : ℝ) - (d : ℝ)) := by
    have hq : α + β < -(d : ℝ) := by rw [hαdef, hβdef]; linarith
    have ht := Section8.sum_power_tail_ball_le (by omega : 1 ≤ d) (2 * M) (by omega : 1 ≤ 2 * M)
      (α + β) hq (s.filter (fun y => 2 * (M : ℝ) < latticeDistance e y)) e
      (fun y hy => by
        have := (Finset.mem_filter.mp hy).2
        push_cast
        exact this)
    rw [← hKdef] at ht
    push_cast at ht
    have he1 : (d : ℝ) + (α + β) = 6 - (d : ℝ) := by rw [hαdef, hβdef]; ring
    have he2 : -(d : ℝ) - (α + β) = (d : ℝ) - 6 := by rw [hαdef, hβdef]; ring
    rw [he1, he2] at ht
    have hden : (1 : ℝ) ≤ (d : ℝ) - 6 := by linarith
    have hscale : (2 * (M : ℝ)) ^ ((6 : ℝ) - (d : ℝ)) ≤ D ^ ((6 : ℝ) - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hDpos (by linarith) (by linarith)
    have hnn : 0 ≤ K * (2 * (M : ℝ)) ^ ((6 : ℝ) - (d : ℝ)) :=
      mul_nonneg hK0 (Real.rpow_nonneg (by positivity) _)
    exact ht.trans ((div_le_self hnn hden).trans (mul_le_mul_of_nonneg_left hscale hK0))
  -- powers
  have hpowα : (D / 2) ^ α * D ^ 2 ≤ (2 : ℝ) ^ d * D ^ ((6 : ℝ) - (d : ℝ)) := by
    have h := half_rpow_le (d := d) (γ := α) hD1 (by rw [hαdef]; linarith)
    have hadd : D ^ α * D ^ 2 = D ^ ((6 : ℝ) - (d : ℝ)) := by
      rw [← Real.rpow_natCast D 2, ← Real.rpow_add hDpos]
      congr 1
      rw [hαdef]
      norm_num
      ring
    calc (D / 2) ^ α * D ^ 2 ≤ (2 : ℝ) ^ d * D ^ α * D ^ 2 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by rw [mul_assoc, hadd]
  have hpowβ : (D / 2) ^ β * D ^ 4 ≤ (2 : ℝ) ^ d * D ^ ((6 : ℝ) - (d : ℝ)) := by
    have h := half_rpow_le (d := d) (γ := β) hD1 (by rw [hβdef]; linarith)
    have hadd : D ^ β * D ^ 4 = D ^ ((6 : ℝ) - (d : ℝ)) := by
      rw [← Real.rpow_natCast D 4, ← Real.rpow_add hDpos]
      congr 1
      rw [hβdef]
      norm_num
      ring
    calc (D / 2) ^ β * D ^ 4 ≤ (2 : ℝ) ^ d * D ^ β * D ^ 4 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by rw [mul_assoc, hadd]
  have h2α : (2 : ℝ) ^ (-α) ≤ (2 : ℝ) ^ d := by
    calc (2 : ℝ) ^ (-α) ≤ (2 : ℝ) ^ ((d : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hαdef]; linarith)
      _ = (2 : ℝ) ^ d := Real.rpow_natCast 2 d
  have hE : 0 ≤ D ^ ((6 : ℝ) - (d : ℝ)) := Real.rpow_nonneg hDpos.le _
  have hDα : 0 ≤ (D / 2) ^ α := Real.rpow_nonneg (by linarith) _
  have hDβ : 0 ≤ (D / 2) ^ β := Real.rpow_nonneg (by linarith) _
  have h2pos : 0 ≤ (2 : ℝ) ^ (-α) := Real.rpow_nonneg (by norm_num) _
  have hK1 : 0 ≤ 1 + K := by linarith
  have t1 : (D / 2) ^ α * ((1 + K) * 25 * D ^ 2) ≤
      (1 + K) * 25 * ((2 : ℝ) ^ d * D ^ ((6 : ℝ) - (d : ℝ))) := by
    calc (D / 2) ^ α * ((1 + K) * 25 * D ^ 2) = (1 + K) * 25 * ((D / 2) ^ α * D ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpowα (by positivity)
  have t2 : (D / 2) ^ β * ((1 + K) * 81 * D ^ 4) ≤
      (1 + K) * 81 * ((2 : ℝ) ^ d * D ^ ((6 : ℝ) - (d : ℝ))) := by
    calc (D / 2) ^ β * ((1 + K) * 81 * D ^ 4) = (1 + K) * 81 * ((D / 2) ^ β * D ^ 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpowβ (by positivity)
  have t3 : (2 : ℝ) ^ (-α) * (K * D ^ ((6 : ℝ) - (d : ℝ))) ≤
      (2 : ℝ) ^ d * ((1 + K) * D ^ ((6 : ℝ) - (d : ℝ))) :=
    mul_le_mul h2α (mul_le_mul_of_nonneg_right (by linarith) hE)
      (mul_nonneg hK0 hE) (by positivity)
  have hfinal := hsum.trans (add_le_add (add_le_add
    ((mul_le_mul_of_nonneg_left hS1 hDα).trans t1)
    ((mul_le_mul_of_nonneg_left hS2 hDβ).trans t2))
    ((mul_le_mul_of_nonneg_left hS3 h2pos).trans t3))
  refine hfinal.trans (le_of_eq ?_)
  unfold convConst
  rw [← hKdef]
  ring

end NearCritical.SplitCrossDirect
end
