module

public import NearCritical.Section10WitnessScale
public import NearCritical.Section10WitnessArith
public import NearCritical.Section10StepDiameterSmall

/-! A witness for the parameter relations of `time_constant_sandwich_of_pregood`.

`move_relations_witness`: in dimension `m + 6` (`m >= 1`), for typicality
parameters with `c_b, c > 0`, any `rho > 1`, Green constant `G₀ >= 0` and
Section 9 size constant `cSize > 0`, there is `k` with

  `2 <= k`, `10 <= 2k^4`, `cSize <= 4 k c_b`, `cSize <= 16 k c c_b^2`,

and then for every `Lambda > 0` and `N₀` there are a mesh factor `n0 = 2a`, a
diameter constant `Ask` (a natural number) and a threshold `p₁ > p_c` such
that for EVERY `p` in `(p_c, p₁]`, with `t = a l_*(p)`,
`q0 = n0^2/(4(1-p_c))`, `eps = (1 - 1/rho)/2`, `K_diam = Ask (2t)^2`:

* `p = p_c + (1 - p_c) q`, `2t = n0 l_*(p)`, `t >= 9`, `t >= N₀`;
* `2 k^4 <= c (2t)^m`, `cSize <= 4 c c_b (2t)^m`;
* the exit relation `((1-p_c)(1-q))^j <= 1 - 1/rho` for `j >= c_b (2t)^2`;
* `Lambda <= q t^2` and `q <= q0/t^2`;
* `1/rho <= 1 - eps - (1 + diamConst t^2)/(K_diam + 1)`.

The order of choice is the one of the Section 9 constants:
`cSize -> k -> (Lambda, N₀) -> n0 -> Ask -> p₁`. The remaining relations of
the capstone (`mo = 2k^4 - 1`, `KA = 4kC_b + 1`, `CB = 8C_b + 1`,
`M_off = M_coal =` cube volume, `A_sp = 2 K_spn`) hold by definition of those
constants; `hpre` and the regularity conditions on `typ` are not part of this
witness.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

lemma diamConst_nonneg (m k : ℕ) (typ : TypicalParameters) {G₀ q0 : ℝ}
    (hbU : 0 ≤ typ.boundaryUpper) (hcU : 0 ≤ typ.countUpper) (hG0 : 0 ≤ G₀) (hq0 : 0 ≤ q0) :
    0 ≤ diamConst m k typ G₀ q0 := by
  have hK := greenConvConst_nonneg (m + 5 + 1)
  unfold diamConst
  positivity

set_option maxHeartbeats 800000 in
theorem move_relations_witness_uniform (m : ℕ) (hm : 1 ≤ m)
    (hpc0 : 0 < (criticalPoint (m + 5 + 1) : ℝ)) (hpc1 : (criticalPoint (m + 5 + 1) : ℝ) < 1)
    (typ : TypicalParameters) (hbL : 0 < typ.boundaryLower) (hcL : 0 < typ.countLower)
    (hbU : 0 ≤ typ.boundaryUpper) (hcU : 0 ≤ typ.countUpper)
    {ϱ : ℝ} (hϱ : 1 < ϱ) {G₀ : ℝ} (hG0 : 0 ≤ G₀) {cSize : ℝ} (hcS : 0 < cSize) :
    ∃ k : ℕ, 2 ≤ k ∧ 10 ≤ 2 * k ^ 4 ∧ cSize ≤ 4 * (k : ℝ) * typ.boundaryLower ∧
      cSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2 ∧
      ∀ Lambda : ℝ, 0 < Lambda →
      ∃ (a AskN : ℕ), 1 ≤ a ∧ ∀ N₀ : ℕ,
      ∃ p₁ : unitInterval, criticalPoint (m + 5 + 1) < p₁ ∧
      ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p → p ≤ p₁ →
      ∃ q : unitInterval,
        orParameter (criticalPoint (m + 5 + 1)) q = p ∧
        2 * (a * chemicalCorrelationScale (m + 5 + 1) p) =
          (2 * a) * chemicalCorrelationScale (m + 5 + 1) p ∧
        9 ≤ a * chemicalCorrelationScale (m + 5 + 1) p ∧
        N₀ ≤ a * chemicalCorrelationScale (m + 5 + 1) p ∧
        2 * (k : ℝ) ^ 4 ≤ typ.countLower *
          (2 * ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ)) ^ m ∧
        cSize ≤ 4 * typ.countLower * typ.boundaryLower *
          (2 * ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ)) ^ m ∧
        (∀ j : ℕ, typ.boundaryLower *
            (2 * ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ)) ^ 2 ≤ (j : ℝ) →
          ((1 - (criticalPoint (m + 5 + 1) : ℝ)) * (1 - (q : ℝ))) ^ j ≤ 1 - ϱ⁻¹) ∧
        Lambda ≤ (q : ℝ) * ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ) ^ 2 ∧
        (q : ℝ) ≤ (((2 * a : ℕ) : ℝ) ^ 2 / (4 * (1 - (criticalPoint (m + 5 + 1) : ℝ)))) /
          ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ) ^ 2 ∧
        ϱ⁻¹ ≤ 1 - (1 - ϱ⁻¹) / 2 -
          (1 + diamConst m k typ G₀
              (((2 * a : ℕ) : ℝ) ^ 2 / (4 * (1 - (criticalPoint (m + 5 + 1) : ℝ)))) *
            ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ) ^ 2) /
          (((AskN * (2 * (a * chemicalCorrelationScale (m + 5 + 1) p)) ^ 2 : ℕ) : ℝ) + 1) := by
  set pc : ℝ := (criticalPoint (m + 5 + 1) : ℝ) with hpc
  set bL : ℝ := typ.boundaryLower with hbLdef
  set cL : ℝ := typ.countLower with hcLdef
  have h1pc : 0 < 1 - pc := by linarith
  have hϱinv : ϱ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hϱ
  have hη : 0 < (1 - ϱ⁻¹) / 2 := by linarith
  -- choice of k
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 2 + ⌈cSize / (4 * bL)⌉₊ + ⌈cSize / (16 * cL * bL ^ 2)⌉₊ :=
    ⟨_, rfl⟩
  have hk2 : 2 ≤ k := by omega
  have hkR1 : cSize / (4 * bL) ≤ (k : ℝ) := by
    have h1 := Nat.le_ceil (cSize / (4 * bL))
    have h2 : (⌈cSize / (4 * bL)⌉₊ : ℝ) ≤ (k : ℝ) := by
      rw [hk]
      push_cast
      have : (0:ℝ) ≤ (⌈cSize / (16 * cL * bL ^ 2)⌉₊ : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hkR2 : cSize / (16 * cL * bL ^ 2) ≤ (k : ℝ) := by
    have h1 := Nat.le_ceil (cSize / (16 * cL * bL ^ 2))
    have h2 : (⌈cSize / (16 * cL * bL ^ 2)⌉₊ : ℝ) ≤ (k : ℝ) := by
      rw [hk]
      push_cast
      have : (0:ℝ) ≤ (⌈cSize / (4 * bL)⌉₊ : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hk10 : 10 ≤ 2 * k ^ 4 := by
    have : 2 ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hk2 4
    omega
  refine ⟨k, hk2, hk10, ?_, ?_, ?_⟩
  · have h := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * bL)).mp hkR1
    linarith
  · have h := (div_le_iff₀ (by positivity : (0:ℝ) < 16 * cL * bL ^ 2)).mp hkR2
    linarith
  intro Lambda hLambda
  -- choice of a
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌈4 * Lambda⌉₊ + 1 := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by omega
  have haR : 4 * Lambda ≤ (a : ℝ) := by
    have h1 := Nat.le_ceil (4 * Lambda)
    rw [ha]
    push_cast
    linarith
  have haR1 : (1:ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  have hwin : Lambda ≤ ((2 * a : ℕ) : ℝ) ^ 2 / (16 * (1 - pc)) := by
    rw [le_div_iff₀ (by positivity)]
    push_cast
    have h1 : Lambda * (16 * (1 - pc)) ≤ 16 * Lambda := by nlinarith [(criticalPoint (m + 5 + 1)).2.1]
    nlinarith
  set q0' : ℝ := ((2 * a : ℕ) : ℝ) ^ 2 / (4 * (1 - pc)) with hq0'
  have hq0'nn : 0 ≤ q0' := by positivity
  -- exit threshold
  obtain ⟨J₀, hJ₀⟩ := exit_bound_eventually hpc0 hpc1.le (c := 1 - ϱ⁻¹) (by linarith)
  -- diameter constant
  have hCnn := diamConst_nonneg m k typ hbU hcU hG0 hq0'nn
  obtain ⟨AskN, hAsk⟩ : ∃ AskN : ℕ,
      AskN = ⌈(1 + diamConst m k typ G₀ q0') / (4 * ((1 - ϱ⁻¹) / 2))⌉₊ := ⟨_, rfl⟩
  have hAskR : 1 + diamConst m k typ G₀ q0' ≤ 4 * (AskN : ℝ) * ((1 - ϱ⁻¹) / 2) := by
    have h1 := Nat.le_ceil ((1 + diamConst m k typ G₀ q0') / (4 * ((1 - ϱ⁻¹) / 2)))
    rw [← hAsk] at h1
    have h2 := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * ((1 - ϱ⁻¹) / 2))).mp h1
    linarith
  refine ⟨a, AskN, ha1, ?_⟩
  intro N₀
  -- target for the mesh
  set T₀ : ℝ := 9 + (N₀ : ℝ) + (k : ℝ) ^ 4 / cL + cSize / (8 * cL * bL) + (J₀ : ℝ) / (4 * bL)
    with hT₀
  have hT₀pos : 0 < T₀ := by positivity
  obtain ⟨p₁, hp₁, hscale⟩ := scale_witness (m + 5 + 1) hpc1 a ha1 hT₀pos
  refine ⟨p₁, hp₁, ?_⟩
  intro p hp hpp
  obtain ⟨hmesh, hT, q, hq, hqlo, hqhi⟩ := hscale p hp hpp
  set t : ℕ := a * chemicalCorrelationScale (m + 5 + 1) p with ht
  have hN0nn : (0:ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
  have hk4nn : (0:ℝ) ≤ (k : ℝ) ^ 4 / cL := by positivity
  have hcSnn : (0:ℝ) ≤ cSize / (8 * cL * bL) := by positivity
  have hJnn : (0:ℝ) ≤ (J₀ : ℝ) / (4 * bL) := by positivity
  have ht9 : (9:ℝ) ≤ (t : ℝ) := by linarith
  have htN : (N₀ : ℝ) ≤ (t : ℝ) := by linarith
  have htk : (k : ℝ) ^ 4 / cL ≤ (t : ℝ) := by linarith
  have htc : cSize / (8 * cL * bL) ≤ (t : ℝ) := by linarith
  have htJ : (J₀ : ℝ) / (4 * bL) ≤ (t : ℝ) := by linarith
  have ht1 : (1:ℝ) ≤ (t : ℝ) := by linarith
  have h2t1 : (1:ℝ) ≤ 2 * (t : ℝ) := by linarith
  have hpow : 2 * (t : ℝ) ≤ (2 * (t : ℝ)) ^ m := le_self_pow₀ h2t1 (by omega)
  have htpos : (0:ℝ) < (t : ℝ) ^ 2 := by positivity
  refine ⟨q, hq, hmesh, by exact_mod_cast ht9, by exact_mod_cast htN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (k : ℝ) ^ 4 ≤ cL * (t : ℝ) := by
      have := (div_le_iff₀ hcL).mp htk
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hpow hcL.le]
  · have h1 : cSize ≤ 8 * cL * bL * (t : ℝ) := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 8 * cL * bL)).mp htc
      linarith
    have h2 : (0:ℝ) ≤ 4 * cL * bL := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow h2]
  · intro j hj
    refine hJ₀ q j ?_
    have h1 : (J₀ : ℝ) ≤ 4 * bL * (t : ℝ) := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 4 * bL)).mp htJ
      linarith
    have h2 : 4 * bL * (t : ℝ) ≤ bL * (2 * (t : ℝ)) ^ 2 := by nlinarith
    have h3 : (J₀ : ℝ) ≤ (j : ℝ) := h1.trans (h2.trans hj)
    exact_mod_cast h3
  · exact hwin.trans hqlo
  · rw [le_div_iff₀ htpos]
    exact hqhi
  · have hratio := diam_ratio_le (C := diamConst m k typ G₀ q0') (A := (AskN : ℝ))
      (η := (1 - ϱ⁻¹) / 2) (T := (t : ℝ)) hCnn (Nat.cast_nonneg _) hη ht1 hAskR
    have hcast : ((AskN * (2 * t) ^ 2 : ℕ) : ℝ) = (AskN : ℝ) * (2 * (t : ℝ)) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    rw [hcast]
    linarith

theorem move_relations_witness (m : ℕ) (hm : 1 ≤ m)
    (hpc0 : 0 < (criticalPoint (m + 5 + 1) : ℝ)) (hpc1 : (criticalPoint (m + 5 + 1) : ℝ) < 1)
    (typ : TypicalParameters) (hbL : 0 < typ.boundaryLower) (hcL : 0 < typ.countLower)
    (hbU : 0 ≤ typ.boundaryUpper) (hcU : 0 ≤ typ.countUpper)
    {ϱ : ℝ} (hϱ : 1 < ϱ) {G₀ : ℝ} (hG0 : 0 ≤ G₀) {cSize : ℝ} (hcS : 0 < cSize) :
    ∃ k : ℕ, 2 ≤ k ∧ 10 ≤ 2 * k ^ 4 ∧ cSize ≤ 4 * (k : ℝ) * typ.boundaryLower ∧
      cSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2 ∧
      ∀ Lambda : ℝ, 0 < Lambda → ∀ N₀ : ℕ,
      ∃ (a AskN : ℕ) (p₁ : unitInterval), 1 ≤ a ∧ criticalPoint (m + 5 + 1) < p₁ ∧
      ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p → p ≤ p₁ →
      ∃ q : unitInterval,
        orParameter (criticalPoint (m + 5 + 1)) q = p ∧
        2 * (a * chemicalCorrelationScale (m + 5 + 1) p) =
          (2 * a) * chemicalCorrelationScale (m + 5 + 1) p ∧
        9 ≤ a * chemicalCorrelationScale (m + 5 + 1) p ∧
        N₀ ≤ a * chemicalCorrelationScale (m + 5 + 1) p ∧
        2 * (k : ℝ) ^ 4 ≤ typ.countLower *
          (2 * ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ)) ^ m ∧
        cSize ≤ 4 * typ.countLower * typ.boundaryLower *
          (2 * ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ)) ^ m ∧
        (∀ j : ℕ, typ.boundaryLower *
            (2 * ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ)) ^ 2 ≤ (j : ℝ) →
          ((1 - (criticalPoint (m + 5 + 1) : ℝ)) * (1 - (q : ℝ))) ^ j ≤ 1 - ϱ⁻¹) ∧
        Lambda ≤ (q : ℝ) * ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ) ^ 2 ∧
        (q : ℝ) ≤ (((2 * a : ℕ) : ℝ) ^ 2 / (4 * (1 - (criticalPoint (m + 5 + 1) : ℝ)))) /
          ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ) ^ 2 ∧
        ϱ⁻¹ ≤ 1 - (1 - ϱ⁻¹) / 2 -
          (1 + diamConst m k typ G₀
              (((2 * a : ℕ) : ℝ) ^ 2 / (4 * (1 - (criticalPoint (m + 5 + 1) : ℝ)))) *
            ((a * chemicalCorrelationScale (m + 5 + 1) p : ℕ) : ℝ) ^ 2) /
          (((AskN * (2 * (a * chemicalCorrelationScale (m + 5 + 1) p)) ^ 2 : ℕ) : ℝ) + 1) := by
  obtain ⟨k,hk,hk10,hc₁,hc₃,h⟩ := move_relations_witness_uniform m hm hpc0 hpc1 typ hbL hcL hbU hcU hϱ hG0 hcS
  refine ⟨k,hk,hk10,hc₁,hc₃,?_⟩
  intro Lambda hLambda N₀
  obtain ⟨a,AskN,ha,hw⟩ := h Lambda hLambda
  obtain ⟨p₁,hp₁,hp⟩ := hw N₀
  exact ⟨a,AskN,p₁,ha,hp₁,hp⟩

end NearCritical.Section10
