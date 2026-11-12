module

public import NearCritical.Section10ConditionedRouteOverlap

/-! Section10 lem.nw.EIT in source form (conditioned on survival).
Converts the floor-blocked tail of `sourceRoute_conditioned_overlap_tail_all`
into `C * q0^(k-1) * M^(1-D)` with an explicit `q0 = (1/2)^(1/K) < 1`.
Draft, not compiled. Deterministic arithmetic only. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

/-- Floor-blocked halving is dominated by a geometric rate, up to factor 2. -/
theorem half_pow_div_le_two_mul_rpow_pow (K n : ℕ) (hK : 0 < K) :
    (1/2:ℝ)^(n/K) ≤ 2 * ((1/2:ℝ)^((1:ℝ)/K))^n := by
  set r : ℝ := (1/2:ℝ)^((1:ℝ)/K) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hKne : (K:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have hrK : r^K = 1/2 := by
    rw [← Real.rpow_natCast, hr, ← Real.rpow_mul (by norm_num),
      one_div_mul_cancel hKne, Real.rpow_one]
  have hlt : n ≤ (n/K+1)*K := by
    have := Nat.lt_div_mul_add (a := n) hK
    rw [add_mul, one_mul]; omega
  have hmono : r^((n/K+1)*K) ≤ r^n := pow_le_pow_of_le_one hr0 hr1 hlt
  rw [pow_mul', hrK, pow_succ] at hmono
  have hp : 0 ≤ (1/2:ℝ)^(n/K) := by positivity
  linarith

theorem source_q0_lt_one (K : ℕ) (hK : 0 < K) : (1/2:ℝ)^((1:ℝ)/K) < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)

/-- Source-form exponential intersection tail for the survival-conditioned
route-pair law: one `q0 < 1` and one `C`, uniform in `M ≥ M₀` and `k ≥ 1`. -/
theorem sourceRoute_conditioned_EIT {D : ℕ} (hD : 3 ≤ D) :
    ∃ (q0 C : ℝ) (M₀ : ℕ), 0 < q0 ∧ q0 < 1 ∧ 0 ≤ C ∧ ∀ M ≥ M₀, ∀ k : ℕ, 0 < k →
      conditionedRouteOverlapTail D M k ≤ C * q0^(k-1) / (M:ℝ)^(D-1) := by
  obtain ⟨K, M₀, hK, ht⟩ := sourceRoute_conditioned_overlap_tail_all hD
  let c : ℝ := 8*((D:ℝ)+1)
  let T : ℝ := ((routeDifferenceTrap D).card : ℝ)
  refine ⟨(1/2:ℝ)^((1:ℝ)/K), 8 * c^D * T, max M₀ 1, by positivity,
    source_q0_lt_one K hK, by positivity, ?_⟩
  intro M hM k hk
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast (le_max_right _ _).trans hM
  have hMpos : (0:ℝ) < M := by linarith
  have hc : 0 < c := by positivity
  have hscale : (M:ℝ) * T / ((M:ℝ)/c)^D = c^D * T / (M:ℝ)^(D-1) := by
    obtain ⟨e, rfl⟩ : ∃ e, D = e+1 := ⟨D-1, by omega⟩
    simp only [Nat.add_sub_cancel, div_pow, pow_succ]
    field_simp
  have hgeo := half_pow_div_le_two_mul_rpow_pow K (k-1) hK
  have hT : 0 ≤ T := Nat.cast_nonneg _
  calc conditionedRouteOverlapTail D M k
      ≤ 4 * ((1/2:ℝ)^((k-1)/K) * ((M:ℝ) * T / ((M:ℝ)/c)^D)) :=
        ht M ((le_max_left _ _).trans hM) k hk
    _ = 4 * ((1/2:ℝ)^((k-1)/K) * (c^D * T / (M:ℝ)^(D-1))) := by rw [hscale]
    _ ≤ 4 * ((2 * ((1/2:ℝ)^((1:ℝ)/K))^(k-1)) * (c^D * T / (M:ℝ)^(D-1))) := by
        gcongr
    _ = 8 * c^D * T * ((1/2:ℝ)^((1:ℝ)/K))^(k-1) / (M:ℝ)^(D-1) := by ring

end NearCritical.Section10
