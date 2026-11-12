module

public import NearCritical.SubcriticalKernelIntegral

/-! Analytic half-slab prerequisite from source lem.A.upperbound.half.
The actual truncated interval integral retains its endpoint exponential.
No percolation differential inequality or half-slab probability bound is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

/-- Source scalar absorption, with the loss of two in the exponential rate. -/
lemma one_add_mul_exp_neg_le {x : ℝ} (_hx : 0 ≤ x) :
    (1+x)*Real.exp (-x) ≤ 2*Real.exp (-x/2) := by
  have hlinear : 1+x ≤ 2*Real.exp (x/2) := by
    have h := Real.add_one_le_exp (x/2)
    linarith
  calc
    _ ≤ (2*Real.exp (x/2))*Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hlinear (Real.exp_nonneg _)
    _ = _ := by
      have he : x/2 + -x = -x/2 := by ring
      rw [mul_assoc, ← Real.exp_add, he]

/-- The explicit accepted primitive evaluates the actual interval [0,p].
The lower primitive is discarded only after proving it nonnegative. -/
lemma subcritical_exp_sqrt_truncated_integral_le_primitive {pc p a : ℝ}
    (hp0 : 0 ≤ p) (hppc : p ≤ pc) (ha : 0 < a) :
    (∫ s in (0 : ℝ)..p, Real.exp (-a*Real.sqrt (pc-s))) ≤
      (2/a^2)*(1+a*Real.sqrt (pc-p))*Real.exp (-a*Real.sqrt (pc-p)) := by
  have hc : Continuous (subcriticalPrimitive a pc) := by
    unfold subcriticalPrimitive
    fun_prop
  have hk : Continuous (fun s : ℝ ↦ Real.exp (-a*Real.sqrt (pc-s))) := by fun_prop
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp0 hc.continuousOn
    (fun s hs ↦ subcriticalPrimitive_hasDerivAt ha (lt_of_lt_of_le hs.2 hppc))
    (hk.intervalIntegrable 0 p)
  rw [H]
  have hnonneg := subcriticalPrimitive_nonneg (pc := pc) (x := 0) ha.le
  change subcriticalPrimitive a pc p - subcriticalPrimitive a pc 0 ≤
    subcriticalPrimitive a pc p
  linarith

/-- Precise NEW half-slab kernel bound: the endpoint decay survives integration,
including p=pc and p=0, without a square-root derivative at the endpoint. -/
theorem subcritical_exp_sqrt_truncated_integral_le {pc p a : ℝ}
    (hp0 : 0 ≤ p) (hppc : p ≤ pc) (ha : 0 < a) :
    (∫ s in (0 : ℝ)..p, Real.exp (-a*Real.sqrt (pc-s))) ≤
      (4/a^2)*Real.exp (-(a/2)*Real.sqrt (pc-p)) := by
  have habs := one_add_mul_exp_neg_le
    (mul_nonneg ha.le (Real.sqrt_nonneg (pc-p)))
  calc
    _ ≤ (2/a^2)*(1+a*Real.sqrt (pc-p))*Real.exp (-a*Real.sqrt (pc-p)) :=
      subcritical_exp_sqrt_truncated_integral_le_primitive hp0 hppc ha
    _ = (2/a^2)*((1+a*Real.sqrt (pc-p))*Real.exp (-(a*Real.sqrt (pc-p)))) := by
      simp only [neg_mul]
      ring
    _ ≤ (2/a^2)*(2*Real.exp (-(a*Real.sqrt (pc-p))/2)) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := by
      have he : -(a*Real.sqrt (pc-p))/2 = -(a/2)*Real.sqrt (pc-p) := by ring
      rw [he]
      ring

/-- The deterministic source scale estimate on the half-slab range. -/
lemma half_slab_scale_ratio_le_real {n k : ℝ}
    (hn : 1 ≤ n) (_hk : 0 ≤ k) (hhalf : 2*k ≤ n) :
    (n+1)/(n-k)^2 ≤ 16/(n+1) := by
  have hnk : 0 < n-k := by linarith
  have hn1 : 0 < n+1 := by linarith
  have hscale : n+1 ≤ 4*(n-k) := by linarith
  have hsquare : (n+1)^2 ≤ (4*(n-k))^2 := by
    exact (sq_le_sq₀ hn1.le (by positivity)).mpr hscale
  apply (div_le_div_iff₀ (sq_pos_of_pos hnk) hn1).mpr
  nlinarith

/-- Actual natural slab height / integer starting height version. No truncation
of k or dimension convention is introduced. -/
lemma half_slab_scale_ratio_le {N : ℕ} {k : ℤ}
    (hN : 1 ≤ N) (hk : 0 ≤ k) (hhalf : 2*k ≤ (N : ℤ)) :
    ((N : ℝ)+1)/((N : ℝ)-(k : ℝ))^2 ≤ 16/((N : ℝ)+1) := by
  apply half_slab_scale_ratio_le_real
  · exact_mod_cast hN
  · exact_mod_cast hk
  · exact_mod_cast hhalf

/-- Multiplying by the nonnegative separation exponential preserves the exact
half-slab 1/(N+1) scale, rather than discarding its decay. -/
lemma half_slab_scale_ratio_mul_exp_le {N : ℕ} {k : ℤ} (z : ℝ)
    (hN : 1 ≤ N) (hk : 0 ≤ k) (hhalf : 2*k ≤ (N : ℤ)) :
    (((N : ℝ)+1)/((N : ℝ)-(k : ℝ))^2)*Real.exp z ≤
      (16/((N : ℝ)+1))*Real.exp z :=
  mul_le_mul_of_nonneg_right (half_slab_scale_ratio_le hN hk hhalf) (Real.exp_nonneg z)

end NearCritical
