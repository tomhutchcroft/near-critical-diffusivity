module

public import NearCritical.TranslationInvariance

/-! Exact formulations of source assumption (A). These equivalences do not
assert that the critical two-point asymptotic holds in any dimension. -/
@[expose] public section
namespace NearCritical
open Filter

lemma euclideanNorm_neg {d : ℕ} (x : Vertex d) :
    euclideanNorm (-x) = euclideanNorm x := by
  simp [euclideanNorm]

lemma euclideanNorm_sub_comm {d : ℕ} (x y : Vertex d) :
    euclideanNorm (x - y) = euclideanNorm (y - x) := by
  rw [← neg_sub x y, euclideanNorm_neg]

/-- The source limit over arbitrary pairs whose Euclidean separation tends to infinity. -/
def PairTwoPointAsymptotics (d : ℕ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ Tendsto
    (fun z : Vertex d × Vertex d => twoPoint d (criticalPoint d) z.1 z.2 /
      euclideanNorm (z.1 - z.2) ^ ((2 : ℝ) - (d : ℝ)))
    (comap (fun z : Vertex d × Vertex d => euclideanNorm (z.1 - z.2)) atTop) (nhds A)

/-- Stationarity identifies the origin limit with the arbitrary-pair limit,
with the same asymptotic coefficient. -/
theorem twoPoint_limit_iff_pair {d : ℕ} (p : unitInterval) (A : ℝ) :
    Tendsto (fun x : Vertex d => twoPoint d p 0 x /
      euclideanNorm x ^ ((2 : ℝ) - (d : ℝ)))
      (comap euclideanNorm atTop) (nhds A) ↔
    Tendsto (fun z : Vertex d × Vertex d => twoPoint d p z.1 z.2 /
      euclideanNorm (z.1 - z.2) ^ ((2 : ℝ) - (d : ℝ)))
      (comap (fun z : Vertex d × Vertex d => euclideanNorm (z.1 - z.2)) atTop)
      (nhds A) := by
  constructor
  · intro h
    have hd : Tendsto (fun z : Vertex d × Vertex d => z.2 - z.1)
        (comap (fun z : Vertex d × Vertex d => euclideanNorm (z.1 - z.2)) atTop)
        (comap euclideanNorm atTop) := by
      rw [tendsto_comap_iff]
      simpa only [Function.comp_def, euclideanNorm_sub_comm] using
        (tendsto_comap (f := fun z : Vertex d × Vertex d => euclideanNorm (z.1 - z.2))
          (x := atTop))
    simpa only [Function.comp_def, ← twoPoint_eq_displacement,
      euclideanNorm_sub_comm] using h.comp hd
  · intro h
    have hd : Tendsto (fun x : Vertex d => ((0 : Vertex d), x))
        (comap euclideanNorm atTop)
        (comap (fun z : Vertex d × Vertex d => euclideanNorm (z.1 - z.2)) atTop) := by
      rw [tendsto_comap_iff]
      simpa only [Function.comp_def, zero_sub, euclideanNorm_neg] using
        (tendsto_comap (f := @euclideanNorm d) (x := atTop))
    simpa only [Function.comp_def, zero_sub, euclideanNorm_neg] using h.comp hd

theorem twoPointAsymptotics_iff_pair (d : ℕ) :
    TwoPointAsymptotics d ↔ PairTwoPointAsymptotics d := by
  unfold TwoPointAsymptotics PairTwoPointAsymptotics
  simp only [twoPoint_limit_iff_pair]

/-- Uniform in both endpoints: the radius depends on epsilon, not on the
location of either vertex. The denominator is the source Euclidean power. -/
theorem twoPoint_pair_limit_iff_uniform {d : ℕ} (p : unitInterval) (A : ℝ) :
    Tendsto (fun z : Vertex d × Vertex d => twoPoint d p z.1 z.2 /
      euclideanNorm (z.1 - z.2) ^ ((2 : ℝ) - (d : ℝ)))
      (comap (fun z : Vertex d × Vertex d => euclideanNorm (z.1 - z.2)) atTop)
      (nhds A) ↔
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : Vertex d,
      R ≤ euclideanNorm (x - y) →
      |twoPoint d p x y / euclideanNorm (x - y) ^ ((2 : ℝ) - (d : ℝ)) - A| < ε := by
  simp only [Metric.tendsto_nhds, Real.dist_eq, eventually_comap, eventually_atTop]
  constructor
  · intro h ε hε
    obtain ⟨R, hR⟩ := h ε hε
    refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x y hxy
    exact hR _ (le_trans (le_max_left _ _) hxy) (x, y) rfl
  · intro h ε hε
    obtain ⟨R, _, hR⟩ := h ε hε
    refine ⟨R, ?_⟩
    intro r hr z hz
    exact hR z.1 z.2 (hz ▸ hr)

/-- Assumption (A) is exactly a positive common coefficient with a uniform
large-separation error bound. No asymptotic estimate is assumed additionally. -/
theorem twoPointAsymptotics_iff_uniform (d : ℕ) :
    TwoPointAsymptotics d ↔ ∃ A : ℝ, 0 < A ∧
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : Vertex d,
        R ≤ euclideanNorm (x - y) →
        |twoPoint d (criticalPoint d) x y /
          euclideanNorm (x - y) ^ ((2 : ℝ) - (d : ℝ)) - A| < ε := by
  rw [twoPointAsymptotics_iff_pair]
  unfold PairTwoPointAsymptotics
  simp only [twoPoint_pair_limit_iff_uniform]

/-- A consequence of the explicit source assumption, uniform in both endpoints.
This only supplies bounds beyond a positive radius, not a global Green bound. -/
theorem twoPointAsymptotics_eventual_bounds {d : ℕ} (h : TwoPointAsymptotics d) :
    ∃ c C R : ℝ, 0 < c ∧ 0 < C ∧ 0 < R ∧ ∀ x y : Vertex d,
      R ≤ euclideanNorm (x - y) →
      c * euclideanNorm (x - y) ^ ((2 : ℝ) - (d : ℝ)) ≤
        twoPoint d (criticalPoint d) x y ∧
      twoPoint d (criticalPoint d) x y ≤
        C * euclideanNorm (x - y) ^ ((2 : ℝ) - (d : ℝ)) := by
  obtain ⟨A, hA, hlim⟩ := (twoPointAsymptotics_iff_uniform d).mp h
  obtain ⟨R, hR, htail⟩ := hlim (A / 2) (half_pos hA)
  refine ⟨A / 2, 3 * A / 2, R, half_pos hA, by positivity, hR, ?_⟩
  intro x y hxy
  have hpow := Real.rpow_pos_of_pos (lt_of_lt_of_le hR hxy) ((2 : ℝ) - (d : ℝ))
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (htail x y hxy)
  constructor
  · apply (le_div_iff₀ hpow).mp
    linarith
  · apply (div_le_iff₀ hpow).mp
    linarith

end NearCritical
