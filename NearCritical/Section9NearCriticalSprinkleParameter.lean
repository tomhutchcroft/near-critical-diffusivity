module
public import NearCritical.Section9SprinkleOrLaw
public import NearCritical.CriticalPointInterior

/-! Exact near-critical parameter selection for the independent enrichment. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- The actual enrichment parameter is exactly p+Lambda/n² at all large
scales, and its fresh rate has q*n² at least Lambda. -/
theorem section9_eventual_sprinkle_parameter (p : unitInterval) (hp : (p : ℝ) < 1)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∃ q : unitInterval,
      (orParameter p q : ℝ) = (p : ℝ)+Λ/(n : ℝ)^2 ∧ Λ ≤ (q : ℝ)*(n : ℝ)^2 := by
  have hgap : 0 < 1-(p : ℝ) := sub_pos.mpr hp
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (Λ/(1-(p : ℝ))))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNnat : 1 ≤ N := by exact_mod_cast hN1.le
  refine ⟨N,hNnat,?_⟩
  intro n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := hN1.le.trans hnR
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hnsq : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hquot : Λ/(1-(p : ℝ)) ≤ (n : ℝ)^2 :=
    ((le_max_right _ _).trans hN.le).trans (hnR.trans hnsq)
  have hΛbound : Λ ≤ (1-(p : ℝ))*(n : ℝ)^2 := by
    simpa only [mul_comm] using (div_le_iff₀ hgap).mp hquot
  let q : ℝ := Λ/((1-(p : ℝ))*(n : ℝ)^2)
  have hden : 0 < (1-(p : ℝ))*(n : ℝ)^2 := mul_pos hgap (sq_pos_of_pos hn0)
  have hq0 : 0 ≤ q := div_nonneg hΛ.le hden.le
  have hq1 : q ≤ 1 := (div_le_one hden).mpr hΛbound
  refine ⟨⟨q,⟨hq0,hq1⟩⟩,?_,?_⟩
  · change (p : ℝ)+(1-(p : ℝ))*q = (p : ℝ)+Λ/(n : ℝ)^2
    dsimp only [q]
    field_simp [ne_of_gt hgap,ne_of_gt hn0]
    <;> ring
  · have heq : q*(n : ℝ)^2 = Λ/(1-(p : ℝ)) := by
      dsimp only [q]
      field_simp [ne_of_gt hgap,ne_of_gt hn0]
      <;> ring
    change Λ ≤ q*(n : ℝ)^2
    rw [heq]
    apply (le_div_iff₀ hgap).mpr
    have hgap1 : 1-(p : ℝ) ≤ 1 := by linarith [p.property.1]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgap1 hΛ.le

/-- Critical-point interior is discharged by the standing two-point
asymptotics, rather than supplied as a new input to the source theorem. -/
theorem section9_critical_eventual_sprinkle_parameter {d : ℕ} (hd : 9 ≤ d)
    (i : Fin d) (asymptotics : TwoPointAsymptotics d) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∃ q : unitInterval,
      (orParameter (criticalPoint d) q : ℝ) = (criticalPoint d : ℝ)+Λ/(n : ℝ)^2 ∧
        Λ ≤ (q : ℝ)*(n : ℝ)^2 :=
  section9_eventual_sprinkle_parameter (criticalPoint d)
    (criticalPoint_lt_one_of_twoPointAsymptotics (by omega) i asymptotics) Λ hΛ

end NearCritical
