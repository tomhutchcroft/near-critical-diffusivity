module
public import NearCritical.Section9PhysicalTargetMean
public import NearCritical.Section9PhysicalTargetConcentration

/-! Fixed-configuration quantitative many-target fresh success. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Actual active-pool and overlap bounds suffice for many fresh successes.
The deterministic scale threshold is independent of target-size caps. -/
theorem section9_physical_target_success_probability_lower {d : ℕ} {ι : Type*}
    (q : unitInterval) (I : Finset ι) (pools : ι → Finset (Bond d))
    (c0 K F ε : ℝ) (m : ℕ) (hc0 : 0 < c0) (hK : 0 ≤ K) (hF : 0 < F) (hε : 0 < ε)
    (hactive : c0*F ≤ ((I.filter (fun j => (pools j).Nonempty)).card : ℝ))
    (hover : (∑ i ∈ I, ∑ j ∈ I.erase i, ((pools i ∩ pools j).card : ℝ)) ≤ K*F)
    (hscale : max (2*((m : ℝ)+1)/c0) (4*(1+K/c0)/(ε*c0)) ≤ (q : ℝ)*F) :
    1-ε ≤ (percolation d q).real {ζ : Configuration d | (m : ℝ) <
      ∑ j ∈ I, if ∃ b ∈ pools j, ζ b = true then (1 : ℝ) else 0} := by
  let μ := percolation d q
  let Y := fun ζ : Configuration d =>
    ∑ j ∈ I, if ∃ b ∈ pools j, ζ b = true then (1 : ℝ) else 0
  let a := ∫ ζ, Y ζ ∂μ
  let R := (q : ℝ)*F
  let κ := K/c0
  have hκ : 0 ≤ κ := div_nonneg hK hc0.le
  have hmean : c0*R ≤ a := by
    have hh := (mul_le_mul_of_nonneg_left hactive q.property.1).trans
      (section9_physical_target_success_mean_lower q I pools)
    simpa only [R,mul_assoc,mul_comm,mul_left_comm] using hh
  have hfirst : 2*((m : ℝ)+1) ≤ c0*R := by
    have hh := (le_max_left _ _).trans hscale
    have ht := (div_le_iff₀ hc0).mp hh
    simpa only [R,mul_comm] using ht
  have ha : 0 < a := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith only [hfirst,hmean,hm]
  have hsecond : 4*(1+κ) ≤ ε*(c0*R) := by
    have hh := (le_max_right _ _).trans hscale
    have ht := (div_le_iff₀ (mul_pos hε hc0)).mp hh
    simpa only [κ,R,mul_assoc,mul_comm,mul_left_comm] using ht
  have hea : 4*(1+κ) ≤ ε*a := hsecond.trans (mul_le_mul_of_nonneg_left hmean hε.le)
  have hcov : (q : ℝ)*(∑ i ∈ I, ∑ j ∈ I.erase i,
      ((pools i ∩ pools j).card : ℝ)) ≤ κ*a := by
    have hh := mul_le_mul_of_nonneg_left hover q.property.1
    have hk := mul_le_mul_of_nonneg_left hmean hκ
    have heq : κ*(c0*R) = (q : ℝ)*(K*F) := by
      dsimp only [κ,R]
      field_simp [ne_of_gt hc0]
      <;> ring
    exact hh.trans (heq ▸ hk)
  have htail := section9_physical_target_success_lower_tail q I pools ha
  have htailε : μ.real {ζ | Y ζ ≤ a/2} ≤ ε := by
    refine htail.trans ?_
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    have hnum : 4*(a+(q : ℝ)*(∑ i ∈ I, ∑ j ∈ I.erase i,
        ((pools i ∩ pools j).card : ℝ))) ≤ 4*(1+κ)*a := by nlinarith only [hcov]
    have hh := mul_le_mul_of_nonneg_right hea ha.le
    nlinarith only [hnum,hh]
  have hcover : (Set.univ : Set (Configuration d)) ⊆
      {ζ | Y ζ ≤ a/2} ∪ {ζ | (m : ℝ) < Y ζ} := by
    intro ζ _
    by_cases hζ : Y ζ ≤ a/2
    · exact Or.inl hζ
    · apply Or.inr
      change (m : ℝ) < Y ζ
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith only [hζ,hfirst,hmean,hm]
  have hp := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
  have hone : μ.real (Set.univ : Set (Configuration d)) = 1 := by simp [μ]
  rw [hone] at hp
  change 1-ε ≤ μ.real {ζ | (m : ℝ) < Y ζ}
  linarith only [hp,htailε]

end NearCritical
