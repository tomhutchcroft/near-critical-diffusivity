module
public import NearCritical.Section9PhysicalTargetVariance

/-! Actual fresh target-count lower tail with overlapping physical pools. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Chebyshev with the proved physical overlap variance, without an
independence premise on target successes. -/
theorem section9_physical_target_success_lower_tail {d : ℕ} {ι : Type*}
    (q : unitInterval) (I : Finset ι) (pools : ι → Finset (Bond d)) :
    let Y := fun ζ : Configuration d =>
      ∑ j ∈ I, if ∃ b ∈ pools j, ζ b = true then (1 : ℝ) else 0
    let m := ∫ ζ, Y ζ ∂percolation d q
    0 < m → (percolation d q).real {ζ | Y ζ ≤ m/2} ≤
      4*(m+(q : ℝ)*(∑ i ∈ I, ∑ j ∈ I.erase i,
        ((pools i ∩ pools j).card : ℝ)))/m^2 := by
  intro Y m hm
  let μ := percolation d q
  let U := I.biUnion pools
  let g := fun ζ : Configuration d => (Y ζ-m)^2
  have hi : Integrable g μ := by
    apply section9_finite_local_integrable μ U
    intro ζ θ hagree
    have hY : Y ζ = Y θ := by
      apply Finset.sum_congr rfl
      intro j hj
      have he : (∃ b ∈ pools j, ζ b = true) ↔ (∃ b ∈ pools j, θ b = true) := by
        constructor
        · rintro ⟨b,hb,hζ⟩
          exact ⟨b,hb,(hagree b (Finset.mem_biUnion.mpr ⟨j,hj,hb⟩)).symm.trans hζ⟩
        · rintro ⟨b,hb,hθ⟩
          exact ⟨b,hb,(hagree b (Finset.mem_biUnion.mpr ⟨j,hj,hb⟩)).trans hθ⟩
      exact if_congr he rfl rfl
    dsimp only [g]
    rw [hY]
  have ht : 0 < (m/2)^2 := sq_pos_of_pos (by linarith)
  have hsub : {ζ : Configuration d | Y ζ ≤ m/2} ⊆ {ζ | (m/2)^2 ≤ g ζ} := by
    intro ζ hζ
    change Y ζ ≤ m/2 at hζ
    change (m/2)^2 ≤ (Y ζ-m)^2
    have hdiff : m/2 ≤ m-Y ζ := by linarith
    have hs := pow_le_pow_left₀ (by linarith : 0 ≤ m/2) hdiff 2
    nlinarith only [hs]
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ζ => sq_nonneg (Y ζ-m))) hi ((m/2)^2)
  have hprob : μ.real {ζ | (m/2)^2 ≤ g ζ} ≤ (∫ ζ, g ζ ∂μ)/(m/2)^2 := by
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm] using hMarkov
  have hv := section9_physical_target_success_variance_le q I pools
  have hbound := (measureReal_mono (μ := μ) hsub).trans
    (hprob.trans (div_le_div_of_nonneg_right hv ht.le))
  change μ.real {ζ | Y ζ ≤ m/2} ≤ _
  convert hbound using 1
  field_simp [ne_of_gt hm]
  <;> ring

end NearCritical
