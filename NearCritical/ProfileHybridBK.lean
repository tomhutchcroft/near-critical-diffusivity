module

public import NearCritical.BulkSupercriticalBound
public import NearCritical.CountableBK

/-! Hybrid BK under the actual thinning coupling. One probability retains its
full lower profile; only the other is replaced by homogeneous percolation. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

lemma increasing_thin_fixed_preimage {E : Type*} {A : Set (E → Bool)}
    (hA : BK.Increasing A) (η : E → Bool) :
    BK.Increasing ((fun ω => thinConfiguration (ω,η)) ⁻¹' A) := by
  intro ω θ h hω
  apply hA _ hω
  intro e he
  have hh := Bool.and_eq_true_iff.mp he
  exact Bool.and_eq_true_iff.mpr ⟨h e hh.1,hh.2⟩

lemma thin_disjointOccurrence_hybrid {E : Type*} {A B : Set (E → Bool)}
    (hA : BK.Increasing A) (hB : BK.Increasing B) (ω η : E → Bool)
    (hD : DisjointOccurrence A B (thinConfiguration (ω,η))) :
    DisjointOccurrence ((fun θ => thinConfiguration (θ,η)) ⁻¹' A) B ω := by
  obtain ⟨F,H,hFinF,hFinH,hdis,hF,hH,hAF,hBH⟩ :=
    BK.openDisjointOccurrence_of_disjointOccurrence hD
  have hFo : ∀ e ∈ F, ω e = true ∧ η e = true := by
    intro e he
    exact Bool.and_eq_true_iff.mp (hF e he)
  have hHo : ∀ e ∈ H, ω e = true ∧ η e = true := by
    intro e he
    exact Bool.and_eq_true_iff.mp (hH e he)
  refine ⟨F,H,hFinF,hFinH,hdis,?_,?_⟩
  · intro θ hagree
    change thinConfiguration (θ,η) ∈ A
    apply hA _ hAF
    intro e he
    have heF := (BK.openMask_eq_true F e).mp he
    exact Bool.and_eq_true_iff.mpr ⟨(hagree e heF).trans (hFo e heF).1,(hFo e heF).2⟩
  · intro θ hagree
    apply hB _ hBH
    intro e he
    have heH := (BK.openMask_eq_true H e).mp he
    exact (hagree e heH).trans (hHo e heH).1

lemma percolation_bk_ennreal (d : ℕ) (p : unitInterval)
    (A B : Set (Configuration d)) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    percolation d p {ω | DisjointOccurrence A B ω} ≤
      percolation d p A * percolation d p B := by
  have h := ENNReal.ofReal_le_ofReal (percolation_bk d p A B hA hB)
  have hreal : ∀ S : Set (Configuration d),
      ENNReal.ofReal ((percolation d p).real S) = percolation d p S := by
    intro S
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [ENNReal.ofReal_mul measureReal_nonneg] at h
  simpa only [hreal] using h

theorem profile_hybrid_bk_of_thinning {d : ℕ} (p : unitInterval)
    (q r : Bond d → unitInterval) (hr : ∀ e, (r e : ℝ) = (p : ℝ)*(q e : ℝ))
    (A B : Set (Configuration d)) (hmA : MeasurableSet A)
    (hA : BK.Increasing A) (hB : BK.Increasing B) :
    percolationProfile d r {ω | DisjointOccurrence A B ω} ≤
      percolationProfile d r A * percolation d p B := by
  let μ := percolation d p
  let ν := percolationProfile d q
  let D : Set (Configuration d) := {ω | DisjointOccurrence A B ω}
  let S := thinConfiguration ⁻¹' D
  let T := thinConfiguration ⁻¹' A
  have hmD : MeasurableSet D := measurableSet_disjointOccurrence hA hB
  have hmS : MeasurableSet S := measurable_thinConfiguration hmD
  have hmT : MeasurableSet T := measurable_thinConfiguration hmA
  have hmap := percolationProfile_thin_map d p q r hr
  have hleft : percolationProfile d r D = (μ.prod ν) S := by
    rw [← hmap,Measure.map_apply measurable_thinConfiguration hmD]
  have hright : percolationProfile d r A = (μ.prod ν) T := by
    rw [← hmap,Measure.map_apply measurable_thinConfiguration hmA]
  change percolationProfile d r D ≤ percolationProfile d r A * μ B
  rw [hleft,hright]
  calc
    _ = ∫⁻ η, μ ((fun ω => (ω,η)) ⁻¹' S) ∂ν := Measure.prod_apply_symm hmS
    _ ≤ ∫⁻ η, μ ((fun ω => thinConfiguration (ω,η)) ⁻¹' A) * μ B ∂ν := by
      apply lintegral_mono
      intro η
      have hsub : ((fun ω => (ω,η)) ⁻¹' S) ⊆
          {ω | DisjointOccurrence ((fun θ => thinConfiguration (θ,η)) ⁻¹' A) B ω} :=
        fun ω hω => thin_disjointOccurrence_hybrid hA hB ω η hω
      exact (measure_mono hsub).trans
        (percolation_bk_ennreal d p _ B (increasing_thin_fixed_preimage hA η) hB)
    _ = (∫⁻ η, μ ((fun ω => thinConfiguration (ω,η)) ⁻¹' A) ∂ν) * μ B :=
      lintegral_mul_const' _ _ (measure_ne_top _ _)
    _ = (μ.prod ν) T * μ B := by
      rw [Measure.prod_apply_symm hmT]
      rfl

/-- Actual arbitrary-profile hybrid bound. The domination is CONSTRUCTED by
independent thinning; no inhomogeneous BK inequality is supplied as an input. -/
theorem profile_hybrid_bk {d : ℕ} (p : unitInterval) (r : Bond d → unitInterval)
    (hr : ∀ e, (r e : ℝ) ≤ (p : ℝ)) (A B : Set (Configuration d))
    (hmA : MeasurableSet A) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    percolationProfile d r {ω | DisjointOccurrence A B ω} ≤
      percolationProfile d r A * percolation d p B := by
  by_cases hp : (p : ℝ) = 0
  · apply profile_hybrid_bk_of_thinning p (fun _ => 1) r _ A B hmA hA hB
    intro e
    have hre : (r e : ℝ) = 0 := le_antisymm (by simpa [hp] using hr e) (r e).2.1
    simp [hre,hp]
  · have hpos : 0 < (p : ℝ) := lt_of_le_of_ne p.2.1 (Ne.symm hp)
    let q : Bond d → unitInterval := fun e =>
      ⟨(r e : ℝ)/(p : ℝ),div_nonneg (r e).2.1 p.2.1,(div_le_one hpos).mpr (hr e)⟩
    apply profile_hybrid_bk_of_thinning p q r _ A B hmA hA hB
    intro e
    dsimp [q]
    field_simp

end NearCritical
