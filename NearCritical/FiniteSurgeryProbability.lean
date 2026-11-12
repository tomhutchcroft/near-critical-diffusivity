module
public import NearCritical.FiniteBlockResampling

/-! Finite-energy comparison from an actual bounded-coordinate surgery. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Every individual assignment has at least the minimum Bernoulli mass.
A nonnegative finite observable taking a value at least one therefore has
expectation at least that mass, including p=0 and p=1. -/
theorem finiteExpectation_ge_min_assignment {E : Type*} [Fintype E]
    (p : unitInterval) (f : (E → Bool) → ℝ) (hf : ∀ η, 0 ≤ f η)
    (η : E → Bool) (hη : 1 ≤ f η) :
    (min (p : ℝ) (1-(p : ℝ)))^(Fintype.card E) ≤ finiteExpectation (p : ℝ) f := by
  let m := min (p : ℝ) (1-(p : ℝ))
  let w := fun ξ : E → Bool => ∏ e : E, if ξ e then (p : ℝ) else 1-(p : ℝ)
  have hm : 0 ≤ m := le_min p.property.1 (sub_nonneg.mpr p.property.2)
  have hw (ξ : E → Bool) : 0 ≤ w ξ := by
    apply Finset.prod_nonneg
    intro e _
    split
    · exact p.property.1
    · exact sub_nonneg.mpr p.property.2
  have hweight : m^(Fintype.card E) ≤ w η := by
    calc
      _ = ∏ _e : E, m := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hm) (fun e _ => by
        split
        · exact min_le_left _ _
        · exact min_le_right _ _)
  calc
    _ ≤ w η := hweight
    _ ≤ f η*w η := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hη (hw η)
    _ ≤ ∑ ξ : E → Bool, f ξ*w ξ :=
      Finset.single_le_sum (fun ξ _ => mul_nonneg (hf ξ) (hw ξ)) (Finset.mem_univ η)
    _ = _ := rfl

/-- An actual surgery on the fixed finite mask S gives a probability lower
bound. Events are arbitrary finite cylinders; the surgery need not preserve
open bits or be monotone, and may depend on the original configuration. -/
theorem percolation_finite_surgery_probability {d : ℕ} (p : unitInterval)
    (G S : Finset (Bond d)) (A B : Set (G → Bool))
    (hsurgery : ∀ ω : Configuration d, G.restrict ω ∈ B →
      ∃ θ : Configuration d, (∀ b, b ∉ S → θ b = ω b) ∧ G.restrict θ ∈ A) :
    (min (p : ℝ) (1-(p : ℝ)))^S.card * (percolation d p).real (G.restrict ⁻¹' B) ≤
      (percolation d p).real (G.restrict ⁻¹' A) := by
  let c : ℝ := (min (p : ℝ) (1-(p : ℝ)))^S.card
  let H : (G → Bool) → ℝ := fun ξ => if ξ ∈ A then 1 else 0
  let J : Configuration d → ℝ := fun ω => if G.restrict ω ∈ B then 1 else 0
  have hRestr : Measurable (G.restrict : Configuration d → (G → Bool)) :=
    Finset.measurable_restrict G
  have hA : MeasurableSet ((G.restrict : Configuration d → (G → Bool)) ⁻¹' A) :=
    (Set.toFinite A).measurableSet.preimage hRestr
  have hB : MeasurableSet ((G.restrict : Configuration d → (G → Bool)) ⁻¹' B) :=
    (Set.toFinite B).measurableSet.preimage hRestr
  have hiJ : Integrable J (percolation d p) := by
    have hJ : J = ((G.restrict : Configuration d → (G → Bool)) ⁻¹' B).indicator
        (fun _ : Configuration d => (1 : ℝ)) := by
      funext ω
      simp only [J,Set.indicator_apply,Set.mem_preimage]
    rw [hJ]
    exact (integrable_const (1 : ℝ)).indicator hB
  have hiAvg : Integrable
      (fun ω => resampleAverage p G S H ((G \ S : Finset (Bond d)).restrict ω)) (percolation d p) := by
    have hi := integrable_two_block_product p (G \ S) ∅ (resampleAverage p G S H) (fun _ => (1 : ℝ))
    simpa only [mul_one] using hi
  have hbound (ω : Configuration d) :
      c*J ω ≤ resampleAverage p G S H ((G \ S : Finset (Bond d)).restrict ω) := by
    by_cases hω : G.restrict ω ∈ B
    · obtain ⟨θ,hagree,hθ⟩ := hsurgery ω hω
      have hresample : resampleBonds S ω θ = θ := by
        funext b
        by_cases hb : b ∈ S
        · simp [resampleBonds,extendConfiguration,hb]
        · simpa only [resampleBonds,extendConfiguration,dif_neg hb] using (hagree b hb).symm
      have heq := resampleBonds_restrict G S ω θ
      rw [hresample] at heq
      have hmass := finiteExpectation_ge_min_assignment p
        (fun η => H (mergeResampledBits G S η ((G \ S : Finset (Bond d)).restrict ω)))
        (fun η => by dsimp [H]; split <;> norm_num) (S.restrict θ)
        (by rw [← heq]; simp [H,hθ])
      have havg : resampleAverage p G S H ((G \ S : Finset (Bond d)).restrict ω) =
          finiteExpectation (p : ℝ)
            (fun η => H (mergeResampledBits G S η ((G \ S : Finset (Bond d)).restrict ω))) :=
        integral_finite_bernoulli p _
      rw [havg]
      simpa only [c,J,if_pos hω,mul_one,Fintype.card_coe] using hmass
    · have havg : 0 ≤ resampleAverage p G S H ((G \ S : Finset (Bond d)).restrict ω) :=
        integral_nonneg (fun η => by dsimp [H]; split <;> norm_num)
      simpa only [J,if_neg hω,mul_zero] using havg
  have hb := integral_mono (hiJ.const_mul c) hiAvg hbound
  rw [integral_const_mul,integral_resampleAverage] at hb
  have hJA : (∫ ω, H (G.restrict ω) ∂percolation d p) =
      (percolation d p).real (G.restrict ⁻¹' A) := by
    simpa only [H,Set.indicator_apply,Set.mem_preimage,Pi.one_apply] using
      integral_indicator_one (μ := percolation d p) hA
  have hJB : (∫ ω, J ω ∂percolation d p) =
      (percolation d p).real (G.restrict ⁻¹' B) := by
    simpa only [J,Set.indicator_apply,Set.mem_preimage,Pi.one_apply] using
      integral_indicator_one (μ := percolation d p) hB
  rw [hJA,hJB] at hb
  exact hb

end NearCritical
