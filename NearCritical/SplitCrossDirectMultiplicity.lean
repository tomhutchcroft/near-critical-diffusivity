module

public import NearCritical.Events

/-! Generic multiplicity bound (for the direct proof of
`SplitCrossInput`).

`sum_measureReal_le_mul_of_multiplicity`: let `μ` be a finite measure, `B` a
finite index set, `(E β)` measurable events all contained in a measurable
event `A`. If every point lies in at most `K` of the events `E β`, `β ∈ B`, then

  `Σ_{β ∈ B} μ(E β) ≤ K · μ(A)`.

Proof: `Σ_β 1_{E β} ≤ K · 1_A` pointwise; integrate.

`measureReal_ge_sum_div_of_multiplicity`: the same as a lower bound for `μ(A)`
when `K > 0`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory
open scoped Classical BigOperators

theorem sum_measureReal_le_mul_of_multiplicity {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Finset ι) (E : ι → Set Ω) (A : Set Ω)
    (hE : ∀ β ∈ B, MeasurableSet (E β)) (hA : MeasurableSet A) (hsub : ∀ β ∈ B, E β ⊆ A)
    (K : ℕ) (hK : ∀ ω, (B.filter fun β => ω ∈ E β).card ≤ K) :
    ∑ β ∈ B, μ.real (E β) ≤ (K : ℝ) * μ.real A := by
  have hint : ∀ β ∈ B, Integrable ((E β).indicator (fun _ => (1 : ℝ))) μ :=
    fun β hβ => (integrable_const (1 : ℝ)).indicator (hE β hβ)
  have hintA : Integrable (fun ω => (K : ℝ) * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hA).const_mul _
  have hpt : ∀ ω, ∑ β ∈ B, (E β).indicator (fun _ => (1 : ℝ)) ω ≤
      (K : ℝ) * A.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hcount : ∑ β ∈ B, (E β).indicator (fun _ => (1 : ℝ)) ω =
        ((B.filter fun β => ω ∈ E β).card : ℝ) := by
      rw [← Finset.sum_boole]
      exact Finset.sum_congr rfl (fun β _ => Set.indicator_apply _ _ _)
    rw [hcount]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, mul_one]
      exact_mod_cast hK ω
    · rw [Set.indicator_of_notMem hω, mul_zero]
      have hempty : (B.filter fun β => ω ∈ E β) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun β hβ h => hω (hsub β hβ h))
      rw [hempty]
      simp
  have hsum : ∑ β ∈ B, μ.real (E β) =
      ∫ ω, ∑ β ∈ B, (E β).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
    rw [integral_finset_sum B hint]
    refine Finset.sum_congr rfl (fun β hβ => ?_)
    have h : (∫ ω, (E β).indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real (E β) :=
      integral_indicator_one (hE β hβ)
    exact h.symm
  have hAint : (∫ ω, (K : ℝ) * A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = (K : ℝ) * μ.real A := by
    rw [integral_const_mul]
    have h : (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real A := integral_indicator_one hA
    rw [h]
  rw [hsum, ← hAint]
  exact integral_mono (integrable_finset_sum B hint) hintA hpt

theorem measureReal_ge_sum_div_of_multiplicity {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Finset ι) (E : ι → Set Ω) (A : Set Ω)
    (hE : ∀ β ∈ B, MeasurableSet (E β)) (hA : MeasurableSet A) (hsub : ∀ β ∈ B, E β ⊆ A)
    (K : ℕ) (hKpos : 0 < K) (hK : ∀ ω, (B.filter fun β => ω ∈ E β).card ≤ K) :
    (∑ β ∈ B, μ.real (E β)) / (K : ℝ) ≤ μ.real A := by
  have h := sum_measureReal_le_mul_of_multiplicity μ B E A hE hA hsub K hK
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  rw [div_le_iff₀ hKR]
  linarith

end NearCritical.SplitCrossDirect
end
