module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Resampling outside a stopping set preserves a product law.

Let `ω₁, ω₂ : J → Bool` be two independent samples of a product law on a finite
index set, and let `E ω` be a STOPPING SET: a set of indices that is determined
by the values of `ω` on it (`ω'` agreeing with `ω` on `E ω` has `E ω' = E ω`).
The composite configuration `ω₁` on `E ω₁`, `ω₂` elsewhere, has the same
product law, and its stopping set is `E ω₁`.

This is the spatial Markov property of a cluster exploration in the form of a
coupling: the explored bonds keep their bits and every unexplored bond gets a
fresh independent bit (source: "conditionally on the `p_c`-clusters ... the
sprinkling in different tubes is independent", main.tex 6086-6088).
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Set

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Keep `ω₁` on its stopping set and use `ω₂` elsewhere. -/
def resample (E : (J → Bool) → Finset J) (q : (J → Bool) × (J → Bool)) : J → Bool :=
  fun j => if j ∈ E q.1 then q.1 j else q.2 j

/-- The stopping set of the composite is that of the first sample. -/
theorem resample_stoppingSet (E : (J → Bool) → Finset J)
    (hE : ∀ ω ω' : J → Bool, (∀ j ∈ E ω, ω' j = ω j) → E ω' = E ω)
    (q : (J → Bool) × (J → Bool)) : E (resample E q) = E q.1 :=
  hE q.1 (resample E q) fun j hj => by
    unfold resample
    rw [if_pos hj]

theorem resample_preimage_singleton (E : (J → Bool) → Finset J)
    (hE : ∀ ω ω' : J → Bool, (∀ j ∈ E ω, ω' j = ω j) → E ω' = E ω) (η : J → Bool) :
    resample E ⁻¹' {η} =
      (Set.pi univ fun j => if j ∈ E η then ({η j} : Set Bool) else univ) ×ˢ
        (Set.pi univ fun j => if j ∈ E η then (univ : Set Bool) else {η j}) := by
  ext ⟨ω₁, ω₂⟩
  simp only [mem_preimage, mem_singleton_iff, mem_prod, mem_pi, mem_univ, true_imp_iff]
  constructor
  · intro h
    have hagree : ∀ j ∈ E ω₁, η j = ω₁ j := fun j hj => by
      have := congrFun h j
      unfold resample at this
      rw [if_pos hj] at this
      exact this.symm
    have hEq : E η = E ω₁ := hE ω₁ η hagree
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j ∈ E η
      · rw [if_pos hj]
        exact (hagree j (hEq ▸ hj)).symm
      · rw [if_neg hj]
        exact mem_univ _
    · by_cases hj : j ∈ E η
      · rw [if_pos hj]
        exact mem_univ _
      · rw [if_neg hj]
        have := congrFun h j
        unfold resample at this
        rw [if_neg (by rw [← hEq]; exact hj)] at this
        exact this
  · rintro ⟨h1, h2⟩
    have hagree : ∀ j ∈ E η, ω₁ j = η j := fun j hj => by
      have := h1 j
      rw [if_pos hj] at this
      exact this
    have hEq : E ω₁ = E η := hE η ω₁ hagree
    funext j
    unfold resample
    by_cases hj : j ∈ E η
    · rw [if_pos (by rw [hEq]; exact hj)]
      exact hagree j hj
    · rw [if_neg (by rw [hEq]; exact hj)]
      have := h2 j
      rw [if_neg hj] at this
      exact this

/-- **Resampling law identity.** -/
theorem resample_law (μ : J → Measure Bool) [∀ j, IsProbabilityMeasure (μ j)]
    (E : (J → Bool) → Finset J)
    (hE : ∀ ω ω' : J → Bool, (∀ j ∈ E ω, ω' j = ω j) → E ω' = E ω) :
    Measure.map (resample E) ((Measure.pi μ).prod (Measure.pi μ)) = Measure.pi μ := by
  have hc : Measurable (resample E) := Measurable.of_discrete
  refine Measure.ext_of_singleton fun η => ?_
  rw [Measure.map_apply hc (measurableSet_singleton η), resample_preimage_singleton E hE η,
    Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Measure.pi_singleton,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ E η
  · rw [if_pos hj, if_pos hj, measure_univ, mul_one]
  · rw [if_neg hj, if_neg hj, measure_univ, one_mul]

end NearCritical
