module

public import NearCritical.SplitCrossPlacementCount

/-! Measurability and boundedness for the terminal count and its square. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical BigOperators

variable {d : ℕ}

theorem countIn_measurable (D : Set (Vertex d)) (Y : Finset (Vertex d)) (x : Vertex d) :
    Measurable (countIn D Y x) :=
  Finset.measurable_fun_sum Y fun y _ =>
    measurable_const.indicator (measurableSet_connectionToSetEvent D x {y})

theorem countIn_nonneg (D : Set (Vertex d)) (Y : Finset (Vertex d)) (x : Vertex d)
    (θ : Configuration d) : 0 ≤ countIn D Y x θ :=
  Finset.sum_nonneg fun y _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem countIn_le_card (D : Set (Vertex d)) (Y : Finset (Vertex d)) (x : Vertex d)
    (θ : Configuration d) : countIn D Y x θ ≤ (Y.card : ℝ) := by
  unfold countIn
  calc
    _ ≤ ∑ _y ∈ Y, (1 : ℝ) := Finset.sum_le_sum fun y _ => by
      by_cases h : θ ∈ connectionToSetEvent D x {y} <;> simp [h]
    _ = _ := by simp [nsmul_eq_mul]

theorem countIn_mono (D : Set (Vertex d)) {Y Z : Finset (Vertex d)} (hYZ : Y ⊆ Z)
    (x : Vertex d) (θ : Configuration d) : countIn D Y x θ ≤ countIn D Z x θ :=
  Finset.sum_le_sum_of_subset_of_nonneg hYZ fun y _ _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem countIn_pow_integrable (D : Set (Vertex d)) (Y : Finset (Vertex d)) (x : Vertex d)
    (p : unitInterval) (n : ℕ) :
    Integrable (fun θ => countIn D Y x θ ^ n) (percolation d p) := by
  refine Integrable.of_bound ((countIn_measurable D Y x).pow_const n).aestronglyMeasurable
    ((Y.card : ℝ) ^ n) (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (countIn_nonneg D Y x θ) _)]
  exact pow_le_pow_left₀ (countIn_nonneg D Y x θ) (countIn_le_card D Y x θ) _

theorem crossingPlacementCount_measurable (t : ℕ) (x : Vertex d) (axis : Fin d) :
    Measurable (crossingPlacementCount t x axis) :=
  ((Finset.measurable_fun_prod _ fun _ _ => countIn_measurable _ _ _).mul
    (Finset.measurable_fun_prod _ fun _ _ => countIn_measurable _ _ _)).indicator
      (Section10.measurableSet_crossAll t t x)

theorem crossingPlacementCount_integrable (t : ℕ) (x : Vertex d) (axis : Fin d)
    (p : unitInterval) (n : ℕ) :
    Integrable (fun θ => crossingPlacementCount t x axis θ ^ n) (percolation d p) := by
  let C := (∏ i : InteriorIndex d, ((nodeSites t x axis (interiorNode i)).card : ℝ)) *
    (∏ k : Fin (4 * d), ((nodeSites t x axis (face k)).card : ℝ))
  refine Integrable.of_bound ((crossingPlacementCount_measurable t x axis).pow_const n).aestronglyMeasurable
    (C ^ n) (Filter.Eventually.of_forall fun θ => ?_)
  have hN : 0 ≤ crossingPlacementCount t x axis θ := by
    unfold crossingPlacementCount
    exact Set.indicator_nonneg (fun ω _ => mul_nonneg
      (Finset.prod_nonneg fun _ _ => countIn_nonneg _ _ _ ω)
      (Finset.prod_nonneg fun _ _ => countIn_nonneg _ _ _ ω)) _
  have hNC : crossingPlacementCount t x axis θ ≤ C := by
    unfold crossingPlacementCount
    by_cases h : θ ∈ Section10.crossAll t t x
    · rw [Set.indicator_of_mem h]
      exact mul_le_mul
        (Finset.prod_le_prod₀ (fun _ _ => countIn_nonneg _ _ _ θ) (fun _ _ => countIn_le_card _ _ _ θ))
        (Finset.prod_le_prod₀ (fun _ _ => countIn_nonneg _ _ _ θ) (fun _ _ => countIn_le_card _ _ _ θ))
        (Finset.prod_nonneg fun _ _ => countIn_nonneg _ _ _ θ)
        (Finset.prod_nonneg fun _ _ => by positivity)
    · rw [Set.indicator_of_notMem h]
      exact mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
        (Finset.prod_nonneg fun _ _ => by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hN _)]
  exact pow_le_pow_left₀ hN hNC _

end NearCritical.SplitCrossDirect
