module

public import NearCritical.VariableSpeedWalkClockLaw
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section
noncomputable section

namespace NearCritical

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal Topology

/-- Independent uniform oriented proposals. -/
def variableSpeedDirectionsLaw (d : ℕ) : Measure (ℕ → Fin d × Bool) :=
  Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set (Fin d × Bool))

/-- Every prefix of length `n` of the proposal sequence has the same mass. -/
theorem variableSpeedDirections_prefix_probability {d : ℕ} (hd : 0 < d) (n : ℕ)
    (a : Fin n → Fin d × Bool) :
    ((variableSpeedDirectionsLaw d).map (fun s k => s k.val)).real {a} =
      ((2*d:ℝ)^n)⁻¹ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let U : ℕ → Set (Fin d × Bool) := fun j => if h : j < n then {a ⟨j,h⟩} else univ
  let I := Finset.range n
  let extract (s : ℕ → Fin d × Bool) (k : Fin n) := s k.val
  have hex : Measurable extract := measurable_pi_iff.mpr fun k => measurable_pi_apply k.val
  have hset : extract ⁻¹' {a} = Set.pi (I : Set ℕ) U := by
    ext s
    simp only [mem_preimage,mem_singleton_iff,Set.mem_pi,Finset.mem_coe, I, Finset.mem_range]
    constructor
    · intro h j hj
      have hj' := congrFun h ⟨j,hj⟩
      simpa only [U,dif_pos hj,mem_singleton_iff] using hj'
    · intro h
      funext k
      simpa only [U,dif_pos k.isLt,mem_singleton_iff] using h k.val k.isLt
  have hU (j : ℕ) (hj : j ∈ I) : MeasurableSet (U j) := by
    have hj' := Finset.mem_range.mp hj
    simp only [U,dif_pos hj',measurableSet_singleton]
  have hsingle (b : Fin d × Bool) :
      uniformOn (Set.univ : Set (Fin d × Bool)) {b} = (2*d:ℝ≥0∞)⁻¹ := by
    simp only [uniformOn_univ, Measure.count_singleton, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, one_div]
    rw [mul_comm (d:ℝ≥0∞) 2]
  change (((variableSpeedDirectionsLaw d).map extract) {a}).toReal = _
  rw [Measure.map_apply hex (measurableSet_singleton a),hset,variableSpeedDirectionsLaw,
    Measure.infinitePi_pi _ hU]
  have hp : (∏ j ∈ I, uniformOn (Set.univ : Set (Fin d × Bool)) (U j)) =
      ((2*d:ℝ≥0∞)⁻¹)^n := by
    calc
      _ = ∏ _j ∈ I, (2*d:ℝ≥0∞)⁻¹ := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [show U j = {a ⟨j,Finset.mem_range.mp hj⟩} from dif_pos (Finset.mem_range.mp hj),hsingle]
      _ = _ := by simp [I]
  rw [hp,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_mul,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast,inv_pow]

/-- Expectation of a fixed number of proposals under the infinite proposal
sequence law is the finite uniform average used in the one-time model. -/
theorem variableSpeedDirections_prefix_expectation {d : ℕ} (hd : 0 < d) (ω : Configuration d)
    (x : Vertex d) (n : ℕ) (f : Vertex d → ℝ) (C : ℝ) (hC : ∀ y, |f y| ≤ C) :
    (∫ s, f (variableSpeedEndpoint ω n x (fun k => s k.val)) ∂variableSpeedDirectionsLaw d) =
      (∑ a : Fin n → Fin d × Bool, f (variableSpeedEndpoint ω n x a))/(2*d:ℝ)^n := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let P := variableSpeedDirectionsLaw d
  letI : IsProbabilityMeasure P := by unfold P variableSpeedDirectionsLaw; infer_instance
  let extract (s : ℕ → Fin d × Bool) (k : Fin n) := s k.val
  let g (a : Fin n → Fin d × Bool) := f (variableSpeedEndpoint ω n x a)
  have hm : Measurable extract := measurable_pi_iff.mpr fun k => measurable_pi_apply k.val
  have hg : Measurable g := measurable_of_finite _
  letI : IsProbabilityMeasure (P.map extract) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hgi : Integrable g (P.map extract) :=
    Integrable.of_bound hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun a => by simpa only [Real.norm_eq_abs] using hC (variableSpeedEndpoint ω n x a))
  change (∫ s, g (extract s) ∂P) = _
  rw [← integral_map hm.aemeasurable hg.aestronglyMeasurable,integral_fintype hgi]
  simp only [P,extract,variableSpeedDirections_prefix_probability hd,smul_eq_mul]
  rw [div_eq_mul_inv,Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The standard exponential-interarrival description of the Poisson
clock, stated for the actual waiting-time count. -/
def ExponentialClockPoissonInput : Prop :=
  ∀ (r t : ℝ), 0 < r → 0 ≤ t →
    (variableSpeedWaitingLaw r).map (variableSpeedWaitingCount t) =
      poissonMeasure (Real.toNNReal (r*t))

/-- The actual path law and the uniformized one-time expectation agree
once the standard Poisson count law is supplied. -/
theorem variableSpeedSamplePath_expectation_of_clock (hclock : ExponentialClockPoissonInput)
    {d : ℕ} (hd : 0 < d) (ω : Configuration d) (x : Vertex d) (t : ℝ) (ht : 0 ≤ t)
    (f : Vertex d → ℝ) (C : ℝ) (hC : ∀ y, |f y| ≤ C) :
    (∫ s, f (variableSpeedSamplePath ω x s t) ∂variableSpeedSampleLaw d) =
      variableSpeedExpectation ω x t f := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let r := (2*d:ℝ)
  let P := variableSpeedWaitingLaw r
  let D := variableSpeedDirectionsLaw d
  have hr : 0 < r := mul_pos (by norm_num) (by exact_mod_cast hd)
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure P := by unfold P variableSpeedWaitingLaw; infer_instance
  letI : IsProbabilityMeasure D := by unfold D variableSpeedDirectionsLaw; infer_instance
  let g (s : (ℕ → ℝ) × (ℕ → Fin d × Bool)) := f (variableSpeedSamplePath ω x s t)
  let F (n : ℕ) := (∑ a : Fin n → Fin d × Bool, f (variableSpeedEndpoint ω n x a))/r^n
  have hg : Measurable g := (measurable_of_countable f).comp (measurable_variableSpeedSamplePath_eval ω x t)
  have hgi : Integrable g (P.prod D) :=
    Integrable.of_bound hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun s => by simpa only [g,Real.norm_eq_abs] using hC (variableSpeedSamplePath ω x s t))
  change (∫ s, g s ∂P.prod D) = _
  rw [integral_prod g hgi]
  calc
    _ = ∫ s, F (variableSpeedWaitingCount t s) ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s =>
        variableSpeedDirections_prefix_expectation hd ω x (variableSpeedWaitingCount t s) f C hC
    _ = ∫ n, F n ∂P.map (variableSpeedWaitingCount t) := by
      rw [integral_map (measurable_variableSpeedWaitingCount t).aemeasurable
        (measurable_of_countable F).aestronglyMeasurable]
    _ = _ := by
      rw [show P.map (variableSpeedWaitingCount t) = poissonMeasure (Real.toNNReal (r*t))
        from hclock r t hr ht]
      rfl

/-- The one-time Gaussian limit tested directly against the exponential-clock
and uniform-proposal sample law. -/
def VariableSpeedSampleGaussianMarginal (d : ℕ) (p : unitInterval) (i : Fin d) (v : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂percolation d p, ω ∈ infiniteClusterEvent d →
    ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun n : ℕ => ∫ s,
        f ((variableSpeedSamplePath ω 0 s (n:ℝ) i:ℝ)/Real.sqrt n) ∂variableSpeedSampleLaw d)
        atTop (𝓝 (∫ y, f y ∂gaussianReal 0 v))

/-- The Gaussian marginal of the actual sample path is the one used
in the diffusivity capstone. -/
theorem variableSpeedSampleGaussianMarginal_iff (hclock : ExponentialClockPoissonInput)
    {d : ℕ} (hd : 0 < d) (p : unitInterval) (i : Fin d) (v : ℝ≥0) :
    VariableSpeedSampleGaussianMarginal d p i v ↔ VariableSpeedGaussianMarginal d p i v := by
  have he (ω : Configuration d) (f : ℝ → ℝ) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
      (fun n : ℕ => ∫ s,
        f ((variableSpeedSamplePath ω 0 s (n:ℝ) i:ℝ)/Real.sqrt n) ∂variableSpeedSampleLaw d) =
      (fun n : ℕ => variableSpeedExpectation ω 0 (n:ℝ)
        (fun x => f ((x i:ℝ)/Real.sqrt n))) := by
    funext n
    exact variableSpeedSamplePath_expectation_of_clock hclock hd ω 0 n (Nat.cast_nonneg _)
      (fun x => f ((x i:ℝ)/Real.sqrt n)) C (fun x => hC _)
  unfold VariableSpeedSampleGaussianMarginal VariableSpeedGaussianMarginal
  constructor
  · intro h
    filter_upwards [h] with ω hω
    intro hinf f hf hbd
    obtain ⟨C,hC⟩ := hbd
    rw [← he ω f C hC]
    exact hω hinf f hf ⟨C,hC⟩
  · intro h
    filter_upwards [h] with ω hω
    intro hinf f hf hbd
    obtain ⟨C,hC⟩ := hbd
    rw [he ω f C hC]
    exact hω hinf f hf ⟨C,hC⟩

end NearCritical
