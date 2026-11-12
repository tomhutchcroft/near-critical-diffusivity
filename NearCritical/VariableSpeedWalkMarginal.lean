module

public import NearCritical.PercolationMonotonicity
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section
noncomputable section

namespace NearCritical

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

/-- The bond and target of an oriented nearest-neighbor proposal. -/
def variableSpeedProposal {d : ℕ} (x : Vertex d) (j : Fin d × Bool) :
    Bond d × Vertex d :=
  if j.2 then ((x,j.1),bondTip (x,j.1))
  else
    let y := Function.update x j.1 (x j.1-1)
    ((y,j.1),y)

/-- One proposal at the uniformization clock. A closed bond leaves the
walk at its current vertex. -/
def variableSpeedStep {d : ℕ} (ω : Configuration d) (x : Vertex d) (j : Fin d × Bool) : Vertex d :=
  let e := variableSpeedProposal x j
  if ω e.1 then e.2 else x

/-- The generator in the paper, indexed by the two orientations of
each coordinate axis. Each open bond contributes rate one. -/
def variableSpeedGenerator {d : ℕ} (ω : Configuration d) (f : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  ∑ j : Fin d × Bool, let e := variableSpeedProposal x j
    if ω e.1 then f e.2 - f x else 0

theorem variableSpeedGenerator_eq_proposal_difference {d : ℕ}
    (ω : Configuration d) (f : Vertex d → ℝ) (x : Vertex d) :
    variableSpeedGenerator ω f x =
      ∑ j : Fin d × Bool, (f (variableSpeedStep ω x j)-f x) := by
  unfold variableSpeedGenerator variableSpeedStep
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  split_ifs <;> simp

/-- Every proposal keeps the walk on the current open cluster. -/
theorem variableSpeedStep_eq_or_adj {d : ℕ} (ω : Configuration d)
    (x : Vertex d) (j : Fin d × Bool) :
    variableSpeedStep ω x j = x ∨ (openGraph ω).Adj x (variableSpeedStep ω x j) := by
  obtain ⟨i,b⟩ := j
  cases b
  · let y := Function.update x i (x i-1)
    have htip : bondTip (y,i) = x := by
      funext k
      by_cases hk : k = i
      · subst k
        simp [bondTip,y]
      · simp [bondTip,y,Function.update_of_ne hk]
    by_cases ho : ω (y,i) = true
    · right
      change (openGraph ω).Adj x (if ω (y,i) then y else x)
      rw [if_pos ho]
      exact ⟨(y,i),ho,Or.inr ⟨rfl,htip.symm⟩⟩
    · left
      exact if_neg ho
  · by_cases ho : ω (x,i) = true
    · right
      change (openGraph ω).Adj x (if ω (x,i) then bondTip (x,i) else x)
      rw [if_pos ho]
      exact ⟨(x,i),ho,Or.inl ⟨rfl,rfl⟩⟩
    · left
      exact if_neg ho

/-- Endpoint after a finite sequence of proposals. -/
def variableSpeedEndpoint {d : ℕ} (ω : Configuration d) :
    (n : ℕ) → Vertex d → (Fin n → Fin d × Bool) → Vertex d
  | 0,x,_ => x
  | n+1,x,f => variableSpeedEndpoint ω n (variableSpeedStep ω x (f 0)) (Fin.tail f)

theorem variableSpeedEndpoint_reachable {d : ℕ} (ω : Configuration d)
    (n : ℕ) (x : Vertex d) (f : Fin n → Fin d × Bool) :
    (openGraph ω).Reachable x (variableSpeedEndpoint ω n x f) := by
  induction n generalizing x with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    have h := ih (variableSpeedStep ω x (f 0)) (Fin.tail f)
    rcases variableSpeedStep_eq_or_adj ω x (f 0) with he | ha
    · simpa only [variableSpeedEndpoint,he] using h
    · exact ha.reachable.trans h

/-- Expectation at time `t` under the variable-speed walk. The
uniformization clock has rate `2*d`; conditional on its count,
the proposals are independent and uniform. -/
def variableSpeedExpectation {d : ℕ} (ω : Configuration d) (x : Vertex d)
    (t : ℝ) (f : Vertex d → ℝ) : ℝ :=
  let rate := Real.toNNReal ((2*d:ℝ)*t)
  ∫ n : ℕ, ((∑ a : Fin n → Fin d × Bool, f (variableSpeedEndpoint ω n x a)) / (2*d:ℝ)^n)
    ∂poissonMeasure rate

/-- The one-time quenched marginal of the invariance principle,
tested against bounded continuous functions of a coordinate. -/
def VariableSpeedGaussianMarginal (d : ℕ) (p : unitInterval) (i : Fin d) (v : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂percolation d p, ω ∈ infiniteClusterEvent d →
    ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun n : ℕ => variableSpeedExpectation ω 0 (n:ℝ)
        (fun x => f ((x i:ℝ)/Real.sqrt n))) atTop (𝓝 (∫ y, f y ∂gaussianReal 0 v))

/-- Above criticality the quenched Gaussian marginal determines the
variance uniquely, since the origin belongs to the infinite cluster
with positive probability. -/
theorem VariableSpeedGaussianMarginal.variance_unique {d : ℕ} {p : unitInterval}
    {i : Fin d} {v₁ v₂ : ℝ≥0} (hp : criticalPoint d < p)
    (h₁ : VariableSpeedGaussianMarginal d p i v₁)
    (h₂ : VariableSpeedGaussianMarginal d p i v₂) : v₁ = v₂ := by
  refine (gaussianReal_ext_iff.mp (show gaussianReal 0 v₁ = gaussianReal 0 v₂ from ?_)).2
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hf : ∃ C : ℝ, ∀ x, |f x| ≤ C :=
    ⟨‖f‖, fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩
  unfold VariableSpeedGaussianMarginal at h₁ h₂
  have he : ∀ᵐ ω ∂percolation d p, ω ∈ infiniteClusterEvent d →
      (∫ y, f y ∂gaussianReal 0 v₁) = ∫ y, f y ∂gaussianReal 0 v₂ := by
    filter_upwards [h₁,h₂] with ω hω₁ hω₂ hω
    exact tendsto_nhds_unique (hω₁ hω f f.continuous hf) (hω₂ hω f f.continuous hf)
  by_contra hn
  have hzero : percolation d p (infiniteClusterEvent d) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (he.mono fun _ h hx => hn (h hx))
  have hd := density_pos_above_critical hp
  rw [density,measureReal_def,hzero,ENNReal.toReal_zero] at hd
  exact (lt_irrefl _ hd)

end NearCritical
