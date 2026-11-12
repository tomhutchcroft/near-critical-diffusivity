module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The nearest-neighbour bond model. Every undirected lattice bond has exactly
one index `(base, positive coordinate direction)`, so no doubled edge variables
are introduced. Probability is Mathlib's infinite product measure. -/
@[expose] public section

namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev Vertex (d : ℕ) := Fin d → ℤ
abbrev Bond (d : ℕ) := Vertex d × Fin d
abbrev Configuration (d : ℕ) := Bond d → Bool

def bondTip {d : ℕ} (e : Bond d) : Vertex d :=
  Function.update e.1 e.2 (e.1 e.2 + 1)

lemma bondTip_ne_base {d : ℕ} (e : Bond d) : bondTip e ≠ e.1 := by
  intro h
  have := congrFun h e.2
  simp [bondTip] at this

def openGraph {d : ℕ} (ω : Configuration d) : SimpleGraph (Vertex d) where
  Adj x y := ∃ e : Bond d, ω e = true ∧
    ((x = e.1 ∧ y = bondTip e) ∨ (y = e.1 ∧ x = bondTip e))
  symm := ⟨by
    rintro x y ⟨e, he, h | h⟩
    · exact ⟨e, he, Or.inr h⟩
    · exact ⟨e, he, Or.inl h⟩⟩
  loopless := ⟨by
    rintro x ⟨e, _, h | h⟩ <;> exact bondTip_ne_base e (h.2.symm.trans h.1)⟩

noncomputable def percolation (d : ℕ) (p : unitInterval) : Measure (Configuration d) :=
  Measure.infinitePi (fun _ : Bond d ↦ bernoulliMeasure true false p)

instance (d : ℕ) (p : unitInterval) : IsProbabilityMeasure (percolation d p) := by
  unfold percolation
  infer_instance

/-- A cluster includes its starting vertex even if every incident edge is closed. -/
def cluster {d : ℕ} (ω : Configuration d) (x : Vertex d) : Set (Vertex d) :=
  {y | (openGraph ω).Reachable x y}

def connectionEvent {d : ℕ} (x y : Vertex d) : Set (Configuration d) :=
  {ω | (openGraph ω).Reachable x y}

def infiniteClusterEvent (d : ℕ) : Set (Configuration d) :=
  {ω | (cluster ω (0 : Vertex d)).Infinite}

noncomputable def twoPoint (d : ℕ) (p : unitInterval) (x y : Vertex d) : ℝ :=
  (percolation d p).real (connectionEvent x y)

noncomputable def density (d : ℕ) (p : unitInterval) : ℝ :=
  (percolation d p).real (infiniteClusterEvent d)

/-- Infimum within `[0,1]`, whose complete lattice structure handles endpoints. -/
noncomputable def criticalPoint (d : ℕ) : unitInterval :=
  sInf {p | 0 < density d p}

/-- Euclidean, rather than the sup norm on the function space `Fin d → ℤ`. -/
noncomputable def euclideanNorm {d : ℕ} (x : Vertex d) : ℝ :=
  Real.sqrt (∑ i, (x i : ℝ) ^ 2)

/-- Assumption (A), translated to a limit from the origin at Euclidean infinity.
Translation invariance of the product measure is a separate theorem to prove. -/
def TwoPointAsymptotics (d : ℕ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ Filter.Tendsto
    (fun x : Vertex d ↦ twoPoint d (criticalPoint d) 0 x /
      euclideanNorm x ^ ((2 : ℝ) - (d : ℝ)))
    (Filter.comap euclideanNorm Filter.atTop) (nhds A)

/-- Every indexed bond has the intended Bernoulli marginal. -/
theorem percolation_open_bond (d : ℕ) (p : unitInterval) (e : Bond d) :
    percolation d p {ω | ω e = true} = ENNReal.ofReal (p : ℝ) := by
  have hp : ENNReal.ofReal (p : ℝ) = (unitInterval.toNNReal p : ℝ≥0∞) :=
    by simpa only [unitInterval.coe_toNNReal] using
      (ENNReal.ofReal_coe_nnreal (p := unitInterval.toNNReal p))
  rw [hp]
  have h := Measure.infinitePi_map_eval
    (fun _ : Bond d ↦ bernoulliMeasure true false p) e
  have h' := congrArg (fun μ : Measure Bool ↦ μ {true}) h
  rw [Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton true)] at h'
  have hs : (fun f : Configuration d ↦ f e) ⁻¹' ({true} : Set Bool) =
      {ω | ω e = true} := by
    ext ω
    simp
  rw [hs] at h'
  simpa [percolation, bernoulliMeasure_def] using h' 

/-- Finite open-edge cylinders have product probabilities. -/
theorem percolation_open_cylinder (d : ℕ) (p : unitInterval) (s : Finset (Bond d)) :
    percolation d p (Set.pi (s : Set (Bond d)) (fun _ ↦ {true})) =
      ∏ _e ∈ s, ENNReal.ofReal (p : ℝ) := by
  have hp : ENNReal.ofReal (p : ℝ) = (unitInterval.toNNReal p : ℝ≥0∞) :=
    by simpa only [unitInterval.coe_toNNReal] using
      (ENNReal.ofReal_coe_nnreal (p := unitInterval.toNNReal p))
  simp_rw [hp]
  unfold percolation
  rw [Measure.infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton true)]
  simp [bernoulliMeasure_def]

end NearCritical
