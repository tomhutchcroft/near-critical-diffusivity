module

public import NearCritical.Events

/-! Endpoint Bernoulli laws and actual endpoint infinite-cluster geometry. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Set

@[simp] theorem percolation_zero (d : ℕ) :
    percolation d 0 = Measure.dirac (fun _ : Bond d ↦ false) := by
  simp [percolation]

@[simp] theorem percolation_one (d : ℕ) :
    percolation d 1 = Measure.dirac (fun _ : Bond d ↦ true) := by
  simp [percolation]

lemma openGraph_allClosed (d : ℕ) :
    openGraph (fun _ : Bond d ↦ false) = ⊥ := by
  ext x y
  simp [openGraph]

lemma cluster_allClosed (d : ℕ) (x : Vertex d) :
    cluster (fun _ : Bond d ↦ false) x = {x} := by
  ext y
  simp [cluster, openGraph_allClosed, SimpleGraph.reachable_bot, eq_comm]

lemma allClosed_not_infinite (d : ℕ) :
    (fun _ : Bond d ↦ false) ∉ infiniteClusterEvent d := by
  simp [infiniteClusterEvent, cluster_allClosed]

/-- A positive-coordinate ray starting at the origin. -/
def coordinateRay {d : ℕ} (i : Fin d) (n : ℕ) : Vertex d :=
  Function.update 0 i (n : ℤ)

lemma coordinateRay_injective {d : ℕ} (i : Fin d) :
    Function.Injective (coordinateRay i) := by
  intro n m h
  have hi := congrFun h i
  simpa [coordinateRay] using hi

lemma bondTip_coordinateRay {d : ℕ} (i : Fin d) (n : ℕ) :
    bondTip (coordinateRay i n, i) = coordinateRay i (n + 1) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [bondTip, coordinateRay]
  · simp [bondTip, coordinateRay, h]

lemma allOpen_reachable_coordinateRay {d : ℕ} (i : Fin d) (n : ℕ) :
    (openGraph (fun _ : Bond d ↦ true)).Reachable 0 (coordinateRay i n) := by
  induction n with
  | zero => simp [coordinateRay]
  | succ n ih =>
    apply ih.trans
    apply SimpleGraph.Adj.reachable
    exact ⟨(coordinateRay i n, i), rfl, Or.inl ⟨rfl, (bondTip_coordinateRay i n).symm⟩⟩

/-- In positive dimension the all-open cluster contains an infinite coordinate
ray; no connectivity or infinite-cluster assertion is assumed as a premise. -/
lemma allOpen_infiniteCluster (d : ℕ) (hd : 0 < d) :
    (fun _ : Bond d ↦ true) ∈ infiniteClusterEvent d := by
  let i : Fin d := ⟨0, hd⟩
  apply (Set.infinite_range_of_injective (coordinateRay_injective i)).mono
  rintro x ⟨n, rfl⟩
  exact allOpen_reachable_coordinateRay i n

@[simp] theorem density_zero (d : ℕ) : density d 0 = 0 := by
  simp [density, Measure.real, Measure.dirac_apply', measurableSet_infiniteClusterEvent,
    allClosed_not_infinite]

@[simp] theorem density_one (d : ℕ) (hd : 0 < d) : density d 1 = 1 := by
  simp [density, Measure.real, Measure.dirac_apply', measurableSet_infiniteClusterEvent,
    allOpen_infiniteCluster d hd]

lemma percolating_parameters_nonempty (d : ℕ) (hd : 0 < d) :
    ({p : unitInterval | 0 < density d p} : Set unitInterval).Nonempty := by
  exact ⟨1, by simp [density_one d hd]⟩

end NearCritical
