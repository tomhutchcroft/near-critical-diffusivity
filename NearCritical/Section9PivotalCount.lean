module

public import NearCritical.Section9Pivotal
public import NearCritical.Events
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Section9 actual pivot-count measurability and first-moment expansion.
The finite measure is explicit so the conditional remaining-bond law can later
be substituted. No conditional independence, regularity or diagram estimate
is assumed or proved by these identities. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical BigOperators

lemma measurableSet_sprinklingUnexplored_adj {d : ℕ}
    (T Q F : Finset (Vertex d)) (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | (sprinklingUnexploredGraph ω T Q F).Adj x y} := by
  exact (measurableSet_open_adj x y).inter (MeasurableSet.const _)

lemma measurableSet_sprinklingUnexploredCluster_mem {d : ℕ}
    (T Q F : Finset (Vertex d)) (root y : Vertex d) :
    MeasurableSet {ω : Configuration d | y ∈ sprinklingUnexploredCluster ω T Q F root} := by
  have heq : {ω : Configuration d | y ∈ sprinklingUnexploredCluster ω T Q F root} =
      {ω : Configuration d | y ∈ T} ∩
        {ω | (sprinklingUnexploredGraph ω T Q F).Reachable root y} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_sprinklingUnexploredCluster]
  rw [heq]
  exact (MeasurableSet.const (y ∈ T)).inter
    (measurableSet_graphReachable (fun ω => sprinklingUnexploredGraph ω T Q F)
      (measurableSet_sprinklingUnexplored_adj T Q F) root y)

lemma measurableSet_sprinklingUnexploredCluster_hits {d : ℕ}
    (T Q F A : Finset (Vertex d)) (root : Vertex d) :
    MeasurableSet {ω : Configuration d | (sprinklingUnexploredCluster ω T Q F root ∩ A).Nonempty} := by
  have heq : {ω : Configuration d | (sprinklingUnexploredCluster ω T Q F root ∩ A).Nonempty} =
      ⋃ x : Vertex d, {ω | x ∈ sprinklingUnexploredCluster ω T Q F root} ∩ {ω | x ∈ A} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Finset.Nonempty, Finset.mem_inter]
  rw [heq]
  exact MeasurableSet.iUnion (fun x =>
    (measurableSet_sprinklingUnexploredCluster_mem T Q F root x).inter (MeasurableSet.const _))

lemma measurableSet_sprinklingUnexploredClusters_disjoint {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (a b : Vertex d) :
    MeasurableSet {ω : Configuration d |
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ a)
        (sprinklingUnexploredCluster ω R Q₃ F₃ b)} := by
  have heq : {ω : Configuration d |
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ a)
        (sprinklingUnexploredCluster ω R Q₃ F₃ b)} =
      ⋂ z : Vertex d, ({ω | z ∈ sprinklingUnexploredCluster ω L Q₁ F₁ a} ∩
        {ω | z ∈ sprinklingUnexploredCluster ω R Q₃ F₃ b})ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff,
      Set.mem_inter_iff, Finset.disjoint_left, not_and]
  rw [heq]
  exact MeasurableSet.iInter (fun z =>
    ((measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ a z).inter
      (measurableSet_sprinklingUnexploredCluster_mem R Q₃ F₃ b z)).compl)

lemma measurableSet_sprinklingPivotalPair {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    MeasurableSet {ω : Configuration d | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} := by
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter
      ((measurableSet_sprinklingUnexploredCluster_hits L Q₁ F₁ A e.1).inter
        ((measurableSet_sprinklingUnexploredCluster_hits R Q₃ F₃ B e.2).inter
          (measurableSet_sprinklingUnexploredClusters_disjoint L R Q₁ F₁ Q₃ F₃ e.1 e.2)))))

/-- Actual critical pivotal-edge indicator, with both orientation and full-cluster
conditions taken from the canonical Section9 predicate. -/
def section9PivotalIndicator {d : ℕ} (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (e : Vertex d × Vertex d) (ω : Configuration d) : ℝ :=
  if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e then 1 else 0

/-- Actual source #piv(A,B), not a free random variable with assumed moments. -/
def section9PivotalCount {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (ω : Configuration d) : ℝ :=
  ((sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A B).card : ℝ)

lemma section9PivotalCount_eq_sum {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (ω : Configuration d) :
    section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω =
      ∑ e ∈ E, section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω := by
  unfold section9PivotalIndicator
  rw [Finset.sum_boole]
  rfl

lemma section9PivotalCount_nonneg {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (ω : Configuration d) :
    0 ≤ section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω := Nat.cast_nonneg _

private lemma pivotalIndicator_eq_indicator {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e =
      ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} : Set (Configuration d)).indicator
        (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases h : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e <;>
    simp [section9PivotalIndicator, Set.indicator, h]

private lemma pivotalCount_fun_eq_sum {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B =
      fun ω => ∑ e ∈ E, section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω := by
  funext ω
  exact section9PivotalCount_eq_sum E L R Q₁ F₁ Q₃ F₃ A B ω

lemma measurable_section9PivotalIndicator {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    Measurable (section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e) := by
  exact measurable_const.piecewise (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e)
    measurable_const

lemma measurable_section9PivotalCount {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    Measurable (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B) := by
  rw [pivotalCount_fun_eq_sum]
  exact E.measurable_fun_sum (fun e _ => measurable_section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e)

lemma integrable_section9PivotalIndicator {d : ℕ} (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    Integrable (section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e) μ := by
  rw [pivotalIndicator_eq_indicator]
  exact (integrable_const (μ := μ) (1 : ℝ)).indicator
    (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e)

lemma integrable_section9PivotalCount {d : ℕ} (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    Integrable (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B) μ := by
  rw [pivotalCount_fun_eq_sum]
  exact integrable_finsetSum E (fun e _ => integrable_section9PivotalIndicator μ L R Q₁ F₁ Q₃ F₃ A B e)

/-- Exact first-moment identity under the actual selected finite law. No edge
probability estimate is supplied or hidden in the count's definition. -/
theorem integral_section9PivotalCount {d : ℕ} (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (∫ ω, section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∂μ) =
      ∑ e ∈ E, μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} := by
  simp_rw [section9PivotalCount_eq_sum]
  rw [integral_finsetSum E (fun e _ => integrable_section9PivotalIndicator μ L R Q₁ F₁ Q₃ F₃ A B e)]
  apply Finset.sum_congr rfl
  intro e _
  rw [pivotalIndicator_eq_indicator]
  exact integral_indicator_one (μ := μ) (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e)

end NearCritical
