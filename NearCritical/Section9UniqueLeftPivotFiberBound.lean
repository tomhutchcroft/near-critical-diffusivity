module
public import NearCritical.Section9UniqueLeftPivotBridge
public import NearCritical.Section9UniqueLeftPivotCount
public import NearCritical.Section9OrientedClusterBoundary
public import NearCritical.Section9AvoidanceHeartComparison

/-! Actual good-exit fiber masses count distinct canonical unique-left pivots. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem fiber_bound_measurable_of_locality {d : ℕ}
    (s : Finset (Bond d)) (A : Set (Configuration d))
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ A ↔ θ ∈ A)) :
    MeasurableSet A := by
  let A₀ : Set ((b : s) → Bool) := {ξ | extendConfiguration s (fun _ => false) ξ ∈ A}
  have heq : A = s.restrict ⁻¹' A₀ := by
    ext ω
    apply hlocal ω (extendConfiguration s (fun _ => false) (s.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  rw [heq]
  exact (Set.toFinite A₀).measurableSet.preimage (Finset.measurable_restrict s)

private theorem fiber_bound_card_sum {α : Type*} [DecidableEq α]
    (K P : Finset α) (hsub : P ⊆ K) :
    (∑ e ∈ K, if e ∈ P then (1 : ℝ) else 0) = (P.card : ℝ) := by
  have hfilter : K.filter (fun e => e ∈ P) = P := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hsub h,h⟩⟩
  rw [Finset.sum_boole,hfilter]

/-- Under any finite law, good exits on a fixed actual left fiber count
 distinct actual canonical pivots with the prescribed unique left label,
 restricted to that same actual cluster fiber.
 No conditional law, positive fiber mass or expected-count estimate is assumed. -/
theorem section9_unique_left_pivotal_fiber_bound {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (i : Fin d) (n : ℕ) (hn : 0 < n)
    (F₁ F₃ C W B : Finset (Vertex d)) (x : Vertex d)
    (hxL : x ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hUnique : C ∩ W = {x}) :
    let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let V := section9ExitFace i n ∩ C
    let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ x = C}
    (∑ t ∈ section9AvoidanceGoodLastExitCandidates R C Q₃ F₃ V,
      μ.real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2)) ≤
      ∫ ω in E, ((section9UniqueLeftPivotalPairs ω
        (orientedLatticePairs (section9FiniteMiddle i n)) L R Q₁ F₁ Q₃ F₃ W B x).card : ℝ) ∂μ := by
  intro L R Q₁ Q₃ V E
  let J := section9AvoidanceGoodLastExitCandidates R C Q₃ F₃ V
  let K := orientedLatticePairs (section9FiniteMiddle i n)
  let P := fun ω : Configuration d => section9UniqueLeftPivotalPairs ω K L R Q₁ F₁ Q₃ F₃ W B x
  let A := fun t : (Vertex d × Vertex d) × Bond d =>
    E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2
  have hE : MeasurableSet E := by
    apply fiber_bound_measurable_of_locality (sprinklingAvailableBonds L Q₁ F₁) E
    intro ω θ hagree
    have heq := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hagree x
    simp only [E,Set.mem_setOf_eq,heq]
  have hA (t : (Vertex d × Vertex d) × Bond d) : MeasurableSet (A t) :=
    hE.inter ((measurableSet_sprinklingUnexploredCluster_hits (R \ C) Q₃ F₃ B t.1.2).inter
      (measurableSet_sprinklingUnexploredCluster_hits R Q₃ F₃ V t.1.2).compl)
  have hPsub (ω : Configuration d) : P ω ⊆ K := by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
  have hPmeas (e : Vertex d × Vertex d) : MeasurableSet {ω | e ∈ P ω} := by
    let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
    apply fiber_bound_measurable_of_locality U
    intro ω θ hagree
    have heqL := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ
      (fun b hb => hagree b (Finset.mem_union_left _ hb)) e.1
    have heqR := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ
      (fun b hb => hagree b (Finset.mem_union_right _ hb)) e.2
    simp only [Set.mem_setOf_eq,P,section9UniqueLeftPivotalPairs,sprinklingPivotalPairs,
      Finset.mem_filter,sprinklingPivotalPair,heqL,heqR]
  have hPsum (ω : Configuration d) : ((P ω).card : ℝ) =
      ∑ e ∈ K, ({θ : Configuration d | e ∈ P θ}).indicator (fun _ => (1 : ℝ)) ω := by
    simpa only [Set.indicator_apply,Set.mem_setOf_eq] using
      (fiber_bound_card_sum K (P ω) (hPsub ω)).symm
  have hIntP : Integrable (fun ω => ((P ω).card : ℝ)) μ := by
    simp_rw [hPsum]
    exact integrable_finsetSum K (fun e _ => (integrable_const (1 : ℝ)).indicator (hPmeas e))
  have hIntA : Integrable (fun ω => ∑ t ∈ J, (A t).indicator (fun _ => (1 : ℝ)) ω) μ :=
    integrable_finsetSum J (fun t _ => (integrable_const (1 : ℝ)).indicator (hA t))
  have hpoint (ω : Configuration d) :
      (∑ t ∈ J, (A t).indicator (fun _ => (1 : ℝ)) ω) ≤ ((P ω).card : ℝ) := by
    let S := J.filter (fun t => ω ∈ A t)
    have hsum : (∑ t ∈ J, (A t).indicator (fun _ => (1 : ℝ)) ω) = (S.card : ℝ) := by
      simp only [Set.indicator_apply]
      rw [Finset.sum_boole]
    have hinj : Set.InjOn (fun t : (Vertex d × Vertex d) × Bond d => t.1) (S : Set _) := by
      intro t ht t' ht' heq
      have htJ := (Finset.mem_filter.mp ht).1
      have ht'J := (Finset.mem_filter.mp ht').1
      exact section9_last_exit_candidate_projection_injOn i n C F₃
        (Finset.mem_filter.mp htJ).1 (Finset.mem_filter.mp ht'J).1 heq
    have hsub : S.image (fun t => t.1) ⊆ P ω := by
      intro e he
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨htJ,htA⟩ := Finset.mem_filter.mp ht
      obtain ⟨hfiber,hsuffix⟩ := htA
      have hb := section9_unique_left_good_exit_pivotal_bridge ω i n hn F₁ F₃ C W B x
        hxL hfiber hUnique t htJ hsuffix
      exact Finset.mem_filter.mpr hb
    rw [hsum]
    have hcard : S.card ≤ (P ω).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    exact_mod_cast hcard
  have hpointFiber (ω : Configuration d) :
      (∑ t ∈ J, (A t).indicator (fun _ => (1 : ℝ)) ω) ≤
        E.indicator (fun θ => ((P θ).card : ℝ)) ω := by
    by_cases hω : ω ∈ E
    · simpa only [Set.indicator_of_mem hω] using hpoint ω
    · have hnot (t : (Vertex d × Vertex d) × Bond d) : ω ∉ A t :=
        fun ht => hω ht.1
      simp only [Set.indicator_apply,if_neg hω]
      apply Finset.sum_nonpos
      intro t _
      simp only [if_neg (hnot t),le_refl]
  have hcompare := integral_mono hIntA (hIntP.indicator hE) hpointFiber
  have hleft : (∫ ω, ∑ t ∈ J, (A t).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      ∑ t ∈ J, μ.real (A t) := by
    rw [integral_finsetSum J (fun t _ => (integrable_const (1 : ℝ)).indicator (hA t))]
    apply Finset.sum_congr rfl
    intro t _
    exact integral_indicator_one (μ := μ) (hA t)
  rw [hleft,integral_indicator hE] at hcompare
  exact hcompare

end NearCritical
