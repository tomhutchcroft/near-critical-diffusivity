module

public import NearCritical.Section9CoalescenceSplit
public import NearCritical.Section9PivotalCount

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical ENNReal

theorem measurableSet_section9_sprinkling_member {d : ℕ}
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (z : Vertex d) :
    MeasurableSet {ξη : Configuration d × Configuration d |
      z ∈ section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A B} := by
  simp only [mem_section9SprinklingCluster, sprinkledPivotalPairs, sprinklingPivotalPairs,
    Finset.mem_filter, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro e
  exact (((MeasurableSet.const (e ∈ P)).inter
    ((measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).preimage measurable_fst)).inter
    ((measurableSet_open_adj e.1 e.2).preimage measurable_snd)).inter
    (((measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ e.1 z).preimage measurable_fst).union
      ((measurableSet_sprinklingUnexploredCluster_mem R Q₃ F₃ e.2 z).preimage measurable_fst))

theorem measurableSet_section9_coalescence_event {d : ℕ}
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (x y : Vertex d) :
    MeasurableSet {ξη : Configuration d × Configuration d |
      (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {x} B ∩
        section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty} := by
  simp only [Finset.Nonempty, Finset.mem_inter, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro z
  exact (measurableSet_section9_sprinkling_member P L R Q₁ F₁ Q₃ F₃ {x} B z).inter
    (measurableSet_section9_sprinkling_member P L R Q₁ F₁ Q₃ F₃ {y} B z)

private theorem section9_coalescence_count_eq_indicators {d : ℕ}
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ X Y B : Finset (Vertex d))
    (ξη : Configuration d × Configuration d) :
      (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) =
        ∑ xy ∈ X.product Y, ({ζ : Configuration d × Configuration d |
          (section9SprinklingCluster ζ.1 ζ.2 P L R Q₁ F₁ Q₃ F₃ {xy.1} B ∩
            section9SprinklingCluster ζ.1 ζ.2 P L R Q₁ F₁ Q₃ F₃ {xy.2} B).Nonempty} :
          Set (Configuration d × Configuration d)).indicator (fun _ => (1 : ℝ)) ξη := by
  simp only [section9CoalescenceCount, section9CoalescencePairs, Finset.card_eq_sum_ones,
      Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Set.indicator_apply, Set.mem_setOf_eq]

/-- The expected count of actual coalescing ordered pairs is exactly
the sum of the corresponding event probabilities. -/
theorem integral_section9_coalescence_count {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ X Y B : Finset (Vertex d)) :
    (∫ ξη, (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) ∂μ) =
      ∑ x ∈ X, ∑ y ∈ Y, μ.real {ξη |
        (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {x} B ∩
          section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty} := by
  let E := fun xy : Vertex d × Vertex d => {ξη : Configuration d × Configuration d |
    (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {xy.1} B ∩
      section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {xy.2} B).Nonempty}
  have hE (xy) : MeasurableSet (E xy) :=
    measurableSet_section9_coalescence_event P L R Q₁ F₁ Q₃ F₃ B xy.1 xy.2
  have hcount (ξη : Configuration d × Configuration d) :
      (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) =
        ∑ xy ∈ X.product Y, (E xy).indicator (fun _ => (1 : ℝ)) ξη :=
    section9_coalescence_count_eq_indicators P L R Q₁ F₁ Q₃ F₃ X Y B ξη
  simp_rw [hcount]
  rw [integral_finsetSum _ (fun xy _ => (integrable_const (1 : ℝ)).indicator (hE xy))]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact integral_indicator_one (hE (x,y))

/-- The expected count is bounded by the sum of the four contributions,
including both orientations of the cross event. -/
theorem integral_section9_coalescence_le_cases {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ X Y B : Finset (Vertex d)) :
    let C := fun ω => sprinklingUnexploredCluster ω L Q₁ F₁
    let D := fun ω => sprinklingUnexploredCluster ω R Q₃ F₃
    let O := fun (ξη : Configuration d × Configuration d) z =>
      sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {z} B
    let A₁ := fun x y => {ξη : Configuration d × Configuration d |
      (C ξη.1 x ∩ C ξη.1 y).Nonempty ∧ (O ξη x).Nonempty}
    let A₂ := fun a b => {ξη : Configuration d × Configuration d |
      ∃ e ∈ O ξη a, ∃ f ∈ O ξη b, Disjoint (C ξη.1 e.1) (C ξη.1 f.1) ∧
        (D ξη.1 e.2 ∩ C ξη.1 f.1).Nonempty}
    let H := fun x y => {ξη : Configuration d × Configuration d |
      (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {x} B ∩
        section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty}
    let A₃ := fun x y => {ξη ∈ H x y | ∀ e ∈ O ξη x, ∀ f ∈ O ξη y,
      Disjoint (C ξη.1 e.1) (C ξη.1 f.1) ∧ Disjoint (C ξη.1 e.1) (D ξη.1 f.2) ∧
      Disjoint (D ξη.1 e.2) (C ξη.1 f.1)}
    (∫ ξη, (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) ∂μ) ≤
      (∑ x ∈ X, ∑ y ∈ Y, μ.real (A₁ x y)) +
      ((∑ x ∈ X, ∑ y ∈ Y, μ.real (A₂ x y)) +
      ((∑ y ∈ Y, ∑ x ∈ X, μ.real (A₂ y x)) +
       (∑ x ∈ X, ∑ y ∈ Y, μ.real (A₃ x y)))) := by
  intro C D O A₁ A₂ H A₃
  rw [integral_section9_coalescence_count]
  calc
    _ ≤ ∑ x ∈ X, ∑ y ∈ Y,
        (μ.real (A₁ x y) + (μ.real (A₂ x y) + (μ.real (A₂ y x) + μ.real (A₃ x y)))) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        section9_coalescence_probability_le_cases μ P L R Q₁ F₁ Q₃ F₃ B x y
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := X) (t := Y) (f := fun x y => μ.real (A₂ y x))]

/-- The count's nonnegative integral is the extended-real version of
its ordinary expectation, for use in the bridge bound. -/
theorem lintegral_section9_coalescence_count_eq_ofReal {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ X Y B : Finset (Vertex d)) :
    (∫⁻ ξη, (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ENNReal) ∂μ) =
      ENNReal.ofReal (∫ ξη, (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) ∂μ) := by
  let E := fun xy : Vertex d × Vertex d => {ξη : Configuration d × Configuration d |
    (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {xy.1} B ∩
      section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {xy.2} B).Nonempty}
  have hE (xy) : MeasurableSet (E xy) :=
    measurableSet_section9_coalescence_event P L R Q₁ F₁ Q₃ F₃ B xy.1 xy.2
  have hcount (ξη : Configuration d × Configuration d) :
      (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) =
        ∑ xy ∈ X.product Y, (E xy).indicator (fun _ => (1 : ℝ)) ξη :=
    section9_coalescence_count_eq_indicators P L R Q₁ F₁ Q₃ F₃ X Y B ξη
  have hi : Integrable (fun ξη =>
      (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ)) μ := by
    simp_rw [hcount]
    exact integrable_finsetSum _ (fun xy _ => (integrable_const (1 : ℝ)).indicator (hE xy))
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)]
  exact lintegral_congr (fun _ => (ENNReal.ofReal_natCast _).symm)

/-- The actual count is measurable as a finite sum of indicators. -/
theorem measurable_section9_coalescence_count {d : ℕ}
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ X Y B : Finset (Vertex d)) :
    Measurable (fun ξη : Configuration d × Configuration d =>
      (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ)) := by
  simp_rw [section9_coalescence_count_eq_indicators]
  apply Finset.measurable_sum
  intro xy _
  exact measurable_const.indicator
    (measurableSet_section9_coalescence_event P L R Q₁ F₁ Q₃ F₃ B xy.1 xy.2)

end NearCritical
