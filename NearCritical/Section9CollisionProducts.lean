module
public import NearCritical.Section9CovarianceFactorization
public import NearCritical.Section9ReplacementMoment

/-! The four side choices in the corrected covariance collision remainder. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Mark the original pivotal event on its chosen component. -/
def section9PivotalMarkEvent {d : ℕ} (right : Bool)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d) :
    Set (Configuration d) :=
  {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
    w ∈ if right then sprinklingUnexploredCluster ω R Q₃ F₃ e.2
      else sprinklingUnexploredCluster ω L Q₁ F₁ e.1}

/-- The replacement only requires disjoint arm witnesses on the chosen side. -/
def section9ArmMarkEvent {d : ℕ} (right : Bool)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (f : Vertex d × Vertex d) (w : Vertex d) :
    Set (Configuration d) :=
  if right then section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w
    else section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w

/-- One of the four collision probability-product sums, over ordered candidates. -/
def section9CollisionProduct {d : ℕ} (μ : Measure (Configuration d))
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B W : Finset (Vertex d)) (oldRight newRight : Bool) : ℝ :=
  ∑ w ∈ W,
    (∑ e ∈ E, μ.real (section9PivotalMarkEvent oldRight L R Q₁ F₁ Q₃ F₃ A B e w)) *
    (∑ f ∈ E, μ.real (section9ArmMarkEvent newRight L R Q₁ F₁ Q₃ F₃ A B f w))

theorem measurableSet_section9PivotalMarkEvent {d : ℕ} (right : Bool)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d) :
    MeasurableSet (section9PivotalMarkEvent right L R Q₁ F₁ Q₃ F₃ A B e w) := by
  cases right
  · exact (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).inter
      (measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ e.1 w)
  · exact (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).inter
      (measurableSet_sprinklingUnexploredCluster_mem R Q₃ F₃ e.2 w)

/-- Under pivotality the two original components are disjoint, so their
union mark splits exactly, rather than merely by a union bound. -/
theorem section9_union_mark_probability {d : ℕ} (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d) :
    μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} =
    μ.real (section9PivotalMarkEvent false L R Q₁ F₁ Q₃ F₃ A B e w) +
      μ.real (section9PivotalMarkEvent true L R Q₁ F₁ Q₃ F₃ A B e w) := by
  have he : {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} =
      section9PivotalMarkEvent false L R Q₁ F₁ Q₃ F₃ A B e w ∪
        section9PivotalMarkEvent true L R Q₁ F₁ Q₃ F₃ A B e w := by
    ext ω
    simp [section9PivotalMarkEvent,Finset.mem_union,and_or_left]
  rw [he]
  apply measureReal_union _ (measurableSet_section9PivotalMarkEvent true L R Q₁ F₁ Q₃ F₃ A B e w)
  apply Set.disjoint_left.mpr
  rintro ω ⟨hp,hL⟩ ⟨_,hR⟩
  exact Finset.disjoint_left.mp hp.2.2.2.2.2 hL hR

/-- Summing the covariance remainder over candidates yields exactly the
four possible original/replacement side products. -/
theorem section9_covariance_remainder_four_products {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B W : Finset (Vertex d)) :
    (∑ e ∈ E, ∑ f ∈ E, ∑ w ∈ W,
      μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} *
      (μ.real (section9ArmMarkEvent false L R Q₁ F₁ Q₃ F₃ A B f w) +
       μ.real (section9ArmMarkEvent true L R Q₁ F₁ Q₃ F₃ A B f w))) =
    section9CollisionProduct μ E L R Q₁ F₁ Q₃ F₃ A B W false false +
    section9CollisionProduct μ E L R Q₁ F₁ Q₃ F₃ A B W false true +
    section9CollisionProduct μ E L R Q₁ F₁ Q₃ F₃ A B W true false +
    section9CollisionProduct μ E L R Q₁ F₁ Q₃ F₃ A B W true true := by
  have hfactor (s t : Bool) :
      (∑ e ∈ E, ∑ f ∈ E, ∑ w ∈ W,
        μ.real (section9PivotalMarkEvent s L R Q₁ F₁ Q₃ F₃ A B e w) *
        μ.real (section9ArmMarkEvent t L R Q₁ F₁ Q₃ F₃ A B f w)) =
      section9CollisionProduct μ E L R Q₁ F₁ Q₃ F₃ A B W s t := by
    calc
      _ = ∑ e ∈ E, ∑ w ∈ W, ∑ f ∈ E,
          μ.real (section9PivotalMarkEvent s L R Q₁ F₁ Q₃ F₃ A B e w) *
          μ.real (section9ArmMarkEvent t L R Q₁ F₁ Q₃ F₃ A B f w) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_comm]
      _ = ∑ w ∈ W, ∑ e ∈ E, ∑ f ∈ E,
          μ.real (section9PivotalMarkEvent s L R Q₁ F₁ Q₃ F₃ A B e w) *
          μ.real (section9ArmMarkEvent t L R Q₁ F₁ Q₃ F₃ A B f w) := Finset.sum_comm
      _ = _ := by
        simp only [section9CollisionProduct,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.sum_comm]
  simp_rw [section9_union_mark_probability μ L R Q₁ F₁ Q₃ F₃ A B]
  simp only [add_mul,mul_add,Finset.sum_add_distrib]
  rw [hfactor false false,hfactor false true,hfactor true false,hfactor true true]
  ring

/-- The covariance comparison summed over all ordered candidates, with
the replacement remainder separated into its four quantitative obligations. -/
theorem section9_conditioned_covariance_sum_four_products_le {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    (∑ e ∈ E, ∑ f ∈ E,
      (ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} -
       ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} *
         ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f})) ≤
    (∑ e ∈ E, ∑ f ∈ E, ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f)) +
      (section9CollisionProduct ν E L R Q₁ F₁ Q₃ F₃ A B (L ∪ R) false false +
       section9CollisionProduct ν E L R Q₁ F₁ Q₃ F₃ A B (L ∪ R) false true +
       section9CollisionProduct ν E L R Q₁ F₁ Q₃ F₃ A B (L ∪ R) true false +
       section9CollisionProduct ν E L R Q₁ F₁ Q₃ F₃ A B (L ∪ R) true true) := by
  intro ν
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E,
        (ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f) +
         ∑ w ∈ L ∪ R,
           ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
             w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} *
           (ν.real (section9ArmMarkEvent false L R Q₁ F₁ Q₃ F₃ A B f w) +
            ν.real (section9ArmMarkEvent true L R Q₁ F₁ Q₃ F₃ A B f w))) := by
      exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ =>
        section9_conditioned_pivotal_covariance_product_le p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
          hH₁ hH₃ hpos hLQ₃ hRQ₁ e f
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [section9_covariance_remainder_four_products ν E L R Q₁ F₁ Q₃ F₃ A B (L ∪ R)]

/-- The already proved same-side source estimate applies directly to
the left/left block of the summed covariance comparison. -/
theorem section9_left_left_collision_product_source_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      section9CollisionProduct (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃)
        (orientedLatticePairs (section9FiniteMiddle i n)) L R Q₁ F₁ Q₃ F₃ A B W false false ≤
        K * (n : ℝ)^((8 : ℝ)-2*(d : ℝ)) * (B.card : ℝ)^2 *
          ∑ x ∈ A, ∑ y ∈ A, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := section9_conditioned_replacement_source_bound hd asymptotics
  refine ⟨K,hK,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hB
  simpa [section9CollisionProduct,section9PivotalMarkEvent,section9ArmMarkEvent] using
    hbound i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hB

end NearCritical
