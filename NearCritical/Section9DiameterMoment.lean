module

public import NearCritical.Section9PivotDistanceMoment
public import NearCritical.SprinklingIntrinsic
public import NearCritical.Section9PivotOpening
public import NearCritical.Section9PhysicalBond

/-! `lem.sprinkling.AB.geo`: the sprinkling intrinsic diameter is dominated by
a sum over opened pivotal pairs.

`diameter_le_pivot_sum` (deterministic): for pivots in the middle box `S`,

  `rin <= 1 + sum_{e in E(S)} 1{sprinkle bond of e open} * W_e(omega)`,

where `W_e` counts, over `x in A`, `y in B` and `z`, the three-factor
disjoint-occurrence events of `Section9PivotDistanceMoment`. This is the
source's "max relaxed to the sum" step, with the BK events already in place.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- `{x <-> z} o {z <-> e_-} o {y <-> e_+}`, left distance. -/
def pivL {d : ℕ} (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (x y z : Vertex d) : Set (Configuration d) :=
  {ω | DisjointOccurrence
    {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
      (unexploredConnEvent L Q₁ F₁ z e.1) θ}
    (unexploredConnEvent R Q₃ F₃ y e.2) ω}

/-- `{y <-> z} o {z <-> e_+} o {x <-> e_-}`, right distance. -/
def pivR {d : ℕ} (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (x y z : Vertex d) : Set (Configuration d) :=
  {ω | DisjointOccurrence
    {θ | DisjointOccurrence (unexploredConnEvent R Q₃ F₃ y z)
      (unexploredConnEvent R Q₃ F₃ z e.2) θ}
    (unexploredConnEvent L Q₁ F₁ x e.1) ω}

/-- The physical bond of the pair `e` is open. -/
def sprinkleEdge {d : ℕ} (e : Vertex d × Vertex d) : Set (Configuration d) :=
  {η | ∃ b : Bond d, s(b.1, bondTip b) = s(e.1, e.2) ∧ η b = true}

/-- Number of three-factor witnesses of the pair `e`. -/
def pivWeight {d : ℕ} (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (ω : Configuration d)
    (e : Vertex d × Vertex d) : ℕ :=
  ∑ x ∈ A, ∑ y ∈ B,
    (((insert x L).filter fun z => ω ∈ pivL L R Q₁ F₁ Q₃ F₃ e x y z).card +
      ((insert y R).filter fun z => ω ∈ pivR L R Q₁ F₁ Q₃ F₃ e x y z).card)

theorem diameter_le_pivot_sum {d : ℕ} (S L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hSL : S ⊆ L) (hsep : Disjoint (S : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    (ω η : Configuration d) :
    sprinklingIntrinsicDiameter (sprinklingUnexploredGraph ω L Q₁ F₁)
      (sprinklingUnexploredGraph ω R Q₃ F₃) A B
      (sprinkledPivotalPairs ω (sprinkleOrConfiguration ω η) (orientedLatticePairs S)
        L R Q₁ F₁ Q₃ F₃ A B) ≤
      1 + ∑ e ∈ orientedLatticePairs S,
        (if η ∈ sprinkleEdge e then pivWeight L R Q₁ F₁ Q₃ F₃ A B ω e else 0) := by
  unfold sprinklingIntrinsicDiameter
  refine Nat.add_le_add_left (Finset.sup_le (fun e he => ?_)) 1
  obtain ⟨hpm, hadj⟩ := Finset.mem_filter.mp he
  obtain ⟨hE, hpiv⟩ := Finset.mem_filter.mp hpm
  have hclosed := middle_sprinklingPivotalPairs_closed S L R Q₁ F₁ Q₃ F₃ A B hSL hsep hpm
  have hJ : η ∈ sprinkleEdge e := by
    obtain ⟨b, hb, hends⟩ := hadj
    have hs : s(b.1, bondTip b) = s(e.1, e.2) := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]; exact Sym2.eq_swap
    refine ⟨b, hs, ?_⟩
    by_contra hη
    apply hclosed
    refine ⟨b, ?_, hends⟩
    have hb' : (ω b || η b) = true := hb
    cases hω : ω b with
    | true => rfl
    | false =>
      rw [hω, Bool.false_or] at hb'
      exact absurd hb' hη
  refine le_trans ?_ (Finset.single_le_sum (f := fun e =>
    if η ∈ sprinkleEdge e then pivWeight L R Q₁ F₁ Q₃ F₃ A B ω e else 0)
    (fun _ _ => Nat.zero_le _) hE)
  rw [if_pos hJ]
  have hsepL := sprinklingPivotalPair_sep L R Q₁ F₁ Q₃ F₃ A B hpiv
  have hsepR : ∀ v, (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable e.2 v →
      ¬ (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable e.1 v :=
    fun v hR hL => hsepL v hL hR
  obtain ⟨_, _, _, ⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, _⟩ := hpiv
  obtain ⟨hx₀c, hx₀A⟩ := Finset.mem_inter.mp hx₀
  obtain ⟨hy₀c, hy₀B⟩ := Finset.mem_inter.mp hy₀
  have hx₀r := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x₀).mp hx₀c).2
  have hy₀r := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y₀).mp hy₀c).2
  have hLrad : intrinsicBoundaryRadius (sprinklingUnexploredGraph ω L Q₁ F₁) e.1 A ≤
      ∑ x ∈ A, ∑ y ∈ B,
        ((insert x L).filter fun z => ω ∈ pivL L R Q₁ F₁ Q₃ F₃ e x y z).card := by
    unfold intrinsicBoundaryRadius
    refine Finset.sup_le (fun x hx => ?_)
    obtain ⟨hxA, hxr⟩ := Finset.mem_filter.mp hx
    have h1 := pivot_dist_succ_le ω L R Q₁ F₁ Q₃ F₃ (insert x L) hxr.symm hy₀r.symm hsepL
      (fun v hr => unexplored_reachable_mem ω L Q₁ F₁ hr)
    have h2 : ((insert x L).filter fun z => ω ∈ pivL L R Q₁ F₁ Q₃ F₃ e x y₀ z).card ≤
        ∑ y ∈ B, ((insert x L).filter fun z => ω ∈ pivL L R Q₁ F₁ Q₃ F₃ e x y z).card :=
      Finset.single_le_sum (f := fun y =>
        ((insert x L).filter fun z => ω ∈ pivL L R Q₁ F₁ Q₃ F₃ e x y z).card)
        (fun _ _ => Nat.zero_le _) hy₀B
    have h3 := Finset.single_le_sum (f := fun x => ∑ y ∈ B,
        ((insert x L).filter fun z => ω ∈ pivL L R Q₁ F₁ Q₃ F₃ e x y z).card)
        (fun _ _ => Nat.zero_le _) hxA
    have h1' : (sprinklingUnexploredGraph ω L Q₁ F₁).dist x e.1 + 1 ≤
        ((insert x L).filter fun z => ω ∈ pivL L R Q₁ F₁ Q₃ F₃ e x y₀ z).card := h1
    exact (Nat.le_of_succ_le h1').trans (h2.trans h3)
  have hRrad : intrinsicBoundaryRadius (sprinklingUnexploredGraph ω R Q₃ F₃) e.2 B ≤
      ∑ x ∈ A, ∑ y ∈ B,
        ((insert y R).filter fun z => ω ∈ pivR L R Q₁ F₁ Q₃ F₃ e x y z).card := by
    unfold intrinsicBoundaryRadius
    refine Finset.sup_le (fun y hy => ?_)
    obtain ⟨hyB, hyr⟩ := Finset.mem_filter.mp hy
    have h1 := pivot_dist_succ_le ω R L Q₃ F₃ Q₁ F₁ (insert y R) hyr.symm hx₀r.symm hsepR
      (fun v hr => unexplored_reachable_mem ω R Q₃ F₃ hr)
    have h1' : (sprinklingUnexploredGraph ω R Q₃ F₃).dist y e.2 + 1 ≤
        ((insert y R).filter fun z => ω ∈ pivR L R Q₁ F₁ Q₃ F₃ e x₀ y z).card := h1
    have h2 : ((insert y R).filter fun z => ω ∈ pivR L R Q₁ F₁ Q₃ F₃ e x₀ y z).card ≤
        ∑ y ∈ B, ((insert y R).filter fun z => ω ∈ pivR L R Q₁ F₁ Q₃ F₃ e x₀ y z).card :=
      Finset.single_le_sum (f := fun y =>
        ((insert y R).filter fun z => ω ∈ pivR L R Q₁ F₁ Q₃ F₃ e x₀ y z).card)
        (fun _ _ => Nat.zero_le _) hyB
    have h3 := Finset.single_le_sum (f := fun x => ∑ y ∈ B,
        ((insert y R).filter fun z => ω ∈ pivR L R Q₁ F₁ Q₃ F₃ e x y z).card)
        (fun _ _ => Nat.zero_le _) hx₀A
    exact (Nat.le_of_succ_le h1').trans (h2.trans h3)
  unfold pivWeight
  simp only [Finset.sum_add_distrib]
  exact Nat.add_le_add hLrad hRrad


/-! ### Expectation under the product law -/

open MeasureTheory

/-- Integrable with integral at most `c`. -/
def IntegralLe {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) : Prop :=
  Integrable f μ ∧ ∫ ω, f ω ∂μ ≤ c

lemma IntegralLe.sum {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (s : Finset I)
    (f : I → Ω → ℝ) (c : I → ℝ) (h : ∀ i ∈ s, IntegralLe μ (f i) (c i)) :
    IntegralLe μ (fun ω => ∑ i ∈ s, f i ω) (∑ i ∈ s, c i) := by
  refine ⟨integrable_finset_sum s (fun i hi => (h i hi).1), ?_⟩
  rw [integral_finset_sum s (fun i hi => (h i hi).1)]
  exact Finset.sum_le_sum (fun i hi => (h i hi).2)

lemma IntegralLe.add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    {a b : ℝ} (hf : IntegralLe μ f a) (hg : IntegralLe μ g b) :
    IntegralLe μ (fun ω => f ω + g ω) (a + b) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  rw [integral_add hf.1 hg.1]
  exact add_le_add hf.2 hg.2

lemma IntegralLe.rect {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) {a b : ℝ}
    (ha : μ.real s ≤ a) (hb : ν.real t ≤ b) (hb0 : 0 ≤ b) :
    IntegralLe (μ.prod ν) (fun z : α × β => if z.1 ∈ s ∧ z.2 ∈ t then (1:ℝ) else 0) (a * b) := by
  have hfun : (fun z : α × β => if z.1 ∈ s ∧ z.2 ∈ t then (1:ℝ) else 0) =
      Set.indicator (s ×ˢ t) (fun _ => (1:ℝ)) := by
    funext z
    simp only [Set.indicator, Set.mem_prod]
  rw [hfun]
  refine ⟨(integrable_const (1:ℝ)).indicator (hs.prod ht), ?_⟩
  rw [integral_indicator_const _ (hs.prod ht), smul_eq_mul, mul_one, measureReal_prod_prod]
  exact mul_le_mul ha hb measureReal_nonneg (measureReal_nonneg.trans ha)

lemma sprinkleEdge_measurable_le {d : ℕ} (q : unitInterval) (e : Vertex d × Vertex d) :
    MeasurableSet (sprinkleEdge e) ∧ (percolation d q).real (sprinkleEdge e) ≤ (q : ℝ) := by
  by_cases h : ∃ b : Bond d, s(b.1, bondTip b) = s(e.1, e.2)
  · obtain ⟨b₀, hb₀⟩ := h
    have heq : sprinkleEdge e = {η : Configuration d | η b₀ = true} := by
      ext η
      constructor
      · rintro ⟨b, hs, hb⟩
        have hbb := section9_bond_endpoints_injective (hs.trans hb₀.symm)
        rw [← hbb]
        exact hb
      · intro hη
        exact ⟨b₀, hb₀, hη⟩
    rw [heq]
    refine ⟨(measurable_pi_apply (X := fun _ : Bond d => Bool) b₀) (measurableSet_singleton true),
      ?_⟩
    unfold Measure.real
    rw [percolation_open_bond, ENNReal.toReal_ofReal q.2.1]
  · have heq : sprinkleEdge e = (∅ : Set (Configuration d)) := by
      ext η
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨b, hs, _⟩
      exact h ⟨b, hs⟩
    rw [heq]
    exact ⟨MeasurableSet.empty, by simp [q.2.1]⟩

lemma pivL_measurable_le {d : ℕ} (p : unitInterval) (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (e : Vertex d × Vertex d) (x y z : Vertex d) :
    MeasurableSet (pivL L R Q₁ F₁ Q₃ F₃ e x y z) ∧
      (percolation d p).real (pivL L R Q₁ F₁ Q₃ F₃ e x y z) ≤
        twoPoint d p x z * twoPoint d p z e.1 * twoPoint d p y e.2 := by
  have hinc : BK.Increasing {θ : Configuration d |
      DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
        (unexploredConnEvent L Q₁ F₁ z e.1) θ} :=
    increasing_disjointOccurrence (unexploredConnEvent_increasing L Q₁ F₁ x z)
      (unexploredConnEvent_increasing L Q₁ F₁ z e.1)
  refine ⟨measurableSet_disjointOccurrence hinc (unexploredConnEvent_increasing R Q₃ F₃ y e.2), ?_⟩
  refine (percolation_bk d p _ _ hinc (unexploredConnEvent_increasing R Q₃ F₃ y e.2)).trans ?_
  have h2 := percolation_bk d p _ _ (unexploredConnEvent_increasing L Q₁ F₁ x z)
    (unexploredConnEvent_increasing L Q₁ F₁ z e.1)
  unfold twoPoint
  have hA := measureReal_mono (μ := percolation d p)
    (unexploredConnEvent_subset_connection L Q₁ F₁ x z) (measure_ne_top _ _)
  have hB := measureReal_mono (μ := percolation d p)
    (unexploredConnEvent_subset_connection L Q₁ F₁ z e.1) (measure_ne_top _ _)
  have hC := measureReal_mono (μ := percolation d p)
    (unexploredConnEvent_subset_connection R Q₃ F₃ y e.2) (measure_ne_top _ _)
  exact mul_le_mul (h2.trans (mul_le_mul hA hB measureReal_nonneg measureReal_nonneg)) hC
    measureReal_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)

lemma pivR_measurable_le {d : ℕ} (p : unitInterval) (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (e : Vertex d × Vertex d) (x y z : Vertex d) :
    MeasurableSet (pivR L R Q₁ F₁ Q₃ F₃ e x y z) ∧
      (percolation d p).real (pivR L R Q₁ F₁ Q₃ F₃ e x y z) ≤
        twoPoint d p y z * twoPoint d p z e.2 * twoPoint d p x e.1 :=
  pivL_measurable_le p R L Q₃ F₃ Q₁ F₁ (e.2, e.1) y x z

/-- The diameter is dominated by an integrable sum of rectangle indicators. -/
theorem diameter_dominated {d : ℕ} (p q : unitInterval)
    (S L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hSL : S ⊆ L) (hsep : Disjoint (S : Set (Vertex d)) (Q₁ : Set (Vertex d))) :
    ∃ g : Configuration d × Configuration d → ℝ,
      IntegralLe ((percolation d p).prod (percolation d q)) g
        (1 + ∑ e ∈ orientedLatticePairs S, ∑ x ∈ A, ∑ y ∈ B,
          ((∑ z ∈ insert x L,
              twoPoint d p x z * twoPoint d p z e.1 * twoPoint d p y e.2 * (q : ℝ)) +
            ∑ z ∈ insert y R,
              twoPoint d p y z * twoPoint d p z e.2 * twoPoint d p x e.1 * (q : ℝ))) ∧
      ∀ z : Configuration d × Configuration d,
        ((sprinklingIntrinsicDiameter (sprinklingUnexploredGraph z.1 L Q₁ F₁)
          (sprinklingUnexploredGraph z.1 R Q₃ F₃) A B
          (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs S)
            L R Q₁ F₁ Q₃ F₃ A B) : ℕ) : ℝ) ≤ g z := by
  have hgood : IntegralLe ((percolation d p).prod (percolation d q))
      (fun z : Configuration d × Configuration d =>
        (1:ℝ) + ∑ e ∈ orientedLatticePairs S, ∑ x ∈ A, ∑ y ∈ B,
          ((∑ z' ∈ insert x L,
              (if z.1 ∈ pivL L R Q₁ F₁ Q₃ F₃ e x y z' ∧ z.2 ∈ sprinkleEdge e
                then (1:ℝ) else 0)) +
            ∑ z' ∈ insert y R,
              (if z.1 ∈ pivR L R Q₁ F₁ Q₃ F₃ e x y z' ∧ z.2 ∈ sprinkleEdge e
                then (1:ℝ) else 0)))
      (1 + ∑ e ∈ orientedLatticePairs S, ∑ x ∈ A, ∑ y ∈ B,
        ((∑ z ∈ insert x L,
            twoPoint d p x z * twoPoint d p z e.1 * twoPoint d p y e.2 * (q : ℝ)) +
          ∑ z ∈ insert y R,
            twoPoint d p y z * twoPoint d p z e.2 * twoPoint d p x e.1 * (q : ℝ))) := by
    refine IntegralLe.add ⟨integrable_const _, by simp⟩ ?_
    refine IntegralLe.sum _ _ _ (fun e _ => IntegralLe.sum _ _ _ (fun x _ =>
      IntegralLe.sum _ _ _ (fun y _ => IntegralLe.add ?_ ?_)))
    · exact IntegralLe.sum _ _ _ (fun z' _ =>
        IntegralLe.rect (pivL_measurable_le p L R Q₁ F₁ Q₃ F₃ e x y z').1
          (sprinkleEdge_measurable_le q e).1 (pivL_measurable_le p L R Q₁ F₁ Q₃ F₃ e x y z').2
          (sprinkleEdge_measurable_le q e).2 q.2.1)
    · exact IntegralLe.sum _ _ _ (fun z' _ =>
        IntegralLe.rect (pivR_measurable_le p L R Q₁ F₁ Q₃ F₃ e x y z').1
          (sprinkleEdge_measurable_le q e).1 (pivR_measurable_le p L R Q₁ F₁ Q₃ F₃ e x y z').2
          (sprinkleEdge_measurable_le q e).2 q.2.1)
  refine ⟨_, hgood, fun z => ?_⟩
  have h := diameter_le_pivot_sum S L R Q₁ F₁ Q₃ F₃ A B hSL hsep z.1 z.2
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  refine h'.trans ?_
  push_cast
  refine add_le_add (le_refl _) (Finset.sum_le_sum (fun e _ => ?_))
  by_cases hJ : z.2 ∈ sprinkleEdge e
  · rw [if_pos hJ]
    unfold pivWeight
    push_cast
    refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    simp only [hJ, and_true]
    exact le_refl _
  · rw [if_neg hJ]
    simp only [hJ, and_false, if_false, Finset.sum_const_zero, add_zero]
    exact le_refl _

/-- **First moment of the sprinkling intrinsic diameter** (lem.sprinkling.AB.geo,
before the two-point sums): critical layer at `p`, independent sprinkle at `q`. -/
theorem diameter_integral_le {d : ℕ} (p q : unitInterval)
    (S L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hSL : S ⊆ L) (hsep : Disjoint (S : Set (Vertex d)) (Q₁ : Set (Vertex d))) :
    (∫ z, ((sprinklingIntrinsicDiameter (sprinklingUnexploredGraph z.1 L Q₁ F₁)
      (sprinklingUnexploredGraph z.1 R Q₃ F₃) A B
      (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs S)
        L R Q₁ F₁ Q₃ F₃ A B) : ℕ) : ℝ) ∂((percolation d p).prod (percolation d q))) ≤
      1 + ∑ e ∈ orientedLatticePairs S, ∑ x ∈ A, ∑ y ∈ B,
        ((∑ z ∈ insert x L,
            twoPoint d p x z * twoPoint d p z e.1 * twoPoint d p y e.2 * (q : ℝ)) +
          ∑ z ∈ insert y R,
            twoPoint d p y z * twoPoint d p z e.2 * twoPoint d p x e.1 * (q : ℝ)) := by
  obtain ⟨g, hg, hle⟩ := diameter_dominated p q S L R Q₁ F₁ Q₃ F₃ A B hSL hsep
  exact (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => Nat.cast_nonneg _))
    hg.1 (Filter.Eventually.of_forall hle)).trans hg.2

/-- Markov for a function dominated by an `IntegralLe` function. -/
lemma IntegralLe.tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f g : Ω → ℝ} {c K : ℝ} (hg : IntegralLe μ g c) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfg : ∀ ω, f ω ≤ g ω) (hK : 0 < K) :
    μ.real {ω | K ≤ f ω} ≤ c / K := by
  have hsub : {ω | K ≤ f ω} ⊆ {ω | K ≤ g ω} := fun ω h => le_trans h (hfg ω)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => (hf0 ω).trans (hfg ω))) hg.1 K
  have h1 := measureReal_mono (μ := μ) hsub (measure_ne_top μ _)
  rw [le_div_iff₀ hK]
  calc μ.real {ω | K ≤ f ω} * K ≤ μ.real {ω | K ≤ g ω} * K :=
        mul_le_mul_of_nonneg_right h1 hK.le
    _ = K * μ.real {ω | K ≤ g ω} := mul_comm _ _
    _ ≤ ∫ ω, g ω ∂μ := hm
    _ ≤ c := hg.2

end NearCritical
