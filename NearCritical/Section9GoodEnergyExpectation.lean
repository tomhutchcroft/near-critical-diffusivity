module
public import NearCritical.Section9SevenEdgeDenominator
public import NearCritical.Section9RestrictedQuartetProbability
public import NearCritical.Section9OrientedClusterBoundary
public import NearCritical.Section9AvoidanceGoodExit
public import NearCritical.Section9FreshEvent
public import NearCritical.Section9CoalescenceGeometry
public import NearCritical.Section8ExtensionSourceGeometry
public import NearCritical.Section9FiniteLocalIntegrability
public import NearCritical.Section9ExitFace
public import NearCritical.Section9PivotalMeanUpper

/-! The actual good-exit denominator has quadratic expectation under the
actual positive outer-heart reveal law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Actual good-exit energy, with restricted fresh-copy weights and the
literal middle-core intersection of the actual left component. -/
def section9GoodExitEnergy {d : ℕ} (i : Fin d) (n : ℕ)
    (F₃ C : Finset (Vertex d)) : ℝ :=
  let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
  let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
  ∑ t ∈ section9AvoidanceGoodLastExitCandidates R C Q₃ F₃ (section9ExitFace i n ∩ C),
    (∑ z ∈ C ∩ section8ExtensionMiddleCore i n,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) z {t.1.1}))^2

private theorem energy_tail_degree {d : ℕ} (S : Finset (Vertex d))
    (f : Vertex d → ℝ) (hf : ∀ w ∈ S, 0 ≤ f w) :
    ∑ e ∈ orientedLatticePairs S, f e.1 ≤ (2*(d : ℝ))*∑ w ∈ S, f w := by
  rw [orientedLatticePairs,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  rw [← Finset.sum_filter]
  simp only [Prod.fst,Prod.snd,Finset.sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hf w hw)
  exact_mod_cast (Finset.card_le_card (show
    S.filter (fun v => (openGraph (fun _ => true)).Adj w v) ⊆ latticeNeighbors w by
      intro v hv
      exact (mem_latticeNeighbors_iff w v).mpr (Finset.mem_filter.mp hv).2)).trans
        (card_latticeNeighbors_le w)

private theorem energy_pointwise {d : ℕ} (i : Fin d) (n : ℕ)
    (F₃ C : Finset (Vertex d))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) :
    section9GoodExitEnergy i n F₃ C ≤ (2*(d : ℝ))*
      ∑ w ∈ section9FiniteMiddle i n,
        if w ∈ C then (∑ z ∈ C ∩ section8ExtensionMiddleCore i n,
          twoPoint d (criticalPoint d) w z)^2 else 0 := by
  let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
  let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
  let J := section9AvoidanceGoodLastExitCandidates R C Q₃ F₃ (section9ExitFace i n ∩ C)
  let S := centeredBox d (3*n)
  let M := section9FiniteMiddle i n
  let Z := section8ExtensionMiddleCore i n
  let f := fun w : Vertex d => if w ∈ C ∩ M then
    (∑ z ∈ C ∩ Z, twoPoint d (criticalPoint d) w z)^2 else 0
  have hf (w : Vertex d) : 0 ≤ f w := by dsimp only [f]; split_ifs <;> positivity
  have hinj : Set.InjOn (fun t : (Vertex d × Vertex d) × Bond d => t.1) (J : Set _) := by
    intro t ht t' ht' heq
    exact section9_last_exit_candidate_projection_injOn i n C F₃
      (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht').1 heq
  have hsub : J.image (fun t => t.1) ⊆ section9OrientedClusterBoundary i n C := by
    intro e he
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp he
    exact section9_last_exit_candidate_projection_subset_boundary i n C F₃ hCL
      (Finset.mem_image.mpr ⟨t,(Finset.mem_filter.mp ht).1,rfl⟩)
  have hweight (t : (Vertex d × Vertex d) × Bond d) (ht : t ∈ J) :
      (∑ z ∈ C ∩ Z, (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) z {t.1.1}))^2 ≤ f t.1.1 := by
    have hboundary := Finset.mem_filter.mp (hsub (Finset.mem_image.mpr ⟨t,ht,rfl⟩))
    have hinner : t.1.1 ∈ C ∩ M := Finset.mem_inter.mpr ⟨hboundary.2.1,hboundary.2.2.1⟩
    rw [show f t.1.1 = (∑ z ∈ C ∩ Z, twoPoint d (criticalPoint d) t.1.1 z)^2 by
      simp only [f,if_pos hinner]]
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => measureReal_nonneg)) _ 2
    apply Finset.sum_le_sum
    intro z _
    have hh := connectionToSet_probability_le_twoPoint_sum (criticalPoint d)
      (R : Set (Vertex d)) z {t.1.1}
    simpa only [Finset.coe_singleton,Finset.sum_singleton,twoPoint_symm (criticalPoint d) z t.1.1] using hh
  have hMsub : M ⊆ S := fun w hw => (Finset.mem_filter.mp hw).1
  have hsum : (∑ w ∈ S, f w) = ∑ w ∈ M,
      if w ∈ C then (∑ z ∈ C ∩ Z, twoPoint d (criticalPoint d) w z)^2 else 0 := by
    rw [← Finset.sum_subset hMsub]
    · apply Finset.sum_congr rfl
      intro w hw
      simp only [f,Finset.mem_inter,hw,and_true]
    · intro w _ hw
      simp only [f,Finset.mem_inter,hw,and_false,if_false]
  calc
    _ ≤ ∑ t ∈ J, f t.1.1 := Finset.sum_le_sum hweight
    _ = ∑ e ∈ J.image (fun t => t.1), f e.1 :=
      (Finset.sum_image (f := fun e : Vertex d × Vertex d => f e.1) hinj).symm
    _ ≤ ∑ e ∈ section9OrientedClusterBoundary i n C, f e.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hf e.1)
    _ ≤ ∑ e ∈ orientedLatticePairs S, f e.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun e _ _ => hf e.1)
    _ ≤ (2*(d : ℝ))*∑ w ∈ S, f w := energy_tail_degree S f (fun w _ => hf w)
    _ = _ := by rw [hsum]

private theorem energy_triple_integral {d : ℕ} (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (L Q F M Z : Finset (Vertex d)) (x : Vertex d) :
    (∫ ω, ∑ w ∈ M, if w ∈ sprinklingUnexploredCluster ω L Q F x then
      (∑ z ∈ sprinklingUnexploredCluster ω L Q F x ∩ Z,
        twoPoint d (criticalPoint d) w z)^2 else 0 ∂μ) =
    ∑ w ∈ M, ∑ z ∈ Z, ∑ z' ∈ Z,
      (twoPoint d (criticalPoint d) w z*twoPoint d (criticalPoint d) w z')*
      μ.real {ω | w ∈ sprinklingUnexploredCluster ω L Q F x ∧
        z ∈ sprinklingUnexploredCluster ω L Q F x ∧
        z' ∈ sprinklingUnexploredCluster ω L Q F x} := by
  let C := fun ω => sprinklingUnexploredCluster ω L Q F x
  let P := twoPoint d (criticalPoint d)
  let A := fun w z z' => {ω : Configuration d | w ∈ C ω ∧ z ∈ C ω ∧ z' ∈ C ω}
  let g := fun w z z' ω => (P w z*P w z')*(A w z z').indicator (fun _ => (1 : ℝ)) ω
  have hm (w z z' : Vertex d) : MeasurableSet (A w z z') :=
    (measurableSet_sprinklingUnexploredCluster_mem L Q F x w).inter
      ((measurableSet_sprinklingUnexploredCluster_mem L Q F x z).inter
        (measurableSet_sprinklingUnexploredCluster_mem L Q F x z'))
  have hi (w z z' : Vertex d) : Integrable (g w z z') μ :=
    ((integrable_const (1 : ℝ)).indicator (hm w z z')).const_mul _
  have hinter (ω : Configuration d) (w : Vertex d) :
      (∑ z ∈ C ω ∩ Z, P w z) = ∑ z ∈ Z, if z ∈ C ω then P w z else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext z
    simp only [Finset.mem_filter,Finset.mem_inter,and_comm]
  have hsum (ω : Configuration d) :
      (∑ w ∈ M, if w ∈ C ω then (∑ z ∈ C ω ∩ Z, P w z)^2 else 0) =
        ∑ w ∈ M, ∑ z ∈ Z, ∑ z' ∈ Z, g w z z' ω := by
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ C ω
    · rw [if_pos hw,hinter,pow_two,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z' _
      by_cases hz : z ∈ C ω <;> by_cases hz' : z' ∈ C ω <;>
        simp only [g,A,Set.indicator_apply,Set.mem_setOf_eq,hw,hz,hz',and_self,
          true_and,false_and,and_true,and_false,if_true,if_false,mul_zero,zero_mul,mul_one]
    · simp only [if_neg hw,g,A,Set.indicator_apply,Set.mem_setOf_eq,hw,false_and,
        if_false,mul_zero,Finset.sum_const_zero]
  change (∫ ω, ∑ w ∈ M, if w ∈ C ω then
    (∑ z ∈ C ω ∩ Z, P w z)^2 else 0 ∂μ) = _
  simp_rw [hsum]
  rw [integral_finsetSum M (fun w _ => integrable_finsetSum Z
    (fun z _ => integrable_finsetSum Z (fun z' _ => hi w z z')))]
  apply Finset.sum_congr rfl
  intro w _
  rw [integral_finsetSum Z (fun z _ => integrable_finsetSum Z (fun z' _ => hi w z z'))]
  apply Finset.sum_congr rfl
  intro z _
  rw [integral_finsetSum Z (fun z' _ => hi w z z')]
  apply Finset.sum_congr rfl
  intro z' _
  dsimp only [g]
  rw [integral_const_mul]
  congr 1
  have hone : (fun _ : Configuration d => (1 : ℝ)) = (1 : Configuration d → ℝ) := by
    funext ω
    rfl
  rw [hone]
  exact integral_indicator_one (hm w z z')

private theorem energy_triple_quartet_bound {d : ℕ} (i : Fin d) (n : ℕ) (hn : 0 < n)
    (H₁ H₃ F₁ F₃ : Finset (Vertex d)) (x : Vertex d)
    (hH₁ : H₁ ⊆ section9FiniteEndCube i n 0)
    (hH₃ : H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)))
    (hpos : percolation d (criticalPoint d) (section9RevealEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0)
    (hx : x ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) (w z z' : Vertex d) :
    let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    let P := twoPoint d (criticalPoint d)
    let T := fun b c e => ∑ u ∈ L, ∑ v ∈ L, P x u*P b u*P u v*P c v*P e v
    ν.real {ω | w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x ∧
      z ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x ∧
      z' ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x} ≤
      T z' z w + T z z' w + T w z' z := by
  intro L R Q₁ Q₃ ν P T
  let A := {ω : Configuration d | w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x ∧
    z ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x ∧ z' ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x}
  let S := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  have hA : MeasurableSet A :=
    (measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ x w).inter
      ((measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ x z).inter
        (measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ x z'))
  have hfresh := section9RevealedLaw_fresh_probability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    hH₁ hH₃ hpos S (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃
      (section9FiniteLeftTube_disjoint_third i hn) (section9FiniteRightTube_disjoint_first i hn))
    A hA (by
      intro ω θ hagree
      have hh := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ
        (fun b hb => hagree b (Finset.mem_union_left _ hb)) x
      simp only [A,Set.mem_setOf_eq,hh])
  let D := (L : Set (Vertex d))
  let Q := fun a b => (percolation d (criticalPoint d)).real (connectionToSetEvent D a {b})
  have hsub : A ⊆ ((connectionToSetEvent D x {z'} ∩ connectionToSetEvent D x {z}) ∩
      connectionToSetEvent D x {w}) := by
    intro ω hω
    have hconn (y : Vertex d) (hy : y ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x) :
        ω ∈ connectionToSetEvent D x {y} := by
      obtain ⟨hyL,hreach⟩ := (mem_sprinklingUnexploredCluster ω L Q₁ F₁ x y).mp hy
      have hle : sprinklingUnexploredGraph ω L Q₁ F₁ ≤ restrictedGraph ω D :=
        fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩
      exact ⟨hx,y,rfl,hyL,hreach.mono hle⟩
    exact ⟨⟨hconn z' hω.2.2,hconn z hω.2.1⟩,hconn w hω.1⟩
  have hDom (a b : Vertex d) : Q a b ≤ P a b := by
    simpa only [Q,P,Finset.coe_singleton,Finset.sum_singleton] using
      connectionToSet_probability_le_twoPoint_sum (criticalPoint d) D a {b}
  have htree (b c e : Vertex d) :
      (∑ u ∈ L, ∑ v ∈ L, Q x u*Q b u*Q u v*Q c v*Q e v) ≤ T b c e := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    have hQ (a b : Vertex d) : 0 ≤ Q a b := measureReal_nonneg
    have hP (a b : Vertex d) : 0 ≤ P a b := twoPoint_nonneg _ _ _
    have hxP := hP x u
    have hbP := hP b u
    have huvP := hP u v
    have hcP := hP c v
    have heP := hP e v
    gcongr <;> first | exact hDom _ _ | positivity
  change ν.real A ≤ _
  rw [hfresh]
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((restricted_quartet_connection_probability_le (criticalPoint d) L x z' z w).trans
      (add_le_add (add_le_add (htree z' z w) (htree z z' w)) (htree w z' z)))

private theorem energy_rotate_sums {α : Type*} (U W Z : Finset α)
    (f : α → α → α → α → α → ℝ) :
    (∑ w ∈ W, ∑ z ∈ Z, ∑ z' ∈ Z, ∑ u ∈ U, ∑ v ∈ U, f u v w z z') =
      ∑ u ∈ U, ∑ v ∈ U, ∑ w ∈ W, ∑ z ∈ Z, ∑ z' ∈ Z, f u v w z z' := by
  simp_rw [Finset.sum_comm (s := Z) (t := U),Finset.sum_comm (s := W) (t := U)]

private theorem energy_weighted_tree_sum {d : ℕ} (U W Z : Finset (Vertex d)) (x : Vertex d) :
    let P := twoPoint d (criticalPoint d)
    let T := fun b c e => ∑ u ∈ U, ∑ v ∈ U, P x u*P b u*P u v*P c v*P e v
    (∑ w ∈ W, ∑ z ∈ Z, ∑ z' ∈ Z,
      (P w z*P w z')*(T z' z w+T z z' w+T w z' z)) =
      2*section9SevenEdgeDiagramI U W Z x+section9SevenEdgeDiagramII U W Z x := by
  intro P T
  have hI : (∑ w ∈ W, ∑ z ∈ Z, ∑ z' ∈ Z, (P w z*P w z')*T z' z w) =
      section9SevenEdgeDiagramI U W Z x := by
    simp only [T,Finset.mul_sum]
    rw [energy_rotate_sums]
    unfold section9SevenEdgeDiagramI
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    dsimp only [P]
    rw [twoPoint_symm (criticalPoint d) z' u,twoPoint_symm (criticalPoint d) z v,
      twoPoint_symm (criticalPoint d) w v]
    ring
  have hI' : (∑ w ∈ W, ∑ z ∈ Z, ∑ z' ∈ Z, (P w z*P w z')*T z z' w) =
      section9SevenEdgeDiagramI U W Z x := by
    rw [← hI]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    ring
  have hII : (∑ w ∈ W, ∑ z ∈ Z, ∑ z' ∈ Z, (P w z*P w z')*T w z' z) =
      section9SevenEdgeDiagramII U W Z x := by
    simp only [T,Finset.mul_sum]
    rw [energy_rotate_sums]
    unfold section9SevenEdgeDiagramII
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro z' _
    dsimp only [P]
    rw [twoPoint_symm (criticalPoint d) w u,twoPoint_symm (criticalPoint d) z' v,
      twoPoint_symm (criticalPoint d) z v]
    ring
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [hI,hI',hII]
  ring

/-- The actual good-exit denominator has quadratic expectation under the
actual positive outer-heart law. No regularity, lower-bound, or assumed
moment/diagram estimate is required. -/
theorem section9_source_good_exit_energy_moment_upper {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 1 ≤ n →
      ∀ (H₁ H₃ F₁ F₃ : Finset (Vertex d)) (x : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 →
      H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      x ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      (∫ ω, section9GoodExitEnergy i n F₃ (sprinklingUnexploredCluster ω L Q₁ F₁ x) ∂ν) ≤
        K*(n : ℝ)^2 := by
  obtain ⟨Ks,hKs,hseven⟩ := section9_finite_seven_edge_diagrams_le hd asymptotics
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  let J : ℝ := 2*(d : ℝ)*3^(d-1)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨(2*(d : ℝ))*(3*Ks)*(G*(1+49*J)),by positivity,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ x hH₁ hH₃ hpos hx L Q₁ Q₃ ν
  let M := section9FiniteMiddle i n
  let Z := section8ExtensionMiddleCore i n
  let C := fun ω : Configuration d => sprinklingUnexploredCluster ω L Q₁ F₁ x
  let P := twoPoint d (criticalPoint d)
  let T := fun b c e => ∑ u ∈ L, ∑ v ∈ L, P x u*P b u*P u v*P c v*P e v
  let f := fun ω : Configuration d => ∑ w ∈ M, if w ∈ C ω then
    (∑ z ∈ C ω ∩ Z, P w z)^2 else 0
  let D := fun ω : Configuration d => section9GoodExitEnergy i n F₃ (C ω)
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hiD : Integrable D ν := section9_finite_local_integrable ν
    (sprinklingAvailableBonds L Q₁ F₁) D (by
      intro ω θ hagree
      have hh := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hagree x
      simp only [D,C,hh])
  have hif : Integrable f ν := section9_finite_local_integrable ν
    (sprinklingAvailableBonds L Q₁ F₁) f (by
      intro ω θ hagree
      have hh := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hagree x
      simp only [f,C,hh])
  have hpoint (ω : Configuration d) : D ω ≤ (2*(d : ℝ))*f ω :=
    energy_pointwise i n F₃ (C ω) (sprinklingUnexploredCluster_subset ω L Q₁ F₁ x)
  have hexpand := energy_triple_integral ν L Q₁ F₁ M Z x
  change (∫ ω, f ω ∂ν) = ∑ w ∈ M, ∑ z ∈ Z, ∑ z' ∈ Z,
    (P w z*P w z')*ν.real {ω | w ∈ C ω ∧ z ∈ C ω ∧ z' ∈ C ω} at hexpand
  have hsum : (∑ w ∈ M, ∑ z ∈ Z, ∑ z' ∈ Z,
      (P w z*P w z')*ν.real {ω | w ∈ C ω ∧ z ∈ C ω ∧ z' ∈ C ω}) ≤
      2*section9SevenEdgeDiagramI L M Z x+section9SevenEdgeDiagramII L M Z x := by
    calc
      _ ≤ ∑ w ∈ M, ∑ z ∈ Z, ∑ z' ∈ Z,
          (P w z*P w z')*(T z' z w+T z z' w+T w z' z) := by
        apply Finset.sum_le_sum
        intro w _
        apply Finset.sum_le_sum
        intro z _
        apply Finset.sum_le_sum
        intro z' _
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (twoPoint_nonneg _ _ _) (twoPoint_nonneg _ _ _))
        exact energy_triple_quartet_bound i n hn0 H₁ H₃ F₁ F₃ x hH₁ hH₃ hpos hx w z z'
      _ = _ := energy_weighted_tree_sum L M Z x
  have hdiagram : 2*section9SevenEdgeDiagramI L M Z x+section9SevenEdgeDiagramII L M Z x ≤
      (3*Ks)*(∑ u ∈ L, P x u) := by
    obtain ⟨hI,hII⟩ := hseven L M Z x
    change section9SevenEdgeDiagramI L M Z x ≤ Ks*(∑ u ∈ L, P x u) at hI
    change section9SevenEdgeDiagramII L M Z x ≤ Ks*(∑ u ∈ L, P x u) at hII
    nlinarith only [hI,hII]
  have hmass : (∑ u ∈ L, P x u) ≤ G*(1+49*J)*(n : ℝ)^2 := by
    have hball := Section8.sum_green_ball_le (by omega : 2 ≤ d) (6*n) L x
      (fun u hu => section9_distance_le_of_mem_centeredBox
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hu).1)
    calc
      _ ≤ G*(∑ u ∈ L, (max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun u _ => green x u)
      _ ≤ G*(1+J*((6*n : ℕ)+1 : ℝ)^2) := mul_le_mul_of_nonneg_left hball hG.le
      _ ≤ _ := by
        have hsq : (((6*n : ℕ)+1 : ℝ))^2 ≤ 49*(n : ℝ)^2 := by
          push_cast
          nlinarith [sq_nonneg ((n : ℝ)-1)]
        have hnn : 1 ≤ (n : ℝ)^2 := by nlinarith
        have hh := mul_le_mul_of_nonneg_left hsq hJ
        have hbase : 1+J*((6*n : ℕ)+1 : ℝ)^2 ≤ (1+49*J)*(n : ℝ)^2 := by
          nlinarith only [hh,hnn]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase hG.le
  calc
    _ ≤ ∫ ω, (2*(d : ℝ))*f ω ∂ν := integral_mono hiD (hif.const_mul _) hpoint
    _ = (2*(d : ℝ))*(∫ ω, f ω ∂ν) := integral_const_mul _ _
    _ ≤ (2*(d : ℝ))*(2*section9SevenEdgeDiagramI L M Z x+section9SevenEdgeDiagramII L M Z x) := by
      rw [hexpand]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2*(d : ℝ))*((3*Ks)*(∑ u ∈ L, P x u)) :=
      mul_le_mul_of_nonneg_left hdiagram (by positivity)
    _ ≤ (2*(d : ℝ))*((3*Ks)*(G*(1+49*J)*(n : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (by positivity)) (by positivity)
    _ = _ := by ring

end NearCritical
