module
public import NearCritical.Section9SharedTargetPivotBK
public import NearCritical.Section9SharedTargetJoint
public import NearCritical.Section9CoalescenceRegularKernel
public import NearCritical.Section9CoalescenceCaseOneSum
public import NearCritical.Section8ExtensionErrorGeometry

/-! The actual SAME-oriented shared-target overlap has one left arm mass
and one regular right-pair kernel. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem shared_intersection_integral {d : ℕ} (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A Bᵢ Bⱼ : Finset (Vertex d)) :
    Integrable (fun ω => ((sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bᵢ ∩
      sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bⱼ).card : ℝ)) μ ∧
    (∫ ω, ((sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bᵢ ∩
      sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bⱼ).card : ℝ) ∂μ) =
      ∑ e ∈ E, μ.real {ω | e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bᵢ ∧
        e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bⱼ} := by
  let P := fun ω => sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bᵢ ∩
    sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bⱼ
  let J := fun e => {ω : Configuration d | e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bᵢ ∧
    e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bⱼ}
  have hm (e : Vertex d × Vertex d) : MeasurableSet (J e) := by
    have hi := (MeasurableSet.const (e ∈ E)).inter
      (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A Bᵢ e)
    have hj := (MeasurableSet.const (e ∈ E)).inter
      (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A Bⱼ e)
    simpa only [J,sprinklingPivotalPairs,Finset.mem_filter,Set.inter_def,Set.mem_setOf_eq] using hi.inter hj
  have hsub (ω : Configuration d) : P ω ⊆ E := by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).1
  have hsum (ω : Configuration d) : ((P ω).card : ℝ) =
      ∑ e ∈ E, (J e).indicator (fun _ => (1 : ℝ)) ω := by
    have heq : E.filter (fun e => e ∈ P ω) = P ω := by
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨hsub ω h,h⟩⟩
    have hh : (∑ e ∈ E, if e ∈ P ω then (1 : ℝ) else 0) = ((P ω).card : ℝ) := by
      rw [Finset.sum_boole,heq]
    simpa only [J,P,Set.indicator_apply,Set.mem_setOf_eq,Finset.mem_inter] using hh.symm
  have hi (e : Vertex d × Vertex d) : Integrable ((J e).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hm e)
  have hfun : (fun ω => ((P ω).card : ℝ)) =
      (fun ω => ∑ e ∈ E, (J e).indicator (fun _ => (1 : ℝ)) ω) := funext hsum
  constructor
  · change Integrable (fun ω => ((P ω).card : ℝ)) μ
    rw [hfun]
    exact integrable_finsetSum E (fun e _ => hi e)
  · change (∫ ω, ((P ω).card : ℝ) ∂μ) = _
    rw [hfun,integral_finsetSum E (fun e _ => hi e)]
    apply Finset.sum_congr rfl
    intro e _
    have hone : (fun _ : Configuration d => (1 : ℝ)) = (1 : Configuration d → ℝ) := by
      funext ω
      rfl
    rw [hone]
    exact integral_indicator_one (hm e)

private theorem shared_family_kernel_sum {ι α : Type*} (I : Finset ι)
    (targets : ι → Finset α) (hdis : Set.PairwiseDisjoint (I : Set ι) targets)
    (f : α → α → ℝ) (hf : ∀ b c, 0 ≤ f b c) :
    (∑ i ∈ I, ∑ j ∈ I.erase i, ∑ b ∈ targets i, ∑ c ∈ targets j, f b c) ≤
      ∑ b ∈ I.biUnion targets, ∑ c ∈ I.biUnion targets, f b c := by
  have heq : (∑ b ∈ I.biUnion targets, ∑ c ∈ I.biUnion targets, f b c) =
      ∑ i ∈ I, ∑ j ∈ I, ∑ b ∈ targets i, ∑ c ∈ targets j, f b c := by
    rw [Finset.sum_biUnion hdis]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ∑ b ∈ targets i, ∑ j ∈ I, ∑ c ∈ targets j, f b c := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_biUnion hdis]
      _ = _ := Finset.sum_comm
  rw [heq]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
  intro j _ _
  exact Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun c _ => hf b c))

private theorem shared_left_target_union {d : ℕ} (p : unitInterval)
    (L : Finset (Vertex d)) (u : Vertex d) (A : Finset (Vertex d)) :
    (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) u (A : Set (Vertex d))) ≤
      ∑ x ∈ A, (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) u {x}) := by
  have hsub : connectionToSetEvent (L : Set (Vertex d)) u (A : Set (Vertex d)) ⊆
      ⋃ x ∈ A, connectionToSetEvent (L : Set (Vertex d)) u {x} := by
    rintro ω ⟨hu,x,hx,hxL,hux⟩
    exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,hu,x,rfl,hxL,hux⟩⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le A _)

/-- Actual same-oriented shared-target overlap. The right family is regular
on the explicitly facing source core. No regularity or size cap on A, no
individual target-size cap, and no lower-cardinality condition is needed. -/
theorem section9_source_shared_oriented_target_moment_upper {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 2 ≤ n →
      ∀ {ι : Type*} (I : Finset ι) (targets : ι → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ boundary₃ A : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      A ⊆ section9FiniteEndCube i n 0 → Set.PairwiseDisjoint (I : Set ι) targets →
      (∀ j ∈ I, ∀ b ∈ targets j, b ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ j ∈ I, ∀ b ∈ targets j, sourceRegularPoint F₃
        ((section8ExtensionSmallCube i n).image (affineReflection (Pi.single i (2*(n : ℤ)))))
        boundary₃ r δ b) →
      let B := I.biUnion targets
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      (∫ ω, (∑ j ∈ I, ∑ k ∈ I.erase j,
        ((sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j) ∩
          sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets k)).card : ℝ)) ∂ν) ≤
        K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨Kj,hKj,hjoint⟩ := section9_middle_right_target_joint_probability_le (by omega : 5 ≤ d) asymptotics
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  let J : ℝ := 2*(d : ℝ)*3^(d-1)
  let Karm : ℝ := (2*(d : ℝ))*G*(1+49*J)
  let Rδ : ℝ := (r : ℝ)^((d : ℝ)-4)*δ
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hKarm : 0 ≤ Karm := by dsimp only [Karm]; positivity
  have hRδ : 0 ≤ Rδ := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) _) hδ
  refine ⟨Kj*Rδ*Karm,mul_nonneg (mul_nonneg hKj hRδ) hKarm,?_⟩
  intro i n hn ι I targets H₁ H₃ F₁ F₃ boundary₃ A hH₁ hH₃ hpos hA hdis hface hregular
    B L R Q₁ Q₃ E ν
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  let Sright := (section8ExtensionSmallCube i n).image (affineReflection (Pi.single i (2*(n : ℤ))))
  let f := fun b c : Vertex d => (max 1 (latticeDistance b c))^((4 : ℝ)-(d : ℝ))
  let T := fun j k => ∑ b ∈ targets j, ∑ c ∈ targets k, f b c
  let left := fun e : Vertex d × Vertex d => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
  let event := fun j k e => {ω : Configuration d |
    e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j) ∧
    e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets k)}
  have hf (b c : Vertex d) : 0 ≤ f b c := Real.rpow_nonneg (by positivity) _
  have hBregular (b : Vertex d) (hb : b ∈ B) : sourceRegularPoint F₃ Sright boundary₃ r δ b := by
    obtain ⟨j,hj,hb⟩ := Finset.mem_biUnion.mp hb
    exact hregular j hj b hb
  have hkernel : (∑ j ∈ I, ∑ k ∈ I.erase j, T j k) ≤ (B.card : ℝ)*Rδ := by
    let Bc : Finset (Vertex d) := @Finset.biUnion ι (Vertex d)
      (fun a b => Classical.propDecidable (a = b)) I targets
    have hBc : Bc = B := by
      ext b
      simp only [Bc,B,Finset.mem_biUnion]
    have hfamily : (∑ j ∈ I, ∑ k ∈ I.erase j, T j k) ≤
        ∑ b ∈ Bc, ∑ c ∈ Bc, f b c := shared_family_kernel_sum I targets hdis f hf
    rw [hBc] at hfamily
    refine hfamily.trans ?_
    simpa only [Rδ,f,min_self] using section9_regular_bubble_pair_sum_le (by omega : 4 ≤ d)
      F₃ Sright boundary₃ B B r hr δ hBregular hBregular
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hprob (j : ι) (hj : j ∈ I) (k : ι) (hk : k ∈ I) (e : Vertex d × Vertex d) (he : e ∈ E) :
      ν.real (event j k e) ≤ left e*(Kj*(n : ℝ)^((2 : ℝ)-(d : ℝ))*T j k) := by
    have hb := section9_source_same_oriented_shared_pivot_probability_le (criticalPoint d) i n hn0
      H₁ H₃ F₁ F₃ A (targets j) (targets k) e hH₁ hH₃ hpos hA (hface j hj) (hface k hk)
    have hvMiddle := ((mem_orientedLatticePairs (section9FiniteMiddle i n) e.1 e.2).mp he).2.1
    have hrj := hjoint i n hn R (targets j) (targets k) e.2 hvMiddle
      (fun b hb => (Finset.mem_filter.mp (hface j hj b hb)).1)
      (fun c hc => (Finset.mem_filter.mp (hface k hk c hc)).1)
    exact hb.trans (mul_le_mul_of_nonneg_left hrj measureReal_nonneg)
  have hscale : G*(1+J*((6*n : ℕ)+1 : ℝ)^2) ≤ G*(1+49*J)*(n : ℝ)^2 := by
    have hsq : (((6*n : ℕ)+1 : ℝ))^2 ≤ 49*(n : ℝ)^2 := by
      push_cast
      nlinarith [sq_nonneg ((n : ℝ)-1)]
    have hnn : 1 ≤ (n : ℝ)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq hJ
    have hbase : 1+J*((6*n : ℕ)+1 : ℝ)^2 ≤ (1+49*J)*(n : ℝ)^2 := by nlinarith only [hh,hnn]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase hG.le
  have hleft : (∑ e ∈ E, left e) ≤ Karm*(n : ℝ)^2*(A.card : ℝ) := by
    calc
      _ ≤ ∑ e ∈ E, ∑ x ∈ A, section9RightArm L e.1 x :=
        Finset.sum_le_sum (fun e _ => shared_left_target_union (criticalPoint d) L e.1 A)
      _ = ∑ x ∈ A, ∑ e ∈ E, section9RightArm L e.1 x := Finset.sum_comm
      _ ≤ ∑ _x ∈ A, ((2*(d : ℝ))*(G*(1+J*((6*n : ℕ)+1 : ℝ)^2))) :=
        Finset.sum_le_sum (fun x hx => section9_middle_tail_mass_le (by omega : 2 ≤ d) hG.le green i n L x
          (Finset.mem_filter.mp (hA hx)).1)
      _ ≤ ∑ _x ∈ A, (Karm*(n : ℝ)^2) := by
        apply Finset.sum_le_sum
        intro x _
        have hh := mul_le_mul_of_nonneg_left hscale (by positivity : (0 : ℝ) ≤ 2*(d : ℝ))
        simpa only [Karm,mul_assoc] using hh
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; ring
  have hi (j k : ι) : Integrable (fun ω =>
      ((sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j) ∩
        sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets k)).card : ℝ)) ν :=
    (shared_intersection_integral ν E L R Q₁ F₁ Q₃ F₃ A (targets j) (targets k)).1
  have hexpand : (∫ ω, (∑ j ∈ I, ∑ k ∈ I.erase j,
      ((sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j) ∩
        sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets k)).card : ℝ)) ∂ν) =
      ∑ j ∈ I, ∑ k ∈ I.erase j, ∑ e ∈ E, ν.real (event j k e) := by
    rw [integral_finsetSum I (fun j _ => integrable_finsetSum (I.erase j) (fun k _ => hi j k))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum (I.erase j) (fun k _ => hi j k)]
    apply Finset.sum_congr rfl
    intro k _
    exact (shared_intersection_integral ν E L R Q₁ F₁ Q₃ F₃ A (targets j) (targets k)).2
  have hmove : (∑ j ∈ I, ∑ k ∈ I.erase j, ∑ e ∈ E, ν.real (event j k e)) =
      ∑ e ∈ E, ∑ j ∈ I, ∑ k ∈ I.erase j, ν.real (event j k e) := by
    calc
      _ = ∑ j ∈ I, ∑ e ∈ E, ∑ k ∈ I.erase j, ν.real (event j k e) :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have heach (e : Vertex d × Vertex d) (he : e ∈ E) :
      (∑ j ∈ I, ∑ k ∈ I.erase j, ν.real (event j k e)) ≤
        left e*(Kj*(n : ℝ)^((2 : ℝ)-(d : ℝ)))*((B.card : ℝ)*Rδ) := by
    calc
      _ ≤ ∑ j ∈ I, ∑ k ∈ I.erase j, left e*(Kj*(n : ℝ)^((2 : ℝ)-(d : ℝ))*T j k) :=
        Finset.sum_le_sum (fun j hj => Finset.sum_le_sum
          (fun k hk => hprob j hj k (Finset.mem_erase.mp hk).2 e he))
      _ = (left e*(Kj*(n : ℝ)^((2 : ℝ)-(d : ℝ))))*(∑ j ∈ I, ∑ k ∈ I.erase j, T j k) := by
        simp only [Finset.mul_sum,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel
        (mul_nonneg measureReal_nonneg (mul_nonneg hKj (Real.rpow_nonneg hnpos.le _)))
  have hpower : (n : ℝ)^2*(n : ℝ)^((2 : ℝ)-(d : ℝ)) = (n : ℝ)^((4 : ℝ)-(d : ℝ)) := by
    rw [← Real.rpow_natCast (n : ℝ) 2,← Real.rpow_add hnpos]
    congr 1
    ring
  rw [hexpand,hmove]
  calc
    _ ≤ ∑ e ∈ E, left e*(Kj*(n : ℝ)^((2 : ℝ)-(d : ℝ)))*((B.card : ℝ)*Rδ) :=
      Finset.sum_le_sum heach
    _ = (∑ e ∈ E, left e)*(Kj*(n : ℝ)^((2 : ℝ)-(d : ℝ)))*((B.card : ℝ)*Rδ) := by
      simp only [Finset.sum_mul]
    _ ≤ (Karm*(n : ℝ)^2*(A.card : ℝ))*(Kj*(n : ℝ)^((2 : ℝ)-(d : ℝ)))*((B.card : ℝ)*Rδ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hleft (mul_nonneg hKj (Real.rpow_nonneg hnpos.le _)))
        (mul_nonneg (Nat.cast_nonneg _) hRδ)
    _ = (Kj*Rδ*Karm)*((n : ℝ)^2*(n : ℝ)^((2 : ℝ)-(d : ℝ)))*(A.card : ℝ)*(B.card : ℝ) := by ring
    _ = _ := by rw [hpower]

end NearCritical
