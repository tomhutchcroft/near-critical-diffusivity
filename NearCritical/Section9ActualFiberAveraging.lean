module
public import NearCritical.Section9SourceGoodEnergyBound
public import NearCritical.Section9FiniteLocalIntegrability

/-! Actual finite cluster-fiber partition and division-free source averaging. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem actual_fiber_measurable {d : ℕ} (L Q F C : Finset (Vertex d))
    (root : Vertex d) :
    MeasurableSet {ω | sprinklingUnexploredCluster ω L Q F root = C} := by
  let S := sprinklingAvailableBonds L Q F
  let A₀ : Set ((b : S) → Bool) :=
    {ξ | sprinklingUnexploredCluster (extendConfiguration S (fun _ => false) ξ) L Q F root = C}
  have heq : {ω | sprinklingUnexploredCluster ω L Q F root = C} = S.restrict ⁻¹' A₀ := by
    ext ω
    have hc := sprinklingUnexploredCluster_eq_of_available_agree L Q F ω
      (extendConfiguration S (fun _ => false) (S.restrict ω))
      (by intro b hb; simp [S,extendConfiguration,hb]) root
    change sprinklingUnexploredCluster ω L Q F root = C ↔
      sprinklingUnexploredCluster (extendConfiguration S (fun _ => false) (S.restrict ω)) L Q F root = C
    rw [hc]
  rw [heq]
  exact (Set.toFinite A₀).measurableSet.preimage (Finset.measurable_restrict S)

private theorem actual_fiber_partition_sum {d : ℕ} (L Q F : Finset (Vertex d))
    (root : Vertex d) (f : Finset (Vertex d) → Configuration d → ℝ) (ω : Configuration d) :
    (∑ C ∈ L.powerset, ({θ | sprinklingUnexploredCluster θ L Q F root = C} :
      Set (Configuration d)).indicator (f C) ω) =
        f (sprinklingUnexploredCluster ω L Q F root) ω := by
  let C₀ := sprinklingUnexploredCluster ω L Q F root
  rw [Finset.sum_eq_single C₀]
  · simp [C₀,Set.indicator_apply]
  · intro C _ hne
    have hnot : sprinklingUnexploredCluster ω L Q F root ≠ C := Ne.symm hne
    simp only [Set.indicator_apply,Set.mem_setOf_eq,if_neg hnot]
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr
      (sprinklingUnexploredCluster_subset ω L Q F root))).elim

/-- Exact actual-cluster partition identity under an arbitrary finite law.
All finite cluster observables are integrable; no positive fiber is required. -/
theorem section9_actual_cluster_fiber_sum {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (L Q F : Finset (Vertex d)) (root : Vertex d) (f : Finset (Vertex d) → ℝ) :
    (∑ C ∈ L.powerset, μ.real {ω | sprinklingUnexploredCluster ω L Q F root = C}*f C) =
      ∫ ω, f (sprinklingUnexploredCluster ω L Q F root) ∂μ := by
  let E := fun C => {ω : Configuration d | sprinklingUnexploredCluster ω L Q F root = C}
  calc
    _ = ∑ C ∈ L.powerset, ∫ ω, (E C).indicator (fun _ => f C) ω ∂μ := by
      apply Finset.sum_congr rfl
      intro C _
      symm
      simpa only [smul_eq_mul] using integral_indicator_const (f C) (actual_fiber_measurable L Q F C root)
    _ = ∫ ω, ∑ C ∈ L.powerset, (E C).indicator (fun _ => f C) ω ∂μ :=
      (integral_finsetSum L.powerset (fun C _ =>
        (integrable_const (f C)).indicator (actual_fiber_measurable L Q F C root))).symm
    _ = _ := integral_congr_ae (ae_of_all _ (fun ω => actual_fiber_partition_sum L Q F root
      (fun C _ => f C) ω))

/-- The same actual fibers partition any integrable observable exactly. -/
theorem section9_actual_cluster_fiber_integral_sum {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (L Q F : Finset (Vertex d)) (root : Vertex d) (g : Configuration d → ℝ)
    (hg : Integrable g μ) :
    (∑ C ∈ L.powerset, ∫ ω in {θ | sprinklingUnexploredCluster θ L Q F root = C}, g ω ∂μ) =
      ∫ ω, g ω ∂μ := by
  have hsum := integral_finsetSum L.powerset (fun C _ =>
    hg.indicator (actual_fiber_measurable L Q F C root))
  simp_rw [integral_indicator (actual_fiber_measurable L Q F _ root)] at hsum
  rw [← hsum]
  exact integral_congr_ae (ae_of_all _ (fun ω => actual_fiber_partition_sum L Q F root (fun _ => g) ω))

/-- Actual source fiber averaging of the good-exit energy inequality.
The numerator vanishes on nonunique fibers, and the count is integrated on
the same fibers before summing. No positive mass or energy is assumed. -/
theorem section9_source_actual_fiber_energy_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ U : ℝ, 0 < U ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary B W : Finset (Vertex d)) (root : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      root ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary r δ y) →
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let cluster := fun ω => sprinklingUnexploredCluster ω L Q₁ F₁ root
      let X := fun C : Finset (Vertex d) => if C ∩ W = {root} then
        max (c-K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*((section9ExitFace i n ∩ C).card : ℝ)) 0 *
          ((C ∩ section8ExtensionMiddleCore i n).card : ℝ) else 0
      let D := fun C : Finset (Vertex d) =>
        ∑ j ∈ section9AvoidanceGoodLastExitCandidates R C Q₃ F₃ (section9ExitFace i n ∩ C),
          (∑ z ∈ C ∩ section8ExtensionMiddleCore i n,
            (percolation d (criticalPoint d)).real
              (connectionToSetEvent (R : Set (Vertex d)) z {j.1.1}))^2
      let g := fun ω => ((section9UniqueLeftPivotalPairs ω
        (orientedLatticePairs (section9FiniteMiddle i n)) L R Q₁ F₁ Q₃ F₃ W B root).card : ℝ)
      let s := (B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))
      (s/U)*(∫ ω, X (cluster ω) ∂ν)^2 ≤
        (∫ ω, D (cluster ω) ∂ν)*(∫ ω, g ω ∂ν) := by
  obtain ⟨U,hU,δ,hδ,hsource⟩ := section9_source_good_energy_bound hd asymptotics rectangle reimer
  refine ⟨U,hU,δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,K,hK,hbound⟩ := hsource r hr
  refine ⟨c,hc,K,hK,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary B W root hH₁ hH₃ hpos hroot hB hreg
    Q₁ Q₃ L R ν cluster X D g s
  let E := fun C : Finset (Vertex d) => {ω : Configuration d | cluster ω = C}
  let m := fun C => ν.real (E C)
  let P := fun C => ∫ ω in E C, g ω ∂ν
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hD (C : Finset (Vertex d)) : 0 ≤ D C := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hP (C : Finset (Vertex d)) : 0 ≤ P C := integral_nonneg fun _ => Nat.cast_nonneg _
  have hg : Integrable g ν := by
    let T := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
    apply section9_finite_local_integrable ν T g
    intro ω θ hagree
    have heqL := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ
      (fun b hb => hagree b (Finset.mem_union_left _ hb))
    have heqR := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ
      (fun b hb => hagree b (Finset.mem_union_right _ hb))
    have hp : section9UniqueLeftPivotalPairs ω (orientedLatticePairs (section9FiniteMiddle i n))
        L R Q₁ F₁ Q₃ F₃ W B root =
      section9UniqueLeftPivotalPairs θ (orientedLatticePairs (section9FiniteMiddle i n))
        L R Q₁ F₁ Q₃ F₃ W B root := by
      ext e
      simp only [section9UniqueLeftPivotalPairs,sprinklingPivotalPairs,Finset.mem_filter,
        sprinklingPivotalPair,heqL e.1,heqR e.2]
    exact congrArg (fun S : Finset (Vertex d × Vertex d) => (S.card : ℝ)) hp
  have hpoint (C : Finset (Vertex d)) (hC : C ∈ L.powerset) :
      (s/U)*m C*(X C)^2 ≤ D C*P C := by
    by_cases hu : C ∩ W = {root}
    · have hh := hbound i n hn H₁ H₃ F₁ F₃ boundary B C
        (C ∩ section8ExtensionMiddleCore i n) W root hH₁ hH₃ hpos hroot
        (Finset.mem_powerset.mp hC) hB hreg Finset.inter_subset_right Finset.inter_subset_left hu
      change s*m C*(max (c-K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*
        ((section9ExitFace i n ∩ C).card : ℝ)) 0)^2*
        ((C ∩ section8ExtensionMiddleCore i n).card : ℝ)^2 ≤ U*D C*P C at hh
      simp only [X,if_pos hu]
      apply (mul_le_mul_iff_right₀ hU).mp
      convert hh using 1 <;>
        field_simp [ne_of_gt hU] <;> ring
    · simp only [X,if_neg hu,pow_two,mul_zero]
      exact mul_nonneg (hD C) (hP C)
  have havg := section9_finite_weighted_energy_averaging L.powerset m X D P (s/U)
    (div_nonneg hs hU.le) (fun _ _ => measureReal_nonneg) (fun C _ => hD C) (fun C _ => hP C) hpoint
  have hsumX := section9_actual_cluster_fiber_sum ν L Q₁ F₁ root X
  have hsumD := section9_actual_cluster_fiber_sum ν L Q₁ F₁ root D
  have hsumP := section9_actual_cluster_fiber_integral_sum ν L Q₁ F₁ root g hg
  change (∑ C ∈ L.powerset, m C*X C) = ∫ ω, X (cluster ω) ∂ν at hsumX
  change (∑ C ∈ L.powerset, m C*D C) = ∫ ω, D (cluster ω) ∂ν at hsumD
  change (∑ C ∈ L.powerset, P C) = ∫ ω, g ω ∂ν at hsumP
  rw [hsumX,hsumD,hsumP] at havg
  exact havg

end NearCritical
