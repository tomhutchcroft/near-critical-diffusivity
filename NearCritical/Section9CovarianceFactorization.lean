module
public import NearCritical.Section9CovarianceIntegrated

/-! Exact product factorization of the retained-witness replacement remainder. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- One vertex's retained-witness contribution: original pivotality marked
in either original component, followed by either replacement-side witness. -/
def section9CovarianceWitnessIntegrand {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (w : Vertex d) (ω ζ : Configuration d) : ℝ :=
  let C := sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2
  let η := resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ
  (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧ w ∈ C then (1 : ℝ) else 0) *
    ((if η ∈ section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w then (1 : ℝ) else 0) +
     (if η ∈ section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w then (1 : ℝ) else 0))

private theorem covariance_witness_integrand_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) (w : Vertex d)
    (ω ω' ζ ζ' : Configuration d)
    (hω : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = ω' b)
    (hζ : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ζ b = ζ' b) :
    section9CovarianceWitnessIntegrand L R Q₁ F₁ Q₃ F₃ A B e f w ω ζ =
      section9CovarianceWitnessIntegrand L R Q₁ F₁ Q₃ F₃ A B e f w ω' ζ' := by
  have hL := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω ω'
    (fun b hb => hω b (Finset.mem_union_left _ hb)) e.1
  have hR := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω ω'
    (fun b hb => hω b (Finset.mem_union_right _ hb)) e.2
  have hp := sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A B ω ω'
    (fun b hb => hω b (Finset.mem_union_left _ hb))
    (fun b hb => hω b (Finset.mem_union_right _ hb)) e
  have hm := section9TwoClusterRevealBonds_local L R Q₁ F₁ Q₃ F₃ e ω ω' hω
  have ha : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃,
      resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ b =
      resampleBonds (section9TwoClusterRevealBonds ω' L R Q₁ F₁ Q₃ F₃ e) ω' ζ' b := by
    intro b hb
    rw [hm]
    unfold resampleBonds extendConfiguration
    split_ifs
    · exact hζ b hb
    · exact hω b hb
  have hl := section9_left_marked_arm_occurrence_local L R Q₁ F₁ Q₃ F₃ A B f w _ _ ha
  have hr := section9_left_marked_arm_occurrence_local R L Q₃ F₃ Q₁ F₁ B A f.swap w _ _
    (fun b hb => ha b (by simpa only [Finset.union_comm] using hb))
  simp only [section9CovarianceWitnessIntegrand,hL,hR,hp,hl,hr]

private theorem covariance_integral_boole {d : ℕ} (μ : Measure (Configuration d))
    (E : Set (Configuration d)) (hE : MeasurableSet E) :
    (∫ ω, (if ω ∈ E then (1 : ℝ) else 0) ∂μ) = μ.real E := by
  simpa only [Set.indicator_apply,Pi.one_apply] using integral_indicator_one (μ := μ) hE

/-- Exact factorization at one collision vertex. The original mark may lie
in either component, and the replacement need only have the retained arms. -/
theorem section9_conditioned_covariance_witness_product {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (e f : Vertex d × Vertex d) (w : Vertex d) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    (∫ ω, (∫ ζ, section9CovarianceWitnessIntegrand L R Q₁ F₁ Q₃ F₃ A B e f w ω ζ
      ∂percolation d p) ∂ν) =
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} *
      (ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w) +
       ν.real (section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w)) := by
  intro ν
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let J := section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w
  let K := section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w
  let M := fun ω => if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
    w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2
    then (1 : ℝ) else 0
  let H := fun ξ : U → Bool =>
    (if extendConfiguration U (fun _ => false) ξ ∈ J then (1 : ℝ) else 0) +
    (if extendConfiguration U (fun _ => false) ξ ∈ K then (1 : ℝ) else 0)
  let F := fun (C₁ C₃ : Finset (Vertex d))
      (_ : section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) =>
    if ((openGraph (fun _ : Bond d => true)).Adj e.1 e.2 ∧ e.1 ∈ L ∧ e.2 ∈ R ∧
      (C₁ ∩ A).Nonempty ∧ (C₃ ∩ B).Nonempty ∧ Disjoint C₁ C₃) ∧ w ∈ C₁ ∪ C₃ then (1 : ℝ) else 0
  have hW (ω : Configuration d) : section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω = M ω := by
    unfold section9TwoClusterRevealWeight
    dsimp only [F,M]
    unfold sprinklingPivotalPair
    congr 1
  have hH (ω : Configuration d) : H (U.restrict ω) =
      (if ω ∈ J then (1 : ℝ) else 0) + (if ω ∈ K then (1 : ℝ) else 0) := by
    have hl := section9_left_marked_arm_occurrence_local L R Q₁ F₁ Q₃ F₃ A B f w ω
      (extendConfiguration U (fun _ => false) (U.restrict ω))
      (by intro b hb; simp [U,extendConfiguration,hb,Finset.restrict])
    have hr := section9_left_marked_arm_occurrence_local R L Q₃ F₃ Q₁ F₁ B A f.swap w ω
      (extendConfiguration U (fun _ => false) (U.restrict ω))
      (by
        intro b hb
        have hbU : b ∈ U := by simpa only [U,Finset.union_comm] using hb
        simp [extendConfiguration,hbU,Finset.restrict])
    simp only [H,J,K,← hl,← hr]
  have hp := section9_conditioned_two_cluster_factorization p L R Q₁ H₁ F₁ Q₃ H₃ F₃
    hH₁ hH₃ hpos hLQ₃ hRQ₁ e U (Finset.Subset.refl _) F H
  simp_rw [hW,hH] at hp
  have hmM : MeasurableSet {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} := by
    have hm := (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).inter
      ((measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ e.1 w).union
       (measurableSet_sprinklingUnexploredCluster_mem R Q₃ F₃ e.2 w))
    have he : ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} ∩
        ({ω | w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} ∪
         {ω | w ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2}) : Set (Configuration d)) =
        {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} := by
      ext ω
      simp only [Set.mem_inter_iff,Set.mem_union,Set.mem_setOf_eq,Finset.mem_union]
    rwa [he] at hm
  have hMi : (∫ ω, M ω ∂ν) =
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} := by
    simpa only [M,Set.mem_setOf_eq] using covariance_integral_boole ν _ hmM
  have hJloc (ω η : Configuration d) (h : ∀ b ∈ U, ω b = η b) : (ω ∈ J ↔ η ∈ J) :=
    section9_left_marked_arm_occurrence_local L R Q₁ F₁ Q₃ F₃ A B f w ω η h
  have hKloc (ω η : Configuration d) (h : ∀ b ∈ U, ω b = η b) : (ω ∈ K ↔ η ∈ K) :=
    section9_left_marked_arm_occurrence_local R L Q₃ F₃ Q₁ F₁ B A f.swap w ω η
      (fun b hb => h b (by simpa only [U,Finset.union_comm] using hb))
  have hiJ : Integrable (fun ω => if ω ∈ J then (1 : ℝ) else 0) ν :=
    section9_finite_local_integrable ν U _ (fun ω η h => by simp only [hJloc ω η h])
  have hiK : Integrable (fun ω => if ω ∈ K then (1 : ℝ) else 0) ν :=
    section9_finite_local_integrable ν U _ (fun ω η h => by simp only [hKloc ω η h])
  have hHK : (∫ ω, ((if ω ∈ J then (1 : ℝ) else 0) + (if ω ∈ K then (1 : ℝ) else 0)) ∂ν) =
      ν.real J + ν.real K := by
    rw [integral_add hiJ hiK,
      covariance_integral_boole ν J (measurableSet_section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w),
      covariance_integral_boole ν K (measurableSet_section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w)]
  calc
    _ = ∫ ω, M ω * (∫ ζ, ((if resampleBonds
        (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ ∈ J then (1 : ℝ) else 0) +
        (if resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ ∈ K
          then (1 : ℝ) else 0)) ∂percolation d p) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => integral_const_mul _ _
    _ = _ := by simpa only [ν,hMi,hHK,J,K] using hp

/-- The entire finite replacement remainder is a product sum under the
actual revealed law, with finite-sum integrability discharged internally. -/
theorem section9_conditioned_covariance_remainder_factorization {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (e f : Vertex d × Vertex d) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    (∫ ω, (∫ ζ, section9CovarianceReplacementError L R Q₁ F₁ Q₃ F₃ A B e f ω ζ
      ∂percolation d p) ∂ν) =
      ∑ w ∈ L ∪ R,
        ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} *
        (ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w) +
         ν.real (section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w)) := by
  intro ν
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let F := section9CovarianceWitnessIntegrand L R Q₁ F₁ Q₃ F₃ A B e f
  have hiInner (ω : Configuration d) (w : Vertex d) : Integrable (F w ω) (percolation d p) :=
    section9_finite_local_integrable (percolation d p) U _
      (fun ζ ζ' h => covariance_witness_integrand_local L R Q₁ F₁ Q₃ F₃ A B e f w
        ω ω ζ ζ' (fun _ _ => rfl) h)
  have hiOuter (w : Vertex d) : Integrable (fun ω => ∫ ζ, F w ω ζ ∂percolation d p) ν :=
    section9_finite_local_integral_integrable ν (percolation d p) U (F w)
      (fun ω ω' h ζ => covariance_witness_integrand_local L R Q₁ F₁ Q₃ F₃ A B e f w
        ω ω' ζ ζ h (fun _ _ => rfl))
  calc
    _ = ∫ ω, (∫ ζ, ∑ w ∈ L ∪ R, F w ω ζ ∂percolation d p) ∂ν := rfl
    _ = ∫ ω, (∑ w ∈ L ∪ R, ∫ ζ, F w ω ζ ∂percolation d p) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => integral_finsetSum _ (fun w _ => hiInner ω w)
    _ = ∑ w ∈ L ∪ R, ∫ ω, (∫ ζ, F w ω ζ ∂percolation d p) ∂ν :=
      integral_finsetSum _ (fun w _ => hiOuter w)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      exact section9_conditioned_covariance_witness_product p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
        hH₁ hH₃ hpos hLQ₃ hRQ₁ e f w

/-- The source covariance decoupling inequality with its replacement
remainder factored into actual conditional probabilities. -/
theorem section9_conditioned_pivotal_covariance_product_le {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (e f : Vertex d × Vertex d) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} -
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} *
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} ≤
    ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f) +
      ∑ w ∈ L ∪ R,
        ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2} *
        (ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w) +
         ν.real (section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w)) := by
  intro ν
  have h := section9_conditioned_pivotal_covariance_le p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ e f
  dsimp only at h
  rw [section9_conditioned_covariance_remainder_factorization p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ e f] at h
  exact h

end NearCritical
