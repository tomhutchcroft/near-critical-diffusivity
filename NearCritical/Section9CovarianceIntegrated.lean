module
public import NearCritical.Section9CovariancePointwise
public import NearCritical.Section9FiniteLocalIntegrability
public import NearCritical.Section9PivotalResamplingProduct

/-! Actual conditional covariance decoupling, including all finite-coordinate
integrability obligations and the retained-witness replacement error. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Original pivotal pairs whose explored component unions intersect. -/
def section9CovarianceOverlapEvent {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    Set (Configuration d) :=
  {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
    sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f ∧
    ¬ (Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ f.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2) ∧
       Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ f.2)
        (sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2))}

/-- The actual retained-witness replacement remainder, with both possible
replacement sides and original-component membership retained explicitly. -/
def section9CovarianceReplacementError {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (ω ζ : Configuration d) : ℝ :=
  let C := sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2
  let η := resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ
  ∑ w ∈ L ∪ R, (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧ w ∈ C then (1 : ℝ) else 0) *
    ((if η ∈ section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w then (1 : ℝ) else 0) +
     (if η ∈ section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w then (1 : ℝ) else 0))

private theorem covariance_pivotal_indicator_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (ω η : Configuration d)
    (h : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = η b) :
    section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω =
      section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e η := by
  have hp := sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A B ω η
    (fun b hb => h b (Finset.mem_union_left _ hb))
    (fun b hb => h b (Finset.mem_union_right _ hb)) e
  simp only [section9PivotalIndicator,hp]

private theorem covariance_resampling_agree {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (ω ω' ζ ζ' : Configuration d)
    (hω : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = ω' b)
    (hζ : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ζ b = ζ' b) :
    ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃,
      resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ b =
      resampleBonds (section9TwoClusterRevealBonds ω' L R Q₁ F₁ Q₃ F₃ e) ω' ζ' b := by
  have hm := section9TwoClusterRevealBonds_local L R Q₁ F₁ Q₃ F₃ e ω ω' hω
  intro b hb
  rw [hm]
  unfold resampleBonds extendConfiguration
  split_ifs
  · exact hζ b hb
  · exact hω b hb

private theorem covariance_overlap_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (ω η : Configuration d)
    (h : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = η b) :
    (ω ∈ section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f ↔
      η ∈ section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f) := by
  have hL (r : Vertex d) := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω η
    (fun b hb => h b (Finset.mem_union_left _ hb)) r
  have hR (r : Vertex d) := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω η
    (fun b hb => h b (Finset.mem_union_right _ hb)) r
  have hp (a : Vertex d × Vertex d) := sprinklingPivotalPair_iff_of_available_agree
    L R Q₁ F₁ Q₃ F₃ A B ω η
    (fun b hb => h b (Finset.mem_union_left _ hb))
    (fun b hb => h b (Finset.mem_union_right _ hb)) a
  simp only [section9CovarianceOverlapEvent,Set.mem_setOf_eq,hp,hL,hR]

private theorem covariance_error_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (ω ω' ζ ζ' : Configuration d)
    (hω : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = ω' b)
    (hζ : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ζ b = ζ' b) :
    section9CovarianceReplacementError L R Q₁ F₁ Q₃ F₃ A B e f ω ζ =
      section9CovarianceReplacementError L R Q₁ F₁ Q₃ F₃ A B e f ω' ζ' := by
  have hL := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω ω'
    (fun b hb => hω b (Finset.mem_union_left _ hb)) e.1
  have hR := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω ω'
    (fun b hb => hω b (Finset.mem_union_right _ hb)) e.2
  have hp := sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A B ω ω'
    (fun b hb => hω b (Finset.mem_union_left _ hb))
    (fun b hb => hω b (Finset.mem_union_right _ hb)) e
  have ha := covariance_resampling_agree L R Q₁ F₁ Q₃ F₃ e ω ω' ζ ζ' hω hζ
  unfold section9CovarianceReplacementError
  apply Finset.sum_congr rfl
  intro w _
  have hl := section9_left_marked_arm_occurrence_local L R Q₁ F₁ Q₃ F₃ A B f w _ _ ha
  have hr := section9_left_marked_arm_occurrence_local R L Q₃ F₃ Q₁ F₁ B A f.swap w _ _
    (fun b hb => ha b (by simpa only [Finset.union_comm] using hb))
  simp only [hp,hL,hR,hl,hr]

private theorem covariance_measurableSet_of_local {d : ℕ}
    (U : Finset (Bond d)) (E : Set (Configuration d))
    (h : ∀ ω η : Configuration d, (∀ b ∈ U, ω b = η b) → (ω ∈ E ↔ η ∈ E)) :
    MeasurableSet E := by
  let S : Set (U → Bool) := {ξ | extendConfiguration U (fun _ => false) ξ ∈ E}
  have he : E = (U.restrict : Configuration d → (U → Bool)) ⁻¹' S := by
    ext ω
    exact h ω _ (by intro b hb; simp [extendConfiguration,hb,Finset.restrict])
  rw [he]
  exact (Set.toFinite S).measurableSet.preimage (Finset.measurable_restrict U)

/-- The source pivotal covariance is at most its original overlap part plus
the actual adaptive retained-witness replacement error. All integrability is
proved from finite-coordinate locality under the actual positive heart law. -/
theorem section9_conditioned_pivotal_covariance_le {d : ℕ} (p : unitInterval)
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
      ∫ ω, (∫ ζ, section9CovarianceReplacementError L R Q₁ F₁ Q₃ F₃ A B e f ω ζ
        ∂percolation d p) ∂ν := by
  intro ν
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let I := section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B
  let O := fun ω => if ω ∈ section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f then (1 : ℝ) else 0
  let D := fun ω ζ => I e ω * I f
    (resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ)
  let F := section9CovarianceReplacementError L R Q₁ F₁ Q₃ F₃ A B e f
  have hI (a : Vertex d × Vertex d) (ω η : Configuration d)
      (h : ∀ b ∈ U, ω b = η b) : I a ω = I a η :=
    covariance_pivotal_indicator_local L R Q₁ F₁ Q₃ F₃ A B a ω η h
  have hO (ω η : Configuration d) (h : ∀ b ∈ U, ω b = η b) : O ω = O η := by
    simp only [O,covariance_overlap_local L R Q₁ F₁ Q₃ F₃ A B e f ω η h]
  have hD (ω ω' ζ ζ' : Configuration d)
      (hω : ∀ b ∈ U, ω b = ω' b) (hζ : ∀ b ∈ U, ζ b = ζ' b) : D ω ζ = D ω' ζ' := by
    dsimp [D]
    rw [hI e ω ω' hω,hI f _ _ (covariance_resampling_agree L R Q₁ F₁ Q₃ F₃ e ω ω' ζ ζ' hω hζ)]
  have hF (ω ω' ζ ζ' : Configuration d)
      (hω : ∀ b ∈ U, ω b = ω' b) (hζ : ∀ b ∈ U, ζ b = ζ' b) : F ω ζ = F ω' ζ' :=
    covariance_error_local L R Q₁ F₁ Q₃ F₃ A B e f ω ω' ζ ζ' hω hζ
  have hiO : Integrable O ν := section9_finite_local_integrable ν U O hO
  have hiP : Integrable (fun ω => I e ω * I f ω) ν :=
    section9_finite_local_integrable ν U _ (fun ω η h => by rw [hI e ω η h,hI f ω η h])
  have hiDi (ω : Configuration d) : Integrable (D ω) (percolation d p) :=
    section9_finite_local_integrable (percolation d p) U _
      (fun ζ ζ' h => hD ω ω ζ ζ' (fun _ _ => rfl) h)
  have hiFi (ω : Configuration d) : Integrable (F ω) (percolation d p) :=
    section9_finite_local_integrable (percolation d p) U _
      (fun ζ ζ' h => hF ω ω ζ ζ' (fun _ _ => rfl) h)
  have hiDo : Integrable (fun ω => ∫ ζ, D ω ζ ∂percolation d p) ν :=
    section9_finite_local_integral_integrable ν (percolation d p) U D
      (fun ω ω' h ζ => hD ω ω' ζ ζ h (fun _ _ => rfl))
  have hiFo : Integrable (fun ω => ∫ ζ, F ω ζ ∂percolation d p) ν :=
    section9_finite_local_integral_integrable ν (percolation d p) U F
      (fun ω ω' h ζ => hF ω ω' ζ ζ h (fun _ _ => rfl))
  have hinner (ω : Configuration d) : I e ω * I f ω ≤ O ω +
      (∫ ζ, D ω ζ ∂percolation d p) + (∫ ζ, F ω ζ ∂percolation d p) := by
    have hp (ζ : Configuration d) : I e ω * I f ω ≤ O ω + D ω ζ + F ω ζ := by
      simpa only [I,O,D,F,section9CovarianceOverlapEvent,Set.mem_setOf_eq,
        section9CovarianceReplacementError] using section9_pivotal_product_resampling_le
        (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e)
        (sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
        (L ∪ R) L R Q₁ F₁ Q₃ F₃ A B
        (Finset.union_subset_union (sprinklingUnexploredCluster_subset ω L Q₁ F₁ e.1)
          (sprinklingUnexploredCluster_subset ω R Q₃ F₃ e.2))
        (section9TwoClusterRevealBonds_touches ω L R Q₁ F₁ Q₃ F₃ e) ω ζ e f
    have hh := integral_mono (integrable_const (I e ω * I f ω))
      (((integrable_const (O ω)).add (hiDi ω)).add (hiFi ω)) hp
    simp only [Pi.add_apply] at hh
    have hs := integral_add ((integrable_const (O ω)).add (hiDi ω)) (hiFi ω)
    simp only [Pi.add_apply] at hs
    rw [hs,integral_add (integrable_const (O ω)) (hiDi ω)] at hh
    simpa only [integral_const,probReal_univ,one_smul] using hh
  have hh := integral_mono hiP ((hiO.add hiDo).add hiFo) hinner
  simp only [Pi.add_apply] at hh
  have hs := integral_add (hiO.add hiDo) hiFo
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add hiO hiDo] at hh
  have hjoint : (∫ ω, I e ω * I f ω ∂ν) =
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} := by
    have hm : MeasurableSet {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} := by
      exact (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).inter
        (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B f)
    have hInd := integral_indicator_one (μ := ν) hm
    simp only [Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply] at hInd
    calc
      _ = ∫ ω, (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f then (1 : ℝ) else 0) ∂ν := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        by_cases he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e <;>
          by_cases hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f <;>
          simp [I,section9PivotalIndicator,he,hf]
      _ = _ := hInd
  have hOi : (∫ ω, O ω ∂ν) = ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f) := by
    have hm := covariance_measurableSet_of_local U
      (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f)
      (covariance_overlap_local L R Q₁ F₁ Q₃ F₃ A B e f)
    simpa only [O,Set.indicator_apply,Pi.one_apply] using integral_indicator_one (μ := ν) hm
  have hDi : (∫ ω, (∫ ζ, D ω ζ ∂percolation d p) ∂ν) =
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} *
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} := by
    calc
      _ = ∫ ω, I e ω * (∫ ζ, I f
          (resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ)
          ∂percolation d p) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => integral_const_mul _ _
      _ = _ := section9_conditioned_pivotal_resampling_product p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
        hH₁ hH₃ hpos hLQ₃ hRQ₁ e f
  rw [hjoint,hOi,hDi] at hh
  exact sub_le_iff_le_add'.mpr (by simpa only [add_assoc,add_comm,add_left_comm] using hh)

end NearCritical
