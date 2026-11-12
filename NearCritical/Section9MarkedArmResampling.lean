module
public import NearCritical.Section9ConditionedResampling
public import NearCritical.Section9MarkedArmOccurrence

/-! Adaptive resampling factorization with a replacement marked-arm witness,
without requiring the replacement configuration to remain pivotal. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Original marked pivotality factors from the replacement marked-arm
occurrence under the actual adaptive resampling law. -/
theorem section9_conditioned_marked_arm_resampling_product {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (e f : Vertex d × Vertex d) (w : Vertex d) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    (∫ ω, (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 then (1 : ℝ) else 0) *
      (∫ ζ, (if resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ ∈
        section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w
        then (1 : ℝ) else 0) ∂percolation d p) ∂ν) =
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} *
      ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w) := by
  intro ν
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let J := section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w
  let H := fun ξ : U → Bool =>
    if extendConfiguration U (fun _ => false) ξ ∈ J then (1 : ℝ) else 0
  let F := fun (C₁ C₃ : Finset (Vertex d))
      (_ : section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) =>
    if ((openGraph (fun _ : Bond d => true)).Adj e.1 e.2 ∧ e.1 ∈ L ∧ e.2 ∈ R ∧
      (C₁ ∩ A).Nonempty ∧ (C₃ ∩ B).Nonempty ∧ Disjoint C₁ C₃) ∧ w ∈ C₁ then (1 : ℝ) else 0
  have hW (ω : Configuration d) :
      section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω =
        (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 then (1 : ℝ) else 0) := by
    unfold section9TwoClusterRevealWeight
    dsimp only [F]
    unfold sprinklingPivotalPair
    congr 1
  have hH (ω : Configuration d) : H (U.restrict ω) =
      (if ω ∈ J then (1 : ℝ) else 0) := by
    have he := section9_left_marked_arm_occurrence_local L R Q₁ F₁ Q₃ F₃ A B f w ω
      (extendConfiguration U (fun _ => false) (U.restrict ω))
      (by intro b hb; simp [U,extendConfiguration,hb,Finset.restrict])
    simp only [H,J,← he]
  have hp := section9_conditioned_two_cluster_factorization p L R Q₁ H₁ F₁ Q₃ H₃ F₃
    hH₁ hH₃ hpos hLQ₃ hRQ₁ e U (Finset.Subset.refl _) F H
  simp_rw [hW,hH] at hp
  have hmarked : (∫ ω, (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 then (1 : ℝ) else 0) ∂ν) =
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} := by
    have hm := (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).inter
      (measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ e.1 w)
    have he : ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} ∩
        {ω | w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} : Set (Configuration d)) =
        {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} := by ext ω; simp
    rw [he] at hm
    simpa only [Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply] using
      (integral_indicator_one (μ := ν) hm)
  have hJ : (∫ ω, (if ω ∈ J then (1 : ℝ) else 0) ∂ν) = ν.real J := by
    simpa only [Set.indicator_apply,Pi.one_apply] using
      (integral_indicator_one (μ := ν)
        (measurableSet_section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w))
  simpa only [ν,hmarked,hJ,J] using hp

end NearCritical
