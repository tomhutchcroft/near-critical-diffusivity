module

public import NearCritical.Section9ConditionedResampling

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Two pivotal events marked by the same vertex factor across the actual
adaptive replacement, as used in the source same-side collision diagrams. -/
theorem section9_conditioned_double_marked_resampling_product {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (e f : Vertex d × Vertex d) (w : Vertex d) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    (∫ ω, (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 then (1 : ℝ) else 0) *
      (∫ ζ, (if sprinklingPivotalPair
        (resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ)
        L R Q₁ F₁ Q₃ F₃ A B f ∧
        w ∈ sprinklingUnexploredCluster
          (resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ)
          L Q₁ F₁ f.1 then (1 : ℝ) else 0) ∂percolation d p) ∂ν) =
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} *
        ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ f.1} := by
  intro ν
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let H := fun ξ : U → Bool =>
    let ω := extendConfiguration U (fun _ => false) ξ
    if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ f.1 then (1 : ℝ) else 0
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
  have hH (ω : Configuration d) :
      H (U.restrict ω) =
        (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ f.1 then (1 : ℝ) else 0) := by
    have he := sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A B ω
      (extendConfiguration U (fun _ => false) (U.restrict ω))
      (by
        intro b hb
        have hbU : b ∈ U := Finset.mem_union_left _ hb
        simp [extendConfiguration, hbU, Finset.restrict])
      (by
        intro b hb
        have hbU : b ∈ U := Finset.mem_union_right _ hb
        simp [extendConfiguration, hbU, Finset.restrict]) f
    have hc := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω
      (extendConfiguration U (fun _ => false) (U.restrict ω))
      (by
        intro b hb
        have hbU : b ∈ U := Finset.mem_union_left _ hb
        simp [extendConfiguration, hbU, Finset.restrict]) f.1
    simp only [H, ← he, ← hc]
  have hp := section9_conditioned_two_cluster_factorization p L R Q₁ H₁ F₁ Q₃ H₃ F₃
    hH₁ hH₃ hpos hLQ₃ hRQ₁ e U (Finset.Subset.refl _) F H
  simp_rw [hW, hH] at hp
  have hmarked (a : Vertex d × Vertex d) :
      (∫ ω, (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B a ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ a.1 then (1 : ℝ) else 0) ∂ν) =
      ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B a ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ a.1} := by
    have hm := (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B a).inter
      (measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ a.1 w)
    have he : ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B a} ∩
        {ω | w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ a.1} : Set (Configuration d)) =
        {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B a ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ a.1} := by
      ext ω
      simp
    rw [he] at hm
    have h := integral_indicator_one (μ := ν) hm
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using h
  simp only [ν] at hmarked
  simpa only [hmarked] using hp

end NearCritical
