module
public import NearCritical.Section9PivotalSwap
public import NearCritical.Section9PivotalResamplingComparison
public import NearCritical.Section9RetainedCollisionWitness

/-! The deterministic replacement alternative used by covariance decoupling. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- An old pivot avoiding the revealed set either remains pivotal or has
retained marked-arm witnesses in the replacement configuration. The latter
alternatives allow replacement pivotality to fail. -/
theorem section9_pivotal_resampling_or_retained_witness {d : ℕ}
    (S : Finset (Bond d)) (C L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (htouch : ∀ b ∈ S, b.1 ∈ C ∨ bondTip b ∈ C)
    (ω ζ : Configuration d) (f : Vertex d × Vertex d)
    (hpivot : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f)
    (hleft : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) C)
    (hright : Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) C) :
    sprinklingPivotalPair (resampleBonds S ω ζ) L R Q₁ F₁ Q₃ F₃ A B f ∨
      (∃ w ∈ C, resampleBonds S ω ζ ∈
        section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w) ∨
      (∃ w ∈ C, resampleBonds S ω ζ ∈
        section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w) := by
  rcases section9_pivotal_resampling_or_collision S C L R Q₁ F₁ Q₃ F₃ A B
    htouch ω ζ f hleft hright hpivot with hp | hL | hR
  · exact Or.inl hp
  · exact Or.inr (Or.inl (section9_retained_left_collision_occurrence S C L R Q₁ F₁ Q₃ F₃ A B
      htouch ω ζ f hpivot hleft hright hL))
  · apply Or.inr ∘ Or.inr
    have hs := (sprinklingPivotalPair_swap_iff ω L R Q₁ F₁ Q₃ F₃ A B f).mp hpivot
    exact section9_retained_left_collision_occurrence S C R L Q₃ F₃ Q₁ F₁ B A
      htouch ω ζ f.swap hs hright hleft hR

end NearCritical
