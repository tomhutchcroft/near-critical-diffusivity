module

public import NearCritical.Section9ResamplingMask

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- The source pivotal event survives resampling unless one of the new
tube components collides with the revealed set. -/
theorem section9_pivotal_resampling_or_collision {d : ℕ}
    (S : Finset (Bond d)) (C L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (htouch : ∀ b ∈ S, b.1 ∈ C ∨ bondTip b ∈ C)
    (ω ζ : Configuration d) (e : Vertex d × Vertex d)
    (hleft : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1) C)
    (hright : Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2) C)
    (hpivot : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e) :
    sprinklingPivotalPair (resampleBonds S ω ζ) L R Q₁ F₁ Q₃ F₃ A B e ∨
      (sprinklingUnexploredCluster (resampleBonds S ω ζ) L Q₁ F₁ e.1 ∩ C).Nonempty ∨
      (sprinklingUnexploredCluster (resampleBonds S ω ζ) R Q₃ F₃ e.2 ∩ C).Nonempty := by
  by_cases hnL : Disjoint (sprinklingUnexploredCluster (resampleBonds S ω ζ) L Q₁ F₁ e.1) C
  · by_cases hnR : Disjoint (sprinklingUnexploredCluster (resampleBonds S ω ζ) R Q₃ F₃ e.2) C
    · apply Or.inl
      have heL := resampleBonds_sprinkling_cluster_eq S C L Q₁ F₁ htouch ω ζ e.1 hleft hnL
      have heR := resampleBonds_sprinkling_cluster_eq S C R Q₃ F₃ htouch ω ζ e.2 hright hnR
      simpa only [sprinklingPivotalPair, heL, heR] using hpivot
    · exact Or.inr (Or.inr (Finset.not_disjoint_iff_nonempty_inter.mp hnR))
  · exact Or.inr (Or.inl (Finset.not_disjoint_iff_nonempty_inter.mp hnL))

/-- Pointwise indicator comparison used before integrating the resampling
law in the covariance estimate. -/
theorem section9_pivotal_resampling_indicator_le {d : ℕ}
    (S : Finset (Bond d)) (C L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (htouch : ∀ b ∈ S, b.1 ∈ C ∨ bondTip b ∈ C)
    (ω ζ : Configuration d) (e : Vertex d × Vertex d) :
    (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1) C ∧
      Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2) C then (1 : ℝ) else 0) ≤
    (if sprinklingPivotalPair (resampleBonds S ω ζ) L R Q₁ F₁ Q₃ F₃ A B e then 1 else 0) +
      ((if (sprinklingUnexploredCluster (resampleBonds S ω ζ) L Q₁ F₁ e.1 ∩ C).Nonempty then 1 else 0) +
       (if (sprinklingUnexploredCluster (resampleBonds S ω ζ) R Q₃ F₃ e.2 ∩ C).Nonempty then 1 else 0)) := by
  by_cases h : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1) C ∧
      Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2) C
  · have hc := section9_pivotal_resampling_or_collision S C L R Q₁ F₁ Q₃ F₃ A B
      htouch ω ζ e h.2.1 h.2.2 h.1
    rcases hc with hp | hL | hR
    all_goals split_ifs <;> simp_all <;> norm_num
  · simp only [if_neg h]
    positivity

end NearCritical
