module

public import NearCritical.Section9RevealLocality

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Fixed examined-bond mask on a specified cluster fiber. -/
def sprinklingClusterFiberMask {d : ℕ} (T Q F C : Finset (Vertex d)) : Finset (Bond d) :=
  (sprinklingAvailableBonds T Q F).filter fun b => b.1 ∈ C ∨ bondTip b ∈ C

theorem sprinklingClusterRevealBonds_eq_fiberMask {d : ℕ}
    (T Q F C : Finset (Vertex d)) (root : Vertex d) (ω : Configuration d)
    (hC : sprinklingUnexploredCluster ω T Q F root = C) :
    sprinklingClusterRevealBonds ω T Q F root = sprinklingClusterFiberMask T Q F C := by
  simp only [sprinklingClusterRevealBonds, sprinklingClusterFiberMask, hC]

/-- Membership in a specified cluster fiber depends only on that fiber's
fixed examined-bond mask. -/
theorem sprinkling_cluster_fiber_local {d : ℕ}
    (T Q F C : Finset (Vertex d)) (root : Vertex d) (ω η : Configuration d)
    (hagree : ∀ b ∈ sprinklingClusterFiberMask T Q F C, ω b = η b) :
    sprinklingUnexploredCluster ω T Q F root = C ↔
      sprinklingUnexploredCluster η T Q F root = C := by
  constructor
  · intro hC
    have he := sprinkling_cluster_eq_of_reveal_agree T Q F root ω η (by
      intro b hb
      exact hagree b ((sprinklingClusterRevealBonds_eq_fiberMask T Q F C root ω hC) ▸ hb))
    exact he.symm.trans hC
  · intro hC
    have he := sprinkling_cluster_eq_of_reveal_agree T Q F root η ω (by
      intro b hb
      exact (hagree b ((sprinklingClusterRevealBonds_eq_fiberMask T Q F C root η hC) ▸ hb)).symm)
    exact he.symm.trans hC

/-- Fixed union mask for a specified pair of tube components. -/
def section9TwoClusterFiberMask {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) : Finset (Bond d) :=
  sprinklingClusterFiberMask L Q₁ F₁ C₁ ∪ sprinklingClusterFiberMask R Q₃ F₃ C₃

theorem section9_two_cluster_fiber_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d))
    (e : Vertex d × Vertex d) (ω η : Configuration d)
    (hagree : ∀ b ∈ section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃, ω b = η b) :
    (sprinklingUnexploredCluster ω L Q₁ F₁ e.1 = C₁ ∧
      sprinklingUnexploredCluster ω R Q₃ F₃ e.2 = C₃) ↔
    (sprinklingUnexploredCluster η L Q₁ F₁ e.1 = C₁ ∧
      sprinklingUnexploredCluster η R Q₃ F₃ e.2 = C₃) := by
  apply and_congr
  · exact sprinkling_cluster_fiber_local L Q₁ F₁ C₁ e.1 ω η
      (fun b hb => hagree b (Finset.mem_union_left _ hb))
  · exact sprinkling_cluster_fiber_local R Q₃ F₃ C₃ e.2 ω η
      (fun b hb => hagree b (Finset.mem_union_right _ hb))

theorem section9TwoClusterRevealBonds_eq_fiberMask {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d))
    (e : Vertex d × Vertex d) (ω : Configuration d)
    (h₁ : sprinklingUnexploredCluster ω L Q₁ F₁ e.1 = C₁)
    (h₃ : sprinklingUnexploredCluster ω R Q₃ F₃ e.2 = C₃) :
    section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e =
      section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ := by
  simp only [section9TwoClusterRevealBonds, section9TwoClusterFiberMask,
    sprinklingClusterRevealBonds_eq_fiberMask L Q₁ F₁ C₁ e.1 ω h₁,
    sprinklingClusterRevealBonds_eq_fiberMask R Q₃ F₃ C₃ e.2 ω h₃]

end NearCritical
