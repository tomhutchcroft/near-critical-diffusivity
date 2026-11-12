module

public import NearCritical.Section10ClusterConditioning

/-! Section10 eq.sigma_pc: the union of revealed clusters determines individual
cube reveals because the cubes are disjoint. Finite-family version only. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
variable {J : Type*}

def clusterFamilyUnion {d : ℕ} (ω : Configuration d) (s : Finset J)
    (Q H : J → Finset (Vertex d)) : Finset (Vertex d) :=
  s.biUnion (fun j => heartClusterUnion ω (Q j) (H j))

/-- Recovering a cube's actual reveal from the global union is proved from
geometric separation, not supplied as a law-identification hypothesis. -/
theorem clusterFamilyUnion_inter_cube {d : ℕ} (ω : Configuration d) (s : Finset J)
    (Q H : J → Finset (Vertex d)) (hQ : (s : Set J).PairwiseDisjoint Q)
    (j : J) (hj : j ∈ s) :
    clusterFamilyUnion ω s Q H ∩ Q j = heartClusterUnion ω (Q j) (H j) := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).1
    by_cases hij : i = j
    · simpa only [hij] using hxi
    · exact (Finset.disjoint_left.mp (hQ hi hj hij)
        (heartClusterUnion_subset ω (Q i) (H i) hxi) (Finset.mem_inter.mp hx).2).elim
  · intro x hx
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨j,hj,hx⟩,heartClusterUnion_subset ω (Q j) (H j) hx⟩

/-- The literal finite global-union atom equals the family of individual-cube
atoms. Values outside the union of cubes are excluded explicitly. -/
theorem clusterFamilyUnion_event_eq_family {d : ℕ} (s : Finset J)
    (Q H : J → Finset (Vertex d)) (hQ : (s : Set J).PairwiseDisjoint Q)
    (F : Finset (Vertex d)) (hF : F ⊆ s.biUnion Q) :
    {ω : Configuration d | clusterFamilyUnion ω s Q H = F} =
      clusterFamilyRevealEvent s Q H (fun j => F ∩ Q j) := by
  ext ω
  change clusterFamilyUnion ω s Q H = F ↔
    ∀ j ∈ s, heartClusterUnion ω (Q j) (H j) = F ∩ Q j
  constructor
  · intro h j hj
    rw [← h,clusterFamilyUnion_inter_cube ω s Q H hQ j hj]
  · intro h
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hx
      rw [h j hj] at hxj
      exact (Finset.mem_inter.mp hxj).1
    · intro x hx
      obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp (hF hx)
      apply Finset.mem_biUnion.mpr
      refine ⟨j,hj,?_⟩
      rw [h j hj]
      exact Finset.mem_inter.mpr ⟨hx,hxj⟩

/-- The actual finite global reveal G is a cylinder on the incident bonds of
its recovered cube components, including the closed cluster boundary. -/
theorem clusterFamilyUnion_event_cylinder {d : ℕ} (s : Finset J)
    (Q H : J → Finset (Vertex d)) (hQ : (s : Set J).PairwiseDisjoint Q)
    (hH : ∀ j ∈ s, H j ⊆ Q j) (F : Finset (Vertex d)) (hF : F ⊆ s.biUnion Q) :
    {ω : Configuration d | clusterFamilyUnion ω s Q H = F} =
      (clusterFamilyRevealBonds s Q (fun j => F ∩ Q j)).restrict ⁻¹'
        clusterFamilyLocalEvent s Q H (fun j => F ∩ Q j) := by
  rw [clusterFamilyUnion_event_eq_family s Q H hQ F hF]
  exact clusterFamilyReveal_event_cylinder s Q H (fun j => F ∩ Q j) hH

end NearCritical.Section10
