module

public import NearCritical.Section9Pivotal

/-! Actual full deleted-graph components partition the tube. These are
structural facts for the two-pivot variance cases, not covariance estimates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

lemma sprinklingUnexploredCluster_eq_of_reachable {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) {x y : Vertex d}
    (hxy : (sprinklingUnexploredGraph ω T Q F).Reachable x y) :
    sprinklingUnexploredCluster ω T Q F x = sprinklingUnexploredCluster ω T Q F y := by
  ext z
  rw [mem_sprinklingUnexploredCluster, mem_sprinklingUnexploredCluster]
  constructor
  · rintro ⟨hz,hr⟩
    exact ⟨hz,hxy.symm.trans hr⟩
  · rintro ⟨hz,hr⟩
    exact ⟨hz,hxy.trans hr⟩

lemma sprinklingUnexploredCluster_eq_of_inter_nonempty {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (x y : Vertex d)
    (h : (sprinklingUnexploredCluster ω T Q F x ∩
      sprinklingUnexploredCluster ω T Q F y).Nonempty) :
    sprinklingUnexploredCluster ω T Q F x = sprinklingUnexploredCluster ω T Q F y := by
  obtain ⟨z,hz⟩ := h
  obtain ⟨hxz,hyz⟩ := Finset.mem_inter.mp hz
  have hrx := ((mem_sprinklingUnexploredCluster ω T Q F x z).mp hxz).2
  have hry := ((mem_sprinklingUnexploredCluster ω T Q F y z).mp hyz).2
  exact sprinklingUnexploredCluster_eq_of_reachable ω T Q F (hrx.trans hry.symm)

/-- Domain guards are retained in the direction that tests root membership.
Outside-domain reflexive roots cannot falsely create a nonempty component. -/
theorem sprinklingUnexploredCluster_disjoint_iff_not_reachable {d : ℕ}
    (ω : Configuration d) (T Q F : Finset (Vertex d)) (x y : Vertex d) (hy : y ∈ T) :
    Disjoint (sprinklingUnexploredCluster ω T Q F x)
      (sprinklingUnexploredCluster ω T Q F y) ↔
        ¬ (sprinklingUnexploredGraph ω T Q F).Reachable x y := by
  constructor
  · intro hdis hr
    exact Finset.disjoint_left.mp hdis
      ((mem_sprinklingUnexploredCluster ω T Q F x y).mpr ⟨hy,hr⟩)
      (root_mem_sprinklingUnexploredCluster ω T Q F hy)
  · intro hn
    apply Finset.disjoint_left.mpr
    intro z hxz hyz
    exact hn (((mem_sprinklingUnexploredCluster ω T Q F x z).mp hxz).2.trans
      ((mem_sprinklingUnexploredCluster ω T Q F y z).mp hyz).2.symm)

/-- Every pair of actual full side components is identical or disjoint,
without any independent-cluster or increasing-event assumption. -/
theorem sprinklingUnexploredCluster_eq_or_disjoint {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (x y : Vertex d) :
    sprinklingUnexploredCluster ω T Q F x = sprinklingUnexploredCluster ω T Q F y ∨
      Disjoint (sprinklingUnexploredCluster ω T Q F x)
        (sprinklingUnexploredCluster ω T Q F y) := by
  by_cases heq : sprinklingUnexploredCluster ω T Q F x = sprinklingUnexploredCluster ω T Q F y
  · exact Or.inl heq
  · apply Or.inr
    apply Finset.disjoint_left.mpr
    intro z hx hy
    exact heq (sprinklingUnexploredCluster_eq_of_inter_nonempty ω T Q F x y
      ⟨z,Finset.mem_inter.mpr ⟨hx,hy⟩⟩)

end NearCritical
