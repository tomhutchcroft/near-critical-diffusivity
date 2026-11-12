module

public import NearCritical.ConnectionToSet
public import NearCritical.ThreePointDiagram

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Bound the joint right connection by a sum of three-terminal diagrams,
one for each possible target. Repeated terminals are allowed. -/
theorem section9_joint_right_probability_le_tree_sum {d : ℕ}
    (tree : ThreePointTreeGraphInput d) (R : Set (Vertex d))
    (B : Finset (Vertex d)) (a b : Vertex d) :
    (percolation d (criticalPoint d)).real
        (connectionToSetEvent R a {b} ∩ connectionToSetEvent R a (B : Set (Vertex d))) ≤
      ∑ z ∈ B, ∑' u : Vertex d, twoPoint d (criticalPoint d) u a *
        twoPoint d (criticalPoint d) u b * twoPoint d (criticalPoint d) u z := by
  let E := fun z : Vertex d => connectionEvent a b ∩ connectionEvent a z
  have hsub : connectionToSetEvent R a {b} ∩ connectionToSetEvent R a (B : Set (Vertex d)) ⊆
      ⋃ z ∈ B, E z := by
    rintro ω ⟨⟨_, v, hv, _, hab⟩, ⟨_, z, hz, _, haz⟩⟩
    have hvb : v = b := hv
    subst v
    have hle : restrictedGraph ω R ≤ openGraph ω := fun _ _ h => h.1
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hab.mono hle, haz.mono hle⟩⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le B E).trans
    (Finset.sum_le_sum fun z _ => tree a b z))

end NearCritical
