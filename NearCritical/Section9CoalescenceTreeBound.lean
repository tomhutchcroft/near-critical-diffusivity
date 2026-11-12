module

public import NearCritical.Section9CoalescenceProbability
public import NearCritical.Section9CoalescenceRightDiagram

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Fixed-pivot Case 3 bound with the joint right probability expanded
as a finite target sum of tree diagrams. -/
theorem section9_shared_right_tree_bound {d : ℕ} (tree : ThreePointTreeGraphInput d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e f : Vertex d × Vertex d) :
    let A := connectionToSetEvent (L : Set (Vertex d)) e.1 {x}
    let C := connectionToSetEvent (L : Set (Vertex d)) f.1 {y}
    (percolation d (criticalPoint d)).real {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
        sprinklingUnexploredCluster ω R Q₃ F₃ f.2} ≤
      (percolation d (criticalPoint d)).real A *
        ((percolation d (criticalPoint d)).real C *
          (∑ z ∈ B, ∑' u : Vertex d, twoPoint d (criticalPoint d) u e.2 *
            twoPoint d (criticalPoint d) u f.2 * twoPoint d (criticalPoint d) u z)) := by
  dsimp only
  refine (section9_shared_right_probability_le (criticalPoint d)
    L R Q₁ F₁ Q₃ F₃ B x y e f).trans ?_
  apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
  apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
  exact section9_joint_right_probability_le_tree_sum tree (R : Set (Vertex d)) B e.2 f.2

/-- Sum the fixed-pivot estimate over distinct candidate pairs. -/
theorem section9_shared_right_pivot_sum_le {d : ℕ} (tree : ThreePointTreeGraphInput d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (P : Finset (Vertex d × Vertex d)) :
    ∑ ef ∈ (P.product P).filter (fun ef => ef.1 ≠ ef.2),
      (percolation d (criticalPoint d)).real {ω |
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B ef.1 ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B ef.2 ∧
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ ef.1.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ ef.2.1) ∧
        sprinklingUnexploredCluster ω R Q₃ F₃ ef.1.2 =
          sprinklingUnexploredCluster ω R Q₃ F₃ ef.2.2} ≤
    ∑ ef ∈ (P.product P).filter (fun ef => ef.1 ≠ ef.2),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (L : Set (Vertex d)) ef.1.1 {x}) *
      ((percolation d (criticalPoint d)).real
        (connectionToSetEvent (L : Set (Vertex d)) ef.2.1 {y}) *
        (∑ z ∈ B, ∑' u : Vertex d, twoPoint d (criticalPoint d) u ef.1.2 *
          twoPoint d (criticalPoint d) u ef.2.2 * twoPoint d (criticalPoint d) u z)) := by
  exact Finset.sum_le_sum fun ef _ =>
    section9_shared_right_tree_bound tree L R Q₁ F₁ Q₃ F₃ B x y ef.1 ef.2

end NearCritical
