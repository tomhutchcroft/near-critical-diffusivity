module

public import NearCritical.ThreePointTreeGraphDerivation
public import NearCritical.Section9CoalescenceTreeBound
public import NearCritical.Section9CoalescenceRightDiagram
public import NearCritical.Section9CoalescenceCaseTwoSum
public import NearCritical.Section9CrossSeparated

/-! # Tree-graph consumers, with the tree input discharged

Every theorem in the project that took `ThreePointTreeGraphInput d` as a
hypothesis now has an `_of_bubble` companion here that supplies it from the
already-assumed spatial bubble input via `threePointTreeGraphInput_of_bubble`.
These are additive corollaries: no existing statement or file is changed, so no
downstream proof is disturbed.  They record that the BK
tree-graph bound need no longer be carried as a separate input anywhere
downstream — the Section 9 coalescence / cross-separated estimates and the
three-point upper bound all follow from the bubble (and, where present, (A))
inputs they already assume. -/

@[expose] public section
noncomputable section
namespace NearCritical

open MeasureTheory
open scoped Classical BigOperators

/-- `lem.threepoint_upper`, tree hypothesis eliminated (from (A)+bubble). -/
theorem threePoint_probability_upper_of_asymptotics_and_bubble {d : ℕ}
    (hd : 4 < d) (h : TwoPointAsymptotics d) {B : ℝ} (hB : 0 < B)
    (bubble : CriticalSpatialBubbleInput d B) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y z : Vertex d, x ≠ y → y ≠ z → x ≠ z →
      (percolation d (criticalPoint d)).real (connectionEvent x y ∩ connectionEvent x z) ≤
        C * tripleMinSeparation x y z ^ ((4 : ℝ) - (d : ℝ)) *
          tripleMaxSeparation x y z ^ ((2 : ℝ) - (d : ℝ)) :=
  threePoint_probability_upper_of_asymptotics_and_standard_inputs hd h hB bubble
    (threePointTreeGraphInput_of_bubble bubble)

/-- Joint right connection as a tree sum, tree hypothesis supplied from bubble. -/
theorem section9_joint_right_probability_le_tree_sum_of_bubble {d : ℕ} {B' : ℝ}
    (bubble : CriticalSpatialBubbleInput d B') (R : Set (Vertex d))
    (B : Finset (Vertex d)) (a b : Vertex d) :
    (percolation d (criticalPoint d)).real
        (connectionToSetEvent R a {b} ∩ connectionToSetEvent R a (B : Set (Vertex d))) ≤
      ∑ z ∈ B, ∑' u : Vertex d, twoPoint d (criticalPoint d) u a *
        twoPoint d (criticalPoint d) u b * twoPoint d (criticalPoint d) u z :=
  section9_joint_right_probability_le_tree_sum (threePointTreeGraphInput_of_bubble bubble) R B a b

/-- Fixed-pivot Case 3 bound, tree hypothesis supplied from bubble. -/
theorem section9_shared_right_tree_bound_of_bubble {d : ℕ} {B' : ℝ}
    (bubble : CriticalSpatialBubbleInput d B')
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
            twoPoint d (criticalPoint d) u f.2 * twoPoint d (criticalPoint d) u z)) :=
  section9_shared_right_tree_bound (threePointTreeGraphInput_of_bubble bubble)
    L R Q₁ F₁ Q₃ F₃ B x y e f

/-- Distinct-pair sum of the fixed-pivot estimate, tree hypothesis from bubble. -/
theorem section9_shared_right_pivot_sum_le_of_bubble {d : ℕ} {B' : ℝ}
    (bubble : CriticalSpatialBubbleInput d B')
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
          twoPoint d (criticalPoint d) u ef.2.2 * twoPoint d (criticalPoint d) u z)) :=
  section9_shared_right_pivot_sum_le (threePointTreeGraphInput_of_bubble bubble)
    L R Q₁ F₁ Q₃ F₃ B x y P

/-- Separated three-point estimate, tree hypothesis eliminated (bubble only). -/
theorem section9_separated_three_point_le_of_bubble {d : ℕ} (hd : 4 < d)
    (asymptotics : TwoPointAsymptotics d) {B : ℝ} (hB : 0 < B)
    (bubble : CriticalSpatialBubbleInput d B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Set (Vertex d)) (a b z : Vertex d) (r : ℝ), 0 < r →
      r ≤ latticeDistance a b → r ≤ latticeDistance b z → r ≤ latticeDistance a z →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {z}) ≤
          C * r ^ (6 - 2 * (d : ℝ)) :=
  section9_separated_three_point_le hd asymptotics hB bubble
    (threePointTreeGraphInput_of_bubble bubble)

/-- Case 2 joint-arm bound, tree hypothesis eliminated (bubble only). -/
theorem section9_cross_joint_arm_le_of_bubble {d : ℕ} (hd : 4 < d)
    (asymptotics : TwoPointAsymptotics d) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (bubble : CriticalSpatialBubbleInput d B₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (D : Set (Vertex d)) (B : Finset (Vertex d)) (a b : Vertex d),
      a ∈ section9FiniteMiddle i n → b ∈ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent D a {b} ∩ connectionToSetEvent D a (B : Set (Vertex d))) ≤
          (B.card : ℝ) * (C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ))) :=
  section9_cross_joint_arm_le hd asymptotics hB₀ bubble
    (threePointTreeGraphInput_of_bubble bubble)

/-- Case 2 critical sum, tree hypothesis eliminated (bubble only). -/
theorem section9_case_two_critical_sum_le_of_bubble {d : ℕ} (hd : 4 < d)
    (asymptotics : TwoPointAsymptotics d) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (bubble : CriticalSpatialBubbleInput d B₀) :
    ∃ C G : ℝ, 0 < C ∧ 0 < G ∧
      ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d),
      x ∈ section9FiniteEndCube i n 0 → y ∈ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let P := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ P, (percolation d (criticalPoint d)).real {ω |
        ∃ f : Vertex d × Vertex d,
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
          Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
            (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
          (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
            sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty}) ≤
        ((2 * (d : ℝ)) * (G * (1 + (2 * (d : ℝ) * 3^(d-1)) * ((6*n : ℕ)+1 : ℝ)^2))) *
          ((B.card : ℝ) * (C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ)))) :=
  section9_case_two_critical_sum_le hd asymptotics hB₀ bubble
    (threePointTreeGraphInput_of_bubble bubble)

end NearCritical
