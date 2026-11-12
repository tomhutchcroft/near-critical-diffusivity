module

public import NearCritical.SplitCrossConcreteOutside
public import NearCritical.SplitCrossCubeEdges
public import NearCritical.SplitCrossExteriorDummy

/-! The four lattice connection estimates applied at the shifted endpoints
of the concrete tree. The two translated rectangles can depend on the
shifted start, while their enclosing edge regions are fixed. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode Section10 Section8 MeasureTheory
open scoped Classical

def crossingEdgeExponent {L : ℕ} (d : ℕ) : SplitTreeNode L → ℝ
  | face _ => 1 - (d : ℝ)
  | _ => 2 - (d : ℝ)

private theorem spine_tip_mem_inner {d t n : ℕ} (ht : 64 ≤ t)
    (hscale : 512 * (4 * d - 1 + 1) * n ≤ t)
    (x : Vertex d) (axis i : Fin d) (b : SplitTreeNode (4 * d) → Vertex d)
    (k : Fin (4 * d - 1)) (hb : b (spine k) ∈ nodeSites t x axis (spine k)) :
    crossingTip b (spine k) i n ∈ centeredBox d (7 * t / 16) := by
  have h := spineBox_subset_inner_cube ht axis k
    (spineBranchCore_add_mem hscale hb (coordinateRay_mem_centeredBox i (le_refl n)))
  simp only [crossingTip, mem_crossingBranches, isCrossingBranch, ite_true]
  apply mem_centeredBox.mpr
  intro j
  have hj := mem_centeredBox.mp h j
  change -((7 * t / 16 : ℕ) : ℤ) ≤ starTip (b (spine k)) i n j ∧
    starTip (b (spine k)) i n j ≤ ((7 * t / 16 : ℕ) : ℤ)
  change -((t / 8 : ℕ) : ℤ) ≤ starTip (b (spine k)) i n j ∧
    starTip (b (spine k)) i n j ≤ ((t / 8 : ℕ) : ℤ) at hj
  omega

private theorem entry_tip_mem_branch {d t n : ℕ} (hscale : 2048 * n ≤ t)
    (x : Vertex d) (axis i : Fin d) (b : SplitTreeNode (4 * d) → Vertex d)
    (k : Fin (4 * d)) (hb : b (entry k) ∈ nodeSites t x axis (entry k)) :
    crossingTip b (entry k) i n ∈ legBranchBox t (splitLegEquiv d k).1 (splitLegEquiv d k).2 true := by
  simpa only [crossingTip, mem_crossingBranches, isCrossingBranch, ite_true, starTip] using
    (legBranchCore_add_mem hscale hb (coordinateRay_mem_centeredBox i (le_refl n)))

private theorem exterior_tip_mem_branch {d t n : ℕ} (hscale : 2048 * n ≤ t)
    (x : Vertex d) (axis i : Fin d) (b : SplitTreeNode (4 * d) → Vertex d)
    (k : Fin (4 * d)) (hb : b (exterior k) ∈ nodeSites t x axis (exterior k)) :
    crossingTip b (exterior k) i n ∈ legBranchBox t (splitLegEquiv d k).1 (splitLegEquiv d k).2 false := by
  simpa only [crossingTip, mem_crossingBranches, isCrossingBranch, ite_true, starTip] using
    (legBranchCore_add_mem hscale hb (coordinateRay_mem_centeredBox i (le_refl n)))

private theorem face_scale_eq {d t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t) (b : ℝ) :
    b * (t : ℝ) ^ ((1 : ℝ) - (d : ℝ)) = b / (t : ℝ) ^ (d - 1) := by
  have h : (1 : ℝ) - (d : ℝ) = -(((d - 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [h, Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]

/-- A positive uniform base probability in the appropriate finite edge tube. -/
theorem concrete_crossing_base_tubes {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {A B C c K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (t : ℕ), 4096 ≤ t → ∀ (x : Vertex d), x ∈ centeredBox d ((t - 1) / 32) →
      ∀ (axis : Fin d) (b : SplitTreeNode (4 * d) → Vertex d), (∀ v, b v ∈ nodeSites t x axis v) →
      ∀ n : ℕ, 512 * (4 * d - 1 + 1) * n ≤ t → 2048 * n ≤ t →
      ∀ (hL : 2 ≤ 4 * d) (v : SplitTreeNode (4 * d)), v ≠ root → ∀ (i j : Fin d),
      let u := crossingTip b (parent hL v) i n
      let w := crossingTip b v j n
      ∃ T : Finset (Vertex d), T ⊆ crossingEdgeRegion t v ∧ u ∈ T ∧ w ∈ T ∧
        a * (t : ℝ) ^ (crossingEdgeExponent d v) ≤
          (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) u {w}) := by
  obtain ⟨aC, haC, hCube⟩ := splitCross_cube_connection_lower (by omega : 2 ≤ d) lower
  obtain ⟨aN, haN, hNeck⟩ := legNeck_connection_lower (by omega : 2 ≤ d) lower
  obtain ⟨aD, haD, hDummy⟩ := exteriorDummy_connection_lower (by omega : 2 ≤ d) lower
  obtain ⟨aF, haF, hFace⟩ := farLegFaceCore_connection_lower hd asymp lower hA hB hC hc hK
    arm second panis hslab hpioneer
  let γ : ℝ := (2 : ℝ) - (d : ℝ)
  let a := min aC (min (aN * (2 : ℝ) ^ γ) (min (aD * (2 : ℝ) ^ γ) aF))
  have hN : 0 < aN * (2 : ℝ) ^ γ := mul_pos haN (by positivity)
  have hD : 0 < aD * (2 : ℝ) ^ γ := mul_pos haD (by positivity)
  have ha : 0 < a := lt_min haC (lt_min hN (lt_min hD haF))
  have haC' : a ≤ aC := min_le_left _ _
  have haN' : a ≤ aN * (2 : ℝ) ^ γ := (min_le_right _ _).trans (min_le_left _ _)
  have haD' : a ≤ aD * (2 : ℝ) ^ γ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have haF' : a ≤ aF := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a, ha, ?_⟩
  intro t ht x hx axis b hb n hts htl hL v hv i j
  have hp (e : ℝ) : 0 < (t : ℝ) ^ e := Real.rpow_pos_of_pos (by positivity) _
  have base (S : Set (Vertex d)) (u w : Vertex d) (hS : S ⊆ (crossingEdgeRegion t v : Set (Vertex d)))
      (hl : a * (t : ℝ) ^ crossingEdgeExponent d v ≤
        (percolation d (criticalPoint d)).real (connectionToSetEvent S u {w})) :
      ∃ T : Finset (Vertex d), T ⊆ crossingEdgeRegion t v ∧ u ∈ T ∧ w ∈ T ∧
        a * (t : ℝ) ^ crossingEdgeExponent d v ≤
          (percolation d (criticalPoint d)).real (connectionToSetEvent (T : Set (Vertex d)) u {w}) := by
    let T := (crossingEdgeRegion t v).filter fun z => z ∈ S
    have hT : (T : Set (Vertex d)) = S := by
      ext z
      exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨hS h, h⟩⟩
    have hpos : 0 < (percolation d (criticalPoint d)).real (connectionToSetEvent S u {w}) :=
      (mul_pos ha (hp _)).trans_le hl
    have hne : (connectionToSetEvent S u {w}).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h, measureReal_empty] at hpos
      exact (lt_irrefl _) hpos
    obtain ⟨ω, hu, z, hz, hw, _⟩ := hne
    have hz' : z = w := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨T, Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · change u ∈ (T : Set (Vertex d))
      rw [hT]
      exact hu
    · change w ∈ (T : Set (Vertex d))
      rw [hT]
      exact hw
    · rw [hT]
      exact hl
  have hroot (l : Fin d) : crossingTip b root l n ∈ centeredBox d (7 * t / 16) := by
    have hbx : b root = x := Finset.mem_singleton.mp (hb root)
    simpa only [crossingTip, mem_crossingBranches, isCrossingBranch, Bool.false_eq_true, ite_false, hbx]
      using root_mem_innerCube hx
  have hsp (k : Fin (4 * d - 1)) (l : Fin d) :
      crossingTip b (spine k) l n ∈ centeredBox d (7 * t / 16) :=
    spine_tip_mem_inner (by omega) hts x axis l b k (hb _)
  have he (k : Fin (4 * d)) (l : Fin d) :
      crossingTip b (entry k) l n ∈ centeredBox d (7 * t / 16) :=
    entryLegBox_subset_inner_cube (by omega) _ _ true
      (legBranchBox_inside_subset_entry _ _ (entry_tip_mem_branch htl x axis l b k (hb _)))
  have hCube' (u w : Vertex d) (hu : u ∈ centeredBox d (7 * t / 16))
      (hw : w ∈ centeredBox d (7 * t / 16)) :
      a * (t : ℝ) ^ γ ≤ (percolation d (criticalPoint d)).real
        (connectionToSetEvent (typicalCube t (0 : Vertex d) : Set (Vertex d)) u {w}) :=
    (mul_le_mul_of_nonneg_right haC' (hp _).le).trans (hCube t (by omega) u w hu hw)
  cases v with
  | root => exact (hv rfl).elim
  | spine k =>
    apply base (typicalCube t (0 : Vertex d) : Set (Vertex d)) _ _ subset_rfl
    apply hCube' _ _ _ (hsp k j)
    by_cases hk : k.val = 0
    · simpa only [parent, dite_eq_left hk] using hroot i
    · simpa only [parent, dite_eq_right hk] using
        hsp (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin (4 * d - 1)) i
  | entry k =>
    apply base (typicalCube t (0 : Vertex d) : Set (Vertex d)) _ _ subset_rfl
    exact hCube' _ _ (hsp _ i) (he k j)
  | cubeDummy k =>
    apply base (typicalCube t (0 : Vertex d) : Set (Vertex d)) _ _ subset_rfl
    apply hCube' _ _ (he k i)
    simpa only [crossingTip, mem_crossingBranches, isCrossingBranch, Bool.false_eq_true, ite_false]
      using entryLegBox_subset_inner_cube (by omega) (splitLegEquiv d k).1
        (splitLegEquiv d k).2 false (hb (cubeDummy k))
  | exterior k =>
    let u := crossingTip b (entry k) i n
    let w := crossingTip b (exterior k) j n
    have hu := entry_tip_mem_branch htl x axis i b k (hb _)
    have hw := exterior_tip_mem_branch htl x axis j b k (hb _)
    apply base (legNeckRectangle t (splitLegEquiv d k).1 u) u w
      (legNeckRectangle_subset_corridor ht _ _ hu)
    have hl := hNeck t ht (splitLegEquiv d k).1 (splitLegEquiv d k).2 u w hu hw
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity), ← mul_assoc] at hl
    exact (mul_le_mul_of_nonneg_right haN' (hp _).le).trans hl
  | exteriorDummy k =>
    let u := crossingTip b (exterior k) i n
    let w := b (exteriorDummy k)
    have hu := exterior_tip_mem_branch htl x axis i b k (hb _)
    have hw := hb (exteriorDummy k)
    have htip : crossingTip b (exteriorDummy k) j n = w := by simp [crossingTip, isCrossingBranch, w]
    rw [htip]
    apply base (exteriorDummyRectangle t (splitLegEquiv d k).1 u) u w
      (exteriorDummyRectangle_subset_beyond ht _ _ hu)
    have hl := hDummy t ht (splitLegEquiv d k).1 (splitLegEquiv d k).2 u w hu hw
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity), ← mul_assoc] at hl
    exact (mul_le_mul_of_nonneg_right haD' (hp _).le).trans hl
  | face k =>
    let u := crossingTip b (exterior k) i n
    let w := b (face k)
    have htip : crossingTip b (face k) j n = w := by simp [crossingTip, isCrossingBranch, w]
    rw [htip]
    apply base (crossingEdgeRegion t (face k) : Set (Vertex d)) u w subset_rfl
    have hu := legBranchBox_exterior_subset_halfBox (splitLegEquiv d k).1 (splitLegEquiv d k).2
      (exterior_tip_mem_branch htl x axis i b k (hb _))
    have hl := hFace t (by omega) (splitLegEquiv d k).1 (splitLegEquiv d k).2 u w hu (hb (face k))
    change a * (t : ℝ) ^ ((1 : ℝ) - (d : ℝ)) ≤ _
    exact (mul_le_mul_of_nonneg_right haF' (hp _).le).trans
      ((face_scale_eq (by omega) (by omega) aF).le.trans hl)

end NearCritical.SplitCrossDirect
