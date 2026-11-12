module

public import NearCritical.SplitCrossConcreteBaseTube
public import NearCritical.SplitCrossMoatBudget

/-! Deletion losses on the actual tree, before the final choice of scale.
The same macroscopic distance controls remote moats and the face loss. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode Section10 Section8
open scoped Classical

theorem crossingTip_dist_center_le {d L : ℕ} (b : SplitTreeNode L → Vertex d)
    (v : SplitTreeNode L) (i : Fin d) (n : ℕ) :
    dist (crossingTip b v i n) (b v) ≤ (n : ℝ) := by
  by_cases hv : v ∈ crossingBranches L
  · simp [crossingTip, hv, dist_starTip_center]
  · simp [crossingTip, hv]

theorem crossingTips_dist_lower {d t n m : ℕ} (hd : 2 ≤ d) (ht : 4096 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    {u v : SplitTreeNode (4 * d)} (hne : u ≠ v) (i j : Fin d) :
    (spineRadius (4 * d - 1) t : ℝ) ≤
      (n : ℝ) + (m : ℝ) + dist (crossingTip b u i n) (crossingTip b v j m) := by
  have hsep := nodeSites_dist_of_ne hd ht hx axis hne (hb u) (hb v)
  have h₁ := dist_triangle (b u) (crossingTip b u i n) (b v)
  have h₂ := dist_triangle (crossingTip b u i n) (crossingTip b v j m) (b v)
  rw [dist_comm (b u) (crossingTip b u i n)] at h₁
  linarith [crossingTip_dist_center_le b u i n, crossingTip_dist_center_le b v j m]

private theorem crossingTip_dist_remote_center {d t n : ℕ} (hd : 2 ≤ d) (ht : 4096 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    {u v : SplitTreeNode (4 * d)} (hne : u ≠ v) (i : Fin d) :
    (spineRadius (4 * d - 1) t : ℝ) ≤
      (n : ℝ) + latticeDistance (crossingTip b u i n) (b v) := by
  rw [latticeDistance_eq_vertex_dist]
  have h₁ := dist_triangle (b u) (crossingTip b u i n) (b v)
  rw [dist_comm (b u) (crossingTip b u i n)] at h₁
  linarith [nodeSites_dist_of_ne hd ht hx axis hne (hb u) (hb v),
    crossingTip_dist_center_le b u i n]

def crossingMoatSize (d : ℕ) (hd : 3 ≤ d) (R : ℕ) : ℝ :=
  ((crossingBranches (4 * d)).card : ℝ) *
    ((((branchAxes hd).card * (R + 1) +
      (branchAxes hd).card * (2 * (1 - 1) + 1) ^ d) * (2 * d) : ℕ) : ℝ)

theorem crossingMoatSize_nonneg (d : ℕ) (hd : 3 ≤ d) (R : ℕ) :
    0 ≤ crossingMoatSize d hd R := by unfold crossingMoatSize; positivity

/-- Both a shifted branch tip and an unshifted root or terminal have small
total Green mass, with only the tip's own moat contributing the local term. -/
theorem concrete_moat_mass_at_tip {d t : ℕ} (hd : 4 ≤ d) (hd3 : 3 ≤ d) (ht : 4096 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (R ρ : ℕ) {s ε : ℝ} (hs : 1 ≤ s) (hε : 0 ≤ ε)
    (hgap : s + ((R + 1 + ρ : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) ≤
      (spineRadius (4 * d - 1) t : ℝ))
    (hown : ∀ a : Vertex d, ∀ i ∈ branchAxes hd3,
      (∑ z ∈ branchMoatVertices a (branchAxes hd3) R 1,
        moatGreen (starTip a i (R + 1 + ρ)) z) ≤ ε)
    (v : SplitTreeNode (4 * d)) (i : Fin d) (hi : i ∈ branchAxes hd3) :
    (∑ z ∈ treeMoatVertices (crossingBranches (4 * d)) b (branchAxes hd3) R 1,
      moatGreen (crossingTip b v i (R + 1 + ρ)) z) ≤ ε + crossingMoatSize d hd3 R / s^2 := by
  letI : DecidableEq (SplitTreeNode (4 * d)) := fun a b => Classical.propDecidable (a = b)
  let I := crossingBranches (4 * d)
  let u := crossingTip b v i (R + 1 + ρ)
  have hremote (w : SplitTreeNode (4 * d)) (hne : v ≠ w) :
      s + ((R + 1 + 1 : ℕ) : ℝ) ≤ latticeDistance u (b w) := by
    have h := crossingTip_dist_remote_center (n := R + 1 + ρ) (by omega) ht x hx axis b hb hne i
    change _ ≤ ((R + 1 + ρ : ℕ) : ℝ) + latticeDistance u (b w) at h
    linarith
  change (∑ z ∈ treeMoatVertices I b (branchAxes hd3) R 1, moatGreen u z) ≤ _
  by_cases hv : v ∈ I
  · have hv' : v ∈ crossingBranches (4 * d) := hv
    have hu : u = starTip (b v) i (R + 1 + ρ) := by simp [u, crossingTip, hv']
    have hmain := treeMoat_green_mass_le_at_outward hd I b (branchAxes hd3) R 1 ρ hv i hs
      (fun w hw => by rw [← hu]; exact hremote w (Finset.mem_erase.mp hw).1.symm)
    rw [hu]
    refine hmain.trans (add_le_add (hown (b v) i hi) ?_)
    unfold crossingMoatSize
    apply div_le_div_of_nonneg_right _ (sq_nonneg s)
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (Finset.erase_subset v I)) (by positivity)
  · have hmain := remoteMoats_green_mass_le hd I b (branchAxes hd3) R 1 u hs
      (fun w hw => hremote w (fun h => hv (by simpa only [h] using hw)))
    exact hmain.trans (le_add_of_nonneg_left hε)

theorem concrete_face_moat_separation {d t : ℕ} (hd : 3 ≤ d) (ht : 4096 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (R : ℕ) {s : ℝ} (hgap : s + ((R + 1 + 1 : ℕ) : ℝ) ≤
      (spineRadius (4 * d - 1) t : ℝ))
    (k : Fin (4 * d)) {z : Vertex d}
    (hz : z ∈ treeMoatVertices (crossingBranches (4 * d)) b (branchAxes hd) R 1) :
    s ≤ latticeDistance (b (face k)) z := by
  obtain ⟨v, hv, hz⟩ := Finset.mem_biUnion.mp hz
  have hv' := (mem_crossingBranches v).mp hv
  have hne : face k ≠ v := by
    intro h
    rw [← h] at hv'
    simp [isCrossingBranch] at hv'
  have hsep := nodeSites_dist_of_ne (by omega : 2 ≤ d) ht hx axis hne (hb (face k)) (hb v)
  have htri := dist_triangle (b (face k)) z (b v)
  rw [latticeDistance_eq_vertex_dist]
  linarith [moatVertex_dist_center_le hz (parentAxis hd)]

/-- The box of the face edge lies in the supporting half-space of the far
face, and the chosen terminal has depth zero there. -/
theorem farLegBox_supporting_halfSpace {d t : ℕ} (ht : 64 ≤ t) (f : Fin d × Bool) (pl : Bool)
    {y : Vertex d} (hy : y ∈ farLegFaceCore t f pl) :
    ∃ (i : Fin d) (cut : ℤ) (positive : Bool),
      (translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)) : Set (Vertex d)) ⊆
        coordinateHalfSpace i cut positive ∧ coordinateDepth i cut positive y = 0 := by
  let N : ℕ := (t - 1) / 2 + t
  have hyT := (Finset.mem_filter.mp (farLegFaceCore_subset_target ht f pl hy)).2
  have hEnv (z : Vertex d)
      (hz : z ∈ translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t))) :
      z ∈ centeredBox d N :=
    splitBeyond_subset_splitEnvelope t f pl (farLegBox_subset_beyond ht f pl hz)
  obtain ⟨i, pos⟩ := f
  cases pos
  · refine ⟨i, -(N : ℤ), true, ?_, ?_⟩
    · intro z hz
      have hl := (mem_centeredBox.mp (hEnv z hz) i).1
      change 0 ≤ coordinateDepth i (-(N : ℤ)) true z
      simp only [coordinateDepth, ite_true, Int.cast_neg, Int.cast_natCast]
      have hh : -((N : ℕ) : ℝ) ≤ (z i : ℝ) := by exact_mod_cast hl
      linarith
    · have hh : (y i : ℤ) = -(N : ℤ) := by
        simp [faceHeight] at hyT
        simp only [N, Nat.cast_add]
        omega
      simp [coordinateDepth, hh]
  · refine ⟨i, (N : ℤ), false, ?_, ?_⟩
    · intro z hz
      have hu := (mem_centeredBox.mp (hEnv z hz) i).2
      change 0 ≤ coordinateDepth i (N : ℤ) false z
      simp only [coordinateDepth, Bool.false_eq_true, ite_false, Int.cast_natCast]
      have hh : (z i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hu
      linarith
    · have hh : (y i : ℤ) = (N : ℤ) := by
        simpa [faceHeight, N, Nat.cast_add] using hyT
      simp [coordinateDepth, hh]

/-- A common bound on the BK loss, with the power appropriate to the
edge's terminal type. -/
theorem concrete_moat_loss_le {d t : ℕ} (hd : 7 ≤ d) (hd3 : 3 ≤ d) (ht : 4096 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (R ρ : ℕ) {s ε G C : ℝ} (hs : 1 ≤ s) (hε : 0 ≤ ε)
    (hgap : 2 * s + 2 * ((R + 1 + ρ : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) ≤
      (spineRadius (4 * d - 1) t : ℝ))
    (hown : ∀ a : Vertex d, ∀ i ∈ branchAxes hd3,
      (∑ z ∈ branchMoatVertices a (branchAxes hd3) R 1,
        moatGreen (starTip a i (R + 1 + ρ)) z) ≤ ε)
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper d C)
    (hL : 2 ≤ 4 * d) (v : SplitTreeNode (4 * d)) (hv : v ≠ root) (i j : Fin d)
    (hi : i ∈ branchAxes hd3) (hj : j ∈ branchAxes hd3)
    (T : Finset (Vertex d)) (hT : T ⊆ crossingEdgeRegion t v)
    (hy : crossingTip b v j (R + 1 + ρ) ∈ T) :
    moatDeletionLoss (criticalPoint d) T (treeMoatVertices (crossingBranches (4 * d)) b (branchAxes hd3) R 1)
        (crossingTip b (parent hL v) i (R + 1 + ρ)) (crossingTip b v j (R + 1 + ρ)) ≤
      (2 * G^2 + (2 * C) * G) * s ^ crossingEdgeExponent d v *
        (ε + crossingMoatSize d hd3 R / s^2) := by
  let n := R + 1 + ρ
  let F := treeMoatVertices (crossingBranches (4 * d)) b (branchAxes hd3) R 1
  let a := crossingTip b (parent hL v) i n
  let y := crossingTip b v j n
  let M := ε + crossingMoatSize d hd3 R / s^2
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hM : 0 ≤ M := add_nonneg hε (div_nonneg (crossingMoatSize_nonneg d hd3 R) (sq_nonneg s))
  have hs' : 0 < s := by linarith
  have hgap' : s + (n : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) ≤
      (spineRadius (4 * d - 1) t : ℝ) := by
    change 2 * s + 2 * (n : ℝ) + _ ≤ _ at hgap
    linarith
  have ha : (∑ z ∈ F, moatGreen a z) ≤ M :=
    concrete_moat_mass_at_tip (by omega) hd3 ht x hx axis b hb R ρ hs hε hgap' hown _ i hi
  have hy' : (∑ z ∈ F, moatGreen y z) ≤ M :=
    concrete_moat_mass_at_tip (by omega) hd3 ht x hx axis b hb R ρ hs hε hgap' hown _ j hj
  have hsep : 2 * s ≤ latticeDistance a y := by
    have h := crossingTips_dist_lower (n := n) (m := n) (by omega) ht x hx axis b hb
      (parent_adj hL v hv).ne i j
    change _ ≤ (n : ℝ) + (n : ℝ) + dist a y at h
    have hR : 0 ≤ ((R + 1 + 1 : ℕ) : ℝ) := by positivity
    rw [latticeDistance_eq_vertex_dist]
    change 2 * s + 2 * (n : ℝ) + _ ≤ _ at hgap
    linarith
  have hinterior :
      moatDeletionLoss (criticalPoint d) T F a y ≤
        (2 * G^2 + (2 * C) * G) * s ^ ((2 : ℝ) - (d : ℝ)) * M := by
    calc
      _ ≤ (G^2 * s ^ ((2 : ℝ) - (d : ℝ))) *
          ((∑ z ∈ F, moatGreen a z) + (∑ z ∈ F, moatGreen y z)) :=
        interior_moatDeletionLoss_le (by omega) hG green T F a y hs' hsep
      _ ≤ (G^2 * s ^ ((2 : ℝ) - (d : ℝ))) * (M + M) :=
        mul_le_mul_of_nonneg_left (add_le_add ha hy') (by positivity)
      _ = (2 * G^2) * s ^ ((2 : ℝ) - (d : ℝ)) * M := by ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (show 0 ≤ (2 * C) * G by positivity))
          (Real.rpow_nonneg hs'.le _)) hM
  cases v with
  | face k =>
    have hyEq : y = b (face k) := by simp [y, crossingTip, isCrossingBranch]
    have hyCore : y ∈ farLegFaceCore t (splitLegEquiv d k).1 (splitLegEquiv d k).2 := hyEq ▸ hb (face k)
    obtain ⟨l, cut, positive, hspace, hdepth⟩ := farLegBox_supporting_halfSpace (by omega) _ _ hyCore
    have hTh : (T : Set (Vertex d)) ⊆ coordinateHalfSpace l cut positive :=
      (Finset.coe_subset.mpr hT).trans hspace
    have hys (z : Vertex d) (hz : z ∈ F ∩ T) : s ≤ latticeDistance y z := by
      rw [hyEq]
      apply concrete_face_moat_separation hd3 ht x hx axis b hb R ?_ k (Finset.mem_inter.mp hz).1
      linarith
    change moatDeletionLoss (criticalPoint d) T F a y ≤
      (2 * G^2 + (2 * C) * G) * s ^ ((1 : ℝ) - (d : ℝ)) * M
    calc
      _ ≤ (((2 * C) * G) * s ^ ((1 : ℝ) - (d : ℝ))) * ∑ z ∈ F, moatGreen a z :=
        face_moatDeletionLoss_le (by omega) hG green hC panis T F a y l cut positive hTh hy hdepth hs' hys
      _ ≤ (((2 * C) * G) * s ^ ((1 : ℝ) - (d : ℝ))) * M :=
        mul_le_mul_of_nonneg_left ha (by positivity)
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (show 0 ≤ 2 * G^2 by positivity))
          (Real.rpow_nonneg hs'.le _)) hM
  | root | spine _ | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ =>
    exact hinterior

end NearCritical.SplitCrossDirect
