module

public import NearCritical.SplitCrossConcreteDeletion
public import NearCritical.SplitCrossOutsideEdge
public import NearCritical.CriticalPointInterior

/-! Attach the outward rays after moat deletion and enlarge to the fixed
edge region of the concrete layout. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode Section10 Section8 MeasureTheory
open scoped Classical

private theorem crossingTip_mem_region_of_offset {d t n k : ℕ}
    (x : Vertex d) (axis : Fin d) (b : SplitTreeNode (4 * d) → Vertex d)
    (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (hts : 512 * (4 * d - 1 + 1) * n ≤ t) (htl : 2048 * n ≤ t)
    (v : SplitTreeNode (4 * d)) (i : Fin d) (hk : k ≤ n)
    (D : Finset (Vertex d)) (hbranch : crossingBranchBox t axis v ⊆ D)
    (hother : v ∉ crossingBranches (4 * d) → b v ∈ D) :
    crossingTip b v i k ∈ D := by
  by_cases hv : v ∈ crossingBranches (4 * d)
  · rw [crossingTip, ite_eq_left hv]
    exact hbranch (branchBox_offset_subset hts htl x axis v hv (hb v) (starTip_mem_box _ _ hk))
  · rw [crossingTip, ite_eq_right hv]
    exact hother hv

private theorem nonbranch_site_mem_incoming_region {d t : ℕ} (ht : 64 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (v : SplitTreeNode (4 * d)) (hv : v ∉ crossingBranches (4 * d)) :
    b v ∈ crossingEdgeRegion t v := by
  cases v with
  | root =>
    have hbx : b root = x := Finset.mem_singleton.mp (hb root)
    rw [hbx]
    exact root_mem_typicalCube (by omega) hx
  | cubeDummy k => exact entryLegBox_subset_cube ht _ _ false (hb (cubeDummy k))
  | exteriorDummy k => exact interiorLegBox_subset_beyond ht _ _ (hb (exteriorDummy k))
  | face k => exact farLegFaceCore_subset_farBox t _ _ (hb (face k))
  | spine _ | entry _ | exterior _ => simp [isCrossingBranch] at hv

private theorem parent_eq_root_of_nonbranch {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L)
    (h : parent hL v ∉ crossingBranches L) : parent hL v = root := by
  cases v with
  | root => rfl
  | spine k =>
    by_cases hk : k.val = 0
    · simp [parent, hk]
    · simp [parent, hk, isCrossingBranch] at h
  | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ | face _ =>
    simp [parent, isCrossingBranch] at h

private theorem nonbranch_parent_mem_outgoing_region {d t : ℕ} (ht : 64 ≤ t)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (hL : 2 ≤ 4 * d) (v : SplitTreeNode (4 * d)) (hv : parent hL v ∉ crossingBranches (4 * d)) :
    b (parent hL v) ∈ crossingEdgeRegion t v := by
  have h := parent_eq_root_of_nonbranch hL v hv
  have hb0 : b root = x := Finset.mem_singleton.mp (hb root)
  rw [h, hb0]
  cases v with
  | root | spine _ | entry _ | cubeDummy _ => exact root_mem_typicalCube (by omega) hx
  | exterior _ | exteriorDummy _ | face _ => simp [parent] at h

private def crossingOutwardLen {L : ℕ} (v : SplitTreeNode L) (ρ : ℕ) : ℕ :=
  if v ∈ crossingBranches L then ρ else 0

private theorem crossingOutwardLen_le {L : ℕ} (v : SplitTreeNode L) (ρ : ℕ) :
    crossingOutwardLen v ρ ≤ ρ := by unfold crossingOutwardLen; split <;> omega

private theorem crossingTip_ray_step {d L : ℕ} (b : SplitTreeNode L → Vertex d)
    (v : SplitTreeNode L) (i : Fin d) (R ρ k : ℕ) (hk : k ≤ crossingOutwardLen v ρ) :
    starTip (crossingTip b v i (R + 1)) i k = crossingTip b v i (R + 1 + k) := by
  by_cases hv : v ∈ crossingBranches L
  · simp [crossingTip, hv, ← starTip_add]
  · have hk0 : k = 0 := by simpa [crossingOutwardLen, hv] using hk
    subst k
    simp only [crossingTip, hv, ite_false]
    rw [← rayPt_eq_starTip]
    rfl

private theorem crossingTip_ray_last {d L : ℕ} (b : SplitTreeNode L → Vertex d)
    (v : SplitTreeNode L) (i : Fin d) (R ρ : ℕ) :
    starTip (crossingTip b v i (R + 1)) i (crossingOutwardLen v ρ) =
      crossingTip b v i (R + 1 + ρ) := by
  rw [crossingTip_ray_step b v i R ρ _ le_rfl]
  by_cases hv : v ∈ crossingBranches L <;> simp [crossingTip, crossingOutwardLen, hv]

/-- The per-edge estimate in the fixed tube with the common moat removed.
The constant and outward length are uniform in every larger star length. -/
theorem concrete_crossing_fixed_tubes_lower {d : ℕ} (hd : 7 ≤ d) (hd3 : 3 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {A B C c K G : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K)
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    ∃ ρ : ℕ, 0 < ρ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ R₀ : ℕ, ∀ R ≥ R₀, ∃ t₀ : ℕ, ∀ t ≥ t₀,
      4096 ≤ t ∧ 512 * (4 * d - 1 + 1) * (R + 1 + ρ) ≤ t ∧ 2048 * (R + 1 + ρ) ≤ t ∧
      ((R + 1 + ρ : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ) ∧
      ∀ (x : Vertex d), x ∈ centeredBox d ((t - 1) / 32) →
      ∀ (axis : Fin d) (b : SplitTreeNode (4 * d) → Vertex d), (∀ v, b v ∈ nodeSites t x axis v) →
      ∀ (hL : 2 ≤ 4 * d) (v : SplitTreeNode (4 * d)), v ≠ root →
      ∀ i ∈ branchAxes hd3, ∀ j ∈ branchAxes hd3,
      a₀ * (t : ℝ) ^ crossingEdgeExponent d v ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent
            ((crossingEdgeRegion t v : Set (Vertex d)) ∩ (crossingOutside hd3 t b R 1 : Set (Vertex d)))
            (crossingTip b (parent hL v) i (R + 1)) {crossingTip b v j (R + 1)}) := by
  obtain ⟨a, ha, hbase⟩ := concrete_crossing_base_tubes hd asymp lower hA hB hC hc hK
    arm second panis hslab hpioneer
  obtain ⟨ρ, hρ, R₀, hscale⟩ :=
    concrete_moat_loss_eventually_small hd hd3 hG green hC panis a ha
  let p := criticalPoint d
  let a₀ := (p : ℝ) ^ (2 * ρ) * (a / 2)
  have hp : 0 < (p : ℝ) := criticalPoint_pos_of_twoPointAsymptotics (parentAxis hd3) asymp
  refine ⟨ρ, hρ, a₀, by dsimp [a₀]; positivity, R₀, ?_⟩
  intro R hR
  obtain ⟨t₀, ht₀⟩ := hscale R hR
  refine ⟨t₀, ?_⟩
  intro t ht
  obtain ⟨ht4096, hts, htl, hgap, hloss⟩ := ht₀ t ht
  refine ⟨ht4096, hts, htl, hgap, ?_⟩
  intro x hx axis b hb hL v hv i hi j hj
  let u := parent hL v
  let n := crossingOutwardLen u ρ
  let m := crossingOutwardLen v ρ
  let S := crossingEdgeRegion t v
  let F := treeMoatVertices (crossingBranches (4 * d)) b (branchAxes hd3) R 1
  let a' := crossingTip b u i (R + 1)
  let b' := crossingTip b v j (R + 1)
  let e := crossingEdgeExponent d v
  have h64 : 64 ≤ t := by omega
  have hS (w : SplitTreeNode (4 * d)) (l : Fin d) (k : ℕ) (hk : k ≤ ρ)
      (hbranch : crossingBranchBox t axis w ⊆ S)
      (hother : w ∉ crossingBranches (4 * d) → b w ∈ S) :
      crossingTip b w l (R + 1 + k) ∈ S \ F := by
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact crossingTip_mem_region_of_offset x axis b hb hts htl w l (by omega) S hbranch hother
    · exact (Finset.mem_sdiff.mp
        (crossingTip_mem_outside ht4096 hd3 x hx axis R ρ hts htl hgap b hb w l k hk)).2
  have ha' (k : ℕ) (hk : k ≤ n) : starTip a' i k ∈ S \ F := by
    rw [crossingTip_ray_step b u i R ρ k hk]
    exact hS u i k (hk.trans (crossingOutwardLen_le u ρ))
      (branchBox_subset_outgoing_region h64 hL axis v)
      (nonbranch_parent_mem_outgoing_region h64 x hx axis b hb hL v)
  have hb' (k : ℕ) (hk : k ≤ m) : starTip b' j k ∈ S \ F := by
    rw [crossingTip_ray_step b v j R ρ k hk]
    exact hS v j k (hk.trans (crossingOutwardLen_le v ρ))
      (branchBox_subset_incoming_region h64 axis v)
      (nonbranch_site_mem_incoming_region h64 x hx axis b hb v)
  obtain ⟨T, hTS, huT, hvT, hprob⟩ :=
    hbase t ht4096 x hx axis b hb (R + 1 + ρ) hts htl hL v hv i j
  have hcost := hloss x hx axis b hb hL v hv i hi j hj T hTS hvT
  have hu_eq : starTip a' i n = crossingTip b u i (R + 1 + ρ) := crossingTip_ray_last b u i R ρ
  have hv_eq : starTip b' j m = crossingTip b v j (R + 1 + ρ) := crossingTip_ray_last b v j R ρ
  have hc' : (a / 2) * (t : ℝ) ^ e +
      moatDeletionLoss p T F (starTip a' i n) (starTip b' j m) ≤
      (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) (starTip a' i n) {starTip b' j m}) := by
    rw [hu_eq, hv_eq]
    linarith
  obtain ⟨D, hD, _, _, hbound⟩ := outside_tube_connection_lower p S T F hTS a' b' i j n m
    ha' hb' (hu_eq.symm ▸ huT) (hv_eq.symm ▸ hvT) ((a / 2) * (t : ℝ) ^ e) hc'
  have hD' : (D : Set (Vertex d)) ⊆
      (crossingEdgeRegion t v : Set (Vertex d)) ∩ (crossingOutside hd3 t b R 1 : Set (Vertex d)) := by
    intro z hz
    obtain ⟨hzS, hzF⟩ := Finset.mem_sdiff.mp (hD hz)
    exact ⟨hzS, Finset.mem_sdiff.mpr ⟨crossingEdgeRegion_subset_envelope h64 v hzS, hzF⟩⟩
  have hn : n ≤ ρ := crossingOutwardLen_le u ρ
  have hm : m ≤ ρ := crossingOutwardLen_le v ρ
  have hpows : (p : ℝ) ^ (2 * ρ) ≤ (p : ℝ) ^ (n + m) :=
    pow_le_pow_of_le_one p.2.1 p.2.2 (by omega)
  change a₀ * (t : ℝ) ^ e ≤ _
  rw [show a₀ * (t : ℝ) ^ e = (p : ℝ) ^ (2 * ρ) * ((a / 2) * (t : ℝ) ^ e) by
    unfold a₀
    rw [mul_assoc]]
  exact (mul_le_mul_of_nonneg_right hpows (by positivity)).trans
    (hbound.trans (measureReal_mono (connectionToSetEvent_mono hD' subset_rfl a') (measure_ne_top _ _)))

end NearCritical.SplitCrossDirect
