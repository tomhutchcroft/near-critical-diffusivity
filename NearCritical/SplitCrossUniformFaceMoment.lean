module

public import NearCritical.SplitCrossFaceAssignmentMoment
public import NearCritical.SplitCrossConcreteFixedTube
public import NearCritical.SplitCrossOverlapScale
public import NearCritical.Section10BoxFaceFromPioneer
public import NearCritical.ThreePointDiagram

/-! Choose the star length once so the face assignment lower bound is
uniform in all admissible placements and all sufficiently large scales. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode Section10 Section8 MeasureTheory
open scoped Classical BigOperators

private theorem scaled_product_le {ι : Type*} {a : ℝ} (ha : 0 ≤ a)
    (s m : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (hm : ∀ i, a * s i ≤ m i) (l : List ι) :
    a ^ l.length * (l.map s).prod ≤ (l.map m).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_cons, List.map_cons, List.prod_cons] at *
    calc
      _ = (a * s i) * (a ^ l.length * (l.map s).prod) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul (hm i) ih
        (mul_nonneg (pow_nonneg ha _) (List.prod_nonneg (by simpa using fun i (_ : i ∈ l) => hs i)))
        ((mul_nonneg ha (hs i)).trans (hm i))

/-- The summed realization bound with a single positive constant and a
single star length for all admissible placements. -/
theorem uniform_face_assignment_moment_lower {d : ℕ} (hd : 7 ≤ d) (hd3 : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {A B C c K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K) :
    ∃ (R : ℕ) (c₀ : ℝ), 0 < c₀ ∧ ∃ T : ℕ, ∀ t ≥ T,
      4096 ≤ t ∧ 512 * (4 * d - 1 + 1) * (R + 1) ≤ t ∧ 2048 * (R + 1) ≤ t ∧
      ((R + 1 : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ) ∧
      ∀ (x : Vertex d), x ∈ centeredBox d ((t - 1) / 32) →
      ∀ (axis : Fin d) (b : SplitTreeNode (4 * d) → Vertex d), (∀ v, b v ∈ nodeSites t x axis v) →
      let L := concreteCrossingLayout hd3 hL t x R
      let P := L.pos (fun v => b v.val) (fun v => b v.val)
      let Y := fun v : CrossingEdgeIndex d => crossingEdgeChoices t v.val (P (crossingPortEdge hL v.val).2)
      c₀ * ((crossingEdgeIndices d).map (fun v => crossingSummedScale d t v.val)).prod ≤
        ∑ f ∈ Fintype.piFinset Y, (percolation d (criticalPoint d)).real
          (L.realEvent (fun v => (faceAssignedSites b f) v.val) (fun v => (faceAssignedSites b f) v.val)) := by
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymp
  obtain ⟨hp, hp'⟩ := criticalPoint_interior_of_twoPointAsymptotics (by omega : 2 < d) (parentAxis hd3) asymp
  obtain ⟨ρ, _, a, ha, R₀, htube⟩ :=
    concrete_crossing_fixed_tubes_lower hd hd3 asymp lower hA hB hC hc hK arm second panis hslab hpioneer hG.le green
  obtain ⟨q, hq, hsep⟩ := crossing_overlap_scales_eventually d
  let l := crossingEdgeIndices d
  obtain ⟨R₁, hover⟩ := crossingRelativeOverlap_eventually_half hd l.length
    (q := q) (a := a) hG.le hK.le
  let R := max R₀ R₁
  obtain ⟨T₀, hT₀⟩ := htube R (le_max_left _ _)
  obtain ⟨T₁, hT₁⟩ := hsep R
  let k := crossingPatternFactor d R (criticalPoint d) / 2
  have hk : 0 < k := div_pos (crossingPatternFactor_pos d R hp hp') (by norm_num)
  have hmass := crossingMassCoeff_pos d ha
  refine ⟨R, k * crossingMassCoeff d a ^ l.length, mul_pos hk (pow_pos hmass _), max T₀ T₁, ?_⟩
  intro t ht
  obtain ⟨ht4, hts', htl', hout', hfixed⟩ := hT₀ t ((le_max_left _ _).trans ht)
  obtain ⟨hgap, hscale⟩ := hT₁ t ((le_max_right _ _).trans ht)
  have hts := (Nat.mul_le_mul_left (512 * (4 * d - 1 + 1)) (Nat.le_add_right (R + 1) ρ)).trans hts'
  have htl := (Nat.mul_le_mul_left 2048 (Nat.le_add_right (R + 1) ρ)).trans htl'
  have hout : ((R + 1 : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) <
      (spineRadius (4 * d - 1) t : ℝ) := by
    have hρ : ((R + 1 : ℕ) : ℝ) ≤ ((R + 1 + ρ : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right (R + 1) ρ
    linarith
  refine ⟨ht4, hts, htl, hout, ?_⟩
  intro x hx axis b hb L P Y
  have hbound (b' : SplitTreeNode (4 * d) → Vertex d) (hb' : ∀ v, b' v ∈ nodeSites t x axis v)
      (v : CrossingEdgeIndex d) :
      a * (t : ℝ) ^ crossingEdgeExponent d v.val ≤
        restrictedConnectionReal (criticalPoint d)
          ((crossingEdgeRegion t v.val : Set (Vertex d)) ∩ (crossingOutside hd3 t b' R 1 : Set (Vertex d)))
          (L.pos (fun w => b' w.val) (fun w => b' w.val)
            (crossingPortAt (parent hL v.val) (childPortSlot (childSlot v.val))))
          (L.pos (fun w => b' w.val) (fun w => b' w.val) (crossingPortAt v.val 0)) := by
    dsimp only [L]
    have hroot : b' root = x := Finset.mem_singleton.mp (hb' root)
    rw [concreteCrossingLayout_pos hd3 hL t x R b' hroot, concreteCrossingLayout_pos hd3 hL t x R b' hroot]
    simp only [crossingPortAxis_zero, crossingPortAxis_child, restrictedConnectionReal]
    exact hfixed x hx axis b' hb' hL v.val v.property _ (childAxis_mem_branchAxes hd3 _)
      _ (parentAxis_mem_branchAxes hd3)
  have hpos (v : CrossingEdgeIndex d) : P (crossingPortEdge hL v.val).1 ∈ crossingOutside hd3 t b R 1 := by
    have he : crossingPortEdge hL v.val ∈ L.edges :=
      (mem_concreteCrossingLayout_edges hd3 hL t x R _).mpr ⟨v.val, v.property, rfl⟩
    simpa only [concreteCrossingLayout_Uout] using
      concreteCrossingLayout_start_mem ht4 hd3 hL x hx axis R hts htl hout b hb _ he
  let E := fun v : CrossingEdgeIndex d => concreteTubeChoice hd3 hL t x R b v (hpos v)
  have hpoint (v : CrossingEdgeIndex d) (y : Vertex d) (hy : y ∈ Y v) :
      a * (t : ℝ) ^ crossingEdgeExponent d v.val ≤ (E v y).tau (criticalPoint d) :=
    concreteTubeChoice_tau_lower hd3 hL x axis R a hbound b hb v (hpos v) y hy
  have hprod := scaled_product_le hmass.le (fun v : CrossingEdgeIndex d => crossingSummedScale d t v.val)
    (tubeChoiceMass (criticalPoint d) Y E)
    (fun v => by cases v.val <;> simp [crossingSummedScale, Real.rpow_nonneg])
    (fun v => crossing_edge_choice_mass_lower (by omega : 1 ≤ d) (by omega : 0 < t) ha
      v.val (P (crossingPortEdge hL v.val).2) (E v) (hpoint v)) l
  have hmoment := concrete_face_assignment_moment_lower hd hd3 hL ht4 hG.le green hK.le
    (Section10.boxFaceFirstMoment_of_pioneerMass hK.le hpioneer) hq ha x hx axis R hts htl hout hgap hscale
    (hover R (le_max_right _ _)) b hb hpos hpoint
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hprod hk.le).trans hmoment

end NearCritical.SplitCrossDirect
