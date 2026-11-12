module

public import NearCritical.SplitCrossConcreteOverlap
public import NearCritical.SplitCrossTotalOverlap

/-! The summed tube probability has the interior power at a singleton
endpoint and constant order after summing the far face. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical BigOperators

private theorem face_choices_card_real {d t : ℕ} (f : Fin d × Bool) (pl : Bool) :
    ((t : ℝ) / 128) ^ (d - 1) ≤ ((farLegFaceCore t f pl).card : ℝ) := by
  have hside : (t : ℝ) / 128 ≤ (2 * (legBoxRadius t / 2) + 1 : ℕ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).mpr
    exact_mod_cast (show t ≤ (2 * (legBoxRadius t / 2) + 1) * 128 by unfold legBoxRadius; omega)
  refine (pow_le_pow_left₀ (by positivity) hside _).trans ?_
  exact_mod_cast farLegFaceCore_card_lower t f pl

private theorem face_power_cancel {d t : ℕ} (hd : 1 ≤ d) (ht : 0 < t) :
    (t : ℝ) ^ ((1 : ℝ) - (d : ℝ)) * ((t : ℝ) / 128) ^ (d - 1) =
      ((1 : ℝ) / 128) ^ (d - 1) := by
  have h : (1 : ℝ) - (d : ℝ) = -(((d - 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  rw [h, Real.rpow_neg ht'.le, Real.rpow_natCast, div_pow, div_pow, one_pow]
  field_simp [ne_of_gt ht']

def crossingMassCoeff (d : ℕ) (a : ℝ) : ℝ :=
  min a (a * ((1 : ℝ) / 128) ^ (d - 1))

theorem crossingMassCoeff_pos (d : ℕ) {a : ℝ} (ha : 0 < a) : 0 < crossingMassCoeff d a :=
  lt_min ha (mul_pos ha (by positivity))

/-- The face cardinal bound cancels the extra boundary decay. -/
theorem crossing_edge_choice_mass_lower {d t : ℕ} {U : Finset (Vertex d)}
    (hd : 1 ≤ d) (ht : 0 < t) {a : ℝ} (ha : 0 < a)
    (v : SplitTreeNode (4 * d)) (z : Vertex d) (E : Vertex d → TEdge d U)
    (h : ∀ y ∈ crossingEdgeChoices t v z,
      a * (t : ℝ) ^ crossingEdgeExponent d v ≤ (E y).tau (criticalPoint d)) :
    crossingMassCoeff d a * crossingSummedScale d t v ≤
      ∑ y ∈ crossingEdgeChoices t v z, (E y).tau (criticalPoint d) := by
  have hI : crossingMassCoeff d a * (t : ℝ) ^ ((2 : ℝ) - (d : ℝ)) ≤
      a * (t : ℝ) ^ ((2 : ℝ) - (d : ℝ)) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)
  cases v with
  | face k =>
    let Y := farLegFaceCore t (splitLegEquiv d k).1 (splitLegEquiv d k).2
    let γ := (1 : ℝ) - (d : ℝ)
    have hy : ((t : ℝ) / 128) ^ (d - 1) ≤ (Y.card : ℝ) := face_choices_card_real _ _
    change crossingMassCoeff d a * 1 ≤ ∑ y ∈ Y, (E y).tau (criticalPoint d)
    rw [mul_one]
    calc
      _ ≤ a * ((1 : ℝ) / 128) ^ (d - 1) := min_le_right _ _
      _ = (a * (t : ℝ) ^ γ) * ((t : ℝ) / 128) ^ (d - 1) := by
        rw [mul_assoc, face_power_cancel hd ht]
      _ ≤ (a * (t : ℝ) ^ γ) * (Y.card : ℝ) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      _ = ∑ _y ∈ Y, a * (t : ℝ) ^ γ := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun y hy => h y hy)
  | root | spine _ | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ =>
    have hz := h z (by simp [crossingEdgeChoices])
    simpa only [crossingEdgeChoices, crossingSummedScale, crossingEdgeExponent, Finset.sum_singleton] using
      (hI.trans hz)

private theorem crossingOutside_update_nonbranch {d : ℕ} (hd : 3 ≤ d) (t R : ℕ)
    (b : SplitTreeNode (4 * d) → Vertex d) (v : SplitTreeNode (4 * d))
    (hv : v ∉ crossingBranches (4 * d)) (y : Vertex d) :
    crossingOutside hd t (Function.update b v y) R 1 = crossingOutside hd t b R 1 := by
  unfold crossingOutside treeMoatVertices
  congr 1
  apply Finset.biUnion_congr rfl
  intro w hw
  have hne : w ≠ v := fun h => hv (by simpa only [h] using hw)
  rw [Function.update_of_ne hne]

/-- Replacing one face terminal preserves the outside domain and all branch
positions. The fixed-tube lower bound therefore applies to every choice. -/
theorem concreteTubeChoice_tau_lower {d t : ℕ} (hd3 : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (x : Vertex d) (axis : Fin d) (R : ℕ) (a : ℝ)
    (hbound : ∀ (b : SplitTreeNode (4 * d) → Vertex d), (∀ v, b v ∈ nodeSites t x axis v) →
      ∀ v : CrossingEdgeIndex d,
      let L := concreteCrossingLayout hd3 hL t x R
      let P := L.pos (fun v => b v.val) (fun v => b v.val)
      let e := crossingPortEdge hL v.val
      a * (t : ℝ) ^ crossingEdgeExponent d v.val ≤
        restrictedConnectionReal (criticalPoint d)
          ((crossingEdgeRegion t v.val : Set (Vertex d)) ∩ (crossingOutside hd3 t b R 1 : Set (Vertex d)))
          (P e.1) (P e.2))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (v : CrossingEdgeIndex d) :
    let L := concreteCrossingLayout hd3 hL t x R
    let P := L.pos (fun v => b v.val) (fun v => b v.val)
    let e := crossingPortEdge hL v.val
    ∀ (hpos : P e.1 ∈ crossingOutside hd3 t b R 1),
      ∀ y ∈ crossingEdgeChoices t v.val (P e.2),
        a * (t : ℝ) ^ crossingEdgeExponent d v.val ≤
          (concreteTubeChoice hd3 hL t x R b v hpos y).tau (criticalPoint d) := by
  intro L P e hpos y hy
  change _ ≤ restrictedConnectionReal (criticalPoint d)
    ((crossingEdgeRegion t v.val : Set (Vertex d)) ∩ (crossingOutside hd3 t b R 1 : Set (Vertex d)))
    (P e.1) y
  by_cases hv : ∃ k : Fin (4 * d), v.val = face k
  · obtain ⟨k, hk⟩ := hv
    have hnb : v.val ∉ crossingBranches (4 * d) := by simp [hk, isCrossingBranch]
    have hy' : y ∈ nodeSites t x axis v.val := by simpa [hk, crossingEdgeChoices, nodeSites] using hy
    let b' := Function.update b v.val y
    have hb' (w : SplitTreeNode (4 * d)) : b' w ∈ nodeSites t x axis w := by
      by_cases h : w = v.val
      · subst w
        simpa [b'] using hy'
      · simpa [b', Function.update_of_ne h] using hb w
    have hU := crossingOutside_update_nonbranch hd3 t R b v.val hnb y
    have hroot : b root = x := Finset.mem_singleton.mp (hb root)
    have hroot' : b' root = x := Finset.mem_singleton.mp (hb' root)
    let P' := L.pos (fun v => b' v.val) (fun v => b' v.val)
    have hp : parent hL v.val ≠ v.val := (parent_adj hL v.val v.property).ne
    have hstart : P' e.1 = P e.1 := by
      change L.pos _ _ (crossingPortAt (parent hL v.val) (childPortSlot (childSlot v.val))) =
        L.pos _ _ (crossingPortAt (parent hL v.val) (childPortSlot (childSlot v.val)))
      rw [concreteCrossingLayout_pos hd3 hL t x R b' hroot', concreteCrossingLayout_pos hd3 hL t x R b hroot]
      simp [crossingTip, b', Function.update_of_ne hp]
    have hend : P' e.2 = y := by
      change L.pos _ _ (crossingPortAt v.val 0) = y
      rw [concreteCrossingLayout_pos hd3 hL t x R b' hroot']
      simp [crossingTip, hnb, b']
    have h := hbound b' hb' v
    change _ ≤ restrictedConnectionReal _ (_ ∩ (crossingOutside hd3 t b' R 1 : Set (Vertex d)))
      (P' e.1) (P' e.2) at h
    rw [show crossingOutside hd3 t b' R 1 = crossingOutside hd3 t b R 1 from hU, hstart, hend] at h
    exact h
  · have heq : y = P e.2 := by
      have hv' := v.property
      cases hh : v.val <;> simp_all [crossingEdgeChoices]
    rw [heq]
    exact hbound b hb v

end NearCritical.SplitCrossDirect
