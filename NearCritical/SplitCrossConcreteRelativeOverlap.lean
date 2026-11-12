module

public import NearCritical.SplitCrossConcreteTubeMass

/-! The concrete pair estimate is small relative to the corresponding
summed tube masses, including when either edge ends on a face. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode Section10 MeasureTheory
open scoped Classical BigOperators

theorem crossingOverlapCoeff_nonneg (d : ℕ) {G B q : ℝ} (hG : 0 ≤ G) (hB : 0 ≤ B) :
    0 ≤ crossingOverlapCoeff d G B q := by
  let M := max (G * B) ((2 : ℝ)^d * G^2 * q ^ ((2 : ℝ) - (d : ℝ)))
  have hM : 0 ≤ M := (mul_nonneg hG hB).trans (le_max_left _ _)
  change 0 ≤ (((M * G) * conv2Const d) * M) * convConst d * 4
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hM hG)
    (conv2Const_nonneg d)) hM) (convConst_nonneg d)) (by norm_num)

def crossingRelativeOverlap (d : ℕ) (G B q a : ℝ) (R : ℕ) : ℝ :=
  (crossingOverlapCoeff d G B q / (crossingMassCoeff d a)^2) *
    ((R + 1 : ℕ) : ℝ) ^ ((6 : ℝ) - (d : ℝ))

theorem crossingRelativeOverlap_nonneg (d R : ℕ) {G B q a : ℝ} (hG : 0 ≤ G) (hB : 0 ≤ B) :
    0 ≤ crossingRelativeOverlap d G B q a R := by
  exact mul_nonneg (div_nonneg (crossingOverlapCoeff_nonneg d (q := q) hG hB) (sq_nonneg _))
    (Real.rpow_nonneg (by positivity) _)

/-- The star radius absorbs the pair error at a fixed edge count. -/
theorem crossingRelativeOverlap_eventually_half {d : ℕ} (hd : 7 ≤ d) (n : ℕ)
    {G B q a : ℝ} (hG : 0 ≤ G) (hB : 0 ≤ B) :
    ∃ R₀ : ℕ, ∀ R ≥ R₀,
      (n : ℝ)^2 * crossingRelativeOverlap d G B q a R ≤ 1 / 2 := by
  let K := crossingOverlapCoeff d G B q / (crossingMassCoeff d a)^2
  have hK : 0 ≤ K := div_nonneg (crossingOverlapCoeff_nonneg d (q := q) hG hB) (sq_nonneg _)
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (2 * (n : ℝ)^2 * K)
  refine ⟨R₀, ?_⟩
  intro R hR
  have hr : 1 ≤ (((R + 1 : ℕ) : ℝ)) := by exact_mod_cast (show 1 ≤ R + 1 by omega)
  have hRd : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : (((R + 1 : ℕ) : ℝ)) ^ ((6 : ℝ) - (d : ℝ)) ≤ (((R + 1 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have hnum : 2 * (n : ℝ)^2 * K ≤ (((R + 1 : ℕ) : ℝ)) :=
    hR₀.le.trans (by exact_mod_cast (show R₀ ≤ R + 1 by omega))
  change (n : ℝ)^2 * (K * (((R + 1 : ℕ) : ℝ)) ^ ((6 : ℝ) - (d : ℝ))) ≤ _
  calc
    _ ≤ (n : ℝ)^2 * (K * (((R + 1 : ℕ) : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hK) (sq_nonneg _)
    _ = ((n : ℝ)^2 * K) / (((R + 1 : ℕ) : ℝ)) := by rw [div_eq_mul_inv, mul_assoc]
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by linarith)

set_option maxHeartbeats 800000 in
/-- Relative distinct-cluster lower bound for the concrete tube lists,
after summing over all face terminals. -/
theorem concrete_summed_distinct_lower {d t : ℕ} (hd : 7 ≤ d) (hd3 : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (ht : 4096 ≤ t) {G B q a : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) (hB : 0 ≤ B)
    (hBm : BoxFaceFirstMoment d B) (hq : 0 < q) (ha : 0 < a)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (hgap : 3 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ))
    (hscale : q * (t : ℝ) + 2 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (l : List (CrossingEdgeIndex d)) (hl : l.Nodup) :
    let L := concreteCrossingLayout hd3 hL t x R
    let P := L.pos (fun v => b v.val) (fun v => b v.val)
    let U := crossingOutside hd3 t b R 1
    ∀ hpos : ∀ v : CrossingEdgeIndex d, P (crossingPortEdge hL v.val).1 ∈ U,
    let Y := fun v : CrossingEdgeIndex d => crossingEdgeChoices t v.val (P (crossingPortEdge hL v.val).2)
    let E := fun v => concreteTubeChoice hd3 hL t x R b v (hpos v)
    (∀ v, ∀ y ∈ Y v, a * (t : ℝ) ^ crossingEdgeExponent d v.val ≤ (E v y).tau (criticalPoint d)) →
    (1 - (l.length : ℝ)^2 * crossingRelativeOverlap d G B q a R) *
      tubeChoiceProduct (criticalPoint d) Y E l ≤
      sumTubeChoices Y E l (fun es =>
        (percolation d (criticalPoint d)).real (distinctLoc U (es.map TEdge.loc))) := by
  intro L P U hpos Y E hpoint
  let M := tubeChoiceMass (criticalPoint d) Y E
  let C := crossingMassCoeff d a
  let K := crossingOverlapCoeff d G B q
  let k := ((R + 1 : ℕ) : ℝ) ^ ((6 : ℝ) - (d : ℝ))
  have hC : 0 < C := crossingMassCoeff_pos d ha
  have hK : 0 ≤ K := crossingOverlapCoeff_nonneg d hG hB
  have hk : 0 ≤ k := Real.rpow_nonneg (by positivity) _
  have hM (v : CrossingEdgeIndex d) : C * crossingSummedScale d t v.val ≤ M v :=
    crossing_edge_choice_mass_lower (by omega) (by omega) ha _ _ _ (hpoint v)
  have hM0 (v : CrossingEdgeIndex d) : 0 ≤ M v := tubeChoiceMass_nonneg _ _ _ _
  have hs (v : CrossingEdgeIndex d) : 0 ≤ crossingSummedScale d t v.val := by
    cases hv : v.val <;> simp [crossingSummedScale, Real.rpow_nonneg (show 0 ≤ (t : ℝ) by positivity)]
  apply sumTubeChoices_distinct_lower _ _ _ _
    (crossingRelativeOverlap_nonneg d R hG hB) _ l hl
  intro v u hne
  have hpair := concrete_crossing_pair_overlap_le hd hd3 hL ht hG green hB hBm hq
    x hx axis R hgap hscale b hb u v hne.symm (hpos u) (hpos v)
  change (∑ y ∈ Y v, ∑ z ∈ Y u, (E v y).overlap (criticalPoint d) (E u z)) ≤ _
  calc
    _ ≤ K * k * crossingSummedScale d t u.val * crossingSummedScale d t v.val := hpair
    _ = (K / C^2 * k) * ((C * crossingSummedScale d t v.val) *
        (C * crossingSummedScale d t u.val)) := by
      field_simp [ne_of_gt hC]
      <;> ring
    _ ≤ _ := by
      have hb' := mul_le_mul (hM v) (hM u) (mul_nonneg hC.le (hs u)) (hM0 v)
      have hcoeff : 0 ≤ K / C^2 * k := mul_nonneg (div_nonneg hK (sq_nonneg _)) hk
      change _ ≤ (K / C^2 * k) * M v * M u
      rw [mul_assoc (K / C^2 * k) (M v) (M u)]
      exact mul_le_mul_of_nonneg_left hb' hcoeff

end NearCritical.SplitCrossDirect
