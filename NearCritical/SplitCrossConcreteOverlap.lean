module

public import NearCritical.SplitCrossOverlapPorts
public import NearCritical.SplitCrossEnvelopeFaceMass
public import NearCritical.SplitCrossConcreteMoats

/-! Uniform overlap for a pair of actual parent edges, summed over the
far-face terminal choices. Other endpoints are held fixed. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode Section10 MeasureTheory
open scoped Classical BigOperators

def crossingEdgeChoices {d : ℕ} (t : ℕ) (v : SplitTreeNode (4 * d)) (z : Vertex d) :
    Finset (Vertex d) :=
  match v with
  | face k => farLegFaceCore t (splitLegEquiv d k).1 (splitLegEquiv d k).2
  | _ => {z}

def crossingSummedScale {L : ℕ} (d t : ℕ) : SplitTreeNode L → ℝ
  | face _ => 1
  | _ => (t : ℝ) ^ ((2 : ℝ) - (d : ℝ))

private def crossingKernelCenters {d : ℕ} (v : SplitTreeNode (4 * d)) (a b : Vertex d) :
    Finset (Vertex d) :=
  match v with
  | face _ => {a}
  | _ => {a,b}

private theorem crossingKernelCenters_card {d : ℕ} (v : SplitTreeNode (4 * d)) (a b : Vertex d) :
    (crossingKernelCenters v a b).card ≤ 2 := by
  have hpair : ({a,b} : Finset (Vertex d)).card ≤ 2 := by
    rcases Finset.card_pair_eq_one_or_two (a := a) (b := b) with h | h <;> omega
  cases v <;> simp [crossingKernelCenters, hpair]

private theorem mem_crossingKernelCenters {d : ℕ} (v : SplitTreeNode (4 * d)) (a b z : Vertex d)
    (hz : z ∈ crossingKernelCenters v a b) : z = a ∨ z = b := by
  cases v <;> simp_all [crossingKernelCenters]

def crossingOverlapCoeff (d : ℕ) (G B q : ℝ) : ℝ :=
  let M := max (G * B) ((2 : ℝ)^d * G^2 * q ^ ((2 : ℝ) - (d : ℝ)))
  (((M * G) * conv2Const d) * M) * convConst d * 4

private theorem concrete_kernel_majorant {d t : ℕ} (hd : 7 ≤ d) (ht : 4096 ≤ t)
    {G B q : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (hBm : BoxFaceFirstMoment d B) (hq : 0 < q)
    (U : Finset (Vertex d)) (hU : U ⊆ splitEnvelope d t) (v : SplitTreeNode (4 * d))
    (a b u : Vertex d) (hu : u ∈ U)
    (hab : q * (t : ℝ) ≤ latticeDistance a b) :
    summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) a (crossingEdgeChoices t v b) u ≤
      (max (G * B) ((2 : ℝ)^d * G^2 * q ^ ((2 : ℝ) - (d : ℝ))) *
        crossingSummedScale d t v) * ∑ z ∈ crossingKernelCenters v a b, kern 2 z u := by
  let γ := (2 : ℝ) - (d : ℝ)
  let M := max (G * B) ((2 : ℝ)^d * G^2 * q ^ γ)
  have htR : 0 < (t : ℝ) := by positivity
  have hqt : 0 < q * (t : ℝ) := mul_pos hq htR
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
  have hγ : γ ≤ 0 := by dsimp [γ]; linarith
  have hne : a ≠ b := by
    intro h
    rw [h, latticeDistance_eq_vertex_dist, dist_self] at hab
    exact (not_le_of_gt hqt) hab
  have hpow : kern 2 a b ≤ q ^ γ * (t : ℝ) ^ γ := by
    unfold kern
    rw [← Real.mul_rpow hq.le htR.le]
    exact Real.rpow_le_rpow_of_nonpos hqt (hab.trans (le_max_right _ _)) hγ
  have hI : summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) a {b} u ≤
      (M * (t : ℝ) ^ γ) * ∑ z ∈ ({a,b} : Finset (Vertex d)), kern 2 z u := by
    refine (summedEndpointKernel_singleton_le (by omega) hG green _ a b u hne).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => kern_nonneg _ _ _))
    calc
      _ ≤ ((2 : ℝ)^d * G^2) * (q ^ γ * (t : ℝ) ^ γ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((2 : ℝ)^d * G^2 * q ^ γ) * (t : ℝ) ^ γ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg htR.le _)
  cases v with
  | face k =>
    have hY := farLegFaceCore_connection_mass_le (by omega) hBm U hU u hu
      (splitLegEquiv d k).1 (splitLegEquiv d k).2
    refine (summedEndpointKernel_le_of_mass hG green _ a u _ hY).trans ?_
    change (G * B) * _ ≤ (M * 1) * _
    rw [mul_one]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg (fun _ _ => kern_nonneg _ _ _))
  | root | spine _ | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ => exact hI

private theorem crossingKernelCenters_dist {d t : ℕ} (hd3 : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (ht : 4096 ≤ t) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (hgap : 3 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (u v : CrossingEdgeIndex d) (hne : u ≠ v) :
    let L := concreteCrossingLayout hd3 hL t x R
    let P := L.pos (fun v => b v.val) (fun v => b v.val)
    let e := crossingPortEdge hL u.val
    let f := crossingPortEdge hL v.val
    ∀ a ∈ crossingKernelCenters u.val (P e.1) (P e.2),
      ∀ c ∈ crossingKernelCenters v.val (P f.1) (P f.2),
        ((R + 1 : ℕ) : ℝ) ≤ latticeDistance a c := by
  intro L P e f a ha c hc
  have hne' : u.val ≠ v.val := fun h => hne (Subtype.ext h)
  rcases mem_crossingKernelCenters _ _ _ _ ha with rfl | rfl <;>
    rcases mem_crossingKernelCenters _ _ _ _ hc with rfl | rfl
  · exact concreteCrossingLayout_distinct_ports_gap hd3 hL ht x hx axis R hgap b hb _ _
      (fun h => hne' (crossingPortEdge_source_injective hL u.property v.property h))
  · exact concreteCrossingLayout_distinct_ports_gap hd3 hL ht x hx axis R hgap b hb _ _
      (crossingPortEdge_source_ne_target hL u.val v.val v.property)
  · exact concreteCrossingLayout_distinct_ports_gap hd3 hL ht x hx axis R hgap b hb _ _
      (crossingPortEdge_source_ne_target hL v.val u.val u.property).symm
  · exact concreteCrossingLayout_distinct_ports_gap hd3 hL ht x hx axis R hgap b hb _ _
      (fun h => hne' (crossingPortEdge_target_injective hL h))

/-- Use the fixed tube of an indexed edge with a specified terminal. -/
def concreteTubeChoice {d : ℕ} (hd3 : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (b : SplitTreeNode (4 * d) → Vertex d)
    (v : CrossingEdgeIndex d)
    (hpos : (concreteCrossingLayout hd3 hL t x R).pos (fun v => b v.val) (fun v => b v.val)
      (crossingPortEdge hL v.val).1 ∈ crossingOutside hd3 t b R 1)
    (y : Vertex d) : TEdge d (crossingOutside hd3 t b R 1) where
  T := (crossingEdgeRegion t v.val : Set (Vertex d)) ∩ (crossingOutside hd3 t b R 1 : Set (Vertex d))
  hT := Set.inter_subset_right
  a := (concreteCrossingLayout hd3 hL t x R).pos (fun v => b v.val) (fun v => b v.val)
    (crossingPortEdge hL v.val).1
  b := y
  ha := hpos

set_option maxHeartbeats 800000 in
/-- The two-edge overlap summed over the actual terminal choices. -/
theorem concrete_crossing_pair_overlap_le {d t : ℕ} (hd : 7 ≤ d) (hd3 : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (ht : 4096 ≤ t) {G B q : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) (hB : 0 ≤ B)
    (hBm : BoxFaceFirstMoment d B) (hq : 0 < q)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (hgap : 3 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ))
    (hscale : q * (t : ℝ) + 2 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (u v : CrossingEdgeIndex d) (hne : u ≠ v) :
    let L := concreteCrossingLayout hd3 hL t x R
    let P := L.pos (fun v => b v.val) (fun v => b v.val)
    let U := crossingOutside hd3 t b R 1
    let e := crossingPortEdge hL u.val
    let f := crossingPortEdge hL v.val
    ∀ (he : P e.1 ∈ U) (hf : P f.1 ∈ U),
      (∑ y ∈ crossingEdgeChoices t v.val (P f.2), ∑ z ∈ crossingEdgeChoices t u.val (P e.2),
        (concreteTubeChoice hd3 hL t x R b v hf y).overlap (criticalPoint d)
          (concreteTubeChoice hd3 hL t x R b u he z)) ≤
        crossingOverlapCoeff d G B q * ((R + 1 : ℕ) : ℝ) ^ ((6 : ℝ) - (d : ℝ)) *
          crossingSummedScale d t u.val * crossingSummedScale d t v.val := by
  intro L P U e f he hf
  let Yx := crossingEdgeChoices t u.val (P e.2)
  let Yf := crossingEdgeChoices t v.val (P f.2)
  let X := crossingKernelCenters u.val (P e.1) (P e.2)
  let F := crossingKernelCenters v.val (P f.1) (P f.2)
  let M := max (G * B) ((2 : ℝ)^d * G^2 * q ^ ((2 : ℝ) - (d : ℝ)))
  let sx := crossingSummedScale d t u.val
  let sf := crossingSummedScale d t v.val
  have hM : 0 ≤ M := (mul_nonneg hG hB).trans (le_max_left _ _)
  have htR : (0 : ℝ) ≤ t := by positivity
  have hs (w : SplitTreeNode (4 * d)) : 0 ≤ crossingSummedScale d t w := by
    cases w <;> simp [crossingSummedScale, Real.rpow_nonneg htR]
  have hU : U ⊆ splitEnvelope d t := Finset.sdiff_subset
  have hDx : q * (t : ℝ) ≤ latticeDistance (P e.1) (P e.2) := by
    have h := concreteCrossingLayout_edge_gap hd3 hL ht x hx axis R b hb u.val u.property
    change _ ≤ _ + latticeDistance (P e.1) (P e.2) at h
    linarith
  have hDf : q * (t : ℝ) ≤ latticeDistance (P f.1) (P f.2) := by
    have h := concreteCrossingLayout_edge_gap hd3 hL ht x hx axis R b hb v.val v.property
    change _ ≤ _ + latticeDistance (P f.1) (P f.2) at h
    linarith
  have hxK (z : Vertex d) (hz : z ∈ U) :
      summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) (P e.1) Yx z ≤
        (M * sx) * ∑ a ∈ X, kern 2 a z :=
    concrete_kernel_majorant hd ht hG green hBm hq U hU _ _ _ z hz hDx
  have hfK (z : Vertex d) (hz : z ∈ U) :
      summedEndpointKernel (criticalPoint d) (U : Set (Vertex d)) (P f.1) Yf z ≤
        (M * sf) * ∑ a ∈ F, kern 2 a z :=
    concrete_kernel_majorant hd ht hG green hBm hq U hU _ _ _ z hz hDf
  have hpair := sum_overlap_le_diagram (criticalPoint d) U Yf Yx (P f.1) (P e.1)
    (concreteTubeChoice hd3 hL t x R b v hf) (concreteTubeChoice hd3 hL t x R b u he)
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
  have hconv := summed_overlap_diagram_le hd hG green (mul_nonneg hM (hs u.val))
    (mul_nonneg hM (hs v.val)) U Yf Yx X F (P f.1) (P e.1) hxK hfK
  let k := ((R + 1 : ℕ) : ℝ) ^ ((6 : ℝ) - (d : ℝ))
  have hR : 0 < ((R + 1 : ℕ) : ℝ) := by positivity
  have hk : 0 ≤ k := Real.rpow_nonneg hR.le _
  have h6 : (6 : ℝ) - (d : ℝ) ≤ 0 := by
    have hh : (6 : ℝ) ≤ d := by exact_mod_cast (show 6 ≤ d by omega)
    linarith
  have hsix : (∑ a ∈ X, ∑ c ∈ F, kern 6 a c) ≤ 4 * k := by
    calc
      _ ≤ ∑ _a ∈ X, ∑ _c ∈ F, k := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro c hc
        have hdist := crossingKernelCenters_dist hd3 hL ht x hx axis R hgap b hb u v hne a ha c hc
        exact Real.rpow_le_rpow_of_nonpos hR (hdist.trans (le_max_right _ _)) h6
      _ = ((X.card : ℝ) * (F.card : ℝ)) * k := by
        simp [nsmul_eq_mul, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hk
        have hX : (X.card : ℝ) ≤ 2 := by exact_mod_cast crossingKernelCenters_card u.val (P e.1) (P e.2)
        have hF : (F.card : ℝ) ≤ 2 := by exact_mod_cast crossingKernelCenters_card v.val (P f.1) (P f.2)
        exact (mul_le_mul hX hF (by positivity) (by norm_num)).trans_eq (by norm_num)
  refine (hpair.trans hconv).trans ?_
  calc
    _ ≤ ((((M * sx * G) * conv2Const d) * (M * sf)) * convConst d) * (4 * k) :=
      mul_le_mul_of_nonneg_left hsix (by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hM (hs u.val)) hG)
          (conv2Const_nonneg d)) (mul_nonneg hM (hs v.val))) (convConst_nonneg d))
    _ = _ := by
      change _ = crossingOverlapCoeff d G B q * k * sx * sf
      dsimp [crossingOverlapCoeff, M]
      ring

end NearCritical.SplitCrossDirect
