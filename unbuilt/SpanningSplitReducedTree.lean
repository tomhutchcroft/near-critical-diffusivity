module

public import NearCritical.SpanningSplitGuide
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory Set
open scoped Classical ENNReal

abbrev SplitEdgePath (d : ℕ) := C(Set.Icc (0:ℝ) 1, Fin d → ℝ)

def splitEdgePathStart : Set.Icc (0:ℝ) 1 := ⟨0,by norm_num⟩
def splitEdgePathEnd : Set.Icc (0:ℝ) 1 := ⟨1,by norm_num⟩

/-- The continuous target path for the Brownian increment on a leaf edge. -/
def splitGuidePath {d : ℕ} (f : Fin d × Bool) (pl : Bool) : SplitEdgePath d where
  toFun u := splitBranchGuide f pl u.val
  continuous_toFun := by
    apply continuous_pi
    intro j
    by_cases h : j = f.1
    · simp only [splitBranchGuide,h,if_true]
      cases hf : f.2 <;> simp [hf] <;> fun_prop
    · simp only [splitBranchGuide, h, if_false]
      cases pl <;> simp <;> fun_prop

theorem splitGuidePath_start {d : ℕ} (f : Fin d × Bool) (pl : Bool) :
    splitGuidePath f pl splitEdgePathStart = 0 := by
  ext j
  simp [splitGuidePath, splitEdgePathStart, splitBranchGuide]

/-- The joint event of the stem and leaf edge paths lying in their
prescribed open tubes. -/
def splitReducedTreeTubeEvent {d : ℕ} {E : Type*}
    (lab : E → Option ((Fin d × Bool) × Bool)) (δ : E → ℝ) :
    Set (E → SplitEdgePath d) :=
  {X | ∀ e, dist (X e) (match lab e with
    | none => 0
    | some i => splitGuidePath i.1 i.2) < δ e}

/-- Independent edge laws with full support on paths starting at zero
give positive joint mass to the prescribed stem and leaf tubes.
This applies at each fixed positive set of Brownian edge lengths. -/
theorem split_reduced_tree_tubes_positive {d : ℕ} {E : Type*} [Fintype E]
    [MeasurableSpace (SplitEdgePath d)] (μ : E → Measure (SplitEdgePath d))
    [∀ e, IsProbabilityMeasure (μ e)]
    (lab : E → Option ((Fin d × Bool) × Bool))
    (δ : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hsupport : ∀ e (g : SplitEdgePath d), g splitEdgePathStart = 0 →
      ∀ r : ℝ, 0 < r → 0 < μ e (Metric.ball g r)) :
    0 < Measure.pi μ (splitReducedTreeTubeEvent lab δ) := by
  let g (e : E) : SplitEdgePath d := match lab e with
    | none => 0
    | some i => splitGuidePath i.1 i.2
  have hg (e : E) : g e splitEdgePathStart = 0 := by
    cases h : lab e with
    | none => simp [g,h]
    | some i => simpa only [g,h] using splitGuidePath_start i.1 i.2
  have he : {X | ∀ e, dist (X e) (g e) < δ e} =
      Set.pi Set.univ (fun e => Metric.ball (g e) (δ e)) := by
    ext X
    simp [Set.mem_pi,Metric.mem_ball]
  change 0 < Measure.pi μ {X | ∀ e, dist (X e) (g e) < δ e}
  rw [he, Measure.pi_pi]
  exact Finset.prod_pos fun e _ => hsupport e (g e) (hg e) (δ e) (hδ e)

/-- The guide-tube probability stays positive after mixing over the
reduced-tree shape and its positive edge lengths. -/
theorem split_reduced_tree_tube_mixture_positive {d : ℕ} {E Z : Type*} [Fintype E]
    [MeasurableSpace Z] [MeasurableSpace (SplitEdgePath d)]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (law : Z → E → Measure (SplitEdgePath d)) [∀ z e, IsProbabilityMeasure (law z e)]
    (lab : Z → E → Option ((Fin d × Bool) × Bool)) (δ : Z → E → ℝ)
    (hδ : ∀ᵐ z ∂ν, ∀ e, 0 < δ z e)
    (hsupport : ∀ᵐ z ∂ν, ∀ e (g : SplitEdgePath d), g splitEdgePathStart = 0 →
      ∀ r : ℝ, 0 < r → 0 < law z e (Metric.ball g r))
    (hmeas : AEMeasurable (fun z => Measure.pi (law z) (splitReducedTreeTubeEvent (lab z) (δ z))) ν) :
    0 < ∫⁻ z, Measure.pi (law z) (splitReducedTreeTubeEvent (lab z) (δ z)) ∂ν := by
  let P (z : Z) := Measure.pi (law z) (splitReducedTreeTubeEvent (lab z) (δ z))
  have hp : ∀ᵐ z ∂ν, 0 < P z := by
    filter_upwards [hδ,hsupport] with z hz hs
    exact split_reduced_tree_tubes_positive (law z) (lab z) (δ z) hz hs
  change 0 < ∫⁻ z, P z ∂ν
  by_contra! hn
  have hzero : (∫⁻ z, P z ∂ν) = 0 := le_antisymm hn bot_le
  have hz := (lintegral_eq_zero_iff' hmeas).mp hzero
  obtain ⟨z,hpz,hzz⟩ := (hp.and hz).exists
  exact (ne_of_gt hpz) hzz

/-- A leaf path concatenated after small internal-edge increments stays
within its guide tube. The same bound for a stem point follows by using
the zero guide at time zero. -/
theorem split_guide_of_concatenation {d : ℕ} {E : Type*} [Fintype E]
    (f : Fin d × Bool) (pl : Bool) (X : E → SplitEdgePath d) (P : Finset E)
    (u : Set.Icc (0:ℝ) 1) (z : Fin d → ℝ)
    (hstem : ∀ e ∈ P, ∥X e splitEdgePathEnd∥ ≤ 1/(256*((Fintype.card E:ℝ)+1)))
    (hz : dist z (splitBranchGuide f pl u.val) ≤ (1/256:ℝ)) :
    dist ((∑ e ∈ P, X e splitEdgePathEnd)+z) (splitBranchGuide f pl u.val) ≤ (1/128:ℝ) := by
  let B := 1/(256*((Fintype.card E:ℝ)+1))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcard : (P.card:ℝ) ≤ (Fintype.card E:ℝ) := by
    exact_mod_cast Finset.card_le_univ P
  have hP : ∥∑ e ∈ P, X e splitEdgePathEnd∥ ≤ (1/256:ℝ) := by
    calc
      _ ≤ ∑ e ∈ P, ∥X e splitEdgePathEnd∥ := norm_sum_le _ _
      _ ≤ ∑ _e ∈ P, B := Finset.sum_le_sum hstem
      _ = (P.card:ℝ)*B := by simp [nsmul_eq_mul]
      _ ≤ ((Fintype.card E:ℝ)+1)*B := mul_le_mul_of_nonneg_right (by linarith) hB
      _ = _ := by
        dsimp only [B]
        field_simp [show (Fintype.card E:ℝ)+1 ≠ 0 by positivity]
  calc
    _ ≤ dist ((∑ e ∈ P, X e splitEdgePathEnd)+z) z + dist z (splitBranchGuide f pl u.val) :=
      dist_triangle _ _ _
    _ ≤ (1/256:ℝ)+(1/256:ℝ) := by
      rw [dist_eq_norm,add_sub_cancel_right]
      exact add_le_add hP hz
    _ = _ := by norm_num

/-- The reduced-tree concatenation transfers the independent edge tube
events to all of the required guide branches in the embedded tree. -/
theorem reducedTreeGuides_of_edgeTubes {d : ℕ} {E T : Type*} [Fintype E] [PseudoMetricSpace T]
    (r : T) (Φ : T → (Fin d → ℝ)) (X : E → SplitEdgePath d)
    (lab : E → Option ((Fin d × Bool) × Bool))
    (leaf : (Fin d × Bool) → Bool → E)
    (hlab : ∀ f pl, lab (leaf f pl) = some (f,pl))
    (htubes : ∀ e, dist (X e) (match lab e with
      | none => 0
      | some i => splitGuidePath i.1 i.2) ≤
        (match lab e with
        | none => 1/(256*((Fintype.card E:ℝ)+1))
        | some _ => 1/256))
    (hbranches : ∀ (f : Fin d × Bool) (pl : Bool), ∃ (y : T) (P : Finset E),
      (∀ e ∈ P, lab e = none) ∧
      Φ y = (∑ e ∈ P, X e splitEdgePathEnd) + X (leaf f pl) splitEdgePathEnd ∧
      ∀ a : T, dist r a + dist a y = dist r y →
        (∃ (Q : Finset E) (e : E) (u : Set.Icc (0:ℝ) 1),
          (∀ e' ∈ Q, lab e' = none) ∧ lab e = none ∧
          Φ a = (∑ e' ∈ Q, X e' splitEdgePathEnd) + X e u) ∨
        (∃ u : Set.Icc (0:ℝ) 1,
          Φ a = (∑ e ∈ P, X e splitEdgePathEnd) + X (leaf f pl) u)) :
    ∀ (f : Fin d × Bool) (pl : Bool), ∃ y : T,
      dist (Φ y) (splitBranchGuide f pl 1) ≤ (1/128:ℝ) ∧
      ∀ a : T, dist r a + dist a y = dist r y →
        ∃ u : ℝ, 0 ≤ u ∧ dist (Φ a) (splitBranchGuide f pl u) ≤ (1/128:ℝ) := by
  let B := 1/(256*((Fintype.card E:ℝ)+1))
  have hB : B ≤ (1/256:ℝ) := by
    dsimp only [B]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card E)]
  have hstem (e : E) (he : lab e = none) (u : Set.Icc (0:ℝ) 1) :
      ∥X e u∥ ≤ B := by
    have hs : dist (X e) 0 ≤ B := by simpa only [he,B] using htubes e
    simpa only [ContinuousMap.zero_apply, dist_zero_right] using
      (ContinuousMap.dist_apply_le_dist (f := X e) (g := 0) u).trans hs
  intro f pl
  obtain ⟨y,P,hP,hy,hpath⟩ := hbranches f pl
  have hleaf (u : Set.Icc (0:ℝ) 1) :
      dist (X (leaf f pl) u) (splitBranchGuide f pl u.val) ≤ (1/256:ℝ) :=
    (ContinuousMap.dist_apply_le_dist (f := X (leaf f pl)) (g := splitGuidePath f pl) u).trans
      (by simpa only [hlab f pl] using htubes (leaf f pl))
  have hp (u : Set.Icc (0:ℝ) 1) :=
    split_guide_of_concatenation f pl X P u (X (leaf f pl) u)
      (fun e he => hstem e (hP e he) splitEdgePathEnd) (hleaf u)
  refine ⟨y, ?_, ?_⟩
  · rw [hy]
    exact hp splitEdgePathEnd
  · intro a ha
    rcases hpath a ha with ⟨Q,e,u,hQ,he,ha'⟩ | ⟨u,ha'⟩
    · have hzero : splitBranchGuide f pl 0 = 0 := splitGuidePath_start f pl
      have hz : dist (X e u) (splitBranchGuide f pl 0) ≤ (1/256:ℝ) := by
        rw [hzero,dist_zero_right]
        exact (hstem e he u).trans hB
      refine ⟨0,le_rfl,?_⟩
      rw [ha']
      exact split_guide_of_concatenation f pl X Q splitEdgePathStart (X e u)
        (fun e' he' => hstem e' (hQ e' he') splitEdgePathEnd) hz
    · refine ⟨u.val,u.property.1,?_⟩
      rw [ha']
      exact hp u

end NearCritical.Section10
