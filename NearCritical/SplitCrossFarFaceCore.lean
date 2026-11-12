module

public import NearCritical.SplitCrossTerminalBox
public import NearCritical.AppendixBoxWideFinal

/-! The trimmed terminal face required by the Appendix A lower bound.
Its transverse coordinates lie in a half-radius box. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section8 Section10 MeasureTheory
open scoped Classical ENNReal

/-- A full half-radius face shifted to the outer face of the radius-`r` cube. -/
def signedCubeFaceCore (d r : ℕ) (f : Fin d × Bool) : Finset (Vertex d) :=
  (signedCubeFace d (r / 2) f).image fun z =>
    Function.update z f.1 (if f.2 then (r : ℤ) else -(r : ℤ))

theorem signedCubeFaceCore_mem {d r : ℕ} {f : Fin d × Bool} {y : Vertex d}
    (hy : y ∈ signedCubeFaceCore d r f) :
    y ∈ signedCubeFace d r f ∧
      ∀ j, j ≠ f.1 → -((r / 2 : ℕ) : ℤ) ≤ y j ∧ y j ≤ ((r / 2 : ℕ) : ℤ) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hz' := mem_centeredBox.mp (Finset.mem_filter.mp hz).1
  refine ⟨Finset.mem_filter.mpr ⟨mem_centeredBox.mpr ?_, by simp⟩, ?_⟩
  · intro j
    by_cases hj : j = f.1
    · subst j
      cases hs : f.2 <;> simp [hs] <;> omega
    · rw [Function.update_of_ne hj]
      have hzj := hz' j
      omega
  · intro j hj
    rw [Function.update_of_ne hj]
    exact hz' j

theorem signedCubeFaceCore_card_lower (d r : ℕ) (f : Fin d × Bool) :
    (2 * (r / 2) + 1) ^ (d - 1) ≤ (signedCubeFaceCore d r f).card := by
  unfold signedCubeFaceCore
  rw [Finset.card_image_of_injOn]
  · exact signedCubeFace_card_lower d _ f
  · intro x hx y hy he
    have hxf := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hyf := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    funext j
    by_cases hj : j = f.1
    · rw [hj, hxf, hyf]
    · simpa [Function.update_of_ne hj] using congrFun he j

def farLegFaceCore {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) : Finset (Vertex d) :=
  translateSites (farLegBoxCenter t f pl) (signedCubeFaceCore d (legBoxRadius t) f)

theorem farLegFaceCore_subset_target {d t : ℕ} (ht : 64 ≤ t)
    (f : Fin d × Bool) (pl : Bool) : farLegFaceCore t f pl ⊆ splitTarget t f pl t := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  exact farLegBox_face_subset_target ht f pl ((mem_translateSites _ _ _).mpr
    (signedCubeFaceCore_mem hz).1)

theorem farLegFaceCore_card_lower {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) :
    (2 * (legBoxRadius t / 2) + 1) ^ (d - 1) ≤ (farLegFaceCore t f pl).card := by
  rw [farLegFaceCore, card_translateSites]
  exact signedCubeFaceCore_card_lower d _ f

/-- Connections from the interior half-box to the trimmed outer face have
the Appendix A power, uniformly in the leg and scale. -/
theorem farLegFaceCore_connection_lower {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {A B C c K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K) :
    ∃ b : ℝ, 0 < b ∧ ∀ (t : ℕ), 64 ≤ t → ∀ (f : Fin d × Bool) (pl : Bool)
      (x y : Vertex d),
      x ∈ translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t / 2)) →
      y ∈ farLegFaceCore t f pl →
      b / (t : ℝ) ^ (d - 1) ≤ (percolation d (criticalPoint d)).real
        (connectionToSetEvent
          (translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)) : Set (Vertex d))
          x {y}) := by
  obtain ⟨b, hb, hbox⟩ := appendix_box_twopoint_lower_from_pioneers hd asymp lower
    (α := 1/2) (by norm_num) (by norm_num) hA hB hC hc hK arm second panis hslab hpioneer
  refine ⟨b, hb, ?_⟩
  intro t ht f pl x y hx hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  let r := legBoxRadius t
  let a := farLegBoxCenter t f pl
  have hr : 1 ≤ r := by dsimp [r, legBoxRadius]; omega
  have hrt : r ≤ t := by dsimp [r, legBoxRadius]; omega
  have hv' := signedCubeFaceCore_mem hv
  have hface : v f.1 = -(r : ℤ) ∨ v f.1 = (r : ℤ) := by
    have hh := (Finset.mem_filter.mp hv'.1).2
    cases hsign : f.2
    · exact Or.inl (by simpa [hsign] using hh)
    · exact Or.inr (by simpa [hsign] using hh)
  have hmargin (z : ℤ) (hlo : -((r / 2 : ℕ) : ℤ) ≤ z)
      (hhi : z ≤ ((r / 2 : ℕ) : ℤ)) :
      |(z : ℝ)| ≤ (r : ℝ) - 1 / 2 * (r : ℝ) := by
    have hdiv : ((r / 2 : ℕ) : ℝ) * 2 ≤ (r : ℝ) := by exact_mod_cast (show r / 2 * 2 ≤ r by omega)
    rw [abs_le]
    have hlow : -((r / 2 : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast hlo
    have hhigh : (z : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := by
      simpa only [Int.cast_natCast] using
        (Int.cast_le.mpr hhi : (z : ℝ) ≤ (((r / 2 : ℕ) : ℤ) : ℝ))
    constructor <;> linarith
  have hbase := hbox f.1 r v u hr hface
    (fun j hj => hmargin _ (hv'.2 j hj).1 (hv'.2 j hj).2)
    (fun j => hmargin _ (mem_centeredBox.mp hu j).1 (mem_centeredBox.mp hu j).2)
  have hdomain : (fun z : Vertex d => a + z) '' (centeredBox d r : Set (Vertex d)) =
      (translateSites a (centeredBox d r) : Set (Vertex d)) := by
    simp [translateSites]
  have he := congrArg ENNReal.toReal (connectionToSet_probability_translation
    (criticalPoint d) a v (centeredBox d r : Set (Vertex d)) {u}).symm
  rw [hdomain, Set.image_singleton] at he
  change (percolation d (criticalPoint d)).real
      (connectionToSetEvent (centeredBox d r : Set (Vertex d)) v {u}) =
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (translateSites a (centeredBox d r) : Set (Vertex d))
        (a + v) {a + u}) at he
  rw [he, connectionToSetEvent_singleton_symm _ (a + v) (a + u)] at hbase
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hrle : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast hrt
  refine le_trans ?_ hbase
  exact div_le_div_of_nonneg_left hb.le (pow_pos hrpos _) (pow_le_pow_left₀ hrpos.le hrle _)

end NearCritical.SplitCrossDirect
