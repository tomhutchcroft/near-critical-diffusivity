module

public import NearCritical.AppendixBoxTwoPointLowerFaces
public import NearCritical.AppendixBoxWideGeometry

/-! The wide-prism version of the Appendix A box two-point lower bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Section8
open scoped Classical ENNReal

/-- Exploration height with enough room for a fixed aspect ratio. -/
def appendixWideHeight (α : ℝ) (m n : ℕ) : ℕ := Nat.floor (α / (m : ℝ) * (n : ℝ) / 8)

theorem appendixWideHeight_scales (α : ℝ) (hα : 0 < α) (m n : ℕ) (hm : 2 ≤ m)
    (hn : 16 ≤ α / (m : ℝ) * (n : ℝ)) :
    let h := appendixWideHeight α m n
    1 ≤ h ∧ h ≤ m * h ∧ ((m * h : ℕ) : ℝ) ≤ α * (n : ℝ) / 4 := by
  intro h
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have hlo : (1 : ℝ) ≤ h := by
    have hf := Nat.lt_floor_add_one (α / (m : ℝ) * (n : ℝ) / 8)
    change α / (m : ℝ) * (n : ℝ) / 8 < (h : ℝ) + 1 at hf
    linarith
  have hhi : (h : ℝ) ≤ α / (m : ℝ) * (n : ℝ) / 8 :=
    Nat.floor_le (by positivity)
  have hR : (m : ℝ) * (h : ℝ) ≤ α * (n : ℝ) / 8 := by
    calc
      _ ≤ (m : ℝ) * (α / (m : ℝ) * (n : ℝ) / 8) := mul_le_mul_of_nonneg_left hhi hm0.le
      _ = _ := by field_simp [hm0.ne'] <;> ring
  refine ⟨by exact_mod_cast hlo, ?_, ?_⟩
  · have ht : (h : ℝ) ≤ (m : ℝ) * (h : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 (Nat.cast_nonneg h)
    exact_mod_cast ht
  · push_cast
    linarith [mul_nonneg hα.le (Nat.cast_nonneg (α := ℝ) n)]

/-- The two uniform error estimates on the wider exploration prism. Only
the cutoffs used by the lower bound, at most the prism height, are required. -/
def AppendixWideBoxErrorBounds (d : ℕ) (α : ℝ) (m : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n r : ℕ) (x : Vertex d),
    1 ≤ n → 1 ≤ r → 16 ≤ α / (m : ℝ) * (n : ℝ) → x i = -(n : ℤ) →
    (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
    let h := appendixWideHeight α m n
    let Q := appendixWideBox i h (m * h) x
    let F := appendixWideFace i h (m * h) x
    r ≤ h →
      appendixBoxClusterMean (criticalPoint d) Q x (fun U => appendixBoxErrCluster U F r) ≤
        K * (r : ℝ) ^ ((6 : ℝ) - (d : ℝ)) / (n : ℝ) ∧
      appendixBoxClusterMean (criticalPoint d) Q x (fun U => appendixBoxErrBoundary U F r) ≤
        K * (r : ℝ) ^ ((6 : ℝ) - (d : ℝ)) / (n : ℝ)

/-- The Appendix box estimate with the top-face lower mass proved using
the wider prism. The two cluster error estimates remain explicit. -/
theorem appendix_box_twopoint_lower_of_wide_errors {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {A B C c K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K)
    (herr : ∀ m : ℕ, 2 ≤ m → AppendixWideBoxErrorBounds d α m) :
    ∃ b : ℝ, 0 < b ∧ ∀ (i : Fin d) (n : ℕ) (x y : Vertex d), 1 ≤ n →
      (x i = -(n : ℤ) ∨ x i = (n : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      b / (n : ℝ) ^ (d - 1) ≤
        (percolation d (criticalPoint d)).real (connectionToSetEvent (centeredBox d n : Set (Vertex d)) x {y}) := by
  obtain ⟨m, hm, htop⟩ := boundary_top_mass_lower_of_pioneer (by omega : 2 ≤ d)
    hA hB hC hc hK arm second panis hslab hpioneer
  let β : ℝ := α / (m : ℝ)
  let h (n : ℕ) := appendixWideHeight α m n
  let Q (n : ℕ) (i : Fin d) (x : Vertex d) := appendixWideBox i (h n) (m * h n) x
  let F (n : ℕ) (i : Fin d) (x : Vertex d) := appendixWideFace i (h n) (m * h n) x
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have hβ0 : 0 < β := div_pos hα0 hm0
  have hβα : β ≤ α := div_le_self hα0.le hm1
  have hwide (n : ℕ) (hn : 16 ≤ β * (n : ℝ)) :
      1 ≤ h n ∧ h n ≤ m * h n ∧ ((m * h n : ℕ) : ℝ) ≤ α * (n : ℝ) / 4 :=
    appendixWideHeight_scales α hα0 m n hm hn
  have hgeom (i : Fin d) (n : ℕ) (x : Vertex d) (_hn : 1 ≤ n) (hlarge : 16 ≤ β * (n : ℝ))
      (hxi : x i = -(n : ℤ)) (hx : ∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) :
      x ∈ Q n i x ∧ Q n i x ⊆ centeredBox d n ∧ (∀ u ∈ Q n i x, u i ≤ -(n : ℤ) + h n) ∧
        F n i x ⊆ Q n i x ∧ (∀ w ∈ F n i x, w i = -(n : ℤ) + h n) ∧
        (∀ w ∈ F n i x, ∀ j, j ≠ i → |(w j : ℝ) - (x j : ℝ)| ≤ α * (n : ℝ) / 4) :=
    appendixWideBox_geometry i x hα1 (hwide n hlarge).2.1 (hwide n hlarge).2.2 hxi hx
  have hreg : ∃ creg : ℝ, 0 < creg ∧ ∀ (i : Fin d) (n : ℕ) (x : Vertex d),
      1 ≤ n → 16 ≤ β * (n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      creg / (n : ℝ) ≤ appendixBoxClusterMean (criticalPoint d) (Q n i x) x
        (fun U => ((U ∩ F n i x).card : ℝ)) := by
    refine ⟨(c / K) / 2, by positivity, ?_⟩
    intro i n x _hn hlarge _hxi _hx
    obtain ⟨hh, hhR, hR⟩ := hwide n hlarge
    have hh0 : (0 : ℝ) < h n := by exact_mod_cast (show 0 < h n by omega)
    have hhR' : (h n : ℝ) ≤ ((m * h n : ℕ) : ℝ) := by exact_mod_cast hhR
    have hhn : (h n : ℝ) ≤ n :=
      hhR'.trans (hR.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
    have htop' := appendixWideBox_face_mass_lower i (h n) (m * h n) x _ (htop i (h n) hh)
    calc
      _ ≤ ((c / K) / 2) / (h n : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hh0 hhn
      _ = (c / K) / (2 * (h n : ℝ)) := by rw [div_div]
      _ ≤ _ := htop'
  obtain ⟨Ke, hKe, herror⟩ := herr m hm
  obtain ⟨bL, hbL, r, _, hL⟩ := appendix_box_twopoint_lower_large_on_domain hd asymp lower
    hβ0 hβα hα1 Q F hgeom hreg
    ⟨Ke, hKe, fun i n r x hn hr hrh hlarge hxi hx => herror i n r x hn hr hlarge hxi hx hrh⟩
  obtain ⟨b, hb, hneg⟩ := appendix_box_twopoint_lower_negFace_of_large hd asymp hα0 hβ0 hbL r hL
  refine ⟨b, hb, ?_⟩
  intro i n x y hn hface hx hy
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : (1 : ℝ) - (d : ℝ) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    ring
  have hp : (n : ℝ) ^ ((1 : ℝ) - (d : ℝ)) = ((n : ℝ) ^ (d - 1))⁻¹ := by
    rw [he, Real.rpow_neg hn0.le, Real.rpow_natCast]
  rw [div_eq_mul_inv, ← hp]
  rcases hface with hxi | hxi
  · exact hneg i n x y hn hxi hx hy
  · have h := hneg i n (-x) (-y) hn (by simp [hxi])
      (fun j hj => by simpa using hx j hj) (fun j => by simpa using hy j)
    rwa [centeredBox_connection_inversion] at h

end NearCritical
