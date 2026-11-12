module
public import NearCritical.Section8LocalHalfSpaceGeometry
public import NearCritical.Section8CubeAllFaceMass
public import NearCritical.Section8CubeExitGeometry

/-! Actual local annulus prefix mass for the corrected RD decomposition. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- A radius strictly below the transverse gap retains just one inner face.
All cube faces are summed; no excluded-face containment is assumed. -/
theorem local_annulus_face_mass_le {d c t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ j : Fin d, HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin d, SlabBoundarySecondMomentUpper j B)
    (Q : Finset (Vertex d)) (w : Vertex d) (i : Fin d) (r s : ℤ)
    (hw : w ∈ heartAnnulus Q (centeredBox d c)) (hr : 0 ≤ r)
    (hts : (t : ℤ) < s) (hsc : s ≤ (c : ℤ))
    (hface : w i = (c : ℤ)+r)
    (htransverse : ∀ j : Fin d, j ≠ i → |w j| ≤ (c : ℤ)-s) :
    (∑ z ∈ (cubeCut (heartAnnulus Q (centeredBox d c)) w t).filter
        (fun z => ∃ j : Fin d, z j = w j+(t : ℤ) ∨ z j = w j-(t : ℤ)),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (cubeCut (heartAnnulus Q (centeredBox d c)) w t : Set (Vertex d)) w {z})) ≤
      (2*(d : ℝ))*((4*C*(A+B)*(9 : ℝ)^(d-1))*(1+(r : ℝ))/(t : ℝ)) := by
  let T := cubeCut (heartAnnulus Q (centeredBox d c)) w t
  have hwT : w ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨hw,?_⟩
    intro j
    constructor <;> omega
  have hTcube : ∀ z ∈ T, ∀ j, w j-(t : ℤ) ≤ z j ∧ z j ≤ w j+(t : ℤ) :=
    fun z hz => (Finset.mem_filter.mp hz).2
  have hD : (T : Set (Vertex d)) ⊆ coordinateHalfSpace i (c : ℤ) true := by
    intro z hz
    have hzAnn := (Finset.mem_filter.mp hz).1
    have hzQ := heartAnnulus_subset Q (centeredBox d c) hzAnn
    have hlocal : ∀ j : Fin d, |z j-w j| ≤ (t : ℤ) := by
      intro j
      have hb := hTcube z hz j
      apply abs_le.mpr
      constructor <;> omega
    have hzheight := (local_annulus_iff_halfSpace Q i w z r s (t : ℤ)
      hr (by omega) hts hsc hface htransverse hlocal hzQ).mp hzAnn
    have hzR : (c : ℝ) ≤ (z i : ℝ) := by exact_mod_cast hzheight
    change 0 ≤ coordinateDepth i (c : ℤ) true z
    simpa [coordinateDepth] using sub_nonneg.mpr hzR
  have hdepth : coordinateDepth i (c : ℤ) true w = (r : ℝ) := by
    simp [coordinateDepth,hface]
  have hp := cube_all_face_mass_le hd ht C A B hC hA hB panis T w hwT
    i (c : ℤ) true arm second hTcube hD
  rw [hdepth] at hp
  exact hp

/-- Half the integer transverse gap gives the source inverse-gap rate,
without requiring the root depth r to be smaller than that local radius. -/
theorem local_annulus_face_mass_le_gap {d c r s : ℕ} (hd : 1 ≤ d) (hs : 2 ≤ s)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ j : Fin d, HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin d, SlabBoundarySecondMomentUpper j B)
    (Q : Finset (Vertex d)) (w : Vertex d) (i : Fin d)
    (hw : w ∈ heartAnnulus Q (centeredBox d c)) (hsc : s ≤ c)
    (hface : w i = (c : ℤ)+(r : ℤ))
    (htransverse : ∀ j : Fin d, j ≠ i → |w j| ≤ (c : ℤ)-(s : ℤ)) :
    (∑ z ∈ (cubeCut (heartAnnulus Q (centeredBox d c)) w (s/2)).filter
        (fun z => ∃ j : Fin d, z j = w j+((s/2 : ℕ) : ℤ) ∨ z j = w j-((s/2 : ℕ) : ℤ)),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (cubeCut (heartAnnulus Q (centeredBox d c)) w (s/2) : Set (Vertex d)) w {z})) ≤
      (6*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(1+(r : ℝ))/(s : ℝ) := by
  have ht : 1 ≤ s/2 := by omega
  have hts : ((s/2 : ℕ) : ℤ) < (s : ℤ) := by omega
  have hp := local_annulus_face_mass_le hd ht C A B hC hA hB panis arm second Q w i
    (r : ℤ) (s : ℤ) hw (by omega) hts (by exact_mod_cast hsc) hface htransverse
  have htpos : (0 : ℝ) < ((s/2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < s/2 by omega)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hscale : (s : ℝ) ≤ 3*((s/2 : ℕ) : ℝ) := by
    exact_mod_cast (show s ≤ 3*(s/2) by omega)
  have hratio : (1 : ℝ)/((s/2 : ℕ) : ℝ) ≤ 3/(s : ℝ) := by
    apply (div_le_div_iff₀ htpos hspos).mpr
    simpa only [one_mul] using hscale
  calc
    _ ≤ _ := hp
    _ = ((2*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(1+(r : ℝ)))*
        (1/((s/2 : ℕ) : ℝ)) := by push_cast; ring
    _ ≤ ((2*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(1+(r : ℝ)))*(3/(s : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end NearCritical.Section8
