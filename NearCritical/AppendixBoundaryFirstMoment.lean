module

public import NearCritical.AppendixBoundaryTopFace
public import NearCritical.Section8EnergyMeanScale
public import NearCritical.Section8FirstExit
public import NearCritical.Section10BoxFaceFromPioneer
public import NearCritical.SlabPioneerConvolution

/-! The Appendix A lower bound for the nonbottom boundary mass of a slab box. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set Section8
open scoped Classical ENNReal

private theorem slab_box_entry_mem_boundaryHat {d : ℕ} (i : Fin d)
    {h R : ℕ} (hhR : h ≤ R) {ω : Configuration d} {v w : Vertex d}
    (hv : v ∈ boundaryBox i h R \ boundaryHat i h R)
    (hw : w ∈ finiteHeightSlab i 0 (h : ℤ))
    (hwout : w ∉ boundaryBox i h R \ boundaryHat i h R)
    (hvw : (openGraph ω).Adj v w) :
    w ∈ boundaryHat i h R := by
  obtain ⟨hvB, hvF⟩ := Finset.mem_sdiff.mp hv
  have hmem : w ∈ boundaryBox i h R := by
    have hw' : (0 : ℤ) ≤ w i ∧ w i ≤ (h : ℤ) := hw
    refine Finset.mem_filter.mpr ⟨mem_centeredBox.mpr ?_, hw'⟩
    intro j
    by_cases hj : j = i
    · subst j
      have hhR' : (h : ℤ) ≤ R := by exact_mod_cast hhR
      constructor <;> omega
    · have hvj := mem_centeredBox.mp (Finset.mem_filter.mp hvB).1 j
      have hvneq : ¬ (v j = (R : ℤ) ∨ v j = -(R : ℤ)) :=
        fun he => hvF (Finset.mem_filter.mpr ⟨hvB, Or.inr ⟨j, hj, he⟩⟩)
      have hadj := openGraph_adj_height_bounds hvw j
      constructor <;> omega
  by_contra hout
  exact hwout (Finset.mem_sdiff.mpr ⟨hmem, hout⟩)

/-- First hit of the nonbottom boundary, with the crossing edge assigned to
the prefix. The suffix can use the whole slab. -/
theorem slab_box_boundary_first_hit_bk {d : ℕ} (p : unitInterval) (i : Fin d)
    {h R : ℕ} (hh : 1 ≤ h) (hhR : h ≤ R) (y : Vertex d) (hy : y i = (h : ℤ)) :
    percolation d p (connectionToSetEvent (finiteHeightSlab i 0 (h : ℤ)) 0 {y}) ≤
      ∑ z ∈ boundaryHat i h R,
        percolation d p (connectionToSetEvent (boundaryBox i h R : Set (Vertex d)) 0 {z}) *
        percolation d p (connectionToSetEvent (finiteHeightSlab i 0 (h : ℤ)) z {y}) := by
  let S := finiteHeightSlab i 0 (h : ℤ)
  let B := boundaryBox i h R
  let F := boundaryHat i h R
  let D := B \ F
  let E (z : F) : Set (Configuration d) := {ω | DisjointOccurrence
    (connectionToSetEvent (B : Set (Vertex d)) 0 {(z : Vertex d)})
    (connectionToSetEvent S (z : Vertex d) {y}) ω}
  have hxD : (0 : Vertex d) ∈ D := by
    have h0B : (0 : Vertex d) ∈ B :=
      Finset.mem_filter.mpr ⟨mem_centeredBox.mpr (fun _ => by simp),
        by simp⟩
    refine Finset.mem_sdiff.mpr ⟨h0B, ?_⟩
    intro h0F
    have hR : 1 ≤ R := hh.trans hhR
    rcases (Finset.mem_filter.mp h0F).2 with he | ⟨k, _, he | he⟩ <;>
      simp only [Pi.zero_apply] at he <;> omega
  have hyD : y ∉ D := by
    intro hm
    obtain ⟨hyB, hyF⟩ := Finset.mem_sdiff.mp hm
    exact hyF (Finset.mem_filter.mpr ⟨hyB, Or.inl hy⟩)
  have hcover : connectionToSetEvent S 0 {y} ⊆ ⋃ z : F, E z := by
    intro ω hω
    obtain ⟨h0S, v, hv, _, ⟨w⟩⟩ := hω
    have hvy : v = y := hv
    subst v
    have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ ha => ha.1
    let r : (openGraph ω).Walk 0 y := w.toPath.val.mapLe hle
    have hr : r.IsPath := w.toPath.property.mapLe _
    have hrS : ∀ z ∈ r.support, z ∈ S := by
      simpa only [r, SimpleGraph.Walk.support_mapLe_eq_support] using
        restrictedWalk_support w.toPath.val h0S
    obtain ⟨z, u, hzu, a, b, hz, hu, hab, ha⟩ :=
      walk_first_exit (D : Set (Vertex d)) r hxD hyD
    have hab' : (a.concat hzu).append b = r := by
      simpa only [SimpleGraph.Walk.concat_append] using hab
    have hbS : ∀ z ∈ b.support, z ∈ S := by
      intro v hv
      apply hrS v
      rw [← hab']
      exact (a.concat hzu).support_subset_support_append_right b hv
    have huF : u ∈ F :=
      slab_box_entry_mem_boundaryHat i hhR hz (hbS u b.start_mem_support) hu hzu
    have haB : ∀ z ∈ (a.concat hzu).support, z ∈ B := by
      intro v hv
      rw [SimpleGraph.Walk.support_concat] at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact (Finset.mem_sdiff.mp (ha v hv)).1
      · have hvu : v = u := by simpa only [List.mem_singleton] using hv
        subst v
        exact (Finset.mem_filter.mp huF).1
    have hdis : (a.concat hzu).edges.Disjoint b.edges :=
      ((SimpleGraph.Walk.isTrail_append (a.concat hzu) b).mp (hab'.symm ▸ hr.isTrail)).2.2
    exact Set.mem_iUnion.mpr ⟨⟨u, huF⟩,
      disjointOpenWalks_occurrence (a.concat hzu) b hdis
        (B : Set (Vertex d)) S {u} {y} haB hbS rfl rfl⟩
  calc
    _ ≤ percolation d p (⋃ z : F, E z) := measure_mono hcover
    _ ≤ ∑' z : F, percolation d p (E z) := measure_iUnion_le _
    _ = ∑ z : F, percolation d p (E z) := tsum_fintype _
    _ ≤ ∑ z : F, percolation d p (connectionToSetEvent (B : Set (Vertex d)) 0 {(z : Vertex d)}) *
        percolation d p (connectionToSetEvent S (z : Vertex d) {y}) := by
      exact Finset.sum_le_sum fun z _ => connectionToSet_bk_ennreal p _ _ _ _ _ _
    _ = _ := Finset.sum_coe_sort F (fun z : Vertex d =>
      percolation d p (connectionToSetEvent (B : Set (Vertex d)) 0 {z}) *
        percolation d p (connectionToSetEvent S z {y}))

private theorem slab_top_suffix_mass_le {d : ℕ} (i : Fin d) {K : ℝ}
    (hpioneer : ∀ m : ℕ, halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K)
    (h : ℕ) (z : Vertex d) (hz : z i ≤ (h : ℤ)) :
    (∑' y : Vertex d, if y i = (h : ℤ) then
      percolation d (criticalPoint d) (connectionToSetEvent (finiteHeightSlab i 0 (h : ℤ)) z {y})
      else 0) ≤ ENNReal.ofReal K := by
  let p := criticalPoint d
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro U
  rw [← Finset.sum_filter]
  let T := U.filter (fun y : Vertex d => y i = (h : ℤ))
  have hs : finiteHeightSlab i 0 (h : ℤ) ⊆ {w | w i ≤ (h : ℤ)} := fun _ hw => hw.2
  have hneg (y : Vertex d) :
      percolation d p (connectionToSetEvent {w | w i ≤ (h : ℤ)} z {y}) =
        percolation d p (connectionToSetEvent {w | -(h : ℤ) ≤ w i} (-z) {-y}) := by
    have hinv := connectionToSet_probability_inversion p z {w : Vertex d | w i ≤ (h : ℤ)} {y}
    rw [Section10.neg_image_upper_halfSpace, Set.image_singleton] at hinv
    exact hinv.symm
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le
    (show 0 ≤ (-z) i - -(h : ℤ) by rw [Pi.neg_apply]; omega)
  change (∑ y ∈ T, _) ≤ _
  calc
    _ ≤ ∑ y ∈ T, percolation d p (connectionToSetEvent {w | w i ≤ (h : ℤ)} z {y}) :=
      Finset.sum_le_sum fun _ _ => measure_mono (connectionToSetEvent_mono hs subset_rfl z)
    _ = ∑ y ∈ T.image Neg.neg, percolation d p (connectionToSetEvent {w | -(h : ℤ) ≤ w i} (-z) {y}) := by
      rw [Finset.sum_image (fun _ _ _ _ he => neg_injective he)]
      exact Finset.sum_congr rfl fun y _ => hneg y
    _ ≤ halfSpacePioneerMass p i ((-z) i - -(h : ℤ)) :=
      Section10.halfSpace_face_sum_le_pioneer p i _ (-z) _ (fun y hy => by
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
        rw [Pi.neg_apply, (Finset.mem_filter.mp hw).2])
    _ ≤ _ := by rw [hm]; exact hpioneer m

/-- Source `lem.boundary_firstmoment`. The lower slab mass and the uniform
critical pioneer bound are the two cited inputs. The box keeps its actual
slab geometry, including the omitted bottom face. -/
theorem boundary_hat_mass_lower {d : ℕ} (i : Fin d) {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hslab : ∀ h : ℕ, 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ m : ℕ, halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K)
    (h R : ℕ) (hh : 1 ≤ h) (hhR : h ≤ R) :
    (c / K) / (h : ℝ) ≤ ∑ z ∈ boundaryHat i h R, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (boundaryBox i h R : Set (Vertex d)) 0 {z}) := by
  let p := criticalPoint d
  let S := finiteHeightSlab i 0 (h : ℤ)
  let F := boundaryHat i h R
  let P (z : Vertex d) := percolation d p
    (connectionToSetEvent (boundaryBox i h R : Set (Vertex d)) 0 {z})
  let f (z y : Vertex d) := if y i = (h : ℤ) then
    percolation d p (connectionToSetEvent S z {y}) else 0
  have hbound : slabPioneerMass p i 0 (h : ℤ) 0 (h : ℤ) ≤ (∑ z ∈ F, P z) * ENNReal.ofReal K := by
    calc
      _ ≤ ∑' y, ∑ z ∈ F, P z * f z y := by
        unfold slabPioneerMass
        apply ENNReal.tsum_le_tsum
        intro y
        by_cases hy : y i = (h : ℤ)
        · simpa only [P, f, S, F, ite_eq_left hy, Pi.single_zero] using
            slab_box_boundary_first_hit_bk p i hh hhR y hy
        · simp only [hy, ite_false, zero_le]
      _ = ∑ z ∈ F, P z * (∑' y, f z y) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact Finset.sum_congr rfl fun z _ => ENNReal.tsum_mul_left
      _ ≤ ∑ z ∈ F, P z * ENNReal.ofReal K := by
        apply Finset.sum_le_sum
        intro z hz
        have hz' := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2.2
        exact mul_le_mul' le_rfl (slab_top_suffix_mass_le i hpioneer h z hz')
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hP (z : Vertex d) : P z ≠ ∞ := measure_ne_top _ _
  have hfinite : (∑ z ∈ F, P z) * ENNReal.ofReal K ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.sum_ne_top.mpr (fun z _ => hP z)) ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono hfinite ((hslab h hh).trans hbound)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ c / (h : ℝ)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le,
    ENNReal.toReal_sum (fun z _ => hP z)] at hr
  calc
    (c / K) / (h : ℝ) = (c / (h : ℝ)) / K := by ring
    _ ≤ _ := (div_le_iff₀ hK).mpr hr

/-- A fixed integer aspect ratio makes the top-face mass uniformly of order
the inverse height. The same aspect ratio works for every height. -/
theorem boundary_top_mass_lower_of_pioneer {d : ℕ} (hd : 2 ≤ d) {A B C c K : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ), halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ (i : Fin d) (h : ℕ), 1 ≤ h →
      (c / K) / (2 * (h : ℝ)) ≤ ∑ z ∈ boundaryTop i h (m * h),
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (boundaryBox i h (m * h) : Set (Vertex d)) 0 {z}) := by
  let U : ℝ := ((d - 1 : ℕ) : ℝ) * (8 * (3 : ℝ) ^ (d - 2) * (2 : ℝ) ^ d * C) * (A + B)
  obtain ⟨m₀, _, hm₀⟩ := exists_inv_nat_pow_threshold (k := 2) (by omega)
    U ((c / K) / 2) (by dsimp [U]; positivity) (by positivity)
  let m := max 2 m₀
  have hm2 : 2 ≤ m := le_max_left _ _
  refine ⟨m, hm2, ?_⟩
  intro i h hh
  let R := m * h
  have hhR : h < R := by dsimp [R]; nlinarith
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (hh.trans hhR.le)
  have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hR : (R : ℝ) = (m : ℝ) * (h : ℝ) := by simp [R]
  have hhalf : (R : ℝ) / 2 ≤ (R : ℝ) - (h : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hm2' (show (0 : ℝ) ≤ h by positivity)
    linarith
  have hpos : (0 : ℝ) < (R : ℝ) / 2 := by linarith
  have hprod : ((h : ℝ) + 1) * (2 * (R : ℝ) + 1) ^ (d - 2) *
      (C * (1 + (h : ℝ)) / ((R : ℝ) - h) ^ d) ≤
      (4 * (3 : ℝ) ^ (d - 2) * (2 : ℝ) ^ d * C) / (m : ℝ) ^ 2 := by
    have hnum : ((h : ℝ) + 1) * (2 * (R : ℝ) + 1) ^ (d - 2) ≤
        (2 * (h : ℝ)) * (3 * (R : ℝ)) ^ (d - 2) :=
      mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (by positivity)
    have hfrac : C * (1 + (h : ℝ)) / ((R : ℝ) - h) ^ d ≤
        C * (2 * (h : ℝ)) / ((R : ℝ) / 2) ^ d := by
      have hden : 0 < (R : ℝ) - (h : ℝ) := hpos.trans_le hhalf
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC)
        (pow_nonneg hden.le _)).trans
          (div_le_div_of_nonneg_left (by positivity) (pow_pos hpos _)
            (pow_le_pow_left₀ hpos.le hhalf _))
    calc
      _ ≤ (2 * (h : ℝ)) * (3 * (R : ℝ)) ^ (d - 2) *
          (C * (2 * (h : ℝ)) / ((R : ℝ) / 2) ^ d) :=
        mul_le_mul hnum hfrac (div_nonneg (by positivity) (pow_nonneg (hpos.trans_le hhalf).le _))
          (by positivity)
      _ = _ := by
        have hpow : (R : ℝ) ^ d = (R : ℝ) ^ (d - 2) * (R : ℝ) ^ 2 := by
          rw [← pow_add, show d - 2 + 2 = d by omega]
        rw [mul_pow, div_pow, hpow]
        have hR0 : (R : ℝ) ≠ 0 := by linarith
        have hm0 : (m : ℝ) ≠ 0 := by linarith
        field_simp [hR0, hm0]
        rw [hR]
        ring
  have hwide : ((d - 1 : ℕ) : ℝ) * (2 * ((((h + 1) * (2 * R + 1) ^ (d - 2) : ℕ) : ℝ) *
      (C * (1 + (h : ℝ)) / ((R : ℝ) - h) ^ d))) * ((A + B) / (h : ℝ)) ≤
      (c / K) / (2 * (h : ℝ)) := by
    push_cast
    calc
      _ ≤ ((d - 1 : ℕ) : ℝ) *
          (2 * ((4 * (3 : ℝ) ^ (d - 2) * (2 : ℝ) ^ d * C) / (m : ℝ) ^ 2)) *
          ((A + B) / (h : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (by norm_num)) (by positivity))
          (by positivity)
      _ = (U / (m : ℝ) ^ 2) / (h : ℝ) := by dsimp [U]; ring
      _ ≤ ((c / K) / 2) / (h : ℝ) :=
        div_le_div_of_nonneg_right (hm₀ m (le_max_right _ _)) (by positivity)
      _ = _ := by rw [div_div]
  exact top_face_mass_lower_of_wide i hA hB hC (arm i) (second i) panis h R hh hhR
    (boundary_hat_mass_lower i hc hK (hslab i) (hpioneer i) h R hh hhR.le)
    (by simpa only [mul_assoc] using hwide)

end NearCritical
