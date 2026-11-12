module

public import NearCritical.FiniteSlabDifferential
public import NearCritical.LatticeInversion
public import NearCritical.HalfSpaceSusceptibilityBounds

/-! Actual critical initial bounds for BOTH finite-cutoff boundary families.
The infinite-law changes of coordinates are proved, not finite-cutoff stationarity. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Inversion about the starting vertex turns a lower halfspace into the
literal source upper halfspace. All endpoints and nil paths are retained. -/
lemma upperHalfSpace_connection_probability {d : ℕ} (p : unitInterval) (i : Fin d)
    (h : ℤ) (x y : Vertex d) :
    percolation d p (connectionToSetEvent {z | z i ≤ h} x {y}) =
      percolation d p (connectionToSetEvent {z | x i - h ≤ z i} 0 {x - y}) := by
  have hneg : Neg.neg '' {z : Vertex d | z i ≤ h} = {z | -h ≤ z i} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change w i ≤ h at hw
      change -h ≤ -w i
      omega
    · intro hz
      refine ⟨-z, ?_, by simp⟩
      change -z i ≤ h
      change -h ≤ z i at hz
      omega
  have hinv := connectionToSet_probability_inversion p x {z | z i ≤ h} {y}
  have htrans := connectionToSet_probability_translation p x (-x) {z | -h ≤ z i} {-y}
  rw [hneg, Set.image_singleton] at hinv
  rw [translate_halfSpace, Set.image_singleton] at htrans
  have hs : {z : Vertex d | -h + x i ≤ z i} = {z | x i - h ≤ z i} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    omega
  simpa only [hs, add_neg_cancel, sub_eq_add_neg] using hinv.symm.trans htrans.symm

/-- Whole top-plane connection mass in a lower halfspace is exactly the
literal pioneer mass; this is an infinite-law identity, never a cutoff symmetry. -/
theorem upperHalfSpace_top_plane_mass {d : ℕ} (p : unitInterval) (i : Fin d)
    (h : ℤ) (x : Vertex d) :
    (∑' y : Vertex d, if y i = h then
      percolation d p (connectionToSetEvent {z | z i ≤ h} x {y}) else 0) =
      halfSpacePioneerMass p i (h - x i) := by
  rw [← (Equiv.neg (Vertex d)).tsum_eq]
  have hid := halfSpace_minimum_prefix_sum p i (-x) (-h)
  have hdom : Neg.neg '' {z : Vertex d | z i ≤ h} = {z | -h ≤ z i} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change w i ≤ h at hw
      change -h ≤ -w i
      omega
    · intro hz
      refine ⟨-z, ?_, by simp⟩
      change -z i ≤ h
      change -h ≤ z i at hz
      omega
  have heq : -(x i) - -h = h - x i := by omega
  rw [Pi.neg_apply, heq] at hid
  rw [← hid]
  apply tsum_congr
  intro y
  have hc : (-y) i = h ↔ y i = -h := by change -y i = h ↔ _; omega
  by_cases hy : y i = -h
  · simp only [Equiv.neg_apply, ite_eq_left hy, ite_eq_left (hc.mpr hy)]
    have hinv := connectionToSet_probability_inversion p x {z | z i ≤ h} {-y}
    simpa only [hdom, Set.image_singleton, neg_neg] using hinv.symm
  · simp only [Equiv.neg_apply, ite_eq_right hy, ite_eq_right (mt hc.mp hy)]

/-- Fixed top vertex to a lower plane: affine inversion gives the upper
halfspace prefix sum, which has already been identified with the pioneer mass. -/
theorem upperHalfSpace_boundary_plane_mass {d : ℕ} (p : unitInterval) (i : Fin d)
    (h r : ℤ) (z : Vertex d) (hz : z i = h) :
    (∑' y : Vertex d, if y i = r then
      percolation d p (connectionToSetEvent {w | w i ≤ h} z {y}) else 0) =
      halfSpacePioneerMass p i (h - r) := by
  rw [← (Equiv.addLeft z).tsum_eq]
  rw [← (Equiv.neg (Vertex d)).tsum_eq]
  rw [← halfSpace_prefix_sum p i (h-r)]
  apply tsum_congr
  intro y
  have hc : (z + -y) i = r ↔ y i = h-r := by
    change z i + -y i = r ↔ _
    omega
  by_cases hy : y i = h-r
  · simp only [Equiv.neg_apply, Equiv.coe_addLeft, ite_eq_left hy, ite_eq_left (hc.mpr hy)]
    have hp := upperHalfSpace_connection_probability p i h z (z + -y)
    have hd : {w : Vertex d | z i - h ≤ w i} = {w | 0 ≤ w i} := by rw [hz, sub_self]
    have he : z - (z + -y) = y := by abel
    rw [hd, he] at hp
    exact hp
  · simp only [Equiv.neg_apply, Equiv.coe_addLeft, ite_eq_right hy, ite_eq_right (mt hc.mp hy)]

/-- Actual finite-cutoff row is dominated by the corresponding whole-plane
mass in the containing lower halfspace. -/
lemma finiteSlabRowMean_ofReal_le_upper_plane {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m h : ℤ) (x : Vertex d) (r : ℤ) :
    ENNReal.ofReal (finiteSlabRowMean p U i m h x r) ≤
      ∑' y : Vertex d, if y i = r then
        percolation d p (connectionToSetEvent {z | z i ≤ h} x {y}) else 0 := by
  unfold finiteSlabRowMean
  rw [ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ by split_ifs <;> positivity)]
  calc
    _ ≤ ∑ y ∈ U, if y i = r then
        percolation d p (connectionToSetEvent {z | z i ≤ h} x {y}) else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hyr : y i = r
      · simp only [ite_eq_left hyr]
        rw [ofReal_measureReal]
        apply measure_mono
        apply connectionToSetEvent_mono (fun z hz ↦ hz.1.2) (Subset.refl _) x
      · simp only [ite_eq_right hyr, ENNReal.ofReal_zero]
        exact le_rfl
    _ ≤ _ := ENNReal.sum_le_tsum _

lemma finiteSlab_forward_ofReal_le_pioneer {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m h : ℤ) (x : Vertex d) :
    ENNReal.ofReal (finiteSlabRowMean p U i m h x h) ≤
      halfSpacePioneerMass p i (h - x i) := by
  exact (finiteSlabRowMean_ofReal_le_upper_plane p U i m h x h).trans_eq
    (upperHalfSpace_top_plane_mass p i h x)

lemma finiteSlab_backward_ofReal_le_pioneer {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m h r : ℤ) (z : Vertex d) (hz : z i = h) :
    ENNReal.ofReal (finiteSlabColumnMean p U i m h r z) ≤
      halfSpacePioneerMass p i (h-r) := by
  rw [finiteSlabColumnMean_eq_rowMean]
  exact (finiteSlabRowMean_ofReal_le_upper_plane p U i m h z r).trans_eq
    (upperHalfSpace_boundary_plane_mass p i h r z hz)

/-- Literal weighted positive-height input, together with the PROVED zero-layer
inequality, bounds every actual forward row at the critical point. -/
theorem finiteSlab_forward_critical_le {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (m h : ℤ) (x : Vertex d) {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hpc : 0 < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    finiteSlabRowMean (criticalPoint d) U i m h x h ≤ 4*C/(criticalPoint d : ℝ)^2 := by
  have hK : 0 ≤ 4*C/(criticalPoint d : ℝ)^2 := by positivity
  by_cases hx : x i ≤ h
  · have hd : ((h-x i).toNat : ℤ) = h-x i := Int.toNat_of_nonneg (by omega)
    have hu := halfSpace_pioneer_uniform_of_weighted (criticalPoint d) i hC hc hpc
      (by linarith : (criticalPoint d : ℝ)/2 ≤ (criticalPoint d : ℝ)) decay (h-x i).toNat
    rw [hd] at hu
    have hb := (finiteSlab_forward_ofReal_le_pioneer (criticalPoint d) U i m h x).trans hu
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [ENNReal.toReal_ofReal (finiteSlabRowMean_nonneg _ U i m h x h),
      ENNReal.toReal_ofReal hK] using hr
  · have hout : x ∉ finiteHeightSlab i m h ∩ (U : Set (Vertex d)) := fun hxS ↦ hx hxS.1.2
    have he (y : Vertex d) := finiteSlabConnectionEvent_empty_of_start_outside U i m h x y hout
    simpa only [finiteSlabRowMean, he, measureReal_empty, ite_self, Finset.sum_const_zero] using hK

/-- The separate fixed-top backward column has the SAME critical bound,
proved via its actual whole-plane comparison rather than cutoff stationarity. -/
theorem finiteSlab_backward_critical_le {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (m h r : ℤ) (z : Vertex d) (hz : z i = h) (hr : r ≤ h)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    finiteSlabColumnMean (criticalPoint d) U i m h r z ≤ 4*C/(criticalPoint d : ℝ)^2 := by
  have hK : 0 ≤ 4*C/(criticalPoint d : ℝ)^2 := by positivity
  have hd : ((h-r).toNat : ℤ) = h-r := Int.toNat_of_nonneg (by omega)
  have hu := halfSpace_pioneer_uniform_of_weighted (criticalPoint d) i hC hc hpc
    (by linarith : (criticalPoint d : ℝ)/2 ≤ (criticalPoint d : ℝ)) decay (h-r).toNat
  rw [hd] at hu
  have hb := (finiteSlab_backward_ofReal_le_pioneer (criticalPoint d) U i m h r z hz).trans hu
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal (finiteSlabColumnMean_nonneg _ U i m h r z),
    ENNReal.toReal_ofReal hK] using ht

/-- Initial bound for EVERY coordinate of the visible actual finite family,
uniform in cutoff U and slab endpoints m,N. Only the literal weighted cited
pioneer input is a probability hypothesis; zero-layer control is proved. -/
theorem finiteSlabBoundaryFamily_critical_le {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m N : ℤ) (a : FiniteSlabBoundaryIndex U i m N)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    finiteSlabBoundaryFamily U i m N a (criticalPoint d : ℝ) ≤ 4*C/(criticalPoint d : ℝ)^2 := by
  cases a with
  | inl _ => change 0 ≤ _; positivity
  | inr a =>
    cases a with
    | inl v =>
      change finiteSlabRowExpectation _ U i m v.1.val v.2.val v.1.val ≤ _
      rw [← finiteSlabRowMean_eq_expectation]
      exact finiteSlab_forward_critical_le U i m v.1.val v.2.val hC hc hpc decay
    | inr v =>
      change finiteSlabColumnExpectation _ U i m v.1.val v.2.2.val v.2.1.val.val ≤ _
      rw [← finiteSlabColumnMean_eq_expectation]
      exact finiteSlab_backward_critical_le U i m v.1.val v.2.2.val v.2.1.val.val
        v.2.1.property (Finset.mem_Icc.mp v.2.2.property).2 hC hc hpc decay

/-- The critical finite maximum is bounded BEFORE choosing any cutoff or height. -/
theorem finiteSlabBoundaryMaximum_critical_le {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m N : ℤ) {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hpc : 0 < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    finiteSlabBoundaryMaximum (criticalPoint d : ℝ) U i m N ≤ 4*C/(criticalPoint d : ℝ)^2 :=
  finiteFamilyMaximum_le _ _ _ (fun a ↦ finiteSlabBoundaryFamily_critical_le U i m N a hC hc hpc decay)

/-- A single positive critical initial bound is chosen BEFORE all finite
cutoffs and slab heights, as required by the later finite-family bootstrap. -/
theorem finiteSlabBoundaryMaximum_critical_uniform {d : ℕ} (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (U : Finset (Vertex d)) (m N : ℤ),
      finiteSlabBoundaryMaximum (criticalPoint d : ℝ) U i m N ≤ K := by
  refine ⟨4*C/(criticalPoint d : ℝ)^2, by positivity, ?_⟩
  intro U m N
  exact finiteSlabBoundaryMaximum_critical_le U i m N hC hc hpc decay

end NearCritical
