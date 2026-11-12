module

public import NearCritical.FiniteSlabConvolution
public import NearCritical.FinitePivotalAvoidance
public import NearCritical.LatticeRusso
public import NearCritical.FiniteFamilyCubicBootstrap

/-! NEW actual finite-slab Russo bounds. Opening support, closed-edge factor
cancellation and BK are proved for the canonical finite-cutoff events. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory BernoulliCalculus
open scoped Classical

/-- Transport actual physical opening support to the internal-bond coordinates
of the canonical cutoff model, retaining the old closed bit and tested-edge-free
finite forcing witnesses in both physical orientations. -/
theorem finiteSlab_local_opening_avoiding_support {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) (e : internalBondSet U)
    (η : (j : internalBondSet U) → Bool)
    (hnew : forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y)
    (hold : η ∉ finiteSlabLocalConnectionEvent U i m n x y) :
    η e = false ∧
      (AvoidingDisjointOccurrence e (finiteSlabLocalConnectionEvent U i m n x e.val.1)
        (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y) η ∨
       AvoidingDisjointOccurrence e (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
        (finiteSlabLocalConnectionEvent U i m n e.val.1 y) η) := by
  let s := internalBondSet U
  let ω := extendConfiguration s (fun _ ↦ false) η
  have hrestrict : s.restrict ω = η := restrict_extendConfiguration s _ η
  have hopenRestr : s.restrict (forceOpen e.val ω) = forceOpen e η := by
    rw [forceOpen_eq_update, restrict_update_bond, hrestrict]
  have hnewg : forceOpen e.val ω ∈ finiteSlabConnectionEvent U i m n x y := by
    rw [finiteSlabConnectionEvent_eq_preimage]
    change s.restrict (forceOpen e.val ω) ∈ finiteSlabLocalConnectionEvent U i m n x y
    rw [hopenRestr]
    exact hnew
  have holdg : ω ∉ finiteSlabConnectionEvent U i m n x y := by
    intro h
    rw [finiteSlabConnectionEvent_eq_preimage] at h
    exact hold (hrestrict ▸ h)
  obtain ⟨hclosed, hav⟩ := opening_connection_avoiding_support
    (finiteHeightSlab i m n ∩ (U : Set (Vertex d))) x y e.val ω hnewg holdg
  have hclosedLocal : η e = false := by
    have heval : ω e.val = η e := by simp [ω, s, extendConfiguration, e.property]
    exact heval.symm.trans hclosed
  have htransport {a b c z : Vertex d}
      (h : AvoidingDisjointOccurrence e.val (finiteSlabConnectionEvent U i m n a b)
        (finiteSlabConnectionEvent U i m n c z) ω) :
      AvoidingDisjointOccurrence e (finiteSlabLocalConnectionEvent U i m n a b)
        (finiteSlabLocalConnectionEvent U i m n c z) η := by
    rw [finiteSlabConnectionEvent_eq_preimage, finiteSlabConnectionEvent_eq_preimage] at h
    have hlocal := (avoidingDisjointOccurrence_restrict_iff s e
      (finiteSlabLocalConnectionEvent U i m n a b)
      (finiteSlabLocalConnectionEvent U i m n c z) ω).mpr h
    exact hrestrict ▸ hlocal
  exact ⟨hclosedLocal, hav.elim (fun h ↦ Or.inl (htransport h)) (fun h ↦ Or.inr (htransport h))⟩

private lemma finiteSlab_opening_indicator_le {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) (e : internalBondSet U)
    (η : (j : internalBondSet U) → Bool) :
    (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y then (1 : ℝ) else 0) -
      (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0) ≤
    (if η e then 0 else 1) * (if AvoidingDisjointOccurrence e
      (finiteSlabLocalConnectionEvent U i m n x e.val.1)
      (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y) η then 1 else 0) +
    (if η e then 0 else 1) * (if AvoidingDisjointOccurrence e
      (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
      (finiteSlabLocalConnectionEvent U i m n e.val.1 y) η then 1 else 0) := by
  let g1 : ℝ := (if η e then 0 else 1) * (if AvoidingDisjointOccurrence e
    (finiteSlabLocalConnectionEvent U i m n x e.val.1)
    (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y) η then 1 else 0)
  let g2 : ℝ := (if η e then 0 else 1) * (if AvoidingDisjointOccurrence e
    (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
    (finiteSlabLocalConnectionEvent U i m n e.val.1 y) η then 1 else 0)
  change _ ≤ g1 + g2
  have hg1 : 0 ≤ g1 := by dsimp [g1]; split_ifs <;> norm_num
  have hg2 : 0 ≤ g2 := by dsimp [g2]; split_ifs <;> norm_num
  by_cases hnew : forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y
  · by_cases hold : η ∈ finiteSlabLocalConnectionEvent U i m n x y
    · simp only [ite_eq_left hnew, ite_eq_left hold, sub_self]
      exact add_nonneg hg1 hg2
    · obtain ⟨hclosed, hav⟩ := finiteSlab_local_opening_avoiding_support U i m n x y e η hnew hold
      rcases hav with ha | hb
      · have heq : g1 = 1 := by simp [g1, hclosed, ha]
        rw [ite_eq_left hnew, ite_eq_right hold, heq]
        linarith
      · have heq : g2 = 1 := by simp [g2, hclosed, hb]
        rw [ite_eq_left hnew, ite_eq_right hold, heq]
        linarith
  · by_cases hold : η ∈ finiteSlabLocalConnectionEvent U i m n x y
    · simp only [ite_eq_right hnew, ite_eq_left hold]
      linarith
    · simp only [ite_eq_right hnew, ite_eq_right hold, sub_self]
      exact add_nonneg hg1 hg2

/-- The actual per-connection opening contribution has no (1-p) loss: the
closed factor cancels by genuine tested-edge-free Mecke before applying BK. -/
theorem finiteSlab_opening_expectation_le {d : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x y : Vertex d) (e : internalBondSet U) :
    (1 - (p : ℝ))⁻¹ * finiteExpectation (p : ℝ) (fun η ↦
      (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y then (1 : ℝ) else 0) -
        (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0)) ≤
      (percolation d p).real (finiteSlabConnectionEvent U i m n x e.val.1) *
        (percolation d p).real (finiteSlabConnectionEvent U i m n (bondTip e.val) y) +
      (percolation d p).real (finiteSlabConnectionEvent U i m n x (bondTip e.val)) *
        (percolation d p).real (finiteSlabConnectionEvent U i m n e.val.1 y) := by
  let g1 := fun η : (j : internalBondSet U) → Bool ↦ (if η e then (0 : ℝ) else 1) *
    (if AvoidingDisjointOccurrence e (finiteSlabLocalConnectionEvent U i m n x e.val.1)
      (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y) η then 1 else 0)
  let g2 := fun η : (j : internalBondSet U) → Bool ↦ (if η e then (0 : ℝ) else 1) *
    (if AvoidingDisjointOccurrence e (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
      (finiteSlabLocalConnectionEvent U i m n e.val.1 y) η then 1 else 0)
  have hmono := finiteExpectation_mono p.2.1 p.2.2 (fun η ↦
    finiteSlab_opening_indicator_le U i m n x y e η)
  have hadd : finiteExpectation (p : ℝ) (fun η ↦ g1 η + g2 η) =
      finiteExpectation (p : ℝ) g1 + finiteExpectation (p : ℝ) g2 := by
    simp only [finiteExpectation, add_mul, Finset.sum_add_distrib]
  have hprob (a b : Vertex d) : BK.eventProbability (p : ℝ)
      (finiteSlabLocalConnectionEvent U i m n a b) =
        (percolation d p).real (finiteSlabConnectionEvent U i m n a b) :=
    (finiteSlabConnectionEvent_probability p U i m n a b).symm
  calc
    _ ≤ (1 - (p : ℝ))⁻¹ * finiteExpectation (p : ℝ) (fun η ↦ g1 η + g2 η) :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (sub_nonneg.mpr p.2.2))
    _ = (1 - (p : ℝ))⁻¹ * finiteExpectation (p : ℝ) g1 +
        (1 - (p : ℝ))⁻¹ * finiteExpectation (p : ℝ) g2 := by rw [hadd, mul_add]
    _ ≤ _ := by
      have h1 := finite_avoiding_russo_bk p hp e
        (finiteSlabLocalConnectionEvent U i m n x e.val.1)
        (finiteSlabLocalConnectionEvent U i m n (bondTip e.val) y)
        (finiteSlabLocalConnectionEvent_increasing U i m n x e.val.1)
        (finiteSlabLocalConnectionEvent_increasing U i m n (bondTip e.val) y)
      have h2 := finite_avoiding_russo_bk p hp e
        (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val))
        (finiteSlabLocalConnectionEvent U i m n e.val.1 y)
        (finiteSlabLocalConnectionEvent_increasing U i m n x (bondTip e.val))
        (finiteSlabLocalConnectionEvent_increasing U i m n e.val.1 y)
      simpa only [hprob] using add_le_add h1 h2

private lemma finiteSlab_expectation_finsetSum {E Y : Type*} [Fintype E]
    (q : ℝ) (U : Finset Y) (g : Y → (E → Bool) → ℝ) :
    finiteExpectation q (fun η ↦ ∑ y ∈ U, g y η) = ∑ y ∈ U, finiteExpectation q (g y) := by
  simp only [finiteExpectation, Finset.sum_mul]
  exact Finset.sum_comm

private lemma finiteSlabRowObservable_opening {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) (e : internalBondSet U)
    (η : (k : internalBondSet U) → Bool) :
    finiteSlabRowObservable U i m n x j (forceOpen e η) - finiteSlabRowObservable U i m n x j η =
      ∑ y ∈ U, if y i = j then
        (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y then (1 : ℝ) else 0) -
          (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0) else 0 := by
  unfold finiteSlabRowObservable
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y i = j <;> simp [hy]

/-- Sum the proved per-connection estimate over the actual target plane. -/
theorem finiteSlab_row_opening_expectation_le {d : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) (e : internalBondSet U) :
    (1 - (p : ℝ))⁻¹ * finiteExpectation (p : ℝ) (fun η ↦
      finiteSlabRowObservable U i m n x j (forceOpen e η) - finiteSlabRowObservable U i m n x j η) ≤
      (percolation d p).real (finiteSlabConnectionEvent U i m n x e.val.1) *
        finiteSlabRowMean p U i m n (bondTip e.val) j +
      (percolation d p).real (finiteSlabConnectionEvent U i m n x (bondTip e.val)) *
        finiteSlabRowMean p U i m n e.val.1 j := by
  calc
    _ = ∑ y ∈ U, if y i = j then (1 - (p : ℝ))⁻¹ * finiteExpectation (p : ℝ) (fun η ↦
        (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y then (1 : ℝ) else 0) -
          (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0)) else 0 := by
      simp_rw [finiteSlabRowObservable_opening]
      rw [finiteSlab_expectation_finsetSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y i = j
      · simp only [ite_eq_left hy]
      · simp only [ite_eq_right hy, finiteExpectation, zero_mul, Finset.sum_const_zero, mul_zero]
    _ ≤ ∑ y ∈ U, if y i = j then
        (percolation d p).real (finiteSlabConnectionEvent U i m n x e.val.1) *
          (percolation d p).real (finiteSlabConnectionEvent U i m n (bondTip e.val) y) +
        (percolation d p).real (finiteSlabConnectionEvent U i m n x (bondTip e.val)) *
          (percolation d p).real (finiteSlabConnectionEvent U i m n e.val.1 y) else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y i = j
      · rw [ite_eq_left hy, ite_eq_left hy]
        exact finiteSlab_opening_expectation_le p hp U i m n x y e
      · simp only [ite_eq_right hy, le_refl]
    _ = _ := by
      unfold finiteSlabRowMean
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y i = j <;> simp [hy]

/-- Actual truncated row Russo differential, with both physical orientations
and no assumed pivotal-support or derivative inequality. -/
theorem finiteSlabRowExpectation_deriv_le {d : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    deriv (fun q ↦ finiteSlabRowExpectation q U i m n x j) (p : ℝ) ≤
      ∑ e : internalBondSet U,
        ((percolation d p).real (finiteSlabConnectionEvent U i m n x e.val.1) *
          finiteSlabRowMean p U i m n (bondTip e.val) j +
        (percolation d p).real (finiteSlabConnectionEvent U i m n x (bondTip e.val)) *
          finiteSlabRowMean p U i m n e.val.1 j) := by
  rw [(finiteSlabRowExpectation_russo (p : ℝ) hp U i m n x j).deriv, Finset.mul_sum]
  exact Finset.sum_le_sum (fun e _ ↦ finiteSlab_row_opening_expectation_le p hp U i m n x j e)

/-- Backward columns use the SAME actual event and polynomial extension. -/
theorem finiteSlabColumnExpectation_deriv_le {d : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m n k : ℤ) (y : Vertex d) :
    deriv (fun q ↦ finiteSlabColumnExpectation q U i m n k y) (p : ℝ) ≤
      ∑ e : internalBondSet U,
        ((percolation d p).real (finiteSlabConnectionEvent U i m n y e.val.1) *
          finiteSlabRowMean p U i m n (bondTip e.val) k +
        (percolation d p).real (finiteSlabConnectionEvent U i m n y (bondTip e.val)) *
          finiteSlabRowMean p U i m n e.val.1 k) :=
  finiteSlabRowExpectation_deriv_le p hp U i m n y k

private lemma finiteSlab_issued_base_sum {d : ℕ} (U : Finset (Vertex d)) (f : Vertex d → ℝ) :
    (∑ e ∈ issuedBondSet U, f e.1) = (d : ℝ) * ∑ v ∈ U, f v := by
  simp [issuedBondSet, Finset.sum_product, nsmul_eq_mul, Finset.mul_sum]

/-- Each vertex contributes at most d positive-coordinate outgoing bonds. -/
lemma finiteSlab_sum_base_incidence_le {d : ℕ} (U : Finset (Vertex d)) (f : Vertex d → ℝ)
    (hf : ∀ v ∈ U, 0 ≤ f v) :
    (∑ e : internalBondSet U, f e.val.1) ≤ (d : ℝ) * ∑ v ∈ U, f v := by
  calc
    _ = ∑ e ∈ internalBondSet U, f e.1 := Finset.sum_coe_sort _ _
    _ ≤ ∑ e ∈ issuedBondSet U, f e.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (internalBondSet_subset_issued (fun _ h ↦ h))
      intro e he _
      exact hf e.1 (Finset.mem_product.mp he).1
    _ = _ := finiteSlab_issued_base_sum U f

/-- The pair (tip,direction) determines the positive-coordinate bond. -/
private lemma finiteSlab_tip_direction_injective (d : ℕ) :
    Function.Injective (fun e : Bond d ↦ (bondTip e, e.2)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have hij : i = j := congrArg Prod.snd h
  subst j
  have ht : bondTip (x, i) = bondTip (y, i) := congrArg Prod.fst h
  have hxy : x = y := by
    funext k
    have hk := congrFun ht k
    by_cases hki : k = i
    · subst k
      simp only [bondTip, Function.update_self] at hk
      omega
    · simpa only [bondTip, Function.update_of_ne hki] using hk
  exact Prod.ext hxy rfl

/-- Each vertex contributes at most d incoming bonds, even at an irregular
cutoff boundary. This is a finite injection, not an invariance assumption. -/
lemma finiteSlab_sum_tip_incidence_le {d : ℕ} (U : Finset (Vertex d)) (f : Vertex d → ℝ)
    (hf : ∀ v ∈ U, 0 ≤ f v) :
    (∑ e : internalBondSet U, f (bondTip e.val)) ≤ (d : ℝ) * ∑ v ∈ U, f v := by
  let R : Bond d → Bond d := fun e ↦ (bondTip e, e.2)
  have hinj : Function.Injective R := finiteSlab_tip_direction_injective d
  have hsub : (internalBondSet U).image R ⊆ issuedBondSet U := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_product.mpr ⟨((mem_internalBondSet U a).mp ha).2, Finset.mem_univ _⟩
  calc
    _ = ∑ e ∈ internalBondSet U, f (bondTip e) := Finset.sum_coe_sort _ _
    _ = ∑ e ∈ (internalBondSet U).image R, f e.1 := by
      symm
      exact Finset.sum_image (fun a _ b _ hab ↦ hinj hab)
    _ ≤ ∑ e ∈ issuedBondSet U, f e.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro e he _
      exact hf e.1 (Finset.mem_product.mp he).1
    _ = _ := finiteSlab_issued_base_sum U f

/-- BOTH physical orientations cost exactly the degree upper bound 2d. No
card(U), conditional independence, or missing incoming-edge factor is hidden. -/
theorem finiteSlab_oriented_edge_sum_le {d : ℕ} (U : Finset (Vertex d))
    (f g : Vertex d → ℝ) (G : ℝ) (hf : ∀ v ∈ U, 0 ≤ f v)
    (hG : 0 ≤ G) (hg : ∀ v ∈ U, g v ≤ G) :
    (∑ e : internalBondSet U, (f e.val.1 * g (bondTip e.val) + f (bondTip e.val) * g e.val.1)) ≤
      2 * (d : ℝ) * G * ∑ v ∈ U, f v := by
  calc
    _ ≤ ∑ e : internalBondSet U, (f e.val.1 * G + f (bondTip e.val) * G) := by
      apply Finset.sum_le_sum
      intro e _
      have he := (mem_internalBondSet U e.val).mp e.property
      exact add_le_add (mul_le_mul_of_nonneg_left (hg _ he.2) (hf _ he.1))
        (mul_le_mul_of_nonneg_left (hg _ he.1) (hf _ he.2))
    _ = ((∑ e : internalBondSet U, f e.val.1) + (∑ e : internalBondSet U, f (bondTip e.val))) * G := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, add_mul]
    _ ≤ ((d : ℝ) * (∑ v ∈ U, f v) + (d : ℝ) * (∑ v ∈ U, f v)) * G :=
      mul_le_mul_of_nonneg_right
        (add_le_add (finiteSlab_sum_base_incidence_le U f hf) (finiteSlab_sum_tip_incidence_le U f hf)) hG
    _ = _ := by ring

/-- Forward fields include every actual starting vertex at every top cut. -/
abbrev FiniteSlabForwardIndex {d : ℕ} (U : Finset (Vertex d)) (m N : ℤ) : Type :=
  ↥(Finset.Icc m N) × ↥U

/-- Backward fields keep each actual TOP vertex and every starting level. -/
abbrev FiniteSlabBackwardIndex {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ) : Type :=
  Σ h : ↥(Finset.Icc m N), {z : ↥U // z.val i = h.val} × ↥(Finset.Icc m h.val)

/-- The zero field guarantees a nonempty finite index even for an empty cutoff. -/
abbrev FiniteSlabBoundaryIndex {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ) : Type :=
  Unit ⊕ (FiniteSlabForwardIndex U m N ⊕ FiniteSlabBackwardIndex U i m N)

/-- Actual row/column polynomial extensions, not stationary identifications.
Only this FINITE FAMILY is smooth; its maximum is not differentiated. -/
def finiteSlabBoundaryFamily {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ)
    (a : FiniteSlabBoundaryIndex U i m N) (q : ℝ) : ℝ :=
  match a with
  | .inl _ => 0
  | .inr (.inl v) => finiteSlabRowExpectation q U i m v.1.val v.2.val v.1.val
  | .inr (.inr v) => finiteSlabColumnExpectation q U i m v.1.val v.2.2.val v.2.1.val.val

def finiteSlabBoundaryMaximum {d : ℕ} (q : ℝ) (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ) : ℝ :=
  finiteFamilyMaximum (finiteSlabBoundaryFamily U i m N) q

lemma finiteSlabBoundaryMaximum_nonneg {d : ℕ} (q : ℝ) (U : Finset (Vertex d))
    (i : Fin d) (m N : ℤ) : 0 ≤ finiteSlabBoundaryMaximum q U i m N :=
  le_finiteFamilyMaximum (finiteSlabBoundaryFamily U i m N) (.inl ()) q

theorem finiteSlabBoundaryFamily_contDiff {d : ℕ} (r : WithTop ℕ∞) (U : Finset (Vertex d))
    (i : Fin d) (m N : ℤ) (a : FiniteSlabBoundaryIndex U i m N) :
    ContDiff ℝ r (finiteSlabBoundaryFamily U i m N a) := by
  cases a with
  | inl _ => exact contDiff_const
  | inr a =>
    cases a with
    | inl v => exact finiteSlabRowExpectation_contDiff r U i m v.1.val v.2.val v.1.val
    | inr v => exact finiteSlabColumnExpectation_contDiff r U i m v.1.val v.2.2.val v.2.1.val.val

lemma finiteSlabBoundaryFamily_nonneg {d : ℕ} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ) (a : FiniteSlabBoundaryIndex U i m N) :
    0 ≤ finiteSlabBoundaryFamily U i m N a q := by
  cases a with
  | inl _ => exact le_rfl
  | inr a =>
    cases a with
    | inl v => exact finiteSlabRowExpectation_nonneg q hq hq1 U i m v.1.val v.2.val v.1.val
    | inr v => exact finiteSlabRowExpectation_nonneg q hq hq1 U i m v.1.val v.2.1.val.val v.2.2.val

/-- The visible actual maximum bounds EVERY forward top-target row. -/
lemma finiteSlabRowMean_le_boundaryMaximum {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ) (hh : h ∈ Finset.Icc m N)
    (x : Vertex d) (hx : x ∈ U) :
    finiteSlabRowMean p U i m h x h ≤ finiteSlabBoundaryMaximum (p : ℝ) U i m N := by
  rw [finiteSlabRowMean_eq_expectation]
  exact le_finiteFamilyMaximum (finiteSlabBoundaryFamily U i m N)
    (.inr (.inl (⟨h, hh⟩, ⟨x, hx⟩))) (p : ℝ)

/-- The visible actual maximum separately bounds EVERY backward top-start column. -/
lemma finiteSlabColumnMean_le_boundaryMaximum {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ) (hh : h ∈ Finset.Icc m N)
    (z : Vertex d) (hzU : z ∈ U) (hzh : z i = h) (r : ℤ) (hr : r ∈ Finset.Icc m h) :
    finiteSlabColumnMean p U i m h r z ≤ finiteSlabBoundaryMaximum (p : ℝ) U i m N := by
  rw [finiteSlabColumnMean_eq_expectation]
  exact le_finiteFamilyMaximum (finiteSlabBoundaryFamily U i m N)
    (.inr (.inr ⟨⟨h, hh⟩, (⟨⟨z, hzU⟩, hzh⟩, ⟨r, hr⟩)⟩)) (p : ℝ)

/-- Exact finite height partition of the actual point connection mass. Outside
slab endpoints contribute zero, including the nil-path convention. -/
lemma finiteSlabRowMean_sum_levels {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) :
    (∑ y ∈ U, (percolation d p).real (finiteSlabConnectionEvent U i m n x y)) =
      ∑ r ∈ Finset.Icc m n, finiteSlabRowMean p U i m n x r := by
  unfold finiteSlabRowMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y i ∈ Finset.Icc m n
  · simp [eq_comm, hy]
  · have hout : y ∉ finiteHeightSlab i m n ∩ (U : Set (Vertex d)) := by
      intro h
      exact hy (Finset.mem_Icc.mpr h.1)
    have he := finiteSlabConnectionEvent_empty_of_end_outside U i m n x y hout
    simp [he]

/-- Actual off-diagonal mass is bounded by H*M², using the actual forward AND
backward fields of the visible maximum. This is the cutoff convolution step. -/
lemma finiteSlabRowMean_le_boundaryMaximum_sq {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ) (hh : h ∈ Finset.Icc m N)
    (x : Vertex d) (hx : x ∈ U) (r : ℤ) (hr : r ∈ Finset.Icc m h) :
    finiteSlabRowMean p U i m h x r ≤
      ((Finset.Icc m N).card : ℝ) * (finiteSlabBoundaryMaximum (p : ℝ) U i m N) ^ 2 := by
  let M := finiteSlabBoundaryMaximum (p : ℝ) U i m N
  have hM : 0 ≤ M := finiteSlabBoundaryMaximum_nonneg _ U i m N
  have hsub : Finset.Icc (max (x i) r) h ⊆ Finset.Icc m N := by
    intro s hs
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1.trans ((le_max_right _ _).trans (Finset.mem_Icc.mp hs).1),
      (Finset.mem_Icc.mp hs).2.trans (Finset.mem_Icc.mp hh).2⟩
  have hconv := finiteSlabRowMean_le_cut_count_mul_sq p U i m h x r M hM
    (fun s hs ↦ finiteSlabRowMean_le_boundaryMaximum p U i m N s (hsub hs) x hx)
    (fun s hs z hzU hzs ↦ finiteSlabColumnMean_le_boundaryMaximum p U i m N s (hsub hs)
      z hzU hzs r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, (le_max_right _ _).trans (Finset.mem_Icc.mp hs).1⟩))
  have hcard : ((Finset.Icc (max (x i) r) h).card : ℝ) ≤ ((Finset.Icc m N).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub)
  exact hconv.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg M))

private lemma finiteSlab_height_card_le {m N h : ℤ} (hh : h ∈ Finset.Icc m N) :
    ((Finset.Icc m h).card : ℝ) ≤ ((Finset.Icc m N).card : ℝ) := by
  have hsub : Finset.Icc m h ⊆ Finset.Icc m N := by
    intro r hr
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2.trans (Finset.mem_Icc.mp hh).2⟩
  exact_mod_cast (Finset.card_le_card hsub)

/-- Sum the proved off-diagonal convolution over all possible endpoint levels. -/
lemma finiteSlab_point_mass_le_boundaryMaximum_sq {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ) (hh : h ∈ Finset.Icc m N)
    (x : Vertex d) (hx : x ∈ U) :
    (∑ y ∈ U, (percolation d p).real (finiteSlabConnectionEvent U i m h x y)) ≤
      ((Finset.Icc m N).card : ℝ) ^ 2 * (finiteSlabBoundaryMaximum (p : ℝ) U i m N) ^ 2 := by
  let H : ℝ := (Finset.Icc m N).card
  let M := finiteSlabBoundaryMaximum (p : ℝ) U i m N
  change _ ≤ H ^ 2 * M ^ 2
  calc
    _ = ∑ r ∈ Finset.Icc m h, finiteSlabRowMean p U i m h x r := finiteSlabRowMean_sum_levels p U i m h x
    _ ≤ ∑ _r ∈ Finset.Icc m h, H * M ^ 2 :=
      Finset.sum_le_sum (fun r hr ↦ finiteSlabRowMean_le_boundaryMaximum_sq p U i m N h hh x hx r hr)
    _ = ((Finset.Icc m h).card : ℝ) * (H * M ^ 2) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ H * (H * M ^ 2) := mul_le_mul_of_nonneg_right (finiteSlab_height_card_le hh) (by dsimp [H]; positivity)
    _ = _ := by ring

/-- For a TOP starting vertex the actual backward fields bound the total
point mass by H*M, rather than using a fictitious finite-cutoff stationarity. -/
lemma finiteSlab_top_point_mass_le_boundaryMaximum {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ) (hh : h ∈ Finset.Icc m N)
    (z : Vertex d) (hzU : z ∈ U) (hzh : z i = h) :
    (∑ y ∈ U, (percolation d p).real (finiteSlabConnectionEvent U i m h z y)) ≤
      ((Finset.Icc m N).card : ℝ) * finiteSlabBoundaryMaximum (p : ℝ) U i m N := by
  let M := finiteSlabBoundaryMaximum (p : ℝ) U i m N
  have hM : 0 ≤ M := finiteSlabBoundaryMaximum_nonneg _ U i m N
  calc
    _ = ∑ r ∈ Finset.Icc m h, finiteSlabRowMean p U i m h z r := finiteSlabRowMean_sum_levels p U i m h z
    _ ≤ ∑ _r ∈ Finset.Icc m h, M := by
      apply Finset.sum_le_sum
      intro r hr
      rw [← finiteSlabColumnMean_eq_rowMean]
      exact finiteSlabColumnMean_le_boundaryMaximum p U i m N h hh z hzU hzh r hr
    _ = ((Finset.Icc m h).card : ℝ) * M := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (finiteSlab_height_card_le hh) hM

/-- Genuine cubic differential for every forward top-target row, with all
physical edge orientations and the exact 2d incidence factor. -/
theorem finiteSlab_forward_deriv_le_cubic {d : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ) (hh : h ∈ Finset.Icc m N)
    (x : Vertex d) (hx : x ∈ U) :
    deriv (fun q ↦ finiteSlabRowExpectation q U i m h x h) (p : ℝ) ≤
      2 * (d : ℝ) * ((Finset.Icc m N).card : ℝ) ^ 2 *
        (finiteSlabBoundaryMaximum (p : ℝ) U i m N) ^ 3 := by
  let H : ℝ := (Finset.Icc m N).card
  let M := finiteSlabBoundaryMaximum (p : ℝ) U i m N
  have hM : 0 ≤ M := finiteSlabBoundaryMaximum_nonneg _ U i m N
  change _ ≤ 2 * (d : ℝ) * H ^ 2 * M ^ 3
  calc
    _ ≤ ∑ e : internalBondSet U,
        ((percolation d p).real (finiteSlabConnectionEvent U i m h x e.val.1) *
          finiteSlabRowMean p U i m h (bondTip e.val) h +
        (percolation d p).real (finiteSlabConnectionEvent U i m h x (bondTip e.val)) *
          finiteSlabRowMean p U i m h e.val.1 h) := finiteSlabRowExpectation_deriv_le p hp U i m h x h
    _ ≤ 2 * (d : ℝ) * M * ∑ y ∈ U, (percolation d p).real (finiteSlabConnectionEvent U i m h x y) :=
      finiteSlab_oriented_edge_sum_le U
        (fun y ↦ (percolation d p).real (finiteSlabConnectionEvent U i m h x y))
        (fun y ↦ finiteSlabRowMean p U i m h y h) M (fun _ _ ↦ measureReal_nonneg) hM
        (fun y hy ↦ finiteSlabRowMean_le_boundaryMaximum p U i m N h hh y hy)
    _ ≤ 2 * (d : ℝ) * M * (H ^ 2 * M ^ 2) := mul_le_mul_of_nonneg_left
      (finiteSlab_point_mass_le_boundaryMaximum_sq p U i m N h hh x hx) (by positivity)
    _ = _ := by ring

/-- Genuine cubic differential for the separately retained backward top-start
column family; this cannot be inferred by stationarity in an arbitrary U. -/
theorem finiteSlab_backward_deriv_le_cubic {d : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ) (hh : h ∈ Finset.Icc m N)
    (z : Vertex d) (hzU : z ∈ U) (hzh : z i = h) (r : ℤ) (hr : r ∈ Finset.Icc m h) :
    deriv (fun q ↦ finiteSlabColumnExpectation q U i m h r z) (p : ℝ) ≤
      2 * (d : ℝ) * ((Finset.Icc m N).card : ℝ) ^ 2 *
        (finiteSlabBoundaryMaximum (p : ℝ) U i m N) ^ 3 := by
  let H : ℝ := (Finset.Icc m N).card
  let M := finiteSlabBoundaryMaximum (p : ℝ) U i m N
  have hM : 0 ≤ M := finiteSlabBoundaryMaximum_nonneg _ U i m N
  have hH : 0 ≤ H := by dsimp [H]; positivity
  change _ ≤ 2 * (d : ℝ) * H ^ 2 * M ^ 3
  calc
    _ ≤ ∑ e : internalBondSet U,
        ((percolation d p).real (finiteSlabConnectionEvent U i m h z e.val.1) *
          finiteSlabRowMean p U i m h (bondTip e.val) r +
        (percolation d p).real (finiteSlabConnectionEvent U i m h z (bondTip e.val)) *
          finiteSlabRowMean p U i m h e.val.1 r) := finiteSlabColumnExpectation_deriv_le p hp U i m h r z
    _ ≤ 2 * (d : ℝ) * (H * M ^ 2) * ∑ y ∈ U, (percolation d p).real (finiteSlabConnectionEvent U i m h z y) :=
      finiteSlab_oriented_edge_sum_le U
        (fun y ↦ (percolation d p).real (finiteSlabConnectionEvent U i m h z y))
        (fun y ↦ finiteSlabRowMean p U i m h y r) (H * M ^ 2) (fun _ _ ↦ measureReal_nonneg)
        (by positivity) (fun y hy ↦ finiteSlabRowMean_le_boundaryMaximum_sq p U i m N h hh y hy r hr)
    _ ≤ 2 * (d : ℝ) * (H * M ^ 2) * (H * M) := mul_le_mul_of_nonneg_left
      (finiteSlab_top_point_mass_le_boundaryMaximum p U i m N h hh z hzU hzh) (by positivity)
    _ = _ := by ring

/-- Every coordinate of the VISIBLE actual finite boundary family satisfies
the cubic inequality. There is no differential inequality hypothesis here,
and no derivative of the nonsmooth maximum is taken. -/
theorem finiteSlabBoundaryFamily_deriv_le_cubic {d : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ) (a : FiniteSlabBoundaryIndex U i m N) :
    deriv (finiteSlabBoundaryFamily U i m N a) (p : ℝ) ≤
      2 * (d : ℝ) * ((Finset.Icc m N).card : ℝ) ^ 2 *
        (finiteSlabBoundaryMaximum (p : ℝ) U i m N) ^ 3 := by
  cases a with
  | inl _ =>
    have hM := finiteSlabBoundaryMaximum_nonneg (p : ℝ) U i m N
    change deriv (fun _ : ℝ ↦ 0) (p : ℝ) ≤ _
    rw [deriv_const]
    positivity
  | inr a =>
    cases a with
    | inl v =>
      exact finiteSlab_forward_deriv_le_cubic p hp U i m N v.1.val v.1.property v.2.val v.2.property
    | inr v =>
      exact finiteSlab_backward_deriv_le_cubic p hp U i m N v.1.val v.1.property
        v.2.1.val.val v.2.1.val.property v.2.1.property v.2.2.val v.2.2.property

/-- Natural source height N: the exact coefficient is 2d(N+1)², valid even
at N=0. For N>=1 this is at most 8dN², the source dimensional O(N²) form. -/
theorem finiteSlabBoundaryFamily_deriv_le_cubic_nat {d : ℕ} (p : unitInterval) (hp : (p : ℝ) ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (N : ℕ) (a : FiniteSlabBoundaryIndex U i 0 (N : ℤ)) :
    deriv (finiteSlabBoundaryFamily U i 0 (N : ℤ) a) (p : ℝ) ≤
      2 * (d : ℝ) * (N + 1 : ℝ) ^ 2 * (finiteSlabBoundaryMaximum (p : ℝ) U i 0 (N : ℤ)) ^ 3 := by
  have hc : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by rw [Int.card_Icc]; omega
  simpa only [hc, Nat.cast_add, Nat.cast_one] using finiteSlabBoundaryFamily_deriv_le_cubic p hp U i 0 (N : ℤ) a

end NearCritical
