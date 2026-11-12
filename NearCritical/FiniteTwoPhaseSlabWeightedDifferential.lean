module

public import NearCritical.FiniteTwoPhaseSlabDifferential
public import NearCritical.FiniteTwoPhaseSlabWeightedConvolution
public import NearCritical.TwoPhaseSlabMaskGeometry

/-! Actual weighted mixed-slab derivative bounds. The variable mask retains
irrelevant off-slab bonds until their contributions are proved zero. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset MeasureTheory
open scoped Classical

/-- The endpoint layer m+1 is retained, including the reversed physical
orientation of an interface-crossing bond. -/
def finiteTwoPhaseLowerSites {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (m h : ℤ) : Finset (Vertex d) :=
  U.filter (fun v => v ∈ finiteHeightSlab i 0 (min h (m+1)))

/-- Masked incidence from actual endpoint support. This is finite algebra;
no convexity, stationarity, or probability estimate is assumed. -/
lemma finiteTwoPhase_masked_oriented_sum_le {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (m h : ℤ)
    (f g : Vertex d → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ v ∈ U, 0 ≤ f v)
    (hfzero : ∀ v, v ∉ finiteHeightSlab i 0 h → f v = 0)
    (hgzero : ∀ v, v ∉ finiteHeightSlab i 0 h → g v = 0)
    (hg : ∀ v ∈ finiteTwoPhaseLowerSites U i m h, g v ≤ L) :
    (∑ e ∈ finiteTwoPhaseVariableMask U i m h,
      (f e.val.1 * g (bondTip e.val) + f (bondTip e.val) * g e.val.1)) ≤
      2*(d : ℝ)*L*(∑ v ∈ finiteTwoPhaseLowerSites U i m h, f v) := by
  let T := finiteTwoPhaseLowerSites U i m h
  let F : Vertex d → ℝ := fun v => if v ∈ T then f v else 0
  have hF : ∀ v ∈ U, 0 ≤ F v := by
    intro v hv
    dsimp [F]
    split_ifs
    · exact hf v hv
    · exact le_rfl
  have heach (e : internalBondSet U) (he : e ∈ finiteTwoPhaseVariableMask U i m h) :
      f e.val.1*g (bondTip e.val)+f (bondTip e.val)*g e.val.1 ≤
        F e.val.1*L+F (bondTip e.val)*L := by
    have heU := (mem_internalBondSet U e.val).mp e.property
    by_cases ha : e.val.1 ∈ finiteHeightSlab i 0 h
    · by_cases hb : bondTip e.val ∈ finiteHeightSlab i 0 h
      · obtain ⟨hal,hbl⟩ := finiteTwoPhaseVariableMask_endpoints_in_lower_slab U i m h e he ha hb
        have haT : e.val.1 ∈ T := Finset.mem_filter.mpr ⟨heU.1,hal⟩
        have hbT : bondTip e.val ∈ T := Finset.mem_filter.mpr ⟨heU.2,hbl⟩
        simp only [F,ite_eq_left haT,ite_eq_left hbT]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hg _ hbT) (hf _ heU.1))
          (mul_le_mul_of_nonneg_left (hg _ haT) (hf _ heU.2))
      · rw [hfzero _ hb,hgzero _ hb,mul_zero,zero_mul,add_zero]
        exact add_nonneg (mul_nonneg (hF _ heU.1) hL) (mul_nonneg (hF _ heU.2) hL)
    · rw [hfzero _ ha,hgzero _ ha,zero_mul,mul_zero,zero_add]
      exact add_nonneg (mul_nonneg (hF _ heU.1) hL) (mul_nonneg (hF _ heU.2) hL)
  have hsum : (∑ v ∈ U, F v) = ∑ v ∈ T, f v := by
    unfold T finiteTwoPhaseLowerSites
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp [F,T,finiteTwoPhaseLowerSites]
    simp only [Finset.mem_filter,hv,true_and]
  calc
    _ ≤ ∑ e ∈ finiteTwoPhaseVariableMask U i m h,
        (F e.val.1*L+F (bondTip e.val)*L) := Finset.sum_le_sum heach
    _ ≤ ∑ e : internalBondSet U, (F e.val.1*L+F (bondTip e.val)*L) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro e _ _
      have heU := (mem_internalBondSet U e.val).mp e.property
      exact add_nonneg (mul_nonneg (hF _ heU.1) hL) (mul_nonneg (hF _ heU.2) hL)
    _ ≤ 2*(d : ℝ)*L*(∑ v ∈ U, F v) :=
      finiteSlab_oriented_edge_sum_le U F (fun _ => L) L hF hL (fun _ _ => le_rfl)
    _ = _ := by rw [hsum]

/-- Exact partition of a restricted prefix mass into actual finite rows. -/
lemma finiteTwoPhase_lower_gauge_sum_eq_levels {d : ℕ}
    (p q : unitInterval) (U : Finset (Vertex d)) (i : Fin d) (m h : ℤ)
    (x : Vertex d) (a : ℝ) :
    (∑ v ∈ finiteTwoPhaseLowerSites U i m h,
      (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
        (finiteSlabConnectionEvent U i 0 h x v) *
          Real.exp (a*twoPhaseSlabDistance m (x i) (v i))) =
      ∑ j ∈ Finset.Icc (0 : ℤ) (min h (m+1)),
        Real.exp (a*twoPhaseSlabDistance m (x i) j) *
          finiteTwoPhaseSlabRowMean p q U i m h x j := by
  unfold finiteTwoPhaseLowerSites finiteTwoPhaseSlabRowMean
  rw [Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hj : v i ∈ Finset.Icc (0 : ℤ) (min h (m+1))
  · have hp := Finset.mem_Icc.mp hj
    simp [finiteHeightSlab,hp,eq_comm,hj,mul_comm] <;> omega
  · have hp : ¬ (0 ≤ v i ∧ v i ≤ min h (m+1)) := fun hv => hj (Finset.mem_Icc.mpr hv)
    simp [finiteHeightSlab,hp,eq_comm,hj] <;> omega

/-- A uniform bound for weighted rows on the retained endpoint layers gives
an exact O(m+1) prefix mass bound; the source count includes m=0. -/
lemma finiteTwoPhase_lower_gauge_sum_le {d : ℕ}
    (p q : unitInterval) (U : Finset (Vertex d)) (i : Fin d) (m : ℕ) (h : ℤ)
    (x : Vertex d) (a D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ j ∈ Finset.Icc (0 : ℤ) (min h ((m : ℤ)+1)),
      Real.exp (a*twoPhaseSlabDistance (m : ℤ) (x i) j) *
        finiteTwoPhaseSlabRowMean p q U i m h x j ≤ D) :
    (∑ v ∈ finiteTwoPhaseLowerSites U i m h,
      (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
        (finiteSlabConnectionEvent U i 0 h x v) *
          Real.exp (a*twoPhaseSlabDistance m (x i) (v i))) ≤ 2*(m+1 : ℝ)*D := by
  have hsub : Finset.Icc (0 : ℤ) (min h ((m : ℤ)+1)) ⊆
      Finset.Icc (0 : ℤ) ((m : ℤ)+1) := by
    intro j hj
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
      (Finset.mem_Icc.mp hj).2.trans (min_le_right _ _)⟩
  have hcard : ((Finset.Icc (0 : ℤ) (min h ((m : ℤ)+1))).card : ℝ) ≤ 2*(m+1 : ℝ) := by
    have hc : (Finset.Icc (0 : ℤ) ((m : ℤ)+1)).card = m+2 := by rw [Int.card_Icc]; omega
    have hb := Finset.card_le_card hsub
    rw [hc] at hb
    have hbR : ((Finset.Icc (0 : ℤ) (min h ((m : ℤ)+1))).card : ℝ) ≤ (m+2 : ℝ) := by exact_mod_cast hb
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [finiteTwoPhase_lower_gauge_sum_eq_levels]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (0 : ℤ) (min h ((m : ℤ)+1)), D := Finset.sum_le_sum hrow
    _ = ((Finset.Icc (0 : ℤ) (min h ((m : ℤ)+1))).card : ℝ)*D := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hD

private lemma twoPhase_weighted_product_le {d : ℕ} (i : Fin d) (m k j : ℤ)
    (e : Bond d) (c s : ℝ) (hc : 0 ≤ c) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (f g : Vertex d → ℝ) (hf : ∀ v, 0 ≤ f v) (hg : ∀ v, 0 ≤ g v) :
    Real.exp (c*s*twoPhaseSlabDistance m k j) *
      (f e.1*g (bondTip e)+f (bondTip e)*g e.1) ≤
    Real.exp c *
      ((f e.1*Real.exp (c*s*twoPhaseSlabDistance m k (e.1 i))) *
        (g (bondTip e)*Real.exp (c*s*twoPhaseSlabDistance m (bondTip e i) j)) +
       (f (bondTip e)*Real.exp (c*s*twoPhaseSlabDistance m k (bondTip e i))) *
        (g e.1*Real.exp (c*s*twoPhaseSlabDistance m (e.1 i) j))) := by
  have hab : e.1 i ≤ bondTip e i+1 ∧ bondTip e i ≤ e.1 i+1 := by
    obtain ⟨ha,hb⟩ := twoPhase_bond_height_step e i
    exact ⟨by omega,hb⟩
  have hscalar (a b : ℤ) (hab : a ≤ b+1 ∧ b ≤ a+1) :
      Real.exp (c*s*twoPhaseSlabDistance m k j) ≤
        Real.exp c * (Real.exp (c*s*twoPhaseSlabDistance m k a) *
          Real.exp (c*s*twoPhaseSlabDistance m b j)) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left (twoPhaseSlabDistance_cross_edge m k j a b hab)
      (mul_nonneg hc hs0)
    have hcs := mul_le_mul_of_nonneg_left hs1 hc
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right (hscalar (e.1 i) (bondTip e i) hab)
    (mul_nonneg (hf e.1) (hg (bondTip e)))
  have h2 := mul_le_mul_of_nonneg_right (hscalar (bondTip e i) (e.1 i) hab.symm)
    (mul_nonneg (hf (bondTip e)) (hg e.1))
  convert add_le_add h1 h2 using 1 <;> ring

/-- Actual weighted row derivative, reduced to its genuine retained-layer
prefix mass and suffix gauge. The two quantitative hypotheses here are a
local algebraic interface; the source cubic theorems below derive them. -/
lemma finiteTwoPhase_weighted_deriv_le_of_gauges {d : ℕ}
    (p q P : unitInterval) (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (hqpc : q ≤ criticalPoint d) (c : ℝ) (hc : 0 ≤ c)
    (U : Finset (Vertex d)) (i : Fin d) (m h : ℤ) (x : Vertex d) (j : ℤ)
    (L S : ℝ) (hL : 0 ≤ L)
    (hG : ∀ v ∈ finiteTwoPhaseLowerSites U i m h,
      finiteTwoPhaseSlabRowMean p q U i m h v j *
        Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m (v i) j) ≤ L)
    (hF : (∑ v ∈ finiteTwoPhaseLowerSites U i m h,
      (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
        (finiteSlabConnectionEvent U i 0 h x v) *
          Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m (x i) (v i))) ≤ S) :
    Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m (x i) j) *
      deriv (fun t => finiteTwoPhaseSlabRowExpectation (q : ℝ) t U i m h x j) (p : ℝ) ≤
        2*(d : ℝ)*Real.exp c*L*S := by
  let s := Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))
  let f : Vertex d → ℝ := fun v =>
    (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
      (finiteSlabConnectionEvent U i 0 h x v)
  let g : Vertex d → ℝ := fun v => finiteTwoPhaseSlabRowMean p q U i m h v j
  let F : Vertex d → ℝ := fun v => f v*Real.exp (c*s*twoPhaseSlabDistance m (x i) (v i))
  let G : Vertex d → ℝ := fun v => g v*Real.exp (c*s*twoPhaseSlabDistance m (v i) j)
  let W := Real.exp (c*s*twoPhaseSlabDistance m (x i) j)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    have hgap : 0 ≤ (criticalPoint d : ℝ)-(q : ℝ) := sub_nonneg.mpr hqpc
    have hgap1 : (criticalPoint d : ℝ)-(q : ℝ) ≤ 1 := by linarith [q.2.1,(criticalPoint d).2.2]
    nlinarith [Real.sq_sqrt hgap,Real.sqrt_nonneg ((criticalPoint d : ℝ)-(q : ℝ))]
  have hf : ∀ v, 0 ≤ f v := fun _ => measureReal_nonneg
  have hg : ∀ v, 0 ≤ g v := by
    intro v
    change 0 ≤ finiteTwoPhaseSlabRowMean p q U i m h v j
    rw [finiteTwoPhaseSlabRowMean_eq_expectation]
    exact finiteTwoPhaseSlabRowExpectation_nonneg p q U i m h v j
  have hF0 : ∀ v, v ∉ finiteHeightSlab i 0 h → F v = 0 := by
    intro v hv
    have hout : v ∉ finiteHeightSlab i 0 h ∩ (U : Set (Vertex d)) := fun hh => hv hh.1
    have he := finiteSlabConnectionEvent_empty_of_end_outside U i 0 h x v hout
    simp [F,f,he]
  have hG0 : ∀ v, v ∉ finiteHeightSlab i 0 h → G v = 0 := by
    intro v hv
    have hout : v ∉ finiteHeightSlab i 0 h ∩ (U : Set (Vertex d)) := fun hh => hv hh.1
    have he (y : Vertex d) := finiteSlabConnectionEvent_empty_of_start_outside U i 0 h v y hout
    simp [G,g,finiteTwoPhaseSlabRowMean,he]
  have hinc := finiteTwoPhase_masked_oriented_sum_le U i m h F G L hL
    (fun v _ => mul_nonneg (hf v) (Real.exp_nonneg _)) hF0 hG0 hG
  have hder := finiteTwoPhaseSlabRowExpectation_deriv_le p q P hP hpP hqP U i m h x j
  change W * deriv (fun t => finiteTwoPhaseSlabRowExpectation (q : ℝ) t U i m h x j) (p : ℝ) ≤ _
  calc
    _ ≤ W*(∑ e ∈ finiteTwoPhaseVariableMask U i m h,
        (f e.val.1*g (bondTip e.val)+f (bondTip e.val)*g e.val.1)) :=
      mul_le_mul_of_nonneg_left hder (Real.exp_nonneg _)
    _ ≤ Real.exp c*(∑ e ∈ finiteTwoPhaseVariableMask U i m h,
        (F e.val.1*G (bondTip e.val)+F (bondTip e.val)*G e.val.1)) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      exact twoPhase_weighted_product_le i m (x i) j e.val c s hc hs0 hs1 f g hf hg
    _ ≤ Real.exp c*(2*(d : ℝ)*L*(∑ v ∈ finiteTwoPhaseLowerSites U i m h, F v)) :=
      mul_le_mul_of_nonneg_left hinc (Real.exp_nonneg _)
    _ ≤ Real.exp c*(2*(d : ℝ)*L*S) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hF (by positivity)) (Real.exp_nonneg _)
    _ = _ := by ring

/-- The actual forward family entry has a cubic p-derivative bound, with
only O(m+1) derivative layers despite the arbitrary cutoff U. -/
theorem finiteTwoPhase_forward_weighted_deriv_le_cubic {d : ℕ}
    (p q P : unitInterval) (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (hqpc : q ≤ criticalPoint d) (c : ℝ) (hc : 0 ≤ c)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℕ) (h : ℤ)
    (hh : h ∈ Finset.Icc (0 : ℤ) (N : ℤ)) (x : Vertex d) (hx : x ∈ U) :
    Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m (x i) h) *
      deriv (fun t => finiteTwoPhaseSlabRowExpectation (q : ℝ) t U i m h x h) (p : ℝ) ≤
        4*(d : ℝ)*Real.exp c*(m+1 : ℝ)*(N+1 : ℝ)*
          (finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m N)^3 := by
  let M := finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i (m : ℤ) (N : ℤ)
  have hM : 0 ≤ M := finiteTwoPhaseBoundaryMaximum_nonneg q c (p : ℝ) U i m N
  have hsuffix : ∀ v ∈ finiteTwoPhaseLowerSites U i m h,
      finiteTwoPhaseSlabRowMean p q U i m h v h *
        Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m (v i) h) ≤ M := by
    intro v hv
    simpa only [mul_comm] using finiteTwoPhase_forward_row_le_boundaryMaximum p q c U i m N h hh v
      (Finset.mem_filter.mp hv).1
  have hprefix := finiteTwoPhase_lower_gauge_sum_le p q U i m h x
    (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))) ((N+1 : ℝ)*M^2)
    (by positivity) (fun j hj =>
      finiteTwoPhaseSlabRowMean_weighted_le_boundaryMaximum_sq p q P hP hpP hqP c hc U i m h N
        (Finset.mem_Icc.mp hh).2 x hx j
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
          (Finset.mem_Icc.mp hj).2.trans (min_le_left _ _)⟩))
  have hb := finiteTwoPhase_weighted_deriv_le_of_gauges p q P hP hpP hqP hqpc c hc U i m h x h
    M (2*(m+1 : ℝ)*((N+1 : ℝ)*M^2)) hM hsuffix hprefix
  convert hb using 1 <;> dsimp [M] <;> ring

/-- For backward entries the top-start prefix is itself a family entry;
the suffix uses the finite convolution. No finite-cutoff stationarity is used. -/
theorem finiteTwoPhase_backward_weighted_deriv_le_cubic {d : ℕ}
    (p q P : unitInterval) (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (hqpc : q ≤ criticalPoint d) (c : ℝ) (hc : 0 ≤ c)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℕ) (h : ℤ)
    (hh : h ∈ Finset.Icc (0 : ℤ) (N : ℤ)) (z : Vertex d) (hz : z ∈ U)
    (hzh : z i = h) (k : ℤ) (hk : k ∈ Finset.Icc (0 : ℤ) h) :
    Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m h k) *
      deriv (fun t => finiteTwoPhaseSlabRowExpectation (q : ℝ) t U i m h z k) (p : ℝ) ≤
        4*(d : ℝ)*Real.exp c*(m+1 : ℝ)*(N+1 : ℝ)*
          (finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m N)^3 := by
  let M := finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i (m : ℤ) (N : ℤ)
  have hM : 0 ≤ M := finiteTwoPhaseBoundaryMaximum_nonneg q c (p : ℝ) U i m N
  have hsuffix : ∀ v ∈ finiteTwoPhaseLowerSites U i m h,
      finiteTwoPhaseSlabRowMean p q U i m h v k *
        Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m (v i) k) ≤
          (N+1 : ℝ)*M^2 := by
    intro v hv
    simpa only [mul_comm] using
      finiteTwoPhaseSlabRowMean_weighted_le_boundaryMaximum_sq p q P hP hpP hqP c hc U i m h N
        (Finset.mem_Icc.mp hh).2 v (Finset.mem_filter.mp hv).1 k hk
  have hprefix := finiteTwoPhase_lower_gauge_sum_le p q U i m h z
    (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))) M hM (by
      intro j hj
      rw [hzh]
      exact finiteTwoPhase_backward_row_le_boundaryMaximum p q c U i m N h hh z hz hzh j
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
          (Finset.mem_Icc.mp hj).2.trans (min_le_left _ _)⟩))
  have hb := finiteTwoPhase_weighted_deriv_le_of_gauges p q P hP hpP hqP hqpc c hc U i m h z k
    ((N+1 : ℝ)*M^2) (2*(m+1 : ℝ)*M) (by positivity) hsuffix hprefix
  rw [hzh] at hb
  convert hb using 1 <;> dsimp [M] <;> ring

end NearCritical
