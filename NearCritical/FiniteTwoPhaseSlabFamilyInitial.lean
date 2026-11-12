module

public import NearCritical.FiniteTwoPhaseSlabInitial

/-! Uniform critical seed for the actual weighted finite maximum. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset
open scoped Classical

private lemma weighted_initial_cancel {r M w : ℝ}
    (h : r ≤ M*Real.exp (-w)) : Real.exp w*r ≤ M := by
  calc
    _ ≤ Real.exp w*(M*Real.exp (-w)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = M*(Real.exp w*Real.exp (-w)) := by ring
    _ = M := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]

/-- One critical amplitude and rate control the entire actual finite family,
uniformly in the cutoff, top, interface, and upper parameter. -/
theorem finiteTwoPhaseBoundaryMaximum_critical_initial {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (U : Finset (Vertex d)) (m N : ℕ)
      (q : unitInterval), q ≤ criticalPoint d →
        finiteTwoPhaseBoundaryMaximum q c (criticalPoint d : ℝ) U i m N ≤ M := by
  obtain ⟨M,c,hM,hc,hrows⟩ :=
    finiteTwoPhaseSlab_critical_boundary_initial i hB hb hpc pioneers
  refine ⟨M,c,hM,hc,?_⟩
  intro U m N q hq
  apply finiteFamilyMaximum_le
  intro a
  cases a with
  | inl _ => exact hM.le
  | inr a =>
    cases a with
    | inl v =>
      let h : ℤ := v.1.val
      let x : Vertex d := v.2.val
      have hh0 : 0 ≤ h := (Finset.mem_Icc.mp v.1.property).1
      have hhNat : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh0
      change Real.exp _ * finiteTwoPhaseSlabRowExpectation _ _ U i _ h x h ≤ M
      rw [← finiteTwoPhaseSlabRowMean_eq_expectation]
      by_cases hx : x ∈ finiteHeightSlab i 0 h ∩ (U : Set (Vertex d))
      · have hkNat : ((x i).toNat : ℤ) = x i := Int.toNat_of_nonneg hx.1.1
        have hkhi : x i ≤ h := hx.1.2
        have hkh : (x i).toNat ≤ h.toNat := by omega
        have hr := (hrows U m (x i).toNat h.toNat hkh q hq).1 x hkNat.symm
        have hr' : finiteTwoPhaseSlabRowMean (criticalPoint d) q U i m h x h ≤
            M*Real.exp (-(c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
              twoPhaseSlabDistance m (x i) h)) := by
          simpa only [hhNat,hkNat,neg_mul] using hr
        exact weighted_initial_cancel hr'
      · rw [finiteTwoPhaseSlabRowMean_zero_of_start_outside _ _ _ _ _ _ _ _ hx,mul_zero]
        exact hM.le
    | inr v =>
      let h : ℤ := v.1.val
      let z : Vertex d := v.2.1.val.val
      let k : ℤ := v.2.2.val
      have hh0 : 0 ≤ h := (Finset.mem_Icc.mp v.1.property).1
      have hk0 : 0 ≤ k := (Finset.mem_Icc.mp v.2.2.property).1
      have hkh : k ≤ h := (Finset.mem_Icc.mp v.2.2.property).2
      have hhNat : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh0
      have hkNat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
      have hzh : z i = (h.toNat : ℤ) := v.2.1.property.trans hhNat.symm
      have hr := (hrows U m k.toNat h.toNat (by omega) q hq).2 z hzh
      have hdist := twoPhaseSlabDistance_symm (m : ℤ) k h
      change Real.exp _ * finiteTwoPhaseSlabRowExpectation _ _ U i _ h z k ≤ M
      rw [← finiteTwoPhaseSlabRowMean_eq_expectation]
      have hr' : finiteTwoPhaseSlabRowMean (criticalPoint d) q U i m h z k ≤
          M*Real.exp (-(c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
            twoPhaseSlabDistance m h k)) := by
        simpa only [hhNat,hkNat,hdist,neg_mul] using hr
      exact weighted_initial_cancel hr'

end NearCritical
