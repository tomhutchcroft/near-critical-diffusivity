module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The square-root exponential integral in the paper's upper-bound argument.
An explicit primitive handles the critical endpoint without differentiating
sqrt at zero. No arm or energy bound is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

def subcriticalPrimitive (t pc x : ℝ) : ℝ :=
  (2 / t^2) * (1 + t * Real.sqrt (pc-x)) * Real.exp (-t * Real.sqrt (pc-x))

lemma subcriticalPrimitive_hasDerivAt {t pc x : ℝ} (ht : 0 < t) (hx : x < pc) :
    HasDerivAt (subcriticalPrimitive t pc) (Real.exp (-t * Real.sqrt (pc-x))) x := by
  have hδ : 0 < pc-x := sub_pos.mpr hx
  have hroot : Real.sqrt (pc-x) ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  have hr := (Real.hasDerivAt_sqrt hδ.ne').comp x ((hasDerivAt_id x).const_sub pc)
  have hz := hr.const_mul t
  have he := (hz.neg).exp
  have H := (((hasDerivAt_const x 1).add hz).mul he).const_mul (2/t^2)
  convert H using 1
  · ext y
    dsimp [subcriticalPrimitive]
    simp only [neg_mul]
    ring
  · dsimp
    simp only [neg_mul]
    field_simp [ht.ne', hroot]
    ring

lemma subcriticalPrimitive_nonneg {t pc x : ℝ} (ht : 0 ≤ t) :
    0 ≤ subcriticalPrimitive t pc x := by
  unfold subcriticalPrimitive
  positivity

/-- Source eq.upper_step_3b_sub: the whole subcritical interval contributes
at most 2/t², independently of its lower endpoint. -/
theorem subcritical_exp_sqrt_integral_le {a pc t : ℝ} (hap : a ≤ pc) (ht : 0 < t) :
    (∫ x in a..pc, Real.exp (-t * Real.sqrt (pc-x))) ≤ 2/t^2 := by
  have hc : Continuous (subcriticalPrimitive t pc) := by
    unfold subcriticalPrimitive
    fun_prop
  have hk : Continuous (fun x : ℝ ↦ Real.exp (-t * Real.sqrt (pc-x))) := by fun_prop
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hap hc.continuousOn
    (fun x hx ↦ subcriticalPrimitive_hasDerivAt ht hx.2) (hk.intervalIntegrable a pc)
  rw [H]
  have h0 := subcriticalPrimitive_nonneg (pc := pc) (x := a) ht.le
  have he : subcriticalPrimitive t pc pc = 2/t^2 := by simp [subcriticalPrimitive]
  rw [he]
  linarith

/-- Integration of an actual pointwise subcritical envelope. The envelope is a
visible premise, not a claimed proof of the paper's missing arm estimate. -/
theorem subcritical_integral_of_envelope {a pc t A : ℝ} {f : ℝ → ℝ}
    (hap : a ≤ pc) (ht : 0 < t) (hA : 0 ≤ A)
    (hf : IntervalIntegrable f volume a pc)
    (hbound : ∀ x ∈ Icc a pc, f x ≤ A * Real.exp (-t * Real.sqrt (pc-x))) :
    (∫ x in a..pc, f x) ≤ 2*A/t^2 := by
  have hc : Continuous (fun x : ℝ ↦ A * Real.exp (-t * Real.sqrt (pc-x))) := by fun_prop
  calc
    _ ≤ ∫ x in a..pc, A * Real.exp (-t * Real.sqrt (pc-x)) :=
      intervalIntegral.integral_mono_on hap hf (hc.intervalIntegrable a pc) hbound
    _ = A * ∫ x in a..pc, Real.exp (-t * Real.sqrt (pc-x)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ A * (2/t^2) := mul_le_mul_of_nonneg_left (subcritical_exp_sqrt_integral_le hap ht) hA
    _ = _ := by ring

/-- The paper's h^-3 subcritical perturbation order, without an unperformed
change of variables at the critical square-root endpoint. -/
theorem subcritical_window_integral_le {a pc h c K : ℝ} {f : ℝ → ℝ}
    (hap : a ≤ pc) (hh : 0 < h) (hc : 0 < c) (hK : 0 ≤ K)
    (hf : IntervalIntegrable f volume a pc)
    (hbound : ∀ x ∈ Icc a pc, f x ≤ (K/h) * Real.exp (-(c*h) * Real.sqrt (pc-x))) :
    (∫ x in a..pc, f x) ≤ (2*K/c^2)/h^3 := by
  have H := subcritical_integral_of_envelope hap (mul_pos hc hh)
    (div_nonneg hK hh.le) hf hbound
  apply H.trans_eq
  field_simp

/-- The supercritical interval of width at most h^-2 contributes at most K/h³
when its square-root auxiliary bound is K/h. -/
theorem supercritical_window_integral_le {pc p h K : ℝ} {f : ℝ → ℝ}
    (hpp : pc ≤ p) (hh : 0 < h) (hK : 0 ≤ K) (hwindow : p-pc ≤ 1/h^2)
    (hf : IntervalIntegrable f volume pc p)
    (hbound : ∀ x ∈ Icc pc p, f x ≤ K/h) :
    (∫ x in pc..p, f x) ≤ K/h^3 := by
  calc
    _ ≤ ∫ x in pc..p, K/h :=
      intervalIntegral.integral_mono_on hpp hf (intervalIntegrable_const) hbound
    _ = (p-pc)*(K/h) := by rw [intervalIntegral.integral_const]; rfl
    _ ≤ (1/h^2)*(K/h) := mul_le_mul_of_nonneg_right hwindow (div_nonneg hK hh.le)
    _ = _ := by field_simp

/-- The combined perturbation bound used after splitting at pc. Constants do
not depend on the lower endpoint or the supercritical interval width. -/
theorem upper_perturbation_integral_le {a pc p h c K : ℝ} {f : ℝ → ℝ}
    (hap : a ≤ pc) (hpp : pc ≤ p) (hh : 0 < h) (hc : 0 < c) (hK : 0 ≤ K)
    (hwindow : p-pc ≤ 1/h^2)
    (hsub : IntervalIntegrable f volume a pc) (hsup : IntervalIntegrable f volume pc p)
    (hboundSub : ∀ x ∈ Icc a pc, f x ≤ (K/h)*Real.exp (-(c*h)*Real.sqrt (pc-x)))
    (hboundSup : ∀ x ∈ Icc pc p, f x ≤ K/h) :
    (∫ x in a..p, f x) ≤ (2*K/c^2+K)/h^3 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals hsub hsup]
  calc
    _ ≤ (2*K/c^2)/h^3+K/h^3 := add_le_add
      (subcritical_window_integral_le hap hh hc hK hsub hboundSub)
      (supercritical_window_integral_le hpp hh hK hwindow hsup hboundSup)
    _ = _ := by ring

end NearCritical
