module

public import NearCritical.ProductExpectation
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! Finite-volume Russo formula for arbitrary real observables. -/
@[expose] public section
noncomputable section
namespace NearCritical.BernoulliCalculus
open Finset
variable {E : Type*} [Fintype E]
open scoped Classical

noncomputable def weight (p : ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, if ω e then p else 1 - p

noncomputable def deletedWeight (p : ℝ) (e : E) (ω : E → Bool) : ℝ :=
  ∏ j ∈ univ.erase e, if ω j then p else 1 - p

noncomputable def score (p : ℝ) (e : E) (ω : E → Bool) : ℝ :=
  deletedWeight p e ω * if ω e then 1 else -1

/-- Force one coordinate open. The chosen decidable equality is kept inside
this definition so concrete and abstract edge types share one operation. -/
def forceOpen (e : E) (ω : E → Bool) : E → Bool := by
  classical
  exact Function.update ω e true

omit [Fintype E] in
lemma forceOpen_eq_update [DecidableEq E] (e : E) (ω : E → Bool) :
    forceOpen e ω = Function.update ω e true := by
  classical
  ext j
  by_cases hj : j = e <;> simp [forceOpen, hj]

def flip (e : E) (ω : E → Bool) : E → Bool :=
  Function.update ω e (!(ω e))

omit [Fintype E] in
lemma flip_involutive (e : E) : Function.Involutive (flip e) := by
  intro ω
  ext j
  by_cases hj : j = e <;> simp [flip, Function.update_apply, hj]

def flipEquiv (e : E) : (E → Bool) ≃ (E → Bool) :=
  Function.Involutive.toPerm (flip e) (flip_involutive e)

lemma sum_flip (e : E) (g : (E → Bool) → ℝ) :
    ∑ ω, g (flip e ω) = ∑ ω, g ω :=
  (flipEquiv e).sum_comp g

lemma deletedWeight_flip (p : ℝ) (e : E) (ω : E → Bool) :
    deletedWeight p e (flip e ω) = deletedWeight p e ω := by
  apply prod_congr rfl
  intro j hj
  simp [flip, Function.update_of_ne (mem_erase.mp hj).1]

lemma weight_split (p : ℝ) (e : E) (ω : E → Bool) :
    weight p ω = (if ω e then p else 1 - p) * deletedWeight p e ω := by
  exact (mul_prod_erase univ (fun j ↦ if ω j then p else 1 - p) (mem_univ e)).symm

omit [Fintype E] in
lemma flip_open (e : E) (ω : E → Bool) :
    forceOpen e (flip e ω) = forceOpen e ω := by
  simp [forceOpen, flip, Function.update_idem]

omit [Fintype E] in
lemma flip_apply_self (e : E) (ω : E → Bool) : flip e ω e = !(ω e) :=
  Function.update_self _ _ _

lemma paired_opening (p : ℝ) (e : E) (f : (E → Bool) → ℝ) (ω : E → Bool) :
    (1 - p) * (f ω * score p e ω + f (flip e ω) * score p e (flip e ω)) =
      (f (forceOpen e ω) - f ω) * weight p ω +
      (f (forceOpen e (flip e ω)) - f (flip e ω)) * weight p (flip e ω) := by
  rw [weight_split p e ω, weight_split p e (flip e ω)]
  simp only [score, deletedWeight_flip, flip_open, flip_apply_self]
  cases h : ω e
  · have hf : flip e ω = forceOpen e ω := by simp [forceOpen, flip, h]
    simp only [Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
    rw [hf]
    ring
  · have ho : forceOpen e ω = ω := by
      simpa only [forceOpen] using (Function.update_eq_self_iff.mpr h.symm : Function.update ω e true = ω)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [ho]
    ring

lemma score_opening_identity (p : ℝ) (e : E) (f : (E → Bool) → ℝ) :
    (1 - p) * (∑ ω, f ω * score p e ω) =
      NearCritical.finiteExpectation p (fun ω ↦ f (forceOpen e ω) - f ω) := by
  classical
  have h : (∑ ω, (1 - p) * (f ω * score p e ω + f (flip e ω) * score p e (flip e ω))) =
      ∑ ω, ((f (forceOpen e ω) - f ω) * weight p ω +
      (f (forceOpen e (flip e ω)) - f (flip e ω)) * weight p (flip e ω)) :=
    sum_congr rfl (fun ω _ ↦ paired_opening p e f ω)
  rw [← mul_sum, sum_add_distrib, sum_add_distrib] at h
  rw [sum_flip e (fun ω ↦ f ω * score p e ω),
    sum_flip e (fun ω ↦ (f (forceOpen e ω) - f ω) * weight p ω)] at h
  change (1 - p) * (∑ ω, f ω * score p e ω) =
    ∑ ω, (f (forceOpen e ω) - f ω) * weight p ω
  linarith

set_option backward.isDefEq.respectTransparency false in
lemma weight_hasDerivAt (p : ℝ) (ω : E → Bool) :
    HasDerivAt (fun q ↦ weight q ω) (∑ e, score p e ω) p := by
  have hf (e : E) : HasDerivAt (fun q : ℝ ↦ if ω e then q else 1 - q)
      (if ω e then 1 else -1) p := by
    cases ω e
    · convert! (hasDerivAt_id p).const_sub 1 using 1
    · convert! hasDerivAt_id p using 1
  simpa only [weight, score, deletedWeight, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (fun e (_ : e ∈ (univ : Finset E)) ↦ hf e)

/-- Russo's edge-opening formula, in the normalization used by the paper.
The formula is algebraic and holds at every real p other than 1. -/
theorem finiteExpectation_russo (p : ℝ) (hp : p ≠ 1) (f : (E → Bool) → ℝ) :
    HasDerivAt (fun q ↦ NearCritical.finiteExpectation q f)
      ((1 - p)⁻¹ * ∑ e, NearCritical.finiteExpectation p
        (fun ω ↦ f (forceOpen e ω) - f ω)) p := by
  classical
  have h := HasDerivAt.fun_sum (u := (univ : Finset (E → Bool)))
    (fun ω _ ↦ (weight_hasDerivAt p ω).const_mul (f ω))
  have hsum : (∑ ω, f ω * ∑ e, score p e ω) =
      (1 - p)⁻¹ * ∑ e, NearCritical.finiteExpectation p
        (fun ω ↦ f (forceOpen e ω) - f ω) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    rw [← score_opening_identity]
    rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hp.symm), one_mul]
  rw [hsum] at h
  exact h

end NearCritical.BernoulliCalculus
