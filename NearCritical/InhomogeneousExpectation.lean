module

public import NearCritical.Mecke

/-! Independent coordinate profiles and mask derivatives for the paper's bulk
perturbation, eq.def.Pdelta and prop.inequality_diff_delta. Only coordinates in
M vary; no derivative or pivotal-support conclusion is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory ProbabilityTheory
open scoped Classical

/-- Explicit expectation under a finite coordinate-dependent Bernoulli profile.
The algebraic definition allows arbitrary real parameters. -/
def finiteExpectationProfile {E : Type*} [Fintype E] (r : E → ℝ)
    (f : (E → Bool) → ℝ) : ℝ :=
  ∑ ω, f ω * ∏ e, if ω e then r e else 1 - r e

/-- Vary the coordinates in M at s and leave all others at p. -/
def maskProfile {E : Type*} (M : Finset E) (p s : ℝ) (e : E) : ℝ :=
  if e ∈ M then s else p

lemma maskProfile_self {E : Type*} (M : Finset E) (p : ℝ) :
    maskProfile M p p = fun _ ↦ p := by
  ext e
  simp [maskProfile]

lemma finiteExpectationProfile_const {E : Type*} [Fintype E]
    (p : ℝ) (f : (E → Bool) → ℝ) :
    finiteExpectationProfile (fun _ ↦ p) f = finiteExpectation p f := rfl

/-- The actual independent infinite-product law with per-bond parameters. -/
def percolationProfile (d : ℕ) (r : Bond d → unitInterval) : Measure (Configuration d) :=
  Measure.infinitePi (fun e ↦ bernoulliMeasure true false (r e))

instance percolationProfile_isProbability (d : ℕ) (r : Bond d → unitInterval) :
    IsProbabilityMeasure (percolationProfile d r) := by
  unfold percolationProfile
  infer_instance

lemma percolationProfile_const (d : ℕ) (p : unitInterval) :
    percolationProfile d (fun _ ↦ p) = percolation d p := rfl

lemma finite_bernoulliProfile_singleton_real {E : Type*} [Fintype E]
    (r : E → unitInterval) (ω : E → Bool) :
    (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real {ω} =
      ∏ e, if ω e then (r e : ℝ) else 1 - (r e : ℝ) := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply prod_congr rfl
  intro e _
  cases ω e <;> simp [bernoulliMeasure_def]

lemma integral_finite_bernoulliProfile {E : Type*} [Fintype E]
    (r : E → unitInterval) (f : (E → Bool) → ℝ) :
    ∫ ω, f ω ∂(Measure.pi (fun e ↦ bernoulliMeasure true false (r e))) =
      finiteExpectationProfile (fun e ↦ (r e : ℝ)) f := by
  rw [integral_fintype (Integrable.of_finite : Integrable f _)]
  simp only [finiteExpectationProfile, finite_bernoulliProfile_singleton_real, smul_eq_mul]
  apply sum_congr rfl
  intro ω _
  exact mul_comm _ _

/-- Cylinder expectations under the actual infinite inhomogeneous law. -/
theorem percolationProfile_cylinder_expectation (d : ℕ) (r : Bond d → unitInterval)
    (s : Finset (Bond d)) (f : ((e : s) → Bool) → ℝ) :
    ∫ ω, f (s.restrict ω) ∂percolationProfile d r =
      finiteExpectationProfile (fun e : s ↦ (r e.val : ℝ)) f := by
  unfold percolationProfile
  rw [integral_restrict_infinitePi (μ := fun e : Bond d ↦ bernoulliMeasure true false (r e))
    (s := s) (f := f)
    (Integrable.of_finite : Integrable f (Measure.pi
      (fun e : s ↦ bernoulliMeasure true false (r e.val)))).aestronglyMeasurable]
  exact integral_finite_bernoulliProfile (fun e : s ↦ r e.val) f

namespace BernoulliCalculus
variable {E : Type*} [Fintype E]

def profileWeight (r : E → ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, if ω e then r e else 1 - r e

def profileDeletedWeight (r : E → ℝ) (e : E) (ω : E → Bool) : ℝ :=
  ∏ j ∈ univ.erase e, if ω j then r j else 1 - r j

def profileScore (r : E → ℝ) (e : E) (ω : E → Bool) : ℝ :=
  profileDeletedWeight r e ω * if ω e then 1 else -1

lemma profileDeletedWeight_flip (r : E → ℝ) (e : E) (ω : E → Bool) :
    profileDeletedWeight r e (flip e ω) = profileDeletedWeight r e ω := by
  apply prod_congr rfl
  intro j hj
  simp [flip, Function.update_of_ne (mem_erase.mp hj).1]

lemma profileWeight_split (r : E → ℝ) (e : E) (ω : E → Bool) :
    profileWeight r ω = (if ω e then r e else 1 - r e) * profileDeletedWeight r e ω := by
  exact (mul_prod_erase univ (fun j ↦ if ω j then r j else 1 - r j) (mem_univ e)).symm

lemma profile_paired_opening (r : E → ℝ) (e : E)
    (f : (E → Bool) → ℝ) (ω : E → Bool) :
    (1 - r e) * (f ω * profileScore r e ω +
      f (flip e ω) * profileScore r e (flip e ω)) =
      (f (forceOpen e ω) - f ω) * profileWeight r ω +
      (f (forceOpen e (flip e ω)) - f (flip e ω)) * profileWeight r (flip e ω) := by
  rw [profileWeight_split r e ω, profileWeight_split r e (flip e ω)]
  simp only [profileScore, profileDeletedWeight_flip, flip_open, flip_apply_self]
  cases h : ω e
  · have hf : flip e ω = forceOpen e ω := by simp [forceOpen, flip, h]
    simp only [Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
    rw [hf]
    ring
  · have ho : forceOpen e ω = ω := by
      simpa only [forceOpen] using
        (Function.update_eq_self_iff.mpr h.symm : Function.update ω e true = ω)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [ho]
    ring

lemma profileScore_opening_identity (r : E → ℝ) (e : E) (f : (E → Bool) → ℝ) :
    (1 - r e) * (∑ ω, f ω * profileScore r e ω) =
      finiteExpectationProfile r (fun ω ↦ f (forceOpen e ω) - f ω) := by
  have h : (∑ ω, (1 - r e) * (f ω * profileScore r e ω +
      f (flip e ω) * profileScore r e (flip e ω))) =
      ∑ ω, ((f (forceOpen e ω) - f ω) * profileWeight r ω +
      (f (forceOpen e (flip e ω)) - f (flip e ω)) * profileWeight r (flip e ω)) :=
    sum_congr rfl (fun ω _ ↦ profile_paired_opening r e f ω)
  rw [← mul_sum, sum_add_distrib, sum_add_distrib] at h
  rw [sum_flip e (fun ω ↦ f ω * profileScore r e ω),
    sum_flip e (fun ω ↦ (f (forceOpen e ω) - f ω) * profileWeight r ω)] at h
  change (1 - r e) * (∑ ω, f ω * profileScore r e ω) =
    ∑ ω, (f (forceOpen e ω) - f ω) * profileWeight r ω
  linarith

set_option backward.isDefEq.respectTransparency false in
lemma profileWeight_hasDerivAt (M : Finset E) (p s : ℝ) (ω : E → Bool) :
    HasDerivAt (fun t ↦ profileWeight (maskProfile M p t) ω)
      (∑ e ∈ M, profileScore (maskProfile M p s) e ω) s := by
  have hf (e : E) : HasDerivAt
      (fun t : ℝ ↦ if ω e then maskProfile M p t e else 1 - maskProfile M p t e)
      (if e ∈ M then (if ω e then 1 else -1) else 0) s := by
    by_cases he : e ∈ M
    · simp only [maskProfile, ite_eq_left he]
      cases ω e
      · convert! (hasDerivAt_id s).const_sub 1 using 1
      · convert! hasDerivAt_id s using 1
    · simp only [maskProfile, ite_eq_right he]
      exact hasDerivAt_const s _
  have h := HasDerivAt.fun_finsetProd (fun e (_ : e ∈ (univ : Finset E)) ↦ hf e)
  simpa only [profileWeight, profileScore, profileDeletedWeight, smul_eq_mul,
    mul_ite, mul_zero, sum_ite_mem, univ_inter] using h

/-- Partial-mask Russo: precisely the coordinates in M contribute. Other
parameters remain fixed at p. This algebraic derivative holds for every s!=1. -/
theorem finiteExpectationProfile_russo (M : Finset E) (p s : ℝ)
    (hs : s ≠ 1) (f : (E → Bool) → ℝ) :
    HasDerivAt (fun t ↦ finiteExpectationProfile (maskProfile M p t) f)
      ((1 - s)⁻¹ * ∑ e ∈ M, finiteExpectationProfile (maskProfile M p s)
        (fun ω ↦ f (forceOpen e ω) - f ω)) s := by
  have h := HasDerivAt.fun_sum (u := (univ : Finset (E → Bool)))
    (fun ω _ ↦ (profileWeight_hasDerivAt M p s ω).const_mul (f ω))
  have hsum : (∑ ω, f ω * ∑ e ∈ M, profileScore (maskProfile M p s) e ω) =
      (1 - s)⁻¹ * ∑ e ∈ M, finiteExpectationProfile (maskProfile M p s)
        (fun ω ↦ f (forceOpen e ω) - f ω) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro e he
    rw [← profileScore_opening_identity]
    simp only [maskProfile, ite_eq_left he]
    rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hs.symm), one_mul]
  rw [hsum] at h
  exact h

lemma profile_paired_mecke (r : E → ℝ) (e : E)
    (f : (E → Bool) → ℝ) (ω : E → Bool) :
    (f ω * (if ω e then 1 else 0)) * profileWeight r ω +
      (f (flip e ω) * (if flip e ω e then 1 else 0)) * profileWeight r (flip e ω) =
    r e * (f (forceOpen e ω) * profileWeight r ω +
      f (forceOpen e (flip e ω)) * profileWeight r (flip e ω)) := by
  rw [profileWeight_split r e ω, profileWeight_split r e (flip e ω)]
  simp only [profileDeletedWeight_flip, flip_open, flip_apply_self]
  cases h : ω e
  · have hf : flip e ω = forceOpen e ω := by simp [forceOpen, flip, h]
    simp only [Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
    rw [hf]
    ring
  · have ho : forceOpen e ω = ω := by
      simpa only [forceOpen] using
        (Function.update_eq_self_iff.mpr h.symm : Function.update ω e true = ω)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [ho]
    ring

/-- Coordinatewise Mecke for the actual independent profile weights. -/
theorem finiteExpectationProfile_mecke (r : E → ℝ) (e : E) (f : (E → Bool) → ℝ) :
    finiteExpectationProfile r (fun ω ↦ f ω * (if ω e then 1 else 0)) =
      r e * finiteExpectationProfile r (fun ω ↦ f (forceOpen e ω)) := by
  have h : (∑ ω, ((f ω * (if ω e then 1 else 0)) * profileWeight r ω +
      (f (flip e ω) * (if flip e ω e then 1 else 0)) * profileWeight r (flip e ω))) =
      ∑ ω, r e * (f (forceOpen e ω) * profileWeight r ω +
      f (forceOpen e (flip e ω)) * profileWeight r (flip e ω)) :=
    sum_congr rfl (fun ω _ ↦ profile_paired_mecke r e f ω)
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib] at h
  rw [sum_flip e (fun ω ↦ (f ω * (if ω e then 1 else 0)) * profileWeight r ω),
    sum_flip e (fun ω ↦ f (forceOpen e ω) * profileWeight r ω)] at h
  change (∑ ω, (f ω * (if ω e then 1 else 0)) * profileWeight r ω) =
    r e * (∑ ω, f (forceOpen e ω) * profileWeight r ω)
  linarith

/-- Mecke factor is s on a perturbed coordinate; no other profile coordinate
has been changed or homogenized. -/
theorem finiteExpectationProfile_mask_mecke (M : Finset E) (p s : ℝ)
    (e : E) (he : e ∈ M) (f : (E → Bool) → ℝ) :
    finiteExpectationProfile (maskProfile M p s) (fun ω ↦ f ω * (if ω e then 1 else 0)) =
      s * finiteExpectationProfile (maskProfile M p s) (fun ω ↦ f (forceOpen e ω)) := by
  simpa only [maskProfile, ite_eq_left he] using
    finiteExpectationProfile_mecke (maskProfile M p s) e f

end BernoulliCalculus
end NearCritical
