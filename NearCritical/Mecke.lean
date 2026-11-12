module

public import NearCritical.Russo

/-! Mecke's identity for finite-edge observables. This is the case needed for
finite-volume energies; extension to arbitrary infinite-coordinate observables
is not asserted here. -/
@[expose] public section
noncomputable section
namespace NearCritical.BernoulliCalculus
open Finset
variable {E : Type*} [Fintype E]
open scoped Classical

lemma paired_mecke (p : ℝ) (e : E) (f : (E → Bool) → ℝ) (ω : E → Bool) :
    (f ω * (if ω e then 1 else 0)) * weight p ω +
      (f (flip e ω) * (if flip e ω e then 1 else 0)) * weight p (flip e ω) =
    p * (f (forceOpen e ω) * weight p ω +
      f (forceOpen e (flip e ω)) * weight p (flip e ω)) := by
  rw [weight_split p e ω, weight_split p e (flip e ω)]
  simp only [deletedWeight_flip, flip_open, flip_apply_self]
  cases h : ω e
  · have hf : flip e ω = forceOpen e ω := by simp [forceOpen, flip, h]
    simp only [Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
    rw [hf]
    ring
  · have ho : forceOpen e ω = ω := by simpa only [forceOpen] using (Function.update_eq_self_iff.mpr h.symm : Function.update ω e true = ω)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [ho]
    ring

/-- The finite-coordinate form of equation `eq.Mecke`. -/
theorem finiteExpectation_mecke (p : ℝ) (e : E) (f : (E → Bool) → ℝ) :
    finiteExpectation p (fun ω ↦ f ω * (if ω e then 1 else 0)) =
      p * finiteExpectation p (fun ω ↦ f (forceOpen e ω)) := by
  classical
  have h : (∑ ω, ((f ω * (if ω e then 1 else 0)) * weight p ω +
      (f (flip e ω) * (if flip e ω e then 1 else 0)) * weight p (flip e ω))) =
    ∑ ω, p * (f (forceOpen e ω) * weight p ω +
      f (forceOpen e (flip e ω)) * weight p (flip e ω)) :=
    sum_congr rfl (fun ω _ ↦ paired_mecke p e f ω)
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib] at h
  rw [sum_flip e (fun ω ↦ (f ω * (if ω e then 1 else 0)) * weight p ω),
    sum_flip e (fun ω ↦ f (forceOpen e ω) * weight p ω)] at h
  change (∑ ω, (f ω * (if ω e then 1 else 0)) * weight p ω) =
    p * (∑ ω, f (forceOpen e ω) * weight p ω)
  linarith

omit [Fintype E] in
/-- The elementary closed-edge condition in `lem.pivot_trick`.
The two-arm condition requires the subsequent geometric argument. -/
lemma opening_change_implies_closed (e : E) (f : (E → Bool) → ℝ) (ω : E → Bool)
    (h : f (forceOpen e ω) ≠ f ω) : ω e = false := by
  cases he : ω e
  · rfl
  · have hu : forceOpen e ω = ω := by simpa only [forceOpen] using (Function.update_eq_self_iff.mpr he.symm : Function.update ω e true = ω)
    exact False.elim (h (congrArg f hu))

end NearCritical.BernoulliCalculus

namespace NearCritical
open MeasureTheory ProbabilityTheory

/-- Mecke's identity for any finite-coordinate observable in the infinite
lattice model, with the edge retained in the selected coordinate set. -/
theorem percolation_cylinder_mecke (d : ℕ) (p : unitInterval) (s : Finset (Bond d))
    (e : s) (f : ((j : s) → Bool) → ℝ) :
    (∫ ω, f (s.restrict ω) * (if ω e.val then 1 else 0) ∂percolation d p) =
      (p : ℝ) * ∫ ω, f (BernoulliCalculus.forceOpen e (s.restrict ω)) ∂percolation d p := by
  classical
  have hl := percolation_cylinder_expectation d p s
    (fun η ↦ f η * (if η e then 1 else 0))
  have hr := percolation_cylinder_expectation d p s (fun η ↦ f (BernoulliCalculus.forceOpen e η))
  simp only [Finset.restrict] at hl
  calc
    _ = finiteExpectation (p : ℝ) (fun η ↦ f η * (if η e then 1 else 0)) := by
      convert! hl using 1
    _ = (p : ℝ) * finiteExpectation (p : ℝ) (fun η ↦ f (BernoulliCalculus.forceOpen e η)) :=
      BernoulliCalculus.finiteExpectation_mecke (p : ℝ) e f
    _ = _ := by
      congr 1
      convert! hr.symm using 1

end NearCritical
