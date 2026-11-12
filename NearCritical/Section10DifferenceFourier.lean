module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-! Finite-history coefficient extraction for the actual paired lazy
coordinate increments in the corrected Section 10 intersection-tail proof.
This step uses finite orthogonality and does not require a Green bound. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate

-- Match the normalized Haar measure used by AddCircleMulti's Fourier APIs.
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem integral_character_pair {D : Type*} [Fintype D] (v w : D → ℤ) :
    (∫ t : UnitAddTorus D, mFourier (-w) t * mFourier v t) =
      if v = w then (1 : ℂ) else 0 := by
  classical
  simpa only [ContinuousMap.inner_toLp, ← mFourier_neg, mul_comm, eq_comm] using!
    (orthonormal_iff_ite.mp (orthonormal_mFourier (d := D))) w v

private theorem character_sum {D I : Type*} [Fintype D]
    (s : Finset I) (v : I → D → ℤ) (t : UnitAddTorus D) :
    mFourier (∑ i ∈ s, v i) t = ∏ i ∈ s, mFourier (v i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mFourier_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, mFourier_add, ih]

/-- The source transverse increment is either zero or one coordinate step. -/
def lazyCoordinateStep (D : ℕ) : Option (Fin D) → (Fin D → ℤ)
  | none => 0
  | some j => Pi.single j 1

/-- The original route increment law assigns half its mass to the zero step. -/
def lazyCoordinateWeight (D : ℕ) : Option (Fin D) → ℝ
  | none => 1/2
  | some _ => 1/(2*(D : ℝ))

/-- Actual difference step on independent route increment symbols. -/
def differenceStep (D : ℕ) (a : Option (Fin D) × Option (Fin D)) : Fin D → ℤ :=
  lazyCoordinateStep D a.1 - lazyCoordinateStep D a.2

def differenceStepWeight (D : ℕ) (a : Option (Fin D) × Option (Fin D)) : ℝ :=
  lazyCoordinateWeight D a.1 * lazyCoordinateWeight D a.2

/-- The finite characteristic polynomial of one actual difference step. -/
def differenceCharacteristic (D : ℕ) (t : UnitAddTorus (Fin D)) : ℂ :=
  ∑ a, (differenceStepWeight D a : ℂ) * mFourier (differenceStep D a) t

/-- Coefficient extraction for the finite product law of n actual paired
increments. In particular the zero coefficient is the return mass. -/
theorem differenceHistory_fourierCoeff (D n : ℕ) (w : Fin D → ℤ) :
    mFourierCoeff (fun t => differenceCharacteristic D t ^ n) w =
      ∑ h : Fin n → Option (Fin D) × Option (Fin D),
        if (∑ j, differenceStep D (h j)) = w then
          ∏ j, (differenceStepWeight D (h j) : ℂ) else 0 := by
  classical
  let wt := fun h : Fin n → Option (Fin D) × Option (Fin D) =>
    ∏ j, (differenceStepWeight D (h j) : ℂ)
  let pos := fun h : Fin n → Option (Fin D) × Option (Fin D) =>
    ∑ j, differenceStep D (h j)
  have hchar (t : UnitAddTorus (Fin D)) :
      differenceCharacteristic D t ^ n = ∑ h, wt h * mFourier (pos h) t := by
    calc
      _ = ∏ _j : Fin n, differenceCharacteristic D t := by simp
      _ = ∑ h : Fin n → Option (Fin D) × Option (Fin D),
          ∏ j, (differenceStepWeight D (h j) : ℂ) *
            mFourier (differenceStep D (h j)) t :=
        Fintype.prod_sum (fun (_j : Fin n) a =>
          (differenceStepWeight D a : ℂ) * mFourier (differenceStep D a) t)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.prod_mul_distrib]
        simp only [wt, pos, character_sum]
  unfold mFourierCoeff
  simp_rw [hchar, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro h _
    have heq : (fun t : UnitAddTorus (Fin D) => mFourier (-w) t *
        (wt h * mFourier (pos h) t)) =
        fun t => wt h * (mFourier (-w) t * mFourier (pos h) t) := by
      funext t
      ring
    change _ = if pos h = w then wt h else 0
    rw [heq, integral_const_mul]
    change wt h * (∫ t : UnitAddTorus (Fin D), mFourier (-w) t * mFourier (pos h) t) =
      if pos h = w then wt h else 0
    rw [integral_character_pair]
    split_ifs <;> simp
  · intro h _
    change Integrable _ (volume : Measure (UnitAddTorus (Fin D)))
    apply Continuous.integrable_of_hasCompactSupport
    · exact (mFourier (-w)).continuous.mul
        (continuous_const.mul (mFourier (pos h)).continuous)
    · exact HasCompactSupport.of_compactSpace _

end NearCritical.Section10
