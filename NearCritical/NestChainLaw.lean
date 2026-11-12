module

public import NearCritical.NestChainWeights
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! A genuine finite-history probability law for the normalized nest-chain
weights. Source exploration-to-transition-law identification remains open. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory
open scoped ENNReal

universe u

def NestTrace (X : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => X × NestTrace X n

instance nestTraceFintype (X : Type*) [Fintype X] (n : ℕ) : Fintype (NestTrace X n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (X × NestTrace X n))

instance nestTraceMeasurableSpace (X : Type*) (n : ℕ) : MeasurableSpace (NestTrace X n) := ⊤
instance nestTraceMeasurableSingletonClass (X : Type*) (n : ℕ) :
    MeasurableSingletonClass (NestTrace X n) where
  measurableSet_singleton _ := trivial

def nestTraceMass {X : Type*} (P : ℕ → X → X → ℝ) :
    (n : ℕ) → X → NestTrace X n → ℝ
  | 0,_,_ => 1
  | n+1,x,z => P n x z.1 * nestTraceMass P n z.1 z.2

def nestTraceWeight {X : Type*} [Fintype X] (P : ℕ → X → X → ℝ)
    (success : ℕ → X → X → Prop) : (n : ℕ) → X → NestTrace X n → ℝ
  | 0,_,_ => 1
  | n+1,x,z => nestSuccessWeight (P n) (success n) x z.1 * nestTraceWeight P success n z.1 z.2

lemma nestTraceMass_nonneg {X : Type*} (P : ℕ → X → X → ℝ) (N : ℕ)
    (hP : ∀ n<N, ∀ x y, 0≤P n x y) (x : X) (z : NestTrace X N) :
    0≤nestTraceMass P N x z := by
  induction N generalizing x with
  | zero => norm_num [nestTraceMass]
  | succ n ih =>
    exact mul_nonneg (hP n (by omega) x z.1)
      (ih (fun k hk x y => hP k (by omega) x y) z.1 z.2)

lemma nestTraceMass_sum {X : Type*} [Fintype X] (P : ℕ → X → X → ℝ) (N : ℕ)
    (hrow : ∀ n<N, ∀ x, ∑ y, P n x y=1) (x : X) :
    ∑ z : NestTrace X N, nestTraceMass P N x z = 1 := by
  induction N generalizing x with
  | zero =>
    let : Unique (NestTrace X 0) := inferInstanceAs (Unique PUnit)
    simp [nestTraceMass]
  | succ n ih =>
    change (∑ z : X × NestTrace X n, P n x z.1 * nestTraceMass P n z.1 z.2)=1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    have ht (y : X) := ih (fun k hk x => hrow k (by omega) x) y
    simp only [ht,mul_one]
    exact hrow n (by omega) x

/-- Actual probability mass function of the whole finite transition history. -/
def nestTraceLaw {X : Type*} [Fintype X] (P : ℕ → X → X → ℝ) (N : ℕ)
    (hP : ∀ n<N, ∀ x y, 0≤P n x y)
    (hrow : ∀ n<N, ∀ x, ∑ y, P n x y=1) (x : X) : PMF (NestTrace X N) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (nestTraceMass P N x z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => nestTraceMass_nonneg P N hP x z),
      nestTraceMass_sum P N hrow x]
    simp)

lemma nestTraceLaw_apply {X : Type*} [Fintype X] (P : ℕ → X → X → ℝ) (N : ℕ)
    (hP : ∀ n<N, ∀ x y, 0≤P n x y)
    (hrow : ∀ n<N, ∀ x, ∑ y, P n x y=1) (x : X) (z : NestTrace X N) :
    nestTraceLaw P N hP hrow x z = ENNReal.ofReal (nestTraceMass P N x z) := rfl

/-- The earlier recursion is exactly the finite path sum under transition masses. -/
lemma nestTrace_weighted_sum {X : Type*} [Fintype X] (P : ℕ → X → X → ℝ)
    (success : ℕ → X → X → Prop) (N : ℕ) (x : X) :
    ∑ z : NestTrace X N, nestTraceMass P N x z * nestTraceWeight P success N x z =
      nestWeightedPathExpectation P success N x := by
  induction N generalizing x with
  | zero =>
    let : Unique (NestTrace X 0) := inferInstanceAs (Unique PUnit)
    simp [nestTraceMass,nestTraceWeight,nestWeightedPathExpectation]
  | succ n ih =>
    change (∑ z : X × NestTrace X n,
      (P n x z.1 * nestTraceMass P n z.1 z.2) *
      (nestSuccessWeight (P n) (success n) x z.1 * nestTraceWeight P success n z.1 z.2)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [mul_mul_mul_comm, ← Finset.mul_sum, ih]
    rfl

/-- The normalized success product has integral one under the actual finite
trace law, not just a formal recurrence. No success independence is assumed. -/
theorem nestTraceLaw_integral_weight {X : Type*} [Fintype X]
    (P : ℕ → X → X → ℝ) (success : ℕ → X → X → Prop) (N : ℕ)
    (hP : ∀ n<N, ∀ x y, 0≤P n x y)
    (hrow : ∀ n<N, ∀ x, ∑ y, P n x y=1)
    (hs : ∀ n<N, ∀ x, 0<nestSuccessProbability (P n) (success n) x) (x : X) :
    ∫ z, nestTraceWeight P success N x z ∂(nestTraceLaw P N hP hrow x).toMeasure = 1 := by
  rw [PMF.integral_eq_sum]
  simp only [nestTraceLaw_apply,ENNReal.toReal_ofReal (nestTraceMass_nonneg P N hP x _),smul_eq_mul]
  rw [nestTrace_weighted_sum,nestWeightedPathExpectation_eq_one P success N hs x]

end NearCritical
