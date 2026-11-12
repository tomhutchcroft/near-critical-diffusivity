module

public import NearCritical.Minimizer
public import NearCritical.Russo

/-! One-edge specialization of the mixed Dirichlet-energy identity. All
minimizers are supplied by finite-network attainment, including zero weights. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open Finset NearCritical.BernoulliCalculus
open scoped Classical

variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

def binaryWeights (η : E → Bool) (e : E) : ℝ := if η e then 1 else 0

omit [Fintype E] in
lemma binaryWeights_nonneg (η : E → Bool) (e : E) : 0 ≤ binaryWeights η e := by
  unfold binaryWeights
  split <;> norm_num

omit [Fintype E] in
lemma binaryWeights_le_one (η : E → Bool) (e : E) : binaryWeights η e ≤ 1 := by
  unfold binaryWeights
  split <;> norm_num

omit [Fintype E] in
lemma binaryWeights_opening_sub (η : E → Bool) (e j : E) :
    binaryWeights (forceOpen e η) j - binaryWeights η j =
      if j = e then 1 - binaryWeights η e else 0 := by
  classical
  by_cases hj : j = e
  · subst j
    simp [binaryWeights, forceOpen_eq_update]
  · simp [binaryWeights, forceOpen_eq_update, hj]

lemma pairing_binary_opening (η : E → Bool) (e : E) (u v : V → ℝ) :
    G.pairing (binaryWeights (forceOpen e η) - binaryWeights η) u v =
      (1 - binaryWeights η e) * G.gradient u e * G.gradient v e := by
  classical
  unfold pairing
  rw [Finset.sum_eq_single e]
  · simp [Pi.sub_apply, binaryWeights_opening_sub]
  · intro j _ hj
    simp [Pi.sub_apply, binaryWeights_opening_sub, hj]
  · simp

lemma energy_binary_opening (η : E → Bool) (e : E) (u : V → ℝ) :
    G.energy (binaryWeights (forceOpen e η) - binaryWeights η) u =
      (1 - binaryWeights η e) * (G.gradient u e) ^ 2 := by
  rw [← G.pairing_self, G.pairing_binary_opening]
  ring

def binaryMinimizer [Fintype V] (boundary : Set V) (data : V → ℝ) (η : E → Bool) : V → ℝ :=
  G.minimizer (binaryWeights_nonneg η) boundary data

lemma binaryMinimizer_spec [Fintype V] (boundary : Set V) (data : V → ℝ) (η : E → Bool) :
    G.IsMinimizer (binaryWeights η) boundary data (G.binaryMinimizer boundary data η) :=
  G.minimizer_spec (binaryWeights_nonneg η) boundary data

def binaryConductance (boundary : Set V) (data : V → ℝ) (η : E → Bool) : ℝ :=
  G.conductance (binaryWeights η) boundary data

lemma binaryConductance_eq_energy [Fintype V] (boundary : Set V) (data : V → ℝ)
    (η : E → Bool) :
    G.binaryConductance boundary data η =
      G.energy (binaryWeights η) (G.binaryMinimizer boundary data η) :=
  G.conductance_eq_energy_minimizer (binaryWeights_nonneg η) boundary data

/-- The mixed identity of `lem.comparison`, collapsed to the single opened edge. -/
theorem binaryConductance_opening_identity [Fintype V] (boundary : Set V) (data : V → ℝ)
    (η : E → Bool) (e : E) :
    G.binaryConductance boundary data (forceOpen e η) - G.binaryConductance boundary data η =
      (1 - binaryWeights η e) *
        G.gradient (G.binaryMinimizer boundary data (forceOpen e η)) e *
        G.gradient (G.binaryMinimizer boundary data η) e := by
  rw [G.binaryConductance_eq_energy, G.binaryConductance_eq_energy]
  rw [G.minimizer_mixed_identity (G.binaryMinimizer_spec boundary data η)
    (G.binaryMinimizer_spec boundary data (forceOpen e η))]
  exact G.pairing_binary_opening η e _ _

/-- Both variational comparison bounds, with no assumed minimizers. -/
theorem binaryConductance_opening_bounds [Fintype V] (boundary : Set V) (data : V → ℝ)
    (η : E → Bool) (e : E) :
    (1 - binaryWeights η e) *
        (G.gradient (G.binaryMinimizer boundary data (forceOpen e η)) e) ^ 2 ≤
      G.binaryConductance boundary data (forceOpen e η) - G.binaryConductance boundary data η ∧
    G.binaryConductance boundary data (forceOpen e η) - G.binaryConductance boundary data η ≤
      (1 - binaryWeights η e) * (G.gradient (G.binaryMinimizer boundary data η) e) ^ 2 := by
  rw [G.binaryConductance_eq_energy, G.binaryConductance_eq_energy]
  have h := G.minimizer_comparison (G.binaryMinimizer_spec boundary data η)
    (G.binaryMinimizer_spec boundary data (forceOpen e η))
  simpa only [G.energy_binary_opening] using h

lemma binaryConductance_opening_nonneg [Fintype V] (boundary : Set V) (data : V → ℝ)
    (η : E → Bool) (e : E) :
    0 ≤ G.binaryConductance boundary data (forceOpen e η) - G.binaryConductance boundary data η := by
  have h := (G.binaryConductance_opening_bounds boundary data η e).1
  exact (mul_nonneg (sub_nonneg.mpr (binaryWeights_le_one η e)) (sq_nonneg _)).trans h

/-- A genuine energy change forces a closed edge and nonzero voltage drops on
both sides of the opening identity. These are inputs to the two-arm support proof. -/
theorem binaryConductance_opening_change [Fintype V] (boundary : Set V) (data : V → ℝ)
    (η : E → Bool) (e : E)
    (h : G.binaryConductance boundary data (forceOpen e η) ≠ G.binaryConductance boundary data η) :
    η e = false ∧ G.gradient (G.binaryMinimizer boundary data (forceOpen e η)) e ≠ 0 ∧
      G.gradient (G.binaryMinimizer boundary data η) e ≠ 0 := by
  have hprod : (1 - binaryWeights η e) *
      G.gradient (G.binaryMinimizer boundary data (forceOpen e η)) e *
      G.gradient (G.binaryMinimizer boundary data η) e ≠ 0 := by
    rw [← G.binaryConductance_opening_identity]
    exact sub_ne_zero.mpr h
  obtain ⟨hfirst, hold⟩ := mul_ne_zero_iff.mp hprod
  obtain ⟨hweight, hopen⟩ := mul_ne_zero_iff.mp hfirst
  refine ⟨?_, hopen, hold⟩
  cases he : η e
  · rfl
  · exact False.elim (hweight (by simp [binaryWeights, he]))

/-- The source's positive-volume normalization for the mixed edge increment. -/
theorem normalized_binaryConductance_opening_identity [Fintype V] (boundary : Set V)
    (data : V → ℝ) (η : E → Bool) (e : E) (volume : ℝ) :
    G.binaryConductance boundary data (forceOpen e η) / volume -
      G.binaryConductance boundary data η / volume =
      ((1 - binaryWeights η e) *
        G.gradient (G.binaryMinimizer boundary data (forceOpen e η)) e *
        G.gradient (G.binaryMinimizer boundary data η) e) / volume := by
  rw [← sub_div, G.binaryConductance_opening_identity]

end NearCritical.Network
