module

public import NearCritical.IssuedPartition
public import NearCritical.LatticeFullConductivity
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Affine competitors bound full and relaxed finite-volume conductivity.
The annealed estimate uses the actual Bernoulli bond marginals. -/
@[expose] public section
namespace NearCritical
open Finset MeasureTheory
open scoped ENNReal

lemma issuedEnergy_coordinate {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) :
    issuedEnergy U ω (fun x => (x i : ℝ)) =
      ∑ x ∈ U, if ω (x,i) then (1 : ℝ) else 0 := by
  classical
  unfold issuedEnergy issuedBondSet
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single i]
  · simp [bondTip]
  · intro j hj hji
    simp [bondTip, Function.update_of_ne (Ne.symm hji)]
  · simp

/-- The affine coordinate function is a genuine full-Dirichlet competitor. -/
theorem fullConductivity_le_open_coordinate_count {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (ω : Configuration d) :
    fullConductivity U i ω ≤
      (∑ x ∈ U, if ω (x,i) then (1 : ℝ) else 0) / U.card := by
  have h := (issuedNetwork U).conductance_le_energy (domainWeights_nonneg ω)
    (show Network.admissible (fullBoundary U) (coordinateData i) (coordinateData i)
      from fun _ _ => rfl)
  have he := issuedEnergy_eq_network U ω (fun x => (x i : ℝ))
  rw [issuedEnergy_coordinate] at he
  exact div_le_div_of_nonneg_right (h.trans_eq he.symm) (Nat.cast_nonneg U.card)

lemma fullConductivity_le_one {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (ω : Configuration d) : fullConductivity U i ω ≤ 1 := by
  have hcount : (∑ x ∈ U, if ω (x,i) then (1 : ℝ) else 0) ≤ (U.card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ U, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        split <;> norm_num
      _ = _ := by simp
  by_cases hz : U.card = 0
  · simp [fullConductivity, hz]
  · have hp : (0 : ℝ) < U.card := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (fullConductivity_le_open_coordinate_count U i ω).trans
      ((div_le_one hp).2 hcount)

lemma integral_open_bond_indicator (d : ℕ) (p : unitInterval) (e : Bond d) :
    ∫ ω : Configuration d, (if ω e then (1 : ℝ) else 0) ∂percolation d p = (p : ℝ) := by
  have hm : MeasurableSet {ω : Configuration d | ω e = true} :=
    by
      change MeasurableSet ((fun ω : Configuration d => ω e) ⁻¹' {true})
      exact (measurable_pi_apply e) (measurableSet_singleton true)
  have he : (fun ω : Configuration d => if ω e then (1 : ℝ) else 0) =
      ({ω : Configuration d | ω e = true} : Set (Configuration d)).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    cases h : ω e <;> simp [h]
  rw [he, integral_indicator_const (1 : ℝ) hm]
  simp only [smul_eq_mul, mul_one]
  rw [measureReal_def, percolation_open_bond]
  exact ENNReal.toReal_ofReal p.2.1

lemma integrable_open_bond_indicator (d : ℕ) (p : unitInterval) (e : Bond d) :
    Integrable (fun ω : Configuration d => if ω e then (1 : ℝ) else 0) (percolation d p) := by
  have hm : MeasurableSet {ω : Configuration d | ω e = true} :=
    by
      change MeasurableSet ((fun ω : Configuration d => ω e) ⁻¹' {true})
      exact (measurable_pi_apply e) (measurableSet_singleton true)
  convert (integrable_const (μ := percolation d p) (1 : ℝ)).indicator hm using 1
  funext ω
  cases h : ω e <;> simp [h]

/-- Annealed full conductivity is at most p on every nonempty finite domain. -/
theorem annealedFull_le_parameter {d : ℕ} (U : Finset (Vertex d)) (hU : U.Nonempty)
    (i : Fin d) (p : unitInterval) : annealedFull U i (p : ℝ) ≤ (p : ℝ) := by
  classical
  have hc : (U.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hU)
  have hint : Integrable (fun ω : Configuration d =>
      (∑ x ∈ U, if ω (x,i) then (1 : ℝ) else 0) / U.card) (percolation d p) :=
    (integrable_finsetSum U (fun x _ => integrable_open_bond_indicator d p (x,i))).div_const _
  rw [annealedFull_eq_integral]
  calc
    _ ≤ ∫ ω : Configuration d,
        (∑ x ∈ U, if ω (x,i) then (1 : ℝ) else 0) / U.card ∂percolation d p :=
      integral_mono (integrable_fullConductivity U i p) hint
        (fullConductivity_le_open_coordinate_count U i)
    _ = (p : ℝ) := by
      rw [integral_div, integral_finsetSum U
        (fun x _ => integrable_open_bond_indicator d p (x,i))]
      simp only [integral_open_bond_indicator, Finset.sum_const, nsmul_eq_mul]
      exact mul_div_cancel_left₀ (p : ℝ) hc

lemma annealedRelaxed_le_parameter {d : ℕ} (U : Finset (Vertex d)) (hU : U.Nonempty)
    (i : Fin d) (p : unitInterval) : annealedRelaxed U i (p : ℝ) ≤ (p : ℝ) :=
  (annealedRelaxed_le_full U i p.2.1 p.2.2).trans (annealedFull_le_parameter U hU i p)

end NearCritical
