module

public import NearCritical.SplitCrossStar
public import NearCritical.ProductExpectation
public import Mathlib.Probability.Independence.InfinitePi

/-! A fixed bond pattern has its exact Bernoulli mass and is independent of
the event read on the disjoint outside bonds. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory ProbabilityTheory
open scoped Classical

theorem prescribed_bonds_probability {d : ℕ} (p : unitInterval) (S : Finset (Bond d))
    (η : S → Bool) :
    (percolation d p).real (S.restrict ⁻¹' {η}) =
      ∏ e : S, if η e then (p : ℝ) else 1 - (p : ℝ) := by
  have hm : (percolation d p).map S.restrict =
      Measure.pi (fun _ : S => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  rw [← map_measureReal_apply (Finset.measurable_restrict S) (measurableSet_singleton η), hm]
  exact finite_bernoulli_singleton_real p η

/-- A cardinality bound on the prescribed bonds gives a uniform finite-energy
constant for every assignment. -/
theorem prescribed_bonds_probability_lower {d M : ℕ} (p : unitInterval)
    (S : Finset (Bond d)) (η : S → Bool) (hS : S.card ≤ M) :
    (min (p : ℝ) (1 - (p : ℝ))) ^ M ≤ (percolation d p).real (S.restrict ⁻¹' {η}) := by
  let a := min (p : ℝ) (1 - (p : ℝ))
  have ha : 0 ≤ a := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have ha1 : a ≤ 1 := (min_le_left _ _).trans p.2.2
  rw [prescribed_bonds_probability]
  calc
    a ^ M ≤ a ^ S.card := pow_le_pow_of_le_one ha ha1 hS
    _ = ∏ _e : S, a := by simp
    _ ≤ ∏ e : S, if η e then (p : ℝ) else 1 - (p : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => ha)
      intro e _
      cases η e
      · simpa [a] using min_le_right (p : ℝ) (1 - (p : ℝ))
      · simpa [a] using min_le_left (p : ℝ) (1 - (p : ℝ))

theorem prescribed_bonds_factor {d : ℕ} (p : unitInterval) (S T : Finset (Bond d))
    (hd : Disjoint S T) (η : S → Bool) (A : Set (T → Bool)) :
    (percolation d p).real (S.restrict ⁻¹' {η} ∩ T.restrict ⁻¹' A) =
      (percolation d p).real (S.restrict ⁻¹' {η}) *
        (percolation d p).real (T.restrict ⁻¹' A) := by
  have hi : IndepFun (S.restrict : Configuration d → (S → Bool))
      (T.restrict : Configuration d → (T → Bool)) (percolation d p) :=
    iIndepFun.indepFun_finset S T hd
      (iIndepFun_infinitePi (fun _ : Bond d => (measurable_id : Measurable (id : Bool → Bool))))
      (fun e => measurable_pi_apply e)
  have h := hi.measure_inter_preimage_eq_mul {η} A (measurableSet_singleton η)
    (Set.toFinite A).measurableSet
  simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h

theorem starPattern_eq_prescribed {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) :
    starPattern b axes R = (starGuardBonds b axes R).restrict ⁻¹'
      ({(fun e : ↥(starGuardBonds b axes R) => decide (e.val ∈ starBonds b axes R))} :
        Set (↥(starGuardBonds b axes R) → Bool)) := by
  ext ω
  simp only [starPattern, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext e
    exact h e.val e.property
  · intro h e he
    exact congrFun h ⟨e, he⟩

end NearCritical.SplitCrossDirect
