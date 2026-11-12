module

public import NearCritical.Section10PreGoodUpper

/-! `prop.proba.pregood` reduced to its lower count at the origin cube.

* `measurableSet_isPreGoodCube`: pre-goodness is a finite-bond event.
* `preGood_integral_ge`: the pre-good probability is at least one minus the
  two count-failure probabilities.
* `hpre_of_lower_count`: at `p_c`, if the lower count of the ORIGIN cube fails
  with probability at most `eta`, then every cube is pre-good with probability
  at least `1 - eta - eps/3` (upper count: `typical_count_upper_failure`;
  other cubes: translation invariance).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
open MeasureTheory

theorem measurableSet_isPreGoodCube {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (z : Vertex d) : MeasurableSet {ω : Configuration d | IsPreGoodCube typ t z ω} := by
  have he : {ω : Configuration d | IsPreGoodCube typ t z ω} =
      (internalBondSet (typicalCube t z)).restrict ⁻¹'
        {η | IsPreGoodCube typ t z (reconstructInterior (typicalCube t z) η)} := by
    ext ω
    exact isPreGoodCube_reconstruct typ t z ω
  rw [he]
  exact (Finset.measurable_restrict _) (Set.toFinite _).measurableSet

theorem preGood_integral_ge {d : ℕ} (p : unitInterval) (typ : TypicalParameters) (t : ℕ)
    (z : Vertex d) {η₁ η₂ : ℝ}
    (hlow : (percolation d p).real
      {ω | ¬ typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤
        ((typicalClusterFamily typ t z ω).card : ℝ)} ≤ η₁)
    (hup : (percolation d p).real
      {ω | ¬ ((typicalClusterFamily typ t z ω).card : ℝ) ≤
        typ.countUpper * (2 * (t : ℝ)) ^ (d - 6)} ≤ η₂) :
    1 - η₁ - η₂ ≤ ∫ ω, (if IsPreGoodCube typ t z ω then (1:ℝ) else 0) ∂(percolation d p) := by
  have hmeas := measurableSet_isPreGoodCube typ t z
  have hind : (fun ω : Configuration d => if IsPreGoodCube typ t z ω then (1:ℝ) else 0) =
      Set.indicator {ω | IsPreGoodCube typ t z ω} (fun _ => (1:ℝ)) := by
    funext ω
    simp only [Set.indicator, Set.mem_setOf_eq]
  rw [hind, integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
  have hcompl : (percolation d p).real {ω | IsPreGoodCube typ t z ω}ᶜ =
      1 - (percolation d p).real {ω | IsPreGoodCube typ t z ω} := by
    rw [measureReal_compl hmeas]
    simp
  have hsub : {ω : Configuration d | IsPreGoodCube typ t z ω}ᶜ ⊆
      {ω | ¬ typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤
        ((typicalClusterFamily typ t z ω).card : ℝ)} ∪
      {ω | ¬ ((typicalClusterFamily typ t z ω).card : ℝ) ≤
        typ.countUpper * (2 * (t : ℝ)) ^ (d - 6)} := by
    intro ω hω
    by_contra hne
    apply hω
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hne
    exact ⟨hne.1, hne.2⟩
  have h1 := (measureReal_mono (μ := percolation d p) hsub (measure_ne_top (percolation d p) _)).trans (measureReal_union_le _ _)
  linarith

/-- **`hpre` from the lower count at the origin cube.** -/
theorem hpre_of_lower_count {d : ℕ} (i : Fin d) (hd : 6 ≤ d) (typ : TypicalParameters)
    (t : ℕ) (ht : 3 ≤ t) {C ε η : ℝ} (hC : 0 < C) (ordinary : OrdinaryArmWindowInput d C)
    (hv : 0 < typ.volumeLower) (hε : 0 < ε)
    (hup : 27 * C / (typ.volumeLower * ε) ≤ typ.countUpper)
    (hlow : (percolation d (criticalPoint d)).real
      {ω | ¬ typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤
        ((typicalClusterFamily typ t (0 : Vertex d) ω).card : ℝ)} ≤ η)
    (a : Vertex d) :
    1 - η - ε / 3 ≤ ∫ ω, (if IsPreGoodCube typ t a ω then (1:ℝ) else 0)
      ∂(percolation d (criticalPoint d)) :=
  preGood_all_of_origin _ typ t _
    (preGood_integral_ge _ typ t 0 hlow
      (typical_count_upper_failure i hd typ t ht hC ordinary hv hε hup)) a

end NearCritical.Section10
