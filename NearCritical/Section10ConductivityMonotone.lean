module

public import NearCritical.LatticeFullConductivity
public import NearCritical.PercolationMonotonicity
public import NearCritical.TriadicDirichletLimit
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.MeasureTheory.Integral.Prod

/-! Section10 final proof: actual full-cube parameter monotonicity from existing
Rayleigh comparison and exact finite thinning coupling; transfer to limits. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Filter
open scoped Classical Topology

/-- Actual local full-boundary conductivity is increasing in its physical
issued-bond assignment, including zero-conductance and empty-domain cases. -/
theorem localFullConductivity_config_mono {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {η ξ : IssuedBond U → Bool} (hηξ : BK.ConfigLE η ξ) :
    localFullConductivity U i η ≤ localFullConductivity U i ξ := by
  have hw (e : IssuedBond U) : (if η e then (1:ℝ) else 0) ≤ if ξ e then 1 else 0 := by
    cases he : η e
    · simp only [he,Bool.false_eq_true,ite_false]
      split <;> norm_num
    · have hf := hηξ e he
      simp [he,hf]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg U.card)
  exact (issuedNetwork U).conductance_mono
    (fun e => by split <;> norm_num) hw (fullBoundary U) (coordinateData i)

private theorem finite_expectation_parameter_le {E : Type*} [Fintype E]
    (f : (E → Bool) → ℝ) (hmono : ∀ η ξ, BK.ConfigLE η ξ → f η ≤ f ξ)
    {p q : unitInterval} (hpq : p ≤ q) : finiteExpectation (p:ℝ) f ≤ finiteExpectation (q:ℝ) f := by
  by_cases hq : (q:ℝ) = 0
  · have heq : p = q := by
      apply Subtype.ext
      exact le_antisymm hpq (by simpa only [hq] using p.2.1)
    rw [heq]
  · have hqpos : 0 < (q:ℝ) := lt_of_le_of_ne q.2.1 (Ne.symm hq)
    let r : unitInterval := ⟨(p:ℝ)/(q:ℝ),div_nonneg p.2.1 q.2.1,(div_le_one hqpos).mpr hpq⟩
    have hr : (p:ℝ) = (q:ℝ)*(r:ℝ) := by dsimp [r]; field_simp
    have hmap := finite_thin_map (E := E) q r p hr
    calc
      _ = ∫ η, f η ∂(Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false p)) :=
        (integral_finite_bernoulli p f).symm
      _ = ∫ z : (E → Bool) × (E → Bool), f (thinConfiguration z)
          ∂((Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false q)).prod
            (Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false r))) := by
        rw [← hmap]
        exact integral_map measurable_thinConfiguration.aemeasurable
          (measurable_of_finite f).aestronglyMeasurable
      _ ≤ ∫ z : (E → Bool) × (E → Bool), f z.1
          ∂((Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false q)).prod
            (Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false r))) := by
        exact integral_mono Integrable.of_finite Integrable.of_finite
          (fun z => hmono _ _ (thinConfiguration_le_left z))
      _ = ∫ η, f η ∂(Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false q)) := by
        rw [integral_fun_fst]
        simp only [probReal_univ,one_smul]
      _ = _ := integral_finite_bernoulli q f

/-- ACTUAL annealed full conductivity is monotone in the percolation parameter.
No monotonicity of expectations is assumed; exact finite thinning proves it. -/
theorem annealedFull_parameter_mono {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {p q : unitInterval} (hpq : p ≤ q) :
    annealedFull U i (p:ℝ) ≤ annealedFull U i (q:ℝ) := by
  exact finite_expectation_parameter_le (localFullConductivity U i)
    (fun η ξ h => localFullConductivity_config_mono U i h) hpq

/-- Monotonicity transfers to supplied limits of the actual full-cube means
along the SAME box sequence. Existence/identification of those limits remains
the named standard homogenization obligation, not a conclusion of this lemma. -/
theorem coefficient_mono_of_cube_limits {d : ℕ} (i : Fin d) (radii : ℕ → ℕ)
    {p q : unitInterval} (hpq : p ≤ q) {κp κq : ℝ}
    (hp : Tendsto (fun M => annealedFull (centeredBox d (radii M)) i (p:ℝ)) atTop (𝓝 κp))
    (hq : Tendsto (fun M => annealedFull (centeredBox d (radii M)) i (q:ℝ)) atTop (𝓝 κq)) :
    κp ≤ κq := by
  exact le_of_tendsto_of_tendsto hp hq
    (Filter.Eventually.of_forall (fun M => annealedFull_parameter_mono (centeredBox d (radii M)) i hpq))

/-- The source near-critical cubic lower rate extends to ALL p>pc using
monotonicity DERIVED from actual cube means and the existing named triadic
limit interface. No monotonicity or all-parameter rate premise is supplied. -/
theorem global_cubic_lower_of_near_critical {d : ℕ} (i : Fin d) (κ : ℝ → ℝ)
    (hlimit : TriadicDirichletLimitInput d i κ) (p1 : unitInterval)
    (hp1 : criticalPoint d < p1) {c : ℝ} (hc : 0 < c)
    (hnear : ∀ p : unitInterval, criticalPoint d < p → p ≤ p1 →
      c*((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ κ (p:ℝ)) :
    ∃ D : ℝ, 0 < D ∧ ∀ p : unitInterval, criticalPoint d < p →
      D*((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ κ (p:ℝ) := by
  let gap1 := (p1:ℝ)-(criticalPoint d:ℝ)
  let D := c*gap1^3
  have hg1 : 0 < gap1 := sub_pos.mpr hp1
  have hg1le : gap1 ≤ 1 := by dsimp [gap1]; linarith [p1.2.2,(criticalPoint d).2.1]
  have hgcube : gap1^3 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hg1.le hg1le 3
  have hD : 0 < D := by dsimp [D]; positivity
  have hDc : D ≤ c := by
    have h := mul_le_mul_of_nonneg_left hgcube hc.le
    simpa only [mul_one] using h
  refine ⟨D,hD,?_⟩
  intro p hp
  by_cases hsmall : p ≤ p1
  · exact (mul_le_mul_of_nonneg_right hDc (pow_nonneg (sub_pos.mpr (show (criticalPoint d:ℝ) < (p:ℝ) from hp)).le _)).trans
      (hnear p hp hsmall)
  · have hp1p : p1 ≤ p := le_of_not_ge hsmall
    have hmono : κ (p1:ℝ) ≤ κ (p:ℝ) :=
      coefficient_mono_of_cube_limits i (fun m => triadicCubeRadius 0 m) hp1p
        (hlimit p1 hp1 0) (hlimit p hp 0)
    have hgap : 0 ≤ (p:ℝ)-(criticalPoint d:ℝ) := (sub_pos.mpr (show (criticalPoint d:ℝ) < (p:ℝ) from hp)).le
    have hgaple : (p:ℝ)-(criticalPoint d:ℝ) ≤ 1 := by linarith [p.2.2,(criticalPoint d).2.1]
    have hpcube : ((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hgap hgaple 3
    calc
      _ ≤ D*1 := mul_le_mul_of_nonneg_left hpcube hD.le
      _ = c*((p1:ℝ)-(criticalPoint d:ℝ))^3 := by dsimp [D,gap1]; ring
      _ ≤ κ (p1:ℝ) := hnear p1 hp1 le_rfl
      _ ≤ κ (p:ℝ) := hmono

end NearCritical.Section10
