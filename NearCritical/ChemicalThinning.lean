module

public import NearCritical.ChemicalConnection
public import Mathlib.MeasureTheory.Measure.Prod

/-! Independent Bernoulli thinning for bounded chemical connections. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Retain a bond precisely when both its original bit and retention bit are open. -/
def thinConfiguration {E : Type*} (z : (E → Bool) × (E → Bool)) : E → Bool :=
  fun e ↦ z.1 e && z.2 e

lemma measurable_thinConfiguration {E : Type*} :
    Measurable (thinConfiguration (E := E)) := by
  apply measurable_pi_iff.mpr
  intro e
  change Measurable (fun z : (E → Bool) × (E → Bool) ↦ z.1 e && z.2 e)
  exact (measurable_of_finite (fun z : Bool × Bool ↦ z.1 && z.2)).comp
    ((measurable_pi_apply e |>.comp (measurable_fst : Measurable (Prod.fst : (E → Bool) × (E → Bool) → _))).prodMk
      (measurable_pi_apply e |>.comp (measurable_snd : Measurable (Prod.snd : (E → Bool) × (E → Bool) → _))))

lemma bernoulli_and_map (p q r : unitInterval)
    (hr : (r : ℝ) = (p : ℝ) * (q : ℝ)) :
    ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool ↦ z.1 && z.2) = bernoulliMeasure true false r := by
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  have ht : (((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool ↦ z.1 && z.2)).real {true} = (r : ℝ) := by
    rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton true)]
    have heq : (fun z : Bool × Bool ↦ z.1 && z.2) ⁻¹' ({true} : Set Bool) =
        ({true} : Set Bool) ×ˢ {true} := by
      ext ⟨a,b⟩; cases a <;> cases b <;> simp
    rw [heq, measureReal_prod_prod]
    simpa using hr.symm
  intro b
  cases b
  · have hc : ({true} : Set Bool)ᶜ = {false} := by ext b; cases b <;> simp
    have htot := measureReal_add_measureReal_compl
      (μ := ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
        (fun z : Bool × Bool ↦ z.1 && z.2)) (measurableSet_singleton true)
    rw [hc, ht, probReal_univ] at htot
    have hb : (bernoulliMeasure true false r).real {false} = 1 - (r : ℝ) := by simp
    rw [hb]
    linarith
  · simpa using ht

lemma finite_thin_map {E : Type*} [Fintype E] (p q r : unitInterval)
    (hr : (r : ℝ) = (p : ℝ) * (q : ℝ)) :
    ((Measure.pi fun _ : E ↦ bernoulliMeasure true false p).prod
      (Measure.pi fun _ : E ↦ bernoulliMeasure true false q)).map thinConfiguration =
        Measure.pi fun _ : E ↦ bernoulliMeasure true false r := by
  let equiv := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool E
  have he := (measurePreserving_arrowProdEquivProdArrow Bool Bool E
    (fun _ ↦ bernoulliMeasure true false p) (fun _ ↦ bernoulliMeasure true false q)).map_eq
  rw [← he, Measure.map_map measurable_thinConfiguration equiv.measurable]
  change (Measure.pi fun _ : E ↦ (bernoulliMeasure true false p).prod
    (bernoulliMeasure true false q)).map
      (fun z e ↦ (z e).1 && (z e).2) = _
  rw [Measure.pi_map_pi (f := fun _ (z : Bool × Bool) ↦ z.1 && z.2)
    (fun _ ↦ (measurable_of_finite _).aemeasurable)]
  simp only [bernoulli_and_map p q r hr]

/-- Thinning two independent full-lattice samples gives the exact product law
with parameter p*q, not merely the correct one-bond marginals. -/
theorem percolation_thin_map (d : ℕ) (p q r : unitInterval)
    (hr : (r : ℝ) = (p : ℝ) * (q : ℝ)) :
    ((percolation d p).prod (percolation d q)).map thinConfiguration =
      percolation d r := by
  refine (Measure.isProjectiveLimit_infinitePi
    (fun _ : Bond d ↦ bernoulliMeasure true false r)).unique ?_ |>.symm
  intro s
  have hsmeas : Measurable (s.restrict : Configuration d → (s → Bool)) :=
    measurable_pi_iff.mpr (fun e ↦ measurable_pi_apply (e : Bond d))
  have hprod : ((percolation d p).prod (percolation d q)).map
      (Prod.map s.restrict s.restrict) =
      (Measure.pi fun _ : s ↦ bernoulliMeasure true false p).prod
        (Measure.pi fun _ : s ↦ bernoulliMeasure true false q) := by
    rw [← Measure.map_prod_map _ _ hsmeas hsmeas]
    simp only [percolation, Measure.infinitePi_map_restrict]
  rw [Measure.map_map hsmeas measurable_thinConfiguration]
  calc
    _ = (((percolation d p).prod (percolation d q)).map
        (Prod.map s.restrict s.restrict)).map thinConfiguration := by
      rw [Measure.map_map measurable_thinConfiguration
        (hsmeas.prodMap hsmeas)]
      rfl
    _ = _ := by rw [hprod, finite_thin_map p q r hr]

/-- Conditional survival bound: a certificate with at most m bonds survives
independent q-thinning with probability at least q^m. -/
lemma chemical_thinning_section {d : ℕ} (q : unitInterval) {x y : Vertex d} {m : ℕ}
    {ω : Configuration d} (hω : ω ∈ chemicalConnectionEvent x y m) :
    ENNReal.ofReal (q : ℝ) ^ m ≤
      percolation d q {ξ | thinConfiguration (ω, ξ) ∈ chemicalConnectionEvent x y m} := by
  obtain ⟨s, hs, hopen, hforce⟩ := chemicalConnectionEvent_open_certificate hω
  calc
    ENNReal.ofReal (q : ℝ) ^ m ≤ ENNReal.ofReal (q : ℝ) ^ s.card :=
      pow_le_pow_right_of_le_one' (by simpa using q.2.2) hs
    _ = percolation d q (Set.pi (s : Set (Bond d)) (fun _ ↦ {true})) := by
      rw [percolation_open_cylinder]
      simp
    _ ≤ _ := measure_mono (by
      intro ξ hξ
      apply hforce
      intro e he
      have hξe : ξ e = true := hξ e he
      simp [thinConfiguration, hopen e he, hξe])

/-- Integrated certificate survival for the actual independent lattice coupling. -/
theorem chemical_thinning_probability (d : ℕ) (p q r : unitInterval)
    (hr : (r : ℝ) = (p : ℝ) * (q : ℝ)) (x y : Vertex d) (m : ℕ) :
    ENNReal.ofReal (q : ℝ) ^ m * percolation d p (chemicalConnectionEvent x y m) ≤
      percolation d r (chemicalConnectionEvent x y m) := by
  let A := chemicalConnectionEvent x y m
  have hA : MeasurableSet A := measurableSet_chemicalConnectionEvent x y m
  rw [← percolation_thin_map d p q r hr,
    Measure.map_apply measurable_thinConfiguration hA,
    Measure.prod_apply (hA.preimage measurable_thinConfiguration)]
  rw [← lintegral_indicator_const hA (ENNReal.ofReal (q : ℝ) ^ m)]
  apply lintegral_mono
  intro ω
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω]
    exact chemical_thinning_section q hω
  · rw [Set.indicator_of_notMem hω]
    exact bot_le

/-- Real-probability form of integrated independent thinning. -/
theorem chemical_thinning_probability_real (d : ℕ) (p q r : unitInterval)
    (hr : (r : ℝ) = (p : ℝ) * (q : ℝ)) (x y : Vertex d) (m : ℕ) :
    (q : ℝ) ^ m * (percolation d p).real (chemicalConnectionEvent x y m) ≤
      (percolation d r).real (chemicalConnectionEvent x y m) := by
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (chemical_thinning_probability d p q r hr x y m)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal q.2.1, Measure.real] using h

/-- Source lem.chem.monotone, also allowing equality of the two parameters.
The chemical-distance event is the actual full-lattice bounded connection. -/
theorem chemicalConnection_probability_comparison (d : ℕ) (p p' : unitInterval)
    (hp' : 0 < (p' : ℝ)) (hpp : (p' : ℝ) ≤ (p : ℝ))
    (x y : Vertex d) (m : ℕ) :
    (percolation d p).real (chemicalConnectionEvent x y m) ≤
      ((p : ℝ) / (p' : ℝ)) ^ m *
        (percolation d p').real (chemicalConnectionEvent x y m) := by
  have hp : 0 < (p : ℝ) := hp'.trans_le hpp
  let q : unitInterval := ⟨(p' : ℝ) / (p : ℝ),
    div_nonneg p'.2.1 p.2.1, (div_le_one hp).mpr hpp⟩
  have hq : (p' : ℝ) = (p : ℝ) * (q : ℝ) := by
    dsimp [q]
    field_simp
  have h := chemical_thinning_probability_real d p q p' hq x y m
  have hpos : 0 < ((p' : ℝ) / (p : ℝ)) ^ m := pow_pos (div_pos hp' hp) m
  calc
    _ ≤ (percolation d p').real (chemicalConnectionEvent x y m) /
        ((p' : ℝ) / (p : ℝ)) ^ m :=
      (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using h)
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow, inv_div]; ring

end NearCritical
