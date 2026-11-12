module
public import NearCritical.Section9PivotOpening
public import NearCritical.ChemicalThinning
public import NearCritical.Section9ConditionalLaw

/-! Exact enrichment marginal and conditioning on the FIRST reveal only. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Set
open scoped Classical

/-- The Bernoulli marginal of the OR of independent p and q bits. -/
def orParameter (p q : unitInterval) : unitInterval :=
  ⟨(p : ℝ)+(1-(p : ℝ))*(q : ℝ),
    add_nonneg p.property.1 (mul_nonneg (sub_nonneg.mpr p.property.2) q.property.1),by
      nlinarith [mul_nonneg (sub_nonneg.mpr p.property.2) (sub_nonneg.mpr q.property.2)]⟩

private def orBits {E : Type*} (z : (E → Bool) × (E → Bool)) : E → Bool :=
  fun e => z.1 e || z.2 e

private theorem measurable_orBits {E : Type*} : Measurable (orBits (E := E)) := by
  apply measurable_pi_iff.mpr
  intro e
  change Measurable (fun z : (E → Bool) × (E → Bool) => z.1 e || z.2 e)
  exact (measurable_of_finite (fun z : Bool × Bool => z.1 || z.2)).comp
    ((measurable_pi_apply e |>.comp (measurable_fst : Measurable (Prod.fst : (E → Bool) × (E → Bool) → _))).prodMk
      (measurable_pi_apply e |>.comp (measurable_snd : Measurable (Prod.snd : (E → Bool) × (E → Bool) → _))))

/-- The actual OR map on two full-lattice configurations is measurable. -/
theorem measurable_sprinkleOrConfiguration {d : ℕ} :
    Measurable (fun z : Configuration d × Configuration d => sprinkleOrConfiguration z.1 z.2) :=
  measurable_orBits

private theorem bernoulli_or_map (p q : unitInterval) :
    ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool => z.1 || z.2) = bernoulliMeasure true false (orParameter p q) := by
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  have hf : (((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool => z.1 || z.2)).real {false} = (1-(p : ℝ))*(1-(q : ℝ)) := by
    rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton false)]
    have heq : (fun z : Bool × Bool => z.1 || z.2) ⁻¹' ({false} : Set Bool) =
        ({false} : Set Bool) ×ˢ {false} := by
      ext ⟨a,b⟩
      cases a <;> cases b <;> simp
    rw [heq,measureReal_prod_prod]
    simp
  intro b
  cases b
  · have hr : (bernoulliMeasure true false (orParameter p q)).real {false} =
        (1-(p : ℝ))*(1-(q : ℝ)) := by
      have hr₀ : (bernoulliMeasure true false (orParameter p q)).real {false} =
          1-(orParameter p q : ℝ) := by simp
      rw [hr₀]
      change 1-((p : ℝ)+(1-(p : ℝ))*(q : ℝ)) = _
      ring
    exact hf.trans hr.symm
  · have hc : ({false} : Set Bool)ᶜ = {true} := by ext b; cases b <;> simp
    have htot := measureReal_add_measureReal_compl
      (μ := ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
        (fun z : Bool × Bool => z.1 || z.2)) (measurableSet_singleton false)
    rw [hc,hf,probReal_univ] at htot
    have hr : (bernoulliMeasure true false (orParameter p q)).real {true} =
        (p : ℝ)+(1-(p : ℝ))*(q : ℝ) := by simp [orParameter]
    rw [hr]
    nlinarith only [htot]

private theorem finite_or_map {E : Type*} [Fintype E] (p q : unitInterval) :
    ((Measure.pi fun _ : E => bernoulliMeasure true false p).prod
      (Measure.pi fun _ : E => bernoulliMeasure true false q)).map orBits =
        Measure.pi fun _ : E => bernoulliMeasure true false (orParameter p q) := by
  let equiv := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool E
  have he := (measurePreserving_arrowProdEquivProdArrow Bool Bool E
    (fun _ => bernoulliMeasure true false p) (fun _ => bernoulliMeasure true false q)).map_eq
  rw [← he,Measure.map_map measurable_orBits equiv.measurable]
  change (Measure.pi fun _ : E => (bernoulliMeasure true false p).prod
    (bernoulliMeasure true false q)).map (fun z e => (z e).1 || (z e).2) = _
  rw [Measure.pi_map_pi (f := fun _ (z : Bool × Bool) => z.1 || z.2)
    (fun _ => (measurable_of_finite _).aemeasurable)]
  simp only [bernoulli_or_map p q]

/-- The exact UNCONDITIONED enrichment marginal, proved for the full product
law rather than just its single-edge marginals. -/
theorem percolation_sprinkleOr_map (d : ℕ) (p q : unitInterval) :
    ((percolation d p).prod (percolation d q)).map
      (fun z => sprinkleOrConfiguration z.1 z.2) = percolation d (orParameter p q) := by
  change ((percolation d p).prod (percolation d q)).map (orBits (E := Bond d)) = _
  refine (Measure.isProjectiveLimit_infinitePi
    (fun _ : Bond d => bernoulliMeasure true false (orParameter p q))).unique ?_ |>.symm
  intro s
  have hsmeas : Measurable (s.restrict : Configuration d → (s → Bool)) :=
    measurable_pi_iff.mpr (fun e => measurable_pi_apply (e : Bond d))
  have hprod : ((percolation d p).prod (percolation d q)).map
      (Prod.map s.restrict s.restrict) =
      (Measure.pi fun _ : s => bernoulliMeasure true false p).prod
        (Measure.pi fun _ : s => bernoulliMeasure true false q) := by
    rw [← Measure.map_prod_map _ _ hsmeas hsmeas]
    simp only [percolation,Measure.infinitePi_map_restrict]
  rw [Measure.map_map hsmeas measurable_orBits]
  calc
    _ = (((percolation d p).prod (percolation d q)).map
        (Prod.map s.restrict s.restrict)).map orBits := by
      rw [Measure.map_map measurable_orBits (hsmeas.prodMap hsmeas)]
      rfl
    _ = _ := by rw [hprod,finite_or_map p q]

/-- The enriched law conditioned on the FIRST configuration's actual reveal
is the pushforward of its actual conditional law times an independent sample.
This is not conditioning an enriched-level reveal. Zero atoms are included. -/
theorem section9_sprinkle_or_reveal_coupling {d : ℕ} (p q : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) :
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).map
      (fun z => sprinkleOrConfiguration z.1 z.2) =
    (ProbabilityTheory.cond ((percolation d p).prod (percolation d q))
      ((section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ×ˢ Set.univ)).map
        (fun z => sprinkleOrConfiguration z.1 z.2) := by
  congr 1
  unfold section9RevealedLaw ProbabilityTheory.cond
  rw [Measure.prod_smul_left,Measure.restrict_prod_eq_prod_univ]
  simp only [Measure.prod_prod,measure_univ,mul_one]

end NearCritical
