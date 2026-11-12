module

public import NearCritical.Section9RevealPositiveAtoms
public import Mathlib.Probability.Kernel.CondDistrib

/-! Conditional expectation identified with actual fiber-conditioned measures.
Measurability of the observation and integrability of the observable are explicit. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Regular conditional distribution of the identity on a positive observation
atom is the literal normalized restriction to that fiber. -/
theorem section9_condDistrib_id_eq_cond {α β : Type*}
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsFiniteMeasure μ] (X : α → β) (hX : Measurable X) (a : β)
    (hpos : μ {ω | X ω = a} ≠ 0) :
    condDistrib id X μ a = ProbabilityTheory.cond μ {ω | X ω = a} := by
  have hmass : μ.map X {a} = μ {ω | X ω = a} := by
    rw [Measure.map_apply hX (measurableSet_singleton a)]
    rfl
  have hposMap : μ.map X {a} ≠ 0 := by
    rw [hmass]
    exact hpos
  ext s hs
  have hjoint : (μ.map (fun ω => (X ω,id ω))) ({a} ×ˢ s) = μ ({ω | X ω = a} ∩ s) := by
    rw [Measure.map_apply (hX.prodMk measurable_id) ((measurableSet_singleton a).prod hs)]
    congr 1
  rw [condDistrib_apply_of_ne_zero hX measurable_id a hposMap s, hmass, hjoint,
    ProbabilityTheory.cond_apply' hs μ]

/-- Countable observation fibers provide an actual version of conditional
expectation, rather than an assumed formula for a supplied remaining-bond law. -/
theorem section9_condExp_eq_fiber_integral {α β : Type*}
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {mβ : MeasurableSpace β} [MeasurableSingletonClass β] [Countable β]
    (μ : Measure α) [IsFiniteMeasure μ] (X : α → β) (hX : Measurable X)
    (f : α → ℝ) (hf : Integrable f μ) :
    μ[f | mβ.comap X] =ᵐ[μ]
      fun ω => ∫ ζ, f ζ ∂ProbabilityTheory.cond μ {z | X z = X ω} := by
  have hk := condExp_ae_eq_integral_condDistrib_id hX hf
  filter_upwards [hk,section9_ae_nonzero_fiber μ X] with ω hω hpos
  rw [hω,section9_condDistrib_id_eq_cond μ X hX (X ω) hpos]

end NearCritical
