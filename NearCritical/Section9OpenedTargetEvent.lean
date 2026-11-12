module
public import NearCritical.Section9PivotalCount

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The opened-target count event is measurable in the critical and enriched configurations. -/
theorem section9_opened_target_event_measurable {d : ℕ} {ι : Type*}
    (I : Finset ι) (targets : ι → Finset (Vertex d))
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d)) (m : ℕ) :
    MeasurableSet {z : Configuration d × Configuration d | (m : ℝ) <
      ((I.filter fun j => (sprinkledPivotalPairs z.1 z.2
        E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} := by
  let H := fun j => {z : Configuration d × Configuration d |
    (sprinkledPivotalPairs z.1 z.2
      E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty}
  have hm (j : ι) : MeasurableSet (H j) := by
    have heq : H j = ⋃ e : Vertex d × Vertex d,
        ({z : Configuration d × Configuration d | e ∈ E} ∩
          {z | sprinklingPivotalPair z.1 L R Q₁ F₁ Q₃ F₃ A (targets j) e}) ∩
          {z | (openGraph z.2).Adj e.1 e.2} := by
      ext z
      simp only [H,sprinkledPivotalPairs,sprinklingPivotalPairs,Finset.Nonempty,
        Finset.mem_filter,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_setOf_eq]
    rw [heq]
    apply MeasurableSet.iUnion
    intro e
    exact ((MeasurableSet.const _).inter
      ((measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A (targets j) e).preimage measurable_fst)).inter
      ((measurableSet_open_adj e.1 e.2).preimage measurable_snd)
  have hcount : Measurable (fun z : Configuration d × Configuration d =>
      ((I.filter fun j => z ∈ H j).card : ℝ)) := by
    have heq : (fun z : Configuration d × Configuration d => ((I.filter fun j => z ∈ H j).card : ℝ)) =
        fun z => ∑ j ∈ I, if z ∈ H j then (1 : ℝ) else 0 := by
      funext z
      rw [Finset.sum_boole]
    rw [heq]
    exact I.measurable_fun_sum (fun j _ => measurable_const.piecewise (hm j) measurable_const)
  exact measurableSet_lt measurable_const hcount

end NearCritical
