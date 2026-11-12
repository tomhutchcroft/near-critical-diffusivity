module
public import NearCritical.Section9OpenedTargetEvent
public import NearCritical.Section9SprinkleJointLabelLaw

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Transport the opened-target count through the joint law conditioned on the
critical configuration's reveal. -/
theorem section9_opened_target_label_probability_eq {d : ℕ} {ι : Type*}
    (p q : unitInterval) (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (I : Finset ι) (targets : ι → Finset (Vertex d))
    (E : Finset (Vertex d × Vertex d)) (L R A : Finset (Vertex d)) (m : ℕ) :
    let S : Set (Configuration d × Configuration d) :=
      {z | (m : ℝ) < ((I.filter fun j =>
        (sprinkledPivotalPairs z.1 z.2 E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)}
    let labels := Measure.infinitePi fun _ : Bond d => (volume : Measure unitInterval)
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
      ((fun z => (z.1, sprinkleOrConfiguration z.1 z.2)) ⁻¹' S) =
    (ProbabilityTheory.cond labels ((labelConfiguration p) ⁻¹'
      section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃)).real
      ((fun u => (labelConfiguration p u, labelConfiguration (orParameter p q) u)) ⁻¹' S) := by
  intro S labels
  have hS : MeasurableSet S :=
    section9_opened_target_event_measurable I targets E L R Q₁ F₁ Q₃ F₃ A m
  have h := congrArg (fun μ : Measure (Configuration d × Configuration d) => μ.real S)
    (section9_sprinkle_or_joint_reveal_label_law p q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃)
  rw [map_measureReal_apply (measurable_fst.prodMk measurable_sprinkleOrConfiguration) hS,
    map_measureReal_apply ((measurable_labelConfiguration p).prodMk
      (measurable_labelConfiguration (orParameter p q))) hS] at h
  exact h

end NearCritical
