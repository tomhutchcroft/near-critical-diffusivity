module
public import NearCritical.Section9ConditionedMarkedTree

/-! Fresh marked-arm events for replacement configurations: no pivotality
assumption is imposed on the replaced configuration. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Disjoint witnesses for the marked left arms and the right arm, in the
configuration with unavailable coordinates closed. This event permits the
replacement clusters to intersect outside those witnesses. -/
def section9LeftMarkedArmOccurrence {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (w : Vertex d) : Set (Configuration d) :=
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  {ω | DisjointOccurrence
    (connectionToSetEvent (L : Set (Vertex d)) e.1 {w} ∩
      connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
    (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d)))
    (extendConfiguration U (fun _ => false) (U.restrict ω))}

theorem section9_left_marked_arm_occurrence_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d)
    (ω η : Configuration d)
    (h : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = η b) :
    (ω ∈ section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w ↔
      η ∈ section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w) := by
  have he : (sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃).restrict ω =
      (sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃).restrict η := by
    funext b
    exact h b b.property
  simp only [section9LeftMarkedArmOccurrence, Set.mem_setOf_eq, he]

theorem measurableSet_section9LeftMarkedArmOccurrence {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d) :
    MeasurableSet (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w) := by
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let S : Set (U → Bool) := {ξ | DisjointOccurrence
    (connectionToSetEvent (L : Set (Vertex d)) e.1 {w} ∩
      connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
    (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d)))
    (extendConfiguration U (fun _ => false) ξ)}
  change MeasurableSet ((U.restrict : Configuration d → (U → Bool)) ⁻¹' S)
  exact (Set.toFinite S).measurableSet.preimage (Finset.measurable_restrict U)

/-- Closing unavailable coordinates cannot create a disjoint connection
witness absent from the original configuration. -/
theorem section9_left_marked_arm_occurrence_subset {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d) :
    section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w ⊆
      {ω | DisjointOccurrence
        (connectionToSetEvent (L : Set (Vertex d)) e.1 {w} ∩
          connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
        (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ω} := by
  intro ω hω
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  have hle : ∀ b, extendConfiguration U (fun _ => false) (U.restrict ω) b = true → ω b = true := by
    intro b hb
    by_cases hbU : b ∈ U
    · simpa [extendConfiguration,hbU,Finset.restrict] using hb
    · simp [extendConfiguration,hbU] at hb
  obtain ⟨F,H,hFfin,hHfin,hdis,hF,hH,hAF,hBH⟩ :=
    BK.openDisjointOccurrence_of_disjointOccurrence hω
  apply BK.OpenDisjointOccurrence.to_disjointOccurrence
    ⟨F,H,hFfin,hHfin,hdis,(fun b hb => hle b (hF b hb)),
      (fun b hb => hle b (hH b hb)),hAF,hBH⟩
  · intro ξ ζ h hξ
    exact ⟨connectionToSetEvent_increasing _ _ _ h hξ.1,
      connectionToSetEvent_increasing _ _ _ h hξ.2⟩
  · exact connectionToSetEvent_increasing _ _ _

/-- A marked-arm replacement event has the same finite tripod/right-arm
bound as a marked pivot, without requiring replacement pivotality. -/
theorem section9_left_marked_arm_occurrence_tree_bound {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d) :
    let P := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    (percolation d p).real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w) ≤
      (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u w * P x u)) *
        (percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) := by
  intro P
  let J := connectionToSetEvent (L : Set (Vertex d)) e.1 {w} ∩
    connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))
  let K := connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))
  have hJ : BK.Increasing J := by
    intro ω η h hω
    exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
      connectionToSetEvent_increasing _ _ _ h hω.2⟩
  refine (measureReal_mono (section9_left_marked_arm_occurrence_subset L R Q₁ F₁ Q₃ F₃ A B e w)
    (measure_ne_top _ _)).trans ?_
  exact (percolation_bk d p J K hJ (connectionToSetEvent_increasing _ _ _)).trans
    (mul_le_mul_of_nonneg_right (restricted_joint_connection_probability_le p L A e.1 w)
      measureReal_nonneg)

/-- Positive heart conditioning preserves this fresh marked-arm event. -/
theorem section9_conditioned_left_marked_arm_tree_bound {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (e : Vertex d × Vertex d) (w : Vertex d) :
    let P := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real
      (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w) ≤
      (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u w * P x u)) *
        (percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) := by
  intro P
  rw [section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
    (sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃)
    (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁)
    _ (measurableSet_section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w)
    (fun ω η h => section9_left_marked_arm_occurrence_local L R Q₁ F₁ Q₃ F₃ A B e w ω η h)]
  exact section9_left_marked_arm_occurrence_tree_bound p L R Q₁ F₁ Q₃ F₃ A B e w

end NearCritical
