module
public import NearCritical.HalfSpaceTranslation

/-! Actual central inversion of the lattice law, needed to compare BOTH water
cube faces with the positive half-space arm. Positive-coordinate bonds reverse
their endpoints, so their new base is the negative OLD tip. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory Set

lemma bondTip_neg_tip {d : ℕ} (e : Bond d) : bondTip (-bondTip e, e.2) = -e.1 := by
  ext j
  by_cases hj : j = e.2
  · subst j; simp [bondTip]
  · simp [bondTip, Function.update_of_ne hj]

def invertBond {d : ℕ} : Bond d ≃ Bond d where
  toFun e := (-bondTip e, e.2)
  invFun e := (-bondTip e, e.2)
  left_inv e := by simp [bondTip_neg_tip]
  right_inv e := by simp [bondTip_neg_tip]

def invertConfiguration {d : ℕ} (ω : Configuration d) : Configuration d :=
  fun e => ω (invertBond e)

lemma measurable_invertConfiguration {d : ℕ} : Measurable (invertConfiguration (d := d)) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

theorem percolation_map_inversion {d : ℕ} (p : unitInterval) :
    (percolation d p).map invertConfiguration = percolation d p := by
  change (Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)).map
    (fun ω e => ω (invertBond e)) = _
  simpa [percolation, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft'] using
    (Measure.infinitePi_map_piCongrLeft
      (fun _ : Bond d => bernoulliMeasure true false p) invertBond.symm)

lemma openGraph_invert_adj {d : ℕ} (ω : Configuration d) (x y : Vertex d) :
    (openGraph (invertConfiguration ω)).Adj x y ↔ (openGraph ω).Adj (-x) (-y) := by
  constructor
  · rintro ⟨e, he, h | h⟩
    · refine ⟨invertBond e, he, Or.inr ?_⟩
      exact ⟨by simp [invertBond, h.2], by simp [invertBond, bondTip_neg_tip, h.1]⟩
    · refine ⟨invertBond e, he, Or.inl ?_⟩
      exact ⟨by simp [invertBond, h.2], by simp [invertBond, bondTip_neg_tip, h.1]⟩
  · rintro ⟨e, he, h | h⟩
    · refine ⟨invertBond e, ?_, Or.inr ?_⟩
      · simpa [invertConfiguration, invertBond, bondTip_neg_tip] using he
      · constructor
        · have := congrArg Neg.neg h.2; simpa [invertBond] using this
        · have := congrArg Neg.neg h.1; simpa [invertBond, bondTip_neg_tip] using this
    · refine ⟨invertBond e, ?_, Or.inl ?_⟩
      · simpa [invertConfiguration, invertBond, bondTip_neg_tip] using he
      · constructor
        · have := congrArg Neg.neg h.2; simpa [invertBond] using this
        · have := congrArg Neg.neg h.1; simpa [invertBond, bondTip_neg_tip] using this

def restrictedInversionGraphIso {d : ℕ} (ω : Configuration d) (S : Set (Vertex d)) :
    restrictedGraph (invertConfiguration ω) S ≃g restrictedGraph ω (Neg.neg '' S) where
  toEquiv := Equiv.neg _
  map_rel_iff' := by
    intro x y
    change ((openGraph ω).Adj (-x) (-y) ∧ -x ∈ Neg.neg '' S ∧ -y ∈ Neg.neg '' S) ↔
      ((openGraph (invertConfiguration ω)).Adj x y ∧ x ∈ S ∧ y ∈ S)
    rw [← openGraph_invert_adj]
    simp

lemma connectionToSetEvent_inversion {d : ℕ} (x : Vertex d) (S B : Set (Vertex d)) :
    invertConfiguration ⁻¹' connectionToSetEvent S x B =
      connectionToSetEvent (Neg.neg '' S) (-x) (Neg.neg '' B) := by
  ext ω
  constructor
  · rintro ⟨hx, y, hy, hyS, hp⟩
    exact ⟨⟨x, hx, rfl⟩, -y, ⟨y, hy, rfl⟩, ⟨y, hyS, rfl⟩,
      (restrictedInversionGraphIso ω S).reachable_iff.mpr hp⟩
  · rintro ⟨hx, z, ⟨y, hy, rfl⟩, hyS, hp⟩
    exact ⟨by simpa using hx, y, hy, by simpa using hyS,
      (restrictedInversionGraphIso ω S).reachable_iff.mp hp⟩

theorem connectionToSet_probability_inversion {d : ℕ} (p : unitInterval)
    (x : Vertex d) (S B : Set (Vertex d)) :
    percolation d p (connectionToSetEvent (Neg.neg '' S) (-x) (Neg.neg '' B)) =
      percolation d p (connectionToSetEvent S x B) := by
  rw [← connectionToSetEvent_inversion, ← Measure.map_apply
    measurable_invertConfiguration (measurableSet_connectionToSetEvent S x B),
    percolation_map_inversion]

end NearCritical
