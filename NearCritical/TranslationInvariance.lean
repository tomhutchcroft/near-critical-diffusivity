module
public import NearCritical.Events
@[expose] public section
namespace NearCritical
open MeasureTheory ProbabilityTheory

/-- Translation preserves the unique positive-coordinate direction of each bond. -/
def translateBond {d : ℕ} (a : Vertex d) : Bond d ≃ Bond d where
  toFun e := (a + e.1, e.2)
  invFun e := (-a + e.1, e.2)
  left_inv e := by ext <;> simp
  right_inv e := by ext <;> simp

/-- Configuration pullback under lattice translation. -/
def translateConfiguration {d : ℕ} (a : Vertex d) (ω : Configuration d) : Configuration d :=
  fun e => ω (translateBond a e)

lemma bondTip_translate {d : ℕ} (a : Vertex d) (e : Bond d) :
    bondTip (translateBond a e) = a + bondTip e := by
  ext i
  by_cases h : i = e.2
  · subst i; simp [bondTip, translateBond, add_assoc]
  · simp [bondTip, translateBond, Function.update_of_ne h]

lemma measurable_translateConfiguration {d : ℕ} (a : Vertex d) :
    Measurable (translateConfiguration a) := by
  exact measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

theorem percolation_map_translation {d : ℕ} (p : unitInterval) (a : Vertex d) :
    (percolation d p).map (translateConfiguration a) = percolation d p := by
  change (Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p)).map
    (fun ω e => ω (translateBond a e)) = _
  simpa [percolation, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft'] using
    (Measure.infinitePi_map_piCongrLeft
      (fun _ : Bond d => bernoulliMeasure true false p) (translateBond a).symm)

lemma openGraph_translate_adj {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (x y : Vertex d) :
    (openGraph (translateConfiguration a ω)).Adj x y ↔
      (openGraph ω).Adj (a + x) (a + y) := by
  constructor
  · rintro ⟨e, he, h | h⟩
    · exact ⟨translateBond a e, he, Or.inl ⟨by simp [h.1, translateBond],
        by rw [h.2, bondTip_translate]⟩⟩
    · exact ⟨translateBond a e, he, Or.inr ⟨by simp [h.1, translateBond],
        by rw [h.2, bondTip_translate]⟩⟩
  · rintro ⟨e, he, h⟩
    refine ⟨(translateBond a).symm e, ?_, ?_⟩
    · simpa [translateConfiguration] using he
    · have ht := bondTip_translate a ((translateBond a).symm e)
      simp only [Equiv.apply_symm_apply] at ht
      rcases h with h | h
      · left
        constructor
        · simpa [translateBond] using congrArg (fun z => -a + z) h.1
        · apply add_left_cancel (a := a)
          simpa [ht] using h.2
      · right
        constructor
        · simpa [translateBond] using congrArg (fun z => -a + z) h.1
        · apply add_left_cancel (a := a)
          simpa [ht] using h.2

/-- Translation transports open paths without changing the bond variables. -/
def translationGraphIso {d : ℕ} (a : Vertex d) (ω : Configuration d) :
    openGraph (translateConfiguration a ω) ≃g openGraph ω where
  toEquiv := Equiv.addLeft a
  map_rel_iff' := (openGraph_translate_adj a ω _ _).symm

lemma connectionEvent_translation {d : ℕ} (a x y : Vertex d) :
    translateConfiguration a ⁻¹' connectionEvent x y = connectionEvent (a + x) (a + y) := by
  ext ω
  exact (translationGraphIso a ω).reachable_iff.symm

theorem twoPoint_translation {d : ℕ} (p : unitInterval) (a x y : Vertex d) :
    twoPoint d p (a + x) (a + y) = twoPoint d p x y := by
  unfold twoPoint Measure.real
  congr 1
  rw [← connectionEvent_translation, ← Measure.map_apply
    (measurable_translateConfiguration a) (measurableSet_connectionEvent x y),
    percolation_map_translation]
/-- The two-point function depends only on displacement. -/
theorem twoPoint_eq_displacement {d : ℕ} (p : unitInterval) (x y : Vertex d) :
    twoPoint d p x y = twoPoint d p 0 (y - x) := by
  have h := twoPoint_translation p (-x) x y
  simpa [sub_eq_add_neg, add_comm] using h.symm

end NearCritical
