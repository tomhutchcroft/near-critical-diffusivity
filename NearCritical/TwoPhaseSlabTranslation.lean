module

public import NearCritical.TwoPhaseSlab
public import NearCritical.HalfSpaceTranslation

/-! Exact profile-law covariance and the source two-phase transverse symmetry.
Translated domains and target sets are explicit: no fixed finite cutoff is
claimed to be stationary. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory ProbabilityTheory

/-- Translation pulls back the independent rate profile as well as the bond
configuration. No stationarity of an arbitrary profile is assumed. -/
theorem percolationProfile_map_translation {d : ℕ} (r : Bond d → unitInterval)
    (a : Vertex d) :
    (percolationProfile d r).map (translateConfiguration a) =
      percolationProfile d (fun e ↦ r (translateBond a e)) := by
  change (Measure.infinitePi (fun e : Bond d ↦ bernoulliMeasure true false (r e))).map
    (fun ω e ↦ ω (translateBond a e)) =
      Measure.infinitePi (fun e : Bond d ↦ bernoulliMeasure true false (r (translateBond a e)))
  simpa [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft'] using
    (Measure.infinitePi_map_piCongrLeft
      (fun e : Bond d ↦ bernoulliMeasure true false (r (translateBond a e)))
      (translateBond a).symm)

/-- Actual restricted connections transform under the same profile pullback. -/
theorem connectionToSet_profile_probability_translation {d : ℕ}
    (r : Bond d → unitInterval) (a x : Vertex d) (S B : Set (Vertex d)) :
    percolationProfile d r (connectionToSetEvent ((fun z ↦ a+z) '' S)
      (a+x) ((fun z ↦ a+z) '' B)) =
      percolationProfile d (fun e ↦ r (translateBond a e)) (connectionToSetEvent S x B) := by
  rw [← connectionToSetEvent_translation, ← Measure.map_apply
    (measurable_translateConfiguration a) (measurableSet_connectionToSetEvent S x B),
    percolationProfile_map_translation]

/-- A transverse shift preserves BOTH endpoint heights, hence both phases. -/
lemma twoPhaseSlabProfile_translate_transverse {d : ℕ} (i : Fin d) (m n : ℤ)
    (p q : unitInterval) (a : Vertex d) (ha : a i = 0) (e : Bond d) :
    twoPhaseSlabProfile i m n p q (translateBond a e) =
      twoPhaseSlabProfile i m n p q e := by
  have hbase : (translateBond a e).1 i = e.1 i := by
    change (a+e.1) i = e.1 i
    simp only [Pi.add_apply,ha,zero_add]
  have htip : bondTip (translateBond a e) i = bondTip e i := by
    rw [bondTip_translate]
    simp only [Pi.add_apply,ha,zero_add]
  simp only [twoPhaseSlabProfile,finiteHeightSlab,Set.mem_setOf_eq,hbase,htip]

/-- Full-law transverse covariance of the literal source two-phase model.
A translated finite U remains translated, rather than falsely identified with U. -/
theorem twoPhaseSlab_connection_probability_transverse {d : ℕ} (i : Fin d) (m n : ℤ)
    (p q : unitInterval) (a : Vertex d) (ha : a i = 0) (x : Vertex d)
    (S B : Set (Vertex d)) :
    percolationProfile d (twoPhaseSlabProfile i m n p q)
        (connectionToSetEvent ((fun z ↦ a+z) '' S) (a+x) ((fun z ↦ a+z) '' B)) =
      percolationProfile d (twoPhaseSlabProfile i m n p q) (connectionToSetEvent S x B) := by
  have hprof : (fun e ↦ twoPhaseSlabProfile i m n p q (translateBond a e)) =
      twoPhaseSlabProfile i m n p q :=
    funext (fun e ↦ twoPhaseSlabProfile_translate_transverse i m n p q a ha e)
  have h := connectionToSet_profile_probability_translation
    (twoPhaseSlabProfile i m n p q) a x S B
  rw [hprof] at h
  exact h

end NearCritical
