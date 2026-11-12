module

public import NearCritical.ORProjection

/-! Exact OR pushforward with a different success parameter in each block. -/
@[expose] public section
noncomputable section
namespace NearCritical.BK
open Set MeasureTheory ProbabilityTheory

/-- The refined profile is constant within each block, not across blocks. -/
theorem orProject_map_bernoulliProfile {E : Type*} [Fintype E] (m : ℕ)
    (p q : E → unitInterval)
    (hp : ∀ e, (p e : ℝ) = 1 - (1 - (q e : ℝ)) ^ m) :
    (Measure.pi (fun ej : E × Fin m ↦ bernoulliMeasure true false (q ej.1))).map
        (orProject m) = Measure.pi (fun e ↦ bernoulliMeasure true false (p e)) := by
  classical
  let curryMap : (E × Fin m → Bool) → (E → Fin m → Bool) :=
    MeasurableEquiv.curry E (Fin m) Bool
  let blockMap : (E → Fin m → Bool) → (E → Bool) := fun ω e ↦ orBlock m (ω e)
  have hcurry :
      (Measure.pi (fun ej : E × Fin m ↦ bernoulliMeasure true false (q ej.1))).map
          curryMap =
        Measure.pi (fun e ↦ Measure.pi (fun _ : Fin m ↦ bernoulliMeasure true false (q e))) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (e : E) (_ : Fin m) ↦
        bernoulliMeasure true false (q e)))
  have hblocks :
      (Measure.pi (fun e ↦ Measure.pi (fun _ : Fin m ↦ bernoulliMeasure true false (q e)))).map
          blockMap = Measure.pi (fun e ↦ bernoulliMeasure true false (p e)) := by
    rw [Measure.pi_map_pi (fun _ ↦ (measurable_of_finite (orBlock m)).aemeasurable)]
    congr 1
    funext e
    exact orBlock_map_bernoulli m (p e) (q e) (hp e)
  calc
    _ = ((Measure.pi (fun ej : E × Fin m ↦ bernoulliMeasure true false (q ej.1))).map
        curryMap).map blockMap := by
      rw [Measure.map_map (measurable_of_finite blockMap) (measurable_of_finite curryMap)]
      rfl
    _ = _ := by rw [hcurry, hblocks]

/-- Both event factors transport under their actual independent profile law. -/
theorem measureReal_orProject_profile {E : Type*} [Fintype E] (m : ℕ)
    (p q : E → unitInterval)
    (hp : ∀ e, (p e : ℝ) = 1 - (1 - (q e : ℝ)) ^ m)
    (A : Set (E → Bool)) :
    (Measure.pi (fun ej : E × Fin m ↦ bernoulliMeasure true false (q ej.1))).real
        ((orProject m) ⁻¹' A) =
      (Measure.pi (fun e ↦ bernoulliMeasure true false (p e))).real A := by
  rw [← orProject_map_bernoulliProfile m p q hp,
    map_measureReal_apply (measurable_of_finite _) (Set.toFinite A).measurableSet]

end NearCritical.BK
