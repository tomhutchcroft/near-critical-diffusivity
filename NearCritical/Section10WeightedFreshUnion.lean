module

public import NearCritical.Section10UnconditionalStep
public import NearCritical.Section10CoupledPairMass

/-! Weighted union bounds between observations on the past and events in
the next fresh tube. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- A real observable determined by finitely many layered bonds factors
through the finite restriction used by the product-law API. -/
theorem ReadsOnly.isLocal {d : ℕ} {R : Finset (LBond d)}
    {f : Configuration d × Configuration d → ℝ} (hf : ReadsOnly R f) : IsLocal R f := by
  let e : (∅ : Finset (LBond d)) → Bool := fun b => (Finset.notMem_empty b.1 b.2).elim
  refine ⟨fun b => f (gluePair e b), fun z => ?_⟩
  apply hf
  intro b hb
  rw [layerVal_gluePair, dif_neg (by simp), dif_pos hb]
  rfl

/-- The entry estimate can sum the individual intersection probabilities.
The occupation indicator for each pair is evaluated on the earlier history,
and the tube event for that pair reads a disjoint fresh block. -/
theorem weighted_fresh_union_le {d : ℕ} {ι : Type*}
    (p q : unitInterval) (R T : Finset (LBond d)) (hd : Disjoint R T)
    (I : Finset ι) (G : Configuration d × Configuration d → ℝ)
    (hG : IsLocal R G) (hG₀ : ∀ z, 0 ≤ G z)
    (A F : ι → Configuration d × Configuration d → Prop)
    (hA : ∀ i ∈ I, ReadsOnly R (A i)) (hF : ∀ i ∈ I, ReadsOnly T (F i)) :
    let μ := (percolation d p).prod (percolation d q)
    (∫ z, {z | ∃ i ∈ I, A i z ∧ F i z}.indicator G z ∂μ) ≤
      ∑ i ∈ I, (∫ z, {z | A i z}.indicator G z ∂μ) * μ.real {z | F i z} := by
  intro μ
  let H (i : ι) := {z | A i z}.indicator G
  let J (i : ι) := ({z | F i z} : Set (Configuration d × Configuration d)).indicator (fun _ => (1:ℝ))
  have hH (i : ι) (hi : i ∈ I) : IsLocal R (H i) := by
    obtain ⟨g, hg⟩ := hG
    apply ReadsOnly.isLocal
    intro z z' he
    have hr : R.restrict (layerVal z) = R.restrict (layerVal z') := funext fun b => he b b.property
    simp only [H, Set.indicator_apply, Set.mem_setOf_eq, hA i hi z z' he, hg z, hg z', hr]
  have hJ (i : ι) (hi : i ∈ I) : IsLocal T (J i) := by
    apply ReadsOnly.isLocal
    intro z z' he
    simp only [J, Set.indicator_apply, Set.mem_setOf_eq, hF i hi z z' he]
  have hterm (i : ι) (z : Configuration d × Configuration d) : 0 ≤ H i z * J i z := by
    by_cases ha : A i z <;> by_cases hf : F i z <;> simp [H, J, ha, hf, hG₀ z]
  calc
    _ ≤ ∫ z, ∑ i ∈ I, H i z * J i z ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall ?_)
        (integrable_finsetSum _ (fun i hi => ((hH i hi).mul_union (hJ i hi)).integrable p q))
        (Filter.Eventually.of_forall ?_)
      · intro z
        by_cases h : ∃ i ∈ I, A i z ∧ F i z <;> simp [h, hG₀ z]
      intro z
      by_cases hz : ∃ i ∈ I, A i z ∧ F i z
      · obtain ⟨i, hi, ha, hf⟩ := hz
        have hle := Finset.single_le_sum (f := fun j => H j z * J j z) (fun j _ => hterm j z) hi
        simpa [H, J, ha, hf, show (∃ i ∈ I, A i z ∧ F i z) from ⟨i, hi, ha, hf⟩] using hle
      · simpa [hz] using (show 0 ≤ ∑ i ∈ I, H i z * J i z from
          Finset.sum_nonneg (fun i _ => hterm i z))
    _ = ∑ i ∈ I, (∫ z, H i z ∂μ) * μ.real {z | F i z} := by
      rw [integral_finsetSum _ (fun i hi => ((hH i hi).mul_union (hJ i hi)).integrable p q)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [IsLocal.integral_mul p q hd (hH i hi) (hJ i hi)]
      rw [integral_indicator_const _ (hF i hi).measurableSet, smul_eq_mul, mul_one]

end NearCritical.Section10
