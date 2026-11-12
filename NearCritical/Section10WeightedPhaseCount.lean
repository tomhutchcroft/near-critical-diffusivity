module

public import NearCritical.Section10PhaseHistory
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Sum the entry and persistence estimates along a finite joint history.
Use prefix weights divided by the nominal prefix growth. The future-weight
bound then transports each counted event to the normalized terminal weight,
including the exit, without requiring a contraction at the exit. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- Weighted mass of the event that the phase started at v is still active
at u. The weight is supplied separately, since the final weight can also
include the exit. -/
def phaseEventMass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (entangled clean : Ω → ℕ → Prop) (W : Ω → ℝ) (v u : ℕ) : ℝ :=
  ∫ z, {z | phaseOrigin (entangled z) (clean z) u = some v}.indicator W z ∂μ

private theorem phaseEventMass_eq_zero_of_lt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (entangled clean : Ω → ℕ → Prop) (W : Ω → ℝ) {v u : ℕ} (hu : u < v) :
    phaseEventMass μ entangled clean W v u = 0 := by
  unfold phaseEventMass
  have h : {z | phaseOrigin (entangled z) (clean z) u = some v} = (∅ : Set Ω) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact (not_le_of_gt hu) (phaseOrigin_spec (entangled z) (clean z) hz).2.1
  rw [h]
  simp

/-- Weighted Step 5. The entry bound is charged once per candidate start.
For an interior active phase the next weighted mass contracts by two
thirds. The normalized future-weight inequality, including the exit,
transports each contribution to final weight. -/
theorem weighted_entanglements_le_of_phase_masses {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (entangled clean : Ω → ℕ → Prop)
    (W : ℕ → Ω → ℝ) (Wfin : Ω → ℝ) (m : ℕ) (S : Finset ℕ)
    (hS : ∀ z u, u < m → entangled z u → u ∈ S)
    (hW : ∀ u z, 0 ≤ W u z) (hfin : ∀ z, 0 ≤ Wfin z)
    (hint : ∀ v ∈ S, ∀ u < m,
      Integrable ({z | phaseOrigin (entangled z) (clean z) u = some v}.indicator Wfin) μ)
    {e : ℝ} (he : 0 ≤ e)
    (hentry : ∀ v ∈ S, v < m → phaseEventMass μ entangled clean (W v) v v ≤ e)
    (hpersist : ∀ v ∈ S, ∀ u, v ≤ u → u+1 < m →
      phaseEventMass μ entangled clean (W (u+1)) v (u+1) ≤
        (2/3:ℝ) * phaseEventMass μ entangled clean (W u) v u)
    (hfuture : ∀ v ∈ S, ∀ u < m,
      phaseEventMass μ entangled clean Wfin v u ≤ phaseEventMass μ entangled clean (W u) v u) :
    (∫ z, (((Finset.range m).filter (entangled z)).card : ℝ) * Wfin z ∂μ) ≤
      3 * e * (S.card : ℝ) := by
  let H (v u : ℕ) (z : Ω) := {z | phaseOrigin (entangled z) (clean z) u = some v}.indicator Wfin z
  have hpoint (z : Ω) : (((Finset.range m).filter (entangled z)).card : ℝ) * Wfin z ≤
      ∑ v ∈ S, ∑ u ∈ Finset.range m, H v u z := by
    have hc (v : ℕ) : (∑ u ∈ Finset.range m, H v u z) =
        (((Finset.range m).filter (fun u => phaseOrigin (entangled z) (clean z) u = some v)).card : ℝ) *
          Wfin z := by
      simp only [H, Set.indicator_apply, Set.mem_setOf_eq]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    simp_rw [hc, ← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (hfin z)
    exact_mod_cast entangled_steps_card_le_phase_members (entangled z) (clean z) m S
      (fun u hu he => hS z u hu he)
  have hs (v : ℕ) (hv : v ∈ S) :
      ∑ u ∈ Finset.range m, phaseEventMass μ entangled clean (W u) v u ≤ 3 * e := by
    by_cases hm : v < m
    · have hz : (∑ u ∈ Finset.range v, phaseEventMass μ entangled clean (W u) v u) = 0 :=
        Finset.sum_eq_zero fun u hu => phaseEventMass_eq_zero_of_lt μ entangled clean (W u)
          (Finset.mem_range.mp hu)
      rw [← Finset.sum_range_add_sum_Ico _ hm.le, hz, zero_add, Finset.sum_Ico_eq_sum_range]
      let a (r : ℕ) :=
        if v+r < m then phaseEventMass μ entangled clean (W (v+r)) v (v+r) else 0
      have ha (r : ℕ) : 0 ≤ a r := by
        by_cases hr : v+r < m
        · rw [show a r = phaseEventMass μ entangled clean (W (v+r)) v (v+r) from if_pos hr]
          apply integral_nonneg
          intro z
          by_cases h : phaseOrigin (entangled z) (clean z) (v+r) = some v <;>
            simp [Set.indicator_apply, h, hW]
        · simp [a, hr]
      have hstart : a 0 ≤ e := by simpa [a, hm] using hentry v hv hm
      have hstep (r : ℕ) : a (r+1) ≤ (2/3:ℝ)*a r := by
        by_cases hr : v+(r+1) < m
        · have hr' : v+r < m := by omega
          simpa only [a, if_pos hr, if_pos hr', Nat.add_assoc] using
            hpersist v hv (v+r) (by omega) (by omega)
        · rw [show a (r+1) = 0 from if_neg hr]
          exact mul_nonneg (by norm_num) (ha r)
      have hge : (∑ r ∈ Finset.range (m-v), (2/3:ℝ)^r) ≤ 3 := by
        have h := geom_sum_mul_neg (2/3:ℝ) (m-v)
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2/3) (m-v)]
      calc
        _ ≤ ∑ r ∈ Finset.range (m-v), e * (2/3:ℝ)^r := by
          apply Finset.sum_le_sum
          intro r hr
          have hr' : v+r < m := by have := Finset.mem_range.mp hr; omega
          simpa [a, hr', Nat.add_comm] using phase_mass_geometric a hstart hstep r
        _ = e * ∑ r ∈ Finset.range (m-v), (2/3:ℝ)^r := by rw [Finset.mul_sum]
        _ ≤ 3 * e := by simpa only [mul_comm e 3] using mul_le_mul_of_nonneg_left hge he
    · have hz : (∑ u ∈ Finset.range m, phaseEventMass μ entangled clean (W u) v u) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        apply phaseEventMass_eq_zero_of_lt
        have := Finset.mem_range.mp hu
        omega
      rw [hz]
      positivity
  have hI (v : ℕ) (hv : v ∈ S) : Integrable (fun z => ∑ u ∈ Finset.range m, H v u z) μ :=
    integrable_finsetSum _ (fun u hu => hint v hv u (Finset.mem_range.mp hu))
  calc
    _ ≤ ∫ z, ∑ v ∈ S, ∑ u ∈ Finset.range m, H v u z ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => mul_nonneg (Nat.cast_nonneg _) (hfin z))
        (integrable_finsetSum _ hI) (Filter.Eventually.of_forall hpoint)
    _ = ∑ v ∈ S, ∑ u ∈ Finset.range m, phaseEventMass μ entangled clean Wfin v u := by
      rw [integral_finsetSum _ hI]
      apply Finset.sum_congr rfl
      intro v hv
      exact integral_finsetSum _ (fun u hu => hint v hv u (Finset.mem_range.mp hu))
    _ ≤ ∑ v ∈ S, 3 * e := by
      apply Finset.sum_le_sum
      intro v hv
      refine (Finset.sum_le_sum fun u hu => hfuture v hv u (Finset.mem_range.mp hu)).trans (hs v hv)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_comm (S.card : ℝ)]

end NearCritical.Section10
