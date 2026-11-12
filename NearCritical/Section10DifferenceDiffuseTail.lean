module

public import NearCritical.Section10DifferenceEntrance
public import NearCritical.Section10DifferenceVisitTail

/-! The finite-history visit tail averaged over the literal independent
uniform transverse starts from Section 10. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

def diffuseDifferenceVisitTail (D T : ℕ) (S B : Finset (Fin D → ℤ)) (k : ℕ) : ℝ :=
  (∑ x ∈ S, ∑ y ∈ S, differenceEventMass D T
    (fun h => k ≤ differenceVisitCount B (x-y) h)) / (S.card : ℝ)^2

theorem diffuseDifferenceVisitTail_one (D T : ℕ) (S B : Finset (Fin D → ℤ)) :
    diffuseDifferenceVisitTail D T S B 1 = diffuseDifferenceEntranceMass D T S B := by
  classical
  unfold diffuseDifferenceVisitTail diffuseDifferenceEntranceMass
  congr 1
  unfold differenceEventMass
  calc
    _ = ∑ h : DifferenceHistory D T, ∑ y ∈ S, ∑ x ∈ S,
        if 1 ≤ differenceVisitCount B (x-y) h then differenceHistoryWeight h else 0 := by
      calc
        _ = ∑ x ∈ S, ∑ h : DifferenceHistory D T, ∑ y ∈ S,
            if 1 ≤ differenceVisitCount B (x-y) h then differenceHistoryWeight h else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h _
          apply Finset.sum_congr rfl
          intro y _
          split_ifs <;> rfl
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h _
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      have he (x : Fin D → ℤ) :
          (1 ≤ differenceVisitCount B (x-y) h) ↔
            ∃ j : Fin T, x-y+differenceDisplacement h j ∈ B := by
        rw [differenceIndexedVisit_exists B (x-y) h (by omega : 0 < 1)]
        constructor
        · rintro ⟨j,hj,hv⟩
          exact ⟨⟨j,hj⟩,hv.1⟩
        · rintro ⟨j,hj⟩
          have hex : ∃ t : ℕ, t < T ∧ x-y+differenceDisplacement h t ∈ B :=
            ⟨j,j.isLt,hj⟩
          let t := Nat.find hex
          obtain ⟨ht,hv⟩ := Nat.find_spec hex
          refine ⟨t,ht,hv,?_⟩
          have hz : differenceVisitsBefore B (x-y) h t = 0 := by
            unfold differenceVisitsBefore
            apply Finset.sum_eq_zero
            intro i hi
            apply if_neg
            intro hh
            exact (not_lt_of_ge (Nat.find_min' hex
              ⟨(Finset.mem_range.mp hi).trans ht,hh⟩)) (Finset.mem_range.mp hi)
          simp [hz]
      simp_rw [he]
      change (∑ x ∈ S, if (∃ j : Fin T, x-y+differenceDisplacement h j ∈ B) then
        differenceHistoryWeight h else 0) =
        differenceHistoryWeight h * ((S.filter
          (fun x => ∃ j : Fin T, x-y+differenceDisplacement h j ∈ B)).card : ℝ)
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
      simp

theorem sourceRoute_difference_visit_tail_le {D : ℕ} (hD : 3 ≤ D)
    (B : Finset (Fin D → ℤ)) :
    ∃ K : ℕ, 0 < K ∧ ∀ {M : ℕ}, 8*(D+1) ≤ M → ∀ l : ℕ,
      diffuseDifferenceVisitTail D M (routeStartBox D M) B (l*K+1) ≤
        (1/2 : ℝ)^l * ((M : ℝ) * (B.card : ℝ) /
          ((M : ℝ)/(8*((D : ℝ)+1)))^D) := by
  obtain ⟨K,hK,htail⟩ := differenceVisitCount_tail_with_first_hit hD B
  refine ⟨K,hK,?_⟩
  intro M hM l
  let S := routeStartBox D M
  calc
    _ ≤ (1/2 : ℝ)^l * diffuseDifferenceVisitTail D M S B 1 := by
      unfold diffuseDifferenceVisitTail
      rw [← mul_div_assoc, Finset.mul_sum]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro x _
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun y _ => htail M l (x-y))
    _ ≤ _ := by
      rw [diffuseDifferenceVisitTail_one]
      exact mul_le_mul_of_nonneg_left
        (sourceRoute_difference_entrance_le (by omega : 0 < D) hM B) (by positivity)

end NearCritical.Section10
