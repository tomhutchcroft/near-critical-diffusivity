module

public import NearCritical.Section10RouteSurvival
public import NearCritical.Section10RouteDifferenceOverlap
public import NearCritical.Section10DifferenceDiffuseTail

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

private def pairRouteHistories (D M : ℕ) :
    (LazyRouteHistory D M × LazyRouteHistory D M) ≃ DifferenceHistory D M where
  toFun ab i := (ab.1 i, ab.2 i)
  invFun h := (fun i => (h i).1, fun i => (h i).2)
  left_inv := by intro ab; cases ab; rfl
  right_inv := by intro h; funext i; exact Prod.eta _

private theorem pairRouteHistories_weight {D M : ℕ}
    (a b : LazyRouteHistory D M) :
    differenceHistoryWeight (pairRouteHistories D M (a,b)) =
      lazyRouteWeight a * lazyRouteWeight b := by
  simp only [differenceHistoryWeight, pairRouteHistories, Equiv.coe_fn_mk,
    differenceStepWeight, lazyRouteWeight, Finset.prod_mul_distrib]

private theorem routeHistory_weight_nonneg {D M : ℕ} (a : LazyRouteHistory D M) :
    0 ≤ lazyRouteWeight a := by
  unfold lazyRouteWeight
  apply Finset.prod_nonneg
  intro j _
  cases a j <;> simp [lazyCoordinateWeight] <;> positivity

/-- Common-level tail under two independent copies of the source route law.
The numerator is the joint mass before conditioning. -/
def conditionedRouteOverlapTail (D M k : ℕ) : ℝ := by
  classical
  let S := routeStartBox D M
  exact (∑ x ∈ S, ∑ y ∈ S,
    ∑ a : LazyRouteHistory D M, ∑ b : LazyRouteHistory D M,
      if lazyRouteSurvives x a ∧ lazyRouteSurvives y b ∧
          k ≤ (commonRouteLevels M (routeHistoryPosition x a)
            (routeHistoryPosition y b)).card
      then lazyRouteWeight a * lazyRouteWeight b else 0) /
    ((S.card : ℝ)^2 * (sourceRouteSurvivalMass D M)^2)

/-- A common-level tail event is contained in the difference-walk visit
tail on the same pair of histories. -/
theorem routeOverlap_le_trapVisits {D M : ℕ} (x y : Fin D → ℤ)
    (a b : LazyRouteHistory D M) :
    (commonRouteLevels M (routeHistoryPosition x a) (routeHistoryPosition y b)).card ≤
      differenceVisitCount (routeDifferenceTrap D) (x-y) (fun i => (a i,b i)) :=
  commonRouteLevels_card_le_differenceVisits x y a b

private theorem survivingOverlapMass_le_visitTail {D M k : ℕ} (x y : Fin D → ℤ) :
    (∑ a : LazyRouteHistory D M, ∑ b : LazyRouteHistory D M,
      if lazyRouteSurvives x a ∧ lazyRouteSurvives y b ∧
          k ≤ (commonRouteLevels M (routeHistoryPosition x a)
            (routeHistoryPosition y b)).card
      then lazyRouteWeight a * lazyRouteWeight b else 0) ≤
    differenceEventMass D M
      (fun h => k ≤ differenceVisitCount (routeDifferenceTrap D) (x-y) h) := by
  classical
  unfold differenceEventMass
  let e := pairRouteHistories D M
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  dsimp only [e]
  rw [pairRouteHistories_weight]
  split_ifs with hsurv hvisit hvisit
  · exact le_rfl
  · exact (hvisit (hsurv.2.2.trans (routeOverlap_le_trapVisits x y a b))).elim
  · exact mul_nonneg (routeHistory_weight_nonneg a) (routeHistory_weight_nonneg b)
  · exact le_rfl

/-- Conditioning the two independently sampled routes costs at most four
once each route survives with probability at least one half. -/
theorem conditionedRouteOverlapTail_le {D M k : ℕ}
    (hs : 1/2 ≤ sourceRouteSurvivalMass D M) :
    conditionedRouteOverlapTail D M k ≤
      4 * diffuseDifferenceVisitTail D M (routeStartBox D M) (routeDifferenceTrap D) k := by
  classical
  unfold conditionedRouteOverlapTail
  rw [pow_two (sourceRouteSurvivalMass D M), ← div_div]
  apply route_pair_conditioning_factor_four _ _ hs hs
  · unfold diffuseDifferenceVisitTail differenceEventMass
    apply div_nonneg _ (sq_nonneg _)
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    apply Finset.sum_nonneg
    intro h _
    split_ifs
    · unfold differenceHistoryWeight differenceStepWeight
      apply Finset.prod_nonneg
      intro j _
      obtain ⟨a,b⟩ := h j
      cases a <;> cases b <;> simp [lazyCoordinateWeight] <;> positivity
    · exact le_rfl
  · unfold diffuseDifferenceVisitTail
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro x _
    exact Finset.sum_le_sum fun y _ => survivingOverlapMass_le_visitTail x y

/-- Geometric common-level tail for the actual conditioned source routes.
With transverse dimension `D = d - 1`, the entrance factor scales as
`M^(2-d)`. The grid `l*K+1` records the block size of the return argument. -/
theorem sourceRoute_conditioned_overlap_tail {D : ℕ} (hD : 3 ≤ D) :
    ∃ K M₀ : ℕ, 0 < K ∧ ∀ M ≥ M₀, ∀ l : ℕ,
      conditionedRouteOverlapTail D M (l*K+1) ≤
        4 * ((1/2 : ℝ)^l * ((M : ℝ) * ((routeDifferenceTrap D).card : ℝ) /
          ((M : ℝ)/(8*((D : ℝ)+1)))^D)) := by
  obtain ⟨K, hK, ht⟩ := sourceRoute_difference_visit_tail_le hD (routeDifferenceTrap D)
  obtain ⟨N, hN⟩ := sourceRouteSurvivalMass_eventually_half (by omega : 2 ≤ D)
  refine ⟨K, max N (8*(D+1)), hK, ?_⟩
  intro M hM l
  have hs := hN M ((le_max_left _ _).trans hM)
  have hbox : 8*(D+1) ≤ M := (le_max_right _ _).trans hM
  exact (conditionedRouteOverlapTail_le hs).trans
    (mul_le_mul_of_nonneg_left (ht hbox l) (by norm_num))

/-- The conditioned common-level tail decreases with the threshold. -/
theorem conditionedRouteOverlapTail_antitone (D M : ℕ) :
    Antitone (conditionedRouteOverlapTail D M) := by
  classical
  intro k l hkl
  unfold conditionedRouteOverlapTail
  apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  split_ifs with hl hk hk
  · exact le_rfl
  · exact (hk ⟨hl.1, hl.2.1, hkl.trans hl.2.2⟩).elim
  · exact mul_nonneg (routeHistory_weight_nonneg a) (routeHistory_weight_nonneg b)
  · exact le_rfl

/-- The route-pair bound applies at every positive threshold. -/
theorem sourceRoute_conditioned_overlap_tail_all {D : ℕ} (hD : 3 ≤ D) :
    ∃ K M₀ : ℕ, 0 < K ∧ ∀ M ≥ M₀, ∀ k : ℕ, 0 < k →
      conditionedRouteOverlapTail D M k ≤
        4 * ((1/2 : ℝ)^((k-1)/K) * ((M : ℝ) * ((routeDifferenceTrap D).card : ℝ) /
          ((M : ℝ)/(8*((D : ℝ)+1)))^D)) := by
  obtain ⟨K, M₀, hK, ht⟩ := sourceRoute_conditioned_overlap_tail hD
  refine ⟨K, M₀, hK, ?_⟩
  intro M hM k hk
  have hgrid : (k-1)/K*K+1 ≤ k := by
    have h := Nat.div_mul_le_self (k-1) K
    omega
  exact (conditionedRouteOverlapTail_antitone D M hgrid).trans (ht M hM ((k-1)/K))

end NearCritical.Section10
