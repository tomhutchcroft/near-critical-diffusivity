module

public import NearCritical.Section10EITSourceForm

/-! The source route measure `mu` (def.nw.route) as a probability on a finite type.

A route is a start point of `routeStartBox D M` together with a lazy history; `mu`
is the uniform start times the lazy step weights, conditioned on survival
(staying in the box). `routeLaw_tail` identifies the common-level tail of
`mu x mu` with `conditionedRouteOverlapTail`, so `sourceRoute_conditioned_EIT`
gives the exponential intersection tail in the form consumed by the Section 10
weight theorems: `mu >= 0`, `sum mu = 1`, `N <= M`, and
`sum_{N >= j+1} mu mu' <= (C / M^(D-1)) q0^j`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

/-- Routes: a start point of the start box and a lazy history. -/
abbrev SourceRoute (D M : ℕ) : Type := ↥(routeStartBox D M) × LazyRouteHistory D M

/-- The transverse positions of a route. -/
def SourceRoute.position {D M : ℕ} (γ : SourceRoute D M) : ℕ → Fin D → ℤ :=
  routeHistoryPosition γ.1.1 γ.2

/-- The survival-conditioned route law. -/
def routeLaw (D M : ℕ) (γ : SourceRoute D M) : ℝ :=
  if lazyRouteSurvives γ.1.1 γ.2 then
    lazyRouteWeight γ.2 / (((routeStartBox D M).card : ℝ) * sourceRouteSurvivalMass D M)
  else 0

/-- Number of common levels of two routes. -/
def routeCommonLevels (D M : ℕ) (y : SourceRoute D M × SourceRoute D M) : ℕ :=
  (commonRouteLevels M y.1.position y.2.position).card

lemma lazyRouteWeight_nonneg' {D M : ℕ} (a : LazyRouteHistory D M) : 0 ≤ lazyRouteWeight a := by
  unfold lazyRouteWeight
  apply Finset.prod_nonneg
  intro j _
  cases a j <;> simp [lazyCoordinateWeight] <;> positivity

theorem routeLaw_nonneg {D M : ℕ} (hmass : 0 ≤ sourceRouteSurvivalMass D M)
    (γ : SourceRoute D M) : 0 ≤ routeLaw D M γ := by
  unfold routeLaw
  split_ifs
  · exact div_nonneg (lazyRouteWeight_nonneg' _) (mul_nonneg (Nat.cast_nonneg _) hmass)
  · exact le_refl _

theorem routeLaw_sum {D M : ℕ} (hmass : 0 < sourceRouteSurvivalMass D M) :
    (∑ γ : SourceRoute D M, routeLaw D M γ) = 1 := by
  have hcard : (0:ℝ) < ((routeStartBox D M).card : ℝ) := by
    by_contra h
    have h0 : ((routeStartBox D M).card : ℝ) = 0 :=
      le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    unfold sourceRouteSurvivalMass at hmass
    rw [h0, div_zero] at hmass
    exact lt_irrefl _ hmass
  have hZ : ((routeStartBox D M).card : ℝ) * sourceRouteSurvivalMass D M ≠ 0 :=
    (mul_pos hcard hmass).ne'
  have hnum : (∑ x ∈ routeStartBox D M, ∑ h : LazyRouteHistory D M,
      if lazyRouteSurvives x h then lazyRouteWeight h else 0) =
      ((routeStartBox D M).card : ℝ) * sourceRouteSurvivalMass D M := by
    unfold sourceRouteSurvivalMass
    rw [mul_div_cancel₀ _ hcard.ne']
  have hpt : ∀ γ : SourceRoute D M, routeLaw D M γ =
      (if lazyRouteSurvives γ.1.1 γ.2 then lazyRouteWeight γ.2 else 0) /
        (((routeStartBox D M).card : ℝ) * sourceRouteSurvivalMass D M) := by
    intro γ
    unfold routeLaw
    split_ifs
    · rfl
    · rw [zero_div]
  rw [Finset.sum_congr rfl (fun γ _ => hpt γ), ← Finset.sum_div, Fintype.sum_prod_type]
  have hconv : (∑ x : ↥(routeStartBox D M), ∑ h : LazyRouteHistory D M,
      if lazyRouteSurvives x.1 h then lazyRouteWeight h else 0) =
      ∑ x ∈ routeStartBox D M, ∑ h : LazyRouteHistory D M,
        if lazyRouteSurvives x h then lazyRouteWeight h else 0 :=
    Finset.sum_coe_sort (routeStartBox D M) (fun x => ∑ h : LazyRouteHistory D M,
      if lazyRouteSurvives x h then lazyRouteWeight h else 0)
  rw [hconv, hnum, div_self hZ]

theorem routeCommonLevels_le (D M : ℕ) (y : SourceRoute D M × SourceRoute D M) :
    routeCommonLevels D M y ≤ M := by
  unfold routeCommonLevels
  have hsub : commonRouteLevels M y.1.position y.2.position ⊆ Finset.range M := by
    intro j hj
    unfold commonRouteLevels at hj
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hj
    have h1 : z ∈ routeSites M y.1.position := by
      simp only [Finset.mem_inter] at hz
      exact hz.1
    have h2 := (mem_routeSites M y.1.position z.1 z.2).mp h1
    exact Finset.mem_range.mpr h2.1
  exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])

/-- The common-level tail of `mu x mu` is the conditioned overlap tail. -/
theorem routeLaw_tail_eq (D M k : ℕ) :
    (∑ y : SourceRoute D M × SourceRoute D M,
      if k ≤ routeCommonLevels D M y then routeLaw D M y.1 * routeLaw D M y.2 else 0) =
      conditionedRouteOverlapTail D M k := by
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ((routeStartBox D M).card : ℝ) * sourceRouteSurvivalMass D M :=
    ⟨_, rfl⟩
  have hpt : ∀ (x y : ↥(routeStartBox D M)) (a b : LazyRouteHistory D M),
      (if k ≤ routeCommonLevels D M ((x, a), (y, b)) then
        routeLaw D M (x, a) * routeLaw D M (y, b) else 0) =
      (if lazyRouteSurvives x.1 a ∧ lazyRouteSurvives y.1 b ∧
          k ≤ (commonRouteLevels M (routeHistoryPosition x.1 a)
            (routeHistoryPosition y.1 b)).card
        then lazyRouteWeight a * lazyRouteWeight b else 0) / Z ^ 2 := by
    intro x y a b
    have hN : routeCommonLevels D M ((x, a), (y, b)) =
        (commonRouteLevels M (routeHistoryPosition x.1 a) (routeHistoryPosition y.1 b)).card :=
      rfl
    rw [hN]
    unfold routeLaw
    rw [← hZ]
    by_cases h1 : lazyRouteSurvives x.1 a <;> by_cases h2 : lazyRouteSurvives y.1 b <;>
      by_cases h3 : k ≤ (commonRouteLevels M (routeHistoryPosition x.1 a)
        (routeHistoryPosition y.1 b)).card <;>
      simp only [h1, h2, h3, ite_true, ite_false, and_self, and_true, and_false, false_and,
        true_and, zero_div, mul_zero, zero_mul]
    rw [div_mul_div_comm, sq]
  have hrhs : conditionedRouteOverlapTail D M k =
      (∑ x ∈ routeStartBox D M, ∑ y ∈ routeStartBox D M,
        ∑ a : LazyRouteHistory D M, ∑ b : LazyRouteHistory D M,
          if lazyRouteSurvives x a ∧ lazyRouteSurvives y b ∧
              k ≤ (commonRouteLevels M (routeHistoryPosition x a)
                (routeHistoryPosition y b)).card
          then lazyRouteWeight a * lazyRouteWeight b else 0) / Z ^ 2 := by
    rw [hZ, mul_pow]
    rfl
  rw [hrhs, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp only [hpt, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_coe_sort (routeStartBox D M)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.sum_coe_sort (routeStartBox D M)]
  exact Finset.sum_comm

/-- **Route law with exponential intersection tails** (def.nw.route, lem.nw.EIT)
in the form consumed by the Section 10 weight theorems. -/
theorem routeLaw_tail {D : ℕ} (hD : 3 ≤ D) :
    ∃ (q0 C : ℝ) (M₀ : ℕ), 0 < q0 ∧ q0 < 1 ∧ 0 ≤ C ∧ ∀ M ≥ M₀,
      (∀ γ : SourceRoute D M, 0 ≤ routeLaw D M γ) ∧
      (∑ γ : SourceRoute D M, routeLaw D M γ) = 1 ∧
      ∀ j : ℕ, (∑ y : SourceRoute D M × SourceRoute D M,
        if j + 1 ≤ routeCommonLevels D M y then routeLaw D M y.1 * routeLaw D M y.2 else 0) ≤
          (C / (M:ℝ) ^ (D-1)) * q0 ^ j := by
  obtain ⟨q0, C, M₀, hq0, hq1, hC, hE⟩ := sourceRoute_conditioned_EIT hD
  obtain ⟨M₁, hM₁⟩ := sourceRouteSurvivalMass_eventually_half (by omega : 2 ≤ D)
  refine ⟨q0, C, max M₀ M₁, hq0, hq1, hC, ?_⟩
  intro M hM
  have hmass : (1/2:ℝ) ≤ sourceRouteSurvivalMass D M := hM₁ M ((le_max_right _ _).trans hM)
  have hmass0 : 0 < sourceRouteSurvivalMass D M := lt_of_lt_of_le (by norm_num) hmass
  refine ⟨routeLaw_nonneg hmass0.le, routeLaw_sum hmass0, ?_⟩
  intro j
  rw [routeLaw_tail_eq]
  have h := hE M ((le_max_left _ _).trans hM) (j+1) (Nat.succ_pos j)
  rw [Nat.add_sub_cancel] at h
  calc conditionedRouteOverlapTail D M (j+1) ≤ C * q0 ^ j / (M:ℝ) ^ (D-1) := h
    _ = (C / (M:ℝ) ^ (D-1)) * q0 ^ j := by ring

end NearCritical.Section10
