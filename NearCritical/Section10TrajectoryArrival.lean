module

public import NearCritical.Section10RouteArrival
public import NearCritical.Section10TrajectoryPieces
public import NearCritical.Section10FirstGoodSignSupport
public import NearCritical.Section10FirstGoodRouteInvariant

/-! The incoming state of a physical move or exit is the state from the
site's arrival. A possible intervening horizontal stay preserves it. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

open scoped Classical

theorem routeLab_source_arrival_or_stay {D M : ℕ} (X : ℕ → Fin D → ℤ)
    {t : ℕ} (ht₀ : 0 < t) (ht : t < 2*M) :
    let z := (routeLab M X t).site
    routeArrivalRank X z = t-1 ∨
      (routeArrivalRank X z = t-2 ∧ 3 ≤ t ∧ (routeLab M X (t-1)).isStep ∧
        (routeLab M X (t-1)).target = (routeLab M X (t-1)).site) := by
  intro z
  by_cases h : routeArrivalRank X z = t-1
  · exact Or.inl h
  · have hr := routeArrivalRank_lt_of_source X ht₀ ht
    change routeArrivalRank X z < t at hr
    have hr' := (routeArrivalRank_le_level X z).1
    have hz : z.1 = t/2 := (routeLab_site X ht).2
    rw [hz] at hr'
    have hlag : routeArrivalRank X z = t-2 := by omega
    have h3 : 3 ≤ t := by omega
    have hprev : (routeLab M X (t-1)).isStep :=
      routeLab_isStep X (by omega) (by omega)
    refine Or.inr ⟨hlag, h3, hprev, ?_⟩
    have htime : t-1+1 = t := by omega
    have heq := routeLab_next_site (M := M) X (t := t-1) (by omega)
    rw [htime] at heq
    by_contra hm
    have ha : routeArrives M X (t-1) z := ⟨by omega, heq.symm, Or.inr ⟨hprev, hm⟩⟩
    exact h (routeArrives_time_eq X ha).symm

theorem trajWeight_kernel_pos {d : ℕ} {X : Type*}
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk₀ : ∀ t x y z, 0 ≤ k t x y z) (z : Configuration d × Configuration d)
    (n t : ℕ) (x : X) (f : Fin n → X) (h : 0 < trajWeight k n t x f z)
    (j : ℕ) (hj : j < n) : 0 < k (t+j) (trajInput n x f j) (f ⟨j,hj⟩) z := by
  induction n generalizing t x j with
  | zero => omega
  | succ n ih =>
    have hprod : 0 < k t x (f 0) z * trajWeight k n (t+1) (f 0) (Fin.tail f) z := h
    cases j with
    | zero =>
      have hp := pos_of_mul_pos_left hprod (trajWeight_nonneg k hk₀ n (t+1) (f 0) (Fin.tail f) z)
      change 0 < k t x (f 0) z
      exact hp
    | succ j =>
      have htail := pos_of_mul_pos_right hprod (hk₀ t x (f 0) z)
      have htime : t+(j+1) = t+1+j := by omega
      rw [htime]
      exact ih (t+1) (f 0) (Fin.tail f) htail j (by omega)

/-- Read an outgoing state using a natural-number local clock. -/
def trajectoryState {X : Type*} {n : ℕ} (fallback : X) (f : Fin n → X) (j : ℕ) : X :=
  if h : j < n then f ⟨j,h⟩ else fallback

theorem trajectoryState_of_lt {X : Type*} {n : ℕ} (fallback : X) (f : Fin n → X)
    {j : ℕ} (h : j < n) : trajectoryState fallback f j = f ⟨j,h⟩ :=
  dif_pos h

namespace NestLayout

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- The outgoing representative is selected from the arrival nest, even
when the route spends an inactive horizontal row at the site. -/
theorem firstGood_trajectory_source_is_arrival (γ : SourceRoute D M)
    (z : Configuration d × Configuration d) (x₀ : Λ.X) (f : Fin (2*M) → Λ.X)
    {t : ℕ} (ht₀ : 0 < t) (ht : t < 2*M) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule
    let a := routeArrivalRank γ.position (routeLab M γ.position t).site
    0 < trajWeight (R.kernel γ G) (2*M) 0 x₀ f z →
    f ⟨t-1, by omega⟩ = f ⟨a, (routeArrivalRank_lt_of_source γ.position ht₀ ht).trans ht⟩ := by
  intro G R a hf
  rcases routeLab_source_arrival_or_stay γ.position ht₀ ht with ha | ⟨ha,h3,hstep,hstay⟩
  · have he : (⟨t-1, by omega⟩ : Fin (2*M)) =
        ⟨a, (routeArrivalRank_lt_of_source γ.position ht₀ ht).trans ht⟩ := Fin.ext ha.symm
    rw [he]
  · have hnon : ∀ j x y w, 0 ≤ R.kernel γ G j x y w := fun j x y w =>
      stepKernel_nonneg _ _ _
        (MeasureTheory.integral_nonneg (fun _ => by split_ifs <;> norm_num)) y w
    have hpos := trajWeight_kernel_pos (R.kernel γ G) hnon z (2*M) 0 x₀ f hf (t-1) (by omega)
    simp only [Nat.zero_add] at hpos
    have he : trajInput (2*M) x₀ f (t-1) = f ⟨t-2, by omega⟩ := by
      have heq := trajInput_eq_output (2*M) x₀ f (t-2) (by omega)
      have htime : t-2+1 = t-1 := by omega
      simpa only [htime] using heq
    rw [he] at hpos
    have hnot (l : RouteLabel D) : l.isStep → ¬ l.isStart := by
      cases l <;> simp [RouteLabel.isStep, RouteLabel.isStart]
    have hdiag := Λ.firstGood_kernel_preserves_state M p q ρ κ hκ hs hsiteProb γ z (t-1)
      (f ⟨t-2, by omega⟩) (f ⟨t-1, by omega⟩)
      (fun h => hnot _ hstep h.1) (fun h => h.2.1 hstay) hpos
    have hindex : (⟨t-2, by omega⟩ : Fin (2*M)) =
        ⟨a, (routeArrivalRank_lt_of_source γ.position ht₀ ht).trans ht⟩ := Fin.ext ha.symm
    exact hdiag.trans (congrArg f hindex)

/-- Each state of the positive trajectory, up to the outgoing exit row,
is a nest of typical clusters at the current physical site. -/
theorem firstGood_trajectory_at_route_site (γ : SourceRoute D M)
    (z : Configuration d × Configuration d) (x₀ : Λ.X) (f : Fin (2*M) → Λ.X)
    (hbox : ∀ j, j < 2*M → (routeLab M γ.position j).site ∈ Λ.siteBox)
    (hpre : ∀ j, j < 2*M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position j).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d-6)) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule
    0 < trajWeight (R.kernel γ G) (2*M) 0 x₀ f z →
    ∀ j (hj : j+1 < 2*M), (f ⟨j,by omega⟩).1.val.card = Λ.k ∧
      (f ⟨j,by omega⟩).1.val ⊆ Λ.fam G (routeLab M γ.position (j+1)).site := by
  intro G R hf j
  have hnon : ∀ j x y w, 0 ≤ R.kernel γ G j x y w := fun j x y w =>
    stepKernel_nonneg _ _ _
      (MeasureTheory.integral_nonneg (fun _ => by split_ifs <;> norm_num)) y w
  induction j with
  | zero =>
    intro hj
    have hp := trajWeight_kernel_pos (R.kernel γ G) hnon z (2*M) 0 x₀ f hf 0 (by omega)
    simp only [Nat.zero_add] at hp
    exact Λ.firstGood_route_next_valid γ z p q ρ κ hκ hs hsiteProb hbox hpre hcount 0 hj
      _ _ (fun h => (by omega : False).elim) hp
  | succ j ih =>
    intro hj
    have hp := trajWeight_kernel_pos (R.kernel γ G) hnon z (2*M) 0 x₀ f hf (j+1) (by omega)
    simp only [Nat.zero_add, trajInput_eq_output (2*M) x₀ f j (by omega)] at hp
    exact Λ.firstGood_route_next_valid γ z p q ρ κ hκ hs hsiteProb hbox hpre hcount (j+1) hj
      _ _ (fun _ => ih (by omega)) hp

/-- Both nest invariants in the natural-number indexing used by the
overlap proof. The transition at local rank j+1 uses the nest at index j. -/
theorem firstGood_trajectory_state_data (γ : SourceRoute D M)
    (z : Configuration d × Configuration d) (x₀ : Λ.X)
    {n : ℕ} (hn : n = 2*M) (f : Fin n → Λ.X)
    (hbox : ∀ j, j < 2*M → (routeLab M γ.position j).site ∈ Λ.siteBox)
    (hpre : ∀ j, j < 2*M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position j).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d-6)) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule
    let state := trajectoryState x₀ f
    0 < trajWeight (R.kernel γ G) n 0 x₀ f z →
    ∀ j, j+1 < 2*M →
      (state j).1.val ⊆ Λ.fam G (routeLab M γ.position (j+1)).site ∧
      state j = state (routeArrivalRank γ.position (routeLab M γ.position (j+1)).site) := by
  subst n
  intro G R state hf j hj
  have hj' : j < 2*M := by omega
  have ha := routeArrivalRank_lt_of_source γ.position (t := j+1) (by omega) hj
  have hi := Λ.firstGood_trajectory_at_route_site p q ρ κ hκ hs hsiteProb γ z x₀ f
    hbox hpre hcount hf j hj
  have hs := Λ.firstGood_trajectory_source_is_arrival p q ρ κ hκ hs hsiteProb γ z x₀ f
    (t := j+1) (by omega) hj hf
  dsimp only [state]
  rw [trajectoryState_of_lt x₀ f hj', trajectoryState_of_lt x₀ f (ha.trans hj)]
  exact ⟨hi.2, by simpa only [Nat.add_sub_cancel] using hs⟩

end NestLayout
end NearCritical.Section10
