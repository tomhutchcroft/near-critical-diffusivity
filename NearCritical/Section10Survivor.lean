module

public import NearCritical.Section10RouteLabels
public import NearCritical.Section9SprinkleOrLaw

/-! From `P[W >= 1/2] >= 1/8` to a surviving chain in the supercritical
configuration (the probabilistic half of `lem.chem.crossing`).

`NestRule` bundles the local data of the Section 10 construction on the coupled
law `(percolation d p).prod (percolation d q)` (`z.1` critical, `z.2` sprinkle):
a reveal, blocks of the route steps, a step rule with success probability at
least `1/rho`, and normalised site indicators with second moment at most `kappa`.
Its existence is what Sections 9 and 10.1 of the source provide
(`prop.proba.pregood`, `prop.proba.k-nest`).

* `ChainSurvives`: some sequence of states has every step kernel positive.
* `survivor_of_half_le`: `W >= 1/2` gives a route with positive cube weight
  whose chain survives.
* `nestRule_crossing_probability`: for every event `T` of the supercritical
  configuration `z.1 OR z.2` that contains all survivor configurations,
  `P_{p OR q}[T] >= 1/8`, for `M` large and `(rho kappa)^2 q0 < 1`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- Some sequence of states makes every remaining step kernel positive. -/
def ChainSurvives {d : ℕ} {X : Type*}
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    ℕ → ℕ → X → Configuration d × Configuration d → Prop
  | 0, _, _, _ => True
  | m+1, t, x, z => ∃ y, 0 < k t x y z ∧ ChainSurvives k m (t+1) y z

lemma chainValue_nonneg {d : ℕ} {X : Type*} [Fintype X]
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ) (hk0 : ∀ t x y z, 0 ≤ k t x y z) :
    ∀ (m t : ℕ) (x : X) (z : Configuration d × Configuration d), 0 ≤ chainValue k m t x z := by
  intro m
  induction m with
  | zero =>
    intro t x z
    simp only [chainValue, zero_le_one]
  | succ m ih =>
    intro t x z
    simp only [chainValue]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hk0 t x y z) (ih (t+1) y z))

theorem chainSurvives_of_chainValue_pos {d : ℕ} {X : Type*} [Fintype X]
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ) (hk0 : ∀ t x y z, 0 ≤ k t x y z) :
    ∀ (m t : ℕ) (x : X) (z : Configuration d × Configuration d),
      0 < chainValue k m t x z → ChainSurvives k m t x z := by
  intro m
  induction m with
  | zero =>
    intro t x z _
    trivial
  | succ m ih =>
    intro t x z hpos
    simp only [chainValue] at hpos
    obtain ⟨y, _, hy⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
      (f := fun _ : X => (0:ℝ)) (by simpa using hpos)
    have hk : 0 < k t x y z := by
      by_contra h
      have h0 : k t x y z = 0 := le_antisymm (not_lt.mp h) (hk0 t x y z)
      rw [h0, zero_mul] at hy
      exact lt_irrefl _ hy
    have hv : 0 < chainValue k m (t+1) y z := by
      by_contra h
      have h0 : chainValue k m (t+1) y z = 0 :=
        le_antisymm (not_lt.mp h) (chainValue_nonneg k hk0 m (t+1) y z)
      rw [h0, mul_zero] at hy
      exact lt_irrefl _ hy
    exact ⟨y, hk, ih (t+1) y z hv⟩

/-- A positive source kernel means: the step succeeded and the new state is an
offspring. -/
lemma stepKernel_pos {d : ℕ} {X : Type*} (T : Finset (LBond d))
    (a : Set (T → Bool)) (o : (T → Bool) → Finset X) (s : ℝ) (y : X)
    (z : Configuration d × Configuration d) (h : 0 < stepKernel T a o s y z) :
    T.restrict (layerVal z) ∈ a ∧ y ∈ o (T.restrict (layerVal z)) := by
  unfold stepKernel at h
  by_contra hc
  rw [if_neg hc] at h
  exact lt_irrefl _ h

/-- `W >= 1/2` produces a route of positive cube weight whose chain survives. -/
theorem survivor_of_half_le {d : ℕ} {X Φ Γ : Type*} [Fintype X] [Fintype Γ]
    (μ : Γ → ℝ) (hμ0 : ∀ γ, 0 ≤ μ γ) (ρ : Configuration d × Configuration d → Φ)
    (w : Γ → Φ → ℝ) (hw0 : ∀ γ F, 0 ≤ w γ F)
    (k : Γ → Φ → ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk0 : ∀ γ F t x y z, 0 ≤ k γ F t x y z) (n : Γ → Φ → ℕ) (x₀ : Γ → Φ → X)
    (z : Configuration d × Configuration d)
    (h : (1/2:ℝ) ≤ routeWeightSum μ ρ w k n x₀ z) :
    ∃ γ, 0 < μ γ ∧ 0 < w γ (ρ z) ∧
      ChainSurvives (k γ (ρ z)) (n γ (ρ z)) 0 (x₀ γ (ρ z)) z := by
  have hpos : (∑ _γ : Γ, (0:ℝ)) < ∑ γ, μ γ *
      (w γ (ρ z) * chainValue (k γ (ρ z)) (n γ (ρ z)) 0 (x₀ γ (ρ z)) z) := by
    rw [Finset.sum_const_zero]
    exact lt_of_lt_of_le (by norm_num) h
  obtain ⟨γ, _, hγ⟩ := Finset.exists_lt_of_sum_lt hpos
  have hv0 := chainValue_nonneg (k γ (ρ z)) (hk0 γ (ρ z)) (n γ (ρ z)) 0 (x₀ γ (ρ z)) z
  have hμ : 0 < μ γ := by
    by_contra hc
    have h0 : μ γ = 0 := le_antisymm (not_lt.mp hc) (hμ0 γ)
    rw [h0, zero_mul] at hγ
    exact lt_irrefl _ hγ
  have hw : 0 < w γ (ρ z) := by
    by_contra hc
    have h0 : w γ (ρ z) = 0 := le_antisymm (not_lt.mp hc) (hw0 γ _)
    rw [h0, zero_mul, mul_zero] at hγ
    exact lt_irrefl _ hγ
  have hv : 0 < chainValue (k γ (ρ z)) (n γ (ρ z)) 0 (x₀ γ (ρ z)) z := by
    by_contra hc
    have h0 : chainValue (k γ (ρ z)) (n γ (ρ z)) 0 (x₀ γ (ρ z)) z = 0 :=
      le_antisymm (not_lt.mp hc) hv0
    rw [h0, mul_zero, mul_zero] at hγ
    exact lt_irrefl _ hγ
  exact ⟨γ, hμ, hw, chainSurvives_of_chainValue_pos _ (hk0 γ (ρ z)) _ 0 _ z hv⟩

/-- Transfer of a coupled-law bound to the law of the supercritical
configuration `z.1 OR z.2`. No measurability of `T` is needed. -/
theorem coupled_event_transfer {d : ℕ} (p q : unitInterval)
    {W : Configuration d × Configuration d → ℝ} (hW : IsLoc W)
    (T : Set (Configuration d))
    (hsub : ∀ z, (1/2:ℝ) ≤ W z → sprinkleOrConfiguration z.1 z.2 ∈ T) {c : ℝ}
    (h : c ≤ ∫ z, (if (1/2:ℝ) ≤ W z then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q))) :
    c ≤ (percolation d (orParameter p q)).real T := by
  obtain ⟨R, g, hg⟩ := hW
  have hWm : Measurable W := by
    have hfun : W = fun z => g (R.restrict (layerVal z)) := funext hg
    rw [hfun]
    exact (measurable_of_finite g).comp
      ((Finset.measurable_restrict R).comp measurable_layerVal)
  have hAm : MeasurableSet {z : Configuration d × Configuration d | (1/2:ℝ) ≤ W z} :=
    measurableSet_le measurable_const hWm
  have hind : (fun z : Configuration d × Configuration d =>
      if (1/2:ℝ) ≤ W z then (1:ℝ) else 0) =
      Set.indicator {z | (1/2:ℝ) ≤ W z} (fun _ => (1:ℝ)) := by
    funext z
    by_cases hz : (1/2:ℝ) ≤ W z
    · rw [if_pos hz, Set.indicator_of_mem (by exact hz)]
    · rw [if_neg hz, Set.indicator_of_notMem (by exact hz)]
  rw [hind, integral_indicator_const _ hAm, smul_eq_mul, mul_one] at h
  refine h.trans ?_
  rw [← percolation_sprinkleOr_map d p q]
  have hle : ((percolation d p).prod (percolation d q))
      {z | (1/2:ℝ) ≤ W z} ≤
      (((percolation d p).prod (percolation d q)).map
        (fun z => sprinkleOrConfiguration z.1 z.2)) T :=
    (measure_mono (fun z hz => hsub z hz)).trans
      (Measure.le_map_apply measurable_sprinkleOrConfiguration.aemeasurable T)
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- The local data of the Section 10 construction. -/
structure NestRule (D M d : ℕ) (p q : unitInterval) (ϱ κ : ℝ) (X Φ : Type)
    [Fintype X] [Fintype Φ] where
  ρ : Configuration d × Configuration d → Φ
  S : Φ → Finset (LBond d)
  hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0)
  Bl : Φ → RouteLabel D → Finset (LBond d)
  hBl : ∀ F a b, a ≠ b → Disjoint (Bl F a) (Bl F b)
  hS : ∀ F a, Disjoint (S F) (Bl F a)
  a : ∀ (γ : SourceRoute D M) (F : Φ) (t : ℕ), X →
    Set (Bl F (routeLab M γ.position t) → Bool)
  o : ∀ (γ : SourceRoute D M) (F : Φ) (t : ℕ), X →
    (Bl F (routeLab M γ.position t) → Bool) → Finset X
  ho : ∀ γ F t x, ∀ b ∈ a γ F t x, (o γ F t x b).Nonempty
  hs : ∀ γ F t x, ϱ⁻¹ ≤
    localSuccessProbability p q (Bl F (routeLab M γ.position t)) (a γ F t x)
  Es : RSite D → Finset (LBond d)
  hEs : ∀ a b, a ≠ b → Disjoint (Es a) (Es b)
  u : RSite D → Configuration d × Configuration d → ℝ
  hu : ∀ a, IsLocal (Es a) (u a)
  hu0 : ∀ a z, 0 ≤ u a z
  humean : ∀ a, (∫ z, u a z ∂((percolation d p).prod (percolation d q))) = 1
  husq : ∀ a, (∫ z, u a z * u a z ∂((percolation d p).prod (percolation d q))) ≤ κ
  w : SourceRoute D M → Φ → ℝ
  hw0 : ∀ γ F, 0 ≤ w γ F
  hwu : ∀ γ z, w γ (ρ z) = ∏ a ∈ routeSites M γ.position, u a z
  x₀ : SourceRoute D M → Φ → X

/-- The chain kernels of a nest rule. -/
def NestRule.kernel {D M d : ℕ} {p q : unitInterval} {ϱ κ : ℝ} {X Φ : Type}
    [Fintype X] [Fintype Φ] (R : NestRule D M d p q ϱ κ X Φ) :
    SourceRoute D M → Φ → ℕ → X → X → Configuration d × Configuration d → ℝ :=
  sourceKernel p q R.Bl (fun γ => routeLab M γ.position) R.a R.o

/-- **Probabilistic half of `lem.chem.crossing`.** Any event of the supercritical
configuration containing all survivor configurations has probability at least
`1/8`. -/
theorem nestRule_crossing_probability {D : ℕ} (hD : 3 ≤ D) :
    ∃ (q0 C : ℝ) (M₀ : ℕ), 0 < q0 ∧ q0 < 1 ∧ 0 ≤ C ∧ ∀ M ≥ M₀,
    ∀ {d : ℕ} {X Φ : Type} [Fintype X] [Fintype Φ] (p q : unitInterval) {ϱ κ : ℝ}
      (_hϱ : 1 ≤ ϱ) (_hκ : 1 ≤ κ) (R : NestRule D M d p q ϱ κ X Φ)
      (_hΛq : (ϱ * κ) ^ 2 * q0 < 1)
      (_hlarge : C * (ϱ * κ) ^ 2 / (1 - (ϱ * κ) ^ 2 * q0) ≤ (M:ℝ) ^ (D-1))
      (T : Set (Configuration d))
      (_hpath : ∀ z γ, lazyRouteSurvives γ.1.1 γ.2 → 0 < R.w γ (R.ρ z) →
        ChainSurvives (R.kernel γ (R.ρ z)) (2 * M) 0 (R.x₀ γ (R.ρ z)) z →
        sprinkleOrConfiguration z.1 z.2 ∈ T),
      (1/8 : ℝ) ≤ (percolation d (orParameter p q)).real T := by
  obtain ⟨q0, C, M₀, hq0, hq1, hC, hmain⟩ := routeLabel_good_weight_probability hD
  obtain ⟨M₁, hM₁⟩ := sourceRouteSurvivalMass_eventually_half (by omega : 2 ≤ D)
  refine ⟨q0, C, max M₀ M₁, hq0, hq1, hC, ?_⟩
  intro M hM d X Φ _ _ p q ϱ κ hϱ hκ R hΛq hlarge T hpath
  have hmass : (0:ℝ) ≤ sourceRouteSurvivalMass D M :=
    le_trans (by norm_num) (hM₁ M ((le_max_right _ _).trans hM))
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le one_pos hϱ
  have hspos : ∀ γ F t x, 0 ≤
      localSuccessProbability p q (R.Bl F (routeLab M γ.position t)) (R.a γ F t x) :=
    fun γ F t x => (inv_nonneg.mpr hϱ0.le).trans (R.hs γ F t x)
  have hk0 : ∀ γ F t x y z, 0 ≤ R.kernel γ F t x y z :=
    fun γ F t x y z => stepKernel_nonneg _ _ _ (hspos γ F t x) y z
  have hprob := hmain M ((le_max_left _ _).trans hM) p q R.ρ R.S R.hρ R.Bl R.hBl R.hS
    R.a R.o R.ho hϱ R.hs R.Es R.hEs R.u R.hu R.hu0 R.humean hκ R.husq R.w R.hw0 R.hwu R.x₀
    hΛq hlarge
  have hWloc : IsLoc (routeWeightSum (routeLaw D M) R.ρ R.w R.kernel
      (fun _ _ => 2 * M) R.x₀) := by
    refine isLoc_sum (fun γ => (isLoc_const _).mul ?_)
    exact isLoc_of_reveal R.ρ R.S R.hρ
      (fun F z => R.w γ F * chainValue (R.kernel γ F) (2 * M) 0 (R.x₀ γ F) z)
      (fun F => (isLoc_const (R.w γ F)).mul
        ⟨_, chainValue_isLocal (fun t => R.Bl F (routeLab M γ.position t)) (R.kernel γ F)
          (fun t x y => stepKernel_isLocal _ _ _ _ y) (2 * M) 0 (R.x₀ γ F)⟩)
  refine coupled_event_transfer p q hWloc T ?_ hprob
  intro z hz
  obtain ⟨γ, hμ, hw, hsurv⟩ := survivor_of_half_le (routeLaw D M) (routeLaw_nonneg hmass) R.ρ
    R.w R.hw0 R.kernel hk0 (fun _ _ => 2 * M) R.x₀ z hz
  have hroute : lazyRouteSurvives γ.1.1 γ.2 := by
    by_contra hc
    unfold routeLaw at hμ
    rw [if_neg hc] at hμ
    exact lt_irrefl _ hμ
  exact hpath z γ hroute hw hsurv

end NearCritical.Section10
