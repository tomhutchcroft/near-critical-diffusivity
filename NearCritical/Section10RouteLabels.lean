module

public import NearCritical.Section10RouteWeightMain

/-! Steps of a source route as labels, and the counting inequality.

A route with transverse positions `X` makes `2M` steps, indexed by `t`:
`t = 0` the start at `(0, X 0)`; `t = 2j+1` the vertical step from `(j, X j)`
(for `j <= M-2`); `t = 2j+2` the horizontal step at level `j+1` from `X j` to
`X (j+1)` (a stay if they are equal); `t = 2M-1` the exit at `(M-1, X (M-1))`.
The rank of the step at time `t` is `t`, so ranks increase along every route and
two routes can share a label only at the same time (source 5408, 5550).

`routeLab_common_le`: two routes have at most `2 N` common labels, `N` the
number of common levels. With the existing bound of `2 N` common sites this
gives the counting inequality of `sourceRoute_good_weight_probability` with
`Lambda = (rho * kappa)^2`, which `routeLabel_good_weight_probability` removes.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- Coarse route sites: level and transverse position. -/
abbrev RSite (D : ℕ) : Type := ℕ × (Fin D → ℤ)

/-- Steps of a route. -/
inductive RouteLabel (D : ℕ) : Type
  | start (z : RSite D)
  | up (z : RSite D)
  | side (z : RSite D) (y : Fin D → ℤ)
  | exit (z : RSite D)
  | pad (k : ℕ)

namespace RouteLabel
variable {D : ℕ}

/-- Position of a step in the joint order. -/
def rank : RouteLabel D → ℕ
  | start _ => 0
  | up z => 2 * z.1 + 1
  | side z _ => 2 * z.1
  | exit z => 2 * z.1 + 1
  | pad k => k

/-- The site at which a step is made. -/
def site : RouteLabel D → RSite D
  | start z => z
  | up z => z
  | side z _ => z
  | exit z => z
  | pad _ => (0, 0)

end RouteLabel

/-- The step of the route `X` at time `t`. -/
def routeLab {D : ℕ} (M : ℕ) (X : ℕ → Fin D → ℤ) (t : ℕ) : RouteLabel D :=
  if t = 0 then RouteLabel.start (0, X 0)
  else if 2 * M ≤ t then RouteLabel.pad t
  else if t = 2 * M - 1 then RouteLabel.exit (M - 1, X (M - 1))
  else if t % 2 = 1 then RouteLabel.up ((t - 1) / 2, X ((t - 1) / 2))
  else RouteLabel.side (t / 2, X (t / 2 - 1)) (X (t / 2))

theorem rank_routeLab {D : ℕ} {M : ℕ} (hM : 1 ≤ M) (X : ℕ → Fin D → ℤ) (t : ℕ) :
    (routeLab M X t).rank = t := by
  unfold routeLab
  split_ifs with h1 h2 h3 h4 <;> simp only [RouteLabel.rank] <;> omega

theorem routeLab_strictMono {D : ℕ} {M : ℕ} (hM : 1 ≤ M) (X : ℕ → Fin D → ℤ) :
    StrictMono (fun t => (routeLab M X t).rank) := by
  intro s t hst
  simp only [rank_routeLab hM]
  exact hst

theorem routeLab_site {D : ℕ} {M : ℕ} (X : ℕ → Fin D → ℤ) {t : ℕ} (ht : t < 2 * M) :
    (routeLab M X t).site ∈ routeSites M X ∧ (routeLab M X t).site.1 = t / 2 := by
  unfold routeLab
  split_ifs with h1 h2 h3 h4
  · refine ⟨(mem_routeSites M X 0 (X 0)).mpr ⟨by omega, Or.inl rfl⟩, ?_⟩
    simp only [RouteLabel.site, h1]
  · omega
  · refine ⟨(mem_routeSites M X (M-1) (X (M-1))).mpr ⟨by omega, Or.inl rfl⟩, ?_⟩
    simp only [RouteLabel.site]
    omega
  · refine ⟨(mem_routeSites M X ((t-1)/2) (X ((t-1)/2))).mpr ⟨by omega, Or.inl rfl⟩, ?_⟩
    simp only [RouteLabel.site]
    omega
  · exact ⟨(mem_routeSites M X (t/2) (X (t/2-1))).mpr ⟨by omega, Or.inr rfl⟩, rfl⟩

/-- Two routes have at most `2 N` common labels. -/
theorem routeLab_common_le {D : ℕ} {M : ℕ} (hM : 1 ≤ M) (X X' : ℕ → Fin D → ℤ) :
    commonLabelCount (routeLab M X) (routeLab M X') (2 * M) (2 * M) ≤
      2 * (commonRouteLevels M X X').card := by
  unfold commonLabelCount
  have hcard : ((commonRouteLevels M X X') ×ˢ (Finset.range 2)).card =
      2 * (commonRouteLevels M X X').card := by
    rw [Finset.card_product, Finset.card_range, mul_comm]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun l : RouteLabel D => (l.rank / 2, l.rank % 2)) ?_ ?_
  · intro l hl
    have hl' := Finset.mem_coe.mp hl
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_Ico] at hl'
    obtain ⟨⟨t, ht, rfl⟩, ⟨t', ht', heq⟩⟩ := hl'
    have hr : t' = t := by
      have := congrArg RouteLabel.rank heq
      rwa [rank_routeLab hM, rank_routeLab hM] at this
    subst hr
    have h1 := routeLab_site (M := M) X (t := t') (by omega)
    have h2 := routeLab_site (M := M) X' (t := t') (by omega)
    rw [heq] at h2
    refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨?_, ?_⟩)
    · show (routeLab M X t').rank / 2 ∈ commonRouteLevels M X X'
      rw [rank_routeLab hM, ← h1.2]
      unfold commonRouteLevels
      simp only [Finset.mem_image, Finset.mem_inter]
      exact ⟨_, ⟨h1.1, h2.1⟩, rfl⟩
    · exact Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))
  · intro l hl l' hl' heq
    have hl1 := Finset.mem_coe.mp hl
    have hl2 := Finset.mem_coe.mp hl'
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_Ico] at hl1 hl2
    obtain ⟨⟨t, _, rfl⟩, _⟩ := hl1
    obtain ⟨⟨t', _, rfl⟩, _⟩ := hl2
    simp only [rank_routeLab hM, Prod.mk.injEq] at heq
    have : t = t' := by omega
    rw [this]

/-- **`prop.nw.main`, first conclusion, for actual routes with labelled steps.**
The counting inequality is proved; `Lambda = (rho * kappa)^2`. -/
theorem routeLabel_good_weight_probability {D : ℕ} (hD : 3 ≤ D) :
    ∃ (q0 C : ℝ) (M₀ : ℕ), 0 < q0 ∧ q0 < 1 ∧ 0 ≤ C ∧ ∀ M ≥ M₀,
    ∀ {d : ℕ} {X Φ : Type*} [Fintype X] [Fintype Φ] (p q : unitInterval)
      (ρ : Configuration d × Configuration d → Φ) (S : Φ → Finset (LBond d))
      (_hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
      (Bl : Φ → RouteLabel D → Finset (LBond d))
      (_hBl : ∀ F a b, a ≠ b → Disjoint (Bl F a) (Bl F b))
      (_hS : ∀ F a, Disjoint (S F) (Bl F a))
      (a : ∀ (γ : SourceRoute D M) (F : Φ) (t : ℕ), X →
        Set (Bl F (routeLab M γ.position t) → Bool))
      (o : ∀ (γ : SourceRoute D M) (F : Φ) (t : ℕ), X →
        (Bl F (routeLab M γ.position t) → Bool) → Finset X)
      (_ho : ∀ γ F t x, ∀ b ∈ a γ F t x, (o γ F t x b).Nonempty)
      {ϱ : ℝ} (_hϱ : 1 ≤ ϱ)
      (_hs : ∀ γ F t x, ϱ⁻¹ ≤
        localSuccessProbability p q (Bl F (routeLab M γ.position t)) (a γ F t x))
      (Es : RSite D → Finset (LBond d)) (_hEs : ∀ a b, a ≠ b → Disjoint (Es a) (Es b))
      (u : RSite D → Configuration d × Configuration d → ℝ)
      (_hu : ∀ a, IsLocal (Es a) (u a)) (_hu0 : ∀ a z, 0 ≤ u a z)
      (_humean : ∀ a, (∫ z, u a z ∂((percolation d p).prod (percolation d q))) = 1)
      {κ : ℝ} (_hκ : 1 ≤ κ)
      (_husq : ∀ a, (∫ z, u a z * u a z ∂((percolation d p).prod (percolation d q))) ≤ κ)
      (w : SourceRoute D M → Φ → ℝ) (_hw0 : ∀ γ F, 0 ≤ w γ F)
      (_hwu : ∀ γ z, w γ (ρ z) = ∏ a ∈ routeSites M γ.position, u a z)
      (x₀ : SourceRoute D M → Φ → X)
      (_hΛq : (ϱ * κ) ^ 2 * q0 < 1)
      (_hlarge : C * (ϱ * κ) ^ 2 / (1 - (ϱ * κ) ^ 2 * q0) ≤ (M:ℝ) ^ (D-1)),
      (1/8 : ℝ) ≤ ∫ z, (if (1/2:ℝ) ≤
          routeWeightSum (routeLaw D M) ρ w
            (sourceKernel p q Bl (fun γ => routeLab M γ.position) a o)
            (fun _ _ => 2 * M) x₀ z
        then (1:ℝ) else 0) ∂((percolation d p).prod (percolation d q)) := by
  obtain ⟨q0, C, M₀, hq0, hq1, hC, hmain⟩ := sourceRoute_good_weight_probability hD
  refine ⟨q0, C, max M₀ 1, hq0, hq1, hC, ?_⟩
  intro M hM d X Φ _ _ p q ρ S hρ Bl hBl hS a o ho ϱ hϱ hs Es hEs u hu hu0 humean κ hκ husq
    w hw0 hwu x₀ hΛq hlarge
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hϱκ : 1 ≤ ϱ * κ := one_le_mul_of_one_le_of_one_le hϱ hκ
  refine hmain M ((le_max_left _ _).trans hM) p q ρ S hρ RouteLabel.rank Bl hBl hS
    (fun γ => routeLab M γ.position) (fun γ => routeLab_strictMono hM1 γ.position)
    (fun _ => 2 * M) a o ho hϱ hs Es hEs u hu hu0 humean hκ husq
    (fun γ => routeSites M γ.position) w hw0 hwu x₀ (sq_nonneg _) hΛq hlarge ?_
  intro γ γ'
  have h1 := routeLab_common_le hM1 γ.position γ'.position
  have h2 := common_route_sites_card_le_two_levels M γ.position γ'.position
  have hN : routeCommonLevels D M (γ, γ') =
      (commonRouteLevels M γ.position γ'.position).card := rfl
  rw [hN]
  refine le_trans (mul_le_mul (pow_le_pow_right₀ hϱ h1) (pow_le_pow_right₀ hκ ?_ :
      κ ^ _ ≤ κ ^ (2 * (commonRouteLevels M γ.position γ'.position).card))
    (pow_nonneg (zero_le_one.trans hκ) _) (pow_nonneg (zero_le_one.trans hϱ) _))
    (le_of_eq ?_)
  · convert h2
  · rw [← mul_pow, pow_mul]

end NearCritical.Section10
