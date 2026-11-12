module

public import NearCritical.Section10ActualLayout
public import NearCritical.Section10LatticeHelpers

/-! Route facts for the actual layout.

* `position_coord`, `survive_range`: a surviving route stays in `{0..M-1}^D`.
* `routeLab_site_mem_box`: all its step sites are in the coarse box.
* `routeLab_hasTube`: a moving step of a route has a tube (its target is a
  positive lattice neighbour at a level below `M`).
* `siteCenter_target`: the target cube is the far cube of the tube.
* `siteCenter_bounds`: cube centres of the box, coordinate by coordinate.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

theorem position_coord {D M : ℕ} (x : Fin D → ℤ) (a : LazyRouteHistory D M) (j : ℕ)
    (i : Fin D) :
    routeHistoryPosition x a j i = x i + (lazyRouteCoordinateCount a i j : ℤ) := by
  unfold routeHistoryPosition lazyRouteCoordinateCount
  simp only [Pi.add_apply, Finset.sum_apply, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  by_cases h1 : i'.val < j
  · cases hai : a i' with
    | none => simp [h1, hai, lazyCoordinateStep]
    | some i'' =>
      by_cases h2 : i'' = i
      · subst h2
        simp [h1, hai, lazyCoordinateStep]
      · have h3 : i ≠ i'' := fun h => h2 h.symm
        simp [h1, hai, lazyCoordinateStep, h2, h3]
  · simp [h1]

theorem survive_range {D M : ℕ} {x : Fin D → ℤ} {a : LazyRouteHistory D M}
    (hsurv : lazyRouteSurvives x a) {j : ℕ} (hj : j < M) (i : Fin D) :
    0 ≤ routeHistoryPosition x a j i ∧ routeHistoryPosition x a j i < (M : ℤ) := by
  rw [position_coord]
  exact hsurv ⟨j, hj⟩ i

theorem routeLab_site_mem_box {D M : ℕ} (γ : SourceRoute D M)
    (hsurv : lazyRouteSurvives γ.1.1 γ.2) {t : ℕ} (ht : t < 2 * M) :
    (routeLab M γ.position t).site ∈ siteBoxOf D M := by
  have h := (routeLab_site γ.position ht).1
  have h2 := (mem_routeSites M γ.position (routeLab M γ.position t).site.1
    (routeLab M γ.position t).site.2).mp h
  rw [mem_siteBoxOf]
  refine ⟨h2.1, fun j => ?_⟩
  rcases h2.2 with h3 | h3
  · rw [h3]
    exact survive_range hsurv h2.1 j
  · rw [h3]
    exact survive_range hsurv (by omega) j

theorem routeLab_hasTube {D M : ℕ} (x : Fin D → ℤ) (a : LazyRouteHistory D M) {t : ℕ}
    (hstep : (routeLab M (routeHistoryPosition x a) t).isStep)
    (hmove : (routeLab M (routeHistoryPosition x a) t).target ≠
      (routeLab M (routeHistoryPosition x a) t).site) :
    HasTube M (routeLab M (routeHistoryPosition x a) t) := by
  unfold routeLab at hstep hmove ⊢
  by_cases h0 : t = 0
  · rw [if_pos h0] at hstep
    exact absurd hstep (fun h => h)
  rw [if_neg h0] at hstep hmove ⊢
  by_cases h1 : 2 * M ≤ t
  · rw [if_pos h1] at hstep
    exact absurd hstep (fun h => h)
  rw [if_neg h1] at hstep hmove ⊢
  by_cases h2 : t = 2 * M - 1
  · rw [if_pos h2] at hstep
    exact absurd hstep (fun h => h)
  rw [if_neg h2] at hstep hmove ⊢
  by_cases h3 : t % 2 = 1
  · rw [if_pos h3] at hmove ⊢
    refine ⟨⟨0, ?_⟩, ?_⟩
    · funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp [RouteLabel.target, RouteLabel.site, vecSite]
      · simp [RouteLabel.target, RouteLabel.site, vecSite]
    · show (t - 1) / 2 + 1 < M
      omega
  · rw [if_neg h3] at hmove ⊢
    have hj : t / 2 - 1 < M := by omega
    have hsucc := routeHistoryPosition_succ x a hj
    have hidx : t / 2 - 1 + 1 = t / 2 := by omega
    rw [hidx] at hsucc
    have hne : routeHistoryPosition x a (t / 2) ≠ routeHistoryPosition x a (t / 2 - 1) := by
      intro heq
      apply hmove
      simp only [RouteLabel.target, RouteLabel.site]
      rw [heq]
    cases hstepv : a ⟨t / 2 - 1, hj⟩ with
    | none =>
      rw [hstepv] at hsucc
      simp only [lazyCoordinateStep, add_zero] at hsucc
      exact absurd hsucc hne
    | some i =>
      rw [hstepv] at hsucc
      simp only [lazyCoordinateStep] at hsucc
      refine ⟨⟨i.succ, ?_⟩, ?_⟩
      · funext k
        refine Fin.cases ?_ (fun j => ?_) k
        · simp [RouteLabel.target, RouteLabel.site, vecSite]
        · simp only [RouteLabel.target, RouteLabel.site, vecSite, Fin.cons_succ, Pi.add_apply]
          rw [hsucc]
          simp [Pi.single_apply]
      · show t / 2 < M
        omega

theorem siteCenter_target {D M : ℕ} (t : ℕ) {ℓ : RouteLabel D} (h : HasTube M ℓ) :
    siteCenter t ℓ.target = farCenter t (siteCenter t ℓ.site) (dirOf ℓ) := by
  have hspec := dirOf_spec h
  funext k
  unfold siteCenter coarseCenter farCenter
  rw [hspec]
  by_cases hk : k = dirOf ℓ
  · subst hk
    simp only [Pi.add_apply, Pi.single_eq_same]
    ring
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hk]
    ring

theorem siteCenter_bounds {D M : ℕ} (t : ℕ) {s : RSite D} (hs : s ∈ siteBoxOf D M)
    (k : Fin (D + 1)) :
    0 ≤ siteCenter t s k ∧ siteCenter t s k ≤ 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ) := by
  obtain ⟨h1, h2⟩ := mem_siteBoxOf.mp hs
  have hM : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
    have : 1 ≤ M := by omega
    push_cast [Nat.cast_sub this]
    ring
  have ht0 : (0 : ℤ) ≤ 2 * (t : ℤ) := by positivity
  have hv : 0 ≤ vecSite s k ∧ vecSite s k ≤ (M : ℤ) - 1 := by
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [vecSite_zero]
      constructor
      · exact Int.natCast_nonneg _
      · have : (s.1 : ℤ) < (M : ℤ) := by exact_mod_cast h1
        linarith
    · rw [vecSite_succ]
      exact ⟨(h2 j).1, by linarith [(h2 j).2]⟩
  unfold siteCenter coarseCenter
  rw [hM]
  exact ⟨mul_nonneg ht0 hv.1, mul_le_mul_of_nonneg_left hv.2 ht0⟩

end NearCritical.Section10
