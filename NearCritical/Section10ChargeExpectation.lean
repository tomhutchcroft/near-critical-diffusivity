import NearCritical.Section10FrozenPairCharge
import NearCritical.Section10RevealedMarkWeight
import NearCritical.Section10EnergyCountMoment

noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory
open scoped Classical

/-- Bound the actual expected trajectory charge by the moment of the
number of common levels. The costs per common level are the two row
factors and the two revealed cube weights. -/
theorem trajectoryCharge_integral_le_of_terminal_counts {D d M : ℕ} (Λ : NestLayout D d)
    {p q : unitInterval} {ρ κ : ℝ} (R : NestRule D M d p q ρ κ Λ.X Λ.Φ)
    (hM : 1 ≤ M) (hρ : 1 ≤ ρ) (hκ : 1 ≤ κ)
    (hG : ∀ z, R.ρ z = refineReveal Λ.ρ₀ Λ.S₀ z)
    (hB : ∀ G ℓ, R.Bl G ℓ = Λ.Bl₀ G.1 ℓ)
    (hLaw : ∀ γ, 0 ≤ routeLaw D M γ) (A B Es Et : ℝ)
    (hA : 0 ≤ A) (hB₀ : 0 ≤ B) (hEs : 0 ≤ Es) (hEt : 0 ≤ Et) :
    let μ := (percolation d p).prod (percolation d q)
    let Y := SourceRoute D M × SourceRoute D M
    let N := routeCommonLevels D M
    let ν (y : Y) := routeLaw D M y.1 * routeLaw D M y.2
    let B₀ := 2*((2*A+1)*Es + B*Et)
    (∀ y : Y, 0 < ν y → ∀ G : Λ.Φ, (∃ z, R.ρ z = G) →
      0 < R.w y.1 G → 0 < R.w y.2 G →
      let s := jointRoutePrefix M y.1.position y.2.position (2*M)
      let K := R.kernel y.1 G
      let K' := R.kernel y.2 G
      let x := (R.x₀ y.1 G,R.x₀ y.2 G)
      (markedPrefixMass p q K K' s 0 0 x (fun h _ => (Λ.mergedSiteCount y.1 y.2 s h:ℝ)) /
        ρ ^ sharedCount s ≤ 2*(N y:ℝ)*Es) ∧
      (markedPrefixMass p q K K' s 0 0 x (fun h z => (Λ.mergedTubeCount y.1 y.2 G s h z:ℝ)) /
        ρ ^ sharedCount s ≤ 2*(N y:ℝ)*Et)) →
    (∫ z, Λ.trajectoryChargeSum R (2*M) z A B ∂μ) ≤
      B₀ * ∑ y : Y, ν y * ((N y:ℝ) * (ρ^2*κ^2)^(N y)) := by
  intro μ Y N ν B₀ hcount
  let s (y : Y) := jointRoutePrefix M y.1.position y.2.position (2*M)
  let Bl (y : Y) (G : Λ.Φ) (δ : SourceRoute D M) i := R.Bl G (routeLab M δ.position i)
  let T (y : Y) (G : Λ.Φ) := mergedTraceBlocks (Bl y G y.1) (Bl y G y.2) (s y) 0 0
  let f (y : Y) (G : Λ.Φ) (z : Configuration d × Configuration d) :=
    Λ.frozenPairCharge R y.1 y.2 G (s y) z A B
  let w (y : Y) (G : Λ.Φ) := R.w y.1 G * R.w y.2 G
  let V (y : Y) (z : Configuration d × Configuration d) := w y (R.ρ z) * f y (R.ρ z) z
  have hρ₀ := zero_lt_one.trans_le hρ
  have hcoef : 0 ≤ 2*A+1 := by linarith
  have hB' : 0 ≤ B₀ := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hcoef hEs) (mul_nonneg hB₀ hEt))
  have hLocal (y : Y) (G : Λ.Φ) : IsLocal (T y G) (f y G) :=
    Λ.frozenPairCharge_local R hB y.1 y.2 G A B
  have hDisj (y : Y) (G : Λ.Φ) : Disjoint (R.S G) (T y G) :=
    PairFresh.disjoint_blocks (Bl y G y.1) (Bl y G y.2) (s y) 0 0 (R.S G)
      (R.route_pair_fresh hM y.1 y.2 G (2*M) (2*M) 0 0)
  have hI (y : Y) : Integrable (V y) μ :=
    revealed_local_marked_mass_integrable p q R.ρ R.S (T y) R.hρ (w y) (f y) (hLocal y)
  have hN (y : Y) : sharedCount (s y) ≤ 2*N y := by
    have h := mergeSched_sharedCount_le RouteLabel.rank (routeLab M y.1.position)
      (routeLab M y.2.position) (routeLab_strictMono hM _) (routeLab_strictMono hM _)
      ((2*M)+(2*M)) (2*M) (2*M) 0 0 le_rfl
    refine h.trans ?_
    simpa only [commonLabelCount,Nat.zero_add,N,routeCommonLevels] using
      routeLab_common_le hM y.1.position y.2.position
  have hfrozen (y : Y) (hy : 0 < ν y) (G : Λ.Φ)
      (hreal : ∃ z, R.ρ z = G) (hγ : 0 < R.w y.1 G) (hγ' : 0 < R.w y.2 G) :
      (∫ z, f y G z ∂μ) ≤ B₀*(N y:ℝ)*ρ^(2*N y) := by
    obtain ⟨hsite,htube⟩ := hcount y hy G hreal hγ hγ'
    have h := Λ.frozenPairCharge_integral_le R y.1 y.2 G A B
      (2*(N y:ℝ)*Es) (2*(N y:ℝ)*Et) hA hB₀ hρ₀ hsite htube
    calc
      _ ≤ ((2*A+1)*(2*(N y:ℝ)*Es) + B*(2*(N y:ℝ)*Et))*ρ^sharedCount (s y) := h
      _ = B₀*(N y:ℝ)*ρ^sharedCount (s y) := by dsimp only [B₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ (hN y))
        (mul_nonneg hB' (Nat.cast_nonneg _))
  have hterm (y : Y) : ν y * (∫ z, V y z ∂μ) ≤
      B₀ * (ν y * ((N y:ℝ) * (ρ^2*κ^2)^(N y))) := by
    have hν : 0 ≤ ν y := mul_nonneg (hLaw y.1) (hLaw y.2)
    by_cases hy : ν y = 0
    · simp only [hy,zero_mul,mul_zero,le_refl]
    have hy' := lt_of_le_of_ne hν (Ne.symm hy)
    have hh := R.revealed_marked_pair_le p q hκ y.1 y.2 (T y) (hDisj y)
      (f y) (hLocal y)
      (mul_nonneg (mul_nonneg hB' (Nat.cast_nonneg _)) (pow_nonneg hρ₀.le (2*N y)))
      (hfrozen y hy')
    calc
      _ ≤ ν y * ((B₀*(N y:ℝ)*ρ^(2*N y))*κ^(2*N y)) :=
        mul_le_mul_of_nonneg_left hh hν
      _ = _ := by rw [mul_pow, pow_mul, pow_mul]; ring
  have he (z : Configuration d × Configuration d) :
      Λ.trajectoryChargeSum R (2*M) z A B = ∑ y : Y, ν y * V y z := by
    rw [Λ.trajectoryChargeSum_eq_frozenPairCharge R hM z (hG z) A B]
    conv_rhs => rw [Fintype.sum_prod_type]
  rw [integral_congr_ae (Filter.Eventually.of_forall he),
    integral_finsetSum _ (fun y _ => (hI y).const_mul (ν y)),Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [integral_const_mul]
  exact hterm y

end NearCritical.Section10.NestLayout
