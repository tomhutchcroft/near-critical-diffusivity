module

public import NearCritical.Section10StepCardinality
public import NearCritical.Section10DiameterArith

/-! `lem.sprinkling.AB.geo` for a step of the actual layout, with all sizes
bounded: the probability that the sprinkling intrinsic diameter exceeds
`K_diam` is at most `(1 + C t^2) / (K_diam + 1)`, with an explicit constant
`C` depending on `d = m + 6`, `k`, the typicality constants, the Green
constant and `q0` (where `q <= q0 / t^2`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- The constant of the diameter bound. -/
def diamConst (m k : ℕ) (typ : TypicalParameters) (G₀ q0 : ℝ) : ℝ :=
  2 * ((m + 6 : ℕ) : ℝ) * 7 ^ (m + 6) * ((k : ℝ) * typ.boundaryUpper * 4) *
    (typ.countUpper * 2 ^ m * (2 * typ.boundaryUpper * 4)) *
    (2 * G₀ ^ 3 * greenConvConst (m + 5 + 1) * 8 ^ (2 * m + 6) * q0)

theorem actualLayout_diamFailure_small (m : ℕ) {G₀ : ℝ} (hG0 : 0 ≤ G₀)
    (hG : CriticalSupGreenUpper (m + 5 + 1) G₀) (q : unitInterval) {q0 : ℝ} (hq0 : 0 ≤ q0)
    (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (hq : (q : ℝ) ≤ q0 / (t : ℝ) ^ 2)
    (hbU : 0 ≤ typ.boundaryUpper) (hcU : 0 ≤ typ.countUpper)
    (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ) (Λ : NestLayout (m + 5) (m + 5 + 1))
    (hΛ : Λ = actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M)
    (G : Λ.Φ) (ℓ : RouteLabel (m + 5)) (hℓ : HasTube M ℓ) (x : Λ.X)
    (hnest : x.1.val ⊆ Λ.fam G ℓ.site) (hcard : x.1.val.card = k)
    (hgood : Λ.goodCube G ℓ.target) :
    ((percolation (m + 5 + 1) (criticalPoint (m + 5 + 1))).prod
        (percolation (m + 5 + 1) q)).real
      {z | ¬ svDiameter (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
        (Λ.tgt G ℓ) ≤ Λ.Kdiam} ≤
      (1 + diamConst m k typ G₀ q0 * (t : ℝ) ^ 2) / ((Kdiam : ℝ) + 1) := by
  have h := actualLayout_diamFailure_le (D := m + 5) (by omega) hG0 hG q typ t ht k hk
    MOff Mcoal Kdiam M Λ hΛ G ℓ hℓ x
  subst hΛ
  refine h.trans ?_
  have hT : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have hT0 : (0:ℝ) < (t : ℝ) := by linarith
  have hKpos : (0:ℝ) < (Kdiam : ℝ) + 1 := by positivity
  have hMid : (actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).Mid ℓ =
      stepMid t (siteCenter t ℓ.site) (dirOf ℓ) := by
    show MidOf t M ℓ = _
    unfold MidOf
    rw [if_pos hℓ]
  have hE : ((orientedLatticePairs
      ((actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).Mid ℓ)).card : ℝ) ≤
      2 * ((m + 6 : ℕ) : ℝ) * (7 * (t : ℝ)) ^ (m + 6) := by
    rw [hMid]
    have h1 := orientedLatticePairs_card_le (stepMid t (siteCenter t ℓ.site) (dirOf ℓ))
    have h2 := stepMid_card_le t (siteCenter t ℓ.site) (dirOf ℓ)
    have h3 : 2 * (3 * t) + 1 ≤ 7 * t := by omega
    have h4 : (stepMid t (siteCenter t ℓ.site) (dirOf ℓ)).card ≤ (7 * t) ^ (m + 5 + 1) :=
      h2.trans (Nat.pow_le_pow_left h3 _)
    have h5 : (orientedLatticePairs (stepMid t (siteCenter t ℓ.site) (dirOf ℓ))).card ≤
        (7 * t) ^ (m + 5 + 1) * (2 * (m + 5 + 1)) := h1.trans (Nat.mul_le_mul_right _ h4)
    have h6 := (Nat.cast_le (α := ℝ)).mpr h5
    push_cast at h6 ⊢
    have : ((m : ℝ) + 5 + 1) = (m : ℝ) + 6 := by ring
    rw [this] at h6
    linarith
  have hA := (actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).srcBoundary_card_le
    G ℓ x.2 x.1.val hnest
  rw [hcard] at hA
  have hB := (actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).tgtBoundary_card_le
    G ℓ hgood hbU
  have hm : m + 5 + 1 - 6 = m := by omega
  rw [hm] at hB
  have hnum := diam_numerator_le m (T := (t : ℝ)) (G := G₀) (K := greenConvConst (m + 5 + 1))
    (kk := (k : ℝ)) (bU := typ.boundaryUpper) (cU := typ.countUpper) (q := (q : ℝ)) (q0 := q0)
    hT hG0 (greenConvConst_nonneg _) (Nat.cast_nonneg k) hbU hcU hq0
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) q.2.1 hE hA hB hq
  unfold diamConst
  exact div_le_div_of_nonneg_right (add_le_add (le_refl 1) hnum) hKpos.le

end NearCritical.Section10
