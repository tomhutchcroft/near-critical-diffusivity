module

public import NearCritical.Section10CoupledPairMass

/-! Carry an observed phase event to the final joint weight. Its prefix
mass may be distributed among all possible pairs of current nests. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- The normalized future-weight bound for an arbitrary nonnegative
distribution of past mass over current pair states. The remaining schedule
may include the shared exit. Its cost is exactly its nominal shared-step
factor, independently of the marks used to select the past mass. -/
theorem pairValue_future_weight_le {d : ℕ} {X X' : Type*} [Fintype X] [Fintype X']
    (p q : unitInterval) (B B' : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → X' → X' → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (hk' : ∀ t x y, IsLocal (B' t) (k' t x y))
    (hk₀ : ∀ t x y z, 0 ≤ k t x y z) (hk'₀ : ∀ t x y z, 0 ≤ k' t x y z)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hL : ∀ t x, (∫ z, ∑ y, k t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hR : ∀ t x, (∫ z, ∑ y, k' t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hBoth : ∀ t t' x x', (∫ z, ∑ y : X × X', k t x y.1 z * k' t' x' y.2 z
      ∂((percolation d p).prod (percolation d q))) ≤ ρ)
    (s : List PairMove) (t t' : ℕ) (R : Finset (LBond d)) (hF : PairFresh B B' s t t' R)
    (G : X × X' → Configuration d × Configuration d → ℝ)
    (hG : ∀ x, IsLocal R (G x)) (hG₀ : ∀ x z, 0 ≤ G x z)
    {b : ℝ} (hb : 0 < b) :
    let μ := (percolation d p).prod (percolation d q)
    (∫ z, ∑ x : X × X', G x z * pairValue k k' s t t' x.1 x.2 z ∂μ) /
      (b * ρ ^ sharedCount s) ≤ (∫ z, ∑ x : X × X', G x z ∂μ) / b := by
  intro μ
  have hGint (x : X × X') :
      Integrable (fun z => G x z * pairValue k k' s t t' x.1 x.2 z) μ := by
    obtain ⟨T, hT⟩ := pairValue_exists_isLocal B B' k k' hk hk' s t t' x.1 x.2
    exact ((hG x).mul_union hT).integrable p q
  have hsum : (∫ z, ∑ x : X × X', G x z * pairValue k k' s t t' x.1 x.2 z ∂μ) ≤
      ρ ^ sharedCount s * (∫ z, ∑ x : X × X', G x z ∂μ) := by
    rw [integral_finsetSum _ (fun x _ => hGint x),
      integral_finsetSum _ (fun x _ => (hG x).integrable p q), Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ =>
      pairValue_integral_le p q B B' k k' hk hk' hk₀ hk'₀ hρ.le hL hR hBoth
        s t t' x.1 x.2 R (G x) (hG x) (hG₀ x) hF
  apply (div_le_div_iff₀ (mul_pos hb (pow_pos hρ _)) hb).2
  convert mul_le_mul_of_nonneg_right hsum hb.le using 1 <;> ring

end NearCritical.Section10
