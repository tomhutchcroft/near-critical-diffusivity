module

public import NearCritical.Section10ChainMean

/-! Source `prop.nw.pair`, mass bound `eq.nw.pair.mass`, on the ACTUAL coupled law.

Two chains (kernels `k`, `k'`, own time counters) are run in a joint order given
by a schedule: a list of moves `left` (only the first chain steps), `right`
(only the second), `both` (a shared step). `pairValue` is the joint remaining
weight; `pairValue_eq_mul` shows it is exactly the product of the two single
chain weights `chainValue`, so it is `zeta_Gamma * zeta_Gamma'`.

`PairFresh` is the precise freshness requirement of the joint exploration: the
block read at each joint step is disjoint from everything read before.

`pairValue_integral_le`: if single steps have total weight of mean at most one
and a shared step has joint total weight of mean at most `rho`, then for every
nonnegative `G` local on the already explored bonds
`E[G * zeta * zeta'] <= rho ^ (#shared steps) * E[G]`.
`stepKernel_pair_integral_le` gives the shared-step hypothesis for the source
kernels: `E[iota * iota'] <= 1/s'`.
`revealed_pair_mass_le` is the version conditional on a finite-valued reveal.

Not here: the count `#shared <= 2 N(Gamma, Gamma')` for actual routes, and the
overlap bound `eq.nw.pair.overlap`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

lemma IsLocal.mul_union {d : ℕ} {R T : Finset (LBond d)}
    {G K : Configuration d × Configuration d → ℝ} (hG : IsLocal R G) (hK : IsLocal T K) :
    IsLocal (R ∪ T) (fun z => G z * K z) :=
  (hG.mono Finset.subset_union_left).mul (hK.mono Finset.subset_union_right)

/-- One joint step of two chains. -/
inductive PairMove
  | left
  | right
  | both

/-- Number of shared steps of a schedule. -/
def sharedCount : List PairMove → ℕ
  | [] => 0
  | PairMove.left :: s => sharedCount s
  | PairMove.right :: s => sharedCount s
  | PairMove.both :: s => sharedCount s + 1

/-- Number of steps of the first chain. -/
def leftCount : List PairMove → ℕ
  | [] => 0
  | PairMove.left :: s => leftCount s + 1
  | PairMove.right :: s => leftCount s
  | PairMove.both :: s => leftCount s + 1

/-- Number of steps of the second chain. -/
def rightCount : List PairMove → ℕ
  | [] => 0
  | PairMove.left :: s => rightCount s
  | PairMove.right :: s => rightCount s + 1
  | PairMove.both :: s => rightCount s + 1

/-- Joint remaining weight of two chains run in the order of the schedule. -/
def pairValue {d : ℕ} {X X' : Type*} [Fintype X] [Fintype X']
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → X' → X' → Configuration d × Configuration d → ℝ) :
    List PairMove → ℕ → ℕ → X → X' → Configuration d × Configuration d → ℝ
  | [], _, _, _, _, _ => 1
  | PairMove.left :: s, t, t', x, x', z =>
      ∑ y, k t x y z * pairValue k k' s (t+1) t' y x' z
  | PairMove.right :: s, t, t', x, x', z =>
      ∑ y, k' t' x' y z * pairValue k k' s t (t'+1) x y z
  | PairMove.both :: s, t, t', x, x', z =>
      ∑ yy : X × X', (k t x yy.1 z * k' t' x' yy.2 z) *
        pairValue k k' s (t+1) (t'+1) yy.1 yy.2 z

/-- The joint weight is the product of the two single-chain weights. -/
theorem pairValue_eq_mul {d : ℕ} {X X' : Type*} [Fintype X] [Fintype X']
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → X' → X' → Configuration d × Configuration d → ℝ) :
    ∀ (s : List PairMove) (t t' : ℕ) (x : X) (x' : X')
      (z : Configuration d × Configuration d),
      pairValue k k' s t t' x x' z =
        chainValue k (leftCount s) t x z * chainValue k' (rightCount s) t' x' z := by
  intro s
  induction s with
  | nil =>
    intro t t' x x' z
    simp only [pairValue, leftCount, rightCount, chainValue, mul_one]
  | cons m s ih =>
    intro t t' x x' z
    cases m with
    | left =>
      simp only [pairValue, leftCount, rightCount, chainValue, ih]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun y _ => (mul_assoc _ _ _).symm)
    | right =>
      simp only [pairValue, leftCount, rightCount, chainValue, ih]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => mul_left_comm _ _ _)
    | both =>
      simp only [pairValue, leftCount, rightCount, chainValue, ih, Fintype.sum_prod_type]
      rw [Fintype.sum_mul_sum]
      exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun y' _ => by ring))

/-- Freshness of the joint exploration: each step reads a block disjoint from
the bonds `R` read so far. -/
def PairFresh {d : ℕ} (B B' : ℕ → Finset (LBond d)) :
    List PairMove → ℕ → ℕ → Finset (LBond d) → Prop
  | [], _, _, _ => True
  | PairMove.left :: s, t, t', R => Disjoint R (B t) ∧ PairFresh B B' s (t+1) t' (R ∪ B t)
  | PairMove.right :: s, t, t', R =>
      Disjoint R (B' t') ∧ PairFresh B B' s t (t'+1) (R ∪ B' t')
  | PairMove.both :: s, t, t', R =>
      Disjoint R (B t ∪ B' t') ∧ PairFresh B B' s (t+1) (t'+1) (R ∪ (B t ∪ B' t'))

lemma pairValue_exists_isLocal {d : ℕ} {X X' : Type*} [Fintype X] [Fintype X']
    (B B' : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → X' → X' → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (hk' : ∀ t x y, IsLocal (B' t) (k' t x y))
    (s : List PairMove) (t t' : ℕ) (x : X) (x' : X') :
    ∃ R : Finset (LBond d), IsLocal R (pairValue k k' s t t' x x') := by
  have h : pairValue k k' s t t' x x' = fun z =>
      chainValue k (leftCount s) t x z * chainValue k' (rightCount s) t' x' z :=
    funext (pairValue_eq_mul k k' s t t' x x')
  rw [h]
  exact ⟨_, (chainValue_isLocal B k hk _ t x).mul_union (chainValue_isLocal B' k' hk' _ t' x')⟩

/-- One weighted step with a fresh block, in inequality form. -/
lemma weighted_step_le {d : ℕ} (p q : unitInterval) {R T : Finset (LBond d)}
    (hRT : Disjoint R T) {G : Configuration d × Configuration d → ℝ}
    (hG : IsLocal R G) (hG0 : ∀ z, 0 ≤ G z) {Y : Type*} [Fintype Y]
    (κ V : Y → Configuration d × Configuration d → ℝ) (hκ : ∀ y, IsLocal T (κ y))
    (hVint : ∀ y, Integrable (fun z => (G z * κ y z) * V y z)
      ((percolation d p).prod (percolation d q)))
    {c a : ℝ} (hc : 0 ≤ c)
    (hV : ∀ y, (∫ z, (G z * κ y z) * V y z ∂((percolation d p).prod (percolation d q))) ≤
      c * ∫ z, G z * κ y z ∂((percolation d p).prod (percolation d q)))
    (ha : (∫ z, ∑ y, κ y z ∂((percolation d p).prod (percolation d q))) ≤ a) :
    (∫ z, G z * ∑ y, κ y z * V y z ∂((percolation d p).prod (percolation d q))) ≤
      c * a * ∫ z, G z ∂((percolation d p).prod (percolation d q)) := by
  have hint2 : ∀ y, Integrable (fun z => G z * κ y z)
      ((percolation d p).prod (percolation d q)) :=
    fun y => (hG.mul_union (hκ y)).integrable p q
  have hG0' : 0 ≤ ∫ z, G z ∂((percolation d p).prod (percolation d q)) :=
    integral_nonneg hG0
  calc (∫ z, G z * ∑ y, κ y z * V y z ∂((percolation d p).prod (percolation d q)))
      = ∫ z, ∑ y, (G z * κ y z) * V y z ∂((percolation d p).prod (percolation d q)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun z => ?_
        change G z * (∑ y, κ y z * V y z) = _
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => (mul_assoc _ _ _).symm)
    _ = ∑ y, ∫ z, (G z * κ y z) * V y z ∂((percolation d p).prod (percolation d q)) :=
        integral_finset_sum _ (fun y _ => hVint y)
    _ ≤ ∑ y, c * ∫ z, G z * κ y z ∂((percolation d p).prod (percolation d q)) :=
        Finset.sum_le_sum (fun y _ => hV y)
    _ = c * ∑ y, ∫ z, G z * κ y z ∂((percolation d p).prod (percolation d q)) :=
        (Finset.mul_sum _ _ _).symm
    _ = c * ∫ z, ∑ y, G z * κ y z ∂((percolation d p).prod (percolation d q)) := by
        rw [integral_finset_sum _ (fun y _ => hint2 y)]
    _ = c * ∫ z, G z * ∑ y, κ y z ∂((percolation d p).prod (percolation d q)) := by
        congr 1
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun z => ?_
        exact (Finset.mul_sum _ _ _).symm
    _ = c * ((∫ z, G z ∂((percolation d p).prod (percolation d q))) *
          ∫ z, ∑ y, κ y z ∂((percolation d p).prod (percolation d q))) := by
        rw [IsLocal.integral_mul p q hRT hG (isLocal_sum hκ)]
    _ ≤ c * ((∫ z, G z ∂((percolation d p).prod (percolation d q))) * a) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha hG0') hc
    _ = c * a * ∫ z, G z ∂((percolation d p).prod (percolation d q)) := by ring

/-- **Source `eq.nw.pair.mass` on the actual coupled law.** -/
theorem pairValue_integral_le {d : ℕ} {X X' : Type*} [Fintype X] [Fintype X']
    (p q : unitInterval) (B B' : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → X' → X' → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (hk' : ∀ t x y, IsLocal (B' t) (k' t x y))
    (hk0 : ∀ t x y z, 0 ≤ k t x y z) (hk'0 : ∀ t x y z, 0 ≤ k' t x y z)
    {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hL : ∀ t x, (∫ z, ∑ y, k t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hR : ∀ t x, (∫ z, ∑ y, k' t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hBoth : ∀ t t' x x', (∫ z, ∑ yy : X × X', k t x yy.1 z * k' t' x' yy.2 z
      ∂((percolation d p).prod (percolation d q))) ≤ ϱ) :
    ∀ (s : List PairMove) (t t' : ℕ) (x : X) (x' : X') (R : Finset (LBond d))
      (G : Configuration d × Configuration d → ℝ),
      IsLocal R G → (∀ z, 0 ≤ G z) → PairFresh B B' s t t' R →
      (∫ z, G z * pairValue k k' s t t' x x' z ∂((percolation d p).prod (percolation d q))) ≤
        ϱ ^ sharedCount s * ∫ z, G z ∂((percolation d p).prod (percolation d q)) := by
  intro s
  induction s with
  | nil =>
    intro t t' x x' R G _ _ _
    simp only [pairValue, sharedCount, mul_one, pow_zero, one_mul, le_refl]
  | cons m s ih =>
    intro t t' x x' R G hG hG0 hfresh
    cases m with
    | left =>
      simp only [PairFresh] at hfresh
      obtain ⟨hd, hF⟩ := hfresh
      have hint : ∀ y, Integrable (fun z => (G z * k t x y z) * pairValue k k' s (t+1) t' y x' z)
          ((percolation d p).prod (percolation d q)) := by
        intro y
        obtain ⟨R', hR'⟩ := pairValue_exists_isLocal B B' k k' hk hk' s (t+1) t' y x'
        exact ((hG.mul_union (hk t x y)).mul_union hR').integrable p q
      have h := weighted_step_le p q hd hG hG0 (fun y => k t x y)
        (fun y => pairValue k k' s (t+1) t' y x') (hk t x) hint
        (c := ϱ ^ sharedCount s) (a := 1) (pow_nonneg hϱ _)
        (fun y => ih (t+1) t' y x' (R ∪ B t) (fun z => G z * k t x y z)
          (hG.mul_union (hk t x y)) (fun z => mul_nonneg (hG0 z) (hk0 t x y z)) hF)
        (hL t x)
      simpa only [pairValue, sharedCount, mul_one] using h
    | right =>
      simp only [PairFresh] at hfresh
      obtain ⟨hd, hF⟩ := hfresh
      have hint : ∀ y, Integrable (fun z => (G z * k' t' x' y z) * pairValue k k' s t (t'+1) x y z)
          ((percolation d p).prod (percolation d q)) := by
        intro y
        obtain ⟨R', hR'⟩ := pairValue_exists_isLocal B B' k k' hk hk' s t (t'+1) x y
        exact ((hG.mul_union (hk' t' x' y)).mul_union hR').integrable p q
      have h := weighted_step_le p q hd hG hG0 (fun y => k' t' x' y)
        (fun y => pairValue k k' s t (t'+1) x y) (hk' t' x') hint
        (c := ϱ ^ sharedCount s) (a := 1) (pow_nonneg hϱ _)
        (fun y => ih t (t'+1) x y (R ∪ B' t') (fun z => G z * k' t' x' y z)
          (hG.mul_union (hk' t' x' y)) (fun z => mul_nonneg (hG0 z) (hk'0 t' x' y z)) hF)
        (hR t' x')
      simpa only [pairValue, sharedCount, mul_one] using h
    | both =>
      simp only [PairFresh] at hfresh
      obtain ⟨hd, hF⟩ := hfresh
      have hκ : ∀ yy : X × X', IsLocal (B t ∪ B' t')
          (fun z => k t x yy.1 z * k' t' x' yy.2 z) :=
        fun yy => (hk t x yy.1).mul_union (hk' t' x' yy.2)
      have hint : ∀ yy : X × X', Integrable (fun z => (G z * (k t x yy.1 z * k' t' x' yy.2 z)) *
          pairValue k k' s (t+1) (t'+1) yy.1 yy.2 z)
          ((percolation d p).prod (percolation d q)) := by
        intro yy
        obtain ⟨R', hR'⟩ := pairValue_exists_isLocal B B' k k' hk hk' s (t+1) (t'+1) yy.1 yy.2
        exact ((hG.mul_union (hκ yy)).mul_union hR').integrable p q
      have h := weighted_step_le p q hd hG hG0
        (fun (yy : X × X') z => k t x yy.1 z * k' t' x' yy.2 z)
        (fun (yy : X × X') => pairValue k k' s (t+1) (t'+1) yy.1 yy.2) hκ hint
        (c := ϱ ^ sharedCount s) (a := ϱ) (pow_nonneg hϱ _)
        (fun yy => ih (t+1) (t'+1) yy.1 yy.2 (R ∪ (B t ∪ B' t'))
          (fun z => G z * (k t x yy.1 z * k' t' x' yy.2 z))
          (hG.mul_union (hκ yy))
          (fun z => mul_nonneg (hG0 z) (mul_nonneg (hk0 t x yy.1 z) (hk'0 t' x' yy.2 z))) hF)
        (hBoth t t' x x')
      simpa only [pairValue, sharedCount, pow_succ] using h

/-- Shared step of two source kernels: `E[iota * iota'] <= 1/s'`, where the
first normaliser is the actual success probability and `s'` is any positive
normaliser. -/
theorem stepKernel_pair_integral_le {d : ℕ} {X X' : Type*} [Fintype X] [Fintype X']
    (p q : unitInterval) (T T' : Finset (LBond d))
    (a : Set ((T → Bool))) (a' : Set ((T' → Bool)))
    (o : (T → Bool) → Finset X) (o' : (T' → Bool) → Finset X')
    (ho : ∀ b ∈ a, (o b).Nonempty) (ho' : ∀ b ∈ a', (o' b).Nonempty)
    (hs : 0 < localSuccessProbability p q T a) {s' : ℝ} (hs' : 0 < s') :
    (∫ z, ∑ yy : X × X', stepKernel T a o (localSuccessProbability p q T a) yy.1 z *
        stepKernel T' a' o' s' yy.2 z ∂((percolation d p).prod (percolation d q))) ≤ s'⁻¹ := by
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = localSuccessProbability p q T a := ⟨_, rfl⟩
  rw [← hsdef] at hs ⊢
  obtain ⟨I, hI⟩ : ∃ I : Configuration d × Configuration d → ℝ, I = fun z : Configuration d × Configuration d =>
      if (T.restrict (layerVal z)) ∈ a then (1:ℝ) else 0 := ⟨_, rfl⟩
  obtain ⟨I', hI'⟩ : ∃ I' : Configuration d × Configuration d → ℝ, I' = fun z : Configuration d × Configuration d =>
      if (T'.restrict (layerVal z)) ∈ a' then (1:ℝ) else 0 := ⟨_, rfl⟩
  have hIloc : IsLocal T I := by
    rw [hI]
    exact ⟨fun b : (T → Bool) => if b ∈ a then (1:ℝ) else 0, fun _ => rfl⟩
  have hI'loc : IsLocal T' I' := by
    rw [hI']
    exact ⟨fun b : (T' → Bool) => if b ∈ a' then (1:ℝ) else 0, fun _ => rfl⟩
  have hI0 : ∀ z, 0 ≤ I z := by
    intro z
    rw [hI]
    beta_reduce
    split_ifs <;> norm_num
  have hI'0 : ∀ z, 0 ≤ I' z := by
    intro z
    rw [hI']
    beta_reduce
    split_ifs <;> norm_num
  have hI'1 : ∀ z, I' z ≤ 1 := by
    intro z
    rw [hI']
    beta_reduce
    split_ifs <;> norm_num
  have hIint : (∫ z, I z ∂((percolation d p).prod (percolation d q))) = s := by
    rw [hsdef, hI]
    rfl
  have hfun : (fun z : Configuration d × Configuration d =>
      ∑ yy : X × X', stepKernel T a o s yy.1 z * stepKernel T' a' o' s' yy.2 z) =
      fun z => (I z * s⁻¹) * (I' z * s'⁻¹) := by
    funext z
    simp only [Fintype.sum_prod_type]
    rw [← Fintype.sum_mul_sum, stepKernel_sum T a o ho, stepKernel_sum T' a' o' ho']
    simp only [hI, hI']
  have hlocL : IsLocal (T ∪ T') (fun z => (I z * s⁻¹) * (I' z * s'⁻¹)) :=
    (hIloc.mul (isLocal_const T s⁻¹)).mul_union (hI'loc.mul (isLocal_const T' s'⁻¹))
  have hlocR : IsLocal T (fun z => I z * (s⁻¹ * s'⁻¹)) :=
    hIloc.mul (isLocal_const T (s⁻¹ * s'⁻¹))
  have hs0 : 0 ≤ s⁻¹ * s'⁻¹ := mul_nonneg (inv_nonneg.mpr hs.le) (inv_nonneg.mpr hs'.le)
  rw [hfun]
  calc (∫ z, (I z * s⁻¹) * (I' z * s'⁻¹) ∂((percolation d p).prod (percolation d q)))
      ≤ ∫ z, I z * (s⁻¹ * s'⁻¹) ∂((percolation d p).prod (percolation d q)) := by
        refine integral_mono (hlocL.integrable p q) (hlocR.integrable p q) (fun z => ?_)
        have h1 : (I z * s⁻¹) * (I' z * s'⁻¹) = (I z * (s⁻¹ * s'⁻¹)) * I' z := by ring
        change (I z * s⁻¹) * (I' z * s'⁻¹) ≤ I z * (s⁻¹ * s'⁻¹)
        rw [h1]
        exact mul_le_of_le_one_right (mul_nonneg (hI0 z) hs0) (hI'1 z)
    _ = s * (s⁻¹ * s'⁻¹) := by rw [integral_mul_const, hIint]
    _ = s'⁻¹ := by rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-- **`eq.nw.pair.mass` conditional on a finite-valued reveal.** On each atom
of the reveal the two chains use their own blocks, kernels and joint schedule,
fresh with respect to the explored bonds `S F`. Then
`E[w(ρ) * zeta * zeta'] <= E[w(ρ) * rho ^ #shared(ρ)]` for `w >= 0`. -/
theorem revealed_pair_mass_le {d : ℕ} {X X' Φ : Type*} [Fintype X] [Fintype X'] [Fintype Φ]
    (p q : unitInterval) (ρ : Configuration d × Configuration d → Φ)
    (S : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (B B' : Φ → ℕ → Finset (LBond d)) (sch : Φ → List PairMove)
    (hfresh : ∀ F, PairFresh (B F) (B' F) (sch F) 0 0 (S F))
    (k : Φ → ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : Φ → ℕ → X' → X' → Configuration d × Configuration d → ℝ)
    (hk : ∀ F t x y, IsLocal (B F t) (k F t x y))
    (hk' : ∀ F t x y, IsLocal (B' F t) (k' F t x y))
    (hk0 : ∀ F t x y z, 0 ≤ k F t x y z) (hk'0 : ∀ F t x y z, 0 ≤ k' F t x y z)
    {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hL : ∀ F t x, (∫ z, ∑ y, k F t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hR : ∀ F t x, (∫ z, ∑ y, k' F t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hBoth : ∀ F t t' x x', (∫ z, ∑ yy : X × X', k F t x yy.1 z * k' F t' x' yy.2 z
      ∂((percolation d p).prod (percolation d q))) ≤ ϱ)
    (w : Φ → ℝ) (hw : ∀ F, 0 ≤ w F) (x₀ : Φ → X) (x₀' : Φ → X') :
    (∫ z, w (ρ z) * (chainValue (k (ρ z)) (leftCount (sch (ρ z))) 0 (x₀ (ρ z)) z *
        chainValue (k' (ρ z)) (rightCount (sch (ρ z))) 0 (x₀' (ρ z)) z)
      ∂((percolation d p).prod (percolation d q))) ≤
      ∫ z, w (ρ z) * ϱ ^ sharedCount (sch (ρ z))
        ∂((percolation d p).prod (percolation d q)) := by
  have hatom : ∀ (f : Φ → ℝ) (z : Configuration d × Configuration d),
      f (ρ z) = ∑ F, (if ρ z = F then (1:ℝ) else 0) * f F := by
    intro f z
    rw [Finset.sum_eq_single (ρ z)]
    · rw [if_pos rfl, one_mul]
    · intro F _ hF
      rw [if_neg (Ne.symm hF), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hloc : ∀ F, IsLocal (S F) (fun z => (if ρ z = F then (1:ℝ) else 0) * w F) :=
    fun F => (hρ F).mul (isLocal_const (S F) (w F))
  have hnn : ∀ F z, 0 ≤ (if ρ z = F then (1:ℝ) else 0) * w F := by
    intro F z
    refine mul_nonneg ?_ (hw F)
    split_ifs <;> norm_num
  have hterm : ∀ F, (∫ z, ((if ρ z = F then (1:ℝ) else 0) * w F) *
      pairValue (k F) (k' F) (sch F) 0 0 (x₀ F) (x₀' F) z
        ∂((percolation d p).prod (percolation d q))) ≤
      ϱ ^ sharedCount (sch F) * ∫ z, (if ρ z = F then (1:ℝ) else 0) * w F
        ∂((percolation d p).prod (percolation d q)) :=
    fun F => pairValue_integral_le p q (B F) (B' F) (k F) (k' F) (hk F) (hk' F) (hk0 F)
      (hk'0 F) hϱ (hL F) (hR F) (hBoth F) (sch F) 0 0 (x₀ F) (x₀' F) (S F) _ (hloc F)
      (hnn F) (hfresh F)
  have hint : ∀ F, Integrable (fun z => ((if ρ z = F then (1:ℝ) else 0) * w F) *
      pairValue (k F) (k' F) (sch F) 0 0 (x₀ F) (x₀' F) z)
      ((percolation d p).prod (percolation d q)) := by
    intro F
    obtain ⟨R', hR'⟩ := pairValue_exists_isLocal (B F) (B' F) (k F) (k' F) (hk F) (hk' F)
      (sch F) 0 0 (x₀ F) (x₀' F)
    exact ((hloc F).mul_union hR').integrable p q
  have hint2 : ∀ F, Integrable (fun z => ((if ρ z = F then (1:ℝ) else 0) * w F) *
      ϱ ^ sharedCount (sch F)) ((percolation d p).prod (percolation d q)) :=
    fun F => ((hloc F).mul (isLocal_const (S F) _)).integrable p q
  calc (∫ z, w (ρ z) * (chainValue (k (ρ z)) (leftCount (sch (ρ z))) 0 (x₀ (ρ z)) z *
        chainValue (k' (ρ z)) (rightCount (sch (ρ z))) 0 (x₀' (ρ z)) z)
        ∂((percolation d p).prod (percolation d q)))
      = ∫ z, ∑ F, ((if ρ z = F then (1:ℝ) else 0) * w F) *
          pairValue (k F) (k' F) (sch F) 0 0 (x₀ F) (x₀' F) z
          ∂((percolation d p).prod (percolation d q)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun z => ?_
        have h := hatom (fun F => w F * pairValue (k F) (k' F) (sch F) 0 0 (x₀ F) (x₀' F) z) z
        refine (congrArg (fun v => w (ρ z) * v)
          (pairValue_eq_mul _ _ _ _ _ _ _ z).symm).trans (h.trans ?_)
        exact Finset.sum_congr rfl (fun F _ => (mul_assoc _ _ _).symm)
    _ = ∑ F, ∫ z, ((if ρ z = F then (1:ℝ) else 0) * w F) *
          pairValue (k F) (k' F) (sch F) 0 0 (x₀ F) (x₀' F) z
          ∂((percolation d p).prod (percolation d q)) :=
        integral_finset_sum _ (fun F _ => hint F)
    _ ≤ ∑ F, ϱ ^ sharedCount (sch F) * ∫ z, (if ρ z = F then (1:ℝ) else 0) * w F
          ∂((percolation d p).prod (percolation d q)) :=
        Finset.sum_le_sum (fun F _ => hterm F)
    _ = ∑ F, ∫ z, ((if ρ z = F then (1:ℝ) else 0) * w F) * ϱ ^ sharedCount (sch F)
          ∂((percolation d p).prod (percolation d q)) :=
        Finset.sum_congr rfl (fun F _ =>
          ((integral_mul_const (ϱ ^ sharedCount (sch F)) _).trans (mul_comm _ _)).symm)
    _ = ∫ z, ∑ F, ((if ρ z = F then (1:ℝ) else 0) * w F) * ϱ ^ sharedCount (sch F)
          ∂((percolation d p).prod (percolation d q)) :=
        (integral_finset_sum _ (fun F _ => hint2 F)).symm
    _ = ∫ z, w (ρ z) * ϱ ^ sharedCount (sch (ρ z))
          ∂((percolation d p).prod (percolation d q)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun z => ?_
        have h := hatom (fun F => w F * ϱ ^ sharedCount (sch F)) z
        refine Eq.trans ?_ h.symm
        exact Finset.sum_congr rfl (fun F _ => mul_assoc _ _ _)

end NearCritical.Section10
