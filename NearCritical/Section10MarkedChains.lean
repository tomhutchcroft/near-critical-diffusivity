module

public import NearCritical.Section10CoupledWeight

/-! Chains with marked steps: exact factorisation into deterministic recursions.

For kernels that are local on pairwise disjoint fresh blocks, the expectation of
a chain weight against any `G` local on the explored bonds factorises EXACTLY:
`E[G * chainValue k] = E[G] * detValue kbar`, where `kbar t x y = E[k t x y]`
and `detValue` is the same recursion on real matrices
(`chainValue_integral_eq`). No normalisation is assumed.

`markedValue k a` is the weighted number of marked steps: at each step the mark
kernel `a` (in the application `a = k * 1{the step is entangled}`) may be used
once, the other steps using `k`. `markedValue_integral_eq` factorises it into
`detMarked kbar abar`.

So the pair estimate `eq.nw.pair.overlap` reduces to an inequality between
finite nonnegative matrices.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- Deterministic chain value of a family of matrices. -/
def detValue {X : Type*} [Fintype X] (K : ℕ → X → X → ℝ) : ℕ → ℕ → X → ℝ
  | 0, _, _ => 1
  | m+1, t, x => ∑ y, K t x y * detValue K m (t+1) y

/-- Deterministic weighted number of marked steps. -/
def detMarked {X : Type*} [Fintype X] (K A : ℕ → X → X → ℝ) : ℕ → ℕ → X → ℝ
  | 0, _, _ => 0
  | m+1, t, x => (∑ y, A t x y * detValue K m (t+1) y) + ∑ y, K t x y * detMarked K A m (t+1) y

/-- Weighted number of marked steps of a chain. -/
def markedValue {d : ℕ} {X : Type*} [Fintype X]
    (k a : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    ℕ → ℕ → X → Configuration d × Configuration d → ℝ
  | 0, _, _, _ => 0
  | m+1, t, x, z => (∑ y, a t x y z * chainValue k m (t+1) y z) +
      ∑ y, k t x y z * markedValue k a m (t+1) y z

lemma chainValue_isLoc {d : ℕ} {X : Type*} [Fintype X] (B : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (m t : ℕ) (x : X) : IsLoc (chainValue k m t x) :=
  ⟨_, chainValue_isLocal B k hk m t x⟩

lemma markedValue_isLoc {d : ℕ} {X : Type*} [Fintype X] (B : ℕ → Finset (LBond d))
    (k a : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (ha : ∀ t x y, IsLocal (B t) (a t x y)) :
    ∀ (m t : ℕ) (x : X), IsLoc (markedValue k a m t x) := by
  intro m
  induction m with
  | zero =>
    intro t x
    exact isLoc_const 0
  | succ m ih =>
    intro t x
    have h1 : IsLoc (fun z => ∑ y, a t x y z * chainValue k m (t+1) y z) :=
      isLoc_sum (fun y => IsLoc.mul ⟨_, ha t x y⟩ (chainValue_isLoc B k hk m (t+1) y))
    have h2 : IsLoc (fun z => ∑ y, k t x y z * markedValue k a m (t+1) y z) :=
      isLoc_sum (fun y => IsLoc.mul ⟨_, hk t x y⟩ (ih (t+1) y))
    obtain ⟨R1, hR1⟩ := h1
    obtain ⟨R2, hR2⟩ := h2
    refine ⟨R1 ∪ R2, ?_⟩
    obtain ⟨g1, hg1⟩ := hR1.mono (Finset.subset_union_left (s₂ := R2))
    obtain ⟨g2, hg2⟩ := hR2.mono (Finset.subset_union_right (s₁ := R1))
    exact ⟨fun b => g1 b + g2 b, fun z => by
      show (∑ y, a t x y z * chainValue k m (t+1) y z) +
        (∑ y, k t x y z * markedValue k a m (t+1) y z) = g1 _ + g2 _
      rw [← hg1 z, ← hg2 z]⟩

/-- **Exact factorisation of a chain weight.** -/
theorem chainValue_integral_eq {d : ℕ} {X : Type*} [Fintype X] (p q : unitInterval)
    (B : ℕ → Finset (LBond d)) (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) :
    ∀ (m t : ℕ) (x : X) (R : Finset (LBond d)) (G : Configuration d × Configuration d → ℝ),
      IsLocal R G → (∀ j, j < m → Disjoint R (B (t+j))) →
      (∫ z, G z * chainValue k m t x z ∂((percolation d p).prod (percolation d q))) =
        (∫ z, G z ∂((percolation d p).prod (percolation d q))) *
          detValue (fun t x y => ∫ z, k t x y z ∂((percolation d p).prod (percolation d q)))
            m t x := by
  intro m
  induction m with
  | zero =>
    intro t x R G _ _
    simp only [chainValue, detValue, mul_one]
  | succ m ih =>
    intro t x R G hG hR
    have hRt : Disjoint R (B t) := by
      have h := hR 0 (Nat.succ_pos m)
      simpa using h
    have hterm : ∀ y, (∫ z, (G z * k t x y z) * chainValue k m (t+1) y z
        ∂((percolation d p).prod (percolation d q))) =
        ((∫ z, G z ∂((percolation d p).prod (percolation d q))) *
          ∫ z, k t x y z ∂((percolation d p).prod (percolation d q))) *
          detValue (fun t x y => ∫ z, k t x y z ∂((percolation d p).prod (percolation d q)))
            m (t+1) y := by
      intro y
      have hloc : IsLocal (R ∪ B t) (fun z => G z * k t x y z) := hG.mul_union (hk t x y)
      rw [ih (t+1) y (R ∪ B t) (fun z => G z * k t x y z) hloc (by
        intro j hj
        have hidx : t + 1 + j = t + (j+1) := by omega
        rw [hidx, Finset.disjoint_union_left]
        exact ⟨hR (j+1) (by omega), hB t (t+(j+1)) (by omega)⟩),
        IsLocal.integral_mul p q hRt hG (hk t x y)]
    have hint : ∀ y, Integrable (fun z => (G z * k t x y z) * chainValue k m (t+1) y z)
        ((percolation d p).prod (percolation d q)) := fun y =>
      (IsLoc.mul (IsLoc.mul ⟨R, hG⟩ ⟨_, hk t x y⟩)
        (chainValue_isLoc B k hk m (t+1) y)).integrable p q
    calc (∫ z, G z * chainValue k (m+1) t x z ∂((percolation d p).prod (percolation d q)))
        = ∫ z, ∑ y, (G z * k t x y z) * chainValue k m (t+1) y z
            ∂((percolation d p).prod (percolation d q)) := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall fun z => ?_
          change G z * (∑ y, k t x y z * chainValue k m (t+1) y z) = _
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => (mul_assoc _ _ _).symm)
      _ = ∑ y, ∫ z, (G z * k t x y z) * chainValue k m (t+1) y z
            ∂((percolation d p).prod (percolation d q)) :=
          integral_finsetSum _ (fun y _ => hint y)
      _ = ∑ y, ((∫ z, G z ∂((percolation d p).prod (percolation d q))) *
            ∫ z, k t x y z ∂((percolation d p).prod (percolation d q))) *
            detValue (fun t x y => ∫ z, k t x y z ∂((percolation d p).prod (percolation d q)))
              m (t+1) y := Finset.sum_congr rfl (fun y _ => hterm y)
      _ = _ := by
          simp only [detValue]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => mul_assoc _ _ _)

/-- **Exact factorisation of the weighted number of marked steps.** -/
theorem markedValue_integral_eq {d : ℕ} {X : Type*} [Fintype X] (p q : unitInterval)
    (B : ℕ → Finset (LBond d)) (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (k a : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (ha : ∀ t x y, IsLocal (B t) (a t x y)) :
    ∀ (m t : ℕ) (x : X) (R : Finset (LBond d)) (G : Configuration d × Configuration d → ℝ),
      IsLocal R G → (∀ j, j < m → Disjoint R (B (t+j))) →
      (∫ z, G z * markedValue k a m t x z ∂((percolation d p).prod (percolation d q))) =
        (∫ z, G z ∂((percolation d p).prod (percolation d q))) *
          detMarked (fun t x y => ∫ z, k t x y z ∂((percolation d p).prod (percolation d q)))
            (fun t x y => ∫ z, a t x y z ∂((percolation d p).prod (percolation d q))) m t x := by
  intro m
  induction m with
  | zero =>
    intro t x R G _ _
    simp only [markedValue, detMarked, mul_zero, integral_zero]
  | succ m ih =>
    intro t x R G hG hR
    have hRt : Disjoint R (B t) := by
      have h := hR 0 (Nat.succ_pos m)
      simpa using h
    have hfut : ∀ j, j < m → Disjoint (R ∪ B t) (B (t+1+j)) := by
      intro j hj
      have hidx : t + 1 + j = t + (j+1) := by omega
      rw [hidx, Finset.disjoint_union_left]
      exact ⟨hR (j+1) (by omega), hB t (t+(j+1)) (by omega)⟩
    have hA : ∀ y, (∫ z, (G z * a t x y z) * chainValue k m (t+1) y z
        ∂((percolation d p).prod (percolation d q))) =
        ((∫ z, G z ∂((percolation d p).prod (percolation d q))) *
          ∫ z, a t x y z ∂((percolation d p).prod (percolation d q))) *
          detValue (fun t x y => ∫ z, k t x y z ∂((percolation d p).prod (percolation d q)))
            m (t+1) y := by
      intro y
      rw [chainValue_integral_eq p q B hB k hk m (t+1) y (R ∪ B t)
        (fun z => G z * a t x y z) (hG.mul_union (ha t x y)) hfut,
        IsLocal.integral_mul p q hRt hG (ha t x y)]
    have hK : ∀ y, (∫ z, (G z * k t x y z) * markedValue k a m (t+1) y z
        ∂((percolation d p).prod (percolation d q))) =
        ((∫ z, G z ∂((percolation d p).prod (percolation d q))) *
          ∫ z, k t x y z ∂((percolation d p).prod (percolation d q))) *
          detMarked (fun t x y => ∫ z, k t x y z ∂((percolation d p).prod (percolation d q)))
            (fun t x y => ∫ z, a t x y z ∂((percolation d p).prod (percolation d q)))
            m (t+1) y := by
      intro y
      rw [ih (t+1) y (R ∪ B t) (fun z => G z * k t x y z) (hG.mul_union (hk t x y)) hfut,
        IsLocal.integral_mul p q hRt hG (hk t x y)]
    have hintA : ∀ y, Integrable (fun z => (G z * a t x y z) * chainValue k m (t+1) y z)
        ((percolation d p).prod (percolation d q)) := fun y =>
      (IsLoc.mul (IsLoc.mul ⟨R, hG⟩ ⟨_, ha t x y⟩)
        (chainValue_isLoc B k hk m (t+1) y)).integrable p q
    have hintK : ∀ y, Integrable (fun z => (G z * k t x y z) * markedValue k a m (t+1) y z)
        ((percolation d p).prod (percolation d q)) := fun y =>
      (IsLoc.mul (IsLoc.mul ⟨R, hG⟩ ⟨_, hk t x y⟩)
        (markedValue_isLoc B k a hk ha m (t+1) y)).integrable p q
    have hsplit : (fun z => G z * markedValue k a (m+1) t x z) =
        fun z => (∑ y, (G z * a t x y z) * chainValue k m (t+1) y z) +
          ∑ y, (G z * k t x y z) * markedValue k a m (t+1) y z := by
      funext z
      change G z * ((∑ y, a t x y z * chainValue k m (t+1) y z) +
        ∑ y, k t x y z * markedValue k a m (t+1) y z) = _
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl (fun y _ => (mul_assoc _ _ _).symm)
    rw [hsplit, integral_add (integrable_finset_sum _ (fun y _ => hintA y))
      (integrable_finset_sum _ (fun y _ => hintK y)),
      integral_finsetSum _ (fun y _ => hintA y), integral_finsetSum _ (fun y _ => hintK y),
      Finset.sum_congr rfl (fun y _ => hA y), Finset.sum_congr rfl (fun y _ => hK y)]
    simp only [detMarked]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun y _ => mul_assoc _ _ _)

end NearCritical.Section10
