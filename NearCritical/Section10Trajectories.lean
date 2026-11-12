module

public import NearCritical.Section10MarkedChains

/-! Chain weights as sums over trajectories.

A trajectory of `m` steps from state `x` is a function `f : Fin m → X` (the
states after each step). `trajWeight` is the product of the kernels along it.

* `chainValue_eq_sum_traj`: the chain weight is the sum of the trajectory
  weights. So each trajectory is an individual chain with its own weight, which
  is what the flow construction needs.
* `markedValue_eq_sum_traj`: the marked value is the sum over trajectories of
  `trajMarked`.
* `trajMarked_eq_weight_mul_count`: if the mark kernel is `k * e` for a step
  indicator `e`, then `trajMarked = trajWeight * (number of marked steps)`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

/-- Weight of a trajectory. -/
def trajWeight {d : ℕ} {X : Type*}
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    (m : ℕ) → ℕ → X → (Fin m → X) → Configuration d × Configuration d → ℝ
  | 0, _, _, _, _ => 1
  | m+1, t, x, f, z => k t x (f 0) z * trajWeight k m (t+1) (f 0) (Fin.tail f) z

/-- Marked weight of a trajectory. -/
def trajMarked {d : ℕ} {X : Type*}
    (k a : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    (m : ℕ) → ℕ → X → (Fin m → X) → Configuration d × Configuration d → ℝ
  | 0, _, _, _, _ => 0
  | m+1, t, x, f, z => a t x (f 0) z * trajWeight k m (t+1) (f 0) (Fin.tail f) z +
      k t x (f 0) z * trajMarked k a m (t+1) (f 0) (Fin.tail f) z

/-- Number of marked steps along a trajectory. -/
def trajCount {d : ℕ} {X : Type*}
    (e : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    (m : ℕ) → ℕ → X → (Fin m → X) → Configuration d × Configuration d → ℝ
  | 0, _, _, _, _ => 0
  | m+1, t, x, f, z => e t x (f 0) z + trajCount e m (t+1) (f 0) (Fin.tail f) z

/-- Functions on `Fin (m+1)` as a first value and a tail. -/
def consEquiv' (X : Type*) (m : ℕ) : X × (Fin m → X) ≃ (Fin (m+1) → X) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, Fin.tail f)
  left_inv p := by simp
  right_inv f := Fin.cons_self_tail f

lemma sum_piFinSucc {X : Type*} [Fintype X] (m : ℕ) (F : (Fin (m+1) → X) → ℝ) :
    (∑ f : Fin (m+1) → X, F f) = ∑ y : X, ∑ g : Fin m → X, F (Fin.cons y g) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (consEquiv' X m) (fun p => F (Fin.cons p.1 p.2)) F
    (fun _ => rfl)).symm

theorem chainValue_eq_sum_traj {d : ℕ} {X : Type*} [Fintype X]
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    ∀ (m t : ℕ) (x : X) (z : Configuration d × Configuration d),
      chainValue k m t x z = ∑ f : Fin m → X, trajWeight k m t x f z := by
  intro m
  induction m with
  | zero =>
    intro t x z
    simp [chainValue, trajWeight]
  | succ m ih =>
    intro t x z
    rw [sum_piFinSucc]
    simp only [chainValue, trajWeight, Fin.cons_zero, Fin.tail_cons]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [ih (t+1) y z, Finset.mul_sum]

theorem markedValue_eq_sum_traj {d : ℕ} {X : Type*} [Fintype X]
    (k a : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    ∀ (m t : ℕ) (x : X) (z : Configuration d × Configuration d),
      markedValue k a m t x z = ∑ f : Fin m → X, trajMarked k a m t x f z := by
  intro m
  induction m with
  | zero =>
    intro t x z
    simp [markedValue, trajMarked]
  | succ m ih =>
    intro t x z
    rw [sum_piFinSucc]
    simp only [markedValue, trajMarked, Fin.cons_zero, Fin.tail_cons]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_add_distrib, chainValue_eq_sum_traj k m (t+1) y z, ih (t+1) y z,
      Finset.mul_sum, Finset.mul_sum]

theorem trajMarked_eq_weight_mul_count {d : ℕ} {X : Type*}
    (k e : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    ∀ (m t : ℕ) (x : X) (f : Fin m → X) (z : Configuration d × Configuration d),
      trajMarked k (fun t x y z => k t x y z * e t x y z) m t x f z =
        trajWeight k m t x f z * trajCount e m t x f z := by
  intro m
  induction m with
  | zero =>
    intro t x f z
    simp [trajMarked, trajCount]
  | succ m ih =>
    intro t x f z
    simp only [trajMarked, trajWeight, trajCount]
    rw [ih (t+1) (f 0) (Fin.tail f) z]
    ring

lemma trajWeight_nonneg {d : ℕ} {X : Type*}
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ) (hk : ∀ t x y z, 0 ≤ k t x y z) :
    ∀ (m t : ℕ) (x : X) (f : Fin m → X) (z : Configuration d × Configuration d),
      0 ≤ trajWeight k m t x f z := by
  intro m
  induction m with
  | zero => intro t x f z; simp [trajWeight]
  | succ m ih => intro t x f z; exact mul_nonneg (hk t x (f 0) z) (ih (t+1) (f 0) _ z)

end NearCritical.Section10
