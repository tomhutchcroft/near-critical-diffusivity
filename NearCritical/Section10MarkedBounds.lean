module

public import NearCritical.Section10MarkedChains

/-! Deterministic core of the pair estimate `prop.nw.pair`.

For nonnegative matrices `K t = A t + B t` on a finite state space (`A` = the
part of the step on which the two bridges intersect, `B` = the clean part), with
row sums of `K t` at most `rho t >= 1`:

* `detValue_le` (mass, `eq.nw.pair.mass`): `detValue K <= prod rho`.
* `detMarked_tube_le` (Steps 3--5): if every row sum of `A t` is at most
  `theta < 1` (a tube entanglement persists with weighted probability at most
  `theta`, `eq.nw.persist`) and from every state
  `sum_y B t x y * (row sum of A (t+1) at y) <= delta t` (after a clean step the
  risk of a tube entanglement at the next step is small, `eq.nw.enter`), then
  the weighted number of tube-entangled steps is at most
  `prod rho * (a_t(x) + sum delta) / (1 - theta)`.
* `detMarked_site_le`: if `C t` has row sums at most `delta t` (site
  entanglement produced by a clean step), the weighted number of such steps is
  at most `prod rho * sum delta`.

Together with `markedValue_integral_eq` this is `eq.nw.pair.overlap` once the
three one-step estimates are known for the actual kernels.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

/-- Product of the step bounds over `m` steps from time `t`. -/
def stepProd (ρ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | m+1, t => ρ t * stepProd ρ m (t+1)

/-- Sum of the step costs over `m` steps from time `t`. -/
def stepSum (δ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m+1, t => δ t + stepSum δ m (t+1)

lemma stepProd_nonneg {ρ : ℕ → ℝ} (hρ : ∀ t, 0 ≤ ρ t) : ∀ m t, 0 ≤ stepProd ρ m t := by
  intro m
  induction m with
  | zero => intro t; simp [stepProd]
  | succ m ih => intro t; exact mul_nonneg (hρ t) (ih (t+1))

lemma stepSum_nonneg {δ : ℕ → ℝ} (hδ : ∀ t, 0 ≤ δ t) : ∀ m t, 0 ≤ stepSum δ m t := by
  intro m
  induction m with
  | zero => intro t; simp [stepSum]
  | succ m ih => intro t; exact add_nonneg (hδ t) (ih (t+1))

variable {X : Type*} [Fintype X]

lemma detValue_nonneg (K : ℕ → X → X → ℝ) (hK : ∀ t x y, 0 ≤ K t x y) :
    ∀ m t x, 0 ≤ detValue K m t x := by
  intro m
  induction m with
  | zero => intro t x; simp [detValue]
  | succ m ih =>
    intro t x
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hK t x y) (ih (t+1) y))

lemma detMarked_nonneg (K A : ℕ → X → X → ℝ) (hK : ∀ t x y, 0 ≤ K t x y)
    (hA : ∀ t x y, 0 ≤ A t x y) : ∀ m t x, 0 ≤ detMarked K A m t x := by
  intro m
  induction m with
  | zero => intro t x; simp [detMarked]
  | succ m ih =>
    intro t x
    exact add_nonneg
      (Finset.sum_nonneg (fun y _ => mul_nonneg (hA t x y) (detValue_nonneg K hK m (t+1) y)))
      (Finset.sum_nonneg (fun y _ => mul_nonneg (hK t x y) (ih (t+1) y)))

/-- Mass bound. -/
theorem detValue_le (K : ℕ → X → X → ℝ) (hK : ∀ t x y, 0 ≤ K t x y) {ρ : ℕ → ℝ}
    (hρ : ∀ t, 0 ≤ ρ t) (hrow : ∀ t x, ∑ y, K t x y ≤ ρ t) :
    ∀ m t x, detValue K m t x ≤ stepProd ρ m t := by
  intro m
  induction m with
  | zero => intro t x; simp [detValue, stepProd]
  | succ m ih =>
    intro t x
    calc detValue K (m+1) t x = ∑ y, K t x y * detValue K m (t+1) y := rfl
      _ ≤ ∑ y, K t x y * stepProd ρ m (t+1) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih (t+1) y) (hK t x y))
      _ = (∑ y, K t x y) * stepProd ρ m (t+1) := (Finset.sum_mul _ _ _).symm
      _ ≤ ρ t * stepProd ρ m (t+1) :=
        mul_le_mul_of_nonneg_right (hrow t x) (stepProd_nonneg hρ m (t+1))

/-- Weighted number of site entanglements produced by clean steps. -/
theorem detMarked_site_le (K C : ℕ → X → X → ℝ) (hK : ∀ t x y, 0 ≤ K t x y)
    (hC : ∀ t x y, 0 ≤ C t x y) {ρ δ : ℕ → ℝ} (hρ : ∀ t, 1 ≤ ρ t)
    (hrow : ∀ t x, ∑ y, K t x y ≤ ρ t) (hδ : ∀ t, 0 ≤ δ t)
    (hc : ∀ t x, ∑ y, C t x y ≤ δ t) :
    ∀ m t x, detMarked K C m t x ≤ stepProd ρ m t * stepSum δ m t := by
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => zero_le_one.trans (hρ t)
  intro m
  induction m with
  | zero => intro t x; simp [detMarked, stepProd, stepSum]
  | succ m ih =>
    intro t x
    have hP := stepProd_nonneg hρ0 m (t+1)
    have hS := stepSum_nonneg hδ m (t+1)
    have h1 : (∑ y, C t x y * detValue K m (t+1) y) ≤ δ t * stepProd ρ m (t+1) := by
      calc (∑ y, C t x y * detValue K m (t+1) y)
          ≤ ∑ y, C t x y * stepProd ρ m (t+1) :=
            Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
              (detValue_le K hK hρ0 hrow m (t+1) y) (hC t x y))
        _ = (∑ y, C t x y) * stepProd ρ m (t+1) := (Finset.sum_mul _ _ _).symm
        _ ≤ δ t * stepProd ρ m (t+1) := mul_le_mul_of_nonneg_right (hc t x) hP
    have h2 : (∑ y, K t x y * detMarked K C m (t+1) y) ≤
        ρ t * (stepProd ρ m (t+1) * stepSum δ m (t+1)) := by
      calc (∑ y, K t x y * detMarked K C m (t+1) y)
          ≤ ∑ y, K t x y * (stepProd ρ m (t+1) * stepSum δ m (t+1)) :=
            Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih (t+1) y) (hK t x y))
        _ = (∑ y, K t x y) * (stepProd ρ m (t+1) * stepSum δ m (t+1)) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ ρ t * (stepProd ρ m (t+1) * stepSum δ m (t+1)) :=
            mul_le_mul_of_nonneg_right (hrow t x) (mul_nonneg hP hS)
    have hδP : 0 ≤ δ t * stepProd ρ m (t+1) := mul_nonneg (hδ t) hP
    show (∑ y, C t x y * detValue K m (t+1) y) + (∑ y, K t x y * detMarked K C m (t+1) y) ≤
      ρ t * stepProd ρ m (t+1) * (δ t + stepSum δ m (t+1))
    nlinarith [hρ t, mul_nonneg (sub_nonneg.mpr (hρ t)) hδP]

/-- **Weighted number of tube-entangled steps** (correlated phases). -/
theorem detMarked_tube_le (K A B : ℕ → X → X → ℝ) (hA : ∀ t x y, 0 ≤ A t x y)
    (hB : ∀ t x y, 0 ≤ B t x y) (hKAB : ∀ t x y, K t x y = A t x y + B t x y)
    {ρ δ : ℕ → ℝ} (hρ : ∀ t, 1 ≤ ρ t) (hrow : ∀ t x, ∑ y, K t x y ≤ ρ t)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : ∀ t x, ∑ y, A t x y ≤ θ)
    (hδ : ∀ t, 0 ≤ δ t)
    (hS : ∀ t x, ∑ y, B t x y * (∑ w, A (t+1) y w) ≤ δ t) :
    ∀ m t x, detMarked K A m t x ≤
      stepProd ρ m t * ((1 - θ)⁻¹ * (∑ y, A t x y) + (1 - θ)⁻¹ * stepSum δ m t) := by
  have hK : ∀ t x y, 0 ≤ K t x y := fun t x y => by
    rw [hKAB]
    exact add_nonneg (hA t x y) (hB t x y)
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => zero_le_one.trans (hρ t)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (1 - θ)⁻¹ := ⟨_, rfl⟩
  rw [← hlam]
  have h1θ : 0 < 1 - θ := by linarith
  have hlam0 : 0 < lam := by rw [hlam]; exact inv_pos.mpr h1θ
  have hlamθ : lam * (1 - θ) = 1 := by rw [hlam]; exact inv_mul_cancel₀ h1θ.ne'
  have hrowA0 : ∀ t x, 0 ≤ ∑ y, A t x y := fun t x => Finset.sum_nonneg (fun y _ => hA t x y)
  intro m
  induction m with
  | zero =>
    intro t x
    simp only [detMarked, stepProd, stepSum, mul_zero, add_zero, one_mul]
    exact mul_nonneg hlam0.le (hrowA0 t x)
  | succ m ih =>
    intro t x
    obtain ⟨P', hP'⟩ : ∃ P' : ℝ, P' = stepProd ρ m (t+1) := ⟨_, rfl⟩
    obtain ⟨S', hS'⟩ : ∃ S' : ℝ, S' = stepSum δ m (t+1) := ⟨_, rfl⟩
    obtain ⟨a, ha'⟩ : ∃ a : ℝ, a = ∑ y, A t x y := ⟨_, rfl⟩
    have hP0 : 0 ≤ P' := by rw [hP']; exact stepProd_nonneg hρ0 m (t+1)
    have hS0 : 0 ≤ S' := by rw [hS']; exact stepSum_nonneg hδ m (t+1)
    have ha0 : 0 ≤ a := by rw [ha']; exact hrowA0 t x
    have h1 : (∑ y, A t x y * detValue K m (t+1) y) ≤ a * P' := by
      rw [ha', hP']
      calc (∑ y, A t x y * detValue K m (t+1) y)
          ≤ ∑ y, A t x y * stepProd ρ m (t+1) :=
            Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
              (detValue_le K hK hρ0 hrow m (t+1) y) (hA t x y))
        _ = (∑ y, A t x y) * stepProd ρ m (t+1) := (Finset.sum_mul _ _ _).symm
    -- the key averaged estimate: sum_y K(x,y) a'(y) <= theta a + delta
    have hKa : (∑ y, K t x y * (∑ w, A (t+1) y w)) ≤ θ * a + δ t := by
      have hsplit : (∑ y, K t x y * (∑ w, A (t+1) y w)) =
          (∑ y, A t x y * (∑ w, A (t+1) y w)) + ∑ y, B t x y * (∑ w, A (t+1) y w) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun y _ => by rw [hKAB]; ring)
      have hAA : (∑ y, A t x y * (∑ w, A (t+1) y w)) ≤ θ * a := by
        rw [ha', Finset.mul_sum]
        exact Finset.sum_le_sum (fun y _ => by
          rw [mul_comm θ]
          exact mul_le_mul_of_nonneg_left (ha (t+1) y) (hA t x y))
      rw [hsplit]
      linarith [hS t x]
    have h2 : (∑ y, K t x y * detMarked K A m (t+1) y) ≤
        P' * lam * (θ * a + δ t) + P' * lam * S' * ρ t := by
      calc (∑ y, K t x y * detMarked K A m (t+1) y)
          ≤ ∑ y, K t x y * (P' * (lam * (∑ w, A (t+1) y w) + lam * S')) := by
            refine Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left ?_ (hK t x y))
            rw [hP', hS']
            exact ih (t+1) y
        _ = P' * lam * (∑ y, K t x y * (∑ w, A (t+1) y w)) +
            P' * lam * S' * (∑ y, K t x y) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun y _ => by ring)
        _ ≤ P' * lam * (θ * a + δ t) + P' * lam * S' * ρ t :=
            add_le_add (mul_le_mul_of_nonneg_left hKa (mul_nonneg hP0 hlam0.le))
              (mul_le_mul_of_nonneg_left (hrow t x)
                (mul_nonneg (mul_nonneg hP0 hlam0.le) hS0))
    have he1 : a + lam * θ * a = lam * a := by linear_combination (-a) * hlamθ
    show (∑ y, A t x y * detValue K m (t+1) y) + (∑ y, K t x y * detMarked K A m (t+1) y) ≤
      ρ t * stepProd ρ m (t+1) * (lam * (∑ y, A t x y) + lam * (δ t + stepSum δ m (t+1)))
    rw [← hP', ← hS', ← ha']
    have hmain : a * P' + (P' * lam * (θ * a + δ t) + P' * lam * S' * ρ t) =
        P' * (lam * a + lam * δ t) + ρ t * (P' * (lam * S')) := by
      have : a * P' + P' * lam * (θ * a) = P' * (lam * a) := by
        rw [← he1]
        ring
      linarith [this]
    have hnn : 0 ≤ P' * (lam * a + lam * δ t) :=
      mul_nonneg hP0 (add_nonneg (mul_nonneg hlam0.le ha0) (mul_nonneg hlam0.le (hδ t)))
    nlinarith [hρ t, mul_nonneg (sub_nonneg.mpr (hρ t)) hnn]

/-- **Weighted number of tube-entangled steps, potential form.** `φ t x` is the
risk carried by the pair state `x` before step `t`. Hypotheses:
`hAφ`: after an entangled step the expected risk is at most `theta` times the
entangled mass (in the application: the next signs are fresh, so with
probability one half the bridges start far apart);
`hBφ`: a clean step carries at most the remaining risk `φ t x - a_t(x)` plus
`delta t`. A stay step (identity kernel) satisfies it with `φ t = φ (t+1)`,
and risk need not be small pointwise. `detMarked_tube_le` is the case
`φ t x = a_t(x)`. -/
theorem detMarked_tube_le_potential (K A B : ℕ → X → X → ℝ) (hA : ∀ t x y, 0 ≤ A t x y)
    (hB : ∀ t x y, 0 ≤ B t x y) (hKAB : ∀ t x y, K t x y = A t x y + B t x y)
    {ρ δ : ℕ → ℝ} (hρ : ∀ t, 1 ≤ ρ t) (hrow : ∀ t x, ∑ y, K t x y ≤ ρ t)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ : ∀ t, 0 ≤ δ t)
    (φ : ℕ → X → ℝ) (hφ0 : ∀ t x, 0 ≤ φ t x)
    (hAφ : ∀ t x, ∑ y, A t x y * φ (t+1) y ≤ θ * ∑ y, A t x y)
    (hBφ : ∀ t x, ∑ y, B t x y * φ (t+1) y ≤ φ t x - (∑ y, A t x y) + δ t) :
    ∀ m t x, detMarked K A m t x ≤
      stepProd ρ m t * ((1 - θ)⁻¹ * φ t x + (1 - θ)⁻¹ * stepSum δ m t) := by
  have hK : ∀ t x y, 0 ≤ K t x y := fun t x y => by
    rw [hKAB]
    exact add_nonneg (hA t x y) (hB t x y)
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => zero_le_one.trans (hρ t)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (1 - θ)⁻¹ := ⟨_, rfl⟩
  rw [← hlam]
  have h1θ : 0 < 1 - θ := by linarith
  have hlam0 : 0 < lam := by rw [hlam]; exact inv_pos.mpr h1θ
  have hlamθ : lam * (1 - θ) = 1 := by rw [hlam]; exact inv_mul_cancel₀ h1θ.ne'
  intro m
  induction m with
  | zero =>
    intro t x
    simp only [detMarked, stepProd, stepSum, mul_zero, add_zero, one_mul]
    exact mul_nonneg hlam0.le (hφ0 t x)
  | succ m ih =>
    intro t x
    obtain ⟨P', hP'⟩ : ∃ P' : ℝ, P' = stepProd ρ m (t+1) := ⟨_, rfl⟩
    obtain ⟨S', hS'⟩ : ∃ S' : ℝ, S' = stepSum δ m (t+1) := ⟨_, rfl⟩
    obtain ⟨a, ha'⟩ : ∃ a : ℝ, a = ∑ y, A t x y := ⟨_, rfl⟩
    have hP0 : 0 ≤ P' := by rw [hP']; exact stepProd_nonneg hρ0 m (t+1)
    have hS0 : 0 ≤ S' := by rw [hS']; exact stepSum_nonneg hδ m (t+1)
    have ha0 : 0 ≤ a := by rw [ha']; exact Finset.sum_nonneg (fun y _ => hA t x y)
    have h1 : (∑ y, A t x y * detValue K m (t+1) y) ≤ a * P' := by
      rw [ha', hP']
      calc (∑ y, A t x y * detValue K m (t+1) y)
          ≤ ∑ y, A t x y * stepProd ρ m (t+1) :=
            Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
              (detValue_le K hK hρ0 hrow m (t+1) y) (hA t x y))
        _ = (∑ y, A t x y) * stepProd ρ m (t+1) := (Finset.sum_mul _ _ _).symm
    have hKφ : (∑ y, K t x y * φ (t+1) y) ≤ θ * a + (φ t x - a + δ t) := by
      have hsplit : (∑ y, K t x y * φ (t+1) y) =
          (∑ y, A t x y * φ (t+1) y) + ∑ y, B t x y * φ (t+1) y := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun y _ => by rw [hKAB]; ring)
      rw [hsplit, ha']
      exact add_le_add (hAφ t x) (hBφ t x)
    have h2 : (∑ y, K t x y * detMarked K A m (t+1) y) ≤
        P' * lam * (θ * a + (φ t x - a + δ t)) + P' * lam * S' * ρ t := by
      calc (∑ y, K t x y * detMarked K A m (t+1) y)
          ≤ ∑ y, K t x y * (P' * (lam * φ (t+1) y + lam * S')) := by
            refine Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left ?_ (hK t x y))
            rw [hP', hS']
            exact ih (t+1) y
        _ = P' * lam * (∑ y, K t x y * φ (t+1) y) + P' * lam * S' * (∑ y, K t x y) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun y _ => by ring)
        _ ≤ P' * lam * (θ * a + (φ t x - a + δ t)) + P' * lam * S' * ρ t :=
            add_le_add (mul_le_mul_of_nonneg_left hKφ (mul_nonneg hP0 hlam0.le))
              (mul_le_mul_of_nonneg_left (hrow t x)
                (mul_nonneg (mul_nonneg hP0 hlam0.le) hS0))
    have he1 : a + lam * θ * a = lam * a := by linear_combination (-a) * hlamθ
    show (∑ y, A t x y * detValue K m (t+1) y) + (∑ y, K t x y * detMarked K A m (t+1) y) ≤
      ρ t * stepProd ρ m (t+1) * (lam * φ t x + lam * (δ t + stepSum δ m (t+1)))
    rw [← hP', ← hS']
    have hmain : a * P' + (P' * lam * (θ * a + (φ t x - a + δ t)) + P' * lam * S' * ρ t) =
        P' * (lam * φ t x + lam * δ t) + ρ t * (P' * (lam * S')) := by
      have : a * P' + P' * lam * (θ * a) - P' * lam * a = 0 := by
        linear_combination P' * he1
      linarith [this]
    have hnn : 0 ≤ P' * (lam * φ t x + lam * δ t) :=
      mul_nonneg hP0 (add_nonneg (mul_nonneg hlam0.le (hφ0 t x)) (mul_nonneg hlam0.le (hδ t)))
    nlinarith [hρ t, mul_nonneg (sub_nonneg.mpr (hρ t)) hnn]

end NearCritical.Section10
