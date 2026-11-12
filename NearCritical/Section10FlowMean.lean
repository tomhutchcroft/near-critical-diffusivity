module

public import NearCritical.Section10Conductance

/-! Section10, eq.resistance_key_mean_mega: finite-law Cauchy--Schwarz
reduction. It avoids assuming integrability of inverse flow energy. Actual
finite Bernoulli laws can instantiate the arbitrary nonnegative weights. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]

/-- A finite-law energy/probability comparison, with actual event restriction.
No normalization of the finite measure is needed for Cauchy--Schwarz. -/
theorem mean_energy_product_lower (μ c e : X → ℝ) (A : Set X) {s : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hc : ∀ x, 0 ≤ c x) (he : ∀ x, 0 ≤ e x)
    (hs : 0 ≤ s) (hpoint : ∀ x ∈ A, s ≤ c x*e x) :
    s*(∑ x, if x ∈ A then μ x else 0)^2 ≤
      (∑ x, μ x*c x)*(∑ x, if x ∈ A then μ x*e x else 0) := by
  let r : X → ℝ := fun x => if x ∈ A then μ x*Real.sqrt s else 0
  let f : X → ℝ := fun x => μ x*c x
  let g : X → ℝ := fun x => if x ∈ A then μ x*e x else 0
  have hf (x : X) : 0 ≤ f x := mul_nonneg (hμ x) (hc x)
  have hg (x : X) : 0 ≤ g x := by
    dsimp [g]
    split_ifs
    · exact mul_nonneg (hμ x) (he x)
    · exact le_rfl
  have hp (x : X) : (r x)^2 ≤ f x*g x := by
    by_cases hx : x ∈ A
    · simp only [r,f,g,if_pos hx]
      calc
        _ = (μ x)^2*s := by rw [mul_pow,Real.sq_sqrt hs]
        _ ≤ (μ x)^2*(c x*e x) := mul_le_mul_of_nonneg_left (hpoint x hx) (sq_nonneg _)
        _ = _ := by ring
    · simp [r,f,g,hx]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => hf x) (fun x _ => hg x) (fun x _ => hp x)
  have hr : (∑ x, r x) = Real.sqrt s*(∑ x, if x ∈ A then μ x else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hx : x ∈ A <;> simp [r,hx,mul_comm]
  rw [hr,mul_pow,Real.sq_sqrt hs] at h
  exact h

/-- Positive event mass and pointwise work force a genuine positive energy
mean, so real division by zero is never used to manufacture a lower bound. -/
theorem mean_conductivity_lower (μ c e : X → ℝ) (A : Set X) {s : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hc : ∀ x, 0 ≤ c x) (he : ∀ x, 0 ≤ e x)
    (hs : 0 < s) (hpoint : ∀ x ∈ A, s ≤ c x*e x)
    (hA : 0 < ∑ x, if x ∈ A then μ x else 0) :
    0 < (∑ x, if x ∈ A then μ x*e x else 0) ∧
      (s*(∑ x, if x ∈ A then μ x else 0)^2)/(∑ x, if x ∈ A then μ x*e x else 0) ≤
        ∑ x, μ x*c x := by
  have hb := mean_energy_product_lower μ c e A hμ hc he hs.le hpoint
  have hnon : 0 ≤ ∑ x, if x ∈ A then μ x*e x else 0 := by
    apply Finset.sum_nonneg
    intro x _hx
    split_ifs
    · exact mul_nonneg (hμ x) (he x)
    · exact le_rfl
  have hpos : 0 < ∑ x, if x ∈ A then μ x*e x else 0 := by
    by_contra h
    have hz : (∑ x, if x ∈ A then μ x*e x else 0) = 0 :=
      le_antisymm (le_of_not_gt h) hnon
    have hl : 0 < s*(∑ x, if x ∈ A then μ x else 0)^2 := by positivity
    rw [hz,mul_zero] at hb
    linarith
  exact ⟨hpos,(div_le_iff₀ hpos).mpr hb⟩

/-- Uniform positive event mass and mean-energy upper bound give the explicit
conductivity lower bound used in the final Section10 scaling argument. -/
theorem mean_conductivity_lower_of_energy_bound (μ c e : X → ℝ) (A : Set X)
    {s a K : ℝ} (hμ : ∀ x, 0 ≤ μ x) (hc : ∀ x, 0 ≤ c x) (he : ∀ x, 0 ≤ e x)
    (hs : 0 < s) (ha : 0 < a) (hK : 0 < K)
    (hpoint : ∀ x ∈ A, s ≤ c x*e x)
    (hA : a ≤ ∑ x, if x ∈ A then μ x else 0)
    (henergy : (∑ x, if x ∈ A then μ x*e x else 0) ≤ K) :
    s*a^2/K ≤ ∑ x, μ x*c x := by
  have hp : 0 < ∑ x, if x ∈ A then μ x else 0 := ha.trans_le hA
  obtain ⟨hepos,hcmean⟩ := mean_conductivity_lower μ c e A hμ hc he hs hpoint hp
  have hsq : a^2 ≤ (∑ x, if x ∈ A then μ x else 0)^2 :=
    (sq_le_sq₀ ha.le hp.le).mpr hA
  calc
    _ ≤ (s*(∑ x, if x ∈ A then μ x else 0)^2)/K :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hs.le) hK.le
    _ ≤ (s*(∑ x, if x ∈ A then μ x else 0)^2)/(∑ x, if x ∈ A then μ x*e x else 0) :=
      div_le_div_of_nonneg_left (by positivity) hepos henergy
    _ ≤ _ := hcmean

end NearCritical.Section10
