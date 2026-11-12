module

public import NearCritical.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Exact exponential factorization across actual neighboring endpoint heights.
No probability envelope or derivative inequality is assumed here. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- The source overline-A neighbor shift costs exp(r), even when the two
physical endpoints lie on different layers. -/
lemma exponential_gauge_edge_factorization (a b n k : ℝ) {r f g : ℝ}
    (hr : 0 ≤ r) (hab : |a-b| ≤ 1) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    f*g ≤ Real.exp r * Real.exp (-r*(n-k)) *
      (f*Real.exp (r*|a-k|)) * (g*Real.exp (r*(n-b))) := by
  have hablow := (abs_le.mp hab).1
  have hheight : 0 ≤ 1-(n-k)+|a-k|+(n-b) := by
    have h := le_abs_self (a-k)
    linarith
  have hE : 0 ≤ r*(1-(n-k)+|a-k|+(n-b)) := mul_nonneg hr hheight
  calc
    _ = (f*g)*1 := by ring
    _ ≤ (f*g)*Real.exp (r*(1-(n-k)+|a-k|+(n-b))) :=
      mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr hE) (mul_nonneg hf hg)
    _ = _ := by
      rw [show r*(1-(n-k)+|a-k|+(n-b)) =
        r+(-r*(n-k))+(r*|a-k|)+(r*(n-b)) by ring]
      rw [Real.exp_add,Real.exp_add,Real.exp_add]
      ring

/-- Every physical bond changes a distinguished coordinate by at most one,
independently of its open/closed state. -/
lemma bondTip_height_dist_le_one {d : ℕ} (e : Bond d) (i : Fin d) :
    |((bondTip e i : ℤ) : ℝ)-((e.1 i : ℤ) : ℝ)| ≤ 1 := by
  by_cases h : i = e.2
  · subst i
    simp [bondTip]
  · simp [bondTip,Function.update_of_ne h]

/-- Apply the scalar factorization to BOTH orientations of each actual bond.
The same common factor can be removed before the finite incidence estimate. -/
theorem bond_two_orientation_exponential_gauge {d : ℕ} (e : Bond d) (i : Fin d)
    (n k : ℤ) {r : ℝ} (hr : 0 ≤ r) (f g : Vertex d → ℝ)
    (hf : ∀ v, 0 ≤ f v) (hg : ∀ v, 0 ≤ g v) :
    f e.1*g (bondTip e)+f (bondTip e)*g e.1 ≤
      (Real.exp r*Real.exp (-r*((n : ℝ)-(k : ℝ)))) *
        ((f e.1*Real.exp (r*|((e.1 i : ℤ) : ℝ)-(k : ℝ)|))*
          (g (bondTip e)*Real.exp (r*((n : ℝ)-((bondTip e i : ℤ) : ℝ))))+
        (f (bondTip e)*Real.exp (r*|((bondTip e i : ℤ) : ℝ)-(k : ℝ)|))*
          (g e.1*Real.exp (r*((n : ℝ)-((e.1 i : ℤ) : ℝ))))) := by
  have hforward := exponential_gauge_edge_factorization
    ((e.1 i : ℤ) : ℝ) ((bondTip e i : ℤ) : ℝ) (n : ℝ) (k : ℝ) hr
    (by simpa only [abs_sub_comm] using bondTip_height_dist_le_one e i)
    (hf e.1) (hg (bondTip e))
  have hreverse := exponential_gauge_edge_factorization
    ((bondTip e i : ℤ) : ℝ) ((e.1 i : ℤ) : ℝ) (n : ℝ) (k : ℝ) hr
    (bondTip_height_dist_le_one e i) (hf (bondTip e)) (hg e.1)
  exact (add_le_add hforward hreverse).trans_eq (by ring)

end NearCritical
