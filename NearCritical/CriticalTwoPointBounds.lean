module

public import NearCritical.TwoPointAsymptotics

/-! Global critical two-point upper bounds derived from source assumption (A).
The regularization at distance one includes coincident endpoints. -/
@[expose] public section
namespace NearCritical
open MeasureTheory

lemma twoPoint_nonneg {d : ℕ} (p : unitInterval) (x y : Vertex d) :
    0 ≤ twoPoint d p x y := measureReal_nonneg

lemma twoPoint_le_one {d : ℕ} (p : unitInterval) (x y : Vertex d) :
    twoPoint d p x y ≤ 1 := measureReal_le_one

/-- Source (A) implies a global upper Green bound, including short distances
and coincident vertices. Dimension two is permitted; source use has d>=9. -/
theorem critical_twoPoint_global_upper {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Vertex d,
      twoPoint d (criticalPoint d) x y ≤
        C * (max 1 (euclideanNorm (x - y))) ^ ((2 : ℝ) - (d : ℝ)) := by
  obtain ⟨c, C, R, _, hC, _, htail⟩ := twoPointAsymptotics_eventual_bounds h
  let M : ℝ := max R 1
  let k : ℝ := M ^ ((2 : ℝ) - (d : ℝ))
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hk : 0 < k := Real.rpow_pos_of_pos hM _
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have he : (2 : ℝ) - (d : ℝ) ≤ 0 := sub_nonpos.mpr hd'
  refine ⟨max C k⁻¹, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro x y
  by_cases hr : euclideanNorm (x - y) ≤ M
  · have hw : max 1 (euclideanNorm (x - y)) ≤ M :=
      max_le (le_max_right _ _) hr
    have hwpos : 0 < max 1 (euclideanNorm (x - y)) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hp : k ≤ (max 1 (euclideanNorm (x - y))) ^ ((2 : ℝ) - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hwpos hw he
    calc
      twoPoint d (criticalPoint d) x y ≤ 1 := twoPoint_le_one _ _ _
      _ = k⁻¹ * k := (inv_mul_cancel₀ hk.ne').symm
      _ ≤ max C k⁻¹ * (max 1 (euclideanNorm (x - y))) ^ ((2 : ℝ) - (d : ℝ)) :=
        mul_le_mul (le_max_right _ _) hp hk.le (le_trans hC.le (le_max_left _ _))
  · have hMr : M ≤ euclideanNorm (x - y) := le_of_not_ge hr
    have hRr : R ≤ euclideanNorm (x - y) := le_trans (le_max_left _ _) hMr
    have h1r : 1 ≤ euclideanNorm (x - y) := le_trans (le_max_right _ _) hMr
    rw [max_eq_right h1r]
    exact (htail x y hRr).2.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (le_trans zero_le_one h1r) _))

lemma euclideanNorm_nonneg {d : ℕ} (x : Vertex d) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

lemma euclideanNorm_pos {d : ℕ} {x : Vertex d} (hx : x ≠ 0) :
    0 < euclideanNorm x := by
  have hex : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hex
  unfold euclideanNorm
  apply Real.sqrt_pos.mpr
  apply Finset.sum_pos' (fun j _ => sq_nonneg (x j : ℝ))
  refine ⟨i, Finset.mem_univ i, ?_⟩
  exact sq_pos_of_ne_zero (by exact_mod_cast hi)

/-- The same global bound with the source's literal Euclidean power, for
all distinct endpoints. The hypothesis (A) is still explicit. -/
theorem critical_twoPoint_upper_off_diagonal {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Vertex d, x ≠ y →
      twoPoint d (criticalPoint d) x y ≤
        C * euclideanNorm (x - y) ^ ((2 : ℝ) - (d : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := critical_twoPoint_global_upper hd h
  refine ⟨C, hC, ?_⟩
  intro x y hxy
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp := Real.rpow_le_rpow_of_nonpos
    (euclideanNorm_pos (sub_ne_zero.mpr hxy))
    (le_max_right 1 (euclideanNorm (x - y))) (sub_nonpos.mpr hd')
  exact (hb x y).trans (mul_le_mul_of_nonneg_left hp hC.le)

end NearCritical
