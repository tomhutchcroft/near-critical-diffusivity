module

public import NearCritical.CriticalTwoPointBounds
public import NearCritical.PercolationEndpoints
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Assumption (A) excludes both deterministic endpoints of the actual model.
No percolation threshold estimate or endpoint-interiority premise is used. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Filter

lemma euclideanNorm_coordinateRay {d : ℕ} (i : Fin d) (N : ℕ) :
    euclideanNorm (coordinateRay i N) = (N : ℝ) := by
  classical
  unfold euclideanNorm
  have hs : (∑ j : Fin d, ((coordinateRay i N j : ℤ) : ℝ) ^ 2) = (N : ℝ) ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp [coordinateRay]
    · intro j _ hji
      simp [coordinateRay, Function.update_of_ne hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [hs, Real.sqrt_sq (Nat.cast_nonneg N)]

private lemma ray_ne_zero {d : ℕ} (i : Fin d) {N : ℕ} (hN : 0 < N) :
    (0 : Vertex d) ≠ coordinateRay i N := by
  intro h
  have hi := congrFun h i
  have : (N : ℤ) = 0 := by simpa [coordinateRay] using hi.symm
  exact (Nat.ne_of_gt hN) (by exact_mod_cast this)

private lemma twoPoint_zero_off_diagonal {d : ℕ} {x y : Vertex d} (hxy : x ≠ y) :
    twoPoint d 0 x y = 0 := by
  simp [twoPoint, Measure.real, Measure.dirac_apply', measurableSet_connectionEvent,
    connectionEvent, openGraph_allClosed, SimpleGraph.reachable_bot, hxy, Ne.symm hxy]

private lemma twoPoint_one_ray {d : ℕ} (i : Fin d) (N : ℕ) :
    twoPoint d 1 0 (coordinateRay i N) = 1 := by
  simp [twoPoint, Measure.real, Measure.dirac_apply', measurableSet_connectionEvent,
    connectionEvent, allOpen_reachable_coordinateRay]

/-- The positive tail in (A) rules out the all-closed critical law. -/
theorem criticalPoint_pos_of_twoPointAsymptotics {d : ℕ} (i : Fin d)
    (h : TwoPointAsymptotics d) : 0 < (criticalPoint d : ℝ) := by
  by_contra hn
  have hz : (criticalPoint d : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (criticalPoint d).2.1
  have hp : criticalPoint d = 0 := Subtype.ext hz
  obtain ⟨c, C, R, hc, _, hR, htail⟩ := twoPointAsymptotics_eventual_bounds h
  obtain ⟨N, hN⟩ := exists_nat_gt (max R 1)
  have hNR : R ≤ (N : ℝ) := le_trans (le_max_left _ _) hN.le
  have hNposR : 0 < (N : ℝ) := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_right _ _) hN)
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hlo := (htail 0 (coordinateRay i N) (by
    simpa only [zero_sub, euclideanNorm_neg, euclideanNorm_coordinateRay] using hNR)).1
  rw [hp, twoPoint_zero_off_diagonal (ray_ne_zero i hNpos)] at hlo
  have hnorm : 0 < euclideanNorm ((0 : Vertex d) - coordinateRay i N) := by
    simpa only [zero_sub, euclideanNorm_neg, euclideanNorm_coordinateRay] using hNposR
  exact (not_le_of_gt (mul_pos hc (Real.rpow_pos_of_pos hnorm _))) hlo

/-- For d>2 the decaying upper tail in (A) rules out the all-open critical law. -/
theorem criticalPoint_lt_one_of_twoPointAsymptotics {d : ℕ} (hd : 2 < d)
    (i : Fin d) (h : TwoPointAsymptotics d) : (criticalPoint d : ℝ) < 1 := by
  by_contra hn
  have hz : (criticalPoint d : ℝ) = 1 := le_antisymm (criticalPoint d).2.2 (le_of_not_gt hn)
  have hp : criticalPoint d = 1 := Subtype.ext hz
  obtain ⟨C, _, hupper⟩ := critical_twoPoint_upper_off_diagonal (Nat.le_of_lt hd) h
  have hdR : 0 < (d : ℝ) - 2 := by
    have hd' : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ ((2 : ℝ) - (d : ℝ))) atTop (nhds 0) := by
    have hh := (tendsto_rpow_neg_atTop hdR).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    simpa only [Function.comp_def, neg_sub] using hh
  have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ ((2 : ℝ) - (d : ℝ))) atTop (nhds 0) := by
    simpa using hpow.const_mul C
  have hsmall : ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ ((2 : ℝ) - (d : ℝ)) < 1 :=
    hlim.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨N, hN, hsmallN⟩ := ((eventually_ge_atTop (1 : ℕ)).and hsmall).exists
  have hu := hupper 0 (coordinateRay i N) (ray_ne_zero i (by omega))
  rw [hp, twoPoint_one_ray] at hu
  simp only [zero_sub, euclideanNorm_neg, euclideanNorm_coordinateRay] at hu
  exact (not_le_of_gt hsmallN) hu

/-- Endpoint interiority is a consequence of the paper's actual hypothesis (A). -/
theorem criticalPoint_interior_of_twoPointAsymptotics {d : ℕ} (hd : 2 < d)
    (i : Fin d) (h : TwoPointAsymptotics d) :
    0 < (criticalPoint d : ℝ) ∧ (criticalPoint d : ℝ) < 1 :=
  ⟨criticalPoint_pos_of_twoPointAsymptotics i h,
    criticalPoint_lt_one_of_twoPointAsymptotics hd i h⟩

end NearCritical
