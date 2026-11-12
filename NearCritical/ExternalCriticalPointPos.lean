import NearCritical.ExternalMeanField

/-!
Positivity of the project's critical point, unconditionally:

  `1/(2d) <= criticalPoint d`   for every `d >= 1`.

Route: for the single-site set `S = {0}` the Duminil-Copin--Tassion quantity is
`phi_p({0}) <= 2 d p`, because the origin has at most `2d` neighbours. If
`2 d p < 1` then `phi_p({0}) < 1`, so by `phi_ge_one_of_density_pos` the
project's density vanishes at `p`. Hence no parameter below `1/(2d)` has
positive density.

This discharges the explicit hypothesis `0 < criticalPoint d` (registered as a
standard premise) without assumption (A).

-/

namespace NearCritical.External
open MeasureTheory
open Percolation.Literature Percolation.Literature.LatticeModels Percolation.Literature.DCT16

/-- Every site of `Z^d` has at most `2d` nearest neighbours. -/
theorem zdGraph_neighborFinset_card_le (d : ℕ) (x : Site d) :
    ((zdGraph d).neighborFinset x).card ≤ 2 * d := by
  classical
  have hsub : (zdGraph d).neighborFinset x ⊆
      (Finset.univ : Finset (Fin d × Bool)).image
        (fun q => if q.2 then x + Pi.single q.1 1 else x - Pi.single q.1 1) := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset, zdGraph_adj_iff] at hy
    obtain ⟨i, h | h⟩ := hy
    · exact Finset.mem_image.mpr ⟨(i, true), Finset.mem_univ _, by simp [h]⟩
    · exact Finset.mem_image.mpr ⟨(i, false), Finset.mem_univ _, by simp [h]⟩
  calc ((zdGraph d).neighborFinset x).card
      ≤ ((Finset.univ : Finset (Fin d × Bool)).image
          (fun q => if q.2 then x + Pi.single q.1 1 else x - Pi.single q.1 1)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]

/-- `phi_p({0}) <= 2 d p`. -/
theorem phi_singleton_le (d : ℕ) (p : unitInterval) :
    DCT16.phi p ({0} : Finset (Site d)) ≤ (p:ℝ) * (2 * (d:ℝ)) := by
  rw [DCT16.phi_def, Finset.sum_singleton]
  refine mul_le_mul_of_nonneg_left ?_ p.2.1
  refine (Finset.sum_le_sum (fun y _ => measureReal_le_one)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (zdGraph_neighborFinset_card_le d 0)

/-- Below `1/(2d)` the project's density vanishes. -/
theorem density_eq_zero_of_two_mul_lt_one {d : ℕ} (hd : 0 < d) (p : unitInterval)
    (h : 2 * (d:ℝ) * (p:ℝ) < 1) : NearCritical.density d p = 0 := by
  by_contra hne
  have hpos : 0 < NearCritical.density d p :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hp0 : (0:ℝ) ≤ (p:ℝ) := p.2.1
  have hp1 : (p:ℝ) < 1 := by nlinarith [mul_le_mul_of_nonneg_right hd1 hp0]
  have hphi := phi_ge_one_of_density_pos p hp1 hpos ({0} : Finset (Site d))
    (Finset.mem_singleton_self 0)
  have hle := phi_singleton_le d p
  linarith

/-- **`1/(2d) <= p_c`** for the project's critical point, every `d >= 1`. -/
theorem one_div_two_mul_le_criticalPoint {d : ℕ} (hd : 0 < d) :
    1 / (2 * (d:ℝ)) ≤ (NearCritical.criticalPoint d : ℝ) := by
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h2d : (0:ℝ) < 2 * (d:ℝ) := by linarith
  have hq0 : (0:ℝ) ≤ 1 / (2 * (d:ℝ)) := by positivity
  have hq1 : 1 / (2 * (d:ℝ)) ≤ 1 := by
    rw [div_le_one h2d]
    linarith
  have hle : (⟨1 / (2 * (d:ℝ)), hq0, hq1⟩ : unitInterval) ≤ NearCritical.criticalPoint d := by
    unfold NearCritical.criticalPoint
    apply le_sInf
    intro p hp
    by_contra hlt
    have hlt' : (p:ℝ) < 1 / (2 * (d:ℝ)) := not_le.mp hlt
    have h : 2 * (d:ℝ) * (p:ℝ) < 1 := by
      have := (lt_div_iff₀ h2d).mp hlt'
      linarith
    have hz := density_eq_zero_of_two_mul_lt_one hd p h
    have hp' : 0 < NearCritical.density d p := hp
    linarith
  exact hle

/-- **`0 < p_c`** for the project's critical point, every `d >= 1`, with no
hypotheses. -/
theorem criticalPoint_pos {d : ℕ} (hd : 0 < d) : 0 < (NearCritical.criticalPoint d : ℝ) := by
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h : (0:ℝ) < 1 / (2 * (d:ℝ)) := by positivity
  exact lt_of_lt_of_le h (one_div_two_mul_le_criticalPoint hd)

end NearCritical.External
