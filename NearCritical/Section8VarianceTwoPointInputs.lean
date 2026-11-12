module

public import NearCritical.AppendixTwoPointBridge
public import NearCritical.Section8CubeOneSided
public import NearCritical.Section8PairDiagrams

/-! Actual one-sided and bulk kernels used in the Appendix variance bounds. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

private theorem div_pow_le_of_le_mul {a b C : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hb : 0 < b)
    {s : ℝ} (hs : 0 ≤ s) (hle : b ≤ s * a) (k : ℕ) : C / a ^ k ≤ (C * s ^ k) / b ^ k := by
  apply (div_le_div_iff₀ (pow_pos ha _) (pow_pos hb _)).mpr
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le hle _) hC

/-- One-sided connection bound for the actual annulus with its nearest-face
depth and the shifted shell convention used in the Appendix. -/
theorem annulusTau_one_sided_shell_le {d n : ℕ} (hd : 1 ≤ d) (C : ℝ) (hC : 0 ≤ C)
    (panis : PanisHalfSpaceTwoPointUpper d C) (heart : Finset (Vertex d))
    (u w : Vertex d) (hu : u ∈ heartAnnulus (centeredBox d n) heart)
    (hw : w ∈ heartAnnulus (centeredBox d n) heart) :
    annulusTau (criticalPoint d) (centeredBox d n) heart w u ≤
      ((2 * C) * (2 : ℝ) ^ (d - 1)) * (1 + ((n : ℝ) - latticeDistance 0 u)) /
        ((linfDist w u + 1 : ℕ) : ℝ) ^ (d - 1) := by
  let Q := centeredBox d n
  let D := heartAnnulus Q heart
  let l := 1 + ((n : ℝ) - latticeDistance 0 u)
  let M := max 1 (latticeDistance u w)
  let S : ℝ := (linfDist w u + 1 : ℕ)
  have hl : 0 ≤ l := by
    obtain ⟨i, cut, b, hQ, hdepth⟩ := cube_nearest_coordinate_halfSpace hd u (heartAnnulus_subset Q heart hu)
    have h : 0 ≤ coordinateDepth i cut b u := hQ (heartAnnulus_subset Q heart hu)
    dsimp [l]
    linarith
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  have hS : 0 < S := by dsimp [S]; positivity
  have hle : S ≤ 2 * M := by
    dsimp [S]
    rw [Nat.cast_add, Nat.cast_one, linfDist_cast_eq_latticeDistance, latticeDistance_comm w u]
    have h₁ : 1 ≤ M := le_max_left _ _
    have h₂ : latticeDistance u w ≤ M := le_max_right _ _
    linarith
  have h := cube_one_sided_connection_le (n := n) hd C hC panis (D : Set (Vertex d))
    (heartAnnulus_subset Q heart) u w hu hw
  have hexp : (1 : ℝ) - (d : ℝ) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [hexp, Real.rpow_neg hM.le, Real.rpow_natCast, inv_eq_one_div, ← mul_div_assoc, mul_one] at h
  rw [annulusTau_comm _ _ _ w u]
  refine h.trans ?_
  calc
    _ ≤ ((2 * C) * l * (2 : ℝ) ^ (d - 1)) / S ^ (d - 1) :=
      div_pow_le_of_le_mul (by positivity) hM hS (by norm_num) hle _
    _ = _ := by change _ = ((2 * C) * (2 : ℝ) ^ (d - 1)) * l / S ^ (d - 1); ring

/-- The capstone's two separated one-sided estimates. The first permits a
nonzero starting depth. The second starts at a boundary point of depth zero. -/
theorem annulusTau_variance_separated_le {d : ℕ} (hd : 1 ≤ d) (C : ℝ) (hC : 0 ≤ C)
    (panis : PanisHalfSpaceTwoPointUpper d C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n h : ℕ), 1 ≤ n → 2 * h ≤ n →
      ∀ (heart : Finset (Vertex d)),
      let D := heartAnnulus (centeredBox d n) heart
      let τ := annulusTau (criticalPoint d) (centeredBox d n) heart
      ∀ x ∈ D, linfDist 0 x = n →
      (∀ w ∈ D, linfDist 0 w ≤ h → ∀ u ∈ D, linfDist x u < (n - h) / 2 →
        τ w u ≤ K * (1 + ((n : ℝ) - latticeDistance 0 u)) / (n : ℝ) ^ (d - 1)) ∧
      (∀ u ∈ D, (n - h) / 2 ≤ linfDist x u → τ u x ≤ K / (n : ℝ) ^ (d - 1)) := by
  let J : ℝ := (2 * C) * (2 : ℝ) ^ (d - 1)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨J * (4 : ℝ) ^ (d - 1), by positivity, ?_⟩
  intro n h hn hh heart D τ x hx hxN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxN' : latticeDistance 0 x = n := by rw [← linfDist_cast_eq_latticeDistance, hxN]
  constructor
  · intro w hw hwN u hu hxu
    have ht₁ := linfDist_triangle 0 w x
    have ht₂ := linfDist_triangle w u x
    rw [hxN] at ht₁
    rw [linfDist_comm u x] at ht₂
    have hsep : (n : ℝ) ≤ 4 * ((linfDist w u + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 4 * (linfDist w u + 1) by omega)
    let l := 1 + ((n : ℝ) - latticeDistance 0 u)
    have hl : 0 ≤ l := by
      obtain ⟨i, cut, b, hQ, hdepth⟩ := cube_nearest_coordinate_halfSpace hd u (heartAnnulus_subset _ _ hu)
      have ht : 0 ≤ coordinateDepth i cut b u := hQ (heartAnnulus_subset _ _ hu)
      dsimp [l]
      linarith
    have h := annulusTau_one_sided_shell_le hd C hC panis heart u w hu hw
    refine h.trans ?_
    calc
      _ ≤ ((J * l) * (4 : ℝ) ^ (d - 1)) / (n : ℝ) ^ (d - 1) :=
        div_pow_le_of_le_mul (by positivity) (by positivity) hn0 (by norm_num) hsep _
      _ = _ := by change _ = (J * (4 : ℝ) ^ (d - 1)) * l / (n : ℝ) ^ (d - 1); ring
  · intro u hu hsep
    have hle : (n : ℝ) ≤ 4 * ((linfDist u x + 1 : ℕ) : ℝ) := by
      rw [linfDist_comm u x]
      exact_mod_cast (show n ≤ 4 * (linfDist x u + 1) by omega)
    have h := annulusTau_one_sided_shell_le hd C hC panis heart x u hx hu
    rw [hxN', sub_self, add_zero, mul_one] at h
    exact h.trans (div_pow_le_of_le_mul hJ (by positivity) hn0 (by norm_num) hle _)

/-- The actual annulus also inherits the shifted full-space Green bound. -/
theorem annulusTau_bulk_shell_le {d : ℕ} (hd : 2 ≤ d) (asymp : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q H : Finset (Vertex d)) (u w : Vertex d),
      annulusTau (criticalPoint d) Q H u w ≤ K / ((linfDist u w + 1 : ℕ) : ℝ) ^ (d - 2) := by
  obtain ⟨K, hK, hgreen⟩ := twoPointBound_of_asymptotics hd asymp
  exact ⟨K, hK, fun Q H u w => (restricted_twoPointBound hgreen (heartAnnulus Q H : Set (Vertex d)) u w).2⟩

end NearCritical.Section8
