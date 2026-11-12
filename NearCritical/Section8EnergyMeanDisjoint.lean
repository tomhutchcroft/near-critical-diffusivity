module

public import NearCritical.Section8EnergyMoments
public import NearCritical.Section8FiveDiagrams
public import NearCritical.Section8HeartOuterProfile
public import NearCritical.Section8WeightedMass

/-! The outer-annulus hitting profile and the disjoint-path contribution to
the first conditional regularity-energy mean. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private lemma centeredBox_norm_le {d N : ℕ} {y : Vertex d}
    (hy : y ∈ centeredBox d N) : latticeDistance 0 y ≤ (N : ℝ) := by
  apply (dist_pi_le_iff (Nat.cast_nonneg N)).mpr
  intro i
  have hc := mem_centeredBox.mp hy i
  have hcoord : |(y i : ℝ)| ≤ (N : ℝ) :=
    abs_le.mpr ⟨by exact_mod_cast hc.1, by exact_mod_cast hc.2⟩
  simpa [vertexReal, Real.dist_eq] using hcoord

/-- The heart hit at an outer-annulus point retains its nearest-face depth.
The coefficient is uniform in the cube radius and the heart ratio. -/
theorem cube_outer_annulusG_scaled {d N L H : ℕ} (hd : 4 ≤ d)
    (hH : 1 ≤ H) (hLN : L ≤ N) (hgap : (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H)
    (ρ : ℝ) (hround : (H : ℝ) ≤ ρ * N) (heart : Finset (Vertex d))
    (hheart : heart ⊆ centeredBox d H) (y : Vertex d)
    (hy : y ∈ heartAnnulus (centeredBox d N) heart) (hyL : y ∉ centeredBox d L)
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B) :
    annulusG (criticalPoint d) (centeredBox d N) heart y ≤
      ((2 * C) * 4 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1))) *
        ρ ^ (d - 4) / (N : ℝ) ^ 3 * (1 + ((N : ℝ) - latticeDistance 0 y)) := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hN : (0 : ℝ) < N := by linarith
  have hRL : 2 * H < L := by
    exact_mod_cast (show 2 * (H : ℝ) < L by linarith)
  have hHQ : heart ⊆ centeredBox d N := by
    intro v hv
    apply mem_centeredBox.mpr
    intro i
    have hc := mem_centeredBox.mp (hheart hv) i
    constructor <;> omega
  have hyQ := heartAnnulus_subset _ _ hy
  have hface : ∃ (j : Fin d) (b : Bool),
      coordinateDepth j (if b then -(N : ℤ) else (N : ℤ)) b y =
        (N : ℝ) - latticeDistance 0 y := by
    have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
      (fun k : Fin d => |(y k : ℝ)|) hne
    have hnorm : |(y j : ℝ)| = latticeDistance 0 y := by
      apply le_antisymm
      · simpa [latticeDistance, vertexReal, Real.dist_eq] using
          dist_le_pi_dist (vertexReal (0 : Vertex d)) (vertexReal y) j
      · apply (dist_pi_le_iff (abs_nonneg (y j : ℝ))).mpr
        intro k
        simpa [vertexReal, Real.dist_eq] using hj k (Finset.mem_univ k)
    by_cases hj0 : 0 ≤ (y j : ℝ)
    · exact ⟨j, false, by simp [coordinateDepth, ← hnorm, abs_of_nonneg hj0]⟩
    · refine ⟨j, true, ?_⟩
      simp [coordinateDepth, ← hnorm, abs_of_neg (lt_of_not_ge hj0), add_comm]
  obtain ⟨j, b, hb⟩ := hface
  have hprob := cube_outer_heart_probability_le (by omega : 1 ≤ d)
    (by omega : H < 2 * H) hRL hLN heart hheart y hyQ hyL j b C B hC hB panis arm
  rw [hb, show 2 * H - H = H by omega] at hprob
  have hevent : heartEvent (centeredBox d N) heart y =
      {ω | y ∈ heartClusterUnion ω (centeredBox d N) heart} := by
    ext ω
    exact heartEvent_iff_union_member _ _ hHQ y ω
  rw [annulusG, annulusHit, ← heart_probability_eq_annulus _ _ _ y hy, hevent]
  have hexp : (1 : ℝ) - (d : ℝ) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    ring
  have hpower : (max 1 ((L : ℝ) - ((2 * H : ℕ) : ℝ))) ^ ((1 : ℝ) - d) ≤
      (4 : ℝ) ^ (d - 1) / (N : ℝ) ^ (d - 1) := by
    have hle : (N : ℝ) / 4 ≤ max 1 ((L : ℝ) - ((2 * H : ℕ) : ℝ)) := by
      push_cast
      exact hgap.trans (le_max_right _ _)
    calc
      _ ≤ ((N : ℝ) / 4) ^ ((1 : ℝ) - d) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle
          (by rw [hexp]; exact neg_nonpos.mpr (Nat.cast_nonneg _))
      _ = _ := by
        rw [hexp, Real.rpow_neg (by positivity), Real.rpow_natCast, div_pow, inv_div]
  have hcard : ((2 * d * (2 * (2 * H) + 1) ^ (d - 1) : ℕ) : ℝ) ≤
      (2 * (d : ℝ) * 5 ^ (d - 1)) * (H : ℝ) ^ (d - 1) := by
    calc
      _ = (2 * (d : ℝ)) * (4 * (H : ℝ) + 1) ^ (d - 1) := by push_cast <;> ring
      _ ≤ (2 * (d : ℝ)) * (5 * (H : ℝ)) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  let depth : ℝ := 1 + ((N : ℝ) - latticeDistance 0 y)
  have hdepth0 : 0 ≤ depth := by dsimp [depth]; linarith [centeredBox_norm_le hyQ]
  have he : d - 1 = (d - 4) + 3 := by omega
  have hscale : (H : ℝ) ^ (d - 1) / ((H : ℝ) ^ 3 * (N : ℝ) ^ (d - 1)) ≤
      ρ ^ (d - 4) / (N : ℝ) ^ 3 := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg H) hround (d - 4)
    rw [mul_pow] at hp
    rw [he, pow_add (H : ℝ), pow_add (N : ℝ)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      _ ≤ (ρ ^ (d - 4) * (N : ℝ) ^ (d - 4)) * ((H : ℝ) ^ 3 * (N : ℝ) ^ 3) := by
        convert mul_le_mul_of_nonneg_right hp
          (show 0 ≤ (H : ℝ) ^ 3 * (N : ℝ) ^ 3 by positivity) using 1 <;> ring
      _ = _ := by ring
  calc
    _ ≤ _ := hprob
    _ ≤ (((2 * C) * depth * (4 ^ (d - 1) / (N : ℝ) ^ (d - 1))) *
          (B / (H : ℝ) ^ 3)) * ((2 * (d : ℝ) * 5 ^ (d - 1)) * (H : ℝ) ^ (d - 1)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower (by positivity)) (by positivity))
        hcard (by positivity) (by positivity)
    _ = (((2 * C) * 4 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1))) * depth) *
        ((H : ℝ) ^ (d - 1) / ((H : ℝ) ^ 3 * (N : ℝ) ^ (d - 1))) := by ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hscale (show
        0 ≤ ((2 * C) * 4 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1))) * depth by positivity) using 1
      ring

/-- The disjoint-path term after cancellation of the conditioning probability
is bounded by a constant times the heart ratio to the power `d - 4`. -/
theorem energyOne_disjoint_sum_le {d N L H : ℕ} (hd : 4 ≤ d)
    (hH : 1 ≤ H) (hLN : L ≤ N) (hgap : (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hround : (H : ℝ) ≤ ρ * N)
    (heart excluded : Finset (Vertex d)) (hheart : heart ⊆ centeredBox d H)
    (hex : centeredBox d L ⊆ excluded) (x : Vertex d) (hx : latticeDistance 0 x = N)
    (r : ℕ) (hr : 1 ≤ r) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C) (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B) :
    ∑ y ∈ heartAnnulus (centeredBox d N) heart,
        energyOneWeight excluded r x y * annulusG (criticalPoint d) (centeredBox d N) heart y ≤
      (((2 * C) * 4 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1))) *
        (1 + 2 * (d : ℝ) * 3 ^ (d - 1)) * 27) * ρ ^ (d - 4) := by
  let K : ℝ := (2 * C) * 4 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1))
  let A : ℝ := 1 + 2 * (d : ℝ) * 3 ^ (d - 1)
  let s := heartAnnulus (centeredBox d N) heart
  let ell (y : Vertex d) := (N : ℝ) - latticeDistance 0 y
  let w (y : Vertex d) := (max (r : ℝ) (latticeDistance x y)) ^ ((2 : ℤ) - (d : ℤ))
  have hN : 1 ≤ N := by
    have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
    exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hdepth (y : Vertex d) (hy : y ∈ s) : 0 ≤ ell y :=
    sub_nonneg.mpr (centeredBox_norm_le (heartAnnulus_subset _ _ hy))
  have hR (y : Vertex d) (hy : y ∈ s) : latticeDistance x y ≤ ((2 * N : ℕ) : ℝ) := by
    have h := latticeDistance_triangle x 0 y
    rw [latticeDistance_comm x 0, hx] at h
    push_cast
    linarith [centeredBox_norm_le (heartAnnulus_subset _ _ hy)]
  have hD (y : Vertex d) (_hy : y ∈ s) : ell y ≤ latticeDistance x y := by
    have h := latticeDistance_triangle 0 y x
    rw [hx, latticeDistance_comm y x] at h
    dsimp [ell]
    linarith
  have hmass := sum_truncated_green_depth_le (by omega : 2 ≤ d) r hr (2 * N) s x ell hR hD
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hsize : (((2 * N : ℕ) : ℝ) + 1) ^ 3 ≤ 27 * (N : ℝ) ^ 3 := by
    push_cast
    calc
      _ ≤ (3 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by ring
  change (∑ y ∈ s, energyOneWeight excluded r x y *
    annulusG (criticalPoint d) (centeredBox d N) heart y) ≤ (K * A * 27) * ρ ^ (d - 4)
  calc
    _ ≤ ∑ y ∈ s, (K * ρ ^ (d - 4) / (N : ℝ) ^ 3) * (w y * (1 + ell y)) := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hey : y ∈ excluded
      · rw [energyOneWeight, if_neg (fun hn => hn hey), zero_mul]
        have := hdepth y hy
        dsimp [w]
        positivity
      · rw [energyOneWeight, if_pos hey]
        have hp := cube_outer_annulusG_scaled hd hH hLN hgap ρ hround heart hheart y hy
          (fun hyL => hey (hex hyL)) C B hC hB panis arm
        change w y * _ ≤ _
        calc
          _ ≤ w y * ((K * ρ ^ (d - 4) / (N : ℝ) ^ 3) * (1 + ell y)) :=
            mul_le_mul_of_nonneg_left hp (by dsimp [w]; positivity)
          _ = _ := by ring
    _ = (K * ρ ^ (d - 4) / (N : ℝ) ^ 3) * (∑ y ∈ s, w y * (1 + ell y)) := by
      rw [Finset.mul_sum]
    _ ≤ (K * ρ ^ (d - 4) / (N : ℝ) ^ 3) * (A * ((((2 * N : ℕ) : ℝ) + 1) ^ 3)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (K * ρ ^ (d - 4) / (N : ℝ) ^ 3) * (A * (27 * (N : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsize hA) (by positivity)
    _ = _ := by field_simp <;> ring

end NearCritical.Section8
