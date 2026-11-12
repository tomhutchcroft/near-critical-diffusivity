module

public import NearCritical.Section8BoundaryBranchConvolution
public import NearCritical.Section8CubeOneSided
public import NearCritical.Section8EnergyMeanDisjoint
public import NearCritical.Section8PairDiagrams
public import NearCritical.Section8TwoSidedDistance
public import NearCritical.AppendixTwoPointBridge

/-! Actual annulus two-point legs and the outer branch convolution of Ef2. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open MeasureTheory AppendixVariance
open scoped Classical

private lemma inverse_power_le_of_le_twice {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ 2 * a) (d : ℕ) : 1 / a ^ d ≤ (2 : ℝ) ^ d / b ^ d := by
  apply (div_le_div_iff₀ (pow_pos ha _) (pow_pos hb _)).mpr
  rw [one_mul, ← mul_pow]
  exact pow_le_pow_left₀ hb.le hab _

/-- A two-sided bound for the actual retained annulus, with a boundary
endpoint and a branch point at its nearest-face depth. -/
theorem annulusTau_boundary_two_sided_le {d : ℕ} (hd : 1 ≤ d) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (heart : Finset (Vertex d))
      (x u : Vertex d),
      x ∈ heartAnnulus (centeredBox d N) heart → u ∈ heartAnnulus (centeredBox d N) heart →
      latticeDistance 0 x = N →
      annulusTau (criticalPoint d) (centeredBox d N) heart u x ≤
        K * (1 + ((N : ℝ) - latticeDistance 0 u)) / ((linfDist x u + 1 : ℕ) : ℝ) ^ d := by
  let F : ℝ := (4 * C + ((2 * (d : ℝ)) * (4 * C * (A + B) * (9 : ℝ) ^ (d - 1)) * (2 * C)) *
    (4 : ℝ) ^ d)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨F * (2 : ℝ) ^ d, by positivity, ?_⟩
  intro N heart x u hx hu hxN
  let Q := centeredBox d N
  let D := heartAnnulus Q heart
  have hDQ := heartAnnulus_subset Q heart
  obtain ⟨ix, wx, sx, hxHs, hxDepth⟩ := cube_nearest_coordinate_halfSpace hd x (hDQ hx)
  obtain ⟨iu, wu, su, huHs, huDepth⟩ := cube_nearest_coordinate_halfSpace hd u (hDQ hu)
  have h := two_halfspaces_connection_le_distance hd C A B hC hA hB panis arm second
    D x u hx hu ix iu wx wu sx su (fun _ hz => hxHs (hDQ hz)) (fun _ hz => huHs (hDQ hz))
  rw [hxDepth, huDepth, hxN, sub_self, add_zero, mul_one] at h
  have hdepth : 0 ≤ (N : ℝ) - latticeDistance 0 u := by
    rw [← huDepth]
    exact huHs (hDQ hu)
  let M := max 1 (latticeDistance x u)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hr : ((linfDist x u + 1 : ℕ) : ℝ) ≤ 2 * M := by
    rw [Nat.cast_add, Nat.cast_one, linfDist_cast_eq_latticeDistance]
    have h₁ : 1 ≤ M := le_max_left _ _
    have h₂ : latticeDistance x u ≤ M := le_max_right _ _
    linarith
  rw [annulusTau_comm _ _ _ u x]
  refine h.trans ?_
  change F * (1 + ((N : ℝ) - latticeDistance 0 u)) * M ^ (-(d : ℝ)) ≤ _
  rw [Real.rpow_neg hM.le, Real.rpow_natCast, inv_eq_one_div]
  have hb := inverse_power_le_of_le_twice hM (by positivity) hr d
  calc
    _ ≤ (F * (1 + ((N : ℝ) - latticeDistance 0 u))) *
        ((2 : ℝ) ^ d / ((linfDist x u + 1 : ℕ) : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The outer part of the actual annulus tree sum at a fixed pair of
boundary points. Its kernel decays as `(1 + |x-y|)^(3-d)`. -/
theorem energyTwo_outer_branch_pointwise_le {d : ℕ} (hd : 7 ≤ d) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N L H : ℕ), 1 ≤ H → L ≤ N →
      (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H → ∀ ρ : ℝ, 0 ≤ ρ → (H : ℝ) ≤ ρ * N →
      ∀ (heart : Finset (Vertex d)), heart ⊆ centeredBox d H →
      let Q := centeredBox d N
      let D := heartAnnulus Q heart
      ∀ x ∈ D, ∀ y ∈ D, latticeDistance 0 x = N → latticeDistance 0 y = N →
      ∑ u ∈ D.filter (fun u => u ∉ centeredBox d L),
        annulusG (criticalPoint d) Q heart u * annulusTau (criticalPoint d) Q heart u x *
          annulusTau (criticalPoint d) Q heart u y ≤
        (K * ρ ^ (d - 4) / (N : ℝ) ^ 3) / ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 3) := by
  obtain ⟨T, hT, hτ⟩ := annulusTau_boundary_two_sided_le (by omega : 1 ≤ d) C A B
    hC hA hB panis arm second
  let F : ℝ := (2 * C) * 4 ^ (d - 1) * A * (2 * (d : ℝ) * 5 ^ (d - 1))
  let V : ℝ := (2 : ℝ) ^ d * (2 * (2 * (d : ℝ) * 3 ^ (d - 1))) *
    ((((d - 3 : ℕ) : ℝ) + 1) / ((d - 3 : ℕ) : ℝ))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  refine ⟨F * T ^ 2 * V, by positivity, ?_⟩
  intro N L H hH hLN hgap ρ hρ hround heart hheart Q D x hx y hy hxN hyN
  let U := D.filter (fun u => u ∉ centeredBox d L)
  let depth (u : Vertex d) := 1 + ((N : ℝ) - latticeDistance 0 u)
  let P : ℝ := F * ρ ^ (d - 4) / (N : ℝ) ^ 3
  let s (v u : Vertex d) : ℝ := (linfDist v u + 1 : ℕ)
  let g := annulusG (criticalPoint d) Q heart
  let τ := annulusTau (criticalPoint d) Q heart
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hdepth (u : Vertex d) (hu : u ∈ U) : 0 ≤ depth u := by
    have huQ := heartAnnulus_subset Q heart (Finset.mem_filter.mp hu).1
    obtain ⟨i, w, b, hs, hdep⟩ := cube_nearest_coordinate_halfSpace (by omega : 1 ≤ d) u huQ
    have h : 0 ≤ coordinateDepth i w b u := hs huQ
    dsimp [depth]
    linarith
  have hdist (v u : Vertex d) (hv : latticeDistance 0 v = N) : depth u ≤ s v u := by
    have h := latticeDistance_triangle 0 u v
    rw [hv, latticeDistance_comm u v] at h
    dsimp [depth, s]
    rw [Nat.cast_add, Nat.cast_one, linfDist_cast_eq_latticeDistance]
    linarith
  have hterm (u : Vertex d) (hu : u ∈ U) : g u * τ u x * τ u y ≤
      (P * T ^ 2) * (depth u ^ 3 / (s x u ^ d * s y u ^ d)) := by
    obtain ⟨huD, huL⟩ := Finset.mem_filter.mp hu
    have hg : g u ≤ P * depth u := cube_outer_annulusG_scaled (by omega : 4 ≤ d)
      hH hLN hgap ρ hround heart hheart u huD huL C A hC hA panis arm
    have h₁ := hτ N heart x u hx huD hxN
    have h₂ := hτ N heart y u hy huD hyN
    have hd0 := hdepth u hu
    calc
      _ ≤ (P * depth u * (T * depth u / s x u ^ d)) * (T * depth u / s y u ^ d) := by
        apply mul_le_mul _ h₂ (show 0 ≤ τ u y from measureReal_nonneg) (by positivity)
        exact mul_le_mul hg h₁ (show 0 ≤ τ u x from measureReal_nonneg) (by positivity)
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  change (∑ u ∈ U, g u * τ u x * τ u y) ≤ _
  calc
    _ ≤ ∑ u ∈ U, (P * T ^ 2) * (depth u ^ 3 / (s x u ^ d * s y u ^ d)) := Finset.sum_le_sum hterm
    _ = (P * T ^ 2) * (∑ u ∈ U, depth u ^ 3 / (s x u ^ d * s y u ^ d)) := by rw [Finset.mul_sum]
    _ ≤ (P * T ^ 2) * (V / s x y ^ (d - 3)) :=
      mul_le_mul_of_nonneg_left (boundary_branch_convolution_le (by omega) x y U depth hdepth
        (fun u _ => hdist x u hxN) (fun u _ => hdist y u hyN)) (by positivity)
    _ = _ := by dsimp [P, s]; ring

end NearCritical.Section8
