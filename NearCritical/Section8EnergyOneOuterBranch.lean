module

public import NearCritical.Section8CubeOneSided
public import NearCritical.Section8EnergyMeanDisjoint
public import NearCritical.Section8F1
public import NearCritical.Section8PairDiagrams
public import NearCritical.Section10ClusterTranslation

/-! The outer branch-point contribution in Proposition Ef1. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open MeasureTheory
open scoped Classical

/-- The contribution of outer branch points to the numerator of the first
conditional regularity-energy mean. The bound retains the hitting scale and
gains the source factor `r^(6-d)`. -/
theorem energyOne_outer_branch_sum_le {d : ℕ} (hd : 7 ≤ d)
    (C B G : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (panis : PanisHalfSpaceTwoPointUpper d C) (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B)
    (green : CriticalSupGreenUpper d G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N L H : ℕ), 1 ≤ H → L ≤ N →
      (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H →
      ∀ ρ : ℝ, 0 ≤ ρ → (H : ℝ) ≤ ρ * N →
      ∀ (heart excluded : Finset (Vertex d)), heart ⊆ centeredBox d H →
      ∀ x ∈ heartAnnulus (centeredBox d N) heart, latticeDistance 0 x = N →
      ∀ r : ℕ, 1 ≤ r →
      ∑ u ∈ (heartAnnulus (centeredBox d N) heart).filter (fun u => u ∉ centeredBox d L),
        annulusG (criticalPoint d) (centeredBox d N) heart u *
        annulusTau (criticalPoint d) (centeredBox d N) heart u x *
        (∑ y ∈ heartAnnulus (centeredBox d N) heart, energyOneWeight excluded r x y *
          annulusTau (criticalPoint d) (centeredBox d N) heart u y) ≤
      K * ρ ^ (d - 4) / (N : ℝ) ^ 3 * (r : ℝ) ^ ((6 : ℝ) - (d : ℝ)) := by
  let A : ℝ := (2 * C) * 4 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1))
  let F : ℝ := G * ((4 : ℝ) ^ ((d : ℝ) - 2) * (2 + 19 * (2 * (d : ℝ) * 3 ^ (d - 1))))
  let R : ℝ := 1 + 5 * (2 * (d : ℝ) * 3 ^ (d - 1))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨4 * C * A * F * R, by dsimp [R]; positivity, ?_⟩
  intro N L H hH hLN hgap ρ hρ hround heart excluded hheart x hx hxN r hr
  let Q := centeredBox d N
  let D := heartAnnulus Q heart
  let outer := D.filter (fun u => u ∉ centeredBox d L)
  let g := annulusG (criticalPoint d) Q heart
  let τ := annulusTau (criticalPoint d) Q heart
  let w := energyOneWeight excluded r x
  let a (u : Vertex d) := max 1 (latticeDistance x u)
  let b (u : Vertex d) := max (r : ℝ) (latticeDistance x u)
  let P : ℝ := A * ρ ^ (d - 4) / (N : ℝ) ^ 3
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hτ (u v : Vertex d) : 0 ≤ τ u v := measureReal_nonneg
  have hweighted (u : Vertex d) : (∑ y ∈ D, w y * τ u y) ≤ F * b u ^ ((4 : ℝ) - d) := by
    have heq : (∑ y ∈ D, w y * τ u y) =
        ∑ y ∈ D \ excluded,
          (max (r : ℝ) (latticeDistance x y)) ^ ((2 : ℤ) - (d : ℤ)) * τ u y := by
      rw [Finset.sdiff_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ excluded <;> simp [w, energyOneWeight, hy]
    have hsub : D \ excluded ⊆ Q \ excluded := by
      intro y hy
      obtain ⟨hyD, hyex⟩ := Finset.mem_sdiff.mp hy
      exact Finset.mem_sdiff.mpr ⟨heartAnnulus_subset Q heart hyD, hyex⟩
    rw [heq]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ =>
      mul_nonneg (by positivity) (hτ u y))).trans ?_
    have h := annulusF1_bound_of_green (by omega : 5 ≤ d) G hG green r hr Q heart excluded x u
    simpa only [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast, F, b, τ,
      annulusTau, annulusLink, D] using h
  have hproduct (u : Vertex d) (hu : u ∈ outer) :
      g u * τ u x ≤ (4 * C * P) * a u ^ ((2 : ℝ) - d) := by
    obtain ⟨huD, huL⟩ := Finset.mem_filter.mp hu
    have hhit := cube_outer_annulusG_scaled (by omega : 4 ≤ d) hH hLN hgap ρ hround
      heart hheart u huD huL C B hC hB panis arm
    have hconn := cube_one_sided_connection_le (by omega : 1 ≤ d) C hC panis
      (D : Set (Vertex d)) (heartAnnulus_subset Q heart) x u hx huD
    rw [hxN, sub_self, add_zero, mul_one] at hconn
    have hleg : τ u x ≤ (2 * C) * a u ^ ((1 : ℝ) - d) := by
      rw [show τ u x = τ x u from annulusTau_comm _ _ _ _ _]
      exact hconn
    have hdepth : 1 + ((N : ℝ) - latticeDistance 0 u) ≤ 2 * a u := by
      have htri := latticeDistance_triangle 0 u x
      rw [hxN, latticeDistance_comm u x] at htri
      have h₁ : 1 ≤ a u := le_max_left _ _
      have h₂ : latticeDistance x u ≤ a u := le_max_right _ _
      linarith
    have hhit' : g u ≤ P * (2 * a u) :=
      hhit.trans (mul_le_mul_of_nonneg_left hdepth hP)
    have hpos : 0 < a u := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    calc
      _ ≤ (P * (2 * a u)) * ((2 * C) * a u ^ ((1 : ℝ) - d)) :=
        mul_le_mul hhit' hleg (hτ u x) (by positivity)
      _ = (4 * C * P) * (a u ^ (1 : ℝ) * a u ^ ((1 : ℝ) - d)) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [← Real.rpow_add hpos, show (1 : ℝ) + (1 - d) = 2 - d by ring]
  have hradial : (∑ u ∈ outer, a u ^ ((2 : ℝ) - d) * b u ^ ((4 : ℝ) - d)) ≤
      R * (r : ℝ) ^ ((6 : ℝ) - d) := by
    have h := sum_radial_energy_le hd r hr (translateSites (-x) outer)
    rw [Section10.sum_translateSites] at h
    have hdist (u : Vertex d) : latticeDistance 0 (-x + u) = latticeDistance x u := by
      simpa only [neg_add_cancel] using Section10.latticeDistance_translate (-x) x u
    simp only [hdist] at h
    exact h
  change (∑ u ∈ outer, g u * τ u x * (∑ y ∈ D, w y * τ u y)) ≤ _
  calc
    _ ≤ ∑ u ∈ outer, ((4 * C * P) * F) * (a u ^ ((2 : ℝ) - d) * b u ^ ((4 : ℝ) - d)) := by
      apply Finset.sum_le_sum
      intro u hu
      have hh : 0 ≤ ∑ y ∈ D, w y * τ u y := Finset.sum_nonneg fun y _ =>
        mul_nonneg (energyOneWeight_nonneg _ _ _ _) (hτ _ _)
      calc
        _ ≤ ((4 * C * P) * a u ^ ((2 : ℝ) - d)) * (F * b u ^ ((4 : ℝ) - d)) :=
          mul_le_mul (hproduct u hu) (hweighted u) hh (by positivity)
        _ = _ := by ring
    _ = ((4 * C * P) * F) * (∑ u ∈ outer, a u ^ ((2 : ℝ) - d) * b u ^ ((4 : ℝ) - d)) := by
      rw [Finset.mul_sum]
    _ ≤ ((4 * C * P) * F) * (R * (r : ℝ) ^ ((6 : ℝ) - d)) :=
      mul_le_mul_of_nonneg_left hradial (by positivity)
    _ = _ := by dsimp [P]; ring

end NearCritical.Section8
