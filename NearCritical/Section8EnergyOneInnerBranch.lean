module

public import NearCritical.AppendixTwoPointBridge
public import NearCritical.Section8CubeOneSided
public import NearCritical.Section8EnergyMoments
public import NearCritical.Section8F1
public import NearCritical.Section8InnerAnnulusHit
public import NearCritical.Section8PairDiagrams

/-! The inner branch-point contribution in Proposition Ef1. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open MeasureTheory AppendixVariance
open scoped Classical

/-- The `F1` convolution with the actual ERE1 weight and with both variables
in the same retained annulus. -/
theorem annulus_energyOne_convolution_le {d : ℕ} (hd : 5 ≤ d) (G : ℝ) (hG : 0 ≤ G)
    (green : CriticalSupGreenUpper d G) (Q H excluded : Finset (Vertex d))
    (x u : Vertex d) (r : ℕ) (hr : 1 ≤ r) :
    (∑ y ∈ heartAnnulus Q H, energyOneWeight excluded r x y * annulusTau (criticalPoint d) Q H u y) ≤
      (G * ((4 : ℝ) ^ ((d : ℝ) - 2) * (2 + 19 * (2 * (d : ℝ) * 3 ^ (d - 1))))) *
        (max (r : ℝ) (latticeDistance x u)) ^ ((4 : ℝ) - (d : ℝ)) := by
  let D := heartAnnulus Q H
  let τ := annulusTau (criticalPoint d) Q H u
  let w (y : Vertex d) := (max (r : ℝ) (latticeDistance x y)) ^ ((2 : ℤ) - (d : ℤ))
  have heq : (∑ y ∈ D, energyOneWeight excluded r x y * τ y) = ∑ y ∈ D \ excluded, w y * τ y := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ excluded <;> simp [energyOneWeight, w, hy]
  have hsub : D \ excluded ⊆ Q \ excluded := by
    intro y hy
    obtain ⟨hyD, hyex⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr ⟨heartAnnulus_subset Q H hyD, hyex⟩
  rw [heq]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ =>
    mul_nonneg (by dsimp [w]; positivity) (show 0 ≤ τ y from measureReal_nonneg))).trans ?_
  simpa only [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast, w, τ,
    annulusTau, annulusLink] using annulusF1_bound_of_green hd G hG green r hr Q H excluded x u

/-- The inner contribution to the first conditional mean numerator. The
outer boundary point is separated from every branch point by at least `N/2`. -/
theorem energyOne_inner_branch_sum_le {k : ℕ} (hk : 6 ≤ k)
    (C G A : ℝ) (hC : 0 ≤ C) (hG : 0 ≤ G) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C) (green : CriticalSupGreenUpper (k + 1) G)
    (ordinary : OrdinaryArmWindowInput (k + 1) A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N H L : ℕ), 1 ≤ N → 2 * L ≤ N →
      ∀ (excluded : Finset (Vertex (k + 1)))
        (x : Vertex (k + 1)),
      x ∈ heartAnnulus (centeredBox (k + 1) N) (centeredBox (k + 1) H) → latticeDistance 0 x = N →
      ∀ r : ℕ, 1 ≤ r →
      let Q := centeredBox (k + 1) N
      let heart := centeredBox (k + 1) H
      let D := heartAnnulus Q heart
      ∑ u ∈ D ∩ centeredBox (k + 1) L,
        annulusG (criticalPoint (k + 1)) Q heart u * annulusTau (criticalPoint (k + 1)) Q heart u x *
          (∑ y ∈ D, energyOneWeight excluded r x y * annulusTau (criticalPoint (k + 1)) Q heart u y) ≤
        K * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
          ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ))) := by
  let d := k + 1
  let F : ℝ := G * ((4 : ℝ) ^ ((d : ℝ) - 2) * (2 + 19 * (2 * (d : ℝ) * 3 ^ (d - 1))))
  let S : ℝ := (4 * A) * (2 * (d : ℝ) * 3 ^ k)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨(2 * C) * F * S * 4, by positivity, ?_⟩
  intro N H L hN hL excluded x hx hxN r hr Q heart D
  let T := D ∩ centeredBox d L
  let g := annulusG (criticalPoint d) Q heart
  let τ := annulusTau (criticalPoint d) Q heart
  let w := energyOneWeight excluded r x
  let M : ℝ := (N : ℝ) / 2
  have hM : 0 < M := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [M]
    linarith
  have hdR : (7 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 7 ≤ d by dsimp [d]; omega)
  have hτ (u v : Vertex d) : 0 ≤ τ u v := measureReal_nonneg
  have hg (u : Vertex d) : 0 ≤ g u := measureReal_nonneg
  have hlegs (u : Vertex d) (hu : u ∈ T) :
      τ u x * (∑ y ∈ D, w y * τ u y) ≤ ((2 * C) * F) * M ^ ((5 : ℝ) - 2 * (d : ℝ)) := by
    obtain ⟨huD, huL⟩ := Finset.mem_inter.mp hu
    have huNorm : latticeDistance 0 u ≤ (L : ℝ) := by
      rw [← linfDist_cast_eq_latticeDistance]
      rw [← appendix_cube_eq_centeredBox] at huL
      have h := (mem_linfBall_iff_dist (0 : Vertex d) u (Int.natCast_nonneg L)).mp huL
      exact_mod_cast (show linfDist 0 u ≤ L by simpa only [Int.toNat_natCast] using h)
    have hgap : M ≤ latticeDistance x u := by
      have htri := latticeDistance_triangle 0 u x
      rw [hxN, latticeDistance_comm u x] at htri
      have hL' : 2 * (L : ℝ) ≤ N := by exact_mod_cast hL
      dsimp [M]
      linarith
    have h1 := cube_one_sided_connection_le (by omega : 1 ≤ k + 1) C hC panis
      (D : Set (Vertex d)) (heartAnnulus_subset Q heart) x u hx huD
    rw [hxN, sub_self, add_zero, mul_one] at h1
    have hfirst : τ u x ≤ (2 * C) * M ^ ((1 : ℝ) - d) := by
      rw [show τ u x = τ x u from annulusTau_comm _ _ _ _ _]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Real.rpow_le_rpow_of_nonpos hM (hgap.trans (le_max_right _ _)) (by linarith)
    have hsecond : (∑ y ∈ D, w y * τ u y) ≤ F * M ^ ((4 : ℝ) - d) := by
      have h := annulus_energyOne_convolution_le (by dsimp [d]; omega : 5 ≤ d)
        G hG green Q heart excluded x u r hr
      exact h.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hM (hgap.trans (le_max_right _ _)) (by linarith)) hF)
    have hsum0 : 0 ≤ ∑ y ∈ D, w y * τ u y :=
      Finset.sum_nonneg fun y _ => mul_nonneg (energyOneWeight_nonneg _ _ _ _) (hτ u y)
    calc
      _ ≤ ((2 * C) * M ^ ((1 : ℝ) - d)) * (F * M ^ ((4 : ℝ) - d)) :=
        mul_le_mul hfirst hsecond hsum0 (by positivity)
      _ = ((2 * C) * F) * (M ^ ((1 : ℝ) - d) * M ^ ((4 : ℝ) - d)) := by ring
      _ = _ := by rw [← Real.rpow_add hM, show (1 : ℝ) - d + (4 - d) = 5 - 2 * d by ring]
  have hmass : ∑ u ∈ T, g u ≤ S * (2 * (2 * (H : ℝ) + 1) ^ k + 4 * ((L : ℝ) + 1) ^ (k - 1)) :=
    inner_annulus_hit_sum_le (N := N) (H := H) (L := L) (by omega) A hA ordinary
  let J : ℝ := ((2 * C) * F) * M ^ ((5 : ℝ) - 2 * (d : ℝ))
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  change (∑ u ∈ T, g u * τ u x * (∑ y ∈ D, w y * τ u y)) ≤ _
  calc
    _ ≤ ∑ u ∈ T, g u * J := by
      apply Finset.sum_le_sum
      intro u hu
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hlegs u hu) (hg u)
    _ = (∑ u ∈ T, g u) * J := by rw [Finset.sum_mul]
    _ ≤ (S * (2 * (2 * (H : ℝ) + 1) ^ k + 4 * ((L : ℝ) + 1) ^ (k - 1))) * J :=
      mul_le_mul_of_nonneg_right hmass hJ
    _ ≤ (S * (4 * ((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)))) * J := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left _ hS) hJ
      linarith [show 0 ≤ (2 * (H : ℝ) + 1) ^ k by positivity]
    _ = _ := by dsimp [J, M]; ring

end NearCritical.Section8
