module

public import NearCritical.Section8CubeOneSided
public import NearCritical.Section8EnergyKernelIdentity
public import NearCritical.Section8InnerAnnulusHit
public import NearCritical.Section8PairDiagrams
public import NearCritical.Section8SourceFRD

/-! The inner branch-point contribution in Proposition Ef2. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

/-- Both boundary-to-branch legs in the inner ERE2 term have length at least
`N/2`. The remaining boundary weight has cubic mass, including the diagonal. -/
theorem energyTwo_inner_branch_sum_le {k : ℕ} (hk : 6 ≤ k)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C) (ordinary : OrdinaryArmWindowInput (k + 1) A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N H L : ℕ), 1 ≤ N → 2 * L ≤ N →
      ∀ x ∈ heartAnnulus (centeredBox (k + 1) N) (centeredBox (k + 1) H),
      latticeDistance 0 x = N → ∀ r : ℕ, 1 ≤ r →
      let Q := centeredBox (k + 1) N
      let heart := centeredBox (k + 1) H
      let D := heartAnnulus Q heart
      ∑ u ∈ D ∩ centeredBox (k + 1) L,
        annulusG (criticalPoint (k + 1)) Q heart u * annulusTau (criticalPoint (k + 1)) Q heart u x *
          (∑ y ∈ D, energyTwoWeight (cubeBoundary N) r x y * annulusTau (criticalPoint (k + 1)) Q heart u y) ≤
        K * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
          ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ))) := by
  let d := k + 1
  let B : ℝ := 27 * (2 : ℝ) ^ (k - 3) * (((k : ℝ) + 1) * (4 * (k : ℝ) * 3 ^ (k - 1)))
  let S : ℝ := (4 * A) * (2 * (d : ℝ) * 3 ^ k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨(2 * C) ^ 2 * B * S * 32, by positivity, ?_⟩
  intro N H L hN hL x hx hxN r hr Q heart D
  let T := D ∩ centeredBox d L
  let g := annulusG (criticalPoint d) Q heart
  let τ := annulusTau (criticalPoint d) Q heart
  let w := energyTwoWeight (cubeBoundary N) r x
  let M : ℝ := (N : ℝ) / 2
  let J : ℝ := (2 * C) * M ^ ((1 : ℝ) - (d : ℝ))
  have hM : 0 < M := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [M]
    linarith
  have hdR : (7 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 7 ≤ d by dsimp [d]; omega)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hg (u : Vertex d) : 0 ≤ g u := measureReal_nonneg
  have hleg (u y : Vertex d) (hu : u ∈ T) (hy : y ∈ D) (hyN : latticeDistance 0 y = N) :
      τ u y ≤ J := by
    obtain ⟨huD, huL⟩ := Finset.mem_inter.mp hu
    have huNorm : latticeDistance 0 u ≤ (L : ℝ) := by
      rw [← linfDist_cast_eq_latticeDistance]
      rw [← appendix_cube_eq_centeredBox] at huL
      have h := (mem_linfBall_iff_dist (0 : Vertex d) u (Int.natCast_nonneg L)).mp huL
      exact_mod_cast (show linfDist 0 u ≤ L by simpa only [Int.toNat_natCast] using h)
    have hgap : M ≤ latticeDistance y u := by
      have htri := latticeDistance_triangle 0 u y
      rw [hyN, latticeDistance_comm u y] at htri
      have hL' : 2 * (L : ℝ) ≤ N := by exact_mod_cast hL
      dsimp [M]
      linarith
    have h := cube_one_sided_connection_le (by omega : 1 ≤ k + 1) C hC panis
      (D : Set (Vertex d)) (heartAnnulus_subset Q heart) y u hy huD
    rw [hyN, sub_self, add_zero, mul_one] at h
    rw [show τ u y = τ y u from annulusTau_comm _ _ _ _ _]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_nonpos hM (hgap.trans (le_max_right _ _)) (by linarith)
  have hmassQ : ∑ y ∈ Q, w y ≤ B * (N : ℝ) ^ 3 := by
    have heq := energyTwoWeight_sum_eq_literal (n := N) (by omega : 4 ≤ k + 1) r x (fun _ => 1)
    simp only [mul_one, show k + 1 - 4 = k - 3 by omega] at heq
    have hxQ := heartAnnulus_subset Q heart hx
    change (∑ y ∈ centeredBox (k + 1) N, energyTwoWeight (cubeBoundary N) r x y) ≤ _
    rw [← appendix_cube_eq_centeredBox (k + 1) N, heq]
    change x ∈ centeredBox (k + 1) N at hxQ
    rw [← appendix_cube_eq_centeredBox (k + 1) N] at hxQ
    exact literal_boundary_mass (by omega) hN hr x hxQ
  have hmassD : ∑ y ∈ D, w y ≤ B * (N : ℝ) ^ 3 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (heartAnnulus_subset Q heart)
      (fun y _ _ => energyTwoWeight_nonneg _ _ _ y)).trans hmassQ
  have hbound (u : Vertex d) (hu : u ∈ T) : (∑ y ∈ D, w y * τ u y) ≤ (B * (N : ℝ) ^ 3) * J := by
    calc
      _ ≤ ∑ y ∈ D, w y * J := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hyb : y ∈ (cubeBoundary N : Finset (Vertex d))
        · have hyN : latticeDistance 0 y = N := by
            rw [← linfDist_cast_eq_latticeDistance, (Finset.mem_filter.mp hyb).2]
          exact mul_le_mul_of_nonneg_left (hleg u y hu hy hyN) (energyTwoWeight_nonneg _ _ _ _)
        · simp [w, energyTwoWeight, hyb]
      _ = (∑ y ∈ D, w y) * J := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hmassD hJ
  have hmass : ∑ u ∈ T, g u ≤ S * (2 * (2 * (H : ℝ) + 1) ^ k + 4 * ((L : ℝ) + 1) ^ (k - 1)) :=
    inner_annulus_hit_sum_le (N := N) (H := H) (L := L) (by omega) A hA ordinary
  have hscale : J * ((B * (N : ℝ) ^ 3) * J) =
      ((2 * C) ^ 2 * B * 8) * M ^ ((5 : ℝ) - 2 * (d : ℝ)) := by
    have hcube : (N : ℝ) ^ 3 = 8 * M ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
      dsimp [M]
      ring
    rw [hcube]
    dsimp [J]
    calc
      _ = ((2 * C) ^ 2 * B * 8) *
          (M ^ ((1 : ℝ) - (d : ℝ)) * M ^ ((1 : ℝ) - (d : ℝ)) * M ^ (3 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hM, ← Real.rpow_add hM,
          show (1 : ℝ) - (d : ℝ) + (1 - (d : ℝ)) + 3 = 5 - 2 * (d : ℝ) by ring]
  change (∑ u ∈ T, g u * τ u x * (∑ y ∈ D, w y * τ u y)) ≤ _
  calc
    _ ≤ ∑ u ∈ T, g u * (J * ((B * (N : ℝ) ^ 3) * J)) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hg u)
      exact mul_le_mul (hleg u x hu hx hxN) (hbound u hu)
        (Finset.sum_nonneg fun y _ => mul_nonneg (energyTwoWeight_nonneg _ _ _ _)
          (show 0 ≤ τ u y from measureReal_nonneg)) hJ
    _ = (∑ u ∈ T, g u) * (J * ((B * (N : ℝ) ^ 3) * J)) := by rw [Finset.sum_mul]
    _ ≤ (S * (2 * (2 * (H : ℝ) + 1) ^ k + 4 * ((L : ℝ) + 1) ^ (k - 1))) *
        (J * ((B * (N : ℝ) ^ 3) * J)) := mul_le_mul_of_nonneg_right hmass (by positivity)
    _ ≤ (S * (4 * ((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)))) *
        (J * ((B * (N : ℝ) ^ 3) * J)) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left _ hS) (by positivity)
      linarith [show 0 ≤ (2 * (H : ℝ) + 1) ^ k by positivity]
    _ = _ := by rw [hscale]; dsimp [M]; ring

end NearCritical.Section8
