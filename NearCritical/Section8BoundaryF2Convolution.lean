module

public import NearCritical.Section8BoundaryRadialMass
public import NearCritical.Section8EnergyMoments
public import NearCritical.Section8EnergyTwoOuterBranch
public import NearCritical.Section8SourceFRD

/-! The global F2 convolution of the boundary weight with the depth kernel. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

/-- The cutoff boundary weight convolved with the shifted two-sided kernel
has the same cutoff power. Both centers may coincide. -/
theorem boundary_frd_convolution_le {k n r : ℕ} (hk : 3 ≤ k) (hr : 1 ≤ r)
    (x u : Vertex (k + 1)) (hx : linfDist 0 x = n) (hu : u ∈ (cube n : Finset (Vertex (k + 1)))) :
    ∑ y ∈ (cubeBoundary n : Finset (Vertex (k + 1))),
      frdKernel r (k - 3) x y *
        (((n - linfDist 0 u + 1 : ℕ) : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (k + 1)) ≤
      (((k : ℝ) + 1) * (2 * (4 * (k : ℝ) * 3 ^ (k - 1))) * (2 : ℝ) ^ (k - 3) +
       ((k : ℝ) + 1) * (2 * (2 * (k : ℝ) * 3 ^ (k - 1))) * (2 : ℝ) ^ (k + 1)) /
        (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (k - 3) := by
  let U : Finset (Vertex (k + 1)) := cubeBoundary n
  let M := max r (linfDist x u + 1)
  let a (y : Vertex (k + 1)) := max r (linfDist x y + 1)
  let l := n - linfDist 0 u + 1
  let f (y : Vertex (k + 1)) := frdKernel r (k - 3) x y
  let g (y : Vertex (k + 1)) : ℝ := (l : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (k + 1)
  let B : ℝ := ((k : ℝ) + 1) * (2 * (4 * (k : ℝ) * 3 ^ (k - 1)))
  let C : ℝ := ((k : ℝ) + 1) * (2 * (2 * (k : ℝ) * 3 ^ (k - 1)))
  let far (y : Vertex (k + 1)) := M ≤ 2 * a y
  have hM : 1 ≤ M := hr.trans (le_max_left _ _)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hl : l ≤ M := by
    have ht := linfDist_triangle 0 u x
    rw [hx, linfDist_comm u x] at ht
    have hm : linfDist x u + 1 ≤ M := le_max_right _ _
    dsimp [l]
    omega
  have hfar : ∑ y ∈ U.filter far, f y * g y ≤ B * (2 : ℝ) ^ (k - 3) / (M : ℝ) ^ (k - 3) := by
    have hsum := boundary_depth_kernel_mass_le (by omega : 1 ≤ k) u hu
    calc
      _ ≤ ∑ y ∈ U.filter far, ((2 : ℝ) ^ (k - 3) / (M : ℝ) ^ (k - 3)) * g y := by
        apply Finset.sum_le_sum
        intro y hy
        have hyf : M ≤ 2 * a y := (Finset.mem_filter.mp hy).2
        have hf : f y ≤ (2 : ℝ) ^ (k - 3) / (M : ℝ) ^ (k - 3) := by
          have ha : (0 : ℝ) < a y := by
            exact_mod_cast (show 0 < a y from lt_of_lt_of_le (by omega : 0 < r) (le_max_left _ _))
          have hma : (M : ℝ) ≤ 2 * (a y : ℝ) := by exact_mod_cast hyf
          have he : (a y : ℝ) = max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ) := by
            dsimp [a]
            rw [Nat.cast_max]
          dsimp [f, frdKernel]
          rw [← he]
          apply (div_le_div_iff₀ (pow_pos ha _) (pow_pos hM0 _)).mpr
          rw [one_mul, ← mul_pow]
          exact pow_le_pow_left₀ hM0.le hma _
        exact mul_le_mul_of_nonneg_right hf (by dsimp [g]; positivity)
      _ = ((2 : ℝ) ^ (k - 3) / (M : ℝ) ^ (k - 3)) * (∑ y ∈ U.filter far, g y) := by rw [Finset.mul_sum]
      _ ≤ ((2 : ℝ) ^ (k - 3) / (M : ℝ) ^ (k - 3)) * B := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun y _ _ => by dsimp [g]; positivity)).trans hsum
      _ = _ := by ring
  have hnear : ∑ y ∈ U.filter (fun y => ¬ far y), f y * g y ≤
      C * (2 : ℝ) ^ (k + 1) / (M : ℝ) ^ (k - 3) := by
    have hgeometry (y : Vertex (k + 1)) (hy : y ∈ U.filter (fun y => ¬ far y)) :
        linfDist x y ≤ M - 1 ∧ M ≤ 2 * (linfDist u y + 1) := by
      have hyf : ¬ M ≤ 2 * a y := (Finset.mem_filter.mp hy).2
      have hxy : linfDist x y + 1 ≤ a y := le_max_right _ _
      have hr' : r ≤ a y := le_max_left _ _
      have hM' : M = linfDist x u + 1 := by
        dsimp [M]
        apply max_eq_right
        by_contra h
        have he : M = r := max_eq_left (by omega)
        omega
      have ht := linfDist_triangle x y u
      rw [linfDist_comm y u] at ht
      omega
    have hmass := boundary_cutoff_mass_in_ball_le (r := r) (R := M - 1) hk x
      (U.filter (fun y => ¬ far y)) (Finset.filter_subset _ _) (fun y hy => (hgeometry y hy).1)
    have hmass' : (∑ y ∈ U.filter (fun y => ¬ far y), f y) ≤ C * (M : ℝ) ^ 3 := by
      have he : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
        exact_mod_cast (show M - 1 + 1 = M by omega)
      rw [he] at hmass
      exact hmass.trans (le_of_eq (by dsimp [C]; ring))
    calc
      _ ≤ ∑ y ∈ U.filter (fun y => ¬ far y), f y * ((2 : ℝ) ^ (k + 1) / (M : ℝ) ^ k) := by
        apply Finset.sum_le_sum
        intro y hy
        have hMy : (M : ℝ) ≤ 2 * ((linfDist u y + 1 : ℕ) : ℝ) := by exact_mod_cast (hgeometry y hy).2
        have hpos : 0 < ((linfDist u y + 1 : ℕ) : ℝ) := by positivity
        have hg : g y ≤ (2 : ℝ) ^ (k + 1) / (M : ℝ) ^ k := by
          calc
            _ ≤ (M : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (k + 1) :=
              div_le_div_of_nonneg_right (by exact_mod_cast hl) (by positivity)
            _ ≤ _ := by
              apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hM0 _)).mpr
              calc
                _ = (M : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
                _ ≤ (2 * ((linfDist u y + 1 : ℕ) : ℝ)) ^ (k + 1) := pow_le_pow_left₀ hM0.le hMy _
                _ = _ := by rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hg (by dsimp [f, frdKernel]; positivity)
      _ = (∑ y ∈ U.filter (fun y => ¬ far y), f y) * ((2 : ℝ) ^ (k + 1) / (M : ℝ) ^ k) := by rw [Finset.sum_mul]
      _ ≤ C * (M : ℝ) ^ 3 * ((2 : ℝ) ^ (k + 1) / (M : ℝ) ^ k) := mul_le_mul_of_nonneg_right hmass' (by positivity)
      _ = _ := by
        have he : (M : ℝ) ^ k = (M : ℝ) ^ (k - 3) * (M : ℝ) ^ 3 := by
          rw [← pow_add, show k - 3 + 3 = k by omega]
        rw [he]
        field_simp [hM0.ne'] <;> ring
  change (∑ y ∈ U, f y * g y) ≤ _
  calc
    _ = (∑ y ∈ U.filter far, f y * g y) + ∑ y ∈ U.filter (fun y => ¬ far y), f y * g y :=
      (Finset.sum_filter_add_sum_filter_not U far (fun y => f y * g y)).symm
    _ ≤ _ := (add_le_add hfar hnear).trans (le_of_eq (by
      dsimp [B, C, M]
      rw [Nat.cast_max]
      ring))

/-- Global F2 bound for the actual annulus connections and the literal ERE2
weight. This supplies the pointwise convolution input in the variance proof. -/
theorem annulus_energyTwo_convolution_le {k : ℕ} (hk : 3 ≤ k) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin (k + 1), SlabBoundarySecondMomentUpper i B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n r : ℕ), 1 ≤ r → ∀ (heart : Finset (Vertex (k + 1))),
      let Q := centeredBox (k + 1) n
      let D := heartAnnulus Q heart
      ∀ x ∈ D, linfDist 0 x = n → ∀ u ∈ D,
      (∑ y ∈ D, energyTwoWeight (cubeBoundary n) r x y * annulusTau (criticalPoint (k + 1)) Q heart u y) ≤
        K / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (k - 3) := by
  obtain ⟨T, hT, hτ⟩ := annulusTau_boundary_two_sided_le (by omega : 1 ≤ k + 1) C A B hC hA hB panis arm second
  let J : ℝ := ((k : ℝ) + 1) * (2 * (4 * (k : ℝ) * 3 ^ (k - 1))) * (2 : ℝ) ^ (k - 3) +
    ((k : ℝ) + 1) * (2 * (2 * (k : ℝ) * 3 ^ (k - 1))) * (2 : ℝ) ^ (k + 1)
  let W : ℝ := T * (2 : ℝ) ^ (k - 3)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨W * J, by positivity, ?_⟩
  intro n r hr heart Q D x _hx hxN u hu
  let E : Finset (Vertex (k + 1)) := cubeBoundary n
  let f (y : Vertex (k + 1)) := frdKernel r (k - 3) x y
  let g (y : Vertex (k + 1)) : ℝ :=
    ((n - linfDist 0 u + 1 : ℕ) : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (k + 1)
  have huQ : u ∈ centeredBox (k + 1) n := heartAnnulus_subset Q heart hu
  have huCube : u ∈ (cube n : Finset (Vertex (k + 1))) := by rwa [appendix_cube_eq_centeredBox]
  have huN : linfDist 0 u ≤ n := by
    have h := (mem_linfBall_iff_dist (0 : Vertex (k + 1)) u (Int.natCast_nonneg n)).mp huCube
    simpa only [Int.toNat_natCast] using h
  have hell : 1 + ((n : ℝ) - latticeDistance 0 u) = ((n - linfDist 0 u + 1 : ℕ) : ℝ) := by
    rw [← linfDist_cast_eq_latticeDistance, Nat.cast_add, Nat.cast_sub huN, Nat.cast_one]
    ring
  have hnum := boundary_frd_convolution_le hk hr x u hxN huCube
  have hterm (y : Vertex (k + 1)) (hy : y ∈ D ∩ E) :
      energyTwoWeight E r x y * annulusTau (criticalPoint (k + 1)) Q heart u y ≤ W * (f y * g y) := by
    obtain ⟨hyD, hyE⟩ := Finset.mem_inter.mp hy
    have hyN : latticeDistance 0 y = n := by
      rw [← linfDist_cast_eq_latticeDistance, (Finset.mem_filter.mp hyE).2]
    have ht := hτ n heart y u hyD hu hyN
    rw [hell, linfDist_comm y u] at ht
    have ht' : annulusTau (criticalPoint (k + 1)) Q heart u y ≤ T * g y := by
      simpa only [g, mul_div_assoc] using ht
    have hw : energyTwoWeight E r x y ≤ (2 : ℝ) ^ (k - 3) * f y := by
      have hexp : (4 : ℤ) - ((k + 1 : ℕ) : ℤ) = -((k - 3 : ℕ) : ℤ) := by omega
      rw [energyTwoWeight, if_pos hyE, hexp, zpow_neg, zpow_natCast, inv_eq_one_div]
      simpa only [f, frdKernel, ← mul_div_assoc, mul_one] using literal_kernel_le hr x y (k - 3)
    exact (mul_le_mul hw ht' measureReal_nonneg (by dsimp [f, frdKernel]; positivity)).trans_eq (by dsimp [W]; ring)
  calc
    _ = ∑ y ∈ D ∩ E, energyTwoWeight E r x y * annulusTau (criticalPoint (k + 1)) Q heart u y := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro y hy hnot
      have hyE : y ∉ E := fun h => hnot (Finset.mem_inter.mpr ⟨hy, h⟩)
      simp [energyTwoWeight, hyE]
    _ ≤ ∑ y ∈ D ∩ E, W * (f y * g y) := Finset.sum_le_sum hterm
    _ ≤ ∑ y ∈ E, W * (f y * g y) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun y _ _ => by dsimp [f, g, frdKernel]; positivity)
    _ = W * (∑ y ∈ E, f y * g y) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hnum hW

end NearCritical.Section8
