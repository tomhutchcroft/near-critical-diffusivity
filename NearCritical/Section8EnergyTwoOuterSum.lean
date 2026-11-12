module

public import NearCritical.Section8EnergyMoments
public import NearCritical.Section8EnergyTwoOuterBranch
public import NearCritical.Section8SourceFRD

/-! Summing the actual outer branch-point contribution in Proposition Ef2. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open MeasureTheory AppendixVariance
open scoped Classical

/-- The ERE2 outer branch contribution has the heart-hitting prefactor and
the cutoff decay `r^(6-d)`. The sum uses the full boundary weight. -/
theorem energyTwo_outer_branch_sum_le {k : ℕ} (hk : 6 ≤ k) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin (k + 1), SlabBoundarySecondMomentUpper i B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N L H : ℕ), 1 ≤ H → L ≤ N →
      (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H → ∀ ρ : ℝ, 0 ≤ ρ → (H : ℝ) ≤ ρ * N →
      ∀ (heart : Finset (Vertex (k + 1))), heart ⊆ centeredBox (k + 1) H →
      let Q := centeredBox (k + 1) N
      let D := heartAnnulus Q heart
      ∀ x ∈ D, latticeDistance 0 x = N → ∀ r : ℕ, 1 ≤ r →
      ∑ u ∈ D.filter (fun u => u ∉ centeredBox (k + 1) L),
        annulusG (criticalPoint (k + 1)) Q heart u * annulusTau (criticalPoint (k + 1)) Q heart u x *
          (∑ y ∈ D, energyTwoWeight (cubeBoundary N) r x y * annulusTau (criticalPoint (k + 1)) Q heart u y) ≤
        K * ρ ^ (k - 3) / (N : ℝ) ^ 3 / (r : ℝ) ^ (k - 5) := by
  obtain ⟨J, hJ, hpoint⟩ := energyTwo_outer_branch_pointwise_le (by omega : 7 ≤ k + 1)
    C A B hC hA hB panis arm second
  let F : ℝ := ((k : ℝ) + 1) * (2 * (2 * (k : ℝ) * 3 ^ (k - 1) *
    ((((k - 5 : ℕ) : ℝ) + 1) / ((k - 5 : ℕ) : ℝ))))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨J * (2 : ℝ) ^ (k - 3) * F, by positivity, ?_⟩
  intro N L H hH hLN hgap ρ hρ hround heart hheart Q D x hx hxN r hr
  let U := D.filter (fun u => u ∉ centeredBox (k + 1) L)
  let E : Finset (Vertex (k + 1)) := cubeBoundary N
  let w := energyTwoWeight E r x
  let τ := annulusTau (criticalPoint (k + 1)) Q heart
  let g := annulusG (criticalPoint (k + 1)) Q heart
  let tree (y : Vertex (k + 1)) := ∑ u ∈ U, g u * τ u x * τ u y
  let P : ℝ := J * ρ ^ (k - 3) / (N : ℝ) ^ 3
  let a (y : Vertex (k + 1)) : ℝ := (linfDist x y + 1 : ℕ)
  let v (y : Vertex (k + 1)) : ℝ := 1 / (a y ^ (k - 2) * (max (r : ℝ) (a y)) ^ (k - 3))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hv (y : Vertex (k + 1)) : 0 ≤ v y := by dsimp [v, a]; positivity
  have hxQ : x ∈ (cube N : Finset (Vertex (k + 1))) := by
    rw [appendix_cube_eq_centeredBox]
    exact heartAnnulus_subset Q heart hx
  have hsum : ∑ y ∈ E, v y ≤ F / (r : ℝ) ^ (k - 5) := by
    have h := boundary_branch_radial_sum_le hk hr x hxQ
    refine h.trans (le_of_eq ?_)
    dsimp [F]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hterm (y : Vertex (k + 1)) (hy : y ∈ D ∩ E) :
      w y * tree y ≤ (P * (2 : ℝ) ^ (k - 3)) * v y := by
    obtain ⟨hyD, hyE⟩ := Finset.mem_inter.mp hy
    have hyN : latticeDistance 0 y = N := by
      rw [← linfDist_cast_eq_latticeDistance, (Finset.mem_filter.mp hyE).2]
    have hb : tree y ≤ P / a y ^ (k - 2) := by
      simpa only [tree, U, g, τ, P, a, show k + 1 - 4 = k - 3 by omega,
        show k + 1 - 3 = k - 2 by omega] using hpoint N L H hH hLN hgap ρ hρ hround heart hheart
          x hx y hyD hxN hyN
    have hw : w y ≤ (2 : ℝ) ^ (k - 3) / (max (r : ℝ) (a y)) ^ (k - 3) := by
      have hexp : (4 : ℤ) - ((k + 1 : ℕ) : ℤ) = -((k - 3 : ℕ) : ℤ) := by omega
      dsimp only [w]
      rw [energyTwoWeight, if_pos hyE, hexp, zpow_neg, zpow_natCast, inv_eq_one_div]
      exact literal_kernel_le hr x y (k - 3)
    have ht0 : 0 ≤ tree y := Finset.sum_nonneg fun u _ =>
      mul_nonneg (mul_nonneg (show 0 ≤ g u from measureReal_nonneg)
        (show 0 ≤ τ u x from measureReal_nonneg)) (show 0 ≤ τ u y from measureReal_nonneg)
    calc
      _ ≤ ((2 : ℝ) ^ (k - 3) / (max (r : ℝ) (a y)) ^ (k - 3)) * (P / a y ^ (k - 2)) :=
        mul_le_mul hw hb ht0 (by positivity)
      _ = _ := by dsimp [v]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  change (∑ u ∈ U, g u * τ u x * (∑ y ∈ D, w y * τ u y)) ≤ _
  calc
    _ = ∑ y ∈ D, w y * tree y := by
      simp only [tree, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ y ∈ D ∩ E, w y * tree y := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro y hy hnot
      have hyE : y ∉ E := fun h => hnot (Finset.mem_inter.mpr ⟨hy, h⟩)
      simp [w, energyTwoWeight, hyE]
    _ ≤ ∑ y ∈ D ∩ E, (P * (2 : ℝ) ^ (k - 3)) * v y := Finset.sum_le_sum hterm
    _ ≤ ∑ y ∈ E, (P * (2 : ℝ) ^ (k - 3)) * v y :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun y _ _ => mul_nonneg (by positivity) (hv y))
    _ = (P * (2 : ℝ) ^ (k - 3)) * (∑ y ∈ E, v y) := by rw [Finset.mul_sum]
    _ ≤ (P * (2 : ℝ) ^ (k - 3)) * (F / (r : ℝ) ^ (k - 5)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [P]; ring

end NearCritical.Section8
