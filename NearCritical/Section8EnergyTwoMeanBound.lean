module

public import NearCritical.Section8EnergyOneMeanBound
public import NearCritical.Section8EnergyTwoDisjoint
public import NearCritical.Section8EnergyTwoInnerBranch
public import NearCritical.Section8EnergyTwoOuterSum

/-! Assembly of the three contributions to the second conditional energy mean. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

/-- The quantitative Ef2 bound with the finite-scale inner remainder and
the heart-hit lower estimate supplied explicitly. The energy uses the full
boundary, including the diagonal at the marked point. -/
theorem energyTwo_mean_le_of_heart_hit {k : ℕ} (hk : 6 ≤ k)
    (C B E A : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i B)
    (second : ∀ i : Fin (k + 1), SlabBoundarySecondMomentUpper i E)
    (ordinary : OrdinaryArmWindowInput (k + 1) A) :
    ∃ Kd Ki Ko : ℝ, 0 ≤ Kd ∧ 0 ≤ Ki ∧ 0 ≤ Ko ∧
      ∀ (N L H : ℕ), 1 ≤ N → 1 ≤ H → 2 * L ≤ N → H ≤ L →
      (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H →
      ∀ ρ : ℝ, 0 < ρ → (H : ℝ) ≤ ρ * N →
      let Q := centeredBox (k + 1) N
      let heart := centeredBox (k + 1) H
      ∀ x ∈ heartAnnulus Q heart, latticeDistance 0 x = N →
      ∀ (r : ℕ), 1 ≤ r → ∀ a : ℝ, 0 < a →
      a * ρ ^ (k - 3) / (N : ℝ) ^ 3 ≤ annulusG (criticalPoint (k + 1)) Q heart x →
      heartConditionalMean (criticalPoint (k + 1)) Q heart (fun U => regularityEnergyTwo U (cubeBoundary N) r x) x ≤
        Kd * ρ ^ (k - 3) + (Ko / a) / (r : ℝ) ^ (k - 5) +
          (Ki * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
            ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)))) /
              (a * ρ ^ (k - 3) / (N : ℝ) ^ 3) := by
  obtain ⟨Ki, hKi, hi⟩ := energyTwo_inner_branch_sum_le hk C A hC hA panis ordinary
  obtain ⟨Ko, hKo, ho⟩ := energyTwo_outer_branch_sum_le hk C B E hC hB hE panis arm second
  let Kd : ℝ := ((2 * C) * 2 ^ k * B * (2 * ((k : ℝ) + 1) * 5 ^ k)) *
    (27 * (2 : ℝ) ^ (k - 3) * (((k : ℝ) + 1) * (4 * (k : ℝ) * 3 ^ (k - 1))))
  refine ⟨Kd, Ki, Ko, by dsimp [Kd]; positivity, hKi, hKo, ?_⟩
  intro N L H hN hH hL hHL hgap ρ hρ hround Q heart x hx hxN r hr a ha hhit
  let p := criticalPoint (k + 1)
  let g := annulusG p Q heart
  let w := energyTwoWeight (cubeBoundary N) r x
  let q : ℝ := a * ρ ^ (k - 3) / (N : ℝ) ^ 3
  let I : ℝ := Ki * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
    ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)))
  let O : ℝ := Ko * ρ ^ (k - 3) / (N : ℝ) ^ 3 / (r : ℝ) ^ (k - 5)
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hq : 0 < q := by dsimp [q]; positivity
  have hg : 0 < g x := hq.trans_le hhit
  have hLN : L ≤ N := by omega
  have h4H : 4 * H ≤ N := by
    have hL' : 2 * (L : ℝ) ≤ N := by exact_mod_cast hL
    exact_mod_cast (show 4 * (H : ℝ) ≤ N by linarith)
  have hHQ : heart ⊆ Q := Section10.centeredBox_mono (hHL.trans hLN)
  have hdisj : ∀ y ∈ cubeBoundary N, y ∉ heart := by
    intro y hy hyH
    have hyN : linfDist 0 y = N := (Finset.mem_filter.mp hy).2
    change y ∈ centeredBox (k + 1) H at hyH
    rw [← appendix_cube_eq_centeredBox] at hyH
    have hyH' := (mem_linfBall_iff_dist (0 : Vertex (k + 1)) y (Int.natCast_nonneg H)).mp hyH
    rw [Int.toNat_natCast, hyN] at hyH'
    omega
  have hm := Section10.energyTwo_mean_le_tree p Q heart (cubeBoundary N) hHQ hdisj r hx
  have hprob : (percolation (k + 1) p).real (heartEvent Q heart x) = g x :=
    heart_probability_eq_annulus p Q heart x hx
  rw [hprob, weighted_pairTree_div_partition p Q heart (centeredBox (k + 1) L) x w hg] at hm
  have hD := energyTwo_disjoint_sum_le (by omega : 3 ≤ k) hH h4H ρ hρ.le hround heart
    (Finset.Subset.refl _) x (heartAnnulus_subset Q heart hx) r hr C B hC hB panis arm
  have hI := hi N H L hN hL x hx hxN r hr
  have hO := ho N L H hH hLN hgap ρ hρ.le hround heart (Finset.Subset.refl _) x hx hxN r hr
  refine hm.trans ((add_le_add hD ((div_le_div_of_nonneg_right (add_le_add hI hO) hg.le).trans
    (div_le_div_of_nonneg_left (show 0 ≤ I + O by dsimp [I, O]; positivity) hq hhit))).trans ?_)
  change Kd * ρ ^ (k - 3) + (I + O) / q ≤ _
  rw [add_div]
  have hcancel : O / q = (Ko / a) / (r : ℝ) ^ (k - 5) := by
    dsimp [O, q]
    field_simp [ne_of_gt ha, ne_of_gt hρ, ne_of_gt hn0, ne_of_gt hr0] <;> ring
  rw [hcancel]
  change _ ≤ Kd * ρ ^ (k - 3) + (Ko / a) / (r : ℝ) ^ (k - 5) + I / q
  apply le_of_eq
  ring

end NearCritical.Section8
