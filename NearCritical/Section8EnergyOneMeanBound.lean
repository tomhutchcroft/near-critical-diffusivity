module

public import NearCritical.Section8EnergyOneInnerBranch
public import NearCritical.Section8EnergyOneOuterBranch
public import NearCritical.Section10EnergyMeanTree
public import NearCritical.Section10SpanningCited

/-! Assembly of the three contributions to the first conditional energy mean. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open MeasureTheory
open scoped Classical

/-- The normalization cancels the hit probability in the disjoint term.
The branching term is split by the location of the branch point. -/
theorem weighted_pairTree_div_partition {d : ℕ} (p : unitInterval)
    (Q H L : Finset (Vertex d)) (x : Vertex d) (w : Vertex d → ℝ)
    (hx : 0 < annulusG p Q H x) :
    let D := heartAnnulus Q H
    let g := annulusG p Q H
    let τ := annulusTau p Q H
    let leg (u : Vertex d) := g u * τ u x * (∑ y ∈ D, w y * τ u y)
    (∑ y ∈ D, w y * Section10.pairTree p Q H x y) / g x =
      (∑ y ∈ D, w y * g y) +
        ((∑ u ∈ D ∩ L, leg u) + ∑ u ∈ D.filter (fun u => u ∉ L), leg u) / g x := by
  intro D g τ leg
  have hcomm : (∑ y ∈ D, w y * (∑ u ∈ D, g u * τ u x * τ u y)) = ∑ u ∈ D, leg u := by
    simp only [leg, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hnum : (∑ y ∈ D, w y * Section10.pairTree p Q H x y) =
      g x * (∑ y ∈ D, w y * g y) + ∑ u ∈ D, leg u := by
    change (∑ y ∈ D, w y * (g x * g y + ∑ u ∈ D, g u * τ u x * τ u y)) = _
    rw [show (∑ y ∈ D, w y * (g x * g y + ∑ u ∈ D, g u * τ u x * τ u y)) =
        (∑ y ∈ D, w y * (g x * g y)) + ∑ y ∈ D, w y * (∑ u ∈ D, g u * τ u x * τ u y) by
      simp only [mul_add, Finset.sum_add_distrib], hcomm]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hpart : (∑ u ∈ D ∩ L, leg u) + ∑ u ∈ D.filter (fun u => u ∉ L), leg u = ∑ u ∈ D, leg u := by
    rw [← Finset.filter_mem_eq_inter, Finset.sum_filter_add_sum_filter_not]
  rw [hnum, hpart, add_div]
  have hx' : g x ≠ 0 := ne_of_gt hx
  congr 1
  field_simp

/-- The quantitative Ef1 bound with the finite-scale inner remainder and
the heart-hit lower estimate supplied explicitly. -/
theorem energyOne_mean_le_of_heart_hit {k : ℕ} (hk : 6 ≤ k)
    (C B G A : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i B)
    (green : CriticalSupGreenUpper (k + 1) G) (ordinary : OrdinaryArmWindowInput (k + 1) A) :
    ∃ Kd Ki Ko : ℝ, 0 ≤ Kd ∧ 0 ≤ Ki ∧ 0 ≤ Ko ∧
      ∀ (N L H : ℕ), 1 ≤ N → 1 ≤ H → 2 * L ≤ N → H ≤ L →
      (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H →
      ∀ ρ : ℝ, 0 < ρ → (H : ℝ) ≤ ρ * N →
      ∀ (excluded : Finset (Vertex (k + 1))), centeredBox (k + 1) L ⊆ excluded →
      let Q := centeredBox (k + 1) N
      let heart := centeredBox (k + 1) H
      ∀ x ∈ heartAnnulus Q heart, latticeDistance 0 x = N →
      ∀ (r : ℕ), 1 ≤ r → ∀ a : ℝ, 0 < a →
      a * ρ ^ (k - 3) / (N : ℝ) ^ 3 ≤ annulusG (criticalPoint (k + 1)) Q heart x →
      heartConditionalMean (criticalPoint (k + 1)) Q heart (fun U => regularityEnergyOne U excluded r x) x ≤
        Kd * ρ ^ (k - 3) + (Ko / a) * (r : ℝ) ^ ((6 : ℝ) - ((k + 1 : ℕ) : ℝ)) +
          (Ki * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
            ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)))) /
              (a * ρ ^ (k - 3) / (N : ℝ) ^ 3) := by
  obtain ⟨Ki, hKi, hi⟩ := energyOne_inner_branch_sum_le hk C G A hC hG hA panis green ordinary
  obtain ⟨Ko, hKo, ho⟩ := energyOne_outer_branch_sum_le (by omega : 7 ≤ k + 1)
    C B G hC hB hG panis arm green
  let Kd : ℝ := ((2 * C) * 4 ^ k * B * (2 * ((k + 1 : ℕ) : ℝ) * 5 ^ k)) *
    (1 + 2 * ((k + 1 : ℕ) : ℝ) * 3 ^ k) * 27
  refine ⟨Kd, Ki, Ko, by dsimp [Kd]; positivity, hKi, hKo, ?_⟩
  intro N L H hN hH hL hHL hgap ρ hρ hround excluded hex Q heart x hx hxN r hr a ha hhit
  let p := criticalPoint (k + 1)
  let g := annulusG p Q heart
  let w := energyOneWeight excluded r x
  let q : ℝ := a * ρ ^ (k - 3) / (N : ℝ) ^ 3
  let I : ℝ := Ki * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
    ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)))
  let O : ℝ := Ko * ρ ^ (k - 3) / (N : ℝ) ^ 3 * (r : ℝ) ^ ((6 : ℝ) - ((k + 1 : ℕ) : ℝ))
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < q := by dsimp [q]; positivity
  have hg : 0 < g x := hq.trans_le hhit
  have hLN : L ≤ N := by omega
  have hHQ : heart ⊆ Q := Section10.centeredBox_mono (hHL.trans hLN)
  have hHex : heart ⊆ excluded := (Section10.centeredBox_mono hHL).trans hex
  have hm := Section10.energyOne_mean_le_tree p Q heart excluded hHQ hHex r hx
  have hprob : (percolation (k + 1) p).real (heartEvent Q heart x) = g x :=
    heart_probability_eq_annulus p Q heart x hx
  rw [hprob, weighted_pairTree_div_partition p Q heart (centeredBox (k + 1) L) x w hg] at hm
  have hD : (∑ y ∈ heartAnnulus Q heart, w y * g y) ≤ Kd * ρ ^ (k - 3) := by
    simpa only [Kd, w, g, p, Nat.add_sub_cancel, show k + 1 - 4 = k - 3 by omega] using
      energyOne_disjoint_sum_le (by omega : 4 ≤ k + 1) hH hLN hgap ρ hρ.le hround heart excluded
        (Finset.Subset.refl _) hex x hxN r hr C B hC hB panis arm
  have hI := hi N H L hN hL excluded x hx hxN r hr
  have hO := ho N L H hH hLN hgap ρ hρ.le hround heart excluded (Finset.Subset.refl _) x hx hxN r hr
  simp only [show k + 1 - 4 = k - 3 by omega] at hO
  refine hm.trans ((add_le_add hD ((div_le_div_of_nonneg_right (add_le_add hI hO) hg.le).trans
    (div_le_div_of_nonneg_left (show 0 ≤ I + O by dsimp [I, O]; positivity) hq hhit))).trans ?_)
  change Kd * ρ ^ (k - 3) + (I + O) / q ≤ _
  rw [add_div]
  have hcancel : O / q = (Ko / a) * (r : ℝ) ^ ((6 : ℝ) - ((k + 1 : ℕ) : ℝ)) := by
    dsimp [O, q]
    field_simp [ne_of_gt ha, ne_of_gt hρ, ne_of_gt hn0] <;> ring
  rw [hcancel]
  change _ ≤ Kd * ρ ^ (k - 3) + (Ko / a) * (r : ℝ) ^ ((6 : ℝ) - ((k + 1 : ℕ) : ℝ)) + I / q
  apply le_of_eq
  ring

end NearCritical.Section8
