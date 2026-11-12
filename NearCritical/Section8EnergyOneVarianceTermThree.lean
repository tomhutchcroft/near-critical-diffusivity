module

public import NearCritical.Section8EnergyMeanScale
public import NearCritical.Section8EnergyOneInnerBranch
public import NearCritical.Section8EnergyOneOuterBranch

/-! The numerical estimate for the third ERE1 variance term, on both regions. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open MeasureTheory
open scoped Classical

/-- The actual third weighted variance term is at most the hit probability
times a uniform multiple of `r^(6-d)`. The cube scale can be chosen after `r`. -/
theorem energyOne_variance_term_three_le {k : ℕ} (hk : 7 ≤ k)
    (C B G A : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i B)
    (green : CriticalSupGreenUpper (k + 1) G) (ordinary : OrdinaryArmWindowInput (k + 1) A)
    (ρ a : ℝ) (hρ : 0 < ρ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N L H : ℕ), 1 ≤ N → 1 ≤ H → 2 * L ≤ N → H ≤ L →
      (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H → (H : ℝ) ≤ ρ * N →
      ∀ (excluded : Finset (Vertex (k + 1))), centeredBox (k + 1) L ⊆ excluded →
      let Q := centeredBox (k + 1) N
      let heart := centeredBox (k + 1) H
      let D := heartAnnulus Q heart
      let p := criticalPoint (k + 1)
      let g := annulusG p Q heart
      let τ := annulusTau p Q heart
      ∀ x ∈ D, latticeDistance 0 x = N → ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ^ (k - 5) ≤ (N : ℝ) ^ (k - 6) →
      a * ρ ^ (k - 3) / (N : ℝ) ^ 3 ≤ g x →
      let w := energyOneWeight excluded r x
      let F (u : Vertex (k + 1)) := ∑ y ∈ D, w y * τ u y
      (∑ y ∈ D, w y * g y) * (∑ u ∈ D, g u * τ u x * F u) ≤
        g x * (K / (r : ℝ) ^ (k - 5)) := by
  obtain ⟨Ki, hKi, hi⟩ := energyOne_inner_branch_sum_le (by omega : 6 ≤ k) C G A hC hG hA panis green ordinary
  obtain ⟨Ko, hKo, ho⟩ := energyOne_outer_branch_sum_le (by omega : 7 ≤ k + 1)
    C B G hC hB hG panis arm green
  let Kd : ℝ := ((2 * C) * 4 ^ k * B * (2 * ((k + 1 : ℕ) : ℝ) * 5 ^ k)) *
    (1 + 2 * ((k + 1 : ℕ) : ℝ) * 3 ^ k) * 27 * ρ ^ (k - 3)
  let J : ℝ := Ki * ((3 : ℝ) ^ k + (2 : ℝ) ^ (k - 1)) * (2 : ℝ) ^ (2 * k - 3) /
    (a * ρ ^ (k - 3))
  have hKd : 0 ≤ Kd := by dsimp [Kd]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨Kd * (J + Ko / a), by positivity, ?_⟩
  intro N L H hN hH hL hHL hgap hround excluded hex Q heart D p g τ x hx hxN r hr hscale hhit w F
  let I : ℝ := Ki * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
    ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ)))
  let q : ℝ := a * ρ ^ (k - 3) / (N : ℝ) ^ 3
  let v (u : Vertex (k + 1)) := g u * τ u x * F u
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hq : 0 < q := by dsimp [q]; positivity
  have hg : 0 ≤ g x := (hq.trans_le hhit).le
  have hLN : L ≤ N := by omega
  have hD : (∑ y ∈ D, w y * g y) ≤ Kd := by
    simpa only [Kd, w, g, p, D, Q, Nat.add_sub_cancel, show k + 1 - 4 = k - 3 by omega] using
      energyOne_disjoint_sum_le (by omega : 4 ≤ k + 1) hH hLN hgap ρ hρ.le hround heart excluded
        (Finset.Subset.refl _) hex x hxN r hr C B hC hB panis arm
  have hI : (∑ u ∈ D ∩ centeredBox (k + 1) L, v u) ≤ I :=
    hi N H L hN hL excluded x hx hxN r hr
  have hIscale : I / q ≤ J / (r : ℝ) ^ (k - 5) := by
    exact (energyMean_inner_remainder_le hk hN (hHL.trans hLN) hLN Ki a ρ hKi ha hρ).trans
      (div_le_div_of_nonneg_left hJ (by positivity) hscale)
  have hI' : (∑ u ∈ D ∩ centeredBox (k + 1) L, v u) ≤ g x * (J / (r : ℝ) ^ (k - 5)) := by
    calc
      _ ≤ I := hI
      _ ≤ (J / (r : ℝ) ^ (k - 5)) * q := (div_le_iff₀ hq).mp hIscale
      _ ≤ (J / (r : ℝ) ^ (k - 5)) * g x := mul_le_mul_of_nonneg_left hhit (by positivity)
      _ = _ := by ring
  have hO := ho N L H hH hLN hgap ρ hρ.le hround heart excluded (Finset.Subset.refl _) x hx hxN r hr
  have hrpow : (r : ℝ) ^ ((6 : ℝ) - ((k + 1 : ℕ) : ℝ)) = 1 / (r : ℝ) ^ (k - 5) := by
    have h : (6 : ℝ) - ((k + 1 : ℕ) : ℝ) = -((k - 5 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 5 ≤ k)]
      push_cast
      ring
    rw [h, Real.rpow_neg hrp.le, Real.rpow_natCast, inv_eq_one_div]
  rw [hrpow, show k + 1 - 4 = k - 3 by omega] at hO
  have hO' : (∑ u ∈ D.filter (fun u => u ∉ centeredBox (k + 1) L), v u) ≤
      g x * ((Ko / a) / (r : ℝ) ^ (k - 5)) := by
    calc
      _ ≤ Ko * ρ ^ (k - 3) / (N : ℝ) ^ 3 * (1 / (r : ℝ) ^ (k - 5)) := hO
      _ = q * ((Ko / a) / (r : ℝ) ^ (k - 5)) := by
        dsimp [q]
        field_simp [ha.ne', hn.ne', hrp.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hhit (by positivity)
  have hv : (∑ u ∈ D, v u) ≤ g x * ((J + Ko / a) / (r : ℝ) ^ (k - 5)) := by
    have hsplit : (∑ u ∈ D ∩ centeredBox (k + 1) L, v u) +
        (∑ u ∈ D.filter (fun u => u ∉ centeredBox (k + 1) L), v u) = ∑ u ∈ D, v u := by
      rw [← Finset.filter_mem_eq_inter, Finset.sum_filter_add_sum_filter_not]
    rw [← hsplit, add_div, mul_add]
    exact add_le_add hI' hO'
  have hv0 : 0 ≤ ∑ u ∈ D, v u := by
    apply Finset.sum_nonneg
    intro u _
    exact mul_nonneg (mul_nonneg (show 0 ≤ g u from measureReal_nonneg)
      (show 0 ≤ τ u x from measureReal_nonneg))
      (Finset.sum_nonneg fun y _ => mul_nonneg (energyOneWeight_nonneg _ _ _ _)
        (show 0 ≤ τ u y from measureReal_nonneg))
  change (∑ y ∈ D, w y * g y) * (∑ u ∈ D, v u) ≤ _
  exact (mul_le_mul hD hv hv0 hKd).trans_eq (by ring)

end NearCritical.Section8
