module

public import NearCritical.Section8AnnulusHeartHitLower
public import NearCritical.Section8EnergyMeanScale
public import NearCritical.Section8EnergyTwoMeanBound
public import NearCritical.Section10MomentCubeGeometry

/-! Uniform conditional mean estimates on the marked faces in Section 10. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open NearCritical.Section8 AppendixVariance MeasureTheory
open scoped Classical

/-- The two mean conditions used for pre-good cubes, with the heart ratio
chosen before the energy cutoff and the cube scale. The uniform first-moment
box lower estimate is the remaining lower-bound input. -/
theorem marked_conditional_means_of_box_lower (e : ℕ) (he : 2 ≤ e)
    (asymp : TwoPointAsymptotics (e + 7)) (C B E A : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (arm : ∀ i : Fin (e + 7), HalfSpaceCriticalArmInput i B)
    (second : ∀ i : Fin (e + 7), SlabBoundarySecondMomentUpper i E)
    (ordinary : OrdinaryArmWindowInput (e + 7) A) (c : ℝ) (hc : 0 < c)
    (hbox : ∀ (i : Fin (e + 7)) (R : ℕ) (x : Vertex (e + 7)), 1 ≤ R →
      (x i = -(R : ℤ) ∨ x i = (R : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (R : ℝ) - (1 / 2 : ℝ) * (R : ℝ)) →
      ∀ y ∈ centeredBox (e + 7) R, R ≤ 2 * (R - linfDist 0 y) →
        c / (R : ℝ) ^ (e + 6) ≤ (percolation (e + 7) (criticalPoint (e + 7))).real
          (connectionToSetEvent (centeredBox (e + 7) R : Set (Vertex (e + 7))) x {y}))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cc : ℝ, 0 < cc ∧ cc ≤ 1 / 32 ∧ ∃ r₀ t₀ : ℕ, 1 ≤ r₀ ∧ 64 ≤ t₀ ∧
      ∀ r ≥ r₀, ∀ t ≥ t₀, ∀ x ∈ typMark t (0 : Vertex (e + 7)),
      let Q := typicalCube t (0 : Vertex (e + 7))
      let heart := typicalHeart t (0 : Vertex (e + 7)) cc
      heartConditionalMean (criticalPoint (e + 7)) Q heart
        (fun U => regularityEnergyOne U (typicalInnerCube t 0) r x) x ≤ ε ∧
      heartConditionalMean (criticalPoint (e + 7)) Q heart
        (fun U => regularityEnergyTwo U (typicalBoundary t 0) r x) x ≤ ε := by
  let k := e + 6
  have hk : 8 ≤ k := by dsimp [k]; omega
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ e + 7) asymp
  obtain ⟨κ, hκ, hhit⟩ := annulusG_lower_at_pc_of_box_lower e asymp C hC panis c hc hbox
  obtain ⟨D₁, I₁, O₁, hD₁, hI₁, hO₁, hmean₁⟩ :=
    energyOne_mean_le_of_heart_hit (k := k) (by omega) C B G A hC hB hG.le hA panis arm green ordinary
  obtain ⟨D₂, I₂, O₂, hD₂, hI₂, hO₂, hmean₂⟩ :=
    energyTwo_mean_le_of_heart_hit (k := k) (by omega) C B E A hC hB hE hA panis arm second ordinary
  let a : ℝ := κ / (4 : ℝ) ^ (k - 3)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨m₀, _, hm₀⟩ := exists_inv_nat_pow_threshold (k := k - 3) (by omega)
    (D₁ + D₂) (ε / 3) (by positivity) (by positivity)
  let m := max 16 m₀
  have hm : (16 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast le_max_left 16 m₀
  have hmpos : (0 : ℝ) < m := by linarith
  let cc : ℝ := 1 / (2 * (m : ℝ))
  let ρ : ℝ := 2 * cc
  have hcc : 0 < cc := by dsimp [cc]; positivity
  have hcc1 : cc ≤ 1 / 32 := by
    dsimp [cc]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρm : ρ = 1 / (m : ℝ) := by dsimp [ρ, cc]; ring
  have hD : (D₁ + D₂) * ρ ^ (k - 3) ≤ ε / 3 := by
    rw [hρm, div_pow, one_pow, ← mul_div_assoc, mul_one]
    exact hm₀ m (le_max_right _ _)
  obtain ⟨r₀, hr₀, hout⟩ := exists_inv_nat_pow_threshold (k := k - 5) (by omega)
    ((O₁ + O₂) / a) (ε / 3) (by positivity) (by positivity)
  let S : ℝ := ((3 : ℝ) ^ k + (2 : ℝ) ^ (k - 1)) * (2 : ℝ) ^ (2 * k - 3)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨N₀, _, hin⟩ := exists_inv_nat_pow_threshold (k := k - 6) (by omega)
    ((I₁ + I₂) * S / (a * ρ ^ (k - 3))) (ε / 3) (by positivity) (by positivity)
  obtain ⟨t₁, _, ht₁⟩ := typicalMomentCube_eventually_scales cc hcc hcc1
  refine ⟨cc, hcc, hcc1, r₀, max 64 (max t₁ (2 * N₀ + 1)), hr₀, le_max_left _ _, ?_⟩
  intro r hr t ht x hx Q heart
  let N := (t - 1) / 2
  let L := N / 2
  let H := typicalHeartRadius t cc
  have ht64 : 64 ≤ t := (le_max_left _ _).trans ht
  have ht' : max t₁ (2 * N₀ + 1) ≤ t := (le_max_right _ _).trans ht
  have hN₀ : N₀ ≤ N := by have := (le_max_right t₁ (2 * N₀ + 1)).trans ht'; dsimp [N]; omega
  obtain ⟨hN, hH, hL, hHL, h5, hgap, hlo, hhi⟩ := ht₁ t ((le_max_left _ _).trans ht')
  have hLN : L ≤ N := by omega
  have hHN : H ≤ N := hHL.trans hLN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hQ : Q = centeredBox (e + 7) N := typicalCube_zero t (by omega)
  have hheart : heart = centeredBox (e + 7) H := typicalHeart_zero_eq_centeredBox t (by omega) cc hcc (by linarith)
  have hboundary := typicalBoundary_zero_eq_cubeBoundary (k := k) t (by omega)
  have hxD : x ∈ heartAnnulus (centeredBox (e + 7) N) (centeredBox (e + 7) H) := by
    rw [← hQ, ← hheart]
    exact typMark_mem_annulus t ht64 (by linarith) hx
  have hxN : linfDist 0 x = N := by
    have h := typMark_subset_boundary t 0 hx
    rw [hboundary] at h
    exact (Finset.mem_filter.mp h).2
  have hxN' : latticeDistance 0 x = N := by rw [← linfDist_cast_eq_latticeDistance, hxN]
  obtain ⟨i, hface, hmargin⟩ := typMark_face_margin t (by omega) hx
  have hhit' := hhit i N H x hH h5 hxN (hface.elim Or.inr Or.inl) (fun j hj => by linarith [hmargin j hj])
  have hnorm : a * ρ ^ (k - 3) / (N : ℝ) ^ 3 ≤
      annulusG (criticalPoint (e + 7)) (centeredBox (e + 7) N) (centeredBox (e + 7) H) x := by
    have hcomp : ρ / 4 ≤ (H : ℝ) / (N : ℝ) := by
      apply (le_div_iff₀ hn0).mpr
      dsimp [ρ]
      linarith
    have hp := pow_le_pow_left₀ (show 0 ≤ ρ / 4 by positivity) hcomp (k - 3)
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hκ.le)
      (show 0 ≤ (N : ℝ) ^ 3 by positivity)
    have hexp : k - 3 = e + 3 := by dsimp [k]; omega
    rw [← hexp] at hhit'
    calc
      _ = κ * (ρ / 4) ^ (k - 3) / (N : ℝ) ^ 3 := by dsimp [a]; rw [div_pow]; ring
      _ ≤ _ := h.trans hhit'
  have hm₁ := hmean₁ N L H hN hH hL hHL hgap ρ hρ hhi _
    (halfBox_subset_typicalInnerCube t (by omega)) x hxD hxN' r hr1 a ha hnorm
  have hm₂ := hmean₂ N L H hN hH hL hHL hgap ρ hρ hhi x hxD hxN' r hr1 a ha hnorm
  have hrpow : (r : ℝ) ^ ((6 : ℝ) - ((k + 1 : ℕ) : ℝ)) = 1 / (r : ℝ) ^ (k - 5) := by
    have h : (6 : ℝ) - ((k + 1 : ℕ) : ℝ) = -((k - 5 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 5 ≤ k)]
      push_cast
      ring
    rw [h, Real.rpow_neg hr0.le, Real.rpow_natCast, inv_eq_one_div]
  rw [hrpow, ← mul_div_assoc, mul_one] at hm₁
  have hi₁ :
      I₁ * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
          ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ))) /
        (a * ρ ^ (k - 3) / (N : ℝ) ^ 3) ≤
      I₁ * S / (a * ρ ^ (k - 3)) / (N : ℝ) ^ (k - 6) := by
    simpa only [S, mul_assoc] using
      (energyMean_inner_remainder_le (N := N) (H := H) (L := L) (by omega : 7 ≤ k)
        hN hHN hLN I₁ a ρ hI₁ ha hρ)
  have hi₂ :
      I₂ * (((2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)) *
          ((N : ℝ) / 2) ^ ((5 : ℝ) - 2 * ((k + 1 : ℕ) : ℝ))) /
        (a * ρ ^ (k - 3) / (N : ℝ) ^ 3) ≤
      I₂ * S / (a * ρ ^ (k - 3)) / (N : ℝ) ^ (k - 6) := by
    simpa only [S, mul_assoc] using
      (energyMean_inner_remainder_le (N := N) (H := H) (L := L) (by omega : 7 ≤ k)
        hN hHN hLN I₂ a ρ hI₂ ha hρ)
  have hi_sum := hin N hN₀
  have ho_sum := hout r hr
  rw [add_div, add_div] at ho_sum
  have hi_sum' : (I₁ * S / (a * ρ ^ (k - 3))) / (N : ℝ) ^ (k - 6) +
      (I₂ * S / (a * ρ ^ (k - 3))) / (N : ℝ) ^ (k - 6) ≤ ε / 3 := by
    rw [← add_div, ← add_div, ← add_mul]
    exact hi_sum
  rw [hQ, hheart, hboundary]
  constructor
  · apply hm₁.trans
    have hposD : 0 ≤ D₂ * ρ ^ (k - 3) := by positivity
    have hposO : 0 ≤ O₂ / a / (r : ℝ) ^ (k - 5) := by positivity
    have hposI : 0 ≤ I₂ * S / (a * ρ ^ (k - 3)) / (N : ℝ) ^ (k - 6) := by positivity
    have hD' : D₁ * ρ ^ (k - 3) + D₂ * ρ ^ (k - 3) ≤ ε / 3 := by rwa [← add_mul]
    linarith only [hi₁, hi_sum', ho_sum, hD', hposD, hposO, hposI]
  · apply hm₂.trans
    have hposD : 0 ≤ D₁ * ρ ^ (k - 3) := by positivity
    have hposO : 0 ≤ O₁ / a / (r : ℝ) ^ (k - 5) := by positivity
    have hposI : 0 ≤ I₁ * S / (a * ρ ^ (k - 3)) / (N : ℝ) ^ (k - 6) := by positivity
    have hD' : D₁ * ρ ^ (k - 3) + D₂ * ρ ^ (k - 3) ≤ ε / 3 := by rwa [← add_mul]
    linarith only [hi₂, hi_sum', ho_sum, hD', hposD, hposO, hposI]

end NearCritical.Section10
