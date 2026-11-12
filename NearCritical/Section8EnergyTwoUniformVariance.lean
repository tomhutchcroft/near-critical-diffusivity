module

public import NearCritical.Section8ActualVarianceSum
public import NearCritical.Section8BoundaryF2Convolution
public import NearCritical.Section8EnergyTwoVarianceTermThree

/-! The actual ERE2 variance bound with a coefficient uniform in the cutoff. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

/-- The ERE2 bound uses every boundary site, including the weight at the root. -/
theorem energyTwo_centeredMoment_le_uniform {E : ℕ} (hE : 2 ≤ E)
    (C B S A : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hS : 0 ≤ S) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (E + 7) C)
    (arm : ∀ i : Fin (E + 7), HalfSpaceCriticalArmInput i B)
    (second : ∀ i : Fin (E + 7), SlabBoundarySecondMomentUpper i S)
    (ordinary : OrdinaryArmWindowInput (E + 7) A) (asymp : TwoPointAsymptotics (E + 7))
    (ρ a : ℝ) (hρ : 0 < ρ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n h c r : ℕ), 1 ≤ n → 1 ≤ r → r ≤ n →
      2 * r ^ (E + 1) ≤ n → 1 ≤ c → 2 * h ≤ n → 5 * c ≤ n →
      (n : ℝ) / 4 ≤ (h : ℝ) - 2 * c → (c : ℝ) ≤ ρ * n →
      let Q := centeredBox (E + 7) n
      let H := centeredBox (E + 7) c
      let p := criticalPoint (E + 7)
      ∀ x ∈ heartAnnulus Q H, linfDist 0 x = n →
      a * ρ ^ (E + 3) / (n : ℝ) ^ 3 ≤ annulusG p Q H x →
      heartCenteredMoment p Q H (fun F => regularityEnergyTwo F (cubeBoundary n) r x) x ≤
        (percolation (E + 7) p).real (heartEvent Q H x) * (K / (r : ℝ) ^ (E + 1)) := by
  obtain ⟨CF, hCF, hglobal⟩ := annulus_energyTwo_convolution_le (k := E + 6)
    (by omega) C B S hC hB hS panis arm second
  obtain ⟨CFr, hCFr, hremote⟩ := energy2_RD_capstone_input (E := E) C B S hC hB hS panis arm second
  obtain ⟨K, hK, hvar⟩ := annulus_appendixVarianceSum_bound hE C B S A CF CFr
    hC hB hS hA hCF hCFr.le panis arm second ordinary asymp
  obtain ⟨J, hJ, hthird⟩ := energyTwo_variance_term_three_le (k := E + 6)
    (by omega) C B S A hC hB hS hA panis arm second ordinary ρ a hρ ha
  let M : ℝ := max (2 / (a * ρ ^ (E + 3))) 1
  have hM : 0 ≤ M := zero_le_one.trans (le_max_right _ _)
  refine ⟨M * K + J, by positivity, ?_⟩
  intro n h c r hn hr hrn hlarge hc hh h5c hgap hcρ Q H p x hx hxN hhit
  let D : Finset (Vertex (E + 7)) := sourceAnnulus n c
  let g := annulusG p Q H
  let τ := annulusTau p Q H
  let f := energyTwoWeight (cubeBoundary n) r x
  let F (u : Vertex (E + 7)) := ∑ y ∈ D, f y * τ u y
  have hD : D = heartAnnulus Q H := sourceAnnulus_eq_heartAnnulus (E + 6) n c
  have hxD : x ∈ D := hD.symm ▸ hx
  have hxB : x ∈ cubeBoundary n := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxD).1, hxN⟩
  have h2c : 2 * c ≤ h := by
    exact_mod_cast (show 2 * (c : ℝ) ≤ h by linarith [show (0 : ℝ) ≤ n by positivity])
  have hHQ : H ⊆ Q := Section10.centeredBox_mono (by omega : c ≤ n)
  have hf : ∀ y, 0 ≤ f y := energyTwoWeight_nonneg _ _ _
  have hzero : ∀ y ∈ Q, y ∉ heartAnnulus Q H → f y = 0 := by
    intro y hy hyn
    have hyB : y ∉ cubeBoundary n := by
      intro hb
      have hnorm : linfDist 0 y = n := (Finset.mem_filter.mp hb).2
      have hyH : y ∉ H := by
        intro hm
        change y ∈ centeredBox (E + 7) c at hm
        rw [← appendix_cube_eq_centeredBox] at hm
        have hh := mem_cube_iff_dist.mp hm
        omega
      exact hyn (Finset.mem_sdiff.mpr ⟨hy, fun hm => hyH (Finset.mem_sdiff.mp hm).1⟩)
    simp [f, energyTwoWeight, hyB]
  have hF0 (u : Vertex (E + 7)) : 0 ≤ F u :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hf y) measureReal_nonneg
  have hglobal' (u : Vertex (E + 7)) (hu : u ∈ D) :
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3) := by
    simpa only [F, f, hD, show E + 6 - 3 = E + 3 by omega] using
      hglobal n r hr H x hx hxN u (hD ▸ hu)
  have hremote' (u : Vertex (E + 7)) (hu : u ∈ sourceRD n c) :
      F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (show D ⊆ cube n from fun y hy => (Finset.mem_filter.mp hy).1)
      (f := fun y => f y * τ u y) (fun y _ _ => mul_nonneg (hf y) measureReal_nonneg)).trans ?_
    exact hremote n c r hn h5c hr x u hxB hu
  have happ := hvar n h c r hn hr hrn hlarge hc h2c hh h5c hgap x hxD hxN F
    (fun u _ => hF0 u) hglobal' hremote'
  have hrpow : r ^ 2 ≤ n := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hn' : 2 * (r : ℝ) ^ (E + 1) ≤ n := by exact_mod_cast hlarge
    have hmon := pow_le_pow_right₀ hr1 (by omega : 2 ≤ E + 1)
    exact_mod_cast (show (r : ℝ) ^ 2 ≤ n by linarith)
  have hs := energyMean_cutoff_power_le_scale (k := E + 6) (by omega) hr hrpow
  have hxN' : latticeDistance 0 x = n := by rw [← linfDist_cast_eq_latticeDistance, hxN]
  have hhit' : a * ρ ^ (E + 6 - 3) / (n : ℝ) ^ 3 ≤ g x := by
    simpa only [show E + 6 - 3 = E + 3 by omega] using hhit
  have hthird' := hthird n h c hn hc hh (by omega) hgap hcρ x hx hxN' r hr hs hhit'
  rw [show E + 6 - 5 = E + 1 by omega] at hthird'
  have hq : 0 < (percolation (E + 7) p).real (heartEvent Q H x) := by
    rw [show (percolation (E + 7) p).real (heartEvent Q H x) = g x from
      heart_probability_eq_annulus p Q H x hx]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact lt_of_lt_of_le (by positivity) hhit
  have hb := heartCenteredMoment_le_appendixVarianceSum p Q H x hx f
    (fun S => regularityEnergyTwo S (cubeBoundary n) r x) hf hzero n hn
    (a * ρ ^ (E + 3)) (J / (r : ℝ) ^ (E + 1)) (by positivity)
    (energyTwo_centeredMoment_le_branches p Q H (cubeBoundary n) hHQ r x hq) hhit hthird'
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hq.le)
  change M * appendixVarianceSum n (heartAnnulus Q H) x g
    (fun u => ∑ y ∈ heartAnnulus Q H, f y * τ u y) τ + J / (r : ℝ) ^ (E + 1) ≤ _
  rw [← hD]
  change M * appendixVarianceSum n D x g F τ + J / (r : ℝ) ^ (E + 1) ≤ _
  rw [add_div, mul_div_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left happ hM) le_rfl

end NearCritical.Section8
