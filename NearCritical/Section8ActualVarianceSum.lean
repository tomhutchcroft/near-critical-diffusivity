module

public import NearCritical.AppendixVarRegime
public import NearCritical.Section8EnergyRDInputs
public import NearCritical.Section8EnergyTwoOuterBranch
public import NearCritical.Section8RDCapstoneInput
public import NearCritical.Section8VarianceNormalization
public import NearCritical.Section8VarianceProfiles
public import NearCritical.Section8VarianceTwoPointInputs

/-! Apply the uniform Appendix B estimate to the actual annulus probabilities.
The global and remote bounds on the energy convolution are supplied by each energy. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

/-- The three Appendix B terms for the actual annulus law. The constants for
the two energy convolution estimates are fixed before the radii and cutoff. -/
theorem annulus_appendixVarianceSum_bound {E : ℕ} (hE : 2 ≤ E)
    (C B S A CF CFr : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hA : 1 ≤ A) (hCF : 0 ≤ CF) (hCFr : 0 ≤ CFr)
    (panis : PanisHalfSpaceTwoPointUpper (E + 7) C)
    (arm : ∀ i : Fin (E + 7), HalfSpaceCriticalArmInput i B)
    (second : ∀ i : Fin (E + 7), SlabBoundarySecondMomentUpper i S)
    (ordinary : OrdinaryArmWindowInput (E + 7) A) (asymp : TwoPointAsymptotics (E + 7)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n h c r : ℕ), 1 ≤ n → 1 ≤ r → r ≤ n →
      2 * r ^ (E + 1) ≤ n → 1 ≤ c → 2 * c ≤ h → 2 * h ≤ n → 5 * c ≤ n →
      (n : ℝ) / 4 ≤ (h : ℝ) - 2 * c →
      let Q := centeredBox (E + 7) n
      let H := centeredBox (E + 7) c
      let D : Finset (Vertex (E + 7)) := sourceAnnulus n c
      let p := criticalPoint (E + 7)
      let g := annulusG p Q H
      let τ := annulusTau p Q H
      ∀ x ∈ D, linfDist 0 x = n → ∀ F : Vertex (E + 7) → ℝ,
      (∀ u ∈ D, 0 ≤ F u) →
      (∀ u ∈ D, F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3)) →
      (∀ u ∈ sourceRD n c,
        F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ))) →
      appendixVarianceSum n D x g F τ ≤ K / (r : ℝ) ^ (E + 1) := by
  obtain ⟨Cgo, hCgo, houter⟩ := annulus_outer_profile_capstone (k := E + 6)
    (by omega) C B hC hB panis arm
  obtain ⟨Cs, hCs, hsep⟩ := annulusTau_variance_separated_le (d := E + 7)
    (by omega) C hC panis
  obtain ⟨Cb, hCb, htwo⟩ := annulusTau_boundary_two_sided_le (d := E + 7)
    (by omega) C B S hC hB hS panis arm second
  obtain ⟨Cτ, hCτ, hbulk⟩ := annulusTau_bulk_shell_le (d := E + 7) (by omega) asymp
  obtain ⟨Ct, hCt, hrd⟩ := annulus_RD_capstone_input (E := E) C B S hC hB hS panis arm second
  let J : ℝ := (2 * C) * (2 : ℝ) ^ (E + 6)
  let Ca : ℝ := max J Cs
  let Cg : ℝ := 4 * A
  let K := varCapstoneConstant E Cgo Cg CF CFr Ca Cb Cs Cτ Ct
    (varBubbleConstant E Cgo CF Cb Cτ) 0 1
  have hCa : 0 ≤ Ca := hCs.trans (le_max_right _ _)
  have hCg : 0 ≤ Cg := by positivity
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro n h c r hn hr hrn hreg hc h2c h2h h5c hgap Q H D p g τ x hx hxN F hF0 hF hFRD
  let l (u : Vertex (E + 7)) : ℝ := (n : ℝ) - latticeDistance 0 u
  have hD : D = heartAnnulus Q H := sourceAnnulus_eq_heartAnnulus (E + 6) n c
  have hin {u : Vertex (E + 7)} (hu : u ∈ D) : u ∈ heartAnnulus Q H := hD ▸ hu
  have hx' : latticeDistance 0 x = n := by rw [← linfDist_cast_eq_latticeDistance, hxN]
  have hxB : x ∈ cubeBoundary n := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hxN⟩
  have hdepth := variance_depth_bounds x hxN (c := c)
  have hl1 (u : Vertex (E + 7)) (hu : u ∈ D) : 0 ≤ 1 + l u :=
    add_nonneg zero_le_one (hdepth u hu).1
  obtain ⟨hnear, hfar⟩ := hsep n h hn h2h H x (hin hx) hxN
  have hone (w : Vertex (E + 7)) (hw : w ∈ D) (u : Vertex (E + 7)) (hu : u ∈ D) :
      τ w u ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 6) := by
    have hb := annulusTau_one_sided_shell_le (n := n) (by omega : 1 ≤ E + 7)
      C hC panis H u w (hin hu) (hin hw)
    rw [show E + 7 - 1 = E + 6 by omega] at hb
    exact hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left J Cs) (hl1 u hu))
      (by positivity))
  have hnear' (w : Vertex (E + 7)) (hw : w ∈ sourceAnnulus h c)
      (u : Vertex (E + 7)) (hu : u ∈ D) (hxu : linfDist x u < (n - h) / 2) :
      τ w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (E + 6) := by
    have hwh := mem_cube_iff_dist.mp (Finset.mem_filter.mp hw).1
    have hwD : w ∈ D := sourceAnnulus_mono (by omega : h ≤ n) hw
    have hb := hnear w (hin hwD) hwh u (hin hu) hxu
    rw [show E + 7 - 1 = E + 6 by omega] at hb
    exact hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right J Cs) (hl1 u hu))
      (by positivity))
  have hfar' (u : Vertex (E + 7)) (hu : u ∈ D) (hu' : (n - h) / 2 ≤ linfDist x u) :
      τ u x ≤ Cs / (n : ℝ) ^ (E + 6) := by
    simpa only [show E + 7 - 1 = E + 6 by omega] using hfar u (hin hu) hu'
  have hbulk' (w u : Vertex (E + 7)) :
      τ w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5) := by
    simpa only [show E + 7 - 2 = E + 5 by omega] using hbulk Q H w u
  have hb := VARf_capstone_large_n_bound (Cρ := 0) hE x hn hr hrn hreg hc h2c h2h hxN g F l τ
    (appendixVarianceSum n (sourceAnnulus n c) x g F τ) 0 hCgo hCg hCF hCFr hCa hCb hCs
    (le_of_lt hCτ) (le_of_lt hCt) le_rfl le_rfl le_rfl
    (by simp only [appendixVarianceSum, zero_mul, mul_zero, add_zero] <;> exact le_rfl)
    (fun _ _ => measureReal_nonneg) hF0 (fun _ _ _ _ => measureReal_nonneg)
    (fun _ _ => measureReal_nonneg)
    (fun u hu => (hdepth u hu).1) (fun u hu => (hdepth u hu).2)
    (houter n h c hn hc (by omega) (by omega) hgap x hxN)
    (fun u _ => annulus_inner_profile_capstone A hA ordinary n c u)
    hF hFRD hone hnear' (fun w _ u _ => hbulk' w u)
    (fun u hu => htwo n H x u (hin hx) (hin hu) hx')
    hfar' (fun u hu => hrd n c hn h5c x u hxB hu)
  have hKbound : appendixVarianceSum n D x g F τ ≤ K / (r : ℝ) ^ (E + 1) := by
    simpa only [K, show E + 7 - 6 = E + 1 by omega] using hb.2
  exact hKbound.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))

/-- Uniform centered ERE1 bound on the actual annulus. The exclusion may
contain any larger set, as in the strict real cutoff of the marked cube. -/
theorem energyOne_centeredMoment_le_uniform {E : ℕ} (hE : 2 ≤ E)
    (C B S A G : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hS : 0 ≤ S) (hA : 1 ≤ A) (hG : 0 ≤ G)
    (panis : PanisHalfSpaceTwoPointUpper (E + 7) C)
    (arm : ∀ i : Fin (E + 7), HalfSpaceCriticalArmInput i B)
    (second : ∀ i : Fin (E + 7), SlabBoundarySecondMomentUpper i S)
    (ordinary : OrdinaryArmWindowInput (E + 7) A) (asymp : TwoPointAsymptotics (E + 7))
    (green : CriticalSupGreenUpper (E + 7) G)
    (ρ a : ℝ) (hρ : 0 < ρ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n h c r : ℕ), 1 ≤ n → 1 ≤ r → r ≤ n →
      2 * r ^ (E + 1) ≤ n → 1 ≤ c → 2 * h ≤ n → 5 * c ≤ n →
      (n : ℝ) / 4 ≤ (h : ℝ) - 2 * c → (c : ℝ) ≤ ρ * n →
      ∀ (excluded : Finset (Vertex (E + 7))), cube (3 * n / 4) ⊆ excluded →
      let Q := centeredBox (E + 7) n
      let H := centeredBox (E + 7) c
      let p := criticalPoint (E + 7)
      ∀ x ∈ heartAnnulus Q H, linfDist 0 x = n →
      a * ρ ^ (E + 3) / (n : ℝ) ^ 3 ≤ annulusG p Q H x →
      heartCenteredMoment p Q H (fun F => regularityEnergyOne F excluded r x) x ≤
        (percolation (E + 7) p).real (heartEvent Q H x) * (K / (r : ℝ) ^ (E + 1)) := by
  obtain ⟨CF, hCF, hglobal⟩ := annulus_energyOne_convolution_shell_le (k := E + 6)
    (by omega) G hG green
  obtain ⟨CFr, hCFr, hremote⟩ := energy1_RD_capstone_input (E := E) C B S hC hB hS panis arm second
  obtain ⟨K, hK, hvar⟩ := annulus_appendixVarianceSum_bound hE C B S A CF CFr
    hC hB hS hA hCF hCFr.le panis arm second ordinary asymp
  obtain ⟨J, hJ, hbranch⟩ := energyOne_centeredMoment_le_appendixVarianceSum (k := E + 6)
    (by omega) C B G A hC hB hG hA panis arm green ordinary ρ a hρ ha
  let M : ℝ := max (2 / (a * ρ ^ (E + 3))) 1
  have hM : 0 ≤ M := zero_le_one.trans (le_max_right _ _)
  refine ⟨M * K + J, by positivity, ?_⟩
  intro n h c r hn hr hrn hlarge hc hh h5c hgap hcρ excluded hex Q H p x hx hxN hhit
  let D : Finset (Vertex (E + 7)) := sourceAnnulus n c
  let g := annulusG p Q H
  let τ := annulusTau p Q H
  let F (u : Vertex (E + 7)) := ∑ y ∈ D, energyOneWeight excluded r x y * τ u y
  have hD : D = heartAnnulus Q H := sourceAnnulus_eq_heartAnnulus (E + 6) n c
  have hxD : x ∈ D := hD.symm ▸ hx
  have hxB : x ∈ cubeBoundary n := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxD).1, hxN⟩
  have h2c : 2 * c ≤ h := by
    exact_mod_cast (show 2 * (c : ℝ) ≤ h by linarith [show (0 : ℝ) ≤ n by positivity])
  have hhex : centeredBox (E + 7) h ⊆ excluded := by
    apply Finset.Subset.trans _ hex
    rw [appendix_cube_eq_centeredBox]
    exact Section10.centeredBox_mono (by omega)
  have hF0 (u : Vertex (E + 7)) : 0 ≤ F u :=
    Finset.sum_nonneg fun y _ => mul_nonneg (energyOneWeight_nonneg _ _ _ _) measureReal_nonneg
  have hglobal' (u : Vertex (E + 7)) :
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3) := by
    simpa only [F, hD, show E + 6 - 3 = E + 3 by omega] using hglobal Q H excluded x u r hr
  have hweight (y : Vertex (E + 7)) :
      energyOneWeight excluded r x y ≤ energyOneWeight (cube (3 * n / 4)) r x y := by
    by_cases hy : y ∈ excluded
    · simpa [energyOneWeight, hy] using
        (energyOneWeight_nonneg (cube (3 * n / 4)) r x y)
    · have hy' : y ∉ (cube (3 * n / 4) : Finset (Vertex (E + 7))) := fun hm => hy (hex hm)
      simp only [energyOneWeight, if_pos hy, if_pos hy', le_refl]
  have hremote' (u : Vertex (E + 7)) (hu : u ∈ sourceRD n c) :
      F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)) := by
    calc
      F u ≤ ∑ y ∈ D, energyOneWeight (cube (3 * n / 4)) r x y * τ u y :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hweight y) measureReal_nonneg
      _ ≤ ∑ y ∈ (cube n : Finset (Vertex (E + 7))),
          energyOneWeight (cube (3 * n / 4)) r x y * τ u y :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => (Finset.mem_filter.mp hy).1)
          (fun y _ _ => mul_nonneg (energyOneWeight_nonneg _ _ _ _) measureReal_nonneg)
      _ ≤ _ := hremote n c r hn h5c hr x u hxB hu
  have happ := hvar n h c r hn hr hrn hlarge hc h2c hh h5c hgap x hxD hxN F
    (fun u _ => hF0 u) (fun u _ => hglobal' u) hremote'
  have hrpow : r ^ 2 ≤ n := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hn' : 2 * (r : ℝ) ^ (E + 1) ≤ n := by exact_mod_cast hlarge
    have hmon := pow_le_pow_right₀ hr1 (by omega : 2 ≤ E + 1)
    exact_mod_cast (show (r : ℝ) ^ 2 ≤ n by linarith)
  have hs := energyMean_cutoff_power_le_scale (k := E + 6) (by omega) hr hrpow
  have hxN' : latticeDistance 0 x = n := by rw [← linfDist_cast_eq_latticeDistance, hxN]
  have hhit' : a * ρ ^ (E + 6 - 3) / (n : ℝ) ^ 3 ≤ g x := by
    simpa only [show E + 6 - 3 = E + 3 by omega] using hhit
  have hb := hbranch n h c hn hc hh (by omega) hgap hcρ excluded hhex x hx hxN' r hr hs hhit'
  have hreal : 0 ≤ (percolation (E + 7) p).real (heartEvent Q H x) := measureReal_nonneg
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hreal)
  rw [show E + 6 - 3 = E + 3 by omega, show E + 6 - 5 = E + 1 by omega]
  change M * appendixVarianceSum n (heartAnnulus Q H) x g
    (fun u => ∑ y ∈ heartAnnulus Q H, energyOneWeight excluded r x y * τ u y) τ +
    J / (r : ℝ) ^ (E + 1) ≤ _
  rw [← hD]
  change M * appendixVarianceSum n D x g F τ + J / (r : ℝ) ^ (E + 1) ≤ _
  rw [add_div, mul_div_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left happ hM) le_rfl

end NearCritical.Section8
