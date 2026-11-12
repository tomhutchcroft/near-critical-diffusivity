module

public import NearCritical.AppendixVarTerm4AllDimensions
public import NearCritical.Section8EnergyMeanDisjoint
public import NearCritical.Section8EnergyMeanScale
public import NearCritical.Section8EnergyOneInnerBranch
public import NearCritical.Section8SourceFRD

/-! The fourth ERE1 variance term with the actual annulus weights. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

/-- The fourth ERE1 term, after the conditioning probability cancels, has
the required cutoff decay in all dimensions `d ≥ 9`. -/
theorem energyOne_variance_term_four_le {k : ℕ} (hk : 8 ≤ k)
    (C B G A : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i B)
    (green : CriticalSupGreenUpper (k + 1) G) (ordinary : OrdinaryArmWindowInput (k + 1) A)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N L H : ℕ), 1 ≤ N → 1 ≤ H → 2 * L ≤ N → H ≤ L →
      (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H → (H : ℝ) ≤ ρ * N →
      ∀ (excluded : Finset (Vertex (k + 1))),
      let Q := centeredBox (k + 1) N
      let heart := centeredBox (k + 1) H
      let D := heartAnnulus Q heart
      let p := criticalPoint (k + 1)
      ∀ x ∈ D, latticeDistance 0 x = N → ∀ r : ℕ, 1 ≤ r → r ^ 2 ≤ N →
      ∑ u ∈ D, annulusG p Q heart u *
        (∑ y ∈ D, energyOneWeight excluded r x y * annulusTau p Q heart u y) ^ 2 ≤
        K / (r : ℝ) ^ (k - 5) := by
  let d := k + 1
  let CF : ℝ := G * ((4 : ℝ) ^ ((d : ℝ) - 2) * (2 + 19 * (2 * (d : ℝ) * 3 ^ (d - 1))))
  let Cg : ℝ := ((2 * C) * 4 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1))) * ρ ^ (k - 3)
  let S : ℝ := (4 * A) * (2 * (d : ℝ) * 3 ^ k)
  let Ki : ℝ := 4 * S * CF ^ 2
  let Cin : ℝ := Ki * ((3 : ℝ) ^ k + (2 : ℝ) ^ (k - 1)) * (2 : ℝ) ^ (2 * k - 3)
  let Cout : ℝ := Cg * (CF * (2 : ℝ) ^ (k - 3)) ^ 2
  have hCF : 0 ≤ CF := by dsimp [CF]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hKi : 0 ≤ Ki := by dsimp [Ki]; positivity
  have hCin : 0 ≤ Cin := by dsimp [Cin]; positivity
  have hCout : 0 ≤ Cout := by dsimp [Cout]; positivity
  refine ⟨Cout * (3 * (2 * (d : ℝ) * 3 ^ (d - 1) *
    ((((d - 8 : ℕ) : ℝ) + 1) / ((d - 8 : ℕ) : ℝ)))) + Cin, by positivity, ?_⟩
  intro N L H hN hH hL hHL hgap hround excluded Q heart D p x hx hxN r hr hrsq
  let outer := D.filter (fun u => u ∉ centeredBox d L)
  let g := annulusG p Q heart
  let F (u : Vertex d) := ∑ y ∈ D, energyOneWeight excluded r x y * annulusTau p Q heart u y
  let M : ℝ := (N : ℝ) / 2
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 0 < M := by dsimp [M]; positivity
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast (show 9 ≤ d by dsimp [d]; omega)
  have hLN : L ≤ N := by omega
  have hrN : r ≤ N := (by simpa only [pow_two, one_mul] using Nat.mul_le_mul_right r hr : r ≤ r ^ 2).trans hrsq
  have hF (u : Vertex d) : F u ≤ CF * (max (r : ℝ) (latticeDistance x u)) ^ ((4 : ℝ) - d) :=
    annulus_energyOne_convolution_le (by dsimp [d]; omega : 5 ≤ d) G hG green Q heart excluded x u r hr
  have hF0 (u : Vertex d) : 0 ≤ F u := Finset.sum_nonneg fun y _ =>
    mul_nonneg (energyOneWeight_nonneg _ _ _ _) measureReal_nonneg
  have hg0 (u : Vertex d) : 0 ≤ g u := measureReal_nonneg
  have houter_pt (u : Vertex d) (hu : u ∈ outer) :
      g u * F u ^ 2 ≤ Cout * ((N : ℝ) ^ 3)⁻¹ *
        (((linfDist x u + 1 : ℕ) : ℝ) / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (2 * d - 8)) := by
    obtain ⟨huD, huL⟩ := Finset.mem_filter.mp hu
    let s : ℝ := (linfDist x u + 1 : ℕ)
    let m := max (r : ℝ) s
    have hdep : 1 + ((N : ℝ) - latticeDistance 0 u) ≤ s := by
      have h := latticeDistance_triangle 0 u x
      rw [hxN, latticeDistance_comm u x] at h
      dsimp [s]
      rw [Nat.cast_add, Nat.cast_one, linfDist_cast_eq_latticeDistance]
      linarith
    have hhit := cube_outer_annulusG_scaled (by dsimp [d]; omega : 4 ≤ d) hH hLN hgap ρ hround
      heart (Finset.Subset.refl _) u huD huL C B hC hB panis arm
    have hg' : g u ≤ Cg / (N : ℝ) ^ 3 * s := by
      refine hhit.trans ?_
      simpa only [Cg, d, Nat.add_sub_cancel, show k + 1 - 4 = k - 3 by omega] using
        mul_le_mul_of_nonneg_left hdep (show 0 ≤ Cg / (N : ℝ) ^ 3 by positivity)
    have hFR := hF u
    have hexp : (4 : ℝ) - (d : ℝ) = -((k - 3 : ℕ) : ℝ) := by
      dsimp [d]
      rw [Nat.cast_sub (by omega : 3 ≤ k)]
      push_cast
      ring
    rw [hexp, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_eq_one_div] at hFR
    have hFF : F u ≤ (CF * (2 : ℝ) ^ (k - 3)) / m ^ (k - 3) := by
      refine hFR.trans ?_
      have h := mul_le_mul_of_nonneg_left (literal_kernel_le hr x u (k - 3)) hCF
      simpa only [m, s, mul_div_assoc] using h
    calc
      _ ≤ (Cg / (N : ℝ) ^ 3 * s) * ((CF * (2 : ℝ) ^ (k - 3)) / m ^ (k - 3)) ^ 2 :=
        mul_le_mul hg' (pow_le_pow_left₀ (hF0 u) hFF _) (by positivity) (by positivity)
      _ = _ := by
        change _ = Cout * ((N : ℝ) ^ 3)⁻¹ * (s / m ^ (2 * d - 8))
        rw [show 2 * d - 8 = (k - 3) * 2 by dsimp [d]; omega, pow_mul, div_pow]
        dsimp [Cout]
        ring
  have hinner : ∑ u ∈ D \ outer, g u * F u ^ 2 ≤ Cin / (r : ℝ) ^ (k - 5) := by
    have hset : D \ outer = D ∩ centeredBox d L := by
      ext u
      simp only [outer, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_inter]
      tauto
    rw [hset]
    have hFinner (u : Vertex d) (hu : u ∈ D ∩ centeredBox d L) : F u ≤ CF * M ^ ((4 : ℝ) - d) := by
      have huL := (Finset.mem_inter.mp hu).2
      have huNorm : latticeDistance 0 u ≤ (L : ℝ) := by
        rw [← linfDist_cast_eq_latticeDistance]
        rw [← appendix_cube_eq_centeredBox] at huL
        have h := (mem_linfBall_iff_dist (0 : Vertex d) u (Int.natCast_nonneg L)).mp huL
        exact_mod_cast (show linfDist 0 u ≤ L by simpa only [Int.toNat_natCast] using h)
      have htri := latticeDistance_triangle 0 u x
      rw [hxN, latticeDistance_comm u x] at htri
      have hL' : 2 * (L : ℝ) ≤ N := by exact_mod_cast hL
      have hgap' : M ≤ latticeDistance x u := by dsimp [M]; linarith
      exact (hF u).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hM (hgap'.trans (le_max_right _ _)) (by linarith)) hCF)
    have hmass := inner_annulus_hit_sum_le (N := N) (H := H) (L := L) (by omega : 2 ≤ k) A hA ordinary
    let V : ℝ := (2 * (H : ℝ) + 1) ^ k + ((L : ℝ) + 1) ^ (k - 1)
    have hmass' : (∑ u ∈ D ∩ centeredBox d L, g u) ≤ S * (4 * V) :=
      hmass.trans (mul_le_mul_of_nonneg_left (by dsimp [V]; linarith [show 0 ≤ (2 * (H : ℝ) + 1) ^ k by positivity]) hS)
    have hsq : (CF * M ^ ((4 : ℝ) - d)) ^ 2 = CF ^ 2 * M ^ ((8 : ℝ) - 2 * d) := by
      rw [mul_pow, pow_two (M ^ ((4 : ℝ) - d)), ← Real.rpow_add hM,
        show (4 : ℝ) - d + (4 - d) = 8 - 2 * d by ring]
    have hscale : M ^ ((8 : ℝ) - 2 * d) ≤ M ^ ((5 : ℝ) - 2 * d) / (1 / (N : ℝ) ^ 3) := by
      have hcub : (N : ℝ) ^ 3 = 8 * M ^ (3 : ℝ) := by
        rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
        dsimp [M]
        ring
      have heq : M ^ ((5 : ℝ) - 2 * d) * M ^ (3 : ℝ) = M ^ ((8 : ℝ) - 2 * d) := by
        rw [← Real.rpow_add hM, show (5 : ℝ) - 2 * d + 3 = 8 - 2 * d by ring]
      calc
        _ ≤ 8 * M ^ ((8 : ℝ) - 2 * d) := by linarith [show 0 ≤ M ^ ((8 : ℝ) - 2 * d) by positivity]
        _ = _ := by rw [div_one_div, hcub, ← heq]; ring
    have hrscale := energyMean_cutoff_power_le_scale (by omega : 7 ≤ k) hr hrsq
    calc
      _ ≤ ∑ u ∈ D ∩ centeredBox d L, g u * (CF * M ^ ((4 : ℝ) - d)) ^ 2 :=
        Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hF0 u) (hFinner u hu) _) (hg0 u)
      _ = (∑ u ∈ D ∩ centeredBox d L, g u) * (CF * M ^ ((4 : ℝ) - d)) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ S * (4 * V) * (CF * M ^ ((4 : ℝ) - d)) ^ 2 := mul_le_mul_of_nonneg_right hmass' (by positivity)
      _ = Ki * V * M ^ ((8 : ℝ) - 2 * d) := by rw [hsq]; dsimp [Ki]; ring
      _ ≤ Ki * V * (M ^ ((5 : ℝ) - 2 * d) / (1 / (N : ℝ) ^ 3)) := mul_le_mul_of_nonneg_left hscale (by dsimp [V]; positivity)
      _ = (Ki * (V * M ^ ((5 : ℝ) - 2 * d))) / (1 / (N : ℝ) ^ 3) := by ring
      _ ≤ Cin / (N : ℝ) ^ (k - 6) := by
        simpa only [V, M, d, Cin, one_pow, mul_one, div_one] using
          energyMean_inner_remainder_le (by omega : 7 ≤ k) hN (hHL.trans hLN) hLN Ki 1 1 hKi one_pos one_pos
      _ ≤ _ := div_le_div_of_nonneg_left hCin (by positivity) hrscale
  have houter_sub : outer ⊆ D := Finset.filter_subset _ _
  have hxQ : x ∈ (cube N : Finset (Vertex d)) := by
    rw [appendix_cube_eq_centeredBox]
    exact heartAnnulus_subset Q heart hx
  have houter_ball : outer ⊆ linfBall x ((2 * N : ℕ) : ℤ) := by
    apply houter_sub.trans ((heartAnnulus_subset Q heart).trans ?_)
    change centeredBox d N ⊆ _
    rw [← appendix_cube_eq_centeredBox]
    exact cube_subset_linfBall_two hxQ
  have hexp : d - 6 = k - 5 := by dsimp [d]; omega
  simpa only [hexp] using var_term_4_all_dimensions (by dsimp [d]; omega : 9 ≤ d) x hr hrN D outer g F
    Cout Cin hCout houter_sub houter_ball houter_pt (by simpa only [hexp] using hinner)

end NearCritical.Section8
