module

public import NearCritical.AppendixVarCapstone
public import NearCritical.Section8EnergyMeanDisjoint
public import NearCritical.Section8EnergyOneInnerBranch
public import NearCritical.Section8SourceFRD

/-! Actual hitting profiles and the global ERE1 convolution input for the
Appendix variance capstone. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance
open scoped Classical

/-- The nearest-face depth is nonnegative and controlled by the separation
from the boundary root. -/
theorem variance_depth_bounds {k n c : ℕ} (x : Vertex (k + 1)) (hx : linfDist 0 x = n)
    (u : Vertex (k + 1)) (hu : u ∈ sourceAnnulus n c) :
    0 ≤ (n : ℝ) - latticeDistance 0 u ∧ (n : ℝ) - latticeDistance 0 u ≤ (linfDist x u : ℝ) := by
  have huN := mem_cube_iff_dist.mp (Finset.mem_filter.mp hu).1
  have ht := linfDist_triangle 0 u x
  rw [hx, linfDist_comm u x] at ht
  rw [← linfDist_cast_eq_latticeDistance]
  have huN' : (linfDist 0 u : ℝ) ≤ n := by exact_mod_cast huN
  have ht' : (n : ℝ) ≤ (linfDist 0 u : ℝ) + (linfDist x u : ℝ) := by exact_mod_cast ht
  constructor <;> linarith

/-- The outer hitting envelope `hgo` for the actual annulus. The heart
radius is bounded by the outer radius, so the amplitude is uniform. -/
theorem annulus_outer_profile_capstone {k : ℕ} (hk : 3 ≤ k) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ j : Fin (k + 1), HalfSpaceCriticalArmInput j B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n h c : ℕ), 1 ≤ n → 1 ≤ c → c ≤ n → h ≤ n →
      (n : ℝ) / 4 ≤ (h : ℝ) - 2 * c →
      ∀ (x : Vertex (k + 1)), linfDist 0 x = n → ∀ u ∈ capOuter n h c,
      (n : ℝ) ^ 3 * annulusG (criticalPoint (k + 1)) (centeredBox (k + 1) n) (centeredBox (k + 1) c) u ≤
        K * ((linfDist x u + 1 : ℕ) : ℝ) := by
  let K : ℝ := (2 * C) * 4 ^ k * B * (2 * ((k + 1 : ℕ) : ℝ) * 5 ^ k)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro n h c hn hc hcn hhn hgap x hx u hu
  have huAnn : u ∈ (sourceAnnulus n c : Finset (Vertex (k + 1))) := capOuter_subset hu
  have huD : u ∈ heartAnnulus (centeredBox (k + 1) n) (centeredBox (k + 1) c) :=
    (sourceAnnulus_eq_heartAnnulus k n c) ▸ huAnn
  have huout : u ∉ centeredBox (k + 1) h := by
    intro hum
    rw [← appendix_cube_eq_centeredBox] at hum
    have := mem_cube_iff_dist.mp hum
    have := (Finset.mem_filter.mp hu).2
    omega
  have hround : (c : ℝ) ≤ (1 : ℝ) * n := by rw [one_mul]; exact_mod_cast hcn
  have hhit := cube_outer_annulusG_scaled (by omega : 4 ≤ k + 1) hc hhn hgap 1 hround
    (centeredBox (k + 1) c) (Finset.Subset.refl _) u huD huout C B hC hB panis arm
  simp only [one_pow, mul_one, Nat.add_sub_cancel] at hhit
  have hdep := (variance_depth_bounds x hx u huAnn).2
  have hdep' : 1 + ((n : ℝ) - latticeDistance 0 u) ≤ ((linfDist x u + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n : ℝ) ^ 3 * (K / (n : ℝ) ^ 3 * (1 + ((n : ℝ) - latticeDistance 0 u))) :=
      mul_le_mul_of_nonneg_left hhit (by positivity)
    _ = K * (1 + ((n : ℝ) - latticeDistance 0 u)) := by field_simp [hn0.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdep' hK

/-- The actual inner hitting envelope `hgi` in the shifted Appendix notation. -/
theorem annulus_inner_profile_capstone {k : ℕ} (A : ℝ) (hA : 1 ≤ A)
    (ordinary : OrdinaryArmWindowInput (k + 1) A) (n c : ℕ) (u : Vertex (k + 1)) :
    annulusG (criticalPoint (k + 1)) (centeredBox (k + 1) n) (centeredBox (k + 1) c) u ≤
      (4 * A) / ((sourceR c u : ℝ) + 1) ^ 2 := by
  simpa only [sourceR, Nat.cast_add, Nat.cast_one] using annulusG_le_ordinary_arm (N := n) (H := c) A hA ordinary u

/-- The actual global ERE1 convolution in the shifted kernel convention. -/
theorem annulus_energyOne_convolution_shell_le {k : ℕ} (hk : 4 ≤ k) (G : ℝ) (hG : 0 ≤ G)
    (green : CriticalSupGreenUpper (k + 1) G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Q H excluded : Finset (Vertex (k + 1))) (x u : Vertex (k + 1))
      (r : ℕ), 1 ≤ r →
      (∑ y ∈ heartAnnulus Q H, energyOneWeight excluded r x y *
        annulusTau (criticalPoint (k + 1)) Q H u y) ≤
        K / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (k - 3) := by
  let F : ℝ := G * ((4 : ℝ) ^ (((k + 1 : ℕ) : ℝ) - 2) *
    (2 + 19 * (2 * ((k + 1 : ℕ) : ℝ) * 3 ^ k)))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨F * (2 : ℝ) ^ (k - 3), by positivity, ?_⟩
  intro Q H excluded x u r hr
  have hb := annulus_energyOne_convolution_le (by omega : 5 ≤ k + 1) G hG green Q H excluded x u r hr
  have hexp : (4 : ℝ) - ((k + 1 : ℕ) : ℝ) = -((k - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 3 ≤ k)]
    push_cast
    ring
  rw [hexp, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_eq_one_div, Nat.add_sub_cancel] at hb
  exact hb.trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (literal_kernel_le hr x u (k - 3)) hF)

end NearCritical.Section8
