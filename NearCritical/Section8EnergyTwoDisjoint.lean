module

public import NearCritical.Section8EnergyKernelIdentity
public import NearCritical.Section8FiveDiagrams
public import NearCritical.Section8HeartUpperScale
public import NearCritical.Section8SourceFRD

/-! The disjoint-path contribution to the second conditional energy mean. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

/-- The disjoint-path term for ERE2, after cancellation of the conditioning
probability. The full cube boundary is used, including the diagonal. -/
theorem energyTwo_disjoint_sum_le {k n H : ℕ} (hk : 3 ≤ k)
    (hH : 1 ≤ H) (hHn : 4 * H ≤ n) (ρ : ℝ) (hρ : 0 ≤ ρ) (hround : (H : ℝ) ≤ ρ * n)
    (heart : Finset (Vertex (k + 1))) (hheart : heart ⊆ centeredBox (k + 1) H)
    (x : Vertex (k + 1)) (hx : x ∈ centeredBox (k + 1) n) (r : ℕ) (hr : 1 ≤ r)
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (panis : PanisHalfSpaceTwoPointUpper (k + 1) C)
    (arm : ∀ i : Fin (k + 1), HalfSpaceCriticalArmInput i B) :
    ∑ y ∈ heartAnnulus (centeredBox (k + 1) n) heart,
        energyTwoWeight (cubeBoundary n) r x y *
          annulusG (criticalPoint (k + 1)) (centeredBox (k + 1) n) heart y ≤
      (((2 * C) * 2 ^ k * B * (2 * ((k : ℝ) + 1) * 5 ^ k)) *
        (27 * (2 : ℝ) ^ (k - 3) * (((k : ℝ) + 1) * (4 * (k : ℝ) * 3 ^ (k - 1))))) *
        ρ ^ (k - 3) := by
  let Q := centeredBox (k + 1) n
  let K : ℝ := (2 * C) * 2 ^ k * B * (2 * ((k : ℝ) + 1) * 5 ^ k)
  let A : ℝ := 27 * (2 : ℝ) ^ (k - 3) * (((k : ℝ) + 1) * (4 * (k : ℝ) * 3 ^ (k - 1)))
  let w := energyTwoWeight (cubeBoundary n) r x
  have hn : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hHQ : heart ⊆ Q := by
    intro y hy
    apply mem_centeredBox.mpr
    intro j
    have hj := mem_centeredBox.mp (hheart hy) j
    constructor <;> omega
  have hmass : ∑ y ∈ Q, w y ≤ A * (n : ℝ) ^ 3 := by
    have heq := energyTwoWeight_sum_eq_literal (n := n) (by omega : 4 ≤ k + 1)
      r x (fun _ => 1)
    simp only [mul_one, show k + 1 - 4 = k - 3 by omega] at heq
    rw [← appendix_cube_eq_centeredBox (k + 1) n] at hx
    change (∑ y ∈ centeredBox (k + 1) n, energyTwoWeight (cubeBoundary n) r x y) ≤ _
    rw [← appendix_cube_eq_centeredBox (k + 1) n, heq]
    exact literal_boundary_mass hk hn hr x hx
  change (∑ y ∈ heartAnnulus Q heart, w y * annulusG (criticalPoint (k + 1)) Q heart y) ≤ _
  calc
    _ ≤ ∑ y ∈ heartAnnulus Q heart, w y * (K * ρ ^ (k - 3) / (n : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hyb : y ∈ (cubeBoundary n : Finset (Vertex (k + 1)))
      · have hy' : y ∈ boundarySites Q :=
          (centeredBox_boundary_norm_iff y).mpr (Finset.mem_filter.mp hyb).2
        have hhit := cube_boundary_heart_probability_rho_le (by omega : 4 ≤ k + 1)
          hH hHn ρ hρ hround heart hheart y hy' C B hC hB panis arm
        have hevent : heartEvent Q heart y = {ω | y ∈ heartClusterUnion ω Q heart} := by
          ext ω
          exact heartEvent_iff_union_member _ _ hHQ y ω
        rw [annulusG, annulusHit, ← heart_probability_eq_annulus _ _ _ y hy, hevent]
        apply mul_le_mul_of_nonneg_left _ (energyTwoWeight_nonneg _ _ _ _)
        simpa only [K, Nat.cast_add, Nat.cast_one,
          show k + 1 - 4 = k - 3 by omega, Nat.add_sub_cancel] using hhit
      · simp [w, energyTwoWeight, hyb]
    _ = (∑ y ∈ heartAnnulus Q heart, w y) * (K * ρ ^ (k - 3) / (n : ℝ) ^ 3) := by
      rw [Finset.sum_mul]
    _ ≤ (A * (n : ℝ) ^ 3) * (K * ρ ^ (k - 3) / (n : ℝ) ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (Finset.sum_le_sum_of_subset_of_nonneg (heartAnnulus_subset Q heart)
        (fun y _ _ => energyTwoWeight_nonneg _ _ _ y)).trans hmass
    _ = _ := by field_simp <;> ring

end NearCritical.Section8
