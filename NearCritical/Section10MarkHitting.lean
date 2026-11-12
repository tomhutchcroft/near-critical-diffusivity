module

public import NearCritical.Section10MarkCard
public import NearCritical.Section10HeartBounds
public import NearCritical.Section8HeartUpperScale
public import NearCritical.Section8LocalHalfSpaceGeometry

/-! Heart-hitting probability of a marked boundary point (`hhit` of
`hloss_of_energy_moments`): source cor.PxinfC, upper bound, via the verified
`Section8.cube_boundary_heart_probability_scaled` at `N = (t-1)/2`,
`H = (t-1)/32` (heart ratio at most 1/16). Constant `512 K`,
`K = 2C 2^(d-1) B 2d 5^(d-1)`. Cited inputs: the half-space two-point upper
bound and the half-space critical arm.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem typMark_hit_le {d : ℕ} (hd : 4 ≤ d) (t : ℕ) (ht : 64 ≤ t) {cc : ℝ}
    (hcc : cc ≤ 1 / 16) {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (panis : Section8.PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B)
    {x : Vertex d} (hx : x ∈ typMark t (0 : Vertex d)) :
    (percolation d (criticalPoint d)).real
      {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 cc)} ≤
      (512 * ((2 * C) * 2 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1)))) /
        (2 * (t : ℝ)) ^ 3 := by
  have ht1 : 1 ≤ t := by omega
  obtain ⟨N, hN⟩ : ∃ N, (t - 1) / 2 = N := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, (t - 1) / 32 = H := ⟨_, rfl⟩
  have hcube : typicalCube t (0 : Vertex d) = centeredBox d N := by
    rw [typicalCube_zero t ht1, hN]
  have hxb : x ∈ boundarySites (centeredBox d N) := by
    obtain ⟨f, _, hf⟩ := Finset.mem_biUnion.mp (typMark_subset_boundary t 0 hx)
    rw [typicalFace_zero t ht1 f, hN] at hf
    unfold signedCubeFace at hf
    obtain ⟨hfb, hfe⟩ := Finset.mem_filter.mp hf
    refine (Section8.mem_centeredBox_boundary_iff x).mpr ⟨hfb, f.1, ?_⟩
    cases hs : f.2
    · rw [hs] at hfe
      exact Or.inr (by simpa using hfe)
    · rw [hs] at hfe
      exact Or.inl (by simpa using hfe)
  have hheart : typicalHeart t (0 : Vertex d) cc ⊆ centeredBox d H := by
    rw [← hH]
    exact heart_subset_rootRegion t ht1 hcc
  have h := Section8.cube_boundary_heart_probability_scaled hd (show 1 ≤ H by omega)
    (show 4 * H ≤ N by omega) _ hheart x hxb C B hC hB panis arm
  rw [hcube]
  refine h.trans ?_
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * C) * 2 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1)) :=
    ⟨_, rfl⟩
  rw [← hK]
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have htpos : (0:ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hHN : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show H ≤ N by omega)
  have hpow : (H : ℝ) ^ (d - 4) ≤ (N : ℝ) ^ (d - 4) :=
    pow_le_pow_left₀ (Nat.cast_nonneg H) hHN _
  have hp : (N : ℝ) ^ (d - 1) = (N : ℝ) ^ (d - 4) * (N : ℝ) ^ 3 := by
    rw [← pow_add]
    congr 1
    omega
  have ht8 : 2 * (t : ℝ) ≤ 8 * (N : ℝ) := by
    exact_mod_cast (show 2 * t ≤ 8 * N by omega)
  have h8 : (2 * (t : ℝ)) ^ 3 ≤ (8 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) ht8 3
  calc K * (H : ℝ) ^ (d - 4) / (N : ℝ) ^ (d - 1)
      ≤ K * (N : ℝ) ^ (d - 4) / (N : ℝ) ^ (d - 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK0) (by positivity)
    _ = K / (N : ℝ) ^ 3 := by
        rw [hp]
        field_simp
    _ ≤ 512 * K / (2 * (t : ℝ)) ^ 3 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left h8 hK0
        linarith [show K * (8 * (N : ℝ)) ^ 3 = 512 * K * (N : ℝ) ^ 3 by ring]

end NearCritical.Section10
