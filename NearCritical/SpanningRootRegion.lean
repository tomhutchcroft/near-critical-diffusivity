module

public import NearCritical.CriticalBoxMass

/-! Actual interior root set for prop.num_spanning_new. Integer floor radii
and the existing odd-side cube convention are retained exactly. -/
@[expose] public section
noncomputable section
namespace NearCritical

def spanningRootRegion (d N : ℕ) : Finset (Vertex d) := centeredBox d (N/16)

lemma spanningRootRegion_subset (d N : ℕ) : spanningRootRegion d N ⊆ centeredBox d N := by
  simp only [spanningRootRegion, centeredBox_eq_latticeSupCube]
  exact latticeSupCube_mono d (Nat.div_le_self N 16)

/-- Uniform density of the actual floor-radius root region, including N=0.
The lower coefficient is 16^-d and is positive in every finite dimension. -/
theorem spanningRootRegion_card_bounds (d N : ℕ) :
    (1/16:ℝ)^d*(N+1:ℝ)^d ≤ ((spanningRootRegion d N).card:ℝ) ∧
      ((spanningRootRegion d N).card:ℝ) ≤ (2:ℝ)^d*(N+1:ℝ)^d := by
  have hloNat : N+1 ≤ 16*(2*(N/16)+1) := by omega
  have hhiNat : 2*(N/16)+1 ≤ 2*(N+1) := by
    have h := Nat.div_le_self N 16
    omega
  have hlo : (N+1:ℝ)/16 ≤ ((2*(N/16)+1:ℕ):ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).mpr
    have hh : N+1 ≤ (2*(N/16)+1)*16 := by
      simpa only [Nat.mul_comm] using hloNat
    exact_mod_cast hh
  have hhi : ((2*(N/16)+1:ℕ):ℝ) ≤ 2*(N+1:ℝ) := by exact_mod_cast hhiNat
  have hcard : ((spanningRootRegion d N).card:ℝ) = (((2*(N/16)+1:ℕ):ℝ))^d := by
    rw [spanningRootRegion, centeredBox_eq_latticeSupCube, card_latticeSupCube, Nat.cast_pow]
  rw [hcard]
  constructor
  · calc
      _ = ((N+1:ℝ)/16)^d := by rw [div_pow, div_pow]; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hlo d
  · calc
      _ ≤ (2*(N+1:ℝ))^d := pow_le_pow_left₀ (by positivity) hhi d
      _ = _ := mul_pow _ _ _

lemma spanningRootRegion_density_pos (d : ℕ) : 0 < (1/16:ℝ)^d := by positivity

end NearCritical
