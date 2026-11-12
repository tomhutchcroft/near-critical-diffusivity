module

public import NearCritical.Section10CubeRemainder
public import NearCritical.FullGridSubadditivity
public import NearCritical.CenteredGridTemplate

/-! Exact fixed-block comparison for Section10's all-radius mean limit.
The uncovered BASE SITES have volume n^d-(floor(n/k)*k)^d. This comparison
uses the actual full issued network and does not assert domain monotonicity. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

def positiveCube (d n : ℕ) : Finset (Vertex d) :=
  latticeRectangle 0 (fun _ => (n:ℤ)-1)

theorem card_positiveCube (d n : ℕ) : (positiveCube d n).card = n^d := by
  have hc : (Finset.Icc (0:ℤ) ((n:ℤ)-1)).card = n := by
    rw [Int.card_Icc]
    omega
  unfold positiveCube latticeRectangle
  rw [Fintype.card_piFinset]
  simp only [Pi.zero_apply,hc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem annealedFull_positiveCube_odd {d : ℕ} (r : ℕ) (p : unitInterval) (i : Fin d) :
    annealedFull (positiveCube d (2*r+1)) i (p:ℝ) =
      annealedFull (centeredBox d r) i (p:ℝ) := by
  have hzero : (fun _ : Fin d => (0:ℤ)) = (0:Vertex d) := by
    funext j
    simp only [Pi.zero_apply]
  have heq : positiveCube d (2*r+1) = gridCell (oddGridWidths (fun _ : Fin d => r)) 0 := by
    simp only [positiveCube,gridCell,oddGridWidths,Pi.zero_apply,zero_mul,zero_add,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,hzero]
  rw [heq,annealedFull_odd_grid_centered]
  rfl

/-- Replicate a fixed k-block inside an n-cube; the exact uncovered volume
controls the difference of actual means. The block size is fixed before n. -/
theorem annealedFull_positiveCube_block_comparison {d : ℕ} (i : Fin d) (p : unitInterval)
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    annealedFull (positiveCube d n) i (p:ℝ) ≤
      annealedFull (positiveCube d k) i (p:ℝ) +
        ((n:ℝ)^d-((n/k*k:ℕ):ℝ)^d)/(n:ℝ)^d := by
  let m := n/k*k
  have hq : 0 < n/k := Nat.div_pos hkn hk
  have hm : 0 < m := Nat.mul_pos hq hk
  have hmn : m ≤ n := Nat.div_mul_le_self n k
  have hvalid : ∀ j : Fin d, (0:Vertex d) j ≤ (m:ℤ)-1 := by
    intro j
    change (0:ℤ) ≤ (m:ℤ)-1
    omega
  have hsub : positiveCube d m ⊆ positiveCube d n := by
    intro x hx
    apply mem_latticeRectangle.mpr
    intro j
    have hxj := mem_latticeRectangle.mp hx j
    have hmnZ : (m:ℤ) ≤ (n:ℤ) := by exact_mod_cast hmn
    constructor
    · exact hxj.1
    · change x j ≤ (n:ℤ)-1
      have hh : x j ≤ (m:ℤ)-1 := hxj.2
      omega
  have hg : annealedFull (positiveCube d m) i (p:ℝ) ≤
      annealedFull (positiveCube d k) i (p:ℝ) := by
    have hw (j : Fin d) : (0:ℤ) < (k:ℤ) := by exact_mod_cast hk
    have hN (j : Fin d) : (0:ℤ) < ((n/k:ℕ):ℤ) := by exact_mod_cast hq
    have h := annealedFull_grid_subadditivity i (fun _ : Fin d => (k:ℤ))
      (fun _ : Fin d => ((n/k:ℕ):ℤ)) hw hN p
    have hzero : (fun _ : Fin d => (0:ℤ)) = (0:Vertex d) := by
      funext j
      simp only [Pi.zero_apply]
    simpa only [positiveCube,gridCell,Pi.zero_apply,zero_mul,zero_add,Nat.cast_mul,m,hzero] using h
  have hb := annealedFull_rectangle_remainder_fraction (positiveCube d n) 0
    (fun _ : Fin d => (m:ℤ)-1) hvalid hsub p i
  change annealedFull (positiveCube d n) i (p:ℝ) ≤
    annealedFull (positiveCube d m) i (p:ℝ) +
      (((positiveCube d n) \ (positiveCube d m)).card:ℝ)/((positiveCube d n).card:ℝ) at hb
  have hrem : (((positiveCube d n) \ (positiveCube d m)).card:ℝ)/
      ((positiveCube d n).card:ℝ) = ((n:ℝ)^d-(m:ℝ)^d)/(n:ℝ)^d := by
    rw [Finset.card_sdiff_of_subset hsub,Nat.cast_sub (Finset.card_le_card hsub)]
    simp only [card_positiveCube,Nat.cast_pow]
  rw [hrem] at hb
  exact hb.trans (add_le_add hg (le_refl _))

/-- The same comparison on actual centered odd cubes, with exact fractional
remainder. No limit or normalized-conductivity domain monotonicity is used. -/
theorem annealedFull_centeredCube_block_comparison {d : ℕ} (i : Fin d) (p : unitInterval)
    (r s : ℕ) (hsr : 2*s+1 ≤ 2*r+1) :
    annealedFull (centeredBox d r) i (p:ℝ) ≤ annealedFull (centeredBox d s) i (p:ℝ) +
      (1-((((2*r+1)/(2*s+1)*(2*s+1):ℕ):ℝ)/(2*(r:ℝ)+1))^d) := by
  have hn : (2*(r:ℝ)+1) ≠ 0 := by positivity
  have hb := annealedFull_positiveCube_block_comparison i p (by omega : 0 < 2*s+1) hsr
  rw [annealedFull_positiveCube_odd,annealedFull_positiveCube_odd] at hb
  have heq : (((2*r+1:ℕ):ℝ)^d-
      (((2*r+1)/(2*s+1)*(2*s+1):ℕ):ℝ)^d)/((2*r+1:ℕ):ℝ)^d =
      1-((((2*r+1)/(2*s+1)*(2*s+1):ℕ):ℝ)/(2*(r:ℝ)+1))^d := by
    push_cast
    rw [div_pow]
    field_simp [hn]
    <;> ring
  rwa [heq] at hb

end NearCritical.Section10
