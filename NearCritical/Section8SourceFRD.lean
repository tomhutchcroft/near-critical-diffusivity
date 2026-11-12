module
public import NearCritical.Section8SourceRDEstimate
public import NearCritical.AppendixFRDSums

/-! The literal weighted annulus sums in source lem.F_RD, at integer radii. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory AppendixVariance
open scoped Classical BigOperators

private theorem cube_norm_le {d n : ℕ} {x : Vertex d}
    (hx : x ∈ (cube n : Finset (Vertex d))) : linfDist 0 x ≤ n := by
  have hh := (mem_linfBall_iff_dist (0 : Vertex d) x (Int.natCast_nonneg n)).mp hx
  simpa using hh

/-- The shifted shell kernel controls the literal cutoff kernel. -/
theorem literal_kernel_le {d r : ℕ} (hr : 1 ≤ r)
    (x y : Vertex d) (e : ℕ) :
    (1 : ℝ)/(max (r : ℝ) (latticeDistance x y))^e ≤
      (2 : ℝ)^e/(max (r : ℝ) ((linfDist x y+1 : ℕ) : ℝ))^e := by
  let M : ℝ := max (r : ℝ) (latticeDistance x y)
  let P : ℝ := max (r : ℝ) ((linfDist x y+1 : ℕ) : ℝ)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM : 1 ≤ M := hrR.trans (le_max_left _ _)
  have hP : 0 < P := lt_of_lt_of_le (by linarith : (0 : ℝ) < r) (le_max_left _ _)
  have hPM : P ≤ 2*M := by
    apply max_le
    · have hh : (r : ℝ) ≤ M := le_max_left _ _
      linarith
    · have hh : latticeDistance x y ≤ M := le_max_right _ _
      rw [Nat.cast_add,Nat.cast_one,linfDist_cast_eq_latticeDistance]
      linarith
  have hp := pow_le_pow_left₀ hP.le hPM e
  rw [mul_pow] at hp
  change 1/M^e ≤ (2 : ℝ)^e/P^e
  apply (div_le_div_iff₀ (pow_pos (by linarith : 0 < M) e) (pow_pos hP e)).mpr
  simpa only [one_mul] using hp

private theorem scale_cube_le {n : ℕ} (hn : 1 ≤ n) :
    (2*(n : ℝ)+1)^3 ≤ 27*(n : ℝ)^3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(n : ℝ)+1)
    (by linarith : 2*(n : ℝ)+1 ≤ 3*(n : ℝ)) 3
  nlinarith only [hp]

private theorem literal_bulk_mass {d n r : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (x : Vertex d) (hx : x ∈ (cubeBoundary n : Finset (Vertex d)))
    (S : Finset (Vertex d)) (hS : S ⊆ cube n) :
    ∑ y ∈ S, (1+((n : ℝ)-latticeDistance 0 y)) /
        (max (r : ℝ) (latticeDistance x y))^(d-2) ≤
      (27*(2 : ℝ)^(d-2)*(2*(d : ℝ)*3^(d-1)))*(n : ℝ)^3 := by
  have hxC := (Finset.mem_filter.mp hx).1
  have hxN := (Finset.mem_filter.mp hx).2
  let wt : Vertex d → ℝ := fun y => 1+((n : ℝ)-latticeDistance 0 y)
  have hwt0 (y : Vertex d) (hy : y ∈ S) : 0 ≤ wt y := by
    have hh : latticeDistance 0 y ≤ n := by
      rw [← linfDist_cast_eq_latticeDistance]
      exact_mod_cast cube_norm_le (hS hy)
    dsimp [wt]
    linarith
  have hwt (y : Vertex d) (hy : y ∈ S) : wt y ≤ ((linfDist x y+1 : ℕ) : ℝ) := by
    have ht := latticeDistance_triangle (0 : Vertex d) y x
    rw [latticeDistance_comm y x,← linfDist_cast_eq_latticeDistance (0 : Vertex d) x,hxN] at ht
    dsimp [wt]
    rw [Nat.cast_add,Nat.cast_one,linfDist_cast_eq_latticeDistance]
    linarith
  have hs := frd_bulk_sum_le (r := r) hd hxC S hS wt hwt0 hwt
  calc
    _ ≤ ∑ y ∈ S, (2 : ℝ)^(d-2) *
        (wt y/(max (r : ℝ) ((linfDist x y+1 : ℕ) : ℝ))^(d-2)) := by
      apply Finset.sum_le_sum
      intro y hy
      have hh := mul_le_mul_of_nonneg_left (literal_kernel_le hr x y (d-2)) (hwt0 y hy)
      dsimp [wt] at hh ⊢
      convert hh using 1 <;> ring
    _ = (2 : ℝ)^(d-2) * ∑ y ∈ S,
        wt y/(max (r : ℝ) ((linfDist x y+1 : ℕ) : ℝ))^(d-2) := by rw [Finset.mul_sum]
    _ ≤ (2 : ℝ)^(d-2) * (2*(d : ℝ)*3^(d-1)*(2*(n : ℝ)+1)^3) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (2 : ℝ)^(d-2) * (2*(d : ℝ)*3^(d-1)*(27*(n : ℝ)^3)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (scale_cube_le hn) (by positivity)
    _ = _ := by ring

/-- Cubic mass bound for the literal ERE2 kernel on the entire cube boundary. -/
theorem literal_boundary_mass {k n r : ℕ} (hk : 3 ≤ k) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (x : Vertex (k+1)) (hx : x ∈ (cube n : Finset (Vertex (k+1)))) :
    ∑ y ∈ (cubeBoundary n : Finset (Vertex (k+1))),
      (1 : ℝ)/(max (r : ℝ) (latticeDistance x y))^(k-3) ≤
      (27*(2 : ℝ)^(k-3)*(((k : ℝ)+1)*(4*(k : ℝ)*3^(k-1))))*(n : ℝ)^3 := by
  have hs := boundary_maxr_pow_sum_le (r := r) hk hx
  calc
    _ ≤ ∑ y ∈ (cubeBoundary n : Finset (Vertex (k+1))),
        (2 : ℝ)^(k-3)/(max (r : ℝ) ((linfDist x y+1 : ℕ) : ℝ))^(k-3) :=
      Finset.sum_le_sum (fun y _ => literal_kernel_le hr x y (k-3))
    _ = (2 : ℝ)^(k-3) * ∑ y ∈ (cubeBoundary n : Finset (Vertex (k+1))),
        (1 : ℝ)/(max (r : ℝ) ((linfDist x y+1 : ℕ) : ℝ))^(k-3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ (2 : ℝ)^(k-3) * (((k : ℝ)+1)*(2*(2*(k : ℝ)*3^(k-1)*(2*(n : ℝ)+1)^3))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ((2 : ℝ)^(k-3)*(((k : ℝ)+1)*(4*(k : ℝ)*3^(k-1))))*(2*(n : ℝ)+1)^3 := by ring
    _ ≤ ((2 : ℝ)^(k-3)*(((k : ℝ)+1)*(4*(k : ℝ)*3^(k-1))))*(27*(n : ℝ)^3) :=
      mul_le_mul_of_nonneg_left (scale_cube_le hn) (by positivity)
    _ = _ := by ring

private theorem outer_mem_annulus {k n c : ℕ} (hcn : 5*c ≤ n)
    {y : Vertex (k+1)} (hy : y ∈ (cube n : Finset (Vertex (k+1))))
    (hout : 3*(n : ℝ)/4 ≤ latticeDistance 0 y) : y ∈ sourceAnnulus n c := by
  have hcR : 5*(c : ℝ) ≤ n := by exact_mod_cast hcn
  have hm : (c : ℝ) ≤ (linfDist (0 : Vertex (k+1)) y : ℝ) := by
    rw [linfDist_cast_eq_latticeDistance]
    linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  exact Finset.mem_filter.mpr ⟨hy,by exact_mod_cast hm⟩

private theorem weighted_RD_sum {k n c : ℕ} (hn : 1 ≤ n) (K L : ℝ) (hK : 0 ≤ K)
    (w : Vertex (k+1)) (S : Finset (Vertex (k+1))) (q : Vertex (k+1) → ℝ)
    (hq : ∀ y ∈ S, 0 ≤ q y)
    (hprob : ∀ y ∈ S,
      (percolation (k+1) (criticalPoint (k+1))).real
        (connectionToSetEvent ((sourceAnnulus n c : Finset (Vertex (k+1))) : Set (Vertex (k+1))) y {w}) ≤
        K*(1+((n : ℝ)-latticeDistance 0 y))*(1+(sourceR c w : ℝ))*
          (n : ℝ)^((1 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ))
    (hmass : ∑ y ∈ S, q y*(1+((n : ℝ)-latticeDistance 0 y)) ≤ L*(n : ℝ)^3) :
    ∑ y ∈ S, q y*(percolation (k+1) (criticalPoint (k+1))).real
      (connectionToSetEvent ((sourceAnnulus n c : Finset (Vertex (k+1))) : Set (Vertex (k+1))) w {y}) ≤
      (K*L)*(1+(sourceR c w : ℝ))*(n : ℝ)^((4 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ) := by
  let Z : ℝ := K*(1+(sourceR c w : ℝ))*
    (n : ℝ)^((1 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpower : (n : ℝ)^3*(n : ℝ)^((1 : ℝ)-((k+1 : ℕ) : ℝ)) =
      (n : ℝ)^((4 : ℝ)-((k+1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hnpos]
    congr 1 <;> push_cast <;> ring
  calc
    _ ≤ ∑ y ∈ S, q y*(1+((n : ℝ)-latticeDistance 0 y))*Z := by
      apply Finset.sum_le_sum
      intro y hy
      rw [connectionToSetEvent_singleton_symm _ w y]
      have hh := mul_le_mul_of_nonneg_left (hprob y hy) (hq y hy)
      convert hh using 1 <;> dsimp [Z] <;> ring
    _ = (∑ y ∈ S, q y*(1+((n : ℝ)-latticeDistance 0 y)))*Z := by rw [Finset.sum_mul]
    _ ≤ (L*(n : ℝ)^3)*Z := mul_le_mul_of_nonneg_right hmass hZ
    _ = (K*L)*(1+(sourceR c w : ℝ))*
        ((n : ℝ)^3*(n : ℝ)^((1 : ℝ)-((k+1 : ℕ) : ℝ)))/(sParam c w : ℝ) := by dsimp [Z]; ring
    _ = _ := by rw [hpower]

/-- Source F1 on the literal outer region, retaining the cutoff and diagonal.
The reciprocal natural power is exactly the source negative integer power. -/
theorem source_F1_RD_upper {k : ℕ} (hk : 3 ≤ k) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper (k+1) C)
    (arm : ∀ j : Fin (k+1), HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin (k+1), SlabBoundarySecondMomentUpper j B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n c r : ℕ, 1 ≤ n → 5*c ≤ n → 1 ≤ r →
      ∀ x w : Vertex (k+1), x ∈ cubeBoundary n → w ∈ sourceRD n c →
      (∑ y ∈ (cube n : Finset (Vertex (k+1))).filter
          (fun y => 3*(n : ℝ)/4 < latticeDistance 0 y),
        (percolation (k+1) (criticalPoint (k+1))).real
          (connectionToSetEvent ((sourceAnnulus n c : Finset (Vertex (k+1))) : Set (Vertex (k+1))) w {y}) /
          (max (r : ℝ) (latticeDistance x y))^((k+1)-2)) ≤
        K*(1+(sourceR c w : ℝ))*(n : ℝ)^((4 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ) := by
  obtain ⟨K,hK,hrd⟩ := source_RD_connection_upper C A B hC hA hB panis arm second
  let L : ℝ := 27*(2 : ℝ)^((k+1)-2)*(2*((k+1 : ℕ) : ℝ)*3^((k+1)-1))
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro n c r hn hcn hr x w hx hw
  let S := (cube n : Finset (Vertex (k+1))).filter
    (fun y => 3*(n : ℝ)/4 < latticeDistance 0 y)
  let q : Vertex (k+1) → ℝ := fun y => 1/(max (r : ℝ) (latticeDistance x y))^((k+1)-2)
  have hq (y : Vertex (k+1)) (_hy : y ∈ S) : 0 ≤ q y := by dsimp [q]; positivity
  have hmass : ∑ y ∈ S, q y*(1+((n : ℝ)-latticeDistance 0 y)) ≤ L*(n : ℝ)^3 := by
    have hh := literal_bulk_mass (by omega : 2 ≤ k+1) hn hr x hx S (Finset.filter_subset _ _)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro y _
    dsimp [q]
    ring
  have hp (y : Vertex (k+1)) (hy : y ∈ S) := hrd n c hn hcn y w
    (outer_mem_annulus hcn (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2.le)
    hw (Finset.mem_filter.mp hy).2.le
  have hh := weighted_RD_sum hn K L hK.le w S q hq hp hmass
  convert hh using 1
  apply Finset.sum_congr rfl
  intro y _
  dsimp [q]
  ring

/-- Source F2 on the actual outer cube boundary. The face-projection estimate
avoids the source's invalid uniform boundary-shell cardinality claim. -/
theorem source_F2_RD_upper {k : ℕ} (hk : 3 ≤ k) (C A B : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper (k+1) C)
    (arm : ∀ j : Fin (k+1), HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin (k+1), SlabBoundarySecondMomentUpper j B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n c r : ℕ, 1 ≤ n → 5*c ≤ n → 1 ≤ r →
      ∀ x w : Vertex (k+1), x ∈ cubeBoundary n → w ∈ sourceRD n c →
      (∑ y ∈ (cubeBoundary n : Finset (Vertex (k+1))),
        (percolation (k+1) (criticalPoint (k+1))).real
          (connectionToSetEvent ((sourceAnnulus n c : Finset (Vertex (k+1))) : Set (Vertex (k+1))) w {y}) /
          (max (r : ℝ) (latticeDistance x y))^((k+1)-4)) ≤
        K*(1+(sourceR c w : ℝ))*(n : ℝ)^((4 : ℝ)-((k+1 : ℕ) : ℝ))/(sParam c w : ℝ) := by
  obtain ⟨K,hK,hrd⟩ := source_RD_connection_upper C A B hC hA hB panis arm second
  let L : ℝ := 27*(2 : ℝ)^(k-3)*(((k : ℝ)+1)*(4*(k : ℝ)*3^(k-1)))
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro n c r hn hcn hr x w hx hw
  let S := (cubeBoundary n : Finset (Vertex (k+1)))
  let q : Vertex (k+1) → ℝ := fun y => 1/(max (r : ℝ) (latticeDistance x y))^((k+1)-4)
  have hyNorm (y : Vertex (k+1)) (hy : y ∈ S) : latticeDistance 0 y = n := by
    rw [← linfDist_cast_eq_latticeDistance,(Finset.mem_filter.mp hy).2]
  have hq (y : Vertex (k+1)) (_hy : y ∈ S) : 0 ≤ q y := by dsimp [q]; positivity
  have hmass : ∑ y ∈ S, q y*(1+((n : ℝ)-latticeDistance 0 y)) ≤ L*(n : ℝ)^3 := by
    have hh := literal_boundary_mass hk hn hr x (Finset.mem_filter.mp hx).1
    calc
      _ = ∑ y ∈ S, (1 : ℝ)/(max (r : ℝ) (latticeDistance x y))^(k-3) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hyNorm y hy]
        simp only [sub_self,add_zero,mul_one,q,show (k+1)-4 = k-3 by omega]
      _ ≤ _ := hh
  have hp (y : Vertex (k+1)) (hy : y ∈ S) := hrd n c hn hcn y w
    (outer_mem_annulus hcn (Finset.mem_filter.mp hy).1
      (by rw [hyNorm y hy]; linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])) hw (by rw [hyNorm y hy]; linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])
  have hh := weighted_RD_sum hn K L hK.le w S q hq hp hmass
  convert hh using 1
  apply Finset.sum_congr rfl
  intro y _
  dsimp [q]
  ring

end NearCritical.Section8
