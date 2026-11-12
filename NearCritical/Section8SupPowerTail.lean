module
public import NearCritical.LatticePowerTail
public import NearCritical.ThreePointDiagram

/-! Direct supremum-metric shell estimates for Section 8. Negative powers
cannot be bounded above using only sup distance ≤ Euclidean distance. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Finset
open scoped Classical

/-- The source supremum distance is exactly n+1 on the integer cube shell. -/
theorem latticeDistance_on_supShell {d n : ℕ} {x : Vertex d}
    (hx : x ∈ latticeSupCube d (n+1) \ latticeSupCube d n) :
    latticeDistance 0 x = (n+1 : ℝ) := by
  have h0 : vertexReal (0 : Vertex d) = 0 := by
    funext i
    simp [vertexReal]
  unfold latticeDistance
  rw [h0,dist_zero_left]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ n+1)).mpr
    intro i
    change |(x i : ℝ)| ≤ (n+1 : ℝ)
    exact_mod_cast mem_latticeSupCube.mp (mem_sdiff.mp hx).1 i
  · have hout := (mem_sdiff.mp hx).2
    rw [mem_latticeSupCube] at hout
    push Not at hout
    obtain ⟨i,hi⟩ := hout
    have hi' : (n+1 : ℝ) ≤ |(x i : ℝ)| := by
      have hz : (n : ℤ)+1 ≤ |x i| := by omega
      exact_mod_cast hz
    exact hi'.trans (by simpa [vertexReal] using norm_le_pi_norm (vertexReal x) i)

/-- Surface-order counting for the actual regularized supremum kernel.
The exponent may have either sign since the shell radius is exact. -/
theorem sum_supShell_rpow_le (d n : ℕ) (a : ℝ) :
    ∑ x ∈ latticeSupCube d (n+1) \ latticeSupCube d n,
      (max 1 (latticeDistance 0 x)) ^ a ≤
      (2*d*(2*n+3)^(d-1) : ℕ) * (n+1 : ℝ)^a := by
  calc
    _ = ∑ _x ∈ latticeSupCube d (n+1) \ latticeSupCube d n, (n+1 : ℝ)^a := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [latticeDistance_on_supShell hx,max_eq_right (by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith : (1 : ℝ) ≤ n+1)]
    _ = ((latticeSupCube d (n+1) \ latticeSupCube d n).card : ℝ) * (n+1 : ℝ)^a := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_latticeSupShell_le d n)
      (Real.rpow_nonneg (by positivity) _)

theorem sum_supShell_power_le {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (a : ℝ) :
    ∑ x ∈ latticeSupCube d (n+1) \ latticeSupCube d n,
      (max 1 (latticeDistance 0 x)) ^ a ≤
      (2*(d : ℝ)*3^(d-1)) * (n+1 : ℝ)^((d : ℝ)-1+a) := by
  calc
    _ ≤ (2*d*(2*n+3)^(d-1) : ℕ) * (n+1 : ℝ)^a := sum_supShell_rpow_le d n a
    _ ≤ (2*d*(3*(n+1))^(d-1) : ℕ) * (n+1 : ℝ)^a := by
      gcongr
      omega
    _ = (2*(d : ℝ)*3^(d-1)) * ((n+1 : ℝ)^(d-1) * (n+1 : ℝ)^a) := by
      push_cast
      rw [mul_pow]
      ring
    _ = _ := by
      rw [← Real.rpow_natCast (n+1 : ℝ) (d-1),← Real.rpow_add (by positivity),
        Nat.cast_sub hd,Nat.cast_one]

theorem sum_cube_sdiff_sup_power_le {d : ℕ} (hd : 1 ≤ d) (N M : ℕ) (a : ℝ) :
    ∑ x ∈ latticeSupCube d (N+M) \ latticeSupCube d N,
      (max 1 (latticeDistance 0 x)) ^ a ≤
      (2*(d : ℝ)*3^(d-1)) * ∑ k ∈ range M, (N+k+1 : ℝ)^((d : ℝ)-1+a) := by
  let f : Vertex d → ℝ := fun x => (max 1 (latticeDistance 0 x))^a
  have hm : Monotone (fun k => latticeSupCube d (N+k)) := by
    intro j k hjk
    exact latticeSupCube_mono d (Nat.add_le_add_left hjk N)
  have heq := Finset.sum_eq_sum_range_sdiff (fun k => latticeSupCube d (N+k)) hm f M
  have hs := Finset.sum_sdiff (f := f) (latticeSupCube_mono d (Nat.le_add_right N M))
  simp only [Nat.add_zero,← Nat.add_assoc] at heq
  calc
    _ = ∑ k ∈ range M, ∑ x ∈ latticeSupCube d (N+k+1) \ latticeSupCube d (N+k), f x := by
      change (∑ x ∈ latticeSupCube d (N+M) \ latticeSupCube d N, f x) = _
      linarith
    _ ≤ ∑ k ∈ range M, (2*(d : ℝ)*3^(d-1)) * (N+k+1 : ℝ)^((d : ℝ)-1+a) := by
      apply Finset.sum_le_sum
      intro k _hk
      simpa only [Nat.cast_add,Nat.cast_one,f] using sum_supShell_power_le hd (N+k) a
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A genuine finite-subset supremum-power tail, uniform in the cutoff set.
This supplies radial tails for F1 and the Section 8 weighted diagram sums. -/
theorem sum_outside_supCube_power_le {d : ℕ} (hd : 1 ≤ d)
    (N : ℕ) (hN : 1 ≤ N) (a : ℝ) (ha : a < -(d : ℝ))
    (s : Finset (Vertex d)) (hs : ∀ x ∈ s, x ∉ latticeSupCube d N) :
    ∑ x ∈ s, (max 1 (latticeDistance 0 x))^a ≤
      (2*(d : ℝ)*3^(d-1)) * (N : ℝ)^((d : ℝ)+a) / (-(d : ℝ)-a) := by
  obtain ⟨M,hM⟩ := exists_subset_latticeSupCube s
  have hK : 0 ≤ 2*(d : ℝ)*3^(d-1) := by positivity
  have he : (d : ℝ)-1+a < -1 := by linarith
  have hsum : Summable (fun k : ℕ => (N+k+1 : ℝ)^((d : ℝ)-1+a)) := by
    have hbase := (Real.summable_nat_rpow.mpr he).comp_injective
      (show Function.Injective (fun k : ℕ => N+k+1) from by
        intro j k hjk
        dsimp at hjk
        omega)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using hbase
  calc
    _ ≤ ∑ x ∈ latticeSupCube d (N+M) \ latticeSupCube d N,
        (max 1 (latticeDistance 0 x))^a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact mem_sdiff.mpr ⟨latticeSupCube_mono d (Nat.le_add_left M N) (hM hx),hs x hx⟩
      · intro x _hx _hxs
        positivity
    _ ≤ _ := (sum_cube_sdiff_sup_power_le hd N M a).trans (by
      calc
        _ ≤ (2*(d : ℝ)*3^(d-1)) * ∑' k : ℕ, (N+k+1 : ℝ)^((d : ℝ)-1+a) :=
          mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun k _hk => by positivity)) hK
        _ ≤ (2*(d : ℝ)*3^(d-1)) *
            ((N : ℝ)^(((d : ℝ)-1+a)+1) / (-((d : ℝ)-1+a)-1)) :=
          mul_le_mul_of_nonneg_left (nat_rpow_tail_le N hN _ he) hK
        _ = _ := by
          rw [show ((d : ℝ)-1+a)+1 = (d : ℝ)+a by ring,
            show -((d : ℝ)-1+a)-1 = -(d : ℝ)-a by ring]
          ring)

end NearCritical.Section8
