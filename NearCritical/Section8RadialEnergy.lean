module
public import NearCritical.Section8SupPowerTail
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! The actual supremum-metric radial sum giving r^(6-d) in Section 8.
This is an analytic component, not a conditional variance assumption. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Finset
open scoped Classical

theorem mem_supCube_iff_latticeDistance {d N : ℕ} {x : Vertex d} :
    x ∈ latticeSupCube d N ↔ latticeDistance 0 x ≤ (N : ℝ) := by
  have h0 : vertexReal (0 : Vertex d) = 0 := by
    funext i
    simp [vertexReal]
  unfold latticeDistance
  rw [h0,dist_zero_left]
  constructor
  · intro hx
    apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg N)).mpr
    intro i
    change |(x i : ℝ)| ≤ (N : ℝ)
    exact_mod_cast mem_latticeSupCube.mp hx i
  · intro hx
    apply mem_latticeSupCube.mpr
    intro i
    have hi : |(x i : ℝ)| ≤ (N : ℝ) := by
      simpa [vertexReal] using (norm_le_pi_norm (vertexReal x) i).trans hx
    exact_mod_cast hi

private lemma sum_supShell_green_le {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∑ x ∈ latticeSupCube d (n+1) \ latticeSupCube d n,
      (max 1 (latticeDistance 0 x))^((2 : ℝ)-(d : ℝ)) ≤
      (2*(d : ℝ)*3^(d-1)) * (n+1 : ℝ) := by
  have h := sum_supShell_power_le (by omega : 1 ≤ d) n ((2 : ℝ)-(d : ℝ))
  have he : (d : ℝ)-1+(2-(d : ℝ)) = 1 := by ring
  simpa only [he,Real.rpow_one] using h

theorem sum_supCube_green_le {d : ℕ} (hd : 2 ≤ d) (N : ℕ) :
    ∑ x ∈ latticeSupCube d N, (max 1 (latticeDistance 0 x))^((2 : ℝ)-(d : ℝ)) ≤
      1+(2*(d : ℝ)*3^(d-1))*(N+1 : ℝ)^2 := by
  have hK : 0 ≤ 2*(d : ℝ)*3^(d-1) := by positivity
  induction N with
  | zero =>
    simp only [latticeSupCube_zero,sum_singleton,latticeDistance,dist_self,
      max_eq_left zero_le_one,Real.one_rpow,Nat.cast_zero,zero_add,one_pow,mul_one]
    linarith
  | succ N ih =>
    have hs := sum_supShell_green_le hd N
    have heq := Finset.sum_sdiff (f := fun x : Vertex d =>
      (max 1 (latticeDistance 0 x))^((2 : ℝ)-(d : ℝ)))
      (latticeSupCube_mono d (Nat.le_succ N))
    simp only [Nat.cast_add,Nat.cast_one] at *
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [mul_nonneg hK hN]

/-- The dominant radial energy sum, with explicit dimension constant and no
cutoff dependence. Includes the origin and all other diagonal contributions. -/
theorem sum_radial_energy_le {d : ℕ} (hd : 7 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (s : Finset (Vertex d)) :
    ∑ x ∈ s, (max 1 (latticeDistance 0 x))^((2 : ℝ)-(d : ℝ)) *
      (max (r : ℝ) (latticeDistance 0 x))^((4 : ℝ)-(d : ℝ)) ≤
      (1+5*(2*(d : ℝ)*3^(d-1))) * (r : ℝ)^((6 : ℝ)-(d : ℝ)) := by
  let K : ℝ := 2*(d : ℝ)*3^(d-1)
  let f : Vertex d → ℝ := fun x =>
    (max 1 (latticeDistance 0 x))^((2 : ℝ)-(d : ℝ)) *
      (max (r : ℝ) (latticeDistance 0 x))^((4 : ℝ)-(d : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hdR : (7 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ)-6 := by linarith
  have hpows : (r : ℝ)^2 * (r : ℝ)^((4 : ℝ)-(d : ℝ)) =
      (r : ℝ)^((6 : ℝ)-(d : ℝ)) := by
    have he : ((2 : ℕ) : ℝ)+((4 : ℝ)-(d : ℝ)) = (6 : ℝ)-(d : ℝ) := by norm_num <;> ring
    rw [← Real.rpow_natCast (r : ℝ) 2,← Real.rpow_add hr0,he]
  have hmass : (∑ x ∈ s ∩ latticeSupCube d r,
      (max 1 (latticeDistance 0 x))^((2 : ℝ)-(d : ℝ))) ≤ (1+4*K)*(r : ℝ)^2 := by
    calc
      _ ≤ ∑ x ∈ latticeSupCube d r, (max 1 (latticeDistance 0 x))^((2 : ℝ)-(d : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro x _hx _hxs
        positivity
      _ ≤ 1+K*(r+1 : ℝ)^2 := sum_supCube_green_le (by omega) r
      _ ≤ _ := by
        have hsquare : (r+1 : ℝ)^2 ≤ 4*(r : ℝ)^2 := by nlinarith [sq_nonneg ((r : ℝ)-1)]
        have hr2 : (1 : ℝ) ≤ (r : ℝ)^2 := by nlinarith [sq_nonneg ((r : ℝ)-1)]
        nlinarith [mul_le_mul_of_nonneg_left hsquare hK]
  have hnear : (∑ x ∈ s ∩ latticeSupCube d r, f x) ≤
      (1+4*K)*(r : ℝ)^((6 : ℝ)-(d : ℝ)) := by
    calc
      _ = (∑ x ∈ s ∩ latticeSupCube d r,
          (max 1 (latticeDistance 0 x))^((2 : ℝ)-(d : ℝ))) * (r : ℝ)^((4 : ℝ)-(d : ℝ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [f]
        rw [max_eq_left (mem_supCube_iff_latticeDistance.mp (Finset.mem_inter.mp hx).2)]
      _ ≤ ((1+4*K)*(r : ℝ)^2) * (r : ℝ)^((4 : ℝ)-(d : ℝ)) :=
        mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hr0.le _)
      _ = _ := by rw [mul_assoc,hpows]
  have hfar : (∑ x ∈ s \ latticeSupCube d r, f x) ≤
      K*(r : ℝ)^((6 : ℝ)-(d : ℝ)) := by
    have heq : (∑ x ∈ s \ latticeSupCube d r, f x) =
        ∑ x ∈ s \ latticeSupCube d r, (max 1 (latticeDistance 0 x))^((6 : ℝ)-2*(d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hRx : (r : ℝ) < latticeDistance 0 x :=
        lt_of_not_ge (fun h => (Finset.mem_sdiff.mp hx).2 (mem_supCube_iff_latticeDistance.mpr h))
      have h1x : (1 : ℝ) ≤ latticeDistance 0 x := hr1.trans hRx.le
      dsimp [f]
      simp only [max_eq_right h1x,max_eq_right hRx.le]
      rw [← Real.rpow_add (hr0.trans hRx)]
      congr 1
      ring
    rw [heq]
    have ht := sum_outside_supCube_power_le (by omega : 1 ≤ d) r hr
      ((6 : ℝ)-2*(d : ℝ)) (by linarith)
      (s \ latticeSupCube d r) (fun x hx => (Finset.mem_sdiff.mp hx).2)
    have he1 : (d : ℝ)+(6-2*(d : ℝ)) = 6-(d : ℝ) := by ring
    have he2 : -(d : ℝ)-(6-2*(d : ℝ)) = (d : ℝ)-6 := by ring
    rw [he1,he2] at ht
    exact ht.trans (div_le_self (mul_nonneg hK (Real.rpow_nonneg hr0.le _)) hd1)
  have hsplit := Finset.sum_inter_add_sum_sdiff s (latticeSupCube d r) f
  change (∑ x ∈ s, f x) ≤ (1+5*K)*(r : ℝ)^((6 : ℝ)-(d : ℝ))
  nlinarith [hnear,hfar,hsplit]

end NearCritical.Section8
