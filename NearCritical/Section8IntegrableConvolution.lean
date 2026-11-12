module
public import NearCritical.Section8Convolution

/-! Integrable squared-bubble kernels in the original-overlap variance diagram. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical BigOperators

/-- The squared fourth-order kernel has uniformly bounded mass over every
finite cutoff in dimensions at least nine, including its diagonal. -/
theorem sum_squared_fourth_kernel_le {d : ℕ} (hd : 9 ≤ d)
    (s : Finset (Vertex d)) (u : Vertex d) :
    ∑ v ∈ s, (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ)) ≤
      1+5*(2*(d : ℝ)*3^(d-1)) := by
  let K : ℝ := 2*(d : ℝ)*3^(d-1)
  let N := s.filter (fun v => latticeDistance u v ≤ 1)
  let F := s.filter (fun v => 1 < latticeDistance u v)
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hnear : (∑ v ∈ N, (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ))) ≤ 1+4*K := by
    calc
      _ ≤ ∑ v ∈ N, (max 1 (latticeDistance u v))^((2 : ℝ)-(d : ℝ)) := by
        apply Finset.sum_le_sum
        intro v _
        exact Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)
      _ ≤ _ := by
        have ht := sum_green_ball_le (by omega : 2 ≤ d) 1 N u
          (fun v hv => by simpa only [Nat.cast_one] using (Finset.mem_filter.mp hv).2)
        convert ht using 1 <;> norm_num [K] <;> ring
  have hfar : (∑ v ∈ F, (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ))) ≤ K := by
    have ht := sum_power_tail_ball_le (by omega : 1 ≤ d) 1 (by omega)
      ((8 : ℝ)-2*(d : ℝ)) (by linarith) F u
      (fun v hv => by simpa only [Nat.cast_one] using (Finset.mem_filter.mp hv).2)
    simp only [Nat.cast_one,Real.one_rpow,mul_one] at ht
    have he : -(d : ℝ)-((8 : ℝ)-2*(d : ℝ)) = (d : ℝ)-8 := by ring
    rw [he] at ht
    exact ht.trans (div_le_self hK (by linarith : (1 : ℝ) ≤ (d : ℝ)-8))
  have hsplit : (∑ v ∈ s, (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ))) =
      (∑ v ∈ N, (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ))) +
      (∑ v ∈ F, (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ))) := by
    simp only [N,F,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : latticeDistance u v ≤ 1
    · simp only [if_pos h,if_neg (not_lt.mpr h),add_zero]
    · simp only [if_neg h,if_pos (lt_of_not_ge h),zero_add]
  rw [hsplit]
  exact (add_le_add hnear hfar).trans_eq (by dsimp [K]; ring)

private theorem integrable_pointwise (a b D k L R : ℝ)
    (ha : a ≤ 0) (hb : b ≤ 0) (hD : D = max 1 k) (hD1 : 1 ≤ D)
    (hk : k ≤ L+R) :
    (max 1 L)^a*(max 1 R)^b ≤
      (2 : ℝ)^(-a)*D^a*(max 1 R)^b +
      (2 : ℝ)^(-b)*D^b*(if L ≤ D then (max 1 L)^a else 0) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hhalf : 0 < D/2 := by positivity
  have hscale (t : ℝ) : (D/2)^t = (2 : ℝ)^(-t)*D^t := by
    rw [Real.div_rpow hDpos.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) t]
    ring
  by_cases hlarge : D/2 ≤ max 1 L
  · have hg := (Real.rpow_le_rpow_of_nonpos hhalf hlarge ha).trans_eq (hscale a)
    exact (mul_le_mul_of_nonneg_right hg (by positivity)).trans
      (le_add_of_nonneg_right (by split_ifs <;> positivity))
  · have hsmall : max 1 L < D/2 := lt_of_not_ge hlarge
    have hD2 : 2 < D := by have h := le_max_left (1 : ℝ) L; linarith
    have hk1 : 1 ≤ k := by
      by_contra hn
      have hke : k ≤ 1 := (lt_of_not_ge hn).le
      have he : D = 1 := by rw [hD,max_eq_left hke]
      linarith
    have hDk : D = k := by rw [hD,max_eq_right hk1]
    have hL : L ≤ D := by have h := le_max_right (1 : ℝ) L; linarith
    have hR : D/2 ≤ max 1 R := by
      have hLL := le_max_right (1 : ℝ) L
      have hRR := le_max_right (1 : ℝ) R
      rw [← hDk] at hk
      linarith
    have hg := (Real.rpow_le_rpow_of_nonpos hhalf hR hb).trans_eq (hscale b)
    calc
      _ ≤ (max 1 L)^a*((2 : ℝ)^(-b)*D^b) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ (2 : ℝ)^(-a)*D^a*(max 1 R)^b +
          (2 : ℝ)^(-b)*D^b*(max 1 L)^a := by
        have hnon : 0 ≤ (2 : ℝ)^(-a)*D^a*(max 1 R)^b := by positivity
        nlinarith only [hnon]
      _ = _ := by rw [if_pos hL]

/-- An order-two kernel convolved with the integrable squared order-four
kernel remains order two, uniformly in every actual finite cutoff. -/
theorem green_squared_fourth_convolution_le {d : ℕ} (hd : 9 ≤ d)
    (s : Finset (Vertex d)) (x u : Vertex d) :
    ∑ v ∈ s, (max 1 (latticeDistance x v))^((2 : ℝ)-(d : ℝ)) *
      (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ)) ≤
      ((2 : ℝ)^((d : ℝ)-2)*(1+5*(2*(d : ℝ)*3^(d-1))) +
       (2 : ℝ)^(2*(d : ℝ)-8)*(1+9*(2*(d : ℝ)*3^(d-1)))) *
      (max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ)) := by
  let a : ℝ := 2-(d : ℝ)
  let b : ℝ := 8-2*(d : ℝ)
  let D : ℝ := max 1 (latticeDistance x u)
  let M : ℕ := Nat.floor D+1
  let K : ℝ := 2*(d : ℝ)*3^(d-1)
  let A : ℝ := (2 : ℝ)^(-a)
  let B : ℝ := (2 : ℝ)^(-b)
  let N := s.filter (fun v => latticeDistance x v ≤ D)
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hMge : D ≤ (M : ℝ) := by
    simpa only [M,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one D).le
  have hMle : (M : ℝ) ≤ 2*D := by
    have hf := Nat.floor_le hDpos.le
    dsimp [M]
    push_cast
    linarith
  have hnear : (∑ v ∈ N, (max 1 (latticeDistance x v))^a) ≤ (1+9*K)*D^2 := by
    calc
      _ ≤ 1+K*(M+1 : ℝ)^2 := sum_green_ball_le (by omega) M N x
        (fun v hv => ((Finset.mem_filter.mp hv).2).trans hMge)
      _ ≤ _ := by
        have hsq : (M+1 : ℝ)^2 ≤ 9*D^2 := by
          have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ M+1)
            (show (M+1 : ℝ) ≤ 3*D by linarith) 2
          nlinarith only [hh]
        have hDsq : (1 : ℝ) ≤ D^2 := by nlinarith [sq_nonneg (D-1)]
        nlinarith [mul_le_mul_of_nonneg_left hsq hK]
  have hmass : (∑ v ∈ s, (max 1 (latticeDistance u v))^b) ≤ 1+5*K :=
    sum_squared_fourth_kernel_le hd s u
  have hp : (∑ v ∈ s, (max 1 (latticeDistance x v))^a * (max 1 (latticeDistance u v))^b) ≤
      A*D^a*(∑ v ∈ s, (max 1 (latticeDistance u v))^b) +
      B*D^b*(∑ v ∈ N, (max 1 (latticeDistance x v))^a) := by
    calc
      _ ≤ ∑ v ∈ s, (A*D^a*(max 1 (latticeDistance u v))^b +
          B*D^b*(if latticeDistance x v ≤ D then (max 1 (latticeDistance x v))^a else 0)) := by
        apply Finset.sum_le_sum
        intro v _
        apply integrable_pointwise a b D (latticeDistance x u) (latticeDistance x v)
          (latticeDistance u v) (by dsimp [a]; linarith) (by dsimp [b]; linarith) rfl hD1
        simpa only [latticeDistance_comm v u] using latticeDistance_triangle x v u
      _ = _ := by simp only [A,B,N,Finset.sum_filter,Finset.sum_add_distrib,Finset.mul_sum]
  have hpows : D^b*D^2 = D^((10 : ℝ)-2*(d : ℝ)) := by
    rw [← Real.rpow_natCast D 2,← Real.rpow_add hDpos]
    congr 1
    dsimp [b]
    norm_num <;> ring
  have hdecay : D^((10 : ℝ)-2*(d : ℝ)) ≤ D^a :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by dsimp [a]; linarith)
  have hmain : (∑ v ∈ s, (max 1 (latticeDistance x v))^a * (max 1 (latticeDistance u v))^b) ≤
      (A*(1+5*K)+B*(1+9*K))*D^a := by
    calc
      _ ≤ A*D^a*(1+5*K)+B*D^b*((1+9*K)*D^2) :=
        hp.trans (add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity))
          (mul_le_mul_of_nonneg_left hnear (by positivity)))
      _ = A*(1+5*K)*D^a+B*(1+9*K)*(D^b*D^2) := by ring
      _ ≤ A*(1+5*K)*D^a+B*(1+9*K)*D^a := by
        rw [hpows]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hdecay (by positivity))
      _ = _ := by ring
  simpa only [A,B,a,b,D,K,neg_sub] using hmain

/-- The central squared-bubble diagram with both exterior order-two arms
has an order-four bound over arbitrary two finite branch cutoffs. -/
theorem green_squared_fourth_green_convolution_le {d : ℕ} (hd : 9 ≤ d)
    (L R : Finset (Vertex d)) (x y : Vertex d) :
    ∑ a ∈ L, ∑ b ∈ R,
      (max 1 (latticeDistance x a))^((2 : ℝ)-(d : ℝ)) *
      (max 1 (latticeDistance a b))^((8 : ℝ)-2*(d : ℝ)) *
      (max 1 (latticeDistance b y))^((2 : ℝ)-(d : ℝ)) ≤
    (((2 : ℝ)^((d : ℝ)-2)*(1+5*(2*(d : ℝ)*3^(d-1))) +
       (2 : ℝ)^(2*(d : ℝ)-8)*(1+9*(2*(d : ℝ)*3^(d-1)))) *
      ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))) *
      (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ)) := by
  let C : ℝ := (2 : ℝ)^((d : ℝ)-2)*(1+5*(2*(d : ℝ)*3^(d-1))) +
    (2 : ℝ)^(2*(d : ℝ)-8)*(1+9*(2*(d : ℝ)*3^(d-1)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hinner (a : Vertex d) :
      (∑ b ∈ R, (max 1 (latticeDistance a b))^((8 : ℝ)-2*(d : ℝ)) *
        (max 1 (latticeDistance b y))^((2 : ℝ)-(d : ℝ))) ≤
      C*(max 1 (latticeDistance y a))^((2 : ℝ)-(d : ℝ)) := by
    calc
      _ = ∑ b ∈ R, (max 1 (latticeDistance y b))^((2 : ℝ)-(d : ℝ)) *
          (max 1 (latticeDistance a b))^((8 : ℝ)-2*(d : ℝ)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [latticeDistance_comm b y]
        ring
      _ ≤ _ := green_squared_fourth_convolution_le hd R y a
  calc
    _ = ∑ a ∈ L, (max 1 (latticeDistance x a))^((2 : ℝ)-(d : ℝ)) *
        (∑ b ∈ R, (max 1 (latticeDistance a b))^((8 : ℝ)-2*(d : ℝ)) *
          (max 1 (latticeDistance b y))^((2 : ℝ)-(d : ℝ))) := by
      simp only [Finset.mul_sum,mul_assoc]
    _ ≤ ∑ a ∈ L, (max 1 (latticeDistance x a))^((2 : ℝ)-(d : ℝ)) *
        (C*(max 1 (latticeDistance y a))^((2 : ℝ)-(d : ℝ))) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hinner a) (by positivity)
    _ = C*(∑ a ∈ L, (max 1 (latticeDistance x a))^((2 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance y a))^((2 : ℝ)-(d : ℝ))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ C*(((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))) *
        (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [Nat.cast_one] using truncated_green_convolution_le (by omega) 1 (by decide) L x y
    _ = _ := by dsimp [C]; ring

end NearCritical.Section8
