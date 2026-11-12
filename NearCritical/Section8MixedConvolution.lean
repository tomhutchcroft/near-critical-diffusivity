module
public import NearCritical.Section8HigherEnergy

/-! The unequal-power convolution needed for the outer variance diagrams. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical

private lemma mixed_pointwise (a b r M k L R : ℝ) (hab : a ≤ b) (hb : b ≤ 0) (hr : 1 ≤ r)
    (hM : 0 < M) (hDM : max r k ≤ M) (hMD : M ≤ 2*max r k)
    (hk : k ≤ L+R) (hR : R ≤ k+L) :
    (max r L)^b*(max 1 R)^a ≤
      (4 : ℝ)^(-a)*M^b*(if R ≤ 2*M then (max 1 R)^a else 0) +
      (4 : ℝ)^(-a)*M^a*(if L ≤ 2*M then (max 1 L)^b else 0) +
      (4 : ℝ)^(-a)*(if 2*M < R then (max 1 R)^(a+b) else 0) := by
  let A := (4 : ℝ)^(-a)
  have ha : a ≤ 0 := hab.trans hb
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hscale (t : ℝ) (ht : a ≤ t) : (M/4)^t ≤ A*M^t := by
    rw [Real.div_rpow hM.le (by norm_num : (0 : ℝ) ≤ 4)]
    have hcoef : (4 : ℝ)^(-t) ≤ A := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc
      _ = (4 : ℝ)^(-t)*M^t := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) t]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hM4 : 0 < M/4 := by positivity
  have hM1 : 1 ≤ M := hr.trans ((le_max_left r k).trans hDM)
  by_cases hnear : R ≤ 2*M
  · have hnfar : ¬ 2*M < R := not_lt.mpr hnear
    by_cases hlarge : M/4 ≤ max r L
    · have hw : (max r L)^b ≤ A*M^b :=
        (Real.rpow_le_rpow_of_nonpos hM4 hlarge hb).trans (hscale b hab)
      have hextra : 0 ≤ A*M^a*(if L ≤ 2*M then (max 1 L)^b else 0) := by
        split_ifs <;> positivity
      calc
        _ ≤ A*M^b*(max 1 R)^a := mul_le_mul_of_nonneg_right hw (by positivity)
        _ ≤ A*M^b*(max 1 R)^a+A*M^a*(if L ≤ 2*M then (max 1 L)^b else 0) :=
          le_add_of_nonneg_right hextra
        _ = _ := by simp only [if_pos hnear,if_neg hnfar,mul_zero,add_zero,A]
    · have hsmall : max r L < M/4 := lt_of_not_ge hlarge
      have hrsmall : r < M/4 := (le_max_left r L).trans_lt hsmall
      have hLsmall : L < M/4 := (le_max_right r L).trans_lt hsmall
      have hrk : r ≤ k := by
        by_contra hn
        have hkr : k ≤ r := (lt_of_not_ge hn).le
        rw [max_eq_left hkr] at hMD
        linarith
      have hkhalf : M/2 ≤ k := by rw [max_eq_right hrk] at hMD; linarith
      have hRlarge : M/4 < R := by linarith
      have hLball : L ≤ 2*M := by linarith
      have hg : (max 1 R)^a ≤ A*M^a :=
        (Real.rpow_le_rpow_of_nonpos hM4 (hRlarge.le.trans (le_max_right _ _)) ha).trans
          (hscale a le_rfl)
      have hw : (max r L)^b ≤ (max 1 L)^b :=
        Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (max_le_max hr le_rfl) hb
      calc
        _ ≤ (max 1 L)^b*(A*M^a) := mul_le_mul hw hg (by positivity) (by positivity)
        _ = A*M^a*(max 1 L)^b := by ring
        _ ≤ A*M^b*(max 1 R)^a+A*M^a*(max 1 L)^b :=
          le_add_of_nonneg_left (by positivity)
        _ = _ := by simp only [if_pos hnear,if_pos hLball,if_neg hnfar,mul_zero,add_zero,A]
  · have hfar : 2*M < R := lt_of_not_ge hnear
    have hRpos : 0 < R := by linarith
    have hR1 : 1 ≤ R := by linarith
    have hkM : k ≤ M := (le_max_right r k).trans hDM
    have hLhalf : R/2 ≤ max r L := by have hLL := le_max_right r L; linarith
    have htwo : (2 : ℝ)^(-b) ≤ A :=
      (Real.rpow_le_rpow (by norm_num) (by norm_num : (2 : ℝ) ≤ 4) (neg_nonneg.mpr hb)).trans
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    have hscaleR : (R/2)^b = (2 : ℝ)^(-b)*R^b := by
      rw [Real.div_rpow hRpos.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) b]
      ring
    have hw : (max r L)^b ≤ A*R^b :=
      ((Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R/2) hLhalf hb).trans_eq hscaleR).trans
        (mul_le_mul_of_nonneg_right htwo (by positivity))
    have hextra : 0 ≤ A*M^a*(if L ≤ 2*M then (max 1 L)^b else 0) := by
      split_ifs <;> positivity
    calc
      _ = (max r L)^b*R^a := by rw [max_eq_right hR1]
      _ ≤ (A*R^b)*R^a := mul_le_mul_of_nonneg_right hw (by positivity)
      _ = A*R^(a+b) := by rw [mul_assoc,← Real.rpow_add hRpos,add_comm b a]
      _ ≤ A*M^a*(if L ≤ 2*M then (max 1 L)^b else 0)+A*R^(a+b) :=
        le_add_of_nonneg_left hextra
      _ = _ := by simp only [if_neg hnear,if_pos hfar,mul_zero,zero_add,max_eq_right hR1,A]

/-- Actual finite fourth/second-order convolution, with positive truncation
and all diagonal terms retained. No summability or convolution input. -/
theorem truncated_fourth_green_convolution_le {d : ℕ} (hd : 7 ≤ d)
    (r : ℕ) (hr : 1 ≤ r) (s : Finset (Vertex d)) (x u : Vertex d) :
    ∑ y ∈ s, (max (r : ℝ) (latticeDistance x y))^((4 : ℝ)-(d : ℝ)) *
      (max 1 (latticeDistance u y))^((2 : ℝ)-(d : ℝ)) ≤
      ((4 : ℝ)^((d : ℝ)-2)*(82+91*(2*(d : ℝ)*3^(d-1)))) *
        (max (r : ℝ) (latticeDistance x u))^((6 : ℝ)-(d : ℝ)) := by
  let a : ℝ := 2-(d : ℝ)
  let b : ℝ := 4-(d : ℝ)
  let D : ℝ := max (r : ℝ) (latticeDistance x u)
  let M : ℕ := Nat.floor D+1
  let K : ℝ := 2*(d : ℝ)*3^(d-1)
  let A : ℝ := (4 : ℝ)^(-a)
  let U := s.filter (fun y => latticeDistance u y ≤ 2*(M : ℝ))
  let X := s.filter (fun y => latticeDistance x y ≤ 2*(M : ℝ))
  let F := s.filter (fun y => 2*(M : ℝ) < latticeDistance u y)
  have hdR : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hD1 : 1 ≤ D := hr1.trans (le_max_left _ _)
  have hDpos : 0 < D := by linarith
  have hMge : D ≤ (M : ℝ) := by
    simpa only [M,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one D).le
  have hMle : (M : ℝ) ≤ 2*D := by
    have hf := Nat.floor_le hDpos.le
    dsimp [M]
    push_cast
    linarith
  have hMNat : 1 ≤ M := by dsimp [M]; omega
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hMNat
  have hMpos : (0 : ℝ) < M := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hab : a ≤ b := by dsimp [a,b]; linarith
  have hb : b ≤ 0 := by dsimp [b]; linarith
  have hballU : (∑ y ∈ U, (max 1 (latticeDistance u y))^a) ≤
      (1+9*K)*(M : ℝ)^2 := by
    calc
      _ ≤ 1+K*(2*M+1 : ℝ)^2 := by
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using
          sum_green_ball_le (by omega : 2 ≤ d) (2*M) U u
            (fun y hy => by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Finset.mem_filter.mp hy).2)
      _ ≤ _ := by
        have hsquare : (2*(M : ℝ)+1)^2 ≤ 9*(M : ℝ)^2 := by
          nlinarith [sq_nonneg ((M : ℝ)-1)]
        have hM2 : (1 : ℝ) ≤ (M : ℝ)^2 := by nlinarith [sq_nonneg ((M : ℝ)-1)]
        nlinarith [mul_le_mul_of_nonneg_left hsquare hK]
  have hballX : (∑ y ∈ X, (max 1 (latticeDistance x y))^b) ≤
      81*(1+K)*(M : ℝ)^4 := by
    calc
      _ ≤ (1+K)*(2*M+1 : ℝ)^4 := by
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using
          sum_fourth_green_ball_le (by omega : 2 ≤ d) (2*M) X x
            (fun y hy => by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Finset.mem_filter.mp hy).2)
      _ ≤ _ := by
        have hpow : (2*(M : ℝ)+1)^4 ≤ (3*(M : ℝ))^4 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 4
        have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 1+K by positivity)
        nlinarith only [hh]
  have hfar : (∑ y ∈ F, (max 1 (latticeDistance u y))^(a+b)) ≤
      K*(M : ℝ)^((6 : ℝ)-(d : ℝ)) := by
    have hq : a+b < -(d : ℝ) := by dsimp [a,b]; linarith
    have ht := sum_power_tail_ball_le (by omega : 1 ≤ d) (2*M) (by omega : 1 ≤ 2*M)
      (a+b) hq F u (fun y hy => by
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Finset.mem_filter.mp hy).2)
    simp only [Nat.cast_mul,Nat.cast_ofNat] at ht
    have he1 : (d : ℝ)+(a+b) = 6-(d : ℝ) := by dsimp [a,b]; ring
    have he2 : -(d : ℝ)-(a+b) = (d : ℝ)-6 := by dsimp [a,b]; ring
    rw [he1,he2] at ht
    have hden : (1 : ℝ) ≤ (d : ℝ)-6 := by linarith
    have hscale : (2*M : ℝ)^((6 : ℝ)-(d : ℝ)) ≤ (M : ℝ)^((6 : ℝ)-(d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hMpos (by push_cast; linarith) (by linarith)
    exact ht.trans ((div_le_self (by positivity) hden).trans
      (mul_le_mul_of_nonneg_left hscale hK))
  have hall :
      (∑ y ∈ s, (max (r : ℝ) (latticeDistance x y))^b * (max 1 (latticeDistance u y))^a) ≤
      A*(M : ℝ)^b*(∑ y ∈ U, (max 1 (latticeDistance u y))^a) +
      A*(M : ℝ)^a*(∑ y ∈ X, (max 1 (latticeDistance x y))^b) +
      A*(∑ y ∈ F, (max 1 (latticeDistance u y))^(a+b)) := by
    calc
      _ ≤ ∑ y ∈ s, (A*(M : ℝ)^b*
          (if latticeDistance u y ≤ 2*(M : ℝ) then (max 1 (latticeDistance u y))^a else 0) +
          A*(M : ℝ)^a*
          (if latticeDistance x y ≤ 2*(M : ℝ) then (max 1 (latticeDistance x y))^b else 0) +
          A*(if 2*(M : ℝ) < latticeDistance u y then (max 1 (latticeDistance u y))^(a+b) else 0)) := by
        apply Finset.sum_le_sum
        intro y _hy
        have hk : latticeDistance x u ≤ latticeDistance x y+latticeDistance u y := by
          simpa only [latticeDistance_comm y u] using latticeDistance_triangle x y u
        have hR : latticeDistance u y ≤ latticeDistance x u+latticeDistance x y := by
          simpa only [latticeDistance_comm u x] using latticeDistance_triangle u x y
        exact mixed_pointwise a b r M (latticeDistance x u) (latticeDistance x y)
          (latticeDistance u y) hab hb hr1 hMpos hMge hMle hk hR
      _ = _ := by
        simp only [A,U,X,F,Finset.sum_filter,Finset.sum_add_distrib,Finset.mul_sum]
  have hpows1 : (M : ℝ)^b*(M : ℝ)^2 = (M : ℝ)^((6 : ℝ)-(d : ℝ)) := by
    rw [← Real.rpow_natCast (M : ℝ) 2,← Real.rpow_add hMpos]
    congr 1
    dsimp [b]
    norm_num <;> ring
  have hpows2 : (M : ℝ)^a*(M : ℝ)^4 = (M : ℝ)^((6 : ℝ)-(d : ℝ)) := by
    rw [← Real.rpow_natCast (M : ℝ) 4,← Real.rpow_add hMpos]
    congr 1
    dsimp [a]
    norm_num <;> ring
  have hmain :
      (∑ y ∈ s, (max (r : ℝ) (latticeDistance x y))^b * (max 1 (latticeDistance u y))^a) ≤
      A*(82+91*K)*D^((6 : ℝ)-(d : ℝ)) := by
    calc
      _ ≤ A*(M : ℝ)^b*((1+9*K)*(M : ℝ)^2) +
          A*(M : ℝ)^a*(81*(1+K)*(M : ℝ)^4) +
          A*(K*(M : ℝ)^((6 : ℝ)-(d : ℝ))) :=
        hall.trans (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hballU (by positivity))
          (mul_le_mul_of_nonneg_left hballX (by positivity)))
          (mul_le_mul_of_nonneg_left hfar hA))
      _ = A*(82+91*K)*(M : ℝ)^((6 : ℝ)-(d : ℝ)) := by
        calc
          _ = A*(1+9*K)*((M : ℝ)^b*(M : ℝ)^2) +
              A*81*(1+K)*((M : ℝ)^a*(M : ℝ)^4) +
              A*K*(M : ℝ)^((6 : ℝ)-(d : ℝ)) := by ring
          _ = _ := by rw [hpows1,hpows2]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hDpos hMge (by linarith)) (by positivity)
  simpa only [A,a,b,neg_sub,K,D] using hmain

end NearCritical.Section8
