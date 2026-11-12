module
public import NearCritical.Section8HigherEnergy

/-! Fourth-order convolution for the Section 9 collision diagrams. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical

private lemma convolution_pointwise (a r M k L R : ℝ) (ha : a ≤ 0) (hr : 1 ≤ r)
    (hM : 0 < M) (hDM : max r k ≤ M) (hMD : M ≤ 2*max r k)
    (hk : k ≤ L+R) (hR : R ≤ k+L) :
    (max r L)^a*(max 1 R)^a ≤
      (4 : ℝ)^(-a)*M^a * ((if R ≤ 2*M then (max 1 R)^a else 0) +
        (if L ≤ 2*M then (max 1 L)^a else 0)) +
      (4 : ℝ)^(-a)*(if 2*M < R then (max 1 R)^(a+a) else 0) := by
  let A := (4 : ℝ)^(-a)
  let c := A*M^a
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 ≤ c := mul_nonneg hA (Real.rpow_nonneg hM.le _)
  have hscale : (M/4)^a = c := by
    dsimp [c,A]
    rw [Real.div_rpow hM.le (by norm_num : (0 : ℝ) ≤ 4),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) a]
    ring
  have hM4 : 0 < M/4 := by positivity
  have hM1 : 1 ≤ M := hr.trans ((le_max_left r k).trans hDM)
  by_cases hnear : R ≤ 2*M
  · have hnfar : ¬ 2*M < R := not_lt.mpr hnear
    by_cases hlarge : M/4 ≤ max r L
    · have hw : (max r L)^a ≤ c :=
        (Real.rpow_le_rpow_of_nonpos hM4 hlarge ha).trans_eq hscale
      have hextra : 0 ≤ if L ≤ 2*M then (max 1 L)^a else 0 := by
        split_ifs <;> positivity
      calc
        _ ≤ c*(max 1 R)^a := mul_le_mul_of_nonneg_right hw (by positivity)
        _ ≤ c*((max 1 R)^a+(if L ≤ 2*M then (max 1 L)^a else 0)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hextra) hc
        _ = _ := by simp only [if_pos hnear,if_neg hnfar,mul_zero,add_zero,c,A]
    · have hsmall : max r L < M/4 := lt_of_not_ge hlarge
      have hrsmall : r < M/4 := (le_max_left r L).trans_lt hsmall
      have hLsmall : L < M/4 := (le_max_right r L).trans_lt hsmall
      have hrk : r ≤ k := by
        by_contra hn
        have hkr : k ≤ r := (lt_of_not_ge hn).le
        rw [max_eq_left hkr] at hMD
        linarith
      have hkhalf : M/2 ≤ k := by
        rw [max_eq_right hrk] at hMD
        linarith
      have hRlarge : M/4 < R := by linarith
      have hLball : L ≤ 2*M := by linarith
      have hg : (max 1 R)^a ≤ c :=
        (Real.rpow_le_rpow_of_nonpos hM4 (hRlarge.le.trans (le_max_right _ _)) ha).trans_eq hscale
      have hw : (max r L)^a ≤ (max 1 L)^a :=
        Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (max_le_max hr le_rfl) ha
      calc
        _ ≤ (max 1 L)^a*c := mul_le_mul hw hg (by positivity) (by positivity)
        _ = c*(max 1 L)^a := mul_comm _ _
        _ ≤ c*((max 1 R)^a+(max 1 L)^a) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hc
        _ = _ := by simp only [if_pos hnear,if_pos hLball,if_neg hnfar,mul_zero,add_zero,c,A]
  · have hfar : 2*M < R := lt_of_not_ge hnear
    have hRpos : 0 < R := by linarith
    have hR1 : 1 ≤ R := by linarith
    have hkM : k ≤ M := (le_max_right r k).trans hDM
    have hLhalf : R/2 ≤ max r L := by
      have hLL : L ≤ max r L := le_max_right _ _
      linarith
    have htwo : (2 : ℝ)^(-a) ≤ A :=
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 4)
        (neg_nonneg.mpr ha)
    have hscaleR : (R/2)^a = (2 : ℝ)^(-a)*R^a := by
      rw [Real.div_rpow hRpos.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) a]
      ring
    have hw : (max r L)^a ≤ A*R^a :=
      ((Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R/2) hLhalf ha).trans_eq hscaleR).trans
        (mul_le_mul_of_nonneg_right htwo (by positivity))
    have hextra : 0 ≤ if L ≤ 2*M then (max 1 L)^a else 0 := by
      split_ifs <;> positivity
    calc
      _ = (max r L)^a*R^a := by rw [max_eq_right hR1]
      _ ≤ (A*R^a)*R^a := mul_le_mul_of_nonneg_right hw (by positivity)
      _ = A*R^(a+a) := by rw [mul_assoc,← Real.rpow_add hRpos]
      _ ≤ c*(if L ≤ 2*M then (max 1 L)^a else 0)+A*R^(a+a) :=
        le_add_of_nonneg_left (mul_nonneg hc hextra)
      _ = _ := by simp only [if_neg hnear,if_pos hfar,zero_add,max_eq_right hR1,c,A]

/-- Finite-cutoff fourth-order convolution, including diagonal terms. -/
theorem truncated_fourth_fourth_convolution_le {d : ℕ} (hd : 9 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (s : Finset (Vertex d)) (x u : Vertex d) :
    ∑ y ∈ s, (max (r : ℝ) (latticeDistance x y))^((4 : ℝ)-(d : ℝ)) *
      (max 1 (latticeDistance u y))^((4 : ℝ)-(d : ℝ)) ≤
      ((4 : ℝ)^((d : ℝ)-4)*(162+163*(2*(d : ℝ)*3^(d-1)))) *
        (max (r : ℝ) (latticeDistance x u))^((8 : ℝ)-(d : ℝ)) := by
  let a : ℝ := 4-(d : ℝ)
  let D : ℝ := max (r : ℝ) (latticeDistance x u)
  let M : ℕ := Nat.floor D+1
  let K : ℝ := 2*(d : ℝ)*3^(d-1)
  let A : ℝ := (4 : ℝ)^(-a)
  let U := s.filter (fun y => latticeDistance u y ≤ 2*(M : ℝ))
  let X := s.filter (fun y => latticeDistance x y ≤ 2*(M : ℝ))
  let F := s.filter (fun y => 2*(M : ℝ) < latticeDistance u y)
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
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
  have ha : a ≤ 0 := by dsimp [a]; linarith
  have hc : 0 ≤ A*(M : ℝ)^a := mul_nonneg hA (Real.rpow_nonneg hMpos.le _)
  have hballs (v : Vertex d) :
      (∑ y ∈ s.filter (fun y => latticeDistance v y ≤ 2*(M : ℝ)),
        (max 1 (latticeDistance v y))^a) ≤ (81*(1+K))*(M : ℝ)^4 := by
    calc
      _ ≤ (1+K)*(2*M+1 : ℝ)^4 := by
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using
          sum_fourth_green_ball_le (by omega : 2 ≤ d) (2*M)
            (s.filter (fun y => latticeDistance v y ≤ 2*(M : ℝ))) v
            (fun y hy => by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Finset.mem_filter.mp hy).2)
      _ ≤ _ := by
        have hb : (2*(M : ℝ)+1)^4 ≤ (3*(M : ℝ))^4 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 4
        nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1+K)]
  have hfar : (∑ y ∈ F, (max 1 (latticeDistance u y))^(a+a)) ≤
      K*(M : ℝ)^((8 : ℝ)-(d : ℝ)) := by
    have hq : a+a < -(d : ℝ) := by dsimp [a]; linarith
    have ht := sum_power_tail_ball_le (by omega : 1 ≤ d) (2*M) (by omega : 1 ≤ 2*M)
      (a+a) hq F u (fun y hy => by
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Finset.mem_filter.mp hy).2)
    simp only [Nat.cast_mul,Nat.cast_ofNat] at ht
    have he1 : (d : ℝ)+(a+a) = 8-(d : ℝ) := by dsimp [a]; ring
    have he2 : -(d : ℝ)-(a+a) = (d : ℝ)-8 := by dsimp [a]; ring
    rw [he1,he2] at ht
    have hden : (1 : ℝ) ≤ (d : ℝ)-8 := by linarith
    have hscale : (2*M : ℝ)^((8 : ℝ)-(d : ℝ)) ≤ (M : ℝ)^((8 : ℝ)-(d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hMpos (by push_cast; linarith) (by linarith)
    exact ht.trans ((div_le_self (by positivity) hden).trans
      (mul_le_mul_of_nonneg_left hscale hK))
  have hall :
      (∑ y ∈ s, (max (r : ℝ) (latticeDistance x y))^a * (max 1 (latticeDistance u y))^a) ≤
      A*(M : ℝ)^a * ((∑ y ∈ U, (max 1 (latticeDistance u y))^a) +
        (∑ y ∈ X, (max 1 (latticeDistance x y))^a)) +
      A*(∑ y ∈ F, (max 1 (latticeDistance u y))^(a+a)) := by
    calc
      _ ≤ ∑ y ∈ s, (A*(M : ℝ)^a *
          ((if latticeDistance u y ≤ 2*(M : ℝ) then (max 1 (latticeDistance u y))^a else 0) +
           (if latticeDistance x y ≤ 2*(M : ℝ) then (max 1 (latticeDistance x y))^a else 0)) +
          A*(if 2*(M : ℝ) < latticeDistance u y then (max 1 (latticeDistance u y))^(a+a) else 0)) := by
        apply Finset.sum_le_sum
        intro y _hy
        have hk : latticeDistance x u ≤ latticeDistance x y+latticeDistance u y := by
          simpa only [latticeDistance_comm y u] using latticeDistance_triangle x y u
        have hR : latticeDistance u y ≤ latticeDistance x u+latticeDistance x y := by
          simpa only [latticeDistance_comm u x] using latticeDistance_triangle u x y
        exact convolution_pointwise a r M (latticeDistance x u) (latticeDistance x y)
          (latticeDistance u y) ha hr1 hMpos hMge hMle hk hR
      _ = _ := by
        simp only [A,U,X,F,Finset.sum_filter,Finset.sum_add_distrib,Finset.mul_sum,mul_add]
  have hpows : (M : ℝ)^a*(M : ℝ)^4 = (M : ℝ)^((8 : ℝ)-(d : ℝ)) := by
    rw [← Real.rpow_natCast (M : ℝ) 4,← Real.rpow_add hMpos]
    congr 1
    dsimp [a]
    norm_num <;> ring
  have hmain :
      (∑ y ∈ s, (max (r : ℝ) (latticeDistance x y))^a * (max 1 (latticeDistance u y))^a) ≤
      A*(162+163*K)*D^((8 : ℝ)-(d : ℝ)) := by
    calc
      _ ≤ A*(M : ℝ)^a * ((81*(1+K))*(M : ℝ)^4+(81*(1+K))*(M : ℝ)^4) +
          A*(K*(M : ℝ)^((8 : ℝ)-(d : ℝ))) :=
        hall.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add (hballs u) (hballs x)) hc)
          (mul_le_mul_of_nonneg_left hfar hA))
      _ = A*(162+163*K)*(M : ℝ)^((8 : ℝ)-(d : ℝ)) := by
        calc
          _ = A*(162+162*K)*((M : ℝ)^a*(M : ℝ)^4) +
              A*K*(M : ℝ)^((8 : ℝ)-(d : ℝ)) := by ring
          _ = _ := by rw [hpows]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hDpos hMge (by linarith)) (by positivity)
  simpa only [A,a,neg_sub,K,D] using hmain

end NearCritical.Section8
