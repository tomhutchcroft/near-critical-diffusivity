module

public import NearCritical.Section10DifferenceEntrance

/-! A finite exponential moment for the actual positive lazy route law. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace NearCritical.Section10
open scoped Classical

abbrev LazyRouteHistory (D T : ℕ) := Fin T → Option (Fin D)

def lazyRouteWeight {D T : ℕ} (h : LazyRouteHistory D T) : ℝ :=
  ∏ j, lazyCoordinateWeight D (h j)

def lazyRouteCoordinateCount {D T : ℕ} (h : LazyRouteHistory D T)
    (i : Fin D) (t : ℕ) : ℕ :=
  ∑ j : Fin T, if j.val < t ∧ h j = some i then 1 else 0

private theorem lazyRouteWeight_nonneg {D T : ℕ} (h : LazyRouteHistory D T) :
    0 ≤ lazyRouteWeight h := by
  apply Finset.prod_nonneg
  intro j _
  cases h j <;> simp only [lazyCoordinateWeight] <;> positivity

private theorem lazyRouteStep_normalized {D : ℕ} (hD : 0 < D) :
    ∑ a, lazyCoordinateWeight D a = 1 := by
  classical
  rw [Fintype.sum_option]
  simp only [lazyCoordinateWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp [hd] <;> ring

theorem lazyRouteWeight_normalized {D : ℕ} (hD : 0 < D) (T : ℕ) :
    (∑ h : LazyRouteHistory D T, lazyRouteWeight h) = 1 := by
  classical
  unfold lazyRouteWeight
  rw [← Fintype.prod_sum (fun (_ : Fin T) a => lazyCoordinateWeight D a)]
  simp only [lazyRouteStep_normalized hD, Finset.prod_const_one]

theorem lazyRouteCoordinate_moment {D T : ℕ} (hD : 2 ≤ D) (i : Fin D) :
    (∑ h : LazyRouteHistory D T, lazyRouteWeight h *
      (4 : ℝ)^lazyRouteCoordinateCount h i T) ≤ (7/4 : ℝ)^T := by
  classical
  have ha (h : LazyRouteHistory D T) :
      (4 : ℝ)^lazyRouteCoordinateCount h i T = ∏ j : Fin T, if h j = some i then 4 else 1 := by
    unfold lazyRouteCoordinateCount
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.isLt, true_and]
    split_ifs <;> simp
  simp_rw [ha, lazyRouteWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin T) a =>
    lazyCoordinateWeight D a * (if a = some i then 4 else 1))]
  have he (a : Option (Fin D)) :
      lazyCoordinateWeight D a * (if a = some i then 4 else 1) =
        lazyCoordinateWeight D a + (if a = some i then 3*lazyCoordinateWeight D a else 0) := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    lazyRouteStep_normalized (by omega : 0 < D), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [lazyCoordinateWeight]
  apply pow_le_pow_left₀ (by positivity)
  have hd : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hdiv : (1 : ℝ)/(2*D) ≤ 1/4 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  linarith

/-- The literal transverse survival event through level M−1. The
length-M history carries one unused last increment. -/
def lazyRouteSurvives {D M : ℕ} (x : Fin D → ℤ) (h : LazyRouteHistory D M) : Prop :=
  ∀ j : Fin M, ∀ i : Fin D,
    0 ≤ x i + (lazyRouteCoordinateCount h i j : ℤ) ∧
      x i + (lazyRouteCoordinateCount h i j : ℤ) < (M : ℤ)

private theorem exit_requires_coordinate_count {D M : ℕ} (hD : 2 ≤ D)
    {x : Fin D → ℤ} (hx : x ∈ routeStartBox D M) (h : LazyRouteHistory D M)
    (hf : ¬ lazyRouteSurvives x h) : ∃ i : Fin D, M ≤ 2*lazyRouteCoordinateCount h i M := by
  classical
  unfold lazyRouteSurvives at hf
  obtain ⟨j,hj⟩ := not_forall.mp hf
  obtain ⟨i,hbad⟩ := not_forall.mp hj
  have hxi := Fintype.mem_piFinset.mp hx i
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hxi
  have h0 : 0 ≤ x i := by
    apply le_trans _ hlo
    exact Int.ceil_nonneg (by positivity)
  have hM' : (0 : ℝ) ≤ M := by positivity
  have hden : (2 : ℝ) ≤ 2*((D : ℝ)+1) := by
    nlinarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  have hxR : (x i : ℝ) ≤ (M : ℝ)/2 :=
    ((Int.le_floor.mp hhi).trans
      (div_le_div_of_nonneg_left hM' (by norm_num) hden))
  have hjle : lazyRouteCoordinateCount h i j ≤ lazyRouteCoordinateCount h i M := by
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : (t : ℕ) < (j : ℕ) ∧ h t = some i
    · rw [if_pos ht, if_pos ⟨ht.1.trans j.isLt, ht.2⟩]
    · rw [if_neg ht]
      split_ifs <;> omega
  refine ⟨i,?_⟩
  have hupper : (M : ℤ) ≤ x i + (lazyRouteCoordinateCount h i j : ℤ) :=
    le_of_not_gt (fun hl => hbad ⟨add_nonneg h0 (by positivity),hl⟩)
  have hupperR : (M : ℝ) ≤ (x i : ℝ) + (lazyRouteCoordinateCount h i j : ℝ) := by
    exact_mod_cast hupper
  have hjleR : (lazyRouteCoordinateCount h i j : ℝ) ≤ lazyRouteCoordinateCount h i M := by
    exact_mod_cast hjle
  exact_mod_cast (show (M : ℝ) ≤ 2*(lazyRouteCoordinateCount h i M : ℝ) by linarith)

theorem lazyRoute_failure_bound {D M : ℕ} (hD : 2 ≤ D)
    {x : Fin D → ℤ} (hx : x ∈ routeStartBox D M) :
    (∑ h : LazyRouteHistory D M, if ¬ lazyRouteSurvives x h then lazyRouteWeight h else 0) ≤
      (D : ℝ)*(7/8 : ℝ)^M := by
  classical
  have hb : 0 < (2 : ℝ)^M := by positivity
  calc
    _ ≤ ∑ h : LazyRouteHistory D M, ∑ i : Fin D,
        lazyRouteWeight h * (4 : ℝ)^lazyRouteCoordinateCount h i M / (2 : ℝ)^M := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hf : ¬ lazyRouteSurvives x h
      · rw [if_pos hf]
        obtain ⟨i,hi⟩ := exit_requires_coordinate_count hD hx h hf
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun i => lazyRouteWeight h * (4 : ℝ)^lazyRouteCoordinateCount h i M / (2 : ℝ)^M)
          (fun i _ => div_nonneg (mul_nonneg (lazyRouteWeight_nonneg h) (by positivity)) hb.le) (Finset.mem_univ i))
        apply (le_div_iff₀ hb).mpr
        apply mul_le_mul_of_nonneg_left _ (lazyRouteWeight_nonneg h)
        have he : (4 : ℝ)^lazyRouteCoordinateCount h i M =
            (2 : ℝ)^(2*lazyRouteCoordinateCount h i M) := by rw [pow_mul]; norm_num
        rw [he]
        exact pow_le_pow_right₀ (by norm_num) hi
      · rw [if_neg hf]
        exact Finset.sum_nonneg (fun i _ => div_nonneg (mul_nonneg (lazyRouteWeight_nonneg h) (by positivity)) hb.le)
    _ = ∑ i : Fin D, ∑ h : LazyRouteHistory D M,
        lazyRouteWeight h * (4 : ℝ)^lazyRouteCoordinateCount h i M / (2 : ℝ)^M :=
      Finset.sum_comm
    _ ≤ ∑ _i : Fin D, (7/8 : ℝ)^M := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_div]
      have he : (7/8 : ℝ)^M = (7/4 : ℝ)^M / (2 : ℝ)^M := by rw [← div_pow]; norm_num
      rw [he]
      exact div_le_div_of_nonneg_right (lazyRouteCoordinate_moment hD i) hb.le
    _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]

theorem lazyRoute_survival_eventually_half {D : ℕ} (hD : 2 ≤ D) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ x ∈ routeStartBox D M,
      (1/2 : ℝ) ≤ ∑ h : LazyRouteHistory D M,
        if lazyRouteSurvives x h then lazyRouteWeight h else 0 := by
  classical
  have hlim : Filter.Tendsto (fun M : ℕ => (D : ℝ)*(7/8 : ℝ)^M)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 7/8) (by norm_num : (7/8 : ℝ) < 1)).const_mul (D : ℝ)
  obtain ⟨M₀,hM₀⟩ := Filter.eventually_atTop.mp (hlim.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))
  refine ⟨M₀,?_⟩
  intro M hM x hx
  have hfail := (lazyRoute_failure_bound hD hx).trans (hM₀ M hM).le
  have htotal : (∑ h : LazyRouteHistory D M, if lazyRouteSurvives x h then lazyRouteWeight h else 0) +
      (∑ h : LazyRouteHistory D M, if ¬ lazyRouteSurvives x h then lazyRouteWeight h else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← lazyRouteWeight_normalized (by omega : 0 < D) M]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : lazyRouteSurvives x h <;> simp [hh]
  linarith

/-- Survival mass with the source's uniform initial distribution. -/
def sourceRouteSurvivalMass (D M : ℕ) : ℝ := by
  classical
  exact (∑ x ∈ routeStartBox D M, ∑ h : LazyRouteHistory D M,
    if lazyRouteSurvives x h then lazyRouteWeight h else 0) /
      ((routeStartBox D M).card : ℝ)

theorem sourceRouteSurvivalMass_eventually_half {D : ℕ} (hD : 2 ≤ D) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, (1/2 : ℝ) ≤ sourceRouteSurvivalMass D M := by
  classical
  obtain ⟨M₀,hM₀⟩ := lazyRoute_survival_eventually_half hD
  refine ⟨max M₀ (8*(D+1)),?_⟩
  intro M hM
  have hs := routeStartBox_card_lower ((le_max_right M₀ (8*(D+1))).trans hM)
  have hMp : 0 < M := by omega
  have hcard : 0 < ((routeStartBox D M).card : ℝ) := lt_of_lt_of_le (by positivity) hs
  unfold sourceRouteSurvivalMass
  apply (le_div_iff₀ hcard).mpr
  calc
    _ = ∑ _x ∈ routeStartBox D M, (1/2 : ℝ) := by
      simp [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun x hx =>
      hM₀ M ((le_max_left M₀ (8*(D+1))).trans hM) x hx)

/-- Independent conditioning with each survival mass at least one half. The
numerator is the joint surviving event mass. -/
theorem route_pair_conditioning_factor_four {joint raw p q : ℝ}
    (hraw : 0 ≤ raw) (hle : joint ≤ raw) (hp : 1/2 ≤ p) (hq : 1/2 ≤ q) :
    joint / (p*q) ≤ 4*raw := by
  have hp' : 0 < p := by linarith
  have hq' : 0 < q := by linarith
  apply (div_le_iff₀ (mul_pos hp' hq')).mpr
  have hpq : (1/4 : ℝ) ≤ p*q := by
    nlinarith [mul_le_mul hp hq (by norm_num : (0 : ℝ) ≤ 1/2) hp'.le]
  exact hle.trans (by nlinarith [mul_nonneg hraw (sub_nonneg.mpr hpq)])

end NearCritical.Section10
