module
public import NearCritical.Section9ActualPivotalConcentration
public import NearCritical.Section9PivotalMeanLower
public import NearCritical.Section9PivotalVariancePaper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-! Actual source pivotal concentration, with size chosen after the fixed
regularity radius. No estimated variance envelope is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private def concentrationEnergy {d : ℕ} (D : Finset (Vertex d)) : ℝ :=
  ∑ x ∈ D, ∑ y ∈ D, (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))

private theorem concentration_near_card {d : ℕ} (D : Finset (Vertex d))
    (x : Vertex d) (R : ℕ) :
    (D.filter (fun y => latticeDistance x y ≤ (R : ℝ))).card ≤ (2*R+1)^d := by
  let I := fun j : Fin d => Finset.Icc (x j-(R : ℤ)) (x j+(R : ℤ))
  let T := Fintype.piFinset I
  have hsub : D.filter (fun y => latticeDistance x y ≤ (R : ℝ)) ⊆ T := by
    intro y hy
    have hd := (Finset.mem_filter.mp hy).2
    apply Fintype.mem_piFinset.mpr
    intro j
    have hc : |(x j : ℝ)-(y j : ℝ)| ≤ (R : ℝ) := by
      have hh : |(x j : ℝ)-(y j : ℝ)| ≤ latticeDistance x y := by
        simpa only [latticeDistance,vertexReal,Real.dist_eq] using
          dist_le_pi_dist (vertexReal x) (vertexReal y) j
      exact hh.trans hd
    obtain ⟨hlo,hhi⟩ := abs_le.mp hc
    apply Finset.mem_Icc.mpr
    constructor
    · have hh : (x j : ℝ)-(R : ℝ) ≤ (y j : ℝ) := by linarith
      exact_mod_cast hh
    · have hh : (y j : ℝ) ≤ (x j : ℝ)+(R : ℝ) := by linarith
      exact_mod_cast hh
  have hcard (j : Fin d) : (I j).card = 2*R+1 := by
    dsimp only [I]
    rw [Int.card_Icc]
    omega
  have hT : T.card = (2*R+1)^d := by
    simp only [T,Fintype.card_piFinset,hcard,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (Finset.card_le_card hsub).trans_eq hT

private theorem concentration_kernel_row {d : ℕ} (hd : 9 ≤ d)
    (D : Finset (Vertex d)) (x : Vertex d) (R : ℕ) :
    (∑ y ∈ D, (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))) ≤
      (((2*R+1)^d : ℕ) : ℝ)+(D.card : ℝ)/((R : ℝ)+1) := by
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : 0 < (R : ℝ)+1 := by positivity
  have hpoint (y : Vertex d) :
      (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ)) ≤
        (if latticeDistance x y ≤ (R : ℝ) then 1 else 0)+1/((R : ℝ)+1) := by
    have hb : 1 ≤ 1+latticeDistance x y := by linarith [latticeDistance_nonneg x y]
    by_cases hy : latticeDistance x y ≤ (R : ℝ)
    · rw [if_pos hy]
      have hh : (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ)) ≤ 1 :=
        (Real.rpow_le_rpow_of_exponent_le hb (by linarith : (8 : ℝ)-(d : ℝ) ≤ 0)).trans_eq
          (Real.rpow_zero _)
      linarith [one_div_nonneg.mpr hR.le]
    · rw [if_neg hy,zero_add]
      calc
        _ ≤ (1+latticeDistance x y)^(-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb (by linarith)
        _ = 1/(1+latticeDistance x y) := by rw [Real.rpow_neg_one,one_div]
        _ ≤ _ := one_div_le_one_div_of_le hR (by linarith [lt_of_not_ge hy])
  have hcard : ((D.filter (fun y => latticeDistance x y ≤ (R : ℝ))).card : ℝ) ≤
      (((2*R+1)^d : ℕ) : ℝ) := by
    exact_mod_cast concentration_near_card D x R
  calc
    _ ≤ ∑ y ∈ D, ((if latticeDistance x y ≤ (R : ℝ) then (1 : ℝ) else 0)+1/((R : ℝ)+1)) :=
      Finset.sum_le_sum (fun y _ => hpoint y)
    _ = ((D.filter (fun y => latticeDistance x y ≤ (R : ℝ))).card : ℝ)+
        (D.card : ℝ)/((R : ℝ)+1) := by
      rw [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := add_le_add hcard le_rfl

private theorem concentration_energy_ratio {d : ℕ} (hd : 9 ≤ d)
    (D : Finset (Vertex d)) (R : ℕ) {L n : ℝ}
    (hL : 0 < L) (hn : 1 ≤ n) (hRL : L ≤ (R : ℝ)+1)
    (hball : (((2*R+1)^d : ℕ) : ℝ) ≤ n)
    (hsize : L*n^2 ≤ (D.card : ℝ)) :
    concentrationEnergy D/(D.card : ℝ)^2 ≤ 2/L := by
  let a : ℝ := D.card
  let b : ℝ := ((2*R+1)^d : ℕ)
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have ha : 0 < a := (mul_pos hL (sq_pos_of_pos hn0)).trans_le hsize
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hpair : concentrationEnergy D ≤ a*b+a^2/((R : ℝ)+1) := by
    calc
      _ ≤ ∑ _x ∈ D, (b+a/((R : ℝ)+1)) :=
        Finset.sum_le_sum (fun x _ => concentration_kernel_row hd D x R)
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; dsimp only [a]; ring
  have hba : b/a ≤ 1/L := by
    apply (div_le_div_iff₀ ha hL).mpr
    have hbn : b ≤ n^2 := hball.trans (by nlinarith [sq_nonneg (n-1)])
    simpa only [mul_comm,one_mul,mul_one] using (mul_le_mul_of_nonneg_left hbn hL.le).trans hsize
  have htail : 1/((R : ℝ)+1) ≤ 1/L := one_div_le_one_div_of_le hL hRL
  have heq : (a*b+a^2/((R : ℝ)+1))/a^2 = b/a+1/((R : ℝ)+1) := by
    have hR : (R : ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [ne_of_gt ha,hR] <;> ring
  calc
    _ ≤ (a*b+a^2/((R : ℝ)+1))/a^2 := div_le_div_of_nonneg_right hpair (sq_nonneg _)
    _ = _ := heq
    _ ≤ 1/L+1/L := add_le_add hba htail
    _ = _ := by ring

private theorem concentration_budget_identity (d : ℕ) {n a b SA SB : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    n^((10 : ℝ)-2*(d : ℝ))*(a*b^2+a^2*b)+
      (n^((6 : ℝ)-2*(d : ℝ))+n^((16 : ℝ)-3*(d : ℝ)))*a^2*b^2+
      a*b*n^((4 : ℝ)-(d : ℝ))+
      n^((8 : ℝ)-2*(d : ℝ))*(b^2*SA+a^2*SB) =
    (n^((4 : ℝ)-(d : ℝ))*a*b)^2*
      (n^((d : ℝ)-4)/(a*b)+n^2/a+n^2/b+n^(-2 : ℝ)+n^((8 : ℝ)-(d : ℝ))+
        SA/a^2+SB/b^2) := by
  have h10 : n^((10 : ℝ)-2*(d : ℝ)) = n^((8 : ℝ)-2*(d : ℝ))*n^2 := by
    rw [← Real.rpow_natCast n 2,← Real.rpow_add hn]
    congr 1
    ring
  have h6 : n^((6 : ℝ)-2*(d : ℝ)) = n^((8 : ℝ)-2*(d : ℝ))*n^(-2 : ℝ) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have h16 : n^((16 : ℝ)-3*(d : ℝ)) =
      n^((8 : ℝ)-2*(d : ℝ))*n^((8 : ℝ)-(d : ℝ)) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have h4 : n^((4 : ℝ)-(d : ℝ)) = n^((8 : ℝ)-2*(d : ℝ))*n^((d : ℝ)-4) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hsq : (n^((4 : ℝ)-(d : ℝ)))^2 = n^((8 : ℝ)-2*(d : ℝ)) := by
    rw [pow_two,← Real.rpow_add hn]
    congr 1
    ring
  conv_rhs => rw [mul_pow,mul_pow,hsq]
  rw [h10,h6,h16,h4]
  field_simp [ne_of_gt ha,ne_of_gt hb] <;> ring

private theorem concentration_budget_small (d : ℕ) (hd : 9 ≤ d)
    {L n a b SA SB : ℝ} (hL : 0 < L) (hn : 1 ≤ n) (hLn : L ≤ n)
    (ha : 0 < a) (hb : 0 < b) (hA : L*n^2 ≤ a) (hB : L*n^2 ≤ b)
    (hAB : L*n^((d : ℝ)-2) ≤ a*b)
    (hSA : SA/a^2 ≤ 2/L) (hSB : SB/b^2 ≤ 2/L) :
    n^((10 : ℝ)-2*(d : ℝ))*(a*b^2+a^2*b)+
      (n^((6 : ℝ)-2*(d : ℝ))+n^((16 : ℝ)-3*(d : ℝ)))*a^2*b^2+
      a*b*n^((4 : ℝ)-(d : ℝ))+
      n^((8 : ℝ)-2*(d : ℝ))*(b^2*SA+a^2*SB) ≤
        (9/L)*(n^((4 : ℝ)-(d : ℝ))*a*b)^2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hterm : n^((d : ℝ)-4)/(a*b) ≤ 1/L := by
    apply (div_le_div_iff₀ (mul_pos ha hb) hL).mpr
    have hp := Real.rpow_le_rpow_of_exponent_le hn (by linarith : (d : ℝ)-4 ≤ (d : ℝ)-2)
    have hh := (mul_le_mul_of_nonneg_left hp hL.le).trans hAB
    simpa only [mul_comm,one_mul,mul_one] using hh
  have hta : n^2/a ≤ 1/L := by
    apply (div_le_div_iff₀ ha hL).mpr
    simpa only [mul_comm,one_mul,mul_one] using hA
  have htb : n^2/b ≤ 1/L := by
    apply (div_le_div_iff₀ hb hL).mpr
    simpa only [mul_comm,one_mul,mul_one] using hB
  have hneg : n^(-2 : ℝ) ≤ 1/L := by
    calc
      _ ≤ n^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      _ = 1/n := by rw [Real.rpow_neg_one,one_div]
      _ ≤ _ := one_div_le_one_div_of_le hL hLn
  have hdim : n^((8 : ℝ)-(d : ℝ)) ≤ 1/L := by
    calc
      _ ≤ n^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
      _ = 1/n := by rw [Real.rpow_neg_one,one_div]
      _ ≤ _ := one_div_le_one_div_of_le hL hLn
  have hsum : n^((d : ℝ)-4)/(a*b)+n^2/a+n^2/b+n^(-2 : ℝ)+n^((8 : ℝ)-(d : ℝ))+
      SA/a^2+SB/b^2 ≤ 9/L := by
    have htwo : (2 : ℝ)/L = 2*(1/L) := by ring
    have hnine : (9 : ℝ)/L = 9*(1/L) := by ring
    rw [htwo] at hSA hSB
    rw [hnine]
    linarith only [hterm,hta,htb,hneg,hdim,hSA,hSB]
  rw [concentration_budget_identity d hn0 ha hb]
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans_eq (mul_comm _ _)

/-- Actual source pivotal concentration. The regularity tolerance is fixed
before r; the cardinality threshold and minimum scale are chosen after r and
ε, and all three source size conditions are retained. -/
theorem section9_source_pivotal_concentration {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∃ N : ℕ, 16*(r+1) ≤ N ∧
      ∀ (i : Fin d) (n : ℕ), N ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      (∀ x ∈ A, x ∈ section8ExtensionPositiveFaceCore i n) →
      (∀ x ∈ A, sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δ x) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary₃ r δ y) →
      cSize*(n : ℝ)^2 ≤ (A.card : ℝ) → cSize*(n : ℝ)^2 ≤ (B.card : ℝ) →
      cSize*(n : ℝ)^((d : ℝ)-2) ≤ (A.card : ℝ)*(B.card : ℝ) →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      let m := section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A B
      1-ε ≤ ν.real {ω | m/2 ≤ section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∧
        section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤ 3*m/2} := by
  obtain ⟨δ,hδ,hmean⟩ := section9_source_pivotal_mean_lower hd asymptotics rectangle reimer
  obtain ⟨C,hC,hvariance⟩ := section9_conditioned_pivotal_variance_paper_bound hd asymptotics
  refine ⟨δ,hδ,?_⟩
  intro r hr ε hε
  obtain ⟨c,hc,N₀,hN₀,hmeanr⟩ := hmean r hr
  let ℓ : ℝ := 1+100*(C+1)/(ε*c^2)
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; positivity
  have hεc : 0 < ε*c^2 := mul_pos hε (sq_pos_of_pos hc)
  have hℓeq : (ε*c^2)*ℓ = ε*c^2+100*(C+1) := by
    dsimp only [ℓ]
    field_simp [ne_of_gt hε,ne_of_gt hc] <;> ring
  have hsmall : C*(9/ℓ) ≤ ε*c^2/4 := by
    have hh : 9*C ≤ (ε*c^2/4)*ℓ := by nlinarith only [hℓeq,hεc,hC]
    simpa only [mul_div_assoc,mul_comm] using (div_le_iff₀ hℓ).mpr hh
  obtain ⟨R₀,hR₀⟩ := exists_nat_gt ℓ
  let N := max N₀ (max R₀ (max ((2*R₀+1)^d) 1))
  refine ⟨ℓ,hℓ,N,hN₀.trans (le_max_left _ _),?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B hH₁ hH₃ hpos hA hAreg hB hBreg hAc hBc hAB
    L R Q₁ Q₃ ν E m
  have hnn : 1 ≤ n := by dsimp only [N] at hn; omega
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnn
  have hℓn : ℓ ≤ (n : ℝ) := hR₀.le.trans (by exact_mod_cast (show R₀ ≤ n by dsimp only [N] at hn; omega))
  have hball : (((2*R₀+1)^d : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (show (2*R₀+1)^d ≤ n by dsimp only [N] at hn; omega)
  have hRℓ : ℓ ≤ (R₀ : ℝ)+1 := by linarith
  let a : ℝ := A.card
  let b : ℝ := B.card
  let s : ℝ := (n : ℝ)^((4 : ℝ)-(d : ℝ))*a*b
  have ha : 0 < a := (mul_pos hℓ (sq_pos_of_pos (zero_lt_one.trans_le hnR))).trans_le hAc
  have hb : 0 < b := (mul_pos hℓ (sq_pos_of_pos (zero_lt_one.trans_le hnR))).trans_le hBc
  have hs : 0 < s := mul_pos (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hnR) _) ha) hb
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hmraw := hmeanr i n (by dsimp only [N] at hn; omega) H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B
    hH₁ hH₃ hpos hA hAreg hB hBreg
  have hmlower : c*s ≤ m := by
    change c*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ≤ m at hmraw
    simpa only [s,a,b,mul_assoc] using hmraw
  have hm : 0 < m := (mul_pos hc hs).trans_le hmlower
  have hSA : concentrationEnergy A/a^2 ≤ 2/ℓ :=
    concentration_energy_ratio hd A R₀ hℓ hnR hRℓ hball hAc
  have hSB : concentrationEnergy B/b^2 ≤ 2/ℓ :=
    concentration_energy_ratio hd B R₀ hℓ hnR hRℓ hball hBc
  have hbudget := concentration_budget_small d hd hℓ hnR hℓn ha hb hAc hBc hAB hSA hSB
  let V : ℝ := ∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω-m)^2 ∂ν
  have hv := hvariance i n hn0 L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos
    (section9FiniteLeftTube_disjoint_third i hn0) (section9FiniteRightTube_disjoint_first i hn0)
    (fun u hu => (Finset.mem_filter.mp hu).1) (fun u hu => (Finset.mem_filter.mp hu).1)
    (fun x hx => (Finset.mem_filter.mp (hA x hx)).1)
    (fun y hy => (Finset.mem_filter.mp (hB y hy)).1)
  have hV : V ≤ ε*(m/2)^2 := by
    calc
      _ ≤ C*((n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(a*b^2+a^2*b)+
          ((n : ℝ)^((6 : ℝ)-2*(d : ℝ))+(n : ℝ)^((16 : ℝ)-3*(d : ℝ)))*a^2*b^2+
          a*b*(n : ℝ)^((4 : ℝ)-(d : ℝ))+
          (n : ℝ)^((8 : ℝ)-2*(d : ℝ))*(b^2*concentrationEnergy A+a^2*concentrationEnergy B)) := hv
      _ ≤ C*((9/ℓ)*s^2) := mul_le_mul_of_nonneg_left hbudget hC
      _ = (C*(9/ℓ))*s^2 := by ring
      _ ≤ (ε*c^2/4)*s^2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
      _ ≤ ε*(m/2)^2 := by
        have hsq : (c*s)^2 ≤ m^2 := pow_le_pow_left₀ (mul_pos hc hs).le hmlower 2
        have hh := mul_le_mul_of_nonneg_left hsq hε.le
        nlinarith only [hh]
  have hratio : V/(m/2)^2 ≤ ε := (div_le_iff₀ (sq_pos_of_pos (div_pos hm (by norm_num)))).mpr hV
  have hinter := section9_actual_pivotal_relative_interval ν E L R Q₁ F₁ Q₃ F₃ A B hm
  change 1-V/(m/2)^2 ≤ _ at hinter
  exact (sub_le_sub_left hratio 1).trans hinter

end NearCritical
