import NearCritical.Section10ActualChargeExpectation
import NearCritical.Section10ChargeScale
import NearCritical.Section10ActualTranslatedBudget

noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- The actual layout supplies the translated cube budget for every
admissible choice of the local success parameters and microscopic
length scales. The success and energy bounds use the same route law. -/
theorem actualLayout_translatedBudget {D : ℕ} [LinearOrder (Finset (Vertex (D+1)))]
    (hd : 7 ≤ D+1) :
    ∃ amp : ℝ, 1 < amp ∧ ∀ (asymp : TwoPointAsymptotics (D+1)) (q₀ : ℝ)
    (hp₀ : 0 < (criticalPoint (D+1) : ℝ)) (hp₁ : (criticalPoint (D+1) : ℝ) < 1)
    (typ : TypicalParameters) (hr : 1 ≤ typ.regularRadius) (hb : 0 ≤ typ.boundaryUpper)
    (hl : 0 < typ.countLower) (hu : 0 ≤ typ.countUpper) (hdiam : 0 ≤ typ.diameterUpper)
    (k : ℕ) (hk : 0 < k) (cCorr cDiam : ℝ) (hcCorr : 0 ≤ cCorr) (hcDiam : 0 ≤ cDiam),
    ∃ (C : ℝ) (M₀ T : ℕ), 0 < C ∧
    ∀ (t : ℕ) (ht : 9 ≤ t), T ≤ t →
    ∀ (MOff Mcoal Kdiam M : ℕ), 1 ≤ M → M₀ ≤ M →
    let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
    let p := criticalPoint (D+1)
    ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (t:ℝ)^(-2:ℝ) →
    ∀ (ρ κ : ℝ) (hκ : 0 < κ), 1 ≤ ρ → ρ ≤ 9/8 → 1 ≤ κ → ρ^2*κ^2 ≤ amp →
    ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
      (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)),
    (k:ℝ) ≤ typ.countLower * (2*(t:ℝ))^(D+1-6) →
    (Kdiam:ℝ) ≤ cDiam*(t:ℝ)^2 →
    (t:ℝ) ≤ cCorr * (chemicalCorrelationScale (D+1) (orParameter p q):ℝ) →
    translatedCoupledCubeFlowBudget p q (boxCenter (D+1) t M) Λ.i₀ (boxRadius t M) (1/8) C := by
  obtain ⟨qT,CT,MT,hqT,hqT',hCT,hTail⟩ := routeLaw_tail (D := D) (by omega)
  obtain ⟨qP,CP,MP,hqP,hqP',hCP,hProb⟩ := routeLabel_good_weight_probability (D := D) (by omega)
  obtain ⟨MS,hMS⟩ := sourceRouteSurvivalMass_eventually_half (D := D) (by omega)
  let qMax := max qT qP
  have hqMax : 0 < qMax := hqT.trans_le (le_max_left _ _)
  have hqMax' : qMax < 1 := max_lt hqT' hqP'
  let amp := (1+qMax)/(2*qMax)
  have hamp : 1 < amp := (lt_div_iff₀ (mul_pos (by norm_num) hqMax)).mpr (by linarith)
  have hamp₀ : 0 ≤ amp := zero_le_one.trans hamp.le
  have hampmax : amp*qMax < 1 := by
    dsimp only [amp]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hqMax)).mpr
    simpa only [one_mul] using mul_lt_mul_of_pos_right (show 1+qMax < 2 by linarith) hqMax
  have hampT : amp*qT < 1 := (mul_le_mul_of_nonneg_left (le_max_left _ _) hamp₀).trans_lt hampmax
  have hampP : amp*qP < 1 := (mul_le_mul_of_nonneg_left (le_max_right _ _) hamp₀).trans_lt hampmax
  obtain ⟨ML,hML⟩ := exists_nat_gt (CP*amp/(1-amp*qP))
  refine ⟨amp,hamp,?_⟩
  intro asymp q₀ hp₀ hp₁ typ hr hb hl hu hdiam k hk cCorr cDiam hcCorr hcDiam
  obtain ⟨Cs,Ct,T,hCs,hCt,hEnergy⟩ :=
    actualLayout_charge_expectation_le hd asymp q₀ hp₀ hp₁ hqT.le hCT MT
      (fun M hM => ⟨(hTail M hM).1,(hTail M hM).2.2⟩) typ hr hb hl hu k hk
  let M₀ := max (max MT MP) (max MS ML)
  let L₀ := (16*typ.diameterUpper+1)*Cs+cDiam*Ct
  let Ccharge := 8*L₀*CT*amp*(2/(1-amp*qT)^2)
  let C := max 1 (Ccharge * (2:ℝ)^(D-1) * cCorr^6)
  have hL₀ : 0 ≤ L₀ := add_nonneg (mul_nonneg (by linarith) hCs) (mul_nonneg hcDiam hCt)
  have hCcharge : 0 ≤ Ccharge := by
    unfold Ccharge
    positivity
  refine ⟨C,M₀,T,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro t ht htT MOff Mcoal Kdiam M hM hM₀ Λ p q hq ρ κ hκ hρ hρ' hκ' hbase hs hsite
    hcount hKdiam hCorr
  let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let μ := (percolation (D+1) p).prod (percolation (D+1) q)
  let A := 8*typ.diameterUpper*(t:ℝ)^2
  let m := 2*M-2
  have hm : m+2 = 2*M := by dsimp only [m]; omega
  have hMS' : MS ≤ M := ((le_max_left MS ML).trans (le_max_right (max MT MP) _)).trans hM₀
  have hMT' : MT ≤ M := ((le_max_left MT MP).trans (le_max_left _ (max MS ML))).trans hM₀
  have hMP' : MP ≤ M := ((le_max_right MT MP).trans (le_max_left _ (max MS ML))).trans hM₀
  have hML' : ML ≤ M := ((le_max_right MS ML).trans (le_max_right (max MT MP) _)).trans hM₀
  have hmass : 0 ≤ sourceRouteSurvivalMass D M :=
    (by norm_num : (0:ℝ) ≤ 1/2).trans (hMS M hMS')
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) hdiam) (sq_nonneg _)
  have hAbound : 2 * (typ.diameterUpper * (2*(t:ℝ))^2) ≤ A :=
    (show 2 * (typ.diameterUpper * (2*(t:ℝ))^2) = A by dsimp only [A]; ring).le
  have ht₁ : 1 ≤ (t:ℝ) := by exact_mod_cast (show 1 ≤ t by omega)
  have hbase' : (ρ*κ)^2 ≤ amp := by rw [mul_pow]; exact hbase
  have hbase₀ : 0 ≤ (ρ*κ)^2 := sq_nonneg _
  have hΛP : (ρ*κ)^2*qP < 1 := (mul_le_mul_of_nonneg_right hbase' hqP.le).trans_lt hampP
  have hlarge : CP*(ρ*κ)^2/(1-(ρ*κ)^2*qP) ≤ (M:ℝ)^(D-1) := by
    have hden : 0 < 1-amp*qP := sub_pos.mpr hampP
    have hden' : 1-amp*qP ≤ 1-(ρ*κ)^2*qP :=
      sub_le_sub_left (mul_le_mul_of_nonneg_right hbase' hqP.le) _
    have hM' : (ML:ℝ) ≤ M := by exact_mod_cast hML'
    calc
      _ ≤ CP*amp/(1-(ρ*κ)^2*qP) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbase' hCP) (hden.le.trans hden')
      _ ≤ CP*amp/(1-amp*qP) := div_le_div_of_nonneg_left (mul_nonneg hCP hamp₀) hden hden'
      _ ≤ (ML:ℝ) := hML.le
      _ ≤ (M:ℝ) := hM'
      _ ≤ _ := by
        have hm' : 1 ≤ (M:ℝ) := by exact_mod_cast hM
        simpa only [pow_one] using (pow_le_pow_right₀ hm' (show 1 ≤ D-1 by omega))
  have hprob := hProb M hMP' p q R.ρ R.S R.hρ R.Bl R.hBl R.hS R.a R.o R.ho hρ R.hs
    R.Es R.hEs R.u R.hu R.hu0 R.humean hκ' R.husq R.w R.hw0 R.hwu R.x₀ hΛP hlarge
  have henergy := hEnergy t ht htT MOff Mcoal Kdiam M hM hMT' q hq ρ κ hκ hρ hρ' hκ' hs hsite
    hcount A Kdiam amp hA (Nat.cast_nonneg _) hbase hampT
  refine actualLayout_translatedBudget_of_charge (D := D) (M := M) (by omega) hM
    typ t ht k hk MOff Mcoal Kdiam p q ρ κ hκ m hm A (1/8) C hmass
    (zero_lt_one.trans_le hρ) hA hAbound hcount hs hsite ?_ ?_
  · simpa only [show m+1+1 = 2*M by omega, NestRule.kernel] using hprob
  · rw [show m+1+1 = 2*M by omega,integral_const_mul]
    let u := (t:ℝ)^(6-((D+1:ℕ):ℝ))
    let Z := (CT / (M:ℝ)^(D-1)) * amp * (2/(1-amp*qT)^2)
    have hu₀ : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hZ : 0 ≤ Z := by unfold Z; positivity
    have hcoef : (2*A+1)*Cs + (Kdiam:ℝ)*Ct ≤ L₀*(t:ℝ)^2 := by
      have ht₂ : 1 ≤ (t:ℝ)^2 := one_le_pow₀ ht₁
      have hAlen : 2*A+1 ≤ (16*typ.diameterUpper+1)*(t:ℝ)^2 := by
        dsimp only [A]
        nlinarith
      calc
        _ ≤ ((16*typ.diameterUpper+1)*(t:ℝ)^2)*Cs + (cDiam*(t:ℝ)^2)*Ct :=
          add_le_add (mul_le_mul_of_nonneg_right hAlen hCs) (mul_le_mul_of_nonneg_right hKdiam hCt)
        _ = _ := by dsimp only [L₀]; ring
    have hnorm := boxRadius_charge_scale_le (d := D+1) (t := t) (M := M)
      (by omega) (by omega) hM hcCorr (Nat.cast_nonneg _) hCorr
    have hdexp : D+1-2 = D-1 := by omega
    rw [hdexp] at hnorm
    have hscaleNonneg :
        0 ≤ cubeFlowNormalization (D+1) (boxRadius t M) *
          (chemicalCorrelationScale (D+1) (orParameter p q):ℝ)^6 :=
      mul_nonneg (cubeFlowNormalization_pos _ _).le (pow_nonneg (Nat.cast_nonneg _) _)
    calc
      _ ≤ 4 * ((2*((2*A+1)*Cs+(Kdiam:ℝ)*Ct)*u)*Z) :=
        mul_le_mul_of_nonneg_left henergy (by norm_num)
      _ ≤ 4 * ((2*(L₀*(t:ℝ)^2)*u)*Z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hu₀) hZ)
          (by norm_num)
      _ = Ccharge * ((t:ℝ)^2*u/(M:ℝ)^(D-1)) := by dsimp only [Ccharge,Z]; ring
      _ ≤ Ccharge * ((2:ℝ)^(D-1)*cCorr^6*cubeFlowNormalization (D+1) (boxRadius t M) *
          (chemicalCorrelationScale (D+1) (orParameter p q):ℝ)^6) :=
        mul_le_mul_of_nonneg_left hnorm hCcharge
      _ = (Ccharge*(2:ℝ)^(D-1)*cCorr^6) *
          (cubeFlowNormalization (D+1) (boxRadius t M) * (chemicalCorrelationScale (D+1) (orParameter p q):ℝ)^6) := by ring
      _ ≤ C * (cubeFlowNormalization (D+1) (boxRadius t M) *
          (chemicalCorrelationScale (D+1) (orParameter p q):ℝ)^6) :=
        mul_le_mul_of_nonneg_right (le_max_right 1 (Ccharge*(2:ℝ)^(D-1)*cCorr^6)) hscaleNonneg
      _ = _ := (mul_assoc C _ _).symm

end NearCritical.Section10
