import NearCritical.Section10ActualBudget
import NearCritical.Section10MoveCapstone
import NearCritical.Section10RelationsWitness
import NearCritical.Section10StepBoundReduction

noncomputable section

namespace NearCritical.Section10

open Filter MeasureTheory
open scoped Classical

/-- Instantiate the actual flow budget uniformly on a near-critical
window. The pre-good probability is the input from the typical-cluster
construction. The route amplification allowance is chosen before the
typicality constants, and the mesh and diameter factors before the
near-critical window. -/
theorem near_translated_budgets_of_pregood (m : ℕ) (hm : 3 ≤ m)
    (asymp : TwoPointAsymptotics (m+5+1))
    (rectangle : RestrictedRectangleLowerInput (m+5+1)) (reimer : FiniteBernoulliBKRInput)
    [LinearOrder (Finset (Vertex (m+5+1)))] :
    ∃ amp δ : ℝ, 1 < amp ∧ 0 < δ ∧ ∀ (typ : TypicalParameters),
      1 ≤ typ.regularRadius → typ.regularTolerance ≤ δ →
      0 < typ.boundaryLower → 0 < typ.countLower → 0 ≤ typ.boundaryUpper →
      0 ≤ typ.countUpper → 0 ≤ typ.diameterUpper →
    ∀ κ : ℝ, 1 ≤ κ → κ^2 < amp → ∀ t₀ : ℕ,
      (∀ t ≥ t₀, ∀ c : Vertex (m+5+1), κ⁻¹ ≤ ∫ ω,
        (if IsPreGoodCube typ t (coarseCenter t c) ω then (1:ℝ) else 0)
          ∂(percolation (m+5+1) (criticalPoint (m+5+1)))) →
    ∃ p₁ a C : ℝ, (criticalPoint (m+5+1):ℝ) < p₁ ∧ p₁ ≤ 1 ∧ 0 < a ∧ 0 < C ∧
      ∀ p : unitInterval, criticalPoint (m+5+1) < p → (p:ℝ) ≤ p₁ →
        ∃ p₀ q : unitInterval, orParameter p₀ q = p ∧ ∃ t r : ℕ, 1 ≤ t ∧
          ∀ᶠ M : ℕ in atTop, ∃ aC : Vertex (m+5+1),
            translatedCoupledCubeFlowBudget p₀ q aC (0 : Fin (m+5+1))
              (chemicalCoarseRadius M t r) a C := by
  let d := m+5+1
  let pc := criticalPoint d
  have hd : 9 ≤ d := by dsimp only [d]; omega
  have hp₀ : 0 < (pc:ℝ) := criticalPoint_pos_of_twoPointAsymptotics (0 : Fin d) asymp
  have hp₁ : (pc:ℝ) < 1 := criticalPoint_lt_one_of_twoPointAsymptotics (by omega) (0 : Fin d) asymp
  obtain ⟨G₀,hG₀,hG⟩ := criticalSupGreenUpper_of_asymptotics (d := d) (by omega) asymp
  obtain ⟨amp,hamp,hBudget⟩ := actualLayout_translatedBudget (D := m+5) (by omega)
  obtain ⟨δ,hδ,hMove⟩ := actualLayout_hmove m hd asymp rectangle reimer hp₀ hp₁ hG₀.le hG
  refine ⟨amp,δ,hamp,hδ,?_⟩
  intro typ hrad htol hbL hcL hbU hcU hdU κ hκ hκamp t₀ hpre
  have hκ₀ : 0 < κ := zero_lt_one.trans_le hκ
  have hκsq : 0 < κ^2 := pow_pos hκ₀ _
  let rρ := Real.sqrt (amp/κ^2)
  have hratio : 1 < amp/κ^2 := (lt_div_iff₀ hκsq).mpr (by simpa only [one_mul] using hκamp)
  have hrρ : 1 < rρ := by
    simpa only [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hratio)
  let ρ := min (9/8:ℝ) rρ
  have hρ : 1 < ρ := lt_min (by norm_num) hrρ
  have hρ' : ρ ≤ 9/8 := min_le_left _ _
  have hρκ : ρ^2*κ^2 ≤ amp := by
    calc
      _ ≤ rρ^2*κ^2 := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (zero_le_one.trans hρ.le) (min_le_right _ _) _) hκsq.le
      _ = amp := by
        dsimp only [rρ]
        rw [Real.sq_sqrt (zero_le_one.trans hratio.le)]
        field_simp [hκ₀.ne']
  have hρinv : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  obtain ⟨cSize,hSize,hMo⟩ := hMove typ.regularRadius hrad ((1-ρ⁻¹)/2) (by linarith)
  obtain ⟨k,hk₂,hk₁₀,hc₁,hc₃,hRelations⟩ :=
    move_relations_witness_uniform m (by omega) hp₀ hp₁ typ hbL hcL hbU hcU hρ hG₀.le hSize
  have hk : 0 < k := by omega
  obtain ⟨Lambda,hLambda,hCBKA⟩ := hMo (2*k^4-1)
  obtain ⟨N₀,_,hmove⟩ := hCBKA (8*typ.boundaryUpper+1) (4*(k:ℝ)*typ.boundaryUpper+1)
    (by linarith) (by positivity)
  obtain ⟨a,AskN,ha,hMesh⟩ := hRelations Lambda hLambda
  let q₀ := ((2*a:ℕ):ℝ)^2/(4*(1-(pc:ℝ)))
  have hq₀ : 0 ≤ q₀ := by dsimp only [q₀]; positivity
  obtain ⟨C,M₀,T,hC,hBuild⟩ := hBudget asymp q₀ hp₀ hp₁ typ hrad hbU hcL hcU hdU k hk
    (a:ℝ) (4*(AskN:ℝ)) (Nat.cast_nonneg _) (by positivity)
  obtain ⟨p₁,hp₁',hPer⟩ := hMesh (max T (max N₀ t₀))
  refine ⟨(p₁:ℝ),(1/8),C,hp₁',p₁.2.2,by norm_num,hC,?_⟩
  intro p hp hpp
  obtain ⟨q,hq,_,ht,htN,hcount,hcs₂,hexit,hqlo,hqhi,hprob⟩ :=
    hPer p hp (Subtype.coe_le_coe.mp hpp)
  let t := a * chemicalCorrelationScale d p
  let Kdiam := AskN*(2*t)^2
  let B := (typicalCube t (0 : Vertex d)).card
  have hN : N₀ ≤ t := (le_max_left N₀ t₀).trans ((le_max_right T _).trans htN)
  have ht₀ : t₀ ≤ t := (le_max_right N₀ t₀).trans ((le_max_right T _).trans htN)
  have hT : T ≤ t := (le_max_left T _).trans htN
  have htpos : 0 < (t:ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hqhi' : (q:ℝ) ≤ q₀*(t:ℝ)^(-2:ℝ) := by
    rw [Real.rpow_neg htpos.le,Real.rpow_two,← div_eq_mul_inv]
    exact hqhi
  have hcube (c : Vertex d) : (typicalCube t c).card ≤ B := by
    have h := typicalCube_translate t c (0 : Vertex d)
    rw [add_zero] at h
    rw [h,card_translateSites]
  have hcount' : (k:ℝ) ≤ typ.countLower*(2*(t:ℝ))^(d-6) := by
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hkP : (k:ℝ) ≤ (k:ℝ)^4 := le_self_pow₀ hkR (by norm_num)
    have hN : d-6 = m := by dsimp only [d]; omega
    rw [hN]
    nlinarith
  have hlen : (Kdiam:ℝ) ≤ 4*(AskN:ℝ)*(t:ℝ)^2 := by
    dsimp only [Kdiam]
    push_cast
    have h : (AskN:ℝ) * (2*(t:ℝ))^2 = 4*(AskN:ℝ)*(t:ℝ)^2 := by ring
    exact h.le
  have hCorr : (t:ℝ) ≤ (a:ℝ)*(chemicalCorrelationScale d (orParameter pc q):ℝ) := by
    rw [hq]
    exact_mod_cast (le_refl t)
  refine ⟨pc,q,hq,t,(t-1)/2,by omega,?_⟩
  refine Filter.eventually_atTop.mpr ⟨max M₀ 1, fun M hM => ?_⟩
  have hM₀ : M₀ ≤ M := (le_max_left _ _).trans hM
  have hM₁ : 1 ≤ M := (le_max_right _ _).trans hM
  let Λ := actualLayout (m+5) typ t ht k hk B B Kdiam M
  have hms := hmove typ t ht hN rfl htol hbU hcU hbL.le hcL.le q q₀ hq₀ hqlo hqhi
    k hk hk₁₀ (by omega) (by linarith) (by linarith) hc₁ (by simpa only [show m+5+1-6 = m by omega] using hcs₂)
    hc₃ B B Kdiam hcube hcube hprob M
  have hs := Λ.hs_of_move (show 0 < t by omega) M pc q hρ.le hexit hms
  have hsite (s : RSite (m+5)) : κ⁻¹ ≤ coupledProb pc q (Λ.siteEvent s) := by
    by_cases hmem : s ∈ Λ.siteBox
    · let F (ω : Configuration d) :=
        if IsPreGoodCube typ t (coarseCenter t (vecSite s)) ω then (1:ℝ) else 0
      have he : (fun z : Configuration d × Configuration d =>
          if z ∈ Λ.siteEvent s then (1:ℝ) else 0) = fun z => F z.1 := by
        funext z
        simp only [F,NestLayout.siteEvent,Set.mem_setOf_eq,hmem,true_implies] <;> rfl
      have hI := (Λ.hsite s).integrable pc q
      rw [he] at hI
      unfold coupledProb
      rw [he,integral_fst_layer pc q F hI]
      exact hpre t ht₀ (vecSite s)
    · unfold coupledProb
      simp only [NestLayout.siteEvent,Set.mem_setOf_eq,hmem,false_implies,ite_true,
        integral_const,probReal_univ,one_smul]
      exact inv_le_one_of_one_le₀ hκ
  have hb := hBuild t ht hT B B Kdiam M hM₁ hM₀ q hqhi' ρ κ hκ₀ hρ.le hρ' hκ hρκ
    hs hsite hcount' hlen hCorr
  exact ⟨boxCenter d t M,hb⟩

end NearCritical.Section10
