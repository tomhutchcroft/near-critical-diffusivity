module
public import NearCritical.Section9CriticalTargetCount
public import NearCritical.Section9SharedPhysicalTargetMoment
public import NearCritical.Section9PhysicalTargetSuccess
public import NearCritical.Section9PhysicalTargetOpening
public import NearCritical.Section9TwoStageProbability
public import NearCritical.Section9SprinkleOrLaw

/-! Actual source many-target success under the first-critical-reveal law
and an independent fresh configuration, without an enriched reveal substitution. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem opened_source_local_event_measurable {d : ℕ}
    (U : Finset (Bond d)) (A : Set (Configuration d))
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ U, ω b = θ b) → (ω ∈ A ↔ θ ∈ A)) :
    MeasurableSet A := by
  let A₀ : Set ((b : U) → Bool) := {ξ | extendConfiguration U (fun _ => false) ξ ∈ A}
  have heq : A = U.restrict ⁻¹' A₀ := by
    ext ω
    apply hlocal ω (extendConfiguration U (fun _ => false) (U.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  rw [heq]
  exact (Set.toFinite A₀).measurableSet.preimage (Finset.measurable_restrict U)

private theorem opened_source_success_measurable {d : ℕ} {ι : Type*}
    (I : Finset ι) (targets : ι → Finset (Vertex d))
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d)) (m : ℕ) :
    MeasurableSet {z : Configuration d × Configuration d | (m : ℝ) <
      ((I.filter fun j => (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
        E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} := by
  let H := fun j => {z : Configuration d × Configuration d |
    (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
      E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty}
  have hm (j : ι) : MeasurableSet (H j) := by
    have heq : H j = ⋃ e : Vertex d × Vertex d,
        ({z : Configuration d × Configuration d | e ∈ E} ∩
          {z | sprinklingPivotalPair z.1 L R Q₁ F₁ Q₃ F₃ A (targets j) e}) ∩
          {z | (openGraph (sprinkleOrConfiguration z.1 z.2)).Adj e.1 e.2} := by
      ext z
      simp only [H,sprinkledPivotalPairs,sprinklingPivotalPairs,Finset.Nonempty,
        Finset.mem_filter,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_setOf_eq]
    rw [heq]
    apply MeasurableSet.iUnion
    intro e
    exact ((MeasurableSet.const _).inter
      ((measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A (targets j) e).preimage measurable_fst)).inter
      ((measurableSet_open_adj e.1 e.2).preimage measurable_sprinkleOrConfiguration)
  have hcount : Measurable (fun z : Configuration d × Configuration d =>
      ((I.filter fun j => z ∈ H j).card : ℝ)) := by
    have heq : (fun z : Configuration d × Configuration d => ((I.filter fun j => z ∈ H j).card : ℝ)) =
        fun z => ∑ j ∈ I, if z ∈ H j then (1 : ℝ) else 0 := by
      funext z
      rw [Finset.sum_boole]
    rw [heq]
    exact I.measurable_fun_sum (fun j _ => measurable_const.piecewise (hm j) measurable_const)
  exact measurableSet_lt measurable_const hcount

/-- Corrected source many-target sprinkling statement in the honest joint law:
first sample the actual critical heart-reveal law, then an independent fresh
configuration, and count actual OR-opened canonical pivots. -/
theorem section9_source_many_opened_pivotal_targets {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ m : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N : ℕ, 16*(r+1) ≤ N ∧ ∀ (i : Fin d) (n : ℕ), N ≤ n →
      ∀ q : unitInterval, Lambda ≤ (q : ℝ)*(n : ℝ)^2 →
      ∀ {ι : Type*} (I : Finset ι) (targets : ι → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ boundary₁ boundary₃ A : Finset (Vertex d)),
      let B := I.biUnion targets
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      (∀ x ∈ A, x ∈ section8ExtensionPositiveFaceCore i n) →
      (∀ x ∈ A, sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δ x) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary₃ r δ y) →
      Set.PairwiseDisjoint (I : Set ι) targets →
      (A.card : ℝ) ≤ KA*(n : ℝ)^2 →
      (∀ j ∈ I, ((targets j).card : ℝ) ≤ CB*(n : ℝ)^2) →
      cSize*(n : ℝ)^2 ≤ (A.card : ℝ) → cSize*(n : ℝ)^2 ≤ (B.card : ℝ) →
      cSize*(n : ℝ)^((d : ℝ)-2) ≤ (A.card : ℝ)*(B.card : ℝ) →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      1-ε ≤ (ν.prod (percolation d q)).real {z : Configuration d × Configuration d |
        (m : ℝ) < ((I.filter fun j =>
          (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
            E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} := by
  obtain ⟨δ,hδ,hcritical⟩ := section9_source_many_critical_pivotal_targets hd asymptotics rectangle reimer
  refine ⟨δ,hδ,?_⟩
  intro r hr ε hε
  obtain ⟨cSize,hSize,c0,hc0,hactive⟩ := hcritical r hr (ε/3) (by positivity)
  obtain ⟨Kw,hKw,hoverlap⟩ := section9_source_shared_physical_target_moment_upper hd asymptotics r hr δ hδ.le
  let κ : ℝ := 3*(Kw+1)/ε
  have hκ : 0 < κ := div_pos (mul_pos (by norm_num) (by linarith)) hε
  refine ⟨cSize,hSize,?_⟩
  intro m
  let T : ℝ := max (2*((m : ℝ)+1)/c0) (4*(1+κ/c0)/((ε/3)*c0))
  let Lambda : ℝ := max 1 (T/cSize)
  have hLambda : 0 < Lambda := zero_lt_one.trans_le (le_max_left _ _)
  have hthreshold : T ≤ cSize*Lambda := by
    have hh : T/cSize ≤ Lambda := le_max_right _ _
    have hm := (div_le_iff₀ hSize).mp hh
    simpa only [mul_comm] using hm
  refine ⟨Lambda,hLambda,?_⟩
  intro CB KA hCB hKA
  obtain ⟨N,hN,hactiveN⟩ := hactive CB KA hCB hKA
  refine ⟨N,hN,?_⟩
  intro i n hn q hq ι I targets H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B hH₁ hH₃ hpos
    hA hAreg hB hBreg hdis hAc hBc hAsize hBsize hAB L R Q₁ Q₃ ν E
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let F : ℝ := (n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ)
  have ha : 0 < (A.card : ℝ) := (mul_pos hSize (sq_pos_of_pos hnpos)).trans_le hAsize
  have hb : 0 < (B.card : ℝ) := (mul_pos hSize (sq_pos_of_pos hnpos)).trans_le hBsize
  have hF : 0 < F := mul_pos (mul_pos (Real.rpow_pos_of_pos hnpos _) ha) hb
  obtain ⟨bond,hbond⟩ := section9_middle_candidate_bond_map i n
  let Pi := fun ω j => sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j)
  let pools := fun ω j => (Pi ω j).image bond
  let M₀ := fun ω : Configuration d => ((I.filter fun j => (pools ω j).Nonempty).card : ℝ)
  let W := fun ω : Configuration d => ∑ j ∈ I, ∑ k ∈ I.erase j,
    (((pools ω j) ∩ (pools ω k)).card : ℝ)
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  have hfamily (ω θ : Configuration d) (hagree : ∀ b ∈ U, ω b = θ b) : Pi ω = Pi θ := by
    funext j
    ext e
    have hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = θ b :=
      fun b hb => hagree b (Finset.mem_union_left _ hb)
    have hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = θ b :=
      fun b hb => hagree b (Finset.mem_union_right _ hb)
    simp only [Pi,sprinklingPivotalPairs,Finset.mem_filter,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A (targets j) ω θ hL hR e]
  have hMlocal (ω θ : Configuration d) (hagree : ∀ b ∈ U, ω b = θ b) : M₀ ω = M₀ θ := by
    apply congrArg (fun S : Finset ι => (S.card : ℝ))
    ext j
    simp only [Finset.mem_filter, pools, hfamily ω θ hagree]
  have hWlocal (ω θ : Configuration d) (hagree : ∀ b ∈ U, ω b = θ b) : W ω = W θ := by
    dsimp only [W,pools]
    rw [hfamily ω θ hagree]
  have hiW : Integrable W ν := section9_finite_local_integrable ν U W hWlocal
  have hWnonneg (ω : Configuration d) : 0 ≤ W ω :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hWbound : (∫ ω, W ω ∂ν) ≤ Kw*F := by
    have hh := hoverlap i n hn2 I targets H₁ H₃ F₁ F₃ boundary₃ A hH₁ hH₃ hpos
      (fun x hx => (Finset.mem_filter.mp (hA x hx)).1) hdis
      (fun j hj b hb => hB b (Finset.mem_biUnion.mpr ⟨j,hj,hb⟩))
      (fun j hj b hb => hBreg b (Finset.mem_biUnion.mpr ⟨j,hj,hb⟩)) bond hbond
    rw [show Kw * F =
      Kw * (n : ℝ)^((4 : ℝ)-(d : ℝ)) * (A.card : ℝ) * (B.card : ℝ) by
        dsimp only [F]
        ring]
    exact hh
  have hM₀eq (ω : Configuration d) : M₀ ω =
      ((section9PivotalTargets I E L R Q₁ F₁ Q₃ F₃ A targets ω).card : ℝ) := by
    change ((I.filter fun j => (pools ω j).Nonempty).card : ℝ) =
      ((section9PivotalTargets I E L R Q₁ F₁ Q₃ F₃ A targets ω).card : ℝ)
    apply congrArg (fun S : Finset ι => (S.card : ℝ))
    ext j
    simp only [pools,Pi,section9PivotalTargets,section9PivotalCount,
      Finset.mem_filter,Finset.image_nonempty,Nat.cast_ne_zero,Finset.card_ne_zero]
  let Active : Set (Configuration d) := {ω | c0*F ≤ M₀ ω}
  let Bad : Set (Configuration d) := {ω | κ*F ≤ W ω}
  let Good : Set (Configuration d) := {ω | c0*F ≤ M₀ ω ∧ W ω ≤ κ*F}
  have hGood : MeasurableSet Good := opened_source_local_event_measurable U Good (by
    intro ω θ hagree
    simp only [Good,Set.mem_setOf_eq,hMlocal ω θ hagree,hWlocal ω θ hagree])
  have hActiveProb : 1-ε/3 ≤ ν.real Active := by
    have hh := hactiveN i n hn I targets H₁ H₃ F₁ F₃ boundary₁ boundary₃ A
      hH₁ hH₃ hpos hA hAreg hB hBreg hdis hAc hBc hAsize hBsize hAB
    have heq : Active = {ω : Configuration d |
        c0*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ≤
          ((section9PivotalTargets I E L R Q₁ F₁ Q₃ F₃ A targets ω).card : ℝ)} := by
      ext ω
      simp only [Active,Set.mem_setOf_eq,hM₀eq,F,mul_assoc]
    rw [heq]
    exact hh
  have hBadProb : ν.real Bad ≤ ε/3 := by
    have hτ : 0 < κ*F := mul_pos hκ hF
    have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hWnonneg) hiW (κ*F)
    apply (mul_le_mul_iff_right₀ hτ).mp
    have heq : (κ*F)*(ε/3) = (Kw+1)*F := by
      dsimp only [κ]
      field_simp [ne_of_gt hε] <;> ring
    rw [heq]
    exact hm.trans (hWbound.trans (mul_le_mul_of_nonneg_right (by linarith) hF.le))
  have hGoodProb : 1-2*ε/3 ≤ ν.real Good := by
    have hcover : Active ⊆ Bad ∪ Good := by
      intro ω hω
      by_cases hw : κ*F ≤ W ω
      · exact Or.inl hw
      · exact Or.inr ⟨hω,(lt_of_not_ge hw).le⟩
    have hh := (measureReal_mono (μ := ν) hcover (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    linarith only [hh,hActiveProb,hBadProb]
  have hpower : (n : ℝ)^((4 : ℝ)-(d : ℝ))*(n : ℝ)^((d : ℝ)-2) = (n : ℝ)^2 := by
    rw [← Real.rpow_natCast (n : ℝ) 2,← Real.rpow_add hnpos]
    congr 1
    ring
  have hFscale : cSize*(n : ℝ)^2 ≤ F := by
    calc
      _ = cSize*((n : ℝ)^((4 : ℝ)-(d : ℝ))*(n : ℝ)^((d : ℝ)-2)) := by rw [hpower]
      _ = (n : ℝ)^((4 : ℝ)-(d : ℝ))*(cSize*(n : ℝ)^((d : ℝ)-2)) := by ring
      _ ≤ (n : ℝ)^((4 : ℝ)-(d : ℝ))*((A.card : ℝ)*(B.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hAB (Real.rpow_nonneg hnpos.le _)
      _ = _ := by dsimp only [F]; ring
  have hqF : T ≤ (q : ℝ)*F := by
    calc
      _ ≤ cSize*Lambda := hthreshold
      _ ≤ cSize*((q : ℝ)*(n : ℝ)^2) := mul_le_mul_of_nonneg_left hq hSize.le
      _ = (q : ℝ)*(cSize*(n : ℝ)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hFscale q.property.1
  let Success : Set (Configuration d × Configuration d) := {z |
    (m : ℝ) < ((I.filter fun j => (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
      E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)}
  have hSuccess : MeasurableSet Success := opened_source_success_measurable I targets E L R Q₁ F₁ Q₃ F₃ A m
  have hsection (ω : Configuration d) (hω : ω ∈ Good) :
      1-ε/3 ≤ (percolation d q).real ((Prod.mk ω) ⁻¹' Success) := by
    have hfresh := section9_physical_target_success_probability_lower q I (pools ω)
      c0 κ F (ε/3) m hc0 hκ.le hF (by positivity) hω.1 hω.2 hqF
    refine hfresh.trans (measureReal_mono ?_ (measure_ne_top _ _))
    intro ζ hζ
    have hcount := section9_physical_target_success_count_le I E L R Q₁ F₁ Q₃ F₃ A targets bond hbond ω ζ
    exact lt_of_lt_of_le hζ hcount
  have htotal := section9_two_stage_probability_lower ν (percolation d q) Good Success
    hGood hSuccess (2*ε/3) (ε/3) (by positivity) hGoodProb hsection
  change 1-ε ≤ (ν.prod (percolation d q)).real Success
  linarith only [htotal]

end NearCritical
