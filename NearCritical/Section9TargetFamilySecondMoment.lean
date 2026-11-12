module
public import NearCritical.Section9PivotalVariancePaper
public import NearCritical.Section9MeanUpperScale
public import NearCritical.Section9CoalescenceGeometry

/-! Actual target-family second moments, with a uniform leading constant
and a minimum scale depending on the two cardinality caps. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem target_energy_le_card_sq {d : ℕ} (hd : 9 ≤ d) (D : Finset (Vertex d)) :
    (∑ x ∈ D, ∑ y ∈ D, (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))) ≤ (D.card : ℝ)^2 := by
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  calc
    _ ≤ ∑ _x ∈ D, ∑ _y ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hb : 1 ≤ 1+latticeDistance x y := by linarith [latticeDistance_nonneg x y]
      exact (Real.rpow_le_rpow_of_exponent_le hb (by linarith : (8 : ℝ)-(d : ℝ) ≤ 0)).trans_eq
        (Real.rpow_zero _)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

private theorem target_scalar_budget {d : ℕ} (hd : 9 ≤ d)
    {n U C KA CB a b : ℝ} (hn : 1 ≤ n) (hC : 0 ≤ C)
    (hKA : 0 ≤ KA) (hCB : 0 ≤ CB) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : a ≤ KA*n^2) (hB : b ≤ CB*n^2) :
    (U*n^((4 : ℝ)-(d : ℝ))*a*b)^2+
      C*(n^((10 : ℝ)-2*(d : ℝ))*(a*b^2+a^2*b)+
        (n^((6 : ℝ)-2*(d : ℝ))+n^((16 : ℝ)-3*(d : ℝ)))*a^2*b^2+
        a*b*n^((4 : ℝ)-(d : ℝ))+2*n^((8 : ℝ)-2*(d : ℝ))*a^2*b^2) ≤
      (C+(U^2*CB*KA+C*(CB+KA+4*CB*KA))*n^((8 : ℝ)-(d : ℝ)))*
        (n^((4 : ℝ)-(d : ℝ))*a*b) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  let q : ℝ := n^((4 : ℝ)-(d : ℝ))
  let ρ : ℝ := n^((8 : ℝ)-(d : ℝ))
  let F : ℝ := q*a*b
  have hq : 0 ≤ q := Real.rpow_nonneg hn0.le _
  have hρ : 0 ≤ ρ := Real.rpow_nonneg hn0.le _
  have hab : a*b ≤ KA*CB*n^4 := by
    have hh := mul_le_mul hA hB hb (mul_nonneg hKA (sq_nonneg n))
    convert hh using 1 <;> ring
  have hfactor (e f g h : ℝ) (he : e+f = g+h) : n^e*n^f = n^g*n^h := by
    rw [← Real.rpow_add hn0,← Real.rpow_add hn0,he]
  have h8 : n^((8 : ℝ)-2*(d : ℝ))*n^4 = q*ρ := by
    rw [← Real.rpow_natCast n 4]
    exact hfactor _ _ _ _ (by ring)
  have h10 : n^((10 : ℝ)-2*(d : ℝ))*n^2 = q*ρ := by
    rw [← Real.rpow_natCast n 2]
    exact hfactor _ _ _ _ (by ring)
  have h6 : n^((6 : ℝ)-2*(d : ℝ))*n^4 ≤ q*ρ := by
    calc
      _ = q*n^((6 : ℝ)-(d : ℝ)) := by
        rw [← Real.rpow_natCast n 4]
        exact hfactor _ _ _ _ (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn (by linarith : (6 : ℝ)-(d : ℝ) ≤ (8 : ℝ)-(d : ℝ))) hq
  have h16 : n^((16 : ℝ)-3*(d : ℝ))*n^4 ≤ q*ρ := by
    calc
      _ = q*n^((16 : ℝ)-2*(d : ℝ)) := by
        rw [← Real.rpow_natCast n 4]
        exact hfactor _ _ _ _ (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn (by linarith : (16 : ℝ)-2*(d : ℝ) ≤ (8 : ℝ)-(d : ℝ))) hq
  have hpair (e : ℝ) : n^e*a^2*b^2 ≤ KA*CB*(n^e*n^4)*a*b := by
    have hh := mul_le_mul_of_nonneg_left hab (mul_nonneg (Real.rpow_nonneg hn0.le e) (mul_nonneg ha hb))
    convert hh using 1 <;> ring
  have hbase : n^((8 : ℝ)-2*(d : ℝ))*a^2*b^2 ≤ CB*KA*ρ*F := by
    have hh := hpair ((8 : ℝ)-2*(d : ℝ))
    rw [h8] at hh
    convert hh using 1 <;> dsimp only [F] <;> ring
  have hfirstA : n^((10 : ℝ)-2*(d : ℝ))*a*b^2 ≤ CB*ρ*F := by
    have hh := mul_le_mul_of_nonneg_left hB
      (mul_nonneg (Real.rpow_nonneg hn0.le ((10 : ℝ)-2*(d : ℝ))) (mul_nonneg ha hb))
    calc
      _ ≤ CB*(n^((10 : ℝ)-2*(d : ℝ))*n^2)*a*b := by convert hh using 1 <;> ring
      _ = _ := by rw [h10]; dsimp only [F]; ring
  have hfirstB : n^((10 : ℝ)-2*(d : ℝ))*a^2*b ≤ KA*ρ*F := by
    have hh := mul_le_mul_of_nonneg_left hA
      (mul_nonneg (Real.rpow_nonneg hn0.le ((10 : ℝ)-2*(d : ℝ))) (mul_nonneg ha hb))
    calc
      _ ≤ KA*(n^((10 : ℝ)-2*(d : ℝ))*n^2)*a*b := by convert hh using 1 <;> ring
      _ = _ := by rw [h10]; dsimp only [F]; ring
  have hsecond6 : n^((6 : ℝ)-2*(d : ℝ))*a^2*b^2 ≤ CB*KA*ρ*F := by
    refine (hpair _).trans ?_
    have hh := mul_le_mul_of_nonneg_left h6 (mul_nonneg hKA hCB)
    have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg ha hb)
    simpa only [F,mul_assoc,mul_comm,mul_left_comm] using hh'
  have hsecond16 : n^((16 : ℝ)-3*(d : ℝ))*a^2*b^2 ≤ CB*KA*ρ*F := by
    refine (hpair _).trans ?_
    have hh := mul_le_mul_of_nonneg_left h16 (mul_nonneg hKA hCB)
    have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg ha hb)
    simpa only [F,mul_assoc,mul_comm,mul_left_comm] using hh'
  have hsq : (U*n^((4 : ℝ)-(d : ℝ))*a*b)^2 =
      U^2*(n^((8 : ℝ)-2*(d : ℝ))*a^2*b^2) := by
    have hp : (n^((4 : ℝ)-(d : ℝ)))^2 = n^((8 : ℝ)-2*(d : ℝ)) := by
      rw [pow_two,← Real.rpow_add hn0]
      congr 1
      ring
    rw [mul_pow,mul_pow,mul_pow,hp]
    ring
  have hm := mul_le_mul_of_nonneg_left hbase (sq_nonneg U)
  have hA' := mul_le_mul_of_nonneg_left hfirstA hC
  have hB' := mul_le_mul_of_nonneg_left hfirstB hC
  have h6' := mul_le_mul_of_nonneg_left hsecond6 hC
  have h16' := mul_le_mul_of_nonneg_left hsecond16 hC
  have he := mul_le_mul_of_nonneg_left hbase (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
  rw [hsq]
  dsimp only [F,q,ρ] at hm hA' hB' h6' h16' he ⊢
  nlinarith only [hm,hA',hB',h6',h16',he]

/-- Actual source M2 for any finite disjoint target family. Its leading
constant is uniform before both cardinality caps; only the minimum scale
depends on those caps. No regularity or lower-cardinality condition is needed. -/
theorem section9_source_target_family_second_moment_upper {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ (i : Fin d) (n : ℕ), N ≤ n →
      ∀ {ι : Type*} (I : Finset ι) (targets : ι → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ A : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      A ⊆ section9FiniteEndCube i n 0 →
      (∀ j ∈ I, targets j ⊆ section9FiniteEndCube i n (2*(n : ℝ))) →
      Set.PairwiseDisjoint (I : Set ι) targets →
      (A.card : ℝ) ≤ KA*(n : ℝ)^2 →
      (∀ j ∈ I, ((targets j).card : ℝ) ≤ CB*(n : ℝ)^2) →
      let B := I.biUnion targets
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∫ ω, (∑ j ∈ I, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (targets j) ω)^2) ∂ν) ≤
        K₂*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨U,hU,hupper⟩ := section9ConditionalMean_upper_scale (by omega : 2 ≤ d) asymptotics
  obtain ⟨C,hC,hvariance⟩ := section9_conditioned_pivotal_variance_paper_bound hd asymptotics
  refine ⟨C+1,by linarith,?_⟩
  intro CB KA hCB hKA
  let H : ℝ := U^2*CB*KA+C*(CB+KA+4*CB*KA)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt H
  let N := max N₀ 1
  refine ⟨N,le_max_right _ _,?_⟩
  intro i n hn ι I targets H₁ H₃ F₁ F₃ A hH₁ hH₃ hpos hA htargets hdis hAc hBc
    B L R Q₁ Q₃ ν E
  have hnn : 1 ≤ n := (le_max_right N₀ 1).trans hn
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hHn : H ≤ (n : ℝ) := hN₀.le.trans (by exact_mod_cast ((le_max_left N₀ 1).trans hn))
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hrem : H*(n : ℝ)^((8 : ℝ)-(d : ℝ)) ≤ 1 := by
    calc
      _ ≤ H*(n : ℝ)^(-1 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnR (by linarith)) hH
      _ = H/(n : ℝ) := by rw [Real.rpow_neg_one]; ring
      _ ≤ _ := (div_le_iff₀ hnpos).mpr (by simpa only [one_mul] using hHn)
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let a : ℝ := A.card
  have hSA : (∑ x ∈ A, ∑ y ∈ A, (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))) ≤ a^2 :=
    target_energy_le_card_sq hd A
  have hsecond (j : ι) (hj : j ∈ I) :
      (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (targets j) ω)^2 ∂ν) ≤
        (C+1)*(n : ℝ)^((4 : ℝ)-(d : ℝ))*a*((targets j).card : ℝ) := by
    let D := targets j
    let b : ℝ := D.card
    let m := section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A D
    let V : ℝ := ∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A D ω-m)^2 ∂ν
    let F : ℝ := (n : ℝ)^((4 : ℝ)-(d : ℝ))*a*b
    have ha : 0 ≤ a := Nat.cast_nonneg _
    have hb : 0 ≤ b := Nat.cast_nonneg _
    have hF : 0 ≤ F := mul_nonneg (mul_nonneg (Real.rpow_nonneg hnpos.le _) ha) hb
    have hm : 0 ≤ m := integral_nonneg (fun ω => section9PivotalCount_nonneg E L R Q₁ F₁ Q₃ F₃ A D ω)
    have hmu := hupper i n hn0 H₁ H₃ F₁ F₃ A D hH₁ hH₃ hA (htargets j hj) hpos
    have hmsq : m^2 ≤ (U*(n : ℝ)^((4 : ℝ)-(d : ℝ))*a*b)^2 :=
      pow_le_pow_left₀ hm hmu 2
    have hSB := target_energy_le_card_sq hd D
    change (∑ x ∈ D, ∑ y ∈ D, (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))) ≤ b^2 at hSB
    have hv := hvariance i n hn0 L R Q₁ H₁ F₁ Q₃ H₃ F₃ A D hH₁ hH₃ hpos
      (section9FiniteLeftTube_disjoint_third i hn0) (section9FiniteRightTube_disjoint_first i hn0)
      (fun u hu => (Finset.mem_filter.mp hu).1) (fun u hu => (Finset.mem_filter.mp hu).1) hA (htargets j hj)
    have henergy := add_le_add
      (mul_le_mul_of_nonneg_left hSA (sq_nonneg b))
      (mul_le_mul_of_nonneg_left hSB (sq_nonneg a))
    have henergyC := mul_le_mul_of_nonneg_left henergy
      (mul_nonneg hC (Real.rpow_nonneg hnpos.le ((8 : ℝ)-2*(d : ℝ))))
    have hv' : V ≤ C*((n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(a*b^2+a^2*b)+
        ((n : ℝ)^((6 : ℝ)-2*(d : ℝ))+(n : ℝ)^((16 : ℝ)-3*(d : ℝ)))*a^2*b^2+
        a*b*(n : ℝ)^((4 : ℝ)-(d : ℝ))+2*(n : ℝ)^((8 : ℝ)-2*(d : ℝ))*a^2*b^2) := by
      change V ≤ C*((n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(a*b^2+a^2*b)+
        ((n : ℝ)^((6 : ℝ)-2*(d : ℝ))+(n : ℝ)^((16 : ℝ)-3*(d : ℝ)))*a^2*b^2+
        a*b*(n : ℝ)^((4 : ℝ)-(d : ℝ))+
        (n : ℝ)^((8 : ℝ)-2*(d : ℝ))*(b^2*(∑ x ∈ A, ∑ y ∈ A,
          (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ)))+
        a^2*(∑ x ∈ D, ∑ y ∈ D,(1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))))) at hv
      nlinarith only [hv,henergyC]
    have hscalar := target_scalar_budget (U := U) hd hnR hC hKA.le hCB.le ha hb hAc (hBc j hj)
    have hid := section9PivotalCount_centered_identity ν E L R Q₁ F₁ Q₃ F₃ A D
    have hraw : (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A D ω)^2 ∂ν) ≤
        (C+H*(n : ℝ)^((8 : ℝ)-(d : ℝ)))*F := by
      change V = (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A D ω)^2 ∂ν)-m^2 at hid
      change _ ≤ (C+H*(n : ℝ)^((8 : ℝ)-(d : ℝ)))*F at hscalar
      linarith only [hv',hmsq,hscalar,hid]
    calc
      _ ≤ (C+H*(n : ℝ)^((8 : ℝ)-(d : ℝ)))*F := hraw
      _ ≤ (C+1)*F := mul_le_mul_of_nonneg_right (add_le_add le_rfl hrem) hF
      _ = _ := by dsimp only [F]; ring
  have hcards : (∑ j ∈ I, ((targets j).card : ℝ)) = (B.card : ℝ) := by
    have hh := Finset.card_biUnion hdis
    exact_mod_cast hh.symm
  calc
    _ = ∑ j ∈ I, ∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (targets j) ω)^2 ∂ν :=
      integral_finsetSum I (fun j _ => integrable_section9PivotalCount_sq ν E L R Q₁ F₁ Q₃ F₃ A (targets j))
    _ ≤ ∑ j ∈ I, ((C+1)*(n : ℝ)^((4 : ℝ)-(d : ℝ))*a*((targets j).card : ℝ)) :=
      Finset.sum_le_sum hsecond
    _ = (C+1)*(n : ℝ)^((4 : ℝ)-(d : ℝ))*a*(∑ j ∈ I, ((targets j).card : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [hcards]

end NearCritical
