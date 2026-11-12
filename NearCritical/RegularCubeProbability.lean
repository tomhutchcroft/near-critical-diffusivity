module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Proof of source prop.regular_cube (3922–4010) from its two inputs.

Abstract per-configuration data: a finite family `Ks ω` of PAIRWISE DISJOINT
clusters, a core set, finitely many faces `face i` (the 2d faces), and the
regular-point sets `R ω i` on each face. With thresholds `a` (cluster count,
source `c₂ n^{d-6}`) and `s` (face mass, source `c₂ n²`):

* `spanningCount ω`: clusters meeting the core with `≥ s` points on every face;
* `regularCount ω`: clusters meeting the core with `≥ s/2` REGULAR points on every
  face (`(r, c₂/2)`-regular clusters);
* `badCount ω i`: non-regular points of `⋃ Ks ω` on face `i`.

`bad_of_spanning_not_regular` (deterministic): `a ≤ spanning`, `regular < a/2`
⇒ `(a/2)(s/2) ≤ Σᵢ badᵢ`. `regular_cube_not_regular_le` (Markov + union):
`ℙ[spanning < a] ≤ ε/2` (Lemma neopzmk) and `𝔼[badᵢ] ≤ η` (prop.choice_c) with
`|faces|·η / ((a/2)(s/2)) ≤ ε/2` give `ℙ[regular < a/2] ≤ ε`. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Finset
open scoped ENNReal Classical

variable {V ι : Type*} [Fintype ι]

def spanningCount (Ks : Finset (Finset V)) (core : Finset V) (face : ι → Finset V)
    (s : ℝ) : ℕ :=
  (Ks.filter (fun C => (C ∩ core).Nonempty ∧ ∀ i, s ≤ ((C ∩ face i).card : ℝ))).card

def regularCount (Ks : Finset (Finset V)) (core : Finset V) (face R : ι → Finset V)
    (s : ℝ) : ℕ :=
  (Ks.filter (fun C => (C ∩ core).Nonempty ∧
    ∀ i, s / 2 ≤ (((C ∩ face i) ∩ R i).card : ℝ))).card

def badCount (Ks : Finset (Finset V)) (face R : ι → Finset V) (i : ι) : ℕ :=
  (((Ks.biUnion id) ∩ face i) \ R i).card

theorem bad_of_spanning_not_regular (Ks : Finset (Finset V))
    (hdisj : (Ks : Set (Finset V)).PairwiseDisjoint id) (core : Finset V)
    (face R : ι → Finset V) {a s : ℝ} (hs : 0 ≤ s)
    (hspan : a ≤ spanningCount Ks core face s)
    (hreg : (regularCount Ks core face R s : ℝ) < a / 2) :
    (a / 2) * (s / 2) ≤ ∑ i, (badCount Ks face R i : ℝ) := by
  set S := Ks.filter (fun C => (C ∩ core).Nonempty ∧ ∀ i, s ≤ ((C ∩ face i).card : ℝ))
  set G := Ks.filter (fun C => (C ∩ core).Nonempty ∧
    ∀ i, s / 2 ≤ (((C ∩ face i) ∩ R i).card : ℝ))
  have hcardS : a ≤ (S.card : ℝ) := hspan
  have hcardG : (G.card : ℝ) < a / 2 := hreg
  have hle : (S.card : ℝ) ≤ ((S \ G).card : ℝ) + G.card := by
    exact_mod_cast card_le_card_sdiff_add_card
  have hT : a / 2 ≤ ((S \ G).card : ℝ) := by linarith
  -- per-cluster bad mass
  let f : Finset V → ℝ := fun C => ∑ i, ((((C ∩ face i) \ R i).card : ℕ) : ℝ)
  have hf : ∀ C ∈ S \ G, s / 2 ≤ f C := by
    intro C hC
    rw [mem_sdiff] at hC
    obtain ⟨hCS, hCG⟩ := hC
    rw [mem_filter] at hCS
    obtain ⟨hCK, hcore, hface⟩ := hCS
    have : ¬ ∀ i, s / 2 ≤ (((C ∩ face i) ∩ R i).card : ℝ) := by
      intro h
      exact hCG (mem_filter.2 ⟨hCK, hcore, h⟩)
    push_neg at this
    obtain ⟨i, hi⟩ := this
    have hsplit := card_sdiff_add_card_inter (C ∩ face i) (R i)
    have hsplit' : ((((C ∩ face i) \ R i).card : ℕ) : ℝ) +
        (((C ∩ face i) ∩ R i).card : ℝ) = ((C ∩ face i).card : ℝ) := by
      exact_mod_cast hsplit
    have hi' := hface i
    have hone : s / 2 ≤ ((((C ∩ face i) \ R i).card : ℕ) : ℝ) := by linarith
    calc s / 2 ≤ ((((C ∩ face i) \ R i).card : ℕ) : ℝ) := hone
      _ ≤ f C := Finset.single_le_sum (f := fun j => ((((C ∩ face j) \ R j).card : ℕ) : ℝ))
          (fun j _ => Nat.cast_nonneg _) (mem_univ i)
  have hsum1 : (a / 2) * (s / 2) ≤ ∑ C ∈ S \ G, f C := by
    calc (a / 2) * (s / 2) ≤ ((S \ G).card : ℝ) * (s / 2) :=
          mul_le_mul_of_nonneg_right hT (by linarith)
      _ = ∑ _C ∈ S \ G, s / 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ C ∈ S \ G, f C := sum_le_sum hf
  have hsub : S \ G ⊆ Ks := fun C hC => (mem_filter.1 (mem_sdiff.1 hC).1).1
  have hfnn : ∀ C, 0 ≤ f C := fun C => sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hsum2 : ∑ C ∈ S \ G, f C ≤ ∑ C ∈ Ks, f C :=
    sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ => hfnn C)
  have hsum3 : ∑ C ∈ Ks, f C = ∑ i, (badCount Ks face R i : ℝ) := by
    show ∑ C ∈ Ks, ∑ i, ((((C ∩ face i) \ R i).card : ℕ) : ℝ) = _
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    have hset : ((Ks.biUnion id) ∩ face i) \ R i = Ks.biUnion (fun C => (C ∩ face i) \ R i) := by
      ext v
      simp only [mem_sdiff, mem_inter, mem_biUnion, id]
      constructor
      · rintro ⟨⟨⟨C, hC, hv⟩, hf⟩, hR⟩
        exact ⟨C, hC, ⟨hv, hf⟩, hR⟩
      · rintro ⟨C, hC, ⟨hv, hf⟩, hR⟩
        exact ⟨⟨⟨C, hC, hv⟩, hf⟩, hR⟩
    have hpd : (Ks : Set (Finset V)).PairwiseDisjoint (fun C => (C ∩ face i) \ R i) := by
      intro C hC C' hC' hne
      exact Disjoint.mono (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1)
        (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1) (hdisj hC hC' hne)
    unfold badCount
    rw [hset, card_biUnion hpd]
    push_cast
    try rfl
  linarith

theorem regular_cube_not_regular_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Ks : Ω → Finset (Finset V))
    (hdisj : ∀ ω, ((Ks ω : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id)
    (core : Finset V) (face : ι → Finset V) (R : Ω → ι → Finset V)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s) {ε η : ℝ≥0∞}
    (hspan : μ {ω | (spanningCount (Ks ω) core face s : ℝ) < a} ≤ ε / 2)
    (hmeas : ∀ i, Measurable (fun ω => (badCount (Ks ω) face (R ω) i : ℝ≥0∞)))
    (hbad : ∀ i, ∫⁻ ω, (badCount (Ks ω) face (R ω) i : ℝ≥0∞) ∂μ ≤ η)
    (hη : (Fintype.card ι : ℝ≥0∞) * η / ENNReal.ofReal ((a / 2) * (s / 2)) ≤ ε / 2) :
    μ {ω | (regularCount (Ks ω) core face (R ω) s : ℝ) < a / 2} ≤ ε := by
  set thr := ENNReal.ofReal ((a / 2) * (s / 2))
  have hthr0 : thr ≠ 0 :=
    (ENNReal.ofReal_pos.2 (mul_pos (half_pos ha) (half_pos hs))).ne'
  have hsub : {ω | (regularCount (Ks ω) core face (R ω) s : ℝ) < a / 2} ⊆
      {ω | (spanningCount (Ks ω) core face s : ℝ) < a} ∪
        {ω | thr ≤ ∑ i, (badCount (Ks ω) face (R ω) i : ℝ≥0∞)} := by
    intro ω hω
    by_cases hsp : (spanningCount (Ks ω) core face s : ℝ) < a
    · exact Or.inl hsp
    · right
      push_neg at hsp
      have h := bad_of_spanning_not_regular (Ks ω) (hdisj ω) core face (R ω) hs.le hsp hω
      show thr ≤ _
      calc thr ≤ ENNReal.ofReal (∑ i, (badCount (Ks ω) face (R ω) i : ℝ)) :=
            ENNReal.ofReal_le_ofReal h
        _ = ∑ i, (badCount (Ks ω) face (R ω) i : ℝ≥0∞) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Nat.cast_nonneg _)]
            simp
  have hsumMeas : Measurable (fun ω => ∑ i, (badCount (Ks ω) face (R ω) i : ℝ≥0∞)) :=
    Finset.measurable_sum _ fun i _ => hmeas i
  have hmarkov := meas_ge_le_lintegral_div (μ := μ) hsumMeas.aemeasurable hthr0 ENNReal.ofReal_ne_top
  have hint : ∫⁻ ω, ∑ i, (badCount (Ks ω) face (R ω) i : ℝ≥0∞) ∂μ ≤
      (Fintype.card ι : ℝ≥0∞) * η := by
    rw [lintegral_finsetSum _ fun i _ => hmeas i]
    calc ∑ i, ∫⁻ ω, (badCount (Ks ω) face (R ω) i : ℝ≥0∞) ∂μ ≤ ∑ _i : ι, η :=
          sum_le_sum fun i _ => hbad i
      _ = (Fintype.card ι : ℝ≥0∞) * η := by rw [sum_const, card_univ, nsmul_eq_mul]
  calc μ {ω | (regularCount (Ks ω) core face (R ω) s : ℝ) < a / 2}
      ≤ μ ({ω | (spanningCount (Ks ω) core face s : ℝ) < a} ∪
          {ω | thr ≤ ∑ i, (badCount (Ks ω) face (R ω) i : ℝ≥0∞)}) := measure_mono hsub
    _ ≤ μ {ω | (spanningCount (Ks ω) core face s : ℝ) < a} +
          μ {ω | thr ≤ ∑ i, (badCount (Ks ω) face (R ω) i : ℝ≥0∞)} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 :=
        add_le_add hspan (hmarkov.trans ((ENNReal.div_le_div_right hint thr).trans hη))
    _ = ε := ENNReal.add_halves ε

end NearCritical
