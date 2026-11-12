module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

/-! Actual uniform k-subset choices in source def.nw.chain. Conditional source
exploration identification remains separate from this finite sampling law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped ENNReal Classical

variable {α : Type*} [MeasurableSpace (Finset α)]
  [MeasurableSingletonClass (Finset α)]

def uniformNestChoice (s : Finset α) (k : ℕ) : Measure (Finset α) :=
  Measure.uniformOfFinset (s.powersetCard k)

lemma uniformNestChoice_apply (s : Finset α) (k : ℕ) (A : Set (Finset α)) :
    uniformNestChoice s k A = ((s.powersetCard k).filter (fun t => t∈A)).card /
      ((s.powersetCard k).card : ℝ≥0∞) := Measure.uniformOfFinset_apply A

lemma uniformNestChoice_probability (s : Finset α) (k : ℕ) (hk : k≤s.card) :
    IsProbabilityMeasure (uniformNestChoice s k) := by
  classical
  constructor
  rw [uniformNestChoice_apply]
  simp only [Set.mem_univ,Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast (Finset.card_ne_zero.mpr (Finset.powersetCard_nonempty.mpr hk))) (by simp)

lemma uniformNestChoice_admissible (s : Finset α) (k : ℕ) (hk : k≤s.card) :
    uniformNestChoice s k {t | t⊆s ∧ t.card=k}=1 := by
  classical
  have he : {t : Finset α | t⊆s ∧ t.card=k} = (s.powersetCard k : Set (Finset α)) := by
    classical
    ext t
    simp
  rw [he,uniformNestChoice_apply]
  simp only [Finset.mem_coe]
  have hf : (s.powersetCard k).filter (fun t => t∈s.powersetCard k) = s.powersetCard k := by
    classical
    ext t; simp
  rw [hf]
  exact ENNReal.div_self (by exact_mod_cast (Finset.card_ne_zero.mpr (Finset.powersetCard_nonempty.mpr hk))) (by simp)

lemma uniformNestChoice_real_apply (s : Finset α) (k : ℕ) (A : Set (Finset α)) :
    (uniformNestChoice s k).real A = (((s.powersetCard k).filter (fun t => t∈A)).card : ℝ) /
      (s.powersetCard k).card := by
  classical
  rw [Measure.real,uniformNestChoice_apply,ENNReal.toReal_div]
  simp

/-- Each offspring is selected with exact probability k/N. -/
theorem uniformNestChoice_mem_probability (s : Finset α) {k : ℕ}
    (hk0 : 1≤k) (hk : k≤s.card) {x : α} (hx : x∈s) :
    (uniformNestChoice s k).real {t | x∈t} = (k:ℝ)/s.card := by
  classical
  rw [uniformNestChoice_real_apply]
  simp only [Set.mem_ofPred_eq]
  have hf : ((s.powersetCard k).filter (fun t => x∈t)).card =
      (s.card-1).choose (k-1) := by
    classical
    simpa using Finset.card_filter_powersetCard_subset ({x}:Finset α) s k
      (by simpa using hx) (by simpa using hk0)
  rw [hf,Finset.card_powersetCard]
  have hn : 1≤s.card := hk0.trans hk
  have hid := Nat.add_one_mul_choose_eq (s.card-1) (k-1)
  rw [Nat.sub_add_cancel hn,Nat.sub_add_cancel hk0] at hid
  have hidR : (s.card:ℝ)*((s.card-1).choose (k-1):ℝ) = (s.card.choose k:ℝ)*(k:ℝ) := by
    classical
    exact_mod_cast hid
  have hN : (s.card:ℝ)≠0 := by exact_mod_cast (by omega : s.card≠0)
  have hc : (s.card.choose k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk))
  apply (div_eq_div_iff hc hN).2
  nlinarith

lemma uniformNestChoice_mem_probability_of_notMem (s : Finset α) (k : ℕ)
    {x : α} (hx : x∉s) : (uniformNestChoice s k).real {t | x∈t}=0 := by
  classical
  rw [uniformNestChoice_real_apply]
  simp only [Set.mem_ofPred_eq]
  have hf : (s.powersetCard k).filter (fun t => x∈t)=∅ := by
    classical
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨hts,hxt⟩ := Finset.mem_filter.mp ht
    exact hx ((Finset.mem_powersetCard.mp hts).1 hxt)
  rw [hf]
  simp

/-- A next nest hits a prescribed finite forbidden set with probability <=|F|k/N. -/
theorem uniformNestChoice_hit_probability (s F : Finset α) {k : ℕ}
    (hk0 : 1≤k) (hk : k≤s.card) :
    (uniformNestChoice s k).real {t | ∃ x∈F, x∈t} ≤ (F.card:ℝ)*(k:ℝ)/s.card := by
  classical
  have := uniformNestChoice_probability s k hk
  have he : {t : Finset α | ∃ x∈F, x∈t} = ⋃ x : F, {t : Finset α | x.val∈t} := by
    classical
    ext t; simp
  rw [he]
  calc
    _ ≤ ∑ x : F, (uniformNestChoice s k).real {t : Finset α | x.val∈t} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _x : F, (k:ℝ)/s.card := by
      classical
      apply Finset.sum_le_sum
      intro x hx
      by_cases hxs : x.val∈s
      · exact le_of_eq (uniformNestChoice_mem_probability s hk0 hk hxs)
      · rw [uniformNestChoice_mem_probability_of_notMem s k hxs]
        positivity
    _ = _ := by simp; ring

/-- The source offspring size 2k^3 makes hitting any prescribed k old clusters
unlikely: the bound is derived from the actual uniform subset law. -/
theorem uniformNestChoice_hit_small_set (s F : Finset α) {k : ℕ}
    (hk0 : 1≤k) (hk : k≤s.card) (hlarge : 2*k^3≤s.card) (hF : F.card≤k) :
    (uniformNestChoice s k).real {t | ∃ x∈F, x∈t} ≤ 1/(2*(k:ℝ)) := by
  have hkr : (0:ℝ)<k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk0)
  have hNr : (0:ℝ)<s.card := by exact_mod_cast (lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hk0) hk)
  have hFR : (F.card:ℝ)≤k := by exact_mod_cast hF
  have hNR : 2*(k:ℝ)^3≤s.card := by exact_mod_cast hlarge
  calc
    _ ≤ (F.card:ℝ)*(k:ℝ)/s.card := uniformNestChoice_hit_probability s F hk0 hk
    _ ≤ (k:ℝ)^2/s.card := div_le_div_of_nonneg_right
      (by nlinarith) hNr.le
    _ ≤ _ := (div_le_div_iff₀ hNr (by positivity : 0<2*(k:ℝ))).2 (by nlinarith)

end NearCritical
