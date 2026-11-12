module
public import NearCritical.Section9PivotOpening
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual covariance of target successes sharing fresh physical bonds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private def physicalOpeningEvent {d : ℕ} (H : Finset (Bond d)) : Set (Configuration d) :=
  {ζ | ∃ b ∈ H, ζ b = true}

private theorem physicalOpeningEvent_measurable {d : ℕ} (H : Finset (Bond d)) :
    MeasurableSet (physicalOpeningEvent H) := by
  have he : physicalOpeningEvent H = ⋃ b : H, {ζ : Configuration d | ζ b.val = true} := by
    ext ζ
    constructor
    · rintro ⟨b,hb,hζ⟩
      exact Set.mem_iUnion.mpr ⟨⟨b,hb⟩,hζ⟩
    · intro hζ
      obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hζ
      exact ⟨b.val,b.property,hb⟩
  rw [he]
  exact MeasurableSet.iUnion fun b =>
    (measurableSet_singleton true).preimage (measurable_pi_apply b.val)

/-- Distinct target success indicators need not be independent. Their actual
covariance is controlled by the physical coordinates they share. -/
theorem section9_physical_opening_covariance_le {d : ℕ} (q : unitInterval)
    (H K : Finset (Bond d)) :
    (percolation d q).real
        ({ζ | ∃ b ∈ H, ζ b = true} ∩ {ζ | ∃ b ∈ K, ζ b = true}) -
      (percolation d q).real {ζ | ∃ b ∈ H, ζ b = true} *
        (percolation d q).real {ζ | ∃ b ∈ K, ζ b = true} ≤
      (q : ℝ)*((H ∩ K).card : ℝ) := by
  let μ := percolation d q
  let a : ℝ := 1-(q : ℝ)
  let E := fun S : Finset (Bond d) => physicalOpeningEvent S
  have hprob (S : Finset (Bond d)) : μ.real (E S) = 1-a^S.card :=
    section9_physical_bonds_open_probability q S
  have heUnion : E H ∪ E K = E (H ∪ K) := by
    ext ζ
    constructor
    · rintro (⟨b,hb,hζ⟩ | ⟨b,hb,hζ⟩)
      · exact ⟨b,Finset.mem_union_left K hb,hζ⟩
      · exact ⟨b,Finset.mem_union_right H hb,hζ⟩
    · rintro ⟨b,hb,hζ⟩
      rcases Finset.mem_union.mp hb with hb | hb
      · exact Or.inl ⟨b,hb,hζ⟩
      · exact Or.inr ⟨b,hb,hζ⟩
  have hsum := measureReal_union_add_inter (μ := μ) (s := E H) (t := E K)
    (physicalOpeningEvent_measurable K)
  rw [heUnion,hprob (H ∪ K),hprob H,hprob K] at hsum
  have hpow : a^H.card*a^K.card = a^(H ∪ K).card*a^(H ∩ K).card := by
    rw [← pow_add,← Finset.card_union_add_card_inter H K,pow_add]
  have hcov : μ.real (E H ∩ E K)-μ.real (E H)*μ.real (E K) =
      a^(H ∪ K).card*(1-a^(H ∩ K).card) := by
    rw [hprob H,hprob K]
    nlinarith only [hsum,hpow]
  have ha0 : 0 ≤ a := sub_nonneg.mpr q.property.2
  have ha1 : a ≤ 1 := by dsimp only [a]; linarith [q.property.1]
  have hnon : 0 ≤ 1-a^(H ∩ K).card := by
    rw [← hprob (H ∩ K)]
    exact measureReal_nonneg
  have hsingle (b : Bond d) : μ.real {ζ | ζ b = true} = (q : ℝ) := by
    simpa using section9_physical_bonds_open_probability q ({b} : Finset (Bond d))
  have hbound (S : Finset (Bond d)) : μ.real (E S) ≤ (q : ℝ)*(S.card : ℝ) := by
    have he : E S = ⋃ b ∈ S, {ζ : Configuration d | ζ b = true} := by
      ext ζ
      simp [E,physicalOpeningEvent]
    rw [he]
    calc
      _ ≤ ∑ b ∈ S, μ.real {ζ | ζ b = true} := measureReal_biUnion_finset_le S _
      _ = _ := by simp only [hsingle,Finset.sum_const,nsmul_eq_mul]; ring
  change μ.real (E H ∩ E K)-μ.real (E H)*μ.real (E K) ≤ _
  rw [hcov]
  calc
    _ ≤ 1-a^(H ∩ K).card := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ ha0 ha1) hnon
    _ = μ.real (E (H ∩ K)) := (hprob (H ∩ K)).symm
    _ ≤ _ := hbound (H ∩ K)

end NearCritical
