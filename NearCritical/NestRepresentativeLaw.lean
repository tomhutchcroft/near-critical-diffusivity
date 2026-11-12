module

public import NearCritical.NestRepresentative
public import NearCritical.NestUniformChoice
public import NearCritical.NestChainLaw

/-! Actual uniform transition rows from the computed first-good representative.
Source offspring/exploration identification remains explicit. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

variable {α : Type*} [Fintype α] [LinearOrder α]
  [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]

/-- Extend the successful selection rule to all states. The universe fallback
is only a totalization of invalid/dead rows, not a claimed surviving transition. -/
def representativeChoicePool (offspring : α → Finset α) (k : ℕ) (nest : Finset α) : Finset α :=
  if h : (goodNestRepresentatives nest offspring k).Nonempty then
    offspring (nestRepresentative nest offspring k h) else Finset.univ

omit [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)] in
lemma representativeChoicePool_of_good (offspring : α → Finset α) (k : ℕ) (nest : Finset α)
    (hg : (goodNestRepresentatives nest offspring k).Nonempty) :
    representativeChoicePool offspring k nest = offspring (nestRepresentative nest offspring k hg) := by
  simp [representativeChoicePool,hg]

omit [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)] in
lemma representativeChoicePool_card (offspring : α → Finset α) {k : ℕ}
    (hk : k≤Fintype.card α) (nest : Finset α) : k≤(representativeChoicePool offspring k nest).card := by
  by_cases hg : (goodNestRepresentatives nest offspring k).Nonempty
  · rw [representativeChoicePool_of_good offspring k nest hg]
    have hlarge := (nestRepresentative_spec nest offspring k hg).2.1
    by_cases hk0 : k=0
    · omega
    · have hsq : k≤k*k := by nlinarith
      have hcube : k*k≤k^3 := by nlinarith [Nat.mul_le_mul_left k hsq]
      omega
  · simpa [representativeChoicePool,hg] using hk

def representativeChoiceLaw (offspring : α → Finset α) (k : ℕ) (nest : Finset α) :
    Measure (Finset α) := uniformNestChoice (representativeChoicePool offspring k nest) k

lemma representativeChoiceLaw_probability (offspring : α → Finset α) {k : ℕ}
    (hk : k≤Fintype.card α) (nest : Finset α) : IsProbabilityMeasure (representativeChoiceLaw offspring k nest) :=
  uniformNestChoice_probability _ _ (representativeChoicePool_card offspring hk nest)

def representativeTransition (offspring : α → Finset α) (k : ℕ)
    (nest next : Finset α) : ℝ := (representativeChoiceLaw offspring k nest).real {next}

omit [MeasurableSingletonClass (Finset α)] in
lemma representativeTransition_nonneg (offspring : α → Finset α) (k : ℕ)
    (nest next : Finset α) : 0≤representativeTransition offspring k nest next := measureReal_nonneg

lemma representativeTransition_sum (offspring : α → Finset α) {k : ℕ}
    (hk : k≤Fintype.card α) (nest : Finset α) : ∑ next, representativeTransition offspring k nest next=1 := by
  have := representativeChoiceLaw_probability offspring hk nest
  simp [representativeTransition]

/-- Successful rows select only k-subsets of the COMPUTED representative's offspring. -/
theorem representativeChoiceLaw_good_admissible (offspring : α → Finset α)
    {k : ℕ} (hk : k≤Fintype.card α) (nest : Finset α)
    (hg : (goodNestRepresentatives nest offspring k).Nonempty) :
    representativeChoiceLaw offspring k nest
      {next | next⊆offspring (nestRepresentative nest offspring k hg) ∧ next.card=k}=1 := by
  have hcard := representativeChoicePool_card offspring hk nest
  rw [representativeChoicePool_of_good offspring k nest hg] at hcard
  unfold representativeChoiceLaw
  rw [representativeChoicePool_of_good offspring k nest hg]
  exact uniformNestChoice_admissible _ _ hcard

/-- The source total-offspring count supplies goodness; it is not an assumed
representative-selection conclusion. The resulting conditional choice is uniform. -/
theorem representativeChoiceLaw_from_total (offspring : α → Finset α) {k : ℕ}
    (hk0 : 0<k) (hk : k≤Fintype.card α) (nest : Finset α) (hsize : nest.card=k)
    (htotal : 2*k^4≤(nest.biUnion offspring).card) :
    ∃ hg : (goodNestRepresentatives nest offspring k).Nonempty,
      representativeChoiceLaw offspring k nest
        {next | next⊆offspring (nestRepresentative nest offspring k hg) ∧ next.card=k}=1 := by
  let hg := goodNestRepresentatives_nonempty nest offspring hk0 hsize htotal
  exact ⟨hg,representativeChoiceLaw_good_admissible offspring hk nest hg⟩

theorem representativeChoiceLaw_hit_small_set (offspring : α → Finset α)
    {k : ℕ} (hk0 : 1≤k) (hk : k≤Fintype.card α) (nest F : Finset α)
    (hg : (goodNestRepresentatives nest offspring k).Nonempty) (hF : F.card≤k) :
    (representativeChoiceLaw offspring k nest).real {next | ∃ x∈F, x∈next} ≤ 1/(2*(k:ℝ)) := by
  have hcard := representativeChoicePool_card offspring hk nest
  have hlarge := (nestRepresentative_spec nest offspring k hg).2.1
  rw [representativeChoicePool_of_good offspring k nest hg] at hcard
  unfold representativeChoiceLaw
  rw [representativeChoicePool_of_good offspring k nest hg]
  exact uniformNestChoice_hit_small_set _ F hk0 hcard hlarge hF

/-- A genuine finite-history PMF for the computed uniform next-nest choices.
No abstract nonnegative/row-sum premises remain in this instantiation. -/
def representativeTraceLaw (offspring : ℕ → Finset α → α → Finset α) (k N : ℕ)
    (hk : k≤Fintype.card α) (start : Finset α) : PMF (NestTrace (Finset α) N) :=
  nestTraceLaw (fun n nest next => representativeTransition (offspring n nest) k nest next) N
    (fun n _hn nest next => representativeTransition_nonneg (offspring n nest) k nest next)
    (fun n _hn nest => representativeTransition_sum (offspring n nest) hk nest) start

lemma representativeTraceLaw_apply (offspring : ℕ → Finset α → α → Finset α) (k N : ℕ)
    (hk : k≤Fintype.card α) (start : Finset α) (trace : NestTrace (Finset α) N) :
    representativeTraceLaw offspring k N hk start trace =
      ENNReal.ofReal (nestTraceMass (fun n nest next => representativeTransition (offspring n nest) k nest next) N start trace) := rfl

end NearCritical
