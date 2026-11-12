module

public import NearCritical.ExternalFiniteEventEntropy

/-! Remove event-probability endpoint guards for positive finite transcript laws.
 No actual half-space parameter-window claim. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open OAI.CriticalPercolation
open scoped Classical BigOperators

/-- A nonempty proper event has interior mass under a positive normalized law. -/
theorem finiteEventMass_interior {X : Type*} [Fintype X]
    (P : X → ℝ) (hP : ∀ x, 0 < P x) (hP1 : ∑ x, P x = 1)
    (A : Set X) (hA : A.Nonempty) (hAc : A ≠ Set.univ) :
    finiteEventMass P A ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem A).mp hAc
  have hnonneg (z : X) : 0 ≤ if z ∈ A then P z else 0 := by
    split_ifs
    · exact (hP z).le
    · exact le_rfl
  have hle (z : X) : (if z ∈ A then P z else 0) ≤ P z := by
    by_cases hz : z ∈ A
    · simp [hz]
    · simpa [hz] using (hP z).le
  constructor
  · apply Finset.sum_pos' (fun z _ => hnonneg z)
    exact ⟨x, Finset.mem_univ _, by simpa [hx] using hP x⟩
  · have hlt := Finset.sum_lt_sum (s := Finset.univ) (fun z _ => hle z)
      ⟨y, Finset.mem_univ _, by simpa [hy] using hP y⟩
    simpa only [finiteEventMass, hP1] using hlt

/-- Refined finite event comparison for positive normalized masses, including
empty/full events; no interior-event-probability hypothesis remains. -/
theorem positive_finite_event_difference {X : Type*} [Fintype X]
    (P R : X → ℝ) (hP : ∀ x, 0 < P x) (hR : ∀ x, 0 < R x)
    (hP1 : ∑ x, P x = 1) (hR1 : ∑ x, R x = 1)
    (A : Set X) {K : ℝ} (hK : 0 ≤ K)
    (hbudget : FiniteEntropy.divergence P R ≤ K) :
    |finiteEventMass P A - finiteEventMass R A| ≤
      3 * Real.sqrt (max (finiteEventMass P A) (finiteEventMass R A) * K) := by
  by_cases hempty : A = ∅
  · simp [finiteEventMass, hempty]
  by_cases hfull : A = Set.univ
  · have hnonneg : (0 : ℝ) ≤ 3 * Real.sqrt K :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    simpa [finiteEventMass, hfull, hP1, hR1] using hnonneg
  have hA : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  have ha := finiteEventMass_interior P hP hP1 A hA hfull
  have hb := finiteEventMass_interior R hR hR1 A hA hfull
  apply binary_entropy_refined_difference ⟨ha.1.le, ha.2.le⟩ hb hK
  exact (finite_event_klBerReal_le P R (fun x => (hP x).le) (fun x => (hR x).le)
    hP1 hR1 (fun x _ => hR x) A).trans hbudget

/-- Any finite transcript event satisfies the refined comparison under a
finite reference entropy budget. Interior INPUT parameters ensure all leaves
have positive mass; no restriction is imposed on the event itself. -/
theorem queryTree_refined_event_difference {E : Type*} (t : QueryTree E)
    {q p K : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (A : Set t.Leaf) (hK : 0 ≤ K)
    (hbudget : FiniteEntropy.divergence (t.reference q) (t.reference p) ≤ K) :
    |finiteEventMass (t.reference q) A - finiteEventMass (t.reference p) A| ≤
      3 * Real.sqrt (max (finiteEventMass (t.reference q) A)
        (finiteEventMass (t.reference p) A) * K) :=
  positive_finite_event_difference (t.reference q) (t.reference p)
    (QueryTree.reference_pos hq t) (QueryTree.reference_pos hp t)
    (QueryTree.reference_sum q t) (QueryTree.reference_sum p t) A hK hbudget

end NearCritical.External
