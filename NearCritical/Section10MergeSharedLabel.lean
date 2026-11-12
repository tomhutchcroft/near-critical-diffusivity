module

public import NearCritical.Section10MergeSchedule
public import NearCritical.Section10MergedTrace

/-! Identify the physical label at a shared step after an arbitrary prefix
of the joint route schedule. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

private theorem shared_label_after_cons {E : Type*} (lab lab' : ℕ → E)
    (t t' : ℕ) (a : PairMove) (s : List PairMove)
    (ha : a = .both → lab t = lab' t')
    (hs : ∀ p r, s = p ++ .both :: r →
      lab (a.nextLeft t + leftCount p) = lab' (a.nextRight t' + rightCount p))
    (p r : List PairMove) (h : a :: s = p ++ .both :: r) :
    lab (t + leftCount p) = lab' (t' + rightCount p) := by
  cases p with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    simpa only [leftCount, rightCount, Nat.add_zero] using ha h.1
  | cons b p =>
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hab,htail⟩ := h
    subst b
    have he := hs p r htail
    cases a <;> simpa only [leftCount, rightCount, PairMove.nextLeft, PairMove.nextRight,
      Nat.add_assoc, Nat.add_comm 1] using he

/-- At a shared position the two local clocks point to the same label. -/
theorem mergeSched_shared_label {E : Type*} (rank : E → ℕ) (lab lab' : ℕ → E)
    (m m' t t' : ℕ) (p r : List PairMove)
    (h : mergeSched rank lab lab' m m' t t' = p ++ .both :: r) :
    lab (t + leftCount p) = lab' (t' + rightCount p) := by
  suffices haux : ∀ n m m' t t', m + m' ≤ n → ∀ p r,
      mergeSched rank lab lab' m m' t t' = p ++ .both :: r →
      lab (t + leftCount p) = lab' (t' + rightCount p) by
    exact haux (m+m') m m' t t' le_rfl p r h
  intro n
  induction n with
  | zero =>
    intro m m' t t' hsize p r h
    obtain ⟨rfl,rfl⟩ : m = 0 ∧ m' = 0 := by omega
    rw [mergeSched] at h
    cases p <;> simp at h
  | succ n ih =>
    intro m m' t t' hsize p r h
    rcases m with _ | m <;> rcases m' with _ | m'
    · rw [mergeSched] at h
      cases p <;> simp at h
    · rw [mergeSched] at h
      exact shared_label_after_cons lab lab' t t' .right _ (by simp)
        (ih 0 m' t (t'+1) (by omega)) p r h
    · rw [mergeSched] at h
      exact shared_label_after_cons lab lab' t t' .left _ (by simp)
        (ih m 0 (t+1) t' (by omega)) p r h
    · rw [mergeSched] at h
      split_ifs at h with hsame hrank
      · exact shared_label_after_cons lab lab' t t' .both _ (fun _ => hsame)
          (ih m m' (t+1) (t'+1) (by omega)) p r h
      · exact shared_label_after_cons lab lab' t t' .left _ (by simp)
          (ih m (m'+1) (t+1) t' (by omega)) p r h
      · exact shared_label_after_cons lab lab' t t' .right _ (by simp)
          (ih (m+1) m' t (t'+1) (by omega)) p r h

end NearCritical.Section10
