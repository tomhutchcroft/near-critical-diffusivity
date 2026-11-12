module

public import NearCritical.Section10PhaseLength

/-! Phase assignment along a finite joint history. A cleaning step ends a
previous phase, and can itself start a phase if its next nests entangle. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Start index of the phase containing the given step, if there is one.
Step zero is the initial pair of draws. Cleaning resets the previous phase
before testing whether the current step starts a new one. -/
def phaseOrigin (entangled clean : ℕ → Prop) : ℕ → Option ℕ
  | 0 => if entangled 0 then some 0 else none
  | u + 1 => if clean (u+1) then
      if entangled (u+1) then some (u+1) else none
    else (phaseOrigin entangled clean u).orElse (fun _ =>
      if entangled (u+1) then some (u+1) else none)

theorem phaseOrigin_exists_of_entangled (entangled clean : ℕ → Prop) {u : ℕ}
    (hu : entangled u) :
    ∃ v, phaseOrigin entangled clean u = some v := by
  cases u with
  | zero => exact ⟨0, by simp [phaseOrigin, hu]⟩
  | succ u =>
    by_cases hc : clean (u+1)
    · exact ⟨u+1, by simp [phaseOrigin, hc, hu]⟩
    · cases h : phaseOrigin entangled clean u with
      | none => exact ⟨u+1, by simp [phaseOrigin, hc, hu, h, Option.orElse]⟩
      | some v => exact ⟨v, by simp [phaseOrigin, hc, h, Option.orElse]⟩

/-- A phase origin is an entangled step and the intervening steps have not
cleaned. The origin itself is assigned to the same phase. -/
theorem phaseOrigin_spec (entangled clean : ℕ → Prop) {u v : ℕ}
    (h : phaseOrigin entangled clean u = some v) :
    entangled v ∧ v ≤ u ∧ phaseOrigin entangled clean v = some v ∧
      ∀ w, v < w → w ≤ u → ¬ clean w := by
  induction u generalizing v with
  | zero =>
    by_cases he : entangled 0
    · have hv : v = 0 := by simpa [phaseOrigin, he, eq_comm] using h
      subst v
      exact ⟨he, le_rfl, h, fun w hw hw' => (by omega : False).elim⟩
    · simp [phaseOrigin, he] at h
  | succ u ih =>
    have atCurrent (hv : v = u+1) (he : entangled (u+1)) :
        entangled v ∧ v ≤ u+1 ∧ phaseOrigin entangled clean v = some v ∧
          ∀ w, v < w → w ≤ u+1 → ¬ clean w := by
      subst v
      exact ⟨he, le_rfl, h, fun w hw hw' => (by omega : False).elim⟩
    by_cases hc : clean (u+1)
    · by_cases he : entangled (u+1)
      · exact atCurrent (by simpa [phaseOrigin, hc, he, eq_comm] using h) he
      · simp [phaseOrigin, hc, he] at h
    · cases hp : phaseOrigin entangled clean u with
      | none =>
        by_cases he : entangled (u+1)
        · exact atCurrent (by simpa [phaseOrigin, hc, hp, he, Option.orElse, eq_comm] using h) he
        · simp [phaseOrigin, hc, hp, he, Option.orElse] at h
      | some a =>
        have hav : a = v := by simpa [phaseOrigin, hc, hp, Option.orElse] using h
        subst a
        obtain ⟨he, hv, ho, hclean⟩ := ih hp
        refine ⟨he, hv.trans (Nat.le_succ _), ho, ?_⟩
        intro w hw hw'
        by_cases hwu : w ≤ u
        · exact hclean w hw hwu
        · have : w = u+1 := by omega
          simpa only [this] using hc

/-- If an old phase is still active after a step, the step is noncleaning
and the phase was active immediately before it. -/
theorem phaseOrigin_prev_of_lt (entangled clean : ℕ → Prop) {u v : ℕ}
    (hv : v < u+1) (h : phaseOrigin entangled clean (u+1) = some v) :
    phaseOrigin entangled clean u = some v ∧ ¬ clean (u+1) := by
  have hc := (phaseOrigin_spec entangled clean h).2.2.2 _ hv le_rfl
  cases hp : phaseOrigin entangled clean u with
  | none =>
    by_cases he : entangled (u+1)
    · have : u+1 = v := by simpa [phaseOrigin, hc, hp, he, Option.orElse] using h
      omega
    · simp [phaseOrigin, hc, hp, he, Option.orElse] at h
  | some a =>
    have hav : a = v := by simpa [phaseOrigin, hc, hp, Option.orElse] using h
    exact ⟨congrArg some hav, hc⟩

/-- An interior step starts a phase exactly when it is entangled and it
either cleans or has no phase to inherit. -/
theorem phaseOrigin_start_iff (entangled clean : ℕ → Prop) (u : ℕ) :
    phaseOrigin entangled clean (u+1) = some (u+1) ↔
      entangled (u+1) ∧ (clean (u+1) ∨ phaseOrigin entangled clean u = none) := by
  by_cases hc : clean (u+1)
  · simp [phaseOrigin, hc]
  · cases hp : phaseOrigin entangled clean u with
    | none => simp [phaseOrigin, hc, hp, Option.orElse]
    | some a =>
      have ha := (phaseOrigin_spec entangled clean hp).2.1
      have hne : a ≠ u+1 := by omega
      simp [phaseOrigin, hc, hp, Option.orElse, hne]

/-- Charge each entangled step to its phase origin. Counting all members
of each phase bounds the number of entangled steps in the history. -/
theorem entangled_steps_card_le_phase_members (entangled clean : ℕ → Prop)
    (m : ℕ) (S : Finset ℕ) (hS : ∀ u < m, entangled u → u ∈ S) :
    ((Finset.range m).filter entangled).card ≤
      ∑ v ∈ S, ((Finset.range m).filter (fun u => phaseOrigin entangled clean u = some v)).card := by
  have hsub : (Finset.range m).filter entangled ⊆
      S.biUnion (fun v => (Finset.range m).filter (fun u => phaseOrigin entangled clean u = some v)) := by
    intro u hu
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hu
    obtain ⟨v, hv⟩ := phaseOrigin_exists_of_entangled entangled clean he
    obtain ⟨hev, hle, _, _⟩ := phaseOrigin_spec entangled clean hv
    exact Finset.mem_biUnion.mpr ⟨v, hS v (hle.trans_lt (Finset.mem_range.mp hm)) hev,
      Finset.mem_filter.mpr ⟨hm, hv⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

end NearCritical.Section10
