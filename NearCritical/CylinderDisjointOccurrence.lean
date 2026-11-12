module

public import NearCritical.DisjointOccurrence
public import Mathlib.Data.Finset.Pi

/-! Finite-edge and full-configuration disjoint occurrence agree for cylinder
events. This connects finite network certificates to the source's events on
all lattice bonds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set

/-- Extend a local assignment while preserving an arbitrary background outside s. -/
def extendConfiguration {E : Type*} (s : Finset E) (ω : E → Bool) (η : (e : s) → Bool) : E → Bool := by
  classical
  exact fun e ↦ if h : e ∈ s then η ⟨e, h⟩ else ω e

lemma restrict_extendConfiguration {E : Type*} (s : Finset E) (ω : E → Bool) (η : (e : s) → Bool) :
    s.restrict (extendConfiguration s ω η) = η := by
  classical
  ext e
  simp [extendConfiguration, e.property]

/-- Cylinder events have the same disjoint occurrence whether interpreted on
their finite coordinates or on the full configuration space. -/
theorem disjointOccurrence_restrict_iff {E : Type*} (s : Finset E)
    (A B : Set ((e : s) → Bool)) (ω : E → Bool) :
    DisjointOccurrence A B (s.restrict ω) ↔
      DisjointOccurrence ((s.restrict) ⁻¹' A) ((s.restrict) ⁻¹' B) ω := by
  classical
  constructor
  · rintro ⟨F, H, hFinF, hFinH, hdis, hF, hH⟩
    refine ⟨Subtype.val '' F, Subtype.val '' H, hFinF.image _, hFinH.image _, ?_, ?_, ?_⟩
    · apply Set.disjoint_left.mpr
      rintro e ⟨f, hf, rfl⟩ ⟨h, hh, heq⟩
      have heq' : h = f := Subtype.ext heq
      subst h
      exact Set.disjoint_left.mp hdis hf hh
    · intro θ hθ
      exact hF (s.restrict θ) (fun e he ↦ hθ e.val ⟨e, he, rfl⟩)
    · intro θ hθ
      exact hH (s.restrict θ) (fun e he ↦ hθ e.val ⟨e, he, rfl⟩)
  · rintro ⟨F, H, _, _, hdis, hF, hH⟩
    let f : Set s := {e | e.val ∈ F}
    let h : Set s := {e | e.val ∈ H}
    refine ⟨f, h, Set.toFinite _, Set.toFinite _, ?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr (fun e hf hh ↦ Set.disjoint_left.mp hdis hf hh)
    · intro θ hθ
      have hagree : ∀ e ∈ F, extendConfiguration s ω θ e = ω e := by
        intro e he
        by_cases hs : e ∈ s
        · simp only [extendConfiguration, dite_eq_left hs]
          exact hθ ⟨e, hs⟩ he
        · simp [extendConfiguration, hs]
      have hevent := hF (extendConfiguration s ω θ) hagree
      change s.restrict (extendConfiguration s ω θ) ∈ A at hevent
      rw [restrict_extendConfiguration] at hevent
      exact hevent
    · intro θ hθ
      have hagree : ∀ e ∈ H, extendConfiguration s ω θ e = ω e := by
        intro e he
        by_cases hs : e ∈ s
        · simp only [extendConfiguration, dite_eq_left hs]
          exact hθ ⟨e, hs⟩ he
        · simp [extendConfiguration, hs]
      have hevent := hH (extendConfiguration s ω θ) hagree
      change s.restrict (extendConfiguration s ω θ) ∈ B at hevent
      rw [restrict_extendConfiguration] at hevent
      exact hevent

end NearCritical
