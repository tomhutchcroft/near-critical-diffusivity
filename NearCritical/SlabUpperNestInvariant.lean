module

public import NearCritical.ExplorationDomination

/-! Nest semantics (input (iii) of prop.slab.upper) reduced to ONE-STEP local
statements, by an invariant along the adaptive exploration.

Fix the block sample `x`. Let `Good v` be any per-site property (e.g. "the k-nest
chosen in cube `v` is joined, in the slab `p`-configuration, to the root nest").
If the root move's success gives `Good o`, and every successful tube move from
an explored site to a new site `z` gives `Good z` whenever all explored sites are
`Good`, then every explored site of the full run is `Good`; in particular a
nonzero payoff yields a `Good` target site. The source's "each added k-nest is
connected to a single cluster of the k-nest from which it was added" is exactly
the one-step `hedge` premise. -/

@[expose] public section
noncomputable section

namespace NearCritical

open scoped ENNReal Classical

section
variable {Vx Ed : Type*} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
variable (ends : Ed → Vx × Vx) (o : Vx)

theorem exploreRun_good {Ω : Vx ⊕ Ed → Type*} [∀ i, MeasurableSpace (Ω i)]
    (succ : ExploreState Vx Ed → (∀ i, Ω i) → Bool) (x : ∀ i, Ω i) (Good : Vx → Prop)
    (hroot : ∀ σ, ExploreInv ends o σ → exploreMove ends o σ = some .root →
      succ σ x = true → Good o)
    (hedge : ∀ σ e z, ExploreInv ends o σ → (∀ v ∈ σ.A, Good v) →
      exploreMove ends o σ = some (.edge e z) → succ σ x = true → Good z) :
    ∀ n σ, ExploreInv ends o σ → (∀ v ∈ σ.A, Good v) →
      ∀ v ∈ (adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ n σ x).A, Good v := by
  intro n
  induction n with
  | zero =>
    intro σ _ hG
    simpa using hG
  | succ n ih =>
    intro σ hσ hG
    cases hq : exploreQuery ends o σ with
    | none =>
      rw [adaptiveRun_succ_of_none hq]
      exact hG
    | some i =>
      rw [adaptiveRun_succ_of_some hq]
      refine ih _ (exploreInv_next ends o hσ hq _) ?_
      cases hm : exploreMove ends o σ with
      | none => simp [exploreQuery, hm] at hq
      | some m =>
        cases m with
        | root =>
          cases hb : succ σ x
          · intro v hv
            simp [exploreNext, hm] at hv
            exact hG v hv
          · intro v hv
            simp [exploreNext, hm] at hv
            rcases hv with rfl | hv
            · exact hroot σ hσ hm hb
            · exact hG v hv
        | site z =>
          cases hb : succ σ x <;>
            (intro v hv; simp [exploreNext, hm] at hv; exact hG v hv)
        | edge e z =>
          cases hb : succ σ x
          · intro v hv
            simp [exploreNext, hm] at hv
            exact hG v hv
          · intro v hv
            simp [exploreNext, hm] at hv
            rcases hv with rfl | hv
            · exact hedge σ e _ hσ hG hm hb
            · exact hG v hv

/-- Nonzero payoff of the full run from the empty state yields a `Good` target. -/
theorem explorePayoff_ne_zero_good {Ω : Vx ⊕ Ed → Type*} [∀ i, MeasurableSpace (Ω i)] (D : Finset Vx)
    (succ : ExploreState Vx Ed → (∀ i, Ω i) → Bool) (x : ∀ i, Ω i) (Good : Vx → Prop)
    (hroot : ∀ σ, ExploreInv ends o σ → exploreMove ends o σ = some .root →
      succ σ x = true → Good o)
    (hedge : ∀ σ e z, ExploreInv ends o σ → (∀ v ∈ σ.A, Good v) →
      exploreMove ends o σ = some (.edge e z) → succ σ x = true → Good z)
    (h : explorePayoff D (adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ
      (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ x) ≠ 0) :
    ∃ v ∈ D, Good v := by
  have hinv : ExploreInv ends o (⟨∅, ∅, ∅, ∅, ∅⟩ : ExploreState Vx Ed) :=
    ⟨by simp, by simp, by simp, fun _ ↦ rfl, fun h ↦ absurd rfl h⟩
  have hall := exploreRun_good ends o succ x Good hroot hedge (Fintype.card (Vx ⊕ Ed))
    ⟨∅, ∅, ∅, ∅, ∅⟩ hinv (by simp)
  unfold explorePayoff at h
  split_ifs at h with hne
  · obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_inter] at hv
    exact ⟨v, hv.2, hall v hv.1⟩
  · exact absurd rfl h

end

end NearCritical
