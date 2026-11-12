module

public import NearCritical.ExplorationDomination

/-! Exploration domination with an AUXILIARY MEMORY.

`exploration_dominates_mixed` lets the per-step success rule depend on the
exploration state `ExploreState` only. A state-dependent rule (source 6096-6099:
the current `k`-nest is determined by the history) needs more: the rule must
know, for instance, the ORDER in which slots were revealed and their outcomes.

`exploration_dominates_mixed_aux` runs the same exploration on the enriched
state `ExploreState × H`, where the memory `h : H` is updated by a deterministic
function of the state and the outcome bit only (never of the sample). The
success rule may depend on `(σ, h)`. Locality, measurability and the per-step
bound `κ{true} <= ν_i{succ}` are required only at states satisfying
`ExploreInv` and an extra invariant `I` of the enriched state that holds
initially and is preserved by every step. The conclusion is the same domination
of the mixed site-bond value.

Since neither the memory update nor `I` reads the sample, the per-step bound is
a bound for a state fixed before the fresh block is read.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Function
open scoped ENNReal Classical

section
variable {Vx Ed : Type*} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
variable (ends : Ed → Vx × Vx) (o : Vx) (D : Finset Vx)

theorem exploration_dominates_mixed_aux {H : Type*}
    {Ω : Vx ⊕ Ed → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)] [∀ i, Nonempty (Ω i)]
    (κ : Measure Bool) [IsProbabilityMeasure κ]
    (nextH : ExploreState Vx Ed → H → Bool → H) (h0 : H)
    (I : ExploreState Vx Ed × H → Prop) (hI0 : I (⟨∅, ∅, ∅, ∅, ∅⟩, h0))
    (hI : ∀ σ h i b, ExploreInv ends o σ → I (σ, h) → exploreQuery ends o σ = some i →
      I (exploreNext ends o σ b, nextH σ h b))
    (succ : ExploreState Vx Ed × H → (∀ i, Ω i) → Bool)
    (hlocal : ∀ σ h i (x x' : ∀ j, Ω j), ExploreInv ends o σ → I (σ, h) →
      exploreQuery ends o σ = some i →
      (∀ j ∈ insert i (exploreRevealed σ), x j = x' j) → succ (σ, h) x = succ (σ, h) x')
    (hmeas : ∀ s, Measurable (succ s))
    (hprob : ∀ σ h i (x : ∀ j, Ω j), ExploreInv ends o σ → I (σ, h) →
      exploreQuery ends o σ = some i →
      κ {true} ≤ ν i {y | succ (σ, h) (update x i y) = true}) :
    mixedValue ends o D κ ⟨∅, ∅, ∅, ∅, ∅⟩ ≤
      ∫⁻ x, explorePayoff D (adaptiveRun (fun s : ExploreState Vx Ed × H => exploreQuery ends o s.1)
        (fun s b => (exploreNext ends o s.1 b, nextH s.1 s.2 b)) succ
        (Fintype.card (Vx ⊕ Ed)) (⟨∅, ∅, ∅, ∅, ∅⟩, h0) x).1 ∂Measure.pi ν := by
  refine adaptive_domination ν (fun s : ExploreState Vx Ed × H => exploreRevealed s.1)
    (fun s => exploreQuery ends o s.1)
    (fun s b => (exploreNext ends o s.1 b, nextH s.1 s.2 b)) succ
    (fun s => ExploreInv ends o s.1 ∧ I s) (fun s => mixedValue ends o D κ s.1)
    (fun s => explorePayoff D s.1) (q := κ {true}) prob_le_one
    (fun s i _ h ↦ exploreQuery_notMem ends o h)
    (fun s i b _ h ↦ exploreRevealed_next ends o h b)
    (fun s i b hs h ↦ ⟨exploreInv_next ends o hs.1 h b, hI s.1 s.2 i b hs.1 hs.2 h⟩)
    (fun s i x x' hs h hx ↦ hlocal s.1 s.2 i x x' hs.1 hs.2 h hx)
    hmeas
    (fun s i x hs h ↦ hprob s.1 s.2 i x hs.1 hs.2 h) ?_ ?_
    (fun s hs h ↦ mixedValue_le_payoff ends o D κ hs.1 h)
    (⟨∅, ∅, ∅, ∅, ∅⟩, h0) ?_ (by ext x; cases x <;> simp [exploreRevealed])
  · intro s i _ h
    obtain ⟨m, hm, rfl⟩ := exploreQuery_eq_some ends o h
    exact pi_bool_step κ (ExploreMove.slot o m)
      (fun β hβ ↦ mixedEvent_step ends o D hm true β hβ)
      (fun β hβ ↦ mixedEvent_step ends o D hm false β hβ)
  · intro s i _ h
    obtain ⟨m, hm, -⟩ := exploreQuery_eq_some ends o h
    exact measure_mono (mixedEvent_next_mono ends o D hm)
  · exact ⟨⟨by simp, by simp, by simp, fun _ ↦ rfl, fun h ↦ absurd rfl h⟩, hI0⟩

end

end NearCritical
