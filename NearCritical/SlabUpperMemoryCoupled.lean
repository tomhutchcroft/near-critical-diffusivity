module

public import NearCritical.SlabUpperCoupled
public import NearCritical.ExplorationDominationAux

/-! Far-reach lower bound from a coupled exploration WITH MEMORY.

`reachFar_ge_of_memory_exploration` is the analogue of
`CoupledRenormalizedExploration.reachFar_ge` for a success rule on the enriched
state `ExploreState × H` (`ExplorationDominationAux`): if the block sample `Φ`
has product law, the rule is local, measurable and succeeds with probability at
least `κ{true}` at every state satisfying `ExploreInv` and a preserved
invariant `I`, and a nonzero payoff of the run forces the far-reach event, then
`θ <= P_p[reach far]` whenever `θ` is at most the mixed site-bond value.

Its conclusion is exactly the hypothesis `hreach` of
`slab_upper_inverse_square_of_reachFar`.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Function
open scoped ENNReal Classical

theorem reachFar_ge_of_memory_exploration {d : ℕ} {p : unitInterval}
    {S : Set (Vertex d)} {F : Finset (Vertex d)} {N : ℕ} {θ : ℝ≥0∞}
    {Vx Ed : Type} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
    (ends : Ed → Vx × Vx) (root : Vx) (target : Finset Vx)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (P : Measure Ω₀) [IsProbabilityMeasure P]
    (cfg : Ω₀ → Configuration d) (measurable_cfg : Measurable cfg)
    (map_cfg : Measure.map cfg P = percolation d p)
    {Ω : Vx ⊕ Ed → Type} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)] [∀ i, Nonempty (Ω i)]
    (κ : Measure Bool) [IsProbabilityMeasure κ]
    (Φ : Ω₀ → ∀ i, Ω i) (measurable_Φ : Measurable Φ)
    (map_Φ : Measure.map Φ P = Measure.pi ν)
    {H : Type} (nextH : ExploreState Vx Ed → H → Bool → H) (h0 : H)
    (I : ExploreState Vx Ed × H → Prop) (hI0 : I (⟨∅, ∅, ∅, ∅, ∅⟩, h0))
    (hI : ∀ σ h i b, ExploreInv ends root σ → I (σ, h) → exploreQuery ends root σ = some i →
      I (exploreNext ends root σ b, nextH σ h b))
    (succ : ExploreState Vx Ed × H → (∀ i, Ω i) → Bool)
    (hlocal : ∀ σ h i (x x' : ∀ j, Ω j), ExploreInv ends root σ → I (σ, h) →
      exploreQuery ends root σ = some i →
      (∀ j ∈ insert i (exploreRevealed σ), x j = x' j) → succ (σ, h) x = succ (σ, h) x')
    (hmeas : ∀ s, Measurable (succ s))
    (hprob : ∀ σ h i (x : ∀ j, Ω j), ExploreInv ends root σ → I (σ, h) →
      exploreQuery ends root σ = some i →
      κ {true} ≤ ν i {y | succ (σ, h) (update x i y) = true})
    (good : ∀ ω₀, explorePayoff target
      (adaptiveRun (fun s : ExploreState Vx Ed × H => exploreQuery ends root s.1)
        (fun s b => (exploreNext ends root s.1 b, nextH s.1 s.2 b)) succ
        (Fintype.card (Vx ⊕ Ed)) (⟨∅, ∅, ∅, ∅, ∅⟩, h0) (Φ ω₀)).1 ≠ 0 →
      cfg ω₀ ∈ restrictedReachFarEvent S F N)
    (mixed_ge : θ ≤ mixedValue ends root target κ ⟨∅, ∅, ∅, ∅, ∅⟩) :
    θ ≤ percolation d p (restrictedReachFarEvent S F N) := by
  have hf := measurable_payoff_adaptiveRun
    (fun s : ExploreState Vx Ed × H => exploreQuery ends root s.1)
    (fun s b => (exploreNext ends root s.1 b, nextH s.1 s.2 b)) succ
    (fun s => explorePayoff target s.1) hmeas
    (Fintype.card (Vx ⊕ Ed)) (⟨∅, ∅, ∅, ∅, ∅⟩, h0)
  have hR := measurableSet_restrictedReachFarEvent S F N
  refine mixed_ge.trans ?_
  calc mixedValue ends root target κ ⟨∅, ∅, ∅, ∅, ∅⟩
      ≤ ∫⁻ x, explorePayoff target
          (adaptiveRun (fun s : ExploreState Vx Ed × H => exploreQuery ends root s.1)
            (fun s b => (exploreNext ends root s.1 b, nextH s.1 s.2 b)) succ
            (Fintype.card (Vx ⊕ Ed)) (⟨∅, ∅, ∅, ∅, ∅⟩, h0) x).1 ∂Measure.pi ν :=
        exploration_dominates_mixed_aux ends root target ν κ nextH h0 I hI0 hI succ hlocal
          hmeas hprob
    _ = ∫⁻ ω₀, explorePayoff target
          (adaptiveRun (fun s : ExploreState Vx Ed × H => exploreQuery ends root s.1)
            (fun s b => (exploreNext ends root s.1 b, nextH s.1 s.2 b)) succ
            (Fintype.card (Vx ⊕ Ed)) (⟨∅, ∅, ∅, ∅, ∅⟩, h0) (Φ ω₀)).1 ∂P := by
        rw [← map_Φ, lintegral_map hf measurable_Φ]
    _ ≤ ∫⁻ ω₀, (restrictedReachFarEvent S F N).indicator 1 (cfg ω₀) ∂P := by
        refine lintegral_mono fun ω₀ ↦ ?_
        try dsimp only
        by_cases hz : explorePayoff target
            (adaptiveRun (fun s : ExploreState Vx Ed × H => exploreQuery ends root s.1)
              (fun s b => (exploreNext ends root s.1 b, nextH s.1 s.2 b)) succ
              (Fintype.card (Vx ⊕ Ed)) (⟨∅, ∅, ∅, ∅, ∅⟩, h0) (Φ ω₀)).1 = 0
        · rw [hz]
          exact zero_le
        · rw [Set.indicator_of_mem (good ω₀ hz), Pi.one_apply]
          unfold explorePayoff
          split_ifs <;> simp
    _ = ∫⁻ ω, (restrictedReachFarEvent S F N).indicator 1 ω ∂percolation d p := by
        rw [← map_cfg, lintegral_map (measurable_one.indicator hR) measurable_cfg]
    _ = _ := lintegral_indicator_one hR

end NearCritical
