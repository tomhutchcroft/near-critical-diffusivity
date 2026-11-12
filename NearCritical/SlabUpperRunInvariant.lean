module

public import NearCritical.SlabUpperOneStepGood

/-! Nest invariant along the ACTUAL run only.

`exploreRun_good` asks for the one-step facts at every state satisfying
`ExploreInv`. For a state-dependent success rule (the current `k`-nest is a
function of the history, source 6096-6099) the facts are only available at
states that are consistent with the sample `x`. `exploreRun_good_inv` therefore
carries an extra invariant `J` of the state, preserved by `exploreNext` under
the actual outcome `succ σ x`, and requires `hroot`/`hedge` only when `J` holds.

`explorePayoff_ne_zero_good_inv` and `slab_good_of_oneStep_inv` are the payoff
and slab versions; the latter produces exactly the `good` field consumed by
`coupledRenormalizedExploration_of_slabBlocks`.

Deterministic; no probability.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open scoped ENNReal Classical

section
variable {Vx Ed : Type*} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
variable (ends : Ed → Vx × Vx) (o : Vx)

theorem exploreRun_good_inv {Ω : Vx ⊕ Ed → Type*} [∀ i, MeasurableSpace (Ω i)]
    (succ : ExploreState Vx Ed → (∀ i, Ω i) → Bool) (x : ∀ i, Ω i) (Good : Vx → Prop)
    (J : ExploreState Vx Ed → Prop)
    (hJ : ∀ σ i, ExploreInv ends o σ → J σ → exploreQuery ends o σ = some i →
      J (exploreNext ends o σ (succ σ x)))
    (hroot : ∀ σ, ExploreInv ends o σ → J σ → exploreMove ends o σ = some .root →
      succ σ x = true → Good o)
    (hedge : ∀ σ e z, ExploreInv ends o σ → J σ → (∀ v ∈ σ.A, Good v) →
      exploreMove ends o σ = some (.edge e z) → succ σ x = true → Good z) :
    ∀ n σ, ExploreInv ends o σ → J σ → (∀ v ∈ σ.A, Good v) →
      ∀ v ∈ (adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ n σ x).A, Good v := by
  intro n
  induction n with
  | zero =>
    intro σ _ _ hG
    simpa using hG
  | succ n ih =>
    intro σ hσ hJσ hG
    cases hq : exploreQuery ends o σ with
    | none =>
      rw [adaptiveRun_succ_of_none hq]
      exact hG
    | some i =>
      rw [adaptiveRun_succ_of_some hq]
      refine ih _ (exploreInv_next ends o hσ hq _) (hJ σ i hσ hJσ hq) ?_
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
            · exact hroot σ hσ hJσ hm hb
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
            · exact hedge σ e _ hσ hJσ hG hm hb
            · exact hG v hv

theorem explorePayoff_ne_zero_good_inv {Ω : Vx ⊕ Ed → Type*} [∀ i, MeasurableSpace (Ω i)]
    (D : Finset Vx)
    (succ : ExploreState Vx Ed → (∀ i, Ω i) → Bool) (x : ∀ i, Ω i) (Good : Vx → Prop)
    (J : ExploreState Vx Ed → Prop) (hJ0 : J ⟨∅, ∅, ∅, ∅, ∅⟩)
    (hJ : ∀ σ i, ExploreInv ends o σ → J σ → exploreQuery ends o σ = some i →
      J (exploreNext ends o σ (succ σ x)))
    (hroot : ∀ σ, ExploreInv ends o σ → J σ → exploreMove ends o σ = some .root →
      succ σ x = true → Good o)
    (hedge : ∀ σ e z, ExploreInv ends o σ → J σ → (∀ v ∈ σ.A, Good v) →
      exploreMove ends o σ = some (.edge e z) → succ σ x = true → Good z)
    (h : explorePayoff D (adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ
      (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ x) ≠ 0) :
    ∃ v ∈ D, Good v := by
  have hinv : ExploreInv ends o (⟨∅, ∅, ∅, ∅, ∅⟩ : ExploreState Vx Ed) :=
    ⟨by simp, by simp, by simp, fun _ ↦ rfl, fun h ↦ absurd rfl h⟩
  have hall := exploreRun_good_inv ends o succ x Good J hJ hroot hedge (Fintype.card (Vx ⊕ Ed))
    ⟨∅, ∅, ∅, ∅, ∅⟩ hinv hJ0 (by simp)
  unfold explorePayoff at h
  split_ifs at h with hne
  · obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_inter] at hv
    exact ⟨v, hv.2, hall v hv.1⟩
  · exact absurd rfl h

end

variable {d : ℕ}

/-- The `good` field of the coupled renormalised exploration from one-step facts
required only along states satisfying a run invariant `J`. -/
theorem slab_good_of_oneStep_inv (hd : 2 ≤ d) {n R : ℕ} (S : Set (Vertex d))
    (F : Finset (Vertex d)) (A : Finset (Bond d)) (h0 : (0 : Vertex 2) ∈ centeredBox 2 R)
    (succ : ExploreState (centeredBox 2 R) (boxBonds (centeredBox 2 R)) →
      (∀ i, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) i → Bool) → Bool)
    (ω : Bond d × Bool → Bool) (Good : centeredBox 2 R → Prop)
    (J : ExploreState (centeredBox 2 R) (boxBonds (centeredBox 2 R)) → Prop)
    (hJ0 : J ⟨∅, ∅, ∅, ∅, ∅⟩)
    (hJ : ∀ st i, ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st → J st →
      exploreQuery (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st = some i →
      J (exploreNext (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st
        (succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω))))
    (hjoin : ∀ v, Good v → slabNestJoined n S F (sprinkleConfiguration ω) (v : Vertex 2))
    (hroot : ∀ st, ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st → J st →
      exploreMove (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st = some .root →
      succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
      Good ⟨0, h0⟩)
    (hedge : ∀ st e z, ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st →
      J st → (∀ v ∈ st.A, Good v) →
      exploreMove (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st =
        some (.edge e z) →
      succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
      Good z) :
    explorePayoff (boxInnerBoundary (centeredBox 2 R))
      (adaptiveRun (exploreQuery (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R))
        (exploreNext (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R)) succ
        (Fintype.card (centeredBox 2 R ⊕ boxBonds (centeredBox 2 R))) ⟨∅, ∅, ∅, ∅, ∅⟩
        (blockFamily (slabSprinkleBlocks (d := d) n A (centeredBox 2 R)) ω)) ≠ 0 →
      sprinkleConfiguration ω ∈ restrictedReachFarEvent S F (2 * n * R - n) := by
  intro h
  obtain ⟨v, hv, hG⟩ :=
    explorePayoff_ne_zero_good_inv (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R)
      (boxInnerBoundary (centeredBox 2 R)) succ
      (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) Good J hJ0 hJ hroot hedge h
  obtain ⟨x, hx, w, hw, hr⟩ := hjoin v hG
  refine ⟨x, hx, w, ?_, hr⟩
  simp only [boxInnerBoundary, Finset.mem_filter] at hv
  obtain ⟨y, hy, hadj⟩ := hv.2
  obtain ⟨c, hc⟩ := exists_coord_abs_ge_of_innerBoundary v.2 hy hadj
  exact vertexSize_ge_of_mem_slabCube hd hc hw

end NearCritical
