module

public import NearCritical.ResamplingLaw
public import NearCritical.Section9RevealSupport

/-! The heart-union reveal is a stopping set, and resampling preserves the heart
clusters.

* `heartRevealSet Q H ω`: the bonds of `Q` incident to the union of the clusters
  of `Q` that meet the heart `H` (open cluster bonds and closed boundary bonds).
* `heartRevealSet_stopping`: a configuration agreeing with `ω` on
  `heartRevealSet Q H ω` has the same heart union and the same reveal set.
* `cubeReveal Q H K ξ` (indices = internal bonds of `Q`, configuration closed
  outside `Q`): the reveal set enlarged by a FIXED set `K` of bonds (the cube
  bonds on which no second copy exists). `cubeReveal_stopping`.
* `cube_resample_law`: for any product law on the internal bonds, keeping the
  first sample on `cubeReveal` and using an independent second sample elsewhere
  preserves the law; `cube_resample_heartUnion`: the heart union of the
  composite is that of the first sample.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Set
open scoped Classical

variable {d : ℕ}

/-- Bonds of `Q` incident to the heart union. -/
def heartRevealSet (Q H : Finset (Vertex d)) (ω : Configuration d) : Finset (Bond d) :=
  clusterRevealBonds Q (heartClusterUnion ω Q H)

theorem heartRevealSet_stopping (Q H : Finset (Vertex d)) (hH : H ⊆ Q)
    (ω ω' : Configuration d) (hagree : ∀ e ∈ heartRevealSet Q H ω, ω' e = ω e) :
    heartClusterUnion ω' Q H = heartClusterUnion ω Q H ∧
      heartRevealSet Q H ω' = heartRevealSet Q H ω := by
  have h : heartClusterUnion ω' Q H = heartClusterUnion ω Q H :=
    (heartClusterUnion_eq_iff_reveal_agree Q H (heartClusterUnion ω Q H) hH ω ω'
      (fun e he => (hagree e he).symm)).mp rfl
  exact ⟨h, by unfold heartRevealSet; rw [h]⟩

lemma heartRevealSet_subset (Q H : Finset (Vertex d)) (ω : Configuration d) :
    heartRevealSet Q H ω ⊆ internalBondSet Q :=
  Finset.filter_subset _ _

lemma reconstructInterior_apply (Q : Finset (Vertex d)) (ξ : internalBondSet Q → Bool)
    (e : Bond d) (he : e ∈ internalBondSet Q) : reconstructInterior Q ξ e = ξ ⟨e, he⟩ := by
  simp [reconstructInterior, extendConfiguration, he]

/-- The reveal set in internal-bond indices, enlarged by a fixed set `K`. -/
def cubeReveal (Q H : Finset (Vertex d)) (K : Finset (internalBondSet Q))
    (ξ : internalBondSet Q → Bool) : Finset (internalBondSet Q) :=
  (Finset.univ.filter fun e : internalBondSet Q =>
    (e : Bond d) ∈ heartRevealSet Q H (reconstructInterior Q ξ)) ∪ K

theorem cubeReveal_agree (Q H : Finset (Vertex d)) (hH : H ⊆ Q)
    (K : Finset (internalBondSet Q)) (ξ ξ' : internalBondSet Q → Bool)
    (hagree : ∀ e ∈ cubeReveal Q H K ξ, ξ' e = ξ e) :
    heartClusterUnion (reconstructInterior Q ξ') Q H =
        heartClusterUnion (reconstructInterior Q ξ) Q H ∧
      cubeReveal Q H K ξ' = cubeReveal Q H K ξ := by
  have h := heartRevealSet_stopping Q H hH (reconstructInterior Q ξ) (reconstructInterior Q ξ')
    (fun e he => by
      have heQ := heartRevealSet_subset Q H _ he
      rw [reconstructInterior_apply Q ξ' e heQ, reconstructInterior_apply Q ξ e heQ]
      exact hagree ⟨e, heQ⟩ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)))
  exact ⟨h.1, by unfold cubeReveal; rw [h.2]⟩

theorem cubeReveal_stopping (Q H : Finset (Vertex d)) (hH : H ⊆ Q)
    (K : Finset (internalBondSet Q)) (ξ ξ' : internalBondSet Q → Bool)
    (hagree : ∀ e ∈ cubeReveal Q H K ξ, ξ' e = ξ e) :
    cubeReveal Q H K ξ' = cubeReveal Q H K ξ :=
  (cubeReveal_agree Q H hH K ξ ξ' hagree).2

/-- Resampling the unrevealed bonds outside `K` preserves any product law on the
internal bonds of the cube. -/
theorem cube_resample_law (Q H : Finset (Vertex d)) (hH : H ⊆ Q)
    (K : Finset (internalBondSet Q)) (μ : internalBondSet Q → Measure Bool)
    [∀ e, IsProbabilityMeasure (μ e)] :
    Measure.map (resample (cubeReveal Q H K)) ((Measure.pi μ).prod (Measure.pi μ)) =
      Measure.pi μ :=
  resample_law μ (cubeReveal Q H K) (cubeReveal_stopping Q H hH K)

/-- The composite has the heart union of the first sample. -/
theorem cube_resample_heartUnion (Q H : Finset (Vertex d)) (hH : H ⊆ Q)
    (K : Finset (internalBondSet Q))
    (q : (internalBondSet Q → Bool) × (internalBondSet Q → Bool)) :
    heartClusterUnion (reconstructInterior Q (resample (cubeReveal Q H K) q)) Q H =
      heartClusterUnion (reconstructInterior Q q.1) Q H :=
  (cubeReveal_agree Q H hH K q.1 (resample (cubeReveal Q H K) q) fun e he => by
    unfold resample
    rw [if_pos he]).1

end NearCritical
