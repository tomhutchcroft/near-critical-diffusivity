module

public import NearCritical.Section10IssuedPath

/-! Section10 lem.nw.overlap support inclusion.

`issued_internal_walk_exit_current` (and the generic
`positive_trail_boundary_current_energy` it calls) return the support set `P`
of the issued boundary unit current but DROP the physical-edge inclusion
`s(tail e, head e) ∈ w.edges` that `positive_trail_current` actually proves.
`lem.nw.overlap` needs that inclusion: the overlap of two bypassed route
currents is bounded by the overlap of the underlying walk edges.

This leaf re-exposes it without editing the existing issued-path API:
`positive_trail_boundary_current_energy_support` is the boundary current with the
retained inclusion, and `issued_internal_walk_exit_current_support` specialises it
to the issued network, placing every support edge among the mapped internal-walk
edges or at the single final exit bond `s(internalIssuedVertex U y,
issuedExitVertex U y i)`.

 -/
@[expose] public section
noncomputable section

namespace NearCritical.Network
open scoped Classical BigOperators
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Boundary variant of `positive_trail_current` that, beyond
`positive_trail_boundary_current_energy`, RETAINS the physical-edge support
inclusion `s(G.tail e, G.head e) ∈ w.edges`. -/
theorem positive_trail_boundary_current_energy_support (G : Network V E) (a : E → ℝ)
    (ha : ∀ e, a e = 0 ∨ a e = 1) (S T : Set V) (hST : Disjoint S T)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T)
    (w : (G.positiveGraph a Set.univ).Walk x y) (hw : w.IsTrail) :
    ∃ (P : Finset E) (θ : E → ℝ),
      G.IsBoundaryUnitFlow S T θ ∧ FlowSupported a θ ∧
      (∀ e, |θ e| ≤ if e ∈ P then (1:ℝ) else 0) ∧
      (∀ e ∈ P, a e = 1) ∧ P.card ≤ w.length ∧
      flowEnergy a θ ≤ (w.length:ℝ) ∧
      (∀ e ∈ P, s(G.tail e, G.head e) ∈ w.edges) := by
  obtain ⟨P,θ,hpos,hmap,hcard,hmag,hsupp,hdiv⟩ := positive_trail_current G a w hw
  have hopen (e : E) (he : e ∈ P) : a e = 1 := by
    rcases ha e with hz | ho
    · have hp := hpos e he
      linarith
    · exact ho
  have hecard : flowEnergy a θ ≤ (P.card:ℝ) := by
    have hb := path_current_pair_energy_le_overlap a θ θ P P hmag hmag hopen
    simpa only [Finset.inter_self,flowEnergy,pow_two] using hb
  refine ⟨P,θ,endpoint_charges_boundary_unit_flow G S T hST hx hy θ hdiv,
    hsupp,hmag,hopen,hcard,hecard.trans ?_,hmap⟩
  exact_mod_cast hcard

end NearCritical.Network

namespace NearCritical.Section10
open scoped Classical

/-- Support-tracking variant of `issued_internal_walk_exit_current`: the same
supported unit boundary current, with every support edge's physical endpoints
lying among the mapped internal-walk edges or at the single final exit bond. -/
theorem issued_internal_walk_exit_current_support {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) (S T : Set (DomainVertex U)) (hST : Disjoint S T)
    (x y : ↥(U : Set (Vertex d))) (i : Fin d)
    (hx : internalIssuedVertex U x ∈ S) (hz : issuedExitVertex U y i ∈ T)
    (w : ((openGraph ω).induce (U : Set (Vertex d))).Walk x y)
    (hexit : ω (y.val,i) = true) :
    ∃ (P : Finset (IssuedBond U)) (θ : IssuedBond U → ℝ),
      (issuedNetwork U).IsBoundaryUnitFlow S T θ ∧ Network.FlowSupported (domainWeights ω) θ ∧
      (∀ e, |θ e| ≤ if e ∈ P then (1:ℝ) else 0) ∧
      (∀ e ∈ P, (domainWeights ω : IssuedBond U → ℝ) e = 1) ∧
      P.card ≤ w.length+1 ∧ Network.flowEnergy (domainWeights ω) θ ≤ (w.length+1:ℕ) ∧
      (∀ e ∈ P,
        s((issuedNetwork U).tail e, (issuedNetwork U).head e)
            ∈ (w.map (issuedInternalGraphHom U ω)).edges ∨
          s((issuedNetwork U).tail e, (issuedNetwork U).head e)
            = s(internalIssuedVertex U y, issuedExitVertex U y i)) := by
  let φ := issuedInternalGraphHom U ω
  have hadj : ((issuedNetwork U).positiveGraph (domainWeights ω) Set.univ).Adj
      (φ y) (issuedExitVertex U y i) :=
    issued_positive_adj_of_open_bond U ω (y.val,i) y.property hexit _ _ (Or.inl ⟨rfl,rfl⟩)
  let v := (w.map φ).concat hadj
  have ha (e : IssuedBond U) : (domainWeights ω : IssuedBond U → ℝ) e = 0 ∨
      (domainWeights ω : IssuedBond U → ℝ) e = 1 := by
    cases he : ω e.val <;> simp [domainWeights,issuedBond,he]
  obtain ⟨P,θ,hunit,hsupp,hmag,hopen,hcard,henergy,hmap⟩ :=
    Network.positive_trail_boundary_current_energy_support (issuedNetwork U) (domainWeights ω)
      ha S T hST hx hz v.bypass v.bypass_isPath.isTrail
  have hlen : v.bypass.length ≤ w.length+1 := by
    calc
      _ ≤ v.length := v.length_bypass_le_length
      _ = _ := by simp only [v,SimpleGraph.Walk.length_concat,SimpleGraph.Walk.length_map]
  have hφy : φ y = internalIssuedVertex U y := rfl
  have hmag' (e : IssuedBond U) : |θ e| ≤ if e ∈ P then (1:ℝ) else 0 := by
    have h := hmag e
    by_cases he : e ∈ P
    · rw [if_pos he] at h ⊢
      exact h
    · rw [if_neg he] at h ⊢
      exact h
  have hsub : ∀ e ∈ P,
      s((issuedNetwork U).tail e, (issuedNetwork U).head e) ∈ (w.map φ).edges ∨
        s((issuedNetwork U).tail e, (issuedNetwork U).head e)
          = s(internalIssuedVertex U y, issuedExitVertex U y i) := by
    intro e he
    have h1 : s((issuedNetwork U).tail e, (issuedNetwork U).head e) ∈ v.bypass.edges := hmap e he
    have h2 : s((issuedNetwork U).tail e, (issuedNetwork U).head e) ∈ v.edges :=
      SimpleGraph.Walk.edges_bypass_subset_edges v h1
    rw [show v = (w.map φ).concat hadj from rfl, SimpleGraph.Walk.edges_concat,
      List.concat_eq_append] at h2
    rcases List.mem_append.mp h2 with h | h
    · exact Or.inl h
    · rw [List.mem_singleton] at h
      exact Or.inr (hφy ▸ h)
  refine ⟨P,θ,hunit,hsupp,hmag',hopen,hcard.trans hlen,henergy.trans ?_,hsub⟩
  exact_mod_cast hlen

end NearCritical.Section10
