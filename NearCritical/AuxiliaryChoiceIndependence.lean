module

public import NearCritical.DifferentialInequality
public import NearCritical.NetworkPivotal
public import NearCritical.NetworkVoltageUniqueness
public import NearCritical.DisjointOccurrence

/-! The source fixes boundary-average constants on boundary-free components. The b term
is independent of that choice because two-arm support anchors both endpoints
to the boundary, even when the tested edge is closed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open Set
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : NearCritical.Network V E)

omit [Fintype V] [Fintype E] in
lemma DisjointBoundaryConnections.boundary_access {a : E → ℝ} {x y : V} {A B : Set V}
    (h : G.DisjointBoundaryConnections a x A y B) :
    (∃ z ∈ A, (G.positiveGraph a Set.univ).Reachable x z) ∧
      (∃ z ∈ B, (G.positiveGraph a Set.univ).Reachable y z) := by
  obtain ⟨F, H, _, _, _, hF, hH, hx, hy⟩ := h
  obtain ⟨zx, hzx, hpathx⟩ := hx
  obtain ⟨zy, hzy, hpathy⟩ := hy
  exact ⟨⟨zx, hzx, SimpleGraph.Reachable.mono (G.positiveGraph_edgeRestricted_le_of_positive hF) hpathx⟩,
    ⟨zy, hzy, SimpleGraph.Reachable.mono (G.positiveGraph_edgeRestricted_le_of_positive hH) hpathy⟩⟩

omit [Fintype V] [Fintype E] in
lemma binaryTwoArm_boundary_access {low high : Set V} {η : E → Bool} {e : E}
    (h : G.binaryTwoArm low high η e) :
    (∃ z ∈ low ∪ high, (G.positiveGraph (binaryWeights η) Set.univ).Reachable (G.tail e) z) ∧
      (∃ z ∈ low ∪ high, (G.positiveGraph (binaryWeights η) Set.univ).Reachable (G.head e) z) := by
  obtain h | h := h
  · obtain ⟨⟨x, hx, hpx⟩, ⟨y, hy, hpy⟩⟩ := h.boundary_access G
    exact ⟨⟨x, Or.inl hx, hpx⟩, ⟨y, Or.inr hy, hpy⟩⟩
  · obtain ⟨⟨x, hx, hpx⟩, ⟨y, hy, hpy⟩⟩ := h.boundary_access G
    exact ⟨⟨x, Or.inr hx, hpx⟩, ⟨y, Or.inl hy, hpy⟩⟩

omit [Fintype V] in
/-- On two-arm support, even a CLOSED-edge voltage is independent of the
selected Dirichlet minimizer. -/
theorem gradient_choice_independent_on_two_arm {low high : Set V} {data : V → ℝ}
    {η : E → Bool} {u v : V → ℝ}
    (hu : G.IsMinimizer (binaryWeights η) (low ∪ high) data u)
    (hv : G.IsMinimizer (binaryWeights η) (low ∪ high) data v)
    {e : E} (h : G.binaryTwoArm low high η e) : G.gradient u e = G.gradient v e := by
  obtain ⟨ht, hh⟩ := G.binaryTwoArm_boundary_access h
  exact hu.gradient_eq_of_endpoints_boundary_access G hv (binaryWeights_nonneg η) e ht hh

/-- The exact b term is unchanged if the arbitrary selected minimizer is
replaced by ANY other Dirichlet minimizer for each configuration. In particular
it agrees with the source's prescribed boundary-average-on-free-components choice. -/
theorem binaryAuxiliary_choice_independent {low high : Set V} {data : V → ℝ}
    (v : (E → Bool) → V → ℝ)
    (hv : ∀ η, G.IsMinimizer (binaryWeights η) (low ∪ high) data (v η)) (r p : ℝ) :
    G.binaryAuxiliary (low ∪ high) data (G.binaryTwoArm low high) r p =
      NearCritical.finiteExpectation p (fun η ↦ r * ∑ e,
        (1 - binaryWeights η e) * (G.gradient (v η) e) ^ 2 *
          if G.binaryTwoArm low high η e then 1 else 0) := by
  classical
  unfold binaryAuxiliary
  congr 1
  funext η
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : G.binaryTwoArm low high η e
  · rw [G.gradient_choice_independent_on_two_arm
      (G.binaryMinimizer_spec (low ∪ high) data η) (hv η) hs]
  · simp [hs]

end NearCritical.Network
