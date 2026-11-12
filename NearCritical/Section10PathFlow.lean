module

public import NearCritical.Section10Flow
public import NearCritical.NetworkMaximumPrinciple

/-! Section10: the unit current carried by an actual open path. Positive
network edges are selected from actual adjacency; conservation is derived. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open scoped Classical BigOperators
variable {V E : Type*} [Fintype V] [Fintype E]

def edgeUnitCurrent (e : E) (j : E) : ℝ := if j = e then 1 else 0

lemma flowDivergence_add (G : Network V E) (θ ψ : E → ℝ) (v : V) :
    G.flowDivergence (fun e => θ e+ψ e) v = G.flowDivergence θ v+G.flowDivergence ψ v := by
  simp only [flowDivergence,mul_add,Finset.sum_add_distrib]

lemma flowDivergence_neg (G : Network V E) (θ : E → ℝ) (v : V) :
    G.flowDivergence (fun e => -θ e) v = -G.flowDivergence θ v := by
  simp only [flowDivergence,mul_neg,Finset.sum_neg_distrib]

lemma flowDivergence_edgeUnitCurrent (G : Network V E) (e : E) (v : V) :
    G.flowDivergence (edgeUnitCurrent e) v =
      (if G.tail e = v then (1:ℝ) else 0)-(if G.head e = v then (1:ℝ) else 0) := by
  simp [flowDivergence,edgeUnitCurrent,mul_ite]

/-- Every positive-edge walk carries a supported current with the exact
endpoint charges. Reverse traversal contributes NEGATIVE edge current. -/
theorem positive_walk_supported_current (G : Network V E) (a : E → ℝ)
    {x y : V} (w : (G.positiveGraph a Set.univ).Walk x y) :
    ∃ θ : E → ℝ, FlowSupported a θ ∧ ∀ v,
      G.flowDivergence θ v = (if x = v then (1:ℝ) else 0)-(if y = v then (1:ℝ) else 0) := by
  induction w with
  | nil =>
    refine ⟨fun _ => 0,?_,?_⟩
    · intro e _he; rfl
    · intro v; simp [flowDivergence]
  | @cons x z y hadj w ih =>
    obtain ⟨θ,hsupport,hdiv⟩ := ih
    obtain ⟨e,he,hends⟩ := hadj.2.2.2
    rcases hends with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · refine ⟨fun j => edgeUnitCurrent e j+θ j,?_,?_⟩
      · intro j hj
        have hje : j ≠ e := by intro h; subst j; exact (ne_of_gt he) hj
        simp [edgeUnitCurrent,hje,hsupport j hj]
      · intro v
        rw [flowDivergence_add,flowDivergence_edgeUnitCurrent,hdiv,ht,hh]
        ring
    · refine ⟨fun j => -edgeUnitCurrent e j+θ j,?_,?_⟩
      · intro j hj
        have hje : j ≠ e := by intro h; subst j; exact (ne_of_gt he) hj
        simp [edgeUnitCurrent,hje,hsupport j hj]
      · intro v
        rw [flowDivergence_add,flowDivergence_neg,flowDivergence_edgeUnitCurrent,hdiv,ht,hh]
        ring

/-- Endpoint charges, not an assumed conservation field, imply the actual
boundary unit-flow conditions. Different paths may choose different endpoints. -/
theorem endpoint_charges_boundary_unit_flow (G : Network V E) (S T : Set V)
    (hST : Disjoint S T) {x y : V} (hx : x ∈ S) (hy : y ∈ T) (θ : E → ℝ)
    (hdiv : ∀ v, G.flowDivergence θ v =
      (if x = v then (1:ℝ) else 0)-(if y = v then (1:ℝ) else 0)) :
    G.IsBoundaryUnitFlow S T θ := by
  have hxT : x ∉ T := fun h => Set.disjoint_left.mp hST hx h
  have hyS : y ∉ S := fun h => Set.disjoint_left.mp hST h hy
  refine ⟨?_,?_,?_⟩
  · intro v hv
    have hxv : x ≠ v := fun h => hv (Or.inl (h ▸ hx))
    have hyv : y ≠ v := fun h => hv (Or.inr (h ▸ hy))
    rw [hdiv]
    simp only [if_neg hxv,if_neg hyv,sub_self]
  · simp_rw [hdiv]
    rw [Finset.sum_sub_distrib]
    simp [hx,hyS]
  · simp_rw [hdiv]
    rw [Finset.sum_sub_distrib]
    simp [hxT,hy]

/-- An actual positive-network crossing supplies a supported unit flow, ready
for the Section10 averaging and deterministic conductivity comparison. -/
theorem positive_crossing_exists_boundary_unit_flow (G : Network V E) (a : E → ℝ)
    (S T : Set V) (hST : Disjoint S T) {x y : V} (hx : x ∈ S) (hy : y ∈ T)
    (hxy : (G.positiveGraph a Set.univ).Reachable x y) :
    ∃ θ : E → ℝ, FlowSupported a θ ∧ G.IsBoundaryUnitFlow S T θ := by
  obtain ⟨w⟩ := hxy
  obtain ⟨θ,hsupport,hdiv⟩ := positive_walk_supported_current G a w
  exact ⟨θ,hsupport,endpoint_charges_boundary_unit_flow G S T hST hx hy θ hdiv⟩

end NearCritical.Network
