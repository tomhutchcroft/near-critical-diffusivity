module

public import NearCritical.NetworkBoundaryAccess
public import NearCritical.NetworkEdgeUpdate
public import NearCritical.NetworkTwoArm

/-! The deterministic pivotal-support statement behind `lem.pivot_trick`.
Use the opened minimizer and potential-separated certificates; the tested edge
is absent from both certificates, so both connections exist before opening. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open Set NearCritical.BernoulliCalculus
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : NearCritical.Network V E)

/-- The two opposite-face alternatives in equation `eq.two_arm`. -/
def binaryTwoArm (low high : Set V) (η : E → Bool) (e : E) : Prop :=
  G.DisjointBoundaryConnections (binaryWeights η) (G.tail e) low (G.head e) high ∨
    G.DisjointBoundaryConnections (binaryWeights η) (G.tail e) high (G.head e) low

/-- A finite-volume conductivity-changing opening has the source's closed-edge
and two-arm support. No boundary-access hypothesis is left as an input. -/
theorem binaryConductance_pivotal_support {low high : Set V} {data : V → ℝ} {lo hi : ℝ}
    (hlohi : lo ≤ hi) (hlow : ∀ v ∈ low, data v = lo) (hhigh : ∀ v ∈ high, data v = hi)
    (η : E → Bool) (e : E)
    (hchange : G.binaryConductance (low ∪ high) data (forceOpen e η) ≠
      G.binaryConductance (low ∪ high) data η) :
    η e = false ∧ G.binaryTwoArm low high η e := by
  obtain ⟨hclosed, hgrad, _⟩ := G.binaryConductance_opening_change (low ∪ high) data η e hchange
  let u := G.binaryMinimizer (low ∪ high) data (forceOpen e η)
  have hu := G.binaryMinimizer_spec (low ∪ high) data (forceOpen e η)
  have hHar := hu.isHarmonic G
  have he : 0 < binaryWeights (forceOpen e η) e := by
    simp [binaryWeights, forceOpen_eq_update]
  have hpaths := hHar.edge_nonzero_both_reach_boundary G (binaryWeights_nonneg _) e he hgrad
  have hlow_u : ∀ v ∈ low, u v = lo := by
    intro v hv
    exact (hu.1 v (Or.inl hv)).trans (hlow v hv)
  have hhigh_u : ∀ v ∈ high, u v = hi := by
    intro v hv
    exact (hu.1 v (Or.inr hv)).trans (hhigh v hv)
  have hab : ∀ f, f ≠ e → binaryWeights η f = binaryWeights (forceOpen e η) f := by
    intro f hf
    simp [binaryWeights, forceOpen_eq_update, hf]
  have hne : u (G.tail e) ≠ u (G.head e) := by
    intro h
    exact hgrad (by change u (G.head e) - u (G.tail e) = 0; rw [← h, sub_self])
  refine ⟨hclosed, ?_⟩
  obtain hlt | hgt := lt_or_gt_of_ne hne
  · have hsep := hHar.separatedBoundaryConnections_of_lt G (binaryWeights_nonneg _)
      hlohi hlow_u hhigh_u hpaths.1 hpaths.2 hlt
    exact Or.inl (hsep.change_crossing_edge G hlt e (Or.inl ⟨rfl, rfl⟩) hab)
  · have hsep := hHar.separatedBoundaryConnections_of_lt G (binaryWeights_nonneg _)
      hlohi hlow_u hhigh_u hpaths.2 hpaths.1 hgt
    exact Or.inr ((hsep.change_crossing_edge G hgt e (Or.inr ⟨rfl, rfl⟩) hab).symm G)

end NearCritical.Network
