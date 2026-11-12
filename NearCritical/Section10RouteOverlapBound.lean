module

public import NearCritical.NestChainPath
public import NearCritical.Section10EntanglementCharging

/-! Section10 `lem.nw.overlap` (deterministic core).

The source lemma bounds the microscopic overlap of the two route paths
`γ, γ'` by a uniform per-piece length budget times the number of entanglement
steps:
  `|γ ∩ γ'| ≤ 2(K_spn+K_skl)ℓ₀² · #{u : 𝖤_u}`.

Here we prove the deterministic edge-charging content for two families of
`MicroscopicPiece`s indexed by the route steps. The per-piece edge budget is
DERIVED from `MicroscopicPiece.walk_length` (not assumed). The remaining input
is the cross-block edge-disjointness of pieces at distinct steps
(`lem.nw.path`: pieces in distinct cubes/tubes, and a cluster piece vs a bridge
piece, are edge-disjoint); it enters as the explicit hypothesis `hcross`, to be
discharged from the route-piece geometry separately. `intersectingPieceIndices` is exactly the set of steps at
which the two families share a physical edge, i.e. the entanglement steps.

 -/
@[expose] public section
noncomputable section
open scoped Classical BigOperators

-- `Section10EntanglementCharging` is stated over a generic edge type with no
-- `DecidableEq` parameter, so its finset operations use `Classical.propDecidable`.
-- Force the same instance to win here (over the concrete `Sym2 (Vertex d)` one)
-- so the cover lemma applies without a `DecidableEq`-instance mismatch.
attribute [local instance 100000] Classical.propDecidable

namespace NearCritical.MicroscopicPiece
variable {d : ℕ} {ω : Configuration d} {D : Set (Vertex d)} {P : ℝ} {x y : Vertex d}

/-- Physical unordered-edge set of a microscopic piece's canonical path. -/
def edgeFinset (a : MicroscopicPiece ω D P x y) : Finset (Sym2 (Vertex d)) :=
  a.walk.edges.toFinset

/-- The number of physical edges of a piece is at most its distance budget `P`. -/
theorem edgeFinset_card_le (a : MicroscopicPiece ω D P x y) :
    (a.edgeFinset.card : ℝ) ≤ P := by
  have hc : a.edgeFinset.card ≤ a.walk.length := by
    rw [edgeFinset, List.card_toFinset]
    calc a.walk.edges.dedup.length ≤ a.walk.edges.length :=
          (List.dedup_sublist _).length_le
      _ = a.walk.length := a.walk.length_edges
  calc (a.edgeFinset.card : ℝ) ≤ (a.walk.length : ℝ) := by exact_mod_cast hc
    _ ≤ P := a.walk_length

end NearCritical.MicroscopicPiece

namespace NearCritical.Section10
variable {d : ℕ} {ω : Configuration d} {D : Set (Vertex d)}

/-- `lem.nw.overlap`, deterministic core: the microscopic-edge overlap of two
route path-piece families is at most the uniform per-piece budget `Pb` times the
number of entanglement steps (indices where the two families' pieces share a
physical edge). `hcross` is the `lem.nw.path` cross-block edge-disjointness
input. -/
theorem route_pieces_overlap_le_entanglements {I : Type*} [Fintype I] {Pb : ℝ}
    {xp yp xq yq : I → Vertex d}
    (p : ∀ i, MicroscopicPiece ω D Pb (xp i) (yp i))
    (q : ∀ i, MicroscopicPiece ω D Pb (xq i) (yq i))
    (hcross : ∀ i j, i ≠ j →
      Disjoint (p i).edgeFinset (q j).edgeFinset) :
    (((Finset.univ.biUnion fun i => (p i).edgeFinset) ∩
        (Finset.univ.biUnion fun i => (q i).edgeFinset)).card : ℝ)
      ≤ Pb * ((intersectingPieceIndices (fun i => (p i).edgeFinset)
          (fun i => (q i).edgeFinset)).card : ℝ) :=
  common_edges_card_le_budget_times_entanglements
    (Finset.univ.biUnion fun i => (p i).edgeFinset)
    (Finset.univ.biUnion fun i => (q i).edgeFinset)
    (fun i => (p i).edgeFinset) (fun i => (q i).edgeFinset)
    (Finset.Subset.refl _) (Finset.Subset.refl _) hcross
    (fun i => (p i).edgeFinset_card_le)

end NearCritical.Section10
