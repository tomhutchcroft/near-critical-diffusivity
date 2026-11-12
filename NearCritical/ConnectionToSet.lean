module

public import NearCritical.CountableBK
public import NearCritical.Slab
public import NearCritical.LatticePivotal

/-! Connections to arbitrary target sets inside an arbitrary vertex domain.
Endpoints are explicitly required to lie in the domain, including zero-length paths. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

def connectionToSetEvent {d : ℕ} (S : Set (Vertex d)) (x : Vertex d)
    (A : Set (Vertex d)) : Set (Configuration d) :=
  {ω | x ∈ S ∧ ∃ y, y ∈ A ∧ y ∈ S ∧ (restrictedGraph ω S).Reachable x y}

lemma measurableSet_connectionToSetEvent {d : ℕ} (S : Set (Vertex d))
    (x : Vertex d) (A : Set (Vertex d)) : MeasurableSet (connectionToSetEvent S x A) := by
  have heq : connectionToSetEvent S x A =
      {ω : Configuration d | x ∈ S} ∩ ⋃ y : Vertex d,
        ({ω : Configuration d | y ∈ A ∧ y ∈ S} ∩
          {ω | (restrictedGraph ω S).Reachable x y}) := by
    ext ω
    simp [connectionToSetEvent]
    aesop
  rw [heq]
  exact (MeasurableSet.const _).inter (MeasurableSet.iUnion fun y ↦
    (MeasurableSet.const _).inter (measurableSet_graphReachable
      (fun ω ↦ restrictedGraph ω S) (measurableSet_restricted_adj S) x y))

lemma connectionToSetEvent_increasing {d : ℕ} (S : Set (Vertex d))
    (x : Vertex d) (A : Set (Vertex d)) : BK.Increasing (connectionToSetEvent S x A) := by
  rintro ω η h ⟨hx, y, hy, hyS, hpath⟩
  refine ⟨hx, y, hy, hyS, SimpleGraph.Reachable.mono ?_ hpath⟩
  rintro u v ⟨huv, hu, hv⟩
  exact ⟨openGraph_mono h huv, hu, hv⟩

lemma connectionToSetEvent_mono {d : ℕ} {S T A B : Set (Vertex d)}
    (hST : S ⊆ T) (hAB : A ⊆ B) (x : Vertex d) :
    connectionToSetEvent S x A ⊆ connectionToSetEvent T x B := by
  rintro ω ⟨hx, y, hy, hyS, hp⟩
  exact ⟨hST hx, y, hAB hy, hST hyS,
    SimpleGraph.Reachable.mono (restrictedGraph_mono ω hST) hp⟩

/-- All-parameter BK for paths to arbitrary targets, including half-space
boundaries. This is a probability product bound, not an arm decay estimate. -/
theorem connectionToSet_bk {d : ℕ} (p : unitInterval) (S T : Set (Vertex d))
    (x y : Vertex d) (A B : Set (Vertex d)) :
    (percolation d p).real {ω | DisjointOccurrence
      (connectionToSetEvent S x A) (connectionToSetEvent T y B) ω} ≤
      (percolation d p).real (connectionToSetEvent S x A) *
        (percolation d p).real (connectionToSetEvent T y B) :=
  percolation_bk d p _ _ (connectionToSetEvent_increasing S x A)
    (connectionToSetEvent_increasing T y B)

/-- The actual issued-edge positive graph embeds in the lattice graph restricted
only to its enlarged support. Extra lattice edges in that support are harmless. -/
def issuedGraphToRestricted {d : ℕ} (U : Finset (Vertex d)) (ω : Configuration d) :
    (issuedNetwork U).positiveGraph
      (Network.binaryWeights ((issuedBondSet U).restrict ω)) Set.univ →g
        restrictedGraph ω (sitesPlus U : Set (Vertex d)) where
  toFun := Subtype.val
  map_rel' := by
    rintro x y ⟨_, _, _, e, he, hends⟩
    refine ⟨?_, x.property, y.property⟩
    have hopen : ω e.val = true := by
      cases hw : ω e.val <;>
        simp [Network.binaryWeights, Finset.restrict, hw] at he ⊢
    refine ⟨e.val, hopen, ?_⟩
    rcases hends with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact Or.inl ⟨(congrArg Subtype.val ht).symm, (congrArg Subtype.val hh).symm⟩
    · exact Or.inr ⟨(congrArg Subtype.val ht).symm, (congrArg Subtype.val hh).symm⟩

/-- Every source finite-domain boundary connection is a genuine restricted
lattice path. This is an inclusion, not an equality of edge sets. -/
theorem latticeBoundaryConnectionEvent_subset {d : ℕ} (U : Finset (Vertex d))
    (x : DomainVertex U) (A : Set (DomainVertex U)) :
    latticeBoundaryConnectionEvent U x A ⊆
      connectionToSetEvent (sitesPlus U : Set (Vertex d)) x.val (Subtype.val '' A) := by
  rintro ω ⟨y, hy, hp⟩
  exact ⟨x.property, y.val, ⟨y, hy, rfl⟩, y.property,
    SimpleGraph.Reachable.map (issuedGraphToRestricted U ω) hp⟩

end NearCritical
