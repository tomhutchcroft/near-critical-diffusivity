module

public import NearCritical.NetworkTwoArm
public import NearCritical.NetworkEdgeUpdate

/-! Standard finite-coordinate forcing certificates and disjoint occurrence.
The mask-based network certificates are proved equivalent to this universal
outside-assignment definition for Bernoulli boundary connection events. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set

/-- F forces the event when fixing its coordinates to their values in η,
regardless of every coordinate outside F. -/
def ForcesOn {E : Type*} (A : Set (E → Bool)) (η : E → Bool) (F : Set E) : Prop :=
  ∀ θ : E → Bool, (∀ e ∈ F, θ e = η e) → θ ∈ A

/-- Standard disjoint occurrence, with disjoint finite coordinate certificates.
Certificates may initially contain both open and closed coordinates. -/
def DisjointOccurrence {E : Type*} (A B : Set (E → Bool)) (η : E → Bool) : Prop :=
  ∃ F H : Set E, F.Finite ∧ H.Finite ∧ Disjoint F H ∧ ForcesOn A η F ∧ ForcesOn B η H

namespace Network
variable {V E : Type*} (G : NearCritical.Network V E)

/-- The ordinary connection event to a target set in the positive Bernoulli graph. -/
def boundaryConnectionEvent (x : V) (A : Set V) : Set (E → Bool) :=
  {η | ∃ z ∈ A, (G.positiveGraph (binaryWeights η) Set.univ).Reachable x z}

lemma positiveGraph_edgeRestricted_le_of_positive {a b : E → ℝ} {F : Set E}
    (hb : ∀ e ∈ F, 0 < b e) :
    G.positiveGraph (edgeRestrictedWeights a F) Set.univ ≤ G.positiveGraph b Set.univ := by
  classical
  rintro x y ⟨hne, hx, hy, e, he, hends⟩
  have heF : e ∈ F := by
    by_contra hn
    simp [edgeRestrictedWeights, hn] at he
  exact ⟨hne, hx, hy, e, hb e heF, hends⟩

/-- Positive finite edge masks force their connections under all outside
coordinate modifications, giving standard disjoint occurrence. -/
theorem DisjointBoundaryConnections.to_disjointOccurrence {η : E → Bool}
    {x y : V} {A B : Set V} (h : G.DisjointBoundaryConnections (binaryWeights η) x A y B) :
    DisjointOccurrence (G.boundaryConnectionEvent x A) (G.boundaryConnectionEvent y B) η := by
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hx, hy⟩ := h
  refine ⟨F, H, hFinF, hFinH, hdisj, ?_, ?_⟩
  · intro θ hagree
    obtain ⟨z, hz, hpath⟩ := hx
    refine ⟨z, hz, SimpleGraph.Reachable.mono (G.positiveGraph_edgeRestricted_le_of_positive ?_) hpath⟩
    intro e he
    simpa only [binaryWeights, hagree e he] using hF e he
  · intro θ hagree
    obtain ⟨z, hz, hpath⟩ := hy
    refine ⟨z, hz, SimpleGraph.Reachable.mono (G.positiveGraph_edgeRestricted_le_of_positive ?_) hpath⟩
    intro e he
    simpa only [binaryWeights, hagree e he] using hH e he

/-- Keep exactly the values of η on F, and close every coordinate outside F. -/
def certificateConfiguration (η : E → Bool) (F : Set E) (e : E) : Bool := by
  classical
  exact if e ∈ F then η e else false

/-- Only the open coordinates of a forcing set are needed for connection events. -/
def openCertificate (η : E → Bool) (F : Set E) : Set E := {e | e ∈ F ∧ η e = true}

lemma edgeRestrictedWeights_openCertificate (η : E → Bool) (F : Set E) :
    edgeRestrictedWeights (binaryWeights η) (openCertificate η F) =
      binaryWeights (certificateConfiguration η F) := by
  classical
  funext e
  by_cases he : e ∈ F <;> cases hη : η e <;>
    simp [edgeRestrictedWeights, binaryWeights, openCertificate, certificateConfiguration, he, hη]

/-- For connection events, arbitrary finite forcing certificates can be replaced
by disjoint finite open-edge masks. Closing all outside certificate coordinates
constructs the required masked connections. -/
theorem disjointBoundaryConnections_of_disjointOccurrence {η : E → Bool} {x y : V} {A B : Set V}
    (h : DisjointOccurrence (G.boundaryConnectionEvent x A) (G.boundaryConnectionEvent y B) η) :
    G.DisjointBoundaryConnections (binaryWeights η) x A y B := by
  classical
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH⟩ := h
  have hx := hF (certificateConfiguration η F)
    (by intro e he; simp [certificateConfiguration, he])
  have hy := hH (certificateConfiguration η H)
    (by intro e he; simp [certificateConfiguration, he])
  refine ⟨openCertificate η F, openCertificate η H,
    hFinF.subset (fun e he ↦ he.1), hFinH.subset (fun e he ↦ he.1), ?_, ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e heF heH
    exact Set.disjoint_left.mp hdisj heF.1 heH.1
  · intro e he
    simp [binaryWeights, he.2]
  · intro e he
    simp [binaryWeights, he.2]
  · rw [edgeRestrictedWeights_openCertificate]
    exact hx
  · rw [edgeRestrictedWeights_openCertificate]
    exact hy

/-- Exact equivalence with standard finite-coordinate disjoint occurrence for
the two Bernoulli boundary connection events. -/
theorem disjointBoundaryConnections_iff_disjointOccurrence (η : E → Bool)
    (x y : V) (A B : Set V) :
    G.DisjointBoundaryConnections (binaryWeights η) x A y B ↔
      DisjointOccurrence (G.boundaryConnectionEvent x A) (G.boundaryConnectionEvent y B) η :=
  ⟨fun h ↦ h.to_disjointOccurrence G, G.disjointBoundaryConnections_of_disjointOccurrence⟩

/-- The two-arm theorem expressed with standard disjoint-occurrence events,
including the case where the tested pair is not joined by an open edge. -/
theorem IsHarmonic.two_arm_disjointOccurrence [Fintype E] {η : E → Bool} {u : V → ℝ}
    {low high : Set V} {lo hi : ℝ} {x y : V}
    (hu : G.IsHarmonic (binaryWeights η) (low ∪ high) u)
    (hlohi : lo ≤ hi)
    (hlow : ∀ v ∈ low, u v = lo) (hhigh : ∀ v ∈ high, u v = hi)
    (hx : ∃ z ∈ low ∪ high, (G.positiveGraph (binaryWeights η) Set.univ).Reachable x z)
    (hy : ∃ z ∈ low ∪ high, (G.positiveGraph (binaryWeights η) Set.univ).Reachable y z)
    (hne : u x ≠ u y) :
    DisjointOccurrence (G.boundaryConnectionEvent x low) (G.boundaryConnectionEvent y high) η ∨
      DisjointOccurrence (G.boundaryConnectionEvent x high) (G.boundaryConnectionEvent y low) η := by
  obtain h | h := hu.two_arm G (binaryWeights_nonneg η) hlohi hlow hhigh hx hy hne
  · exact Or.inl (h.to_disjointOccurrence G)
  · exact Or.inr (h.to_disjointOccurrence G)

end Network
end NearCritical
