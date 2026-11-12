module

public import NearCritical.LatticeFaces
public import NearCritical.NetworkTwoArm

/-! Specialization of the deterministic two-arm theorem to the paper's issued
lattice edges and the two actual extreme-coordinate faces of U⁺. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set

/-- The deterministic event appearing in `eq.two_arm`, with finite disjoint
positive-edge witnesses. Both tested-edge orientations are included. -/
def latticeTwoArm {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) (x y : DomainVertex U) : Prop :=
  (issuedNetwork U).DisjointBoundaryConnections (domainWeights ω) x (negativeFace U i) y (positiveFace U i) ∨
    (issuedNetwork U).DisjointBoundaryConnections (domainWeights ω) x (positiveFace U i) y (negativeFace U i)

/-- The source lemma `lem.two_arm` for its actual finite lattice domains.
There is no openness hypothesis on a tested edge between the two vertices. -/
theorem lattice_two_arm {d : ℕ} {U : Finset (Vertex d)} (hU : U.Nonempty) (i : Fin d)
    (ω : Configuration d) {u : DomainVertex U → ℝ}
    (hu : (issuedNetwork U).IsMinimizer (domainWeights ω) (twoFaceBoundary U i) (coordinateData i) u)
    {x y : DomainVertex U}
    (hx : ∃ z ∈ twoFaceBoundary U i,
      ((issuedNetwork U).positiveGraph (domainWeights ω) Set.univ).Reachable x z)
    (hy : ∃ z ∈ twoFaceBoundary U i,
      ((issuedNetwork U).positiveGraph (domainWeights ω) Set.univ).Reachable y z)
    (hne : u x ≠ u y) : latticeTwoArm U i ω x y := by
  obtain ⟨l, hl⟩ := negativeFace_nonempty hU i
  obtain ⟨h, hh⟩ := positiveFace_nonempty hU i
  have hlow : ∀ v ∈ negativeFace U i, u v = coordinateData i l := by
    intro v hv
    rw [hu.1 v (by rw [twoFaceBoundary_eq_union]; exact Or.inl hv)]
    exact negativeFace_data_constant hv hl
  have hhigh : ∀ v ∈ positiveFace U i, u v = coordinateData i h := by
    intro v hv
    rw [hu.1 v (by rw [twoFaceBoundary_eq_union]; exact Or.inr hv)]
    exact positiveFace_data_constant hv hh
  have hHar : (issuedNetwork U).IsHarmonic (domainWeights ω)
      (negativeFace U i ∪ positiveFace U i) u := by
    rw [← twoFaceBoundary_eq_union]
    exact hu.isHarmonic (issuedNetwork U)
  rw [twoFaceBoundary_eq_union] at hx hy
  exact hHar.two_arm (issuedNetwork U) (domainWeights_nonneg ω)
    (face_data_lt hU hl hh).le hlow hhigh hx hy hne

end NearCritical
