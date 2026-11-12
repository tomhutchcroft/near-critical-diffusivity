module

public import NearCritical.ClusterCountSpatialSum
public import NearCritical.CriticalBoxMass

/-! Source eq.var.N with the spatial input derived from actual assumption(A).
No independent spatial-sum or variance estimate remains as a premise. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- ONE positive coefficient chosen before all radii, finite root sets,
cluster properties and size caps. Spatial mass is derived from actual(A). -/
theorem critical_rootedPropertyCount_centered_bound {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (Z : Finset (Vertex d)), Z ⊆ centeredBox d N →
      ∀ (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (V : ℝ),
      (∀ ω r, r ∈ Z → rootedClusterProperty (centeredBox d N) r P ω →
        ((finiteBoxCluster ω (centeredBox d N) r).card:ℝ) ≤ V) →
      (∫ ω, (rootedPropertyCount (centeredBox d N) Z P ω -
        rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P)^2
        ∂percolation d (criticalPoint d)) ≤
      rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P +
        (Z.card:ℝ)*(K*(N+1:ℝ)^2) +
        V*(K*(N+1:ℝ)^2)*rootedPropertyCountMean (criticalPoint d) (centeredBox d N) Z P := by
  obtain ⟨K, hK, hmass⟩ := critical_twoPoint_mass_in_centered_box hd hA
  refine ⟨K, hK, ?_⟩
  intro N Z hZ P V hcap
  exact rootedPropertyCount_centered_spatial_bound (criticalPoint d) (centeredBox d N) Z hZ P
    (show 0 ≤ K*(N+1:ℝ)^2 by positivity) (hmass N Z hZ) hcap

end NearCritical
