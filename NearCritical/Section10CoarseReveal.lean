module

public import NearCritical.Section10ClusterUnionReveal
public import NearCritical.CoarseCubeIndependence

/-! Section10 actual finite coarse-cube reveal instance, reusing the project's
mesh2t and translated odd cubes. Radius/rounding conventions remain explicit. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
open MeasureTheory

def coarseRevealCube {d : ℕ} (t r : ℕ) (a : Fin d → ℕ) : Finset (Vertex d) :=
  translateSites (chemicalCoarseCenter t a) (centeredBox d r)

/-- The actual translated smaller heart cube is contained in its outer cube. -/
theorem coarseRevealHeart_subset {d t r h : ℕ} (hhr : h ≤ r) (a : Fin d → ℕ) :
    coarseRevealCube t h a ⊆ coarseRevealCube t r a := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨y,mem_centeredBox.mpr ?_,rfl⟩
  intro k
  have hk := mem_centeredBox.mp hy k
  have hhrZ : (h:ℤ) ≤ (r:ℤ) := by exact_mod_cast hhr
  constructor <;> linarith

/-- Source-mesh separation supplies pairwise disjointness for ANY selected
finite cube family; no geometric-disjointness hypothesis is left to the caller. -/
theorem coarseRevealCubes_pairwiseDisjoint {d t r : ℕ} (hr : r < t)
    (s : Finset (Fin d → ℕ)) : (s : Set (Fin d → ℕ)).PairwiseDisjoint (coarseRevealCube t r) := by
  intro a _ b _ hab
  exact chemicalCoarseCubes_disjoint hr hab

abbrev coarseUnionRevealBonds {d : ℕ} (t r : ℕ) (s : Finset (Fin d → ℕ))
    (F : Finset (Vertex d)) : Finset (Bond d) :=
  clusterFamilyRevealBonds s (coarseRevealCube t r) (fun a => F ∩ coarseRevealCube t r a)

/-- Actual finite source-mesh union reveal depends on the literal recovered
incident mask. Cube separation and heart containment are derived. -/
theorem coarseClusterUnion_reveal_cylinder {d t r h : ℕ} (hr : r < t) (hhr : h ≤ r)
    (s : Finset (Fin d → ℕ)) (F : Finset (Vertex d))
    (hF : F ⊆ s.biUnion (coarseRevealCube t r)) :
    {ω : Configuration d | clusterFamilyUnion ω s (coarseRevealCube t r) (coarseRevealCube t h) = F} =
      (coarseUnionRevealBonds t r s F).restrict ⁻¹'
        clusterFamilyLocalEvent s (coarseRevealCube t r) (coarseRevealCube t h)
          (fun a => F ∩ coarseRevealCube t r a) := by
  exact clusterFamilyUnion_event_cylinder s (coarseRevealCube t r) (coarseRevealCube t h)
    (coarseRevealCubes_pairwiseDisjoint hr s) (fun a _ => coarseRevealHeart_subset hhr a) F hF

/-- Actual normalized fresh-tube product law conditioned on the ACTUAL finite
coarse revealed union. The desired law and geometric separation are derived;
only raw radii, a compatible union value and positive actual atom mass remain. -/
theorem coarseClusterUnion_conditional_freshTube_product {d t r h : ℕ}
    (p : unitInterval) (ht : 1 ≤ t) (hr : r < t) (hhr : h ≤ r)
    (ambient : Finset (Bond d)) (s : Finset (Fin d → ℕ)) (F : Finset (Vertex d))
    (hF : F ⊆ s.biUnion (coarseRevealCube t r))
    (tubes : Finset ((Fin d → ℤ) × Fin d))
    (f : ∀ e : (Fin d → ℤ) × Fin d,
      (freshCoarseTubeBonds (2*(t:ℝ)) ambient (coarseUnionRevealBonds t r s F) e.1 e.2 → Bool) → ℝ)
    (hprob : 0 < (percolation d p).real
      {ω | clusterFamilyUnion ω s (coarseRevealCube t r) (coarseRevealCube t h) = F}) :
    (∫ ω : Configuration d,
      ({η | clusterFamilyUnion η s (coarseRevealCube t r) (coarseRevealCube t h) = F} :
        Set (Configuration d)).indicator (fun _ => (1:ℝ)) ω *
      (∏ e ∈ tubes, f e ((freshCoarseTubeBonds (2*(t:ℝ)) ambient
        (coarseUnionRevealBonds t r s F) e.1 e.2).restrict ω)) ∂percolation d p) /
        (percolation d p).real
          {ω | clusterFamilyUnion ω s (coarseRevealCube t r) (coarseRevealCube t h) = F} =
      ∏ e ∈ tubes, ∫ ω : Configuration d, f e ((freshCoarseTubeBonds (2*(t:ℝ)) ambient
        (coarseUnionRevealBonds t r s F) e.1 e.2).restrict ω) ∂percolation d p := by
  have hell : 0 < 2*(t:ℝ) := by
    have htR : 0 < (t:ℝ) := by exact_mod_cast (show 0 < t by omega)
    positivity
  have hQ := coarseRevealCubes_pairwiseDisjoint hr s
  have hE := clusterFamilyUnion_event_eq_family s (coarseRevealCube t r) (coarseRevealCube t h) hQ F hF
  have hpf : 0 < (percolation d p).real
      (clusterFamilyRevealEvent s (coarseRevealCube t r) (coarseRevealCube t h)
        (fun a => F ∩ coarseRevealCube t r a)) := by
    rw [← hE]
    exact hprob
  have hb := clusterFamilyReveal_conditional_freshTube_product p hell ambient s
    (coarseRevealCube t r) (coarseRevealCube t h) (fun a => F ∩ coarseRevealCube t r a)
    (fun a _ => coarseRevealHeart_subset hhr a) tubes f hpf
  simpa only [coarseUnionRevealBonds,← hE] using hb

end NearCritical.Section10
