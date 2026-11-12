module

public import NearCritical.SpanningBoundaryDiameter
public import NearCritical.ChemicalCrossingLength

/-! Actual finite-component instantiation of the selected microscopic trace.
The metric/interface fields are proved from the paper's distinct-face rin;
random production of the local typical data remains unresolved. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- Arbitrary finite domains and labelled faces include translated route cubes.
This supplies the trace's metric field inside the FULL actual component. -/
theorem finiteCluster_faceInterface_connection {d : ℕ} {φ : Type*}
    [Fintype φ] [DecidableEq φ] [Nontrivial φ]
    (ω : Configuration d) (U : Finset (Vertex d)) (root : Vertex d)
    (faces : φ → Finset (Vertex d))
    (hspan : ∀ i, (finiteBoxCluster ω U root ∩ faces i).Nonempty) {K : ℝ}
    (hdiam : (spanningFaceDiameter (restrictedGraph ω (U : Set (Vertex d)))
      (finiteBoxCluster ω U root) faces : ℝ) ≤ K)
    {x y : Vertex d} (hx : x ∈ clusterFaceBoundary (finiteBoxCluster ω U root) faces)
    (hy : y ∈ clusterFaceBoundary (finiteBoxCluster ω U root) faces) :
    BoundedIntrinsicConnection
      (restrictedGraph ω (finiteBoxCluster ω U root : Set (Vertex d))) x y (2*K) := by
  obtain ⟨i, hi⟩ := (mem_clusterFaceBoundary _ _ x).mp hx
  obtain ⟨j, hj⟩ := (mem_clusterFaceBoundary _ _ y).mp hy
  have h := boundary_dist_le_twice_spanningFaceDiameter (restrictedGraph ω (U : Set (Vertex d)))
    (finiteBoxCluster ω U root) faces hspan
    (fun x hx y hy => finiteBoxCluster_reachable ω U root hx hy) hi hj
  apply finiteBoxCluster_bounded_connection ω U root
    (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hj).1
  have hR : ((restrictedGraph ω (U : Set (Vertex d))).dist x y : ℝ) ≤
      2*(spanningFaceDiameter (restrictedGraph ω (U : Set (Vertex d)))
        (finiteBoxCluster ω U root) faces : ℝ) := by exact_mod_cast h
  linarith

/-- Raw local data for an actual finite-component nest trace. Unlike the generic
selected trace, there are no supplied site sets or bounded metric connections:
components, interfaces and short critical connections are constructed below.
The face spanning/rin inputs and random exploration identification remain open. -/
structure ActualClusterNestData (d : ℕ) (ι φ : Type*) [Fintype φ] [DecidableEq φ]
    (ω : Configuration d) (D : Set (Vertex d)) (K B : ℝ) (n : ℕ) where
  critical : Configuration d
  critical_le : ∀ e, critical e = true → ω e = true
  cube : ℕ → Finset (Vertex d)
  cube_subset : ∀ t, t ≤ n → (cube t : Set (Vertex d)) ⊆ D
  root : ℕ → ι → Vertex d
  faces : ℕ → φ → Finset (Vertex d)
  nest : ℕ → Finset ι
  representative : ℕ → ι
  representative_mem : ∀ t, t ≤ n → representative t ∈ nest t
  spanning : ∀ t, t ≤ n → ∀ i,
    (finiteBoxCluster critical (cube t) (root t (representative t)) ∩ faces t i).Nonempty
  face_diameter : ∀ t, t ≤ n →
    (spanningFaceDiameter (restrictedGraph critical (cube t : Set (Vertex d)))
      (finiteBoxCluster critical (cube t) (root t (representative t))) (faces t) : ℝ) ≤ K
  step : ∀ t, t < n → NestSprinklingStep d ι ω D B
  critical_sides : ∀ t (ht : t < n),
    (step t ht).leftGraph ≤ openGraph critical ∧ (step t ht).rightGraph ≤ openGraph critical
  source_on_face : ∀ t (ht : t < n), ∀ x ∈ (step t ht).sourceBoundary,
    ∃ i, x ∈ finiteBoxCluster critical (cube t) (root t (representative t)) ∩ faces t i
  target_on_face : ∀ t (ht : t < n), ∀ c, ∀ y ∈ (step t ht).targetBoundary c,
    ∃ i, y ∈ finiteBoxCluster critical (cube (t+1)) (root (t+1) c) ∩ faces (t+1) i
  next_nest_offspring : ∀ t (ht : t < n), nest (t+1) ⊆ (step t ht).offspring

namespace ActualClusterNestData

/-- The actual full critical component at a chosen cube and cluster label. -/
def component {d : ℕ} {ι φ : Type*} [Fintype φ] [DecidableEq φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ActualClusterNestData d ι φ ω D K B n) (t : ℕ) (c : ι) : Finset (Vertex d) :=
  finiteBoxCluster dat.critical (dat.cube t) (dat.root t c)

/-- Exactly the component's union of labelled-face intersections. -/
def boundary {d : ℕ} {ι φ : Type*} [Fintype φ] [DecidableEq φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ActualClusterNestData d ι φ ω D K B n) (t : ℕ) (c : ι) : Finset (Vertex d) :=
  clusterFaceBoundary (dat.component t c) (dat.faces t)

/-- All metric/interface fields are PROVED from actual components and source
face rin. This constructs the generalized trace with spanning coefficient2K. -/
def toSelectedTrace {d : ℕ} {ι φ : Type*} [Fintype φ] [DecidableEq φ] [Nontrivial φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ActualClusterNestData d ι φ ω D K B n) : SelectedNestTrace d ι ω D (2*K) B n where
  critical := dat.critical
  critical_le := dat.critical_le
  nest := dat.nest
  representative := dat.representative
  representative_mem := dat.representative_mem
  sites := fun t c => (dat.component t c : Set (Vertex d))
  interfaceSites := fun t c => (dat.boundary t c : Set (Vertex d))
  interface_subset := fun t _ => clusterFaceBoundary_subset _ _
  sites_subset := by
    intro t ht x hx
    exact dat.cube_subset t ht (finiteBoxCluster_subset _ _ _ hx)
  typical_diameter := by
    intro t ht x hx y hy
    exact finiteCluster_faceInterface_connection dat.critical (dat.cube t)
      (dat.root t (dat.representative t)) (dat.faces t)
      (dat.spanning t ht) (dat.face_diameter t ht) hx hy
  step := dat.step
  critical_sides := dat.critical_sides
  source_in_representative := by
    intro t ht x hx
    exact (mem_clusterFaceBoundary _ _ x).mpr (dat.source_on_face t ht x hx)
  target_in_cluster := by
    intro t ht c y hy
    exact (mem_clusterFaceBoundary _ _ y).mpr (dat.target_on_face t ht c y hy)
  next_nest_offspring := dat.next_nest_offspring

/-- Actual local components, not arbitrary supplied graphs, construct a
confined self-avoiding path with the corrected spanning factor and terminal+1. -/
theorem exists_path_with_exit {d : ℕ} {ι φ : Type*} [Fintype φ] [DecidableEq φ] [Nontrivial φ]
    {ω : Configuration d} {D : Set (Vertex d)} {K B : ℝ} {n : ℕ}
    (dat : ActualClusterNestData d ι φ ω D K B n) {x y z : Vertex d}
    (hx : x ∈ dat.boundary 0 (dat.representative 0))
    (hy : y ∈ dat.boundary n (dat.representative n))
    (hexit : (openGraph ω).Adj y z) (hz : z ∈ D) :
    ∃ p : (restrictedGraph ω D).Walk x z, p.IsPath ∧
      (p.length : ℝ) ≤ ((n:ℝ)+1)*(2*K)+(n:ℝ)*B+1 :=
  dat.toSelectedTrace.exists_path_with_exit hx hy hexit hz

/-- Literal confined crossing from actual finite critical components and the
source initial/exit witnesses, without a metric-connection/path hypothesis. -/
theorem crossing {d r : ℕ} {ι φ : Type*} [Fintype φ] [DecidableEq φ] [Nontrivial φ]
    (a : Vertex d) (i : Fin d) {ω : Configuration d} {K B C : ℝ} {n : ℕ}
    (dat : ActualClusterNestData d ι φ ω
      (translateSites a (chemicalCrossingSupport d r i) : Set (Vertex d)) K B n)
    (hbottom : ∃ x ∈ chemicalBottomFace d r i,
      a+x ∈ dat.boundary 0 (dat.representative 0))
    (hexit : ∃ y ∈ dat.boundary n (dat.representative n),
      ∃ z ∈ chemicalExitFace d r i, (openGraph ω).Adj y (a+z))
    (hlen : ((n:ℝ)+1)*(2*K)+(n:ℝ)*B+1 ≤ C*(2*r+1:ℕ)) :
    ω ∈ chemicalBoxCrossingEvent a r i C :=
  dat.toSelectedTrace.crossing a i hbottom hexit hlen

/-- Full deterministic source-scale consumer: the final length bound is DERIVED
from the route and scale identities. The corrected coefficient2Kspn and terminal
exit+1 are both absorbed explicitly; no final crossing-length bound is assumed. -/
theorem crossing_with_source_length {d R : ℕ} {ι φ : Type*}
    [Fintype φ] [DecidableEq φ] [Nontrivial φ] (a : Vertex d) (i : Fin d)
    {ω : Configuration d} {Kspn Kskl : ℝ} {n M ell0 s n0 ellStar : ℕ}
    (dat : ActualClusterNestData d ι φ ω
      (translateSites a (chemicalCrossingSupport d R i) : Set (Vertex d))
      (Kspn*(ell0:ℝ)^2) (Kskl*(ell0:ℝ)^2) n)
    (hspn : 0≤Kspn) (hskl : 0≤Kskl)
    (hbottom : ∃ x ∈ chemicalBottomFace d R i,
      a+x ∈ dat.boundary 0 (dat.representative 0))
    (hexit : ∃ y ∈ dat.boundary n (dat.representative n),
      ∃ z ∈ chemicalExitFace d R i, (openGraph ω).Adj y (a+z))
    (hn : n+1≤2*M) (hM : 2≤M) (hscale : ell0=n0*ellStar)
    (hstar : 1≤ellStar) (hs : 1≤s) (hside : (M-1)*ell0+s=2*R+1) :
    ω ∈ chemicalBoxCrossingEvent a R i
      ((4*(2*Kspn+Kskl)*(n0:ℝ)+1)*(ellStar:ℝ)) := by
  obtain ⟨x, hx, hxsite⟩ := hbottom
  obtain ⟨y, hysite, z, hz, hopen⟩ := hexit
  have hgeom : MicroscopicChainGeometry
      (restrictedGraph ω (translateSites a (chemicalCrossingSupport d R i) : Set (Vertex d)))
      ((2*Kspn)*(ell0:ℝ)^2) (Kskl*(ell0:ℝ)^2) n (a+x) y := by
    simpa only [mul_assoc] using dat.toSelectedTrace.geometry hxsite hysite
  have hyD := dat.toSelectedTrace.sites_subset n (by omega)
    (dat.toSelectedTrace.interface_subset n (by omega) hysite)
  have hzD : a+z ∈ translateSites a (chemicalCrossingSupport d R i) :=
    (mem_translateSites a (chemicalCrossingSupport d R i) z).mpr
      (Finset.mem_union.mpr (Or.inr hz))
  exact microscopicChain_crossing_with_source_length a i (by linarith) hskl hx hz
    hgeom ⟨hopen, hyD, hzD⟩ hn hM hscale hstar hs hside

end ActualClusterNestData
end NearCritical
