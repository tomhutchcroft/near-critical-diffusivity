module

public import NearCritical.FiniteClusterMetric

/-! Literal source eq.def.rin is a distinct-face boundary diameter, NOT a
whole-cluster diameter. Any two boundary points are at distance at most twice
this diameter: same-face points use a point on another spanning face. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- The finite maximum in source eq.def.rin, over distinct labelled faces and
their cluster boundary points. Empty maxima have value zero. -/
def spanningFaceDiameter {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (C : Finset V) (faces : ι → Finset V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (ι × ι)).filter fun p => p.1 ≠ p.2).sup fun p =>
    ((C ∩ faces p.1).product (C ∩ faces p.2)).sup fun xy => G.dist xy.1 xy.2

lemma dist_le_spanningFaceDiameter {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) (C : Finset V) (faces : ι → Finset V) {i j : ι}
    (hij : i ≠ j) {x y : V} (hx : x ∈ C ∩ faces i) (hy : y ∈ C ∩ faces j) :
    G.dist x y ≤ spanningFaceDiameter G C faces := by
  classical
  unfold spanningFaceDiameter
  refine Finset.le_sup_of_le (b := (i,j)) ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hij
  · exact Finset.le_sup (s := (C ∩ faces i).product (C ∩ faces j))
      (b := (x,y)) (f := fun xy : V × V => G.dist xy.1 xy.2)
      (Finset.mem_product.mpr ⟨hx, hy⟩)

/-- Boundary-only consequence. This deliberately makes NO assertion about
arbitrary interior vertices of the cluster. No all-vertex diameter is assumed. -/
theorem boundary_dist_le_twice_spanningFaceDiameter {V ι : Type*}
    [DecidableEq V] [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (G : SimpleGraph V) (C : Finset V) (faces : ι → Finset V)
    (hspan : ∀ i, (C ∩ faces i).Nonempty)
    (hconn : ∀ x ∈ C, ∀ y ∈ C, G.Reachable x y)
    {i j : ι} {x y : V} (hx : x ∈ C ∩ faces i) (hy : y ∈ C ∩ faces j) :
    G.dist x y ≤ 2*spanningFaceDiameter G C faces := by
  classical
  by_cases hij : i=j
  · subst j
    obtain ⟨k, hki⟩ := exists_ne i
    obtain ⟨z, hz⟩ := hspan k
    have hxz := dist_le_spanningFaceDiameter G C faces hki.symm hx hz
    have hzy := dist_le_spanningFaceDiameter G C faces hki hz hy
    have htriangle := (hconn x (Finset.mem_inter.mp hx).1 z
      (Finset.mem_inter.mp hz).1).dist_triangle_left y
    omega
  · have h := dist_le_spanningFaceDiameter G C faces hij hx hy
    omega

/-- Literal signed faces of the paper's odd cube, including its vertices. -/
def signedCubeFace (d r : ℕ) (face : Fin d × Bool) : Finset (Vertex d) := by
  classical
  exact (centeredBox d r).filter fun x => x face.1 = if face.2 then (r:ℤ) else -(r:ℤ)

/-- Actual finite critical cluster and literal distinct-face rin. It yields a
short connection inside the exact component for boundary-interface endpoints,
with an explicit factor2 in the spanning constant. -/
theorem finiteBoxCluster_boundary_connection {d r : ℕ} [NeZero d]
    (ω : Configuration d) (root : Vertex d)
    (hspan : ∀ i : Fin d × Bool,
      (finiteBoxCluster ω (centeredBox d r) root ∩ signedCubeFace d r i).Nonempty)
    {i j : Fin d × Bool} {x y : Vertex d}
    (hx : x ∈ finiteBoxCluster ω (centeredBox d r) root ∩ signedCubeFace d r i)
    (hy : y ∈ finiteBoxCluster ω (centeredBox d r) root ∩ signedCubeFace d r j)
    {K : ℝ}
    (hdiam : (spanningFaceDiameter (restrictedGraph ω (centeredBox d r : Set (Vertex d)))
      (finiteBoxCluster ω (centeredBox d r) root) (signedCubeFace d r) : ℝ) ≤ K) :
    BoundedIntrinsicConnection (restrictedGraph ω
      (finiteBoxCluster ω (centeredBox d r) root : Set (Vertex d))) x y (2*K) := by
  classical
  have h := boundary_dist_le_twice_spanningFaceDiameter
    (restrictedGraph ω (centeredBox d r : Set (Vertex d)))
    (finiteBoxCluster ω (centeredBox d r) root) (signedCubeFace d r) hspan
    (fun x hx y hy => finiteBoxCluster_reachable ω (centeredBox d r) root hx hy) hx hy
  apply finiteBoxCluster_bounded_connection ω (centeredBox d r) root
    (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1
  have hR : ((restrictedGraph ω (centeredBox d r : Set (Vertex d))).dist x y : ℝ) ≤
      2*(spanningFaceDiameter (restrictedGraph ω (centeredBox d r : Set (Vertex d)))
        (finiteBoxCluster ω (centeredBox d r) root) (signedCubeFace d r) : ℝ) := by
    exact_mod_cast h
  linarith

/-- The cluster's boundary interface, rather than all of its interior vertices. -/
def clusterFaceBoundary {V ι : Type*} [DecidableEq V] [Fintype ι]
    (C : Finset V) (faces : ι → Finset V) : Finset V :=
  Finset.univ.biUnion fun i => C ∩ faces i

lemma mem_clusterFaceBoundary {V ι : Type*} [DecidableEq V] [Fintype ι]
    (C : Finset V) (faces : ι → Finset V) (x : V) :
    x ∈ clusterFaceBoundary C faces ↔ ∃ i, x ∈ C ∩ faces i := by
  simp [clusterFaceBoundary]

lemma clusterFaceBoundary_subset {V ι : Type*} [DecidableEq V] [Fintype ι]
    (C : Finset V) (faces : ι → Finset V) : clusterFaceBoundary C faces ⊆ C := by
  intro x hx
  obtain ⟨i, hi⟩ := (mem_clusterFaceBoundary C faces x).mp hx
  exact (Finset.mem_inter.mp hi).1

/-- This is the boundary-only typical_diameter field required by the generalized
SelectedNestTrace: the graph is the FULL actual critical component, and only
its interface endpoints require the source diameter bound. -/
theorem finiteBoxCluster_interface_connection {d r : ℕ} [NeZero d]
    (ω : Configuration d) (root : Vertex d)
    (hspan : ∀ i : Fin d × Bool,
      (finiteBoxCluster ω (centeredBox d r) root ∩ signedCubeFace d r i).Nonempty)
    {K : ℝ}
    (hdiam : (spanningFaceDiameter (restrictedGraph ω (centeredBox d r : Set (Vertex d)))
      (finiteBoxCluster ω (centeredBox d r) root) (signedCubeFace d r) : ℝ) ≤ K) :
    ∀ x ∈ clusterFaceBoundary (finiteBoxCluster ω (centeredBox d r) root) (signedCubeFace d r),
    ∀ y ∈ clusterFaceBoundary (finiteBoxCluster ω (centeredBox d r) root) (signedCubeFace d r),
      BoundedIntrinsicConnection (restrictedGraph ω
        (finiteBoxCluster ω (centeredBox d r) root : Set (Vertex d))) x y (2*K) := by
  intro x hx y hy
  obtain ⟨i, hi⟩ := (mem_clusterFaceBoundary _ _ x).mp hx
  obtain ⟨j, hj⟩ := (mem_clusterFaceBoundary _ _ y).mp hy
  exact finiteBoxCluster_boundary_connection ω root hspan hi hj hdiam

end NearCritical
