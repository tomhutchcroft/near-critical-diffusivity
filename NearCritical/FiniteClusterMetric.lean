module

public import NearCritical.SelectedNestChain

/-! Actual finite components of a box, and their intrinsic metric. This bridge
is needed to apply the paper's boundary-only spanning diameter to the path
inside an exact selected critical component. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- The actual component of root inside the finite vertex domain U. Filtering
by U prevents the isolated-outside-root convention from adding an outside site. -/
def finiteBoxCluster {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (root : Vertex d) : Finset (Vertex d) := by
  classical
  exact U.filter fun x => (restrictedGraph ω (U : Set (Vertex d))).Reachable root x

lemma mem_finiteBoxCluster {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (root x : Vertex d) : x ∈ finiteBoxCluster ω U root ↔
      x ∈ U ∧ (restrictedGraph ω (U : Set (Vertex d))).Reachable root x := by
  classical
  simp [finiteBoxCluster]

lemma finiteBoxCluster_subset {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (root : Vertex d) : finiteBoxCluster ω U root ⊆ U := by
  intro x hx
  exact ((mem_finiteBoxCluster ω U root x).mp hx).1

lemma root_mem_finiteBoxCluster {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    {root : Vertex d} (hroot : root ∈ U) : root ∈ finiteBoxCluster ω U root :=
  (mem_finiteBoxCluster ω U root root).mpr ⟨hroot, SimpleGraph.Reachable.refl root⟩

lemma finiteBoxCluster_reachable {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (root : Vertex d) {x y : Vertex d} (hx : x ∈ finiteBoxCluster ω U root)
    (hy : y ∈ finiteBoxCluster ω U root) :
    (restrictedGraph ω (U : Set (Vertex d))).Reachable x y :=
  ((mem_finiteBoxCluster ω U root x).mp hx).2.symm.trans
    ((mem_finiteBoxCluster ω U root y).mp hy).2

/-- Every walk starting in the component stays in that SAME component. This
constructs a walk in its exact induced graph without modifying any edge. -/
def finiteBoxClusterWalk {d : ℕ} {ω : Configuration d} {U : Finset (Vertex d)}
    {root x y : Vertex d} (w : (restrictedGraph ω (U : Set (Vertex d))).Walk x y) :
    x ∈ finiteBoxCluster ω U root →
      (restrictedGraph ω (finiteBoxCluster ω U root : Set (Vertex d))).Walk x y := by
  induction w with
  | nil => intro _; exact .nil
  | @cons x z y hadj w ih =>
    intro hx
    have hz : z ∈ finiteBoxCluster ω U root :=
      (mem_finiteBoxCluster ω U root z).mpr ⟨hadj.2.2,
        ((mem_finiteBoxCluster ω U root x).mp hx).2.trans hadj.reachable⟩
    exact .cons ⟨hadj.1, hx, hz⟩ (ih hz)

lemma finiteBoxClusterWalk_length {d : ℕ} {ω : Configuration d} {U : Finset (Vertex d)}
    {root x y : Vertex d} (w : (restrictedGraph ω (U : Set (Vertex d))).Walk x y)
    (hx : x ∈ finiteBoxCluster ω U root) :
    (finiteBoxClusterWalk w hx).length = w.length := by
  induction w with
  | nil => rfl
  | @cons x z y hadj w ih =>
    have hz : z ∈ finiteBoxCluster ω U root :=
      (mem_finiteBoxCluster ω U root z).mpr ⟨hadj.2.2,
        ((mem_finiteBoxCluster ω U root x).mp hx).2.trans hadj.reachable⟩
    change (finiteBoxClusterWalk w hz).length + 1 = w.length + 1
    rw [ih]

lemma finiteBoxCluster_induced_reachable {d : ℕ} (ω : Configuration d)
    (U : Finset (Vertex d)) (root : Vertex d) {x y : Vertex d}
    (hx : x ∈ finiteBoxCluster ω U root) (hy : y ∈ finiteBoxCluster ω U root) :
    (restrictedGraph ω (finiteBoxCluster ω U root : Set (Vertex d))).Reachable x y := by
  obtain ⟨w⟩ := finiteBoxCluster_reachable ω U root hx hy
  exact ⟨finiteBoxClusterWalk w hx⟩

/-- Cube-restricted distances equal distances in the exact finite component.
No equality of two graph metrics is assumed. -/
lemma finiteBoxCluster_dist_eq {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (root : Vertex d) {x y : Vertex d} (hx : x ∈ finiteBoxCluster ω U root)
    (hy : y ∈ finiteBoxCluster ω U root) :
    (restrictedGraph ω (finiteBoxCluster ω U root : Set (Vertex d))).dist x y =
      (restrictedGraph ω (U : Set (Vertex d))).dist x y := by
  apply Nat.le_antisymm
  · obtain ⟨w, hw⟩ := (finiteBoxCluster_reachable ω U root hx hy).exists_walk_length_eq_dist
    have h := SimpleGraph.dist_le (finiteBoxClusterWalk w hx)
    rwa [finiteBoxClusterWalk_length, hw] at h
  · obtain ⟨w, hw⟩ := (finiteBoxCluster_induced_reachable ω U root hx hy).exists_walk_length_eq_dist
    have h := SimpleGraph.dist_le (w.mapLe (restrictedGraph_mono ω
      (show (finiteBoxCluster ω U root : Set (Vertex d)) ⊆ (U : Set (Vertex d)) from
        finiteBoxCluster_subset ω U root)))
    simpa only [SimpleGraph.Walk.length_mapLe, hw] using h

/-- A bound on the paper's cube-restricted distance supplies an intrinsic
connection inside the actual selected critical component. -/
theorem finiteBoxCluster_bounded_connection {d : ℕ} (ω : Configuration d)
    (U : Finset (Vertex d)) (root : Vertex d) {x y : Vertex d}
    (hx : x ∈ finiteBoxCluster ω U root) (hy : y ∈ finiteBoxCluster ω U root)
    {A : ℝ} (hA : ((restrictedGraph ω (U : Set (Vertex d))).dist x y : ℝ) ≤ A) :
    BoundedIntrinsicConnection
      (restrictedGraph ω (finiteBoxCluster ω U root : Set (Vertex d))) x y A := by
  refine ⟨finiteBoxCluster_induced_reachable ω U root hx hy, ?_⟩
  change ((restrictedGraph ω (finiteBoxCluster ω U root : Set (Vertex d))).dist x y : ℝ) ≤ A
  rwa [finiteBoxCluster_dist_eq ω U root hx hy]

end NearCritical
