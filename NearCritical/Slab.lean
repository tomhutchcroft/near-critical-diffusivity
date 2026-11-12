module

public import NearCritical.Events

@[expose] public section
namespace NearCritical
open MeasureTheory

/-- Restrict edges to a vertex set; outside vertices are isolated. This avoids
changing the probability space when comparing two nested slabs. -/
def restrictedGraph {d : ℕ} (ω : Configuration d) (S : Set (Vertex d)) : SimpleGraph (Vertex d) where
  Adj x y := (openGraph ω).Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := ⟨by rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩⟩
  loopless := ⟨by rintro x ⟨h, _⟩; exact h.ne rfl⟩

lemma restrictedGraph_mono {d : ℕ} (ω : Configuration d) {S T : Set (Vertex d)}
    (hST : S ⊆ T) : restrictedGraph ω S ≤ restrictedGraph ω T := by
  rintro x y ⟨h, hx, hy⟩
  exact ⟨h, hST hx, hST hy⟩

def restrictedInfiniteEvent (d : ℕ) (S : Set (Vertex d)) : Set (Configuration d) :=
  {ω | {y | (restrictedGraph ω S).Reachable 0 y}.Infinite}

lemma measurableSet_restricted_adj {d : ℕ} (S : Set (Vertex d)) (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | (restrictedGraph ω S).Adj x y} := by
  exact (measurableSet_open_adj x y).inter (MeasurableSet.const _)

lemma measurableSet_restrictedInfiniteEvent (d : ℕ) (S : Set (Vertex d)) :
    MeasurableSet (restrictedInfiniteEvent d S) :=
  measurableSet_graphInfiniteCluster (fun ω ↦ restrictedGraph ω S)
    (measurableSet_restricted_adj S) 0

@[simp] lemma restrictedGraph_univ {d : ℕ} (ω : Configuration d) :
    restrictedGraph ω Set.univ = openGraph ω := by
  ext x y
  simp [restrictedGraph]

@[simp] lemma restrictedInfiniteEvent_univ (d : ℕ) :
    restrictedInfiniteEvent d Set.univ = infiniteClusterEvent d := by
  ext ω
  simp [restrictedInfiniteEvent, infiniteClusterEvent, cluster]

noncomputable def restrictedDensity (d : ℕ) (S : Set (Vertex d)) (p : unitInterval) : ℝ :=
  (percolation d p).real (restrictedInfiniteEvent d S)

noncomputable def restrictedCriticalPoint (d : ℕ) (S : Set (Vertex d)) : unitInterval :=
  sInf {p | 0 < restrictedDensity d S p}

@[simp] lemma restrictedDensity_univ (d : ℕ) (p : unitInterval) :
    restrictedDensity d Set.univ p = density d p := by
  simp [restrictedDensity, density]

@[simp] lemma restrictedCriticalPoint_univ (d : ℕ) :
    restrictedCriticalPoint d Set.univ = criticalPoint d := by
  simp [restrictedCriticalPoint, criticalPoint]

lemma restrictedInfiniteEvent_mono {d : ℕ} {S T : Set (Vertex d)} (hST : S ⊆ T) :
    restrictedInfiniteEvent d S ⊆ restrictedInfiniteEvent d T := by
  intro ω hω
  exact hω.mono (fun y hy ↦ SimpleGraph.Reachable.mono (restrictedGraph_mono ω hST) hy)

lemma restrictedDensity_mono {d : ℕ} {S T : Set (Vertex d)} (hST : S ⊆ T)
    (p : unitInterval) : restrictedDensity d S p ≤ restrictedDensity d T p := by
  exact measureReal_mono (restrictedInfiniteEvent_mono hST)

/-- Increasing the available vertex set decreases the critical point. -/
theorem restrictedCriticalPoint_antitone {d : ℕ} {S T : Set (Vertex d)} (hST : S ⊆ T) :
    restrictedCriticalPoint d T ≤ restrictedCriticalPoint d S := by
  apply sInf_le_sInf
  intro p hp
  exact lt_of_lt_of_le hp (restrictedDensity_mono hST p)

lemma criticalPoint_le_restrictedCriticalPoint (d : ℕ) (S : Set (Vertex d)) :
    criticalPoint d ≤ restrictedCriticalPoint d S := by
  rw [← restrictedCriticalPoint_univ]
  exact restrictedCriticalPoint_antitone (Set.subset_univ S)

/-- `ℤ^k × {0,...,n}^{d-k}` in the original lattice coordinates. -/
def slabVertices (d k n : ℕ) : Set (Vertex d) :=
  {x | ∀ i : Fin d, k ≤ i.val → 0 ≤ x i ∧ x i ≤ (n : ℤ)}

lemma slabVertices_mono (d n : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    slabVertices d j n ⊆ slabVertices d k n := by
  intro x hx i hi
  exact hx i (hjk.trans hi)

/-- The middle inequality of Theorem 1.3, without its quantitative bounds. -/
theorem slabCriticalPoint_comparison (d n : ℕ) (hd : 3 ≤ d) :
    restrictedCriticalPoint d (slabVertices d (d - 1) n) ≤
      restrictedCriticalPoint d (slabVertices d 2 n) := by
  apply restrictedCriticalPoint_antitone
  apply slabVertices_mono
  omega

end NearCritical
