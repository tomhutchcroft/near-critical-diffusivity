module

public import NearCritical.ActualClusterTrace

/-! Canonical actual component labels for source k-nests and pre-good counts.
A finite image deduplicates roots in the same component. Uniform selection and
stochastic typicality estimates are separate source obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical

lemma finiteBoxCluster_rebase {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (root : Vertex d) {x : Vertex d} (hx : x ∈ finiteBoxCluster ω U root) :
    finiteBoxCluster ω U x = finiteBoxCluster ω U root := by
  ext y
  simp only [mem_finiteBoxCluster]
  have hrx := ((mem_finiteBoxCluster ω U root x).mp hx).2
  exact ⟨fun h => ⟨h.1, hrx.trans h.2⟩, fun h => ⟨h.1, hrx.symm.trans h.2⟩⟩

/-- Distinct components, rather than their possibly repeated roots. -/
def finiteClusterFamily {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d)) :
    Finset (Finset (Vertex d)) := by
  classical
  exact U.image (finiteBoxCluster ω U)

lemma mem_finiteClusterFamily {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (C : Finset (Vertex d)) : C ∈ finiteClusterFamily ω U ↔
      ∃ x ∈ U, finiteBoxCluster ω U x = C := by
  classical
  simp [finiteClusterFamily]

lemma finiteClusterFamily_nonempty_component {d : ℕ} (ω : Configuration d)
    (U : Finset (Vertex d)) {C : Finset (Vertex d)} (hC : C ∈ finiteClusterFamily ω U) :
    C.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := (mem_finiteClusterFamily ω U C).mp hC
  exact ⟨x, root_mem_finiteBoxCluster ω U hx⟩

lemma finiteClusterFamily_component_subset {d : ℕ} (ω : Configuration d)
    (U : Finset (Vertex d)) {C : Finset (Vertex d)} (hC : C ∈ finiteClusterFamily ω U) :
    C ⊆ U := by
  obtain ⟨x, _, rfl⟩ := (mem_finiteClusterFamily ω U C).mp hC
  exact finiteBoxCluster_subset ω U x

/-- Every vertex in a component recovers exactly that component as its root. -/
lemma finiteClusterFamily_recover {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    {C : Finset (Vertex d)} (hC : C ∈ finiteClusterFamily ω U) {x : Vertex d} (hx : x ∈ C) :
    finiteBoxCluster ω U x = C := by
  obtain ⟨root, _, rfl⟩ := (mem_finiteClusterFamily ω U C).mp hC
  exact finiteBoxCluster_rebase ω U root hx

lemma finiteClusterFamily_disjoint {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    {C E : Finset (Vertex d)} (hC : C ∈ finiteClusterFamily ω U)
    (hE : E ∈ finiteClusterFamily ω U) (hne : C ≠ E) : Disjoint C E := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxC hxE
  exact hne ((finiteClusterFamily_recover ω U hC hxC).symm.trans
    (finiteClusterFamily_recover ω U hE hxE))

lemma finiteClusterFamily_union {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d)) :
    (finiteClusterFamily ω U).biUnion id = U := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
    exact finiteClusterFamily_component_subset ω U hC hxC
  · intro hx
    exact Finset.mem_biUnion.mpr ⟨finiteBoxCluster ω U x,
      (mem_finiteClusterFamily ω U _).mpr ⟨x, hx, rfl⟩, root_mem_finiteBoxCluster ω U hx⟩

/-- Exact partition mass; in particular roots are not counted as separate
clusters when they belong to the same component. -/
lemma finiteClusterFamily_sum_card {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d)) :
    ∑ C ∈ finiteClusterFamily ω U, C.card = U.card := by
  classical
  rw [← Finset.card_biUnion]
  · exact congrArg Finset.card (finiteClusterFamily_union ω U)
  · intro C hC E hE hne
    exact finiteClusterFamily_disjoint ω U hC hE hne

/-- A total canonical representative for a finite vertex set. Its value on the
empty set is irrelevant for actual components, which are proved nonempty. -/
def finiteClusterRoot {d : ℕ} (C : Finset (Vertex d)) : Vertex d :=
  if h : C.Nonempty then Classical.choose h else 0

lemma finiteClusterRoot_mem {d : ℕ} {C : Finset (Vertex d)} (hC : C.Nonempty) :
    finiteClusterRoot C ∈ C := by
  simp only [finiteClusterRoot, dite_eq_left hC]
  exact Classical.choose_spec hC

lemma finiteClusterRoot_recovers {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    {C : Finset (Vertex d)} (hC : C ∈ finiteClusterFamily ω U) :
    finiteBoxCluster ω U (finiteClusterRoot C) = C :=
  finiteClusterFamily_recover ω U hC
    (finiteClusterRoot_mem (finiteClusterFamily_nonempty_component ω U hC))

lemma finiteClusterRoot_injective {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d)) :
    Set.InjOn finiteClusterRoot (finiteClusterFamily ω U : Set (Finset (Vertex d))) := by
  intro C hC E hE hroot
  rw [← finiteClusterRoot_recovers ω U hC, ← finiteClusterRoot_recovers ω U hE, hroot]

/-- Literal typical-component family for any component-local predicate. The
full source typicality predicate/probability is not supplied by this definition. -/
def filteredClusterFamily {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) : Finset (Finset (Vertex d)) := by
  classical
  exact (finiteClusterFamily ω U).filter P

/-- Vertices whose ACTUAL component satisfies the same predicate. -/
def filteredClusterVertices {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) : Finset (Vertex d) := by
  classical
  exact U.filter fun x => P (finiteBoxCluster ω U x)

lemma filteredClusterFamily_union {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) :
    (filteredClusterFamily ω U P).biUnion id = filteredClusterVertices ω U P := by
  classical
  ext x
  simp only [filteredClusterFamily, filteredClusterVertices, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨C, ⟨hC, hP⟩, hx⟩
    refine ⟨finiteClusterFamily_component_subset ω U hC hx, ?_⟩
    rwa [finiteClusterFamily_recover ω U hC hx]
  · rintro ⟨hx, hP⟩
    exact ⟨finiteBoxCluster ω U x,
      ⟨(mem_finiteClusterFamily ω U _).mpr ⟨x, hx, rfl⟩, hP⟩,
      root_mem_finiteBoxCluster ω U hx⟩

/-- Exact source pre-good counting identity: every satisfying component is
counted once as a cluster and once per vertex in the rooted indicator sum. -/
lemma filteredClusterFamily_sum_card {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) :
    ∑ C ∈ filteredClusterFamily ω U P, C.card = (filteredClusterVertices ω U P).card := by
  classical
  rw [← Finset.card_biUnion]
  · exact congrArg Finset.card (filteredClusterFamily_union ω U P)
  · intro C hC E hE hne
    exact finiteClusterFamily_disjoint ω U (Finset.mem_filter.mp hC).1
      (Finset.mem_filter.mp hE).1 hne

/-- Deterministic volume-to-number bound used in source pre-good Step3. -/
theorem filteredClusterFamily_volume_count {d : ℕ} (ω : Configuration d)
    (U : Finset (Vertex d)) (P : Finset (Vertex d) → Prop) {v : ℝ}
    (hsize : ∀ C ∈ filteredClusterFamily ω U P, v ≤ (C.card : ℝ)) :
    v * (filteredClusterFamily ω U P).card ≤ (filteredClusterVertices ω U P).card := by
  classical
  calc
    _ = ∑ C ∈ filteredClusterFamily ω U P, v := by simp [mul_comm]
    _ ≤ ∑ C ∈ filteredClusterFamily ω U P, (C.card : ℝ) := Finset.sum_le_sum hsize
    _ = (filteredClusterVertices ω U P).card := by
      exact_mod_cast filteredClusterFamily_sum_card ω U P

lemma filteredClusterVertices_mono {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    {P Q : Finset (Vertex d) → Prop} (hPQ : ∀ C, P C → Q C) :
    filteredClusterVertices ω U P ⊆ filteredClusterVertices ω U Q := by
  classical
  intro x hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
    hPQ _ (Finset.mem_filter.mp hx).2⟩

/-- Source Step3 counts typical components against the broader spanning-vertex
indicator. No equality of those two predicates or probability bound is assumed. -/
theorem filteredClusterFamily_volume_count_of_implies {d : ℕ} (ω : Configuration d)
    (U : Finset (Vertex d)) (P Q : Finset (Vertex d) → Prop) {v : ℝ}
    (hsize : ∀ C ∈ filteredClusterFamily ω U P, v ≤ (C.card : ℝ))
    (hPQ : ∀ C, P C → Q C) :
    v * (filteredClusterFamily ω U P).card ≤ (filteredClusterVertices ω U Q).card := by
  have h := filteredClusterFamily_volume_count ω U P hsize
  have hcard := Finset.card_le_card (filteredClusterVertices_mono ω U hPQ)
  exact h.trans (by exact_mod_cast hcard)

end NearCritical
