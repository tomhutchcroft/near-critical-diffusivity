module

public import NearCritical.IssuedPartition
public import Mathlib.Data.Int.Interval

/-! Arbitrary integer rectangles and the boundary overlap control used in the
source Dirichlet gluing argument. -/
@[expose] public section
namespace NearCritical
open Finset

noncomputable def latticeRectangle {d : ℕ} (lo hi : Vertex d) : Finset (Vertex d) := by
  classical
  exact Fintype.piFinset (fun j => Finset.Icc (lo j) (hi j))

lemma mem_latticeRectangle {d : ℕ} {lo hi x : Vertex d} :
    x ∈ latticeRectangle lo hi ↔ ∀ j, lo j ≤ x j ∧ x j ≤ hi j := by
  classical
  simp [latticeRectangle, Fintype.mem_piFinset]

/-- The negative coordinate neighbor, inverse to the indexed positive bond. -/
def bondPredecessor {d : ℕ} (x : Vertex d) (j : Fin d) : Vertex d :=
  Function.update x j (x j - 1)

lemma bondTip_predecessor {d : ℕ} (x : Vertex d) (j : Fin d) :
    bondTip (bondPredecessor x j, j) = x := by
  ext k
  by_cases h : k = j
  · subst k; simp [bondTip, bondPredecessor]
  · simp [bondTip, bondPredecessor, h]

lemma predecessor_bondTip {d : ℕ} (e : Bond d) :
    bondPredecessor (bondTip e) e.2 = e.1 := by
  ext k
  by_cases h : k = e.2
  · subst k; simp [bondTip, bondPredecessor]
  · simp [bondTip, bondPredecessor, h]

lemma fullGraph_adj_tip {d : ℕ} (x : Vertex d) (j : Fin d) :
    (openGraph (fun _ => true)).Adj x (bondTip (x,j)) :=
  ⟨(x,j), rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma fullGraph_adj_predecessor {d : ℕ} (x : Vertex d) (j : Fin d) :
    (openGraph (fun _ => true)).Adj x (bondPredecessor x j) := by
  exact ⟨(bondPredecessor x j,j), rfl, Or.inr ⟨rfl, (bondTip_predecessor x j).symm⟩⟩

lemma neighbor_mem_of_not_boundary {d : ℕ} {S : Finset (Vertex d)}
    {x y : Vertex d} (hx : x ∈ S) (hb : x ∉ boundarySites S)
    (hxy : (openGraph (fun _ => true)).Adj x y) : y ∈ S := by
  classical
  by_contra hy
  exact hb (Finset.mem_filter.mpr ⟨hx, y, hy, hxy⟩)

/-- Every interior point of the enlarged rectangle is strictly above each lower
face, and at most the original upper face in every coordinate. -/
lemma rectangle_interior_bounds {d : ℕ} {lo hi x : Vertex d}
    (hx : x ∈ sitesPlus (latticeRectangle lo hi))
    (hb : x ∉ boundarySites (sitesPlus (latticeRectangle lo hi))) :
    ∀ j, lo j < x j ∧ x j ≤ hi j := by
  intro j
  have hbounds := sitesPlus_coordinate_bounds (latticeRectangle lo hi) j
    (fun y hy => (mem_latticeRectangle.mp hy) j)
  have hn := hbounds (bondPredecessor x j)
    (neighbor_mem_of_not_boundary hx hb (fullGraph_adj_predecessor x j))
  have hp := hbounds (bondTip (x,j))
    (neighbor_mem_of_not_boundary hx hb (fullGraph_adj_tip x j))
  simp only [bondPredecessor, Function.update_self] at hn
  simp only [bondTip, Function.update_self] at hp
  omega

lemma rectangle_interior_mem {d : ℕ} {lo hi x : Vertex d}
    (hx : x ∈ sitesPlus (latticeRectangle lo hi))
    (hb : x ∉ boundarySites (sitesPlus (latticeRectangle lo hi))) :
    x ∈ latticeRectangle lo hi := by
  exact mem_latticeRectangle.mpr (fun j =>
    ⟨(rectangle_interior_bounds hx hb j).1.le, (rectangle_interior_bounds hx hb j).2⟩)

lemma rectangle_interior_predecessor_mem {d : ℕ} {lo hi x : Vertex d}
    (hx : x ∈ sitesPlus (latticeRectangle lo hi))
    (hb : x ∉ boundarySites (sitesPlus (latticeRectangle lo hi))) (j : Fin d) :
    bondPredecessor x j ∈ latticeRectangle lo hi := by
  apply mem_latticeRectangle.mpr
  intro k
  have hk := rectangle_interior_bounds hx hb k
  by_cases h : k = j
  · subst k
    simp only [bondPredecessor, Function.update_self]
    omega
  · simpa [bondPredecessor, h] using And.intro hk.1.le hk.2

/-- The interior of one enlarged rectangle misses the enlarged support of any
base set disjoint from the rectangle. The other set need not be a rectangle. -/
lemma rectangle_interior_not_mem_other_sitesPlus {d : ℕ} {lo hi x : Vertex d}
    {W : Finset (Vertex d)} (hd : Disjoint (latticeRectangle lo hi) W)
    (hx : x ∈ sitesPlus (latticeRectangle lo hi))
    (hb : x ∉ boundarySites (sitesPlus (latticeRectangle lo hi))) :
    x ∉ sitesPlus W := by
  classical
  intro hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact Finset.disjoint_left.mp hd (rectangle_interior_mem hx hb) hw
  · obtain ⟨y, hy, hm⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hm
    have hpred := rectangle_interior_predecessor_mem hx hb j
    rw [← he, predecessor_bondTip] at hpred
    exact Finset.disjoint_left.mp hd hpred hy

/-- Overlap points lie on the local full boundary, as required for gluing. -/
lemma rectangle_overlap_mem_boundary {d : ℕ} {lo hi x : Vertex d}
    {W : Finset (Vertex d)} (hd : Disjoint (latticeRectangle lo hi) W)
    (hx : x ∈ sitesPlus (latticeRectangle lo hi)) (hw : x ∈ sitesPlus W) :
    x ∈ boundarySites (sitesPlus (latticeRectangle lo hi)) := by
  by_contra hb
  exact rectangle_interior_not_mem_other_sitesPlus hd hx hb hw

lemma sitesPlus_mono {d : ℕ} {U W : Finset (Vertex d)} (h : U ⊆ W) :
    sitesPlus U ⊆ sitesPlus W := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact base_mem_sitesPlus (h hx)
  · obtain ⟨y, hy, hm⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
    exact tip_mem_sitesPlus (h hy) j

/-- A point of a smaller support on the outer support boundary is also on the
smaller support boundary. This gives outer admissibility of glued corrections. -/
lemma boundarySites_of_subset {d : ℕ} {S T : Finset (Vertex d)}
    (h : S ⊆ T) {x : Vertex d} (hx : x ∈ S) (hb : x ∈ boundarySites T) :
    x ∈ boundarySites S := by
  classical
  obtain ⟨_, y, hy, hxy⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hx, y, (fun hs => hy (h hs)), hxy⟩

end NearCritical
