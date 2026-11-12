module

public import NearCritical.NestChainPath
public import NearCritical.FiniteClusterMetric

/-! Section9, eq.def.C12_23 and eq.def.piv_AB. Components delete explored
EDGES, allowing explored vertices. Candidate pairs are oriented; both physical
orientations are represented by the finite candidate set. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset
open scoped Classical

/-- The actual tube graph after deleting the revealed bonds of one heart union. -/
def sprinklingUnexploredGraph {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) : SimpleGraph (Vertex d) :=
  microscopicPieceGraph ω (T : Set (Vertex d))
    (exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)))ᶜ

/-- Literal finite C12/C23: only tube vertices are retained, even for an
outside root with a reflexive ambient graph path. -/
def sprinklingUnexploredCluster {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (root : Vertex d) : Finset (Vertex d) :=
  T.filter (fun y => (sprinklingUnexploredGraph ω T Q F).Reachable root y)

lemma mem_sprinklingUnexploredCluster {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (root y : Vertex d) :
    y ∈ sprinklingUnexploredCluster ω T Q F root ↔
      y ∈ T ∧ (sprinklingUnexploredGraph ω T Q F).Reachable root y := by
  simp only [sprinklingUnexploredCluster,Finset.mem_filter]

lemma root_mem_sprinklingUnexploredCluster {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) {root : Vertex d} (hroot : root ∈ T) :
    root ∈ sprinklingUnexploredCluster ω T Q F root :=
  (mem_sprinklingUnexploredCluster ω T Q F root root).mpr ⟨hroot,.refl root⟩

lemma sprinklingUnexploredCluster_subset {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (root : Vertex d) :
    sprinklingUnexploredCluster ω T Q F root ⊆ T := by
  intro y hy
  exact ((mem_sprinklingUnexploredCluster ω T Q F root y).mp hy).1

/-- Source oriented pivotal candidate. Root-domain guards match candidates
inside the common tube segment; geometric adjacency excludes non-bond pairs. -/
def sprinklingPivotalPair {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) : Prop :=
  (openGraph (fun _ : Bond d => true)).Adj e.1 e.2 ∧ e.1 ∈ L ∧ e.2 ∈ R ∧
    (sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∩ A).Nonempty ∧
    (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩ B).Nonempty ∧
    Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)

def sprinklingPivotalPairs {d : ℕ} (ω : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    Finset (Vertex d × Vertex d) :=
  E.filter (sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B)

/-- Source pivo: critical pivotal pairs whose joining edge is open in the
sprinkled configuration. Openness is checked on the actual physical edge. -/
def sprinkledPivotalPairs {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    Finset (Vertex d × Vertex d) :=
  (sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A B).filter
    (fun e => (openGraph η).Adj e.1 e.2)

/-- Opening an AVAILABLE joining edge merges the two alleged disjoint
components. Availability is a geometry fact, not an automatic consequence
of using two different deleted-edge graphs. -/
theorem sprinklingPivotalPair_not_open {d : ℕ} {ω : Configuration d}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) {e : Vertex d × Vertex d}
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e)
    (hother : e.2 ∈ L)
    (havailable : s(e.1,e.2) ∉ exploredEdgeSet (Q₁ : Set (Vertex d)) (F₁ : Set (Vertex d))) :
    ¬ (openGraph ω).Adj e.1 e.2 := by
  intro hopen
  have hleft : e.2 ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 := by
    apply (mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 e.2).mpr
    refine ⟨hother,?_⟩
    have hadj : (sprinklingUnexploredGraph ω L Q₁ F₁).Adj e.1 e.2 :=
      ⟨hopen,he.2.1,hother,havailable⟩
    exact hadj.reachable
  have hright := root_mem_sprinklingUnexploredCluster ω R Q₃ F₃ he.2.2.1
  exact Finset.disjoint_left.mp he.2.2.2.2.2 hleft hright

/-- Positive-coordinate representation of either physical orientation is
closed in the critical field, under the same explicit availability geometry. -/
theorem sprinklingPivotalPair_bond_closed {d : ℕ} {ω : Configuration d}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) {e : Vertex d × Vertex d}
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e)
    (hother : e.2 ∈ L)
    (havailable : s(e.1,e.2) ∉ exploredEdgeSet (Q₁ : Set (Vertex d)) (F₁ : Set (Vertex d)))
    (b : Bond d)
    (hends : (e.1 = b.1 ∧ e.2 = bondTip b) ∨ (e.2 = b.1 ∧ e.1 = bondTip b)) :
    ω b = false := by
  have hnot := sprinklingPivotalPair_not_open L R Q₁ F₁ Q₃ F₃ A B he hother havailable
  cases hb : ω b
  · rfl
  · exact (hnot ⟨b,hb,hends⟩).elim

end NearCritical
