module

public import NearCritical.MicroscopicChainPath
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Edge-controlled microscopic pieces and the source sprinkling bridge.
Global chain assembly is reused from MicroscopicChainPath. Random survival,
offspring/typicality and moment estimates remain separate NEW obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Actual open lattice graph localized both by vertices and allowed unordered
edges. Bridge exclusions can be encoded literally in A. -/
def microscopicPieceGraph {d : ℕ} (ω : Configuration d) (S : Set (Vertex d))
    (A : Set (Sym2 (Vertex d))) : SimpleGraph (Vertex d) where
  Adj x y := (openGraph ω).Adj x y ∧ x ∈ S ∧ y ∈ S ∧ s(x,y) ∈ A
  symm := ⟨by
    rintro x y ⟨h, hx, hy, he⟩
    refine ⟨h.symm, hy, hx, ?_⟩
    rwa [Sym2.eq_swap]⟩
  loopless := ⟨by intro x h; exact h.1.ne rfl⟩

lemma microscopicPieceGraph_le {d : ℕ} (ω : Configuration d) (S : Set (Vertex d))
    (A : Set (Sym2 (Vertex d))) : microscopicPieceGraph ω S A ≤ openGraph ω :=
  fun _ _ h ↦ h.1

lemma microscopicWalk_support {d : ℕ} {ω : Configuration d} {S : Set (Vertex d)}
    {A : Set (Sym2 (Vertex d))} {x y : Vertex d}
    (w : (microscopicPieceGraph ω S A).Walk x y) (hx : x ∈ S) :
    ∀ z ∈ w.support, z ∈ S := by
  induction w with
  | nil => simpa using hx
  | @cons x z y h w ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hx
    · exact ih h.2.2.1 t ht

lemma microscopicWalk_edges {d : ℕ} {ω : Configuration d} {S : Set (Vertex d)}
    {A : Set (Sym2 (Vertex d))} {x y : Vertex d}
    (w : (microscopicPieceGraph ω S A).Walk x y) : ∀ e ∈ w.edges, e ∈ A := by
  induction w with
  | nil => simp
  | @cons x z y h w ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h.2.2.2
    · exact ih e he

/-- Local source geometry, stated with actual restricted connectivity and
intrinsic distance, not an assumed global path. Entry membership handles nil
pieces correctly. The region and edge set retain representative/tube provenance. -/
structure MicroscopicPiece {d : ℕ} (ω : Configuration d) (D : Set (Vertex d))
    (P : ℝ) (x y : Vertex d) where
  region : Set (Vertex d)
  allowedEdges : Set (Sym2 (Vertex d))
  region_subset : region ⊆ D
  entry_mem : x ∈ region
  connected : (microscopicPieceGraph ω region allowedEdges).Reachable x y
  distance_bound : ((microscopicPieceGraph ω region allowedEdges).dist x y : ℝ) ≤ P

namespace MicroscopicPiece
variable {d : ℕ} {ω : Configuration d} {D : Set (Vertex d)} {P : ℝ} {x y : Vertex d}

theorem exists_path (a : MicroscopicPiece ω D P x y) :
    ∃ w : (openGraph ω).Walk x y, w.IsPath ∧ (w.length : ℝ) ≤ P ∧
      (∀ z ∈ w.support, z ∈ D) ∧ (∀ e ∈ w.edges, e ∈ a.allowedEdges) := by
  obtain ⟨w, hw⟩ := a.connected.exists_walk_length_eq_dist
  let v := w.bypass.mapLe (microscopicPieceGraph_le ω a.region a.allowedEdges)
  refine ⟨v, w.bypass_isPath.mapLe _, ?_, ?_, ?_⟩
  · have hb : (w.bypass.length : ℝ) ≤ (w.length : ℝ) := by
      exact_mod_cast w.length_bypass_le_length
    simpa only [v, SimpleGraph.Walk.length_mapLe, hw] using hb.trans (by simpa [hw] using a.distance_bound)
  · intro z hz
    have hz' : z ∈ w.bypass.support := by
      simpa only [v, SimpleGraph.Walk.support_mapLe_eq_support] using hz
    exact a.region_subset (microscopicWalk_support w.bypass a.entry_mem z hz')
  · intro e he
    have he' : e ∈ w.bypass.edges := by
      simpa only [v, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact microscopicWalk_edges w.bypass e he'

def walk (a : MicroscopicPiece ω D P x y) : (openGraph ω).Walk x y := a.exists_path.choose

lemma walk_isPath (a : MicroscopicPiece ω D P x y) : a.walk.IsPath := a.exists_path.choose_spec.1
lemma walk_length (a : MicroscopicPiece ω D P x y) : (a.walk.length : ℝ) ≤ P :=
  a.exists_path.choose_spec.2.1
lemma walk_support (a : MicroscopicPiece ω D P x y) : ∀ z ∈ a.walk.support, z ∈ D :=
  a.exists_path.choose_spec.2.2.1
lemma walk_edges (a : MicroscopicPiece ω D P x y) : ∀ e ∈ a.walk.edges, e ∈ a.allowedEdges :=
  a.exists_path.choose_spec.2.2.2

end MicroscopicPiece

/-- Source2879 explored bonds: both endpoints in Q and at least one in F.
This deletes explored EDGES, while intersections with vertices of F are allowed. -/
def exploredEdgeSet {d : ℕ} (Q F : Set (Vertex d)) : Set (Sym2 (Vertex d)) :=
  {e | e ∈ Q.sym2 ∧ ∃ z ∈ e, z ∈ F}

@[simp] lemma pair_mem_exploredEdgeSet {d : ℕ} (Q F : Set (Vertex d)) (x y : Vertex d) :
    s(x,y) ∈ exploredEdgeSet Q F ↔ x ∈ Q ∧ y ∈ Q ∧ (x ∈ F ∨ y ∈ F) := by
  simp [exploredEdgeSet, Sym2.mem_iff]
  tauto

/-- The source exploration predicate in the unique positive-coordinate bond
indexing of the actual probability model. Ambient non-neighbour pairs are unused. -/
def exploredBondSet {d : ℕ} (Q F : Set (Vertex d)) : Set (Bond d) :=
  {e | s(e.1, bondTip e) ∈ exploredEdgeSet Q F}

@[simp] lemma mem_exploredBondSet {d : ℕ} (Q F : Set (Vertex d)) (e : Bond d) :
    e ∈ exploredBondSet Q F ↔ e.1 ∈ Q ∧ bondTip e ∈ Q ∧ (e.1 ∈ F ∨ bondTip e ∈ F) :=
  pair_mem_exploredEdgeSet Q F e.1 (bondTip e)

/-- A boundary-to-outside bond is not explored, even if its base belongs to F. -/
lemma outward_bond_not_explored {d : ℕ} (Q F : Set (Vertex d)) (e : Bond d)
    (hout : bondTip e ∉ Q) : e ∉ exploredBondSet Q F := by
  intro he
  exact hout ((mem_exploredBondSet Q F e).mp he).2.1

lemma open_outward_bond_retained {d : ℕ} {ω : Configuration d}
    (D Q F : Set (Vertex d)) (e : Bond d) (he : ω e = true)
    (hbase : e.1 ∈ D) (htip : bondTip e ∈ D) (hout : bondTip e ∉ Q) :
    (microscopicPieceGraph ω D (exploredEdgeSet Q F)ᶜ).Adj e.1 (bondTip e) := by
  refine ⟨⟨e, he, Or.inl ⟨rfl, rfl⟩⟩, hbase, htip, ?_⟩
  exact outward_bond_not_explored Q F e hout

/-- If a local region is disjoint from Q, none of its edges can be an explored
edge inside Q, regardless of intersections with any other vertex set. -/
lemma microscopicPieceGraph_avoid_opposite {d : ℕ} {ω : Configuration d}
    {S D Q₁ F₁ Q₂ F₂ : Set (Vertex d)} (hSD : S ⊆ D) (hdis : Disjoint S Q₂) :
    microscopicPieceGraph ω S (exploredEdgeSet Q₁ F₁)ᶜ ≤
      microscopicPieceGraph ω D (exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₂ F₂)ᶜ := by
  rintro x y ⟨hopen, hx, hy, hown⟩
  refine ⟨hopen, hSD hx, hSD hy, ?_⟩
  intro he
  rcases he with he | he
  · exact hown he
  · exact Set.disjoint_left.mp hdis hx ((pair_mem_exploredEdgeSet Q₂ F₂ x y).mp he).1

/-- The actual source intrinsic-diameter construction: two localized short
connections plus an open joining bond produce a simple bridge. Its length has
the exact +1, and no edge of either explored end cube is used. -/
theorem sprinkling_bridge_subgraphs {d : ℕ} {ω : Configuration d}
    (D L R Q₁ F₁ Q₂ F₂ : Set (Vertex d))
    (hLD : L ⊆ D) (hRD : R ⊆ D) (hLQ : Disjoint L Q₂) (hRQ : Disjoint R Q₁)
    {x a b y : Vertex d} (hx : x ∈ L) (hb : b ∈ R) {P Q : ℝ}
    {G_L G_R : SimpleGraph (Vertex d)}
    (hGL : G_L ≤ microscopicPieceGraph ω L (exploredEdgeSet Q₁ F₁)ᶜ)
    (hGR : G_R ≤ microscopicPieceGraph ω R (exploredEdgeSet Q₂ F₂)ᶜ)
    (hleft : BoundedIntrinsicConnection G_L x a P)
    (hright : BoundedIntrinsicConnection G_R b y Q)
    (hpivot : (openGraph ω).Adj a b) :
    ∃ w : (openGraph ω).Walk x y, w.IsPath ∧ (w.length : ℝ) ≤ P+1+Q ∧
      (∀ z ∈ w.support, z ∈ D) ∧
      (∀ e ∈ w.edges, e ∉ exploredEdgeSet Q₁ F₁ ∧ e ∉ exploredEdgeSet Q₂ F₂) ∧
      (∀ e ∈ w.edges, e ∈ G_L.edgeSet ∨ e = s(a,b) ∨ e ∈ G_R.edgeSet) := by
  let H := microscopicPieceGraph ω D (exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₂ F₂)ᶜ
  obtain ⟨wl, hwl⟩ := hleft.exists_walk
  obtain ⟨wr, hwr⟩ := hright.exists_walk
  have ha : a ∈ L := microscopicWalk_support (wl.mapLe hGL) hx a (by simp)
  have hl : G_L ≤ H := hGL.trans (microscopicPieceGraph_avoid_opposite hLD hLQ)
  have hr : G_R ≤ H := by
    have hh := microscopicPieceGraph_avoid_opposite (ω := ω)
      (Q₁ := Q₂) (F₁ := F₂) (Q₂ := Q₁) (F₂ := F₁) hRD hRQ
    exact hGR.trans (by simpa only [Set.union_comm] using hh)
  have hp : H.Adj a b := by
    refine ⟨hpivot, hLD ha, hRD hb, ?_⟩
    intro he
    rcases he with he | he
    · exact Set.disjoint_left.mp hRQ hb ((pair_mem_exploredEdgeSet Q₁ F₁ a b).mp he).2.1
    · exact Set.disjoint_left.mp hLQ ha ((pair_mem_exploredEdgeSet Q₂ F₂ a b).mp he).1
  let raw : H.Walk x y := ((wl.mapLe hl).concat hp).append (wr.mapLe hr)
  let v := raw.bypass
  let w := v.mapLe (microscopicPieceGraph_le ω D _)
  refine ⟨w, raw.bypass_isPath.mapLe _, ?_, ?_, ?_, ?_⟩
  · have hlen : (v.length : ℝ) ≤ (raw.length : ℝ) := by exact_mod_cast raw.length_bypass_le_length
    have hrlen : (raw.length : ℝ) = (wl.length : ℝ)+1+(wr.length : ℝ) := by
      simp [raw]
    have hwlen : w.length = v.length := SimpleGraph.Walk.length_mapLe _ _
    rw [hwlen]
    linarith
  · intro z hz
    have hz' : z ∈ v.support := by simpa only [w, SimpleGraph.Walk.support_mapLe_eq_support] using hz
    exact microscopicWalk_support v (hLD hx) z hz'
  · intro e he
    have he' : e ∈ v.edges := by simpa only [w, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    have hnot := microscopicWalk_edges v e he'
    exact ⟨fun h ↦ hnot (Or.inl h), fun h ↦ hnot (Or.inr h)⟩

  · intro e he
    have he' : e ∈ v.edges := by simpa only [w, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    have heraw := raw.edges_bypass_subset_edges he'
    simp only [raw, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_concat,
      SimpleGraph.Walk.edges_mapLe_eq_edges, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at heraw
    rcases heraw with (heL | heP) | heR
    · exact Or.inl (wl.edges_subset_edgeSet heL)
    · exact Or.inr (Or.inl heP)
    · exact Or.inr (Or.inr (wr.edges_subset_edgeSet heR))

/-- The actual source intrinsic-diameter construction: two localized short
connections plus an open joining bond produce a simple bridge. Its length has
the exact +1, and no edge of either explored end cube is used. -/
theorem sprinkling_bridge_path {d : ℕ} {ω : Configuration d}
    (D L R Q₁ F₁ Q₂ F₂ : Set (Vertex d))
    (hLD : L ⊆ D) (hRD : R ⊆ D) (hLQ : Disjoint L Q₂) (hRQ : Disjoint R Q₁)
    {x a b y : Vertex d} (hx : x ∈ L) (hb : b ∈ R) {P Q : ℝ}
    (hleft : BoundedIntrinsicConnection
      (microscopicPieceGraph ω L (exploredEdgeSet Q₁ F₁)ᶜ) x a P)
    (hright : BoundedIntrinsicConnection
      (microscopicPieceGraph ω R (exploredEdgeSet Q₂ F₂)ᶜ) b y Q)
    (hpivot : (openGraph ω).Adj a b) :
    ∃ w : (openGraph ω).Walk x y, w.IsPath ∧ (w.length : ℝ) ≤ P+1+Q ∧
      (∀ z ∈ w.support, z ∈ D) ∧
      (∀ e ∈ w.edges, e ∉ exploredEdgeSet Q₁ F₁ ∧ e ∉ exploredEdgeSet Q₂ F₂) := by
  obtain ⟨w, hp, hl, hs, he, _⟩ := sprinkling_bridge_subgraphs D L R Q₁ F₁ Q₂ F₂
    hLD hRD hLQ hRQ hx hb le_rfl le_rfl hleft hright hpivot
  exact ⟨w, hp, hl, hs, he⟩

/-- The literal edge union of the supplied two side graphs and joining bond.
Supplying critical-cluster subgraphs preserves their identity, rather than
allowing an unrelated full-p path inside the tube. -/
def sprinklingBridgeGraph {d : ℕ} (G_L G_R : SimpleGraph (Vertex d)) (a b : Vertex d) :
    SimpleGraph (Vertex d) :=
  SimpleGraph.fromEdgeSet (G_L.edgeSet ∪ ({s(a,b)} ∪ G_R.edgeSet))

lemma sprinklingBridgeGraph_le {d : ℕ} {G_L G_R H : SimpleGraph (Vertex d)}
    {a b : Vertex d} (hL : G_L ≤ H) (hR : G_R ≤ H) (hp : H.Adj a b) :
    sprinklingBridgeGraph G_L G_R a b ≤ H := by
  rw [sprinklingBridgeGraph, SimpleGraph.fromEdgeSet_le]
  intro e he
  rcases he.1 with heL | heP | heR
  · exact SimpleGraph.edgeSet_mono hL heL
  · have heq : e = s(a,b) := heP
    subst e
    exact hp
  · exact SimpleGraph.edgeSet_mono hR heR

/-- The entire supplied bridge graph, not only one selected path, avoids both
explored sets. Therefore later shortest-path choices cannot lose the exclusion. -/
theorem sprinklingBridgeGraph_le_deleted {d : ℕ} {ω : Configuration d}
    (D L R Q₁ F₁ Q₂ F₂ : Set (Vertex d))
    (hLD : L ⊆ D) (hRD : R ⊆ D) (hLQ : Disjoint L Q₂) (hRQ : Disjoint R Q₁)
    {G_L G_R : SimpleGraph (Vertex d)}
    (hGL : G_L ≤ microscopicPieceGraph ω L (exploredEdgeSet Q₁ F₁)ᶜ)
    (hGR : G_R ≤ microscopicPieceGraph ω R (exploredEdgeSet Q₂ F₂)ᶜ)
    {x a b : Vertex d} (hx : x ∈ L) (hb : b ∈ R) (hconn : G_L.Reachable x a)
    (hpivot : (openGraph ω).Adj a b) :
    sprinklingBridgeGraph G_L G_R a b ≤
      microscopicPieceGraph ω D (exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₂ F₂)ᶜ := by
  obtain ⟨wl⟩ := hconn
  have ha : a ∈ L := microscopicWalk_support (wl.mapLe hGL) hx a (by simp)
  have hL := hGL.trans (microscopicPieceGraph_avoid_opposite (F₂ := F₂) hLD hLQ)
  have hR := hGR.trans (microscopicPieceGraph_avoid_opposite (ω := ω)
    (Q₁ := Q₂) (F₁ := F₂) (Q₂ := Q₁) (F₂ := F₁) hRD hRQ)
  apply sprinklingBridgeGraph_le hL
    (by simpa only [Set.union_comm] using hR)
  refine ⟨hpivot, hLD ha, hRD hb, ?_⟩
  intro he
  rcases he with he | he
  · exact Set.disjoint_left.mp hRQ hb ((pair_mem_exploredEdgeSet Q₁ F₁ a b).mp he).2.1
  · exact Set.disjoint_left.mp hLQ ha ((pair_mem_exploredEdgeSet Q₂ F₂ a b).mp he).1

lemma microscopicPieceGraph_le_restricted {d : ℕ} (ω : Configuration d)
    (D : Set (Vertex d)) (A : Set (Sym2 (Vertex d))) :
    microscopicPieceGraph ω D A ≤ restrictedGraph ω D := by
  rintro x y ⟨h, hx, hy, _⟩
  exact ⟨h, hx, hy⟩

/-- Construct the exact short bridge witness consumed by MicroscopicChainGeometry.
Neither a joined path nor its bounded connection is assumed as an input. -/
theorem sprinkling_bridge_bounded_connection {d : ℕ} {ω : Configuration d}
    (D L R Q₁ F₁ Q₂ F₂ : Set (Vertex d))
    (hLD : L ⊆ D) (hRD : R ⊆ D) (hLQ : Disjoint L Q₂) (hRQ : Disjoint R Q₁)
    {x a b y : Vertex d} (hx : x ∈ L) (hb : b ∈ R) {P Q : ℝ}
    {G_L G_R : SimpleGraph (Vertex d)}
    (hGL : G_L ≤ microscopicPieceGraph ω L (exploredEdgeSet Q₁ F₁)ᶜ)
    (hGR : G_R ≤ microscopicPieceGraph ω R (exploredEdgeSet Q₂ F₂)ᶜ)
    (hleft : BoundedIntrinsicConnection G_L x a P)
    (hright : BoundedIntrinsicConnection G_R b y Q) (hpivot : (openGraph ω).Adj a b) :
    BoundedIntrinsicConnection (sprinklingBridgeGraph G_L G_R a b) x y (P+1+Q) := by
  obtain ⟨w, _, hlen, _, _, hprov⟩ := sprinkling_bridge_subgraphs D L R Q₁ F₁ Q₂ F₂
    hLD hRD hLQ hRQ hx hb hGL hGR hleft hright hpivot
  let B := sprinklingBridgeGraph G_L G_R a b
  have heB : ∀ e ∈ w.edges, e ∈ B.edgeSet := by
    intro e he
    change e ∈ (SimpleGraph.fromEdgeSet (G_L.edgeSet ∪ ({s(a,b)} ∪ G_R.edgeSet))).edgeSet
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨?_, (openGraph ω).not_isDiag_of_mem_edgeSet (w.edges_subset_edgeSet he)⟩
    rcases hprov e he with heL | heP | heR
    · exact Or.inl heL
    · exact Or.inr (Or.inl heP)
    · exact Or.inr (Or.inr heR)
  let v := w.transfer B heB
  refine ⟨⟨v⟩, ?_⟩
  have hd : ((B.dist x y : ℕ) : ℝ) ≤ (v.length : ℝ) := by
    exact_mod_cast SimpleGraph.dist_le v
  have hv : (v.length : ℝ) ≤ P+1+Q := by
    simpa only [v, SimpleGraph.Walk.length_transfer] using hlen
  exact hd.trans hv

/-- Literal first/third end cubes in the source's (Q,S,H,T) structure. -/
def sprinklingEndCube {d : ℕ} (i : Fin d) (n center : ℝ) : Set (Vertex d) :=
  {x | ∀ j, -n/2 < (x j : ℝ) - (if j=i then center else 0) ∧
    (x j : ℝ) - (if j=i then center else 0) < n/2}

def sprinklingTube {d : ℕ} (i : Fin d) (n : ℝ) (lo hi : ℝ) : Set (Vertex d) :=
  {x | n+lo*n < (x i : ℝ) ∧ (x i : ℝ) < n+hi*n ∧
    ∀ j, j ≠ i → -3*n/8 < (x j : ℝ) ∧ (x j : ℝ) < 3*n/8}

lemma sprinklingLeftTube_subset {d : ℕ} (i : Fin d) {n : ℝ} (hn : 0 < n) :
    sprinklingTube i n (-(5:ℝ)/8) (3/8) ⊆ sprinklingTube i n (-(5:ℝ)/8) (5/8) := by
  rintro x ⟨hl, hu, ht⟩
  exact ⟨hl, lt_of_lt_of_le hu (by linarith), ht⟩

lemma sprinklingRightTube_subset {d : ℕ} (i : Fin d) {n : ℝ} (hn : 0 < n) :
    sprinklingTube i n (-(3:ℝ)/8) (5/8) ⊆ sprinklingTube i n (-(5:ℝ)/8) (5/8) := by
  rintro x ⟨hl, hu, ht⟩
  exact ⟨lt_of_le_of_lt (by linarith) hl, hu, ht⟩

lemma sprinklingLeftTube_disjoint_third {d : ℕ} (i : Fin d) {n : ℝ} (hn : 0 < n) :
    Disjoint (sprinklingTube i n (-(5:ℝ)/8) (3/8)) (sprinklingEndCube i n (2*n)) := by
  apply Set.disjoint_left.mpr
  intro x hx hq
  have hheight := (hq i).1
  simp only [ite_true] at hheight
  have hu := hx.2.1
  linarith

lemma sprinklingRightTube_disjoint_first {d : ℕ} (i : Fin d) {n : ℝ} (hn : 0 < n) :
    Disjoint (sprinklingTube i n (-(3:ℝ)/8) (5/8)) (sprinklingEndCube i n 0) := by
  apply Set.disjoint_left.mpr
  intro x hx hq
  have hheight := (hq i).2
  simp only [ite_true, sub_zero] at hheight
  have hl := hx.1
  linarith

/-- Specialization to the literal T12,T23,T123,Q1,Q3 source geometry. Opposite
cube avoidance and both explored-edge exclusions are proved, not premises. -/
theorem sprinkling_tube_bridge_path {d : ℕ} {ω : Configuration d} (i : Fin d)
    {n : ℝ} (hn : 0 < n) (F₁ F₃ : Set (Vertex d)) {x a b y : Vertex d}
    (hx : x ∈ sprinklingTube i n (-(5:ℝ)/8) (3/8))
    (hb : b ∈ sprinklingTube i n (-(3:ℝ)/8) (5/8)) {P Q : ℝ}
    (hleft : BoundedIntrinsicConnection
      (microscopicPieceGraph ω (sprinklingTube i n (-(5:ℝ)/8) (3/8))
        (exploredEdgeSet (sprinklingEndCube i n 0) F₁)ᶜ) x a P)
    (hright : BoundedIntrinsicConnection
      (microscopicPieceGraph ω (sprinklingTube i n (-(3:ℝ)/8) (5/8))
        (exploredEdgeSet (sprinklingEndCube i n (2*n)) F₃)ᶜ) b y Q)
    (hpivot : (openGraph ω).Adj a b) :
    ∃ w : (openGraph ω).Walk x y, w.IsPath ∧ (w.length : ℝ) ≤ P+1+Q ∧
      (∀ z ∈ w.support, z ∈ sprinklingTube i n (-(5:ℝ)/8) (5/8)) ∧
      (∀ e ∈ w.edges,
        e ∉ exploredEdgeSet (sprinklingEndCube i n 0) F₁ ∧
        e ∉ exploredEdgeSet (sprinklingEndCube i n (2*n)) F₃) :=
  sprinkling_bridge_path _ _ _ _ _ _ _
    (sprinklingLeftTube_subset i hn) (sprinklingRightTube_subset i hn)
    (sprinklingLeftTube_disjoint_third i hn) (sprinklingRightTube_disjoint_first i hn)
    hx hb hleft hright hpivot

end NearCritical
