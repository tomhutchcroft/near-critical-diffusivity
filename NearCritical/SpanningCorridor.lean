module

public import NearCritical.PreGoodUpperCount
public import NearCritical.HalfSpaceLastVisit

/-! NEW lem.arm.2dspanning: actual corridor connections imply simultaneous
spanning via first-exit paths inside the cube. No crossing probability or
scaling-limit conclusion is supplied or asserted here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Exit from a finite vertex domain has a reachable last inside vertex.
The prefix connectivity is in the INSIDE restricted graph, not the corridor. -/
lemma restricted_walk_first_exit {d : ℕ} {ω : Configuration d}
    (C : Finset (Vertex d)) (D : Set (Vertex d)) {x y : Vertex d}
    (w : (restrictedGraph ω D).Walk x y) (hx : x ∈ C) (hy : y ∉ C) :
    ∃ z ∈ C, ∃ u ∈ D, u ∉ C ∧ (openGraph ω).Adj z u ∧
      (restrictedGraph ω (C : Set (Vertex d))).Reachable x z := by
  revert hx hy
  induction w with
  | nil =>
    intro hx hy
    exact (hy hx).elim
  | @cons a b c hab w ih =>
    intro hx hy
    by_cases hb : b ∈ C
    · obtain ⟨z,hz,u,hu,huout,hzu,hbz⟩ := ih hb hy
      refine ⟨z,hz,u,hu,huout,hzu,?_⟩
      exact (show (restrictedGraph ω (C : Set (Vertex d))).Reachable a b from
        ⟨SimpleGraph.Walk.cons ⟨hab.1,hx,hb⟩ SimpleGraph.Walk.nil⟩).trans hbz
    · exact ⟨a,hx,b,hab.2.2,hb,hab.1,.refl a⟩

/-- A coarse signed corridor containing the paper's narrower cuboid: all
transverse coordinates stay in the cube, and only the selected face can be
crossed outward. The positive sign is true, matching signedCubeFace. -/
def spanningCorridor {d : ℕ} (R : ℕ) (f : Fin d × Bool) : Set (Vertex d) :=
  {z | (if f.2 then -(R:ℤ) ≤ z f.1 else z f.1 ≤ (R:ℤ)) ∧
    ∀ j, j ≠ f.1 → |z j| ≤ (R:ℤ)}

def spanningCorridorTarget {d : ℕ} (R : ℕ) (f : Fin d × Bool) : Set (Vertex d) :=
  {z | if f.2 then (R:ℤ) < z f.1 else z f.1 < -(R:ℤ)}

/-- Any actual signed-corridor connection beyond its face yields a face
vertex in the ACTUAL finite-box cluster. Both orientations are retained. -/
theorem spanningCorridor_connection_hits_face {d R : ℕ} (f : Fin d × Bool)
    (x : Vertex d) (hx : x ∈ centeredBox d R) (ω : Configuration d)
    (hconn : ω ∈ connectionToSetEvent (spanningCorridor R f) x (spanningCorridorTarget R f)) :
    (finiteBoxCluster ω (centeredBox d R) x ∩ signedCubeFace d R f).Nonempty := by
  obtain ⟨_hxD,y,hyfar,_hyD,⟨w⟩⟩ := hconn
  have hyout : y ∉ centeredBox d R := by
    intro hy
    have hb := mem_centeredBox.mp hy f.1
    rcases f with ⟨i,s⟩
    cases s <;> simp_all [spanningCorridorTarget]
    <;> omega
  obtain ⟨z,hz,u,hu,huout,hzu,hxz⟩ :=
    restricted_walk_first_exit (centeredBox d R) (spanningCorridor R f) w hx hyout
  have hiout : ¬ (-(R:ℤ) ≤ u f.1 ∧ u f.1 ≤ (R:ℤ)) := by
    intro hi
    apply huout
    apply mem_centeredBox.mpr
    intro j
    by_cases hj : j = f.1
    · simpa only [hj] using hi
    · exact abs_le.mp (hu.2 j hj)
  have hface : z f.1 = if f.2 then (R:ℤ) else -(R:ℤ) := by
    have hb := mem_centeredBox.mp hz f.1
    have hstep := openGraph_adj_height_bounds hzu f.1
    have hside := hu.1
    rcases f with ⟨i,s⟩
    cases s <;> simp_all [spanningCorridor]
    <;> omega
  refine ⟨z,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
  · exact (mem_finiteBoxCluster ω (centeredBox d R) x z).mpr ⟨hz,hxz⟩
  · exact Finset.mem_filter.mpr ⟨hz,hface⟩

/-- The source intersection of signed corridor events is a subset of the
actual simultaneous-spanning event; no probabilistic assumption is used. -/
theorem all_spanningCorridors_subset_spanning {d R : ℕ}
    (x : Vertex d) (hx : x ∈ centeredBox d R) :
    {ω : Configuration d | ∀ f : Fin d × Bool,
      ω ∈ connectionToSetEvent (spanningCorridor R f) x (spanningCorridorTarget R f)} ⊆
        finiteRootSpanningEvent (centeredBox d R) (signedCubeFace d R) x := by
  intro ω hω f
  exact spanningCorridor_connection_hits_face f x hx ω (hω f)

end NearCritical
