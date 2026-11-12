module

public import NearCritical.ChemicalCrossingGeometry
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Deterministic assembly step of source lem.nw.path. Local selected cluster
and bridge geometry is explicit; random offspring/survival is not constructed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Actual finite intrinsic connection with a real length bound. Reachability
prevents the toNat convention at infinity from supplying false connections. -/
def BoundedIntrinsicConnection {V : Type*} (G : SimpleGraph V) (x y : V) (A : ℝ) : Prop :=
  G.Reachable x y ∧ ((G.edist x y).toNat:ℝ) ≤ A

lemma BoundedIntrinsicConnection.exists_walk {V : Type*} {G : SimpleGraph V}
    {x y : V} {A : ℝ} (h : BoundedIntrinsicConnection G x y A) :
    ∃ w : G.Walk x y, (w.length:ℝ) ≤ A := by
  have hf := SimpleGraph.edist_ne_top_iff_reachable.mpr h.1
  obtain ⟨w,hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hf
  refine ⟨w,?_⟩
  have hnat : w.length = (G.edist x y).toNat := by
    rw [← hw]
    simp
  simpa [hnat] using h.2

/-- n bridge steps, interleaved with n+1 actual selected spanning clusters.
Every local graph lies in the same confined open graph. The random chain must
later supply these witnesses from offspring and typical-diameter properties. -/
def MicroscopicChainGeometry {V : Type*} (G : SimpleGraph V) (A B : ℝ) :
    ℕ → V → V → Prop
  | 0,x,y => ∃ C : SimpleGraph V, C ≤ G ∧ BoundedIntrinsicConnection C x y A
  | n+1,x,y => ∃ C D : SimpleGraph V, ∃ u v : V,
      C ≤ G ∧ D ≤ G ∧ BoundedIntrinsicConnection C x u A ∧
      BoundedIntrinsicConnection D u v B ∧ MicroscopicChainGeometry G A B n v y

/-- Local intrinsic bounds construct the actual concatenated open walk. -/
theorem microscopicChain_exists_walk {V : Type*} {G : SimpleGraph V} {A B : ℝ}
    {n : ℕ} {x y : V} (h : MicroscopicChainGeometry G A B n x y) :
    ∃ w : G.Walk x y, (w.length:ℝ) ≤ ((n:ℝ)+1)*A+(n:ℝ)*B := by
  induction n generalizing x with
  | zero =>
    obtain ⟨C,hCG,hC⟩ := h
    obtain ⟨w,hw⟩ := hC.exists_walk
    exact ⟨w.mapLe hCG,by simpa using hw⟩
  | succ n ih =>
    obtain ⟨C,D,u,v,hCG,hDG,hC,hD,htail⟩ := h
    obtain ⟨c,hc⟩ := hC.exists_walk
    obtain ⟨b,hb⟩ := hD.exists_walk
    obtain ⟨w,hw⟩ := ih htail
    refine ⟨(c.mapLe hCG).append ((b.mapLe hDG).append w),?_⟩
    simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_mapLe,Nat.cast_add,
      Nat.cast_one]
    nlinarith

/-- The final open exit edge is counted explicitly. Loop erasure preserves
endpoints, decreases length, and adds no unordered edge to the concatenation. -/
theorem microscopicChain_exists_path_with_exit {V : Type*} {G : SimpleGraph V}
    {A B : ℝ} {n : ℕ} {x y z : V}
    (h : MicroscopicChainGeometry G A B n x y) (hexit : G.Adj y z) :
    ∃ w : G.Walk x y, ∃ p : G.Walk x z, p.IsPath ∧
      p.edges ⊆ (w.concat hexit).edges ∧
      (w.length:ℝ) ≤ ((n:ℝ)+1)*A+(n:ℝ)*B ∧
      (p.length:ℝ) ≤ ((n:ℝ)+1)*A+(n:ℝ)*B+1 := by
  classical
  obtain ⟨w,hw⟩ := microscopicChain_exists_walk h
  let q := w.concat hexit
  refine ⟨w,q.bypass,q.bypass_isPath,?_,hw,?_⟩
  · exact q.edges_toPath_subset_edges
  · have hlen : (q.bypass.length:ℝ) ≤ q.length := by exact_mod_cast q.length_bypass_le_length
    have hq : (q.length:ℝ)=(w.length:ℝ)+1 := by simp [q]
    linarith

/-- Source coarse-route accounting: at most 2M cluster pieces and 2M bridge
pieces give the printed 2M(A+B)+1 bound, including the exit bond. -/
lemma microscopicChain_route_length_bound {n M : ℕ} {A B : ℝ}
    (hn : n+1≤2*M) (hA : 0≤A) (hB : 0≤B) :
    ((n:ℝ)+1)*A+(n:ℝ)*B+1 ≤ 2*(M:ℝ)*(A+B)+1 := by
  have hnR : (n:ℝ)+1≤2*(M:ℝ) := by exact_mod_cast hn
  nlinarith [mul_le_mul_of_nonneg_right hnR hA,
    mul_le_mul_of_nonneg_right (show (n:ℝ)≤2*(M:ℝ) by linarith) hB]

/-- Local confined chain geometry plus its actual exit edge yields the literal
source confined crossing event. The chain's probabilistic existence is not assumed proved. -/
theorem microscopicChain_crossing {d r : ℕ} (a : Vertex d) (i : Fin d)
    {ω : Configuration d} {A B K : ℝ} {n : ℕ} {x y z : Vertex d}
    (hx : x ∈ chemicalBottomFace d r i) (hz : z ∈ chemicalExitFace d r i)
    (h : MicroscopicChainGeometry
      (restrictedGraph ω (translateSites a (chemicalCrossingSupport d r i) : Set (Vertex d)))
      A B n (a+x) y)
    (hexit : (restrictedGraph ω (translateSites a (chemicalCrossingSupport d r i) :
      Set (Vertex d))).Adj y (a+z))
    (hlen : ((n:ℝ)+1)*A+(n:ℝ)*B+1≤K*(2*r+1:ℕ)) :
    ω ∈ chemicalBoxCrossingEvent a r i K := by
  obtain ⟨w,p,hp,hedges,hw,hlenp⟩ := microscopicChain_exists_path_with_exit h hexit
  exact chemicalBoxCrossingEvent_of_walk a i hx hz p (hlenp.trans hlen)

end NearCritical
