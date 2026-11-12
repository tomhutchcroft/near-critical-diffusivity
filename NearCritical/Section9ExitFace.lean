module

public import NearCritical.Section9ClusterEntry
public import NearCritical.Section9FiniteGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact positive exit face from source main.tex4064. Entry boundary is used
only as an intermediate existing object; the final path hits the source face. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Source partial-ex T12: vertices whose positive axial neighbor leaves T12. -/
def section9ExitFace {d : ℕ} (i : Fin d) (n : ℕ) : Finset (Vertex d) :=
  (section9FiniteTube i n (-(5:ℝ)/8) (3/8)).filter fun v =>
    bondTip (v,i) ∉ section9FiniteTube i n (-(5:ℝ)/8) (3/8)

/-- Transverse widths of the tubes agree, so an entry into T12 from T23 can
only cross its positive axial boundary. This inclusion holds even at small n. -/
theorem section9_entryBoundary_subset_exitFace {d : ℕ} (i : Fin d) (n : ℕ) :
    innerEntryBoundary (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
      (section9FiniteTube i n (-(5:ℝ)/8) (3/8)) ⊆ section9ExitFace i n := by
  intro v hv
  obtain ⟨hvL,u,huR,huL,huv⟩ := Finset.mem_filter.mp hv
  have huRshape := (Finset.mem_filter.mp huR).2
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have huNotShape : u ∉ sprinklingTube i n (-(5:ℝ)/8) (3/8) := by
    intro huShape
    apply huL
    exact (mem_section9FiniteTube i n _ _ (by norm_num) (by norm_num) u).mpr huShape
  have huHigh : (n:ℝ)+(3/8)*(n:ℝ) ≤ (u i:ℝ) := by
    apply le_of_not_gt
    intro huUpper
    apply huNotShape
    refine ⟨?_,huUpper,huRshape.2.2⟩
    have hl := huRshape.1
    linarith
  have hstep : (u i:ℝ) ≤ (v i:ℝ)+1 := by
    exact_mod_cast (openGraph_adj_height_bounds huv i).1
  apply Finset.mem_filter.mpr
  refine ⟨hvL,?_⟩
  intro hvNext
  have hupper := (Finset.mem_filter.mp hvNext).2.2.1
  simp only [bondTip, Function.update_self, Int.cast_add, Int.cast_one] at hupper
  linarith

/-- The actual right-tube path can meet the actual revealed left component
only through the source exit face. This is a deterministic reachability fact. -/
theorem section9_rightPath_hits_cluster_exit {d : ℕ} {ω : Configuration d}
    (i : Fin d) {n : ℕ} (hn : 0 < n) (F₁ F₃ : Finset (Vertex d))
    (root : Vertex d) {x y : Vertex d}
    (hx : x ∉ sprinklingUnexploredCluster ω
      (section9FiniteTube i n (-(5:ℝ)/8) (3/8)) (section9FiniteEndCube i n 0) F₁ root)
    (hy : y ∈ sprinklingUnexploredCluster ω
      (section9FiniteTube i n (-(5:ℝ)/8) (3/8)) (section9FiniteEndCube i n 0) F₁ root)
    (hxy : (sprinklingUnexploredGraph ω (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
      (section9FiniteEndCube i n (2*(n:ℝ))) F₃).Reachable x y) :
    ∃ v ∈ section9ExitFace i n ∩ sprinklingUnexploredCluster ω
      (section9FiniteTube i n (-(5:ℝ)/8) (3/8)) (section9FiniteEndCube i n 0) F₁ root,
      (sprinklingUnexploredGraph ω (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
        (section9FiniteEndCube i n (2*(n:ℝ))) F₃).Reachable x v := by
  obtain ⟨v,hv,hpath⟩ := sprinklingCluster_path_hits_entry _ _ _ _ _ _
    (section9FiniteRightTube_disjoint_first i hn) root hx hy hxy
  obtain ⟨hvBoundary,hvCluster⟩ := Finset.mem_inter.mp hv
  exact ⟨v,Finset.mem_inter.mpr
    ⟨section9_entryBoundary_subset_exitFace i n hvBoundary,hvCluster⟩,hpath⟩

end NearCritical
