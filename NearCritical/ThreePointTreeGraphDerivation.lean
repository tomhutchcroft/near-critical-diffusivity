module

public import NearCritical.Section9RestrictedTripod
public import NearCritical.ConnectionToSet
public import NearCritical.BulkSupercriticalBound
public import NearCritical.ThreePointDiagram

/-! # Derivation of the BK tree-graph input

The three-point BK tree-graph inequality
`P[x↔y, x↔z] ≤ ∑_u τ(u,x) τ(u,y) τ(u,z)` is often stated in the literature as a
"standard input".  It is, however, an honest *theorem*, and this module proves it
from pieces already in the project, with **no tree-graph premise**:

* the branch-point tripod decomposition `restricted_connection_tripod_occurrence`
  (a pair of connections on a domain yields a branch vertex with three
  edge-disjoint legs), which is combinatorial and unconditional; and
* increasing-event BK on the full percolation measure `percolation_bk`
  (standard-axiom-audited; connection events are increasing, so Reimer's general
  inequality is *not* needed).

The finite-domain bound `restricted_tripod_connection_probability_le` is entirely
unconditional.  The infinite-volume form `threePointTree_of_summable` is conditional
only on summability of the right-hand side.  That summability is in turn supplied by
the spatial bubble input already assumed everywhere the tree bound is used (the
third two-point factor is a probability, hence `≤ 1`), so
`threePointTreeGraphInput_of_bubble` discharges `ThreePointTreeGraphInput d` from
`CriticalSpatialBubbleInput d B` with nothing further cited.  The BK tree-graph
input is therefore not an independent axiom. -/

@[expose] public section
noncomputable section
namespace NearCritical

open MeasureTheory
open scoped Classical BigOperators

/-- Three-occurrence BK product bound for the nested tripod occurrence, on the
full percolation measure.  Unconditional: only increasing-event BK. -/
theorem tripod_occurrence_probability_le {d : ℕ} (p : unitInterval)
    (A B C : Set (Configuration d))
    (hA : BK.Increasing A) (hB : BK.Increasing B) (hC : BK.Increasing C) :
    (percolation d p).real
      {ω | DisjointOccurrence A {θ | DisjointOccurrence B C θ} ω} ≤
      (percolation d p).real A * (percolation d p).real B * (percolation d p).real C := by
  calc
    _ ≤ (percolation d p).real A *
        (percolation d p).real {θ | DisjointOccurrence B C θ} :=
      percolation_bk d p A _ hA (increasing_disjointOccurrence hB hC)
    _ ≤ (percolation d p).real A *
        ((percolation d p).real B * (percolation d p).real C) :=
      mul_le_mul_of_nonneg_left (percolation_bk d p B C hB hC) measureReal_nonneg
    _ = _ := by ring

/-- Finite-domain three-point tree-graph probability bound, proven from the
branch-point tripod decomposition and increasing BK.  No tree-graph premise. -/
theorem restricted_tripod_connection_probability_le {d : ℕ} (p : unitInterval)
    (R : Finset (Vertex d)) (a b z : Vertex d) :
    let D := (R : Set (Vertex d))
    let P := fun x y => (percolation d p).real (connectionToSetEvent D x {y})
    (percolation d p).real
      (connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {z}) ≤
      ∑ u ∈ R, P a u * P u b * P z u := by
  intro D P
  let F := ⋃ u ∈ R, {ω : Configuration d | DisjointOccurrence (connectionToSetEvent D a {u})
      {θ | DisjointOccurrence (connectionToSetEvent D u {b}) (connectionToSetEvent D z {u}) θ} ω}
  have hsub : (connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {z}) ⊆ F := by
    rintro ω ⟨⟨ha, b', hb', _, hab⟩, ⟨_, z', hz', _, haz⟩⟩
    obtain rfl : b' = b := hb'
    obtain rfl : z' = z := hz'
    obtain ⟨u, hu, hocc⟩ := restricted_connection_tripod_occurrence D ha hab haz
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, hocc⟩⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le R _).trans ?_
  apply Finset.sum_le_sum
  intro u _
  exact tripod_occurrence_probability_le p _ _ _
    (connectionToSetEvent_increasing _ _ _)
    (connectionToSetEvent_increasing _ _ _)
    (connectionToSetEvent_increasing _ _ _)

/-- A restricted-domain connection to a singleton is an unrestricted connection. -/
lemma connectionToSetEvent_singleton_subset {d : ℕ} (S : Set (Vertex d)) (x y : Vertex d) :
    connectionToSetEvent S x {y} ⊆ connectionEvent x y := by
  rintro ω ⟨hx, w, rfl, hwS, hreach⟩
  exact SimpleGraph.Reachable.mono (by rintro u v ⟨h, _, _⟩; exact h) hreach

/-- An open walk whose support lies in `R` is a connection restricted to `R`. -/
lemma reachable_restricted_of_walk {d : ℕ} {ω : Configuration d} {x y : Vertex d}
    (w : (openGraph ω).Walk x y) {R : Finset (Vertex d)}
    (hsub : w.support.toFinset ⊆ R) :
    (restrictedGraph ω (↑R : Set (Vertex d))).Reachable x y := by
  refine ⟨w.transfer (restrictedGraph ω (↑R : Set (Vertex d)))
    (fun e => Sym2.ind (fun u v he => ?_) e)⟩
  rw [SimpleGraph.mem_edgeSet]
  have hadj : (openGraph ω).Adj u v := by
    have h := w.edges_subset_edgeSet he
    rwa [SimpleGraph.mem_edgeSet] at h
  refine ⟨hadj, ?_, ?_⟩
  · exact Finset.mem_coe.mpr (hsub (List.mem_toFinset.mpr (w.fst_mem_support_of_mem_edges he)))
  · exact Finset.mem_coe.mpr (hsub (List.mem_toFinset.mpr (w.snd_mem_support_of_mem_edges he)))

lemma twoPoint_comm {d : ℕ} (p : unitInterval) (a b : Vertex d) :
    twoPoint d p a b = twoPoint d p b a := by
  unfold twoPoint connectionEvent
  congr 1
  exact Set.ext (fun ω => ⟨fun h => h.symm, fun h => h.symm⟩)

/-- The infinite-volume three-point tree-graph bound, conditional ONLY on
summability of the right-hand side.  No tree-graph inequality is assumed; it is
derived from the branch-point tripod decomposition and increasing-event BK. -/
theorem threePointTree_of_summable {d : ℕ} (p : unitInterval)
    (hsum : ∀ x y z : Vertex d,
      Summable (fun u => twoPoint d p u x * twoPoint d p u y * twoPoint d p u z))
    (x y z : Vertex d) :
    (percolation d p).real (connectionEvent x y ∩ connectionEvent x z) ≤
      ∑' u, twoPoint d p u x * twoPoint d p u y * twoPoint d p u z := by
  set C := ∑' u, twoPoint d p u x * twoPoint d p u y * twoPoint d p u z with hCdef
  have hterm : ∀ u, 0 ≤ twoPoint d p u x * twoPoint d p u y * twoPoint d p u z := fun u =>
    mul_nonneg (mul_nonneg (twoPoint_nonneg p u x) (twoPoint_nonneg p u y)) (twoPoint_nonneg p u z)
  have hC_nonneg : 0 ≤ C := tsum_nonneg hterm
  let E : Finset (Vertex d) → Set (Configuration d) := fun R =>
    connectionToSetEvent (↑R) x {y} ∩ connectionToSetEvent (↑R) x {z}
  have hdir : Directed (· ⊆ ·) E := by
    intro R S
    refine ⟨R ∪ S, ?_, ?_⟩
    · exact Set.inter_subset_inter
        (connectionToSetEvent_mono (by exact_mod_cast Finset.subset_union_left) le_rfl x)
        (connectionToSetEvent_mono (by exact_mod_cast Finset.subset_union_left) le_rfl x)
    · exact Set.inter_subset_inter
        (connectionToSetEvent_mono (by exact_mod_cast Finset.subset_union_right) le_rfl x)
        (connectionToSetEvent_mono (by exact_mod_cast Finset.subset_union_right) le_rfl x)
  have hunion : (⋃ R, E R) = connectionEvent x y ∩ connectionEvent x z := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun R => Set.inter_subset_inter
        (connectionToSetEvent_singleton_subset _ _ _)
        (connectionToSetEvent_singleton_subset _ _ _))
    · rintro ω ⟨h1, h2⟩
      obtain ⟨wy⟩ := h1
      obtain ⟨wz⟩ := h2
      refine Set.mem_iUnion.mpr ⟨wy.support.toFinset ∪ wz.support.toFinset, ⟨?_, y, rfl, ?_, ?_⟩,
        ⟨?_, z, rfl, ?_, ?_⟩⟩
      · exact Finset.mem_coe.mpr (Finset.mem_union_left _
          (List.mem_toFinset.mpr wy.start_mem_support))
      · exact Finset.mem_coe.mpr (Finset.mem_union_left _
          (List.mem_toFinset.mpr wy.end_mem_support))
      · exact reachable_restricted_of_walk wy Finset.subset_union_left
      · exact Finset.mem_coe.mpr (Finset.mem_union_left _
          (List.mem_toFinset.mpr wy.start_mem_support))
      · exact Finset.mem_coe.mpr (Finset.mem_union_right _
          (List.mem_toFinset.mpr wz.end_mem_support))
      · exact reachable_restricted_of_walk wz Finset.subset_union_right
  have hPle : ∀ (R : Finset (Vertex d)) (a b : Vertex d),
      (percolation d p).real (connectionToSetEvent (↑R) a {b}) ≤ twoPoint d p a b :=
    fun R a b => measureReal_mono (connectionToSetEvent_singleton_subset _ _ _) (measure_ne_top _ _)
  have hle : ∀ R, (percolation d p) (E R) ≤ ENNReal.ofReal C := by
    intro R
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hC_nonneg).mpr ?_
    refine (restricted_tripod_connection_probability_le p R x y z).trans ?_
    refine (Finset.sum_le_sum (fun u _ => ?_)).trans
      ((hsum x y z).sum_le_tsum R (fun u _ => hterm u))
    have h1 : (percolation d p).real (connectionToSetEvent (↑R) x {u}) ≤ twoPoint d p u x := by
      rw [twoPoint_comm]; exact hPle R x u
    have h2 : (percolation d p).real (connectionToSetEvent (↑R) u {y}) ≤ twoPoint d p u y := hPle R u y
    have h3 : (percolation d p).real (connectionToSetEvent (↑R) z {u}) ≤ twoPoint d p u z := by
      rw [twoPoint_comm]; exact hPle R z u
    exact mul_le_mul
      (mul_le_mul h1 h2 measureReal_nonneg (twoPoint_nonneg p u x))
      h3 measureReal_nonneg
      (mul_nonneg (twoPoint_nonneg p u x) (twoPoint_nonneg p u y))
  have hmeas : (percolation d p) (⋃ R, E R) = ⨆ R, (percolation d p) (E R) :=
    hdir.measure_iUnion
  have hfinal : (percolation d p) (connectionEvent x y ∩ connectionEvent x z) ≤ ENNReal.ofReal C := by
    rw [← hunion, hmeas]
    exact iSup_le hle
  calc (percolation d p).real (connectionEvent x y ∩ connectionEvent x z)
      ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal
    _ = C := ENNReal.toReal_ofReal hC_nonneg

/-- The BK tree-graph input is NOT an independent axiom: it follows from the
spatial bubble input already assumed downstream, since the third two-point
factor is a probability (`≤ 1`) and the pair sum is bubble-summable.  The
inequality itself comes from the branch-point tripod decomposition and
increasing-event BK. -/
theorem threePointTreeGraphInput_of_bubble {d : ℕ} {B : ℝ}
    (bubble : CriticalSpatialBubbleInput d B) : ThreePointTreeGraphInput d := by
  have hsum : ∀ x y z : Vertex d, Summable (fun u =>
      twoPoint d (criticalPoint d) u x * twoPoint d (criticalPoint d) u y *
        twoPoint d (criticalPoint d) u z) := by
    intro x y z
    refine Summable.of_nonneg_of_le (fun u => ?_) (fun u => ?_) (bubble x y).1
    · exact mul_nonneg (mul_nonneg (twoPoint_nonneg _ u x) (twoPoint_nonneg _ u y))
        (twoPoint_nonneg _ u z)
    · exact mul_le_of_le_one_right
        (mul_nonneg (twoPoint_nonneg _ u x) (twoPoint_nonneg _ u y)) measureReal_le_one
  exact fun x y z => threePointTree_of_summable (criticalPoint d) hsum x y z

/-- `lem.threepoint_upper` with the tree-graph hypothesis ELIMINATED: it now
follows from the green and bubble inputs alone, since the tree-graph input is
derived (`threePointTreeGraphInput_of_bubble`) rather than assumed. -/
theorem threePoint_probability_upper_of_green_bubble {d : ℕ} (hd : 4 < d)
    {G B : ℝ} (hG : 0 < G) (hB : 0 < B)
    (green : CriticalSupGreenUpper d G) (bubble : CriticalSpatialBubbleInput d B) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y z : Vertex d, x ≠ y → y ≠ z → x ≠ z →
      (percolation d (criticalPoint d)).real (connectionEvent x y ∩ connectionEvent x z) ≤
        C * tripleMinSeparation x y z ^ ((4 : ℝ) - (d : ℝ)) *
          tripleMaxSeparation x y z ^ ((2 : ℝ) - (d : ℝ)) :=
  threePoint_probability_upper_of_standard_inputs hd hG hB green bubble
    (threePointTreeGraphInput_of_bubble bubble)

end NearCritical
