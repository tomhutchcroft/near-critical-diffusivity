module
public import NearCritical.Section9AvoidanceConditional
public import NearCritical.Section9ExitFace

/-! Source tube/exit-face specialization of the actual avoidance comparison. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The paper's exit-face target contains every possible right-tube entry
into C from outside the left tube. This is purely source geometry and needs
only C⊆T12, not an actual-cluster or positive-scale hypothesis. -/
theorem section9_source_exit_face_exterior_guard {d : ℕ} (i : Fin d) (n : ℕ)
    (C Q F : Finset (Vertex d))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) :
    ∀ b ∈ sprinklingAvailableBonds
        (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) Q F,
      (b.1 ∈ C → bondTip b ∉ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
        b.1 ∈ section9ExitFace i n ∩ C) ∧
      (bondTip b ∈ C → b.1 ∉ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
        bondTip b ∈ section9ExitFace i n ∩ C) := by
  intro b hb
  have hbR := (mem_internalBondSet
    (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) b).mp (Finset.mem_sdiff.mp hb).1
  constructor
  · intro hbaseC htipNot
    have hentry : b.1 ∈ innerEntryBoundary
        (section9FiniteTube i n (-(3 : ℝ)/8) (5/8))
        (section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) := by
      apply Finset.mem_filter.mpr
      exact ⟨hCL hbaseC,bondTip b,hbR.2,htipNot,
        ⟨b,rfl,Or.inr ⟨rfl,rfl⟩⟩⟩
    exact Finset.mem_inter.mpr ⟨section9_entryBoundary_subset_exitFace i n hentry,hbaseC⟩
  · intro htipC hbaseNot
    have hentry : bondTip b ∈ innerEntryBoundary
        (section9FiniteTube i n (-(3 : ℝ)/8) (5/8))
        (section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) := by
      apply Finset.mem_filter.mpr
      exact ⟨hCL htipC,b.1,hbR.1,hbaseNot,
        ⟨b,rfl,Or.inl ⟨rfl,rfl⟩⟩⟩
    exact Finset.mem_inter.mpr ⟨section9_entryBoundary_subset_exitFace i n hentry,htipC⟩

/-- The source fresh-copy avoidance upper bound, transferred to actual
left-cluster joint probabilities. The exterior-entry, deletion-separation,
and end-target/component disjointness guards are all discharged from the
actual T12/T23 geometry. Zero-probability cluster fibers are included. -/
theorem section9_source_avoidance_fresh_to_left_fiber_candidate_bound {d : ℕ}
    (reimer : FiniteBernoulliBKRInput) (p : unitInterval)
    (i : Fin d) (n : ℕ) (hn : 0 < n)
    (F₁ F₃ C B : Finset (Vertex d)) (root : Vertex d)
    (hr : root ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hB : B ⊆ section9FiniteEndCube i n (2*(n : ℝ))) {z : Vertex d}
    (hzR : z ∈ section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) (hzC : z ∈ C) :
    let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let V := section9ExitFace i n ∩ C
    let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
    (percolation d p).real E *
      (percolation d p).real (section9AvoidanceEvent R R Q₃ F₃ B V z) ≤
      ∑ t ∈ section9AvoidanceLastExitCandidates R C Q₃ F₃,
        (p : ℝ)*(percolation d p).real
          {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} *
        (percolation d p).real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2) := by
  intro L R Q₁ Q₃ V E
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxC
    exact Finset.disjoint_left.mp (section9FiniteLeftTube_disjoint_third i hn)
      (hCL hxC) (hB hxB)
  exact section9_avoidance_fresh_to_left_fiber_candidate_bound reimer p
    L R Q₁ F₁ Q₃ F₃ C B V root hr (section9FiniteRightTube_disjoint_first i hn)
    hzR hzC hBC (section9_source_exit_face_exterior_guard i n C Q₃ F₃ hCL)

end NearCritical
