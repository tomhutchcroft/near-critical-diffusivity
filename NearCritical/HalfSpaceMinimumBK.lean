module

public import NearCritical.HalfSpaceArmGeometry

/-! The new minimum-height probability reduction from prop.onearm_half_plus.
All sums are extended nonnegative sums under the actual infinite lattice law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Extended-probability version of the actual-law BK bound for target connections. -/
lemma connectionToSet_bk_ennreal {d : ℕ} (p : unitInterval) (S T : Set (Vertex d))
    (x y : Vertex d) (A B : Set (Vertex d)) :
    percolation d p {ω | DisjointOccurrence
      (connectionToSetEvent S x A) (connectionToSetEvent T y B) ω} ≤
      percolation d p (connectionToSetEvent S x A) *
        percolation d p (connectionToSetEvent T y B) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  simpa only [ENNReal.toReal_mul, Measure.real] using connectionToSet_bk p S T x y A B

/-- Minimum-height path decomposition, followed by a countable union bound and
BK. The products and their sum are proved from actual event geometry, not assumed. -/
theorem halfSpace_connection_minimum_bk {d : ℕ} (p : unitInterval)
    (i : Fin d) (a : ℤ) (x : Vertex d) (B : Set (Vertex d)) :
    percolation d p (connectionToSetEvent {z | a ≤ z i} x B) ≤
      ∑' u : Vertex d, if a ≤ u i ∧ u i ≤ x i then
        percolation d p (connectionToSetEvent {z | u i ≤ z i} x {u}) *
          percolation d p (connectionToSetEvent {z | u i ≤ z i} u B)
        else 0 := by
  let C := fun u : Vertex d ↦ {ω : Configuration d | a ≤ u i ∧ u i ≤ x i ∧
    DisjointOccurrence (connectionToSetEvent {z | u i ≤ z i} x {u})
      (connectionToSetEvent {z | u i ≤ z i} u B) ω}
  have hsub : connectionToSetEvent {z | a ≤ z i} x B ⊆ ⋃ u, C u := by
    intro ω hω
    obtain ⟨u, hau, hux, hdis⟩ := halfSpace_connection_minimum_split i a x B hω
    exact Set.mem_iUnion.mpr ⟨u, hau, hux, hdis⟩
  calc
    _ ≤ percolation d p (⋃ u, C u) := measure_mono hsub
    _ ≤ ∑' u, percolation d p (C u) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro u
      by_cases hu : a ≤ u i ∧ u i ≤ x i
      · rw [ite_eq_left hu]
        exact (measure_mono (show C u ⊆ {ω | DisjointOccurrence
          (connectionToSetEvent {z | u i ≤ z i} x {u})
          (connectionToSetEvent {z | u i ≤ z i} u B) ω} from fun _ h ↦ h.2.2)).trans
          (connectionToSet_bk_ennreal p _ _ _ _ _ _)
      · have hempty : C u = ∅ := by
          ext ω
          simp only [C, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h ↦ hu ⟨h.1, h.2.1⟩
        simp only [ite_eq_right hu, hempty, measure_empty, le_refl]

end NearCritical
