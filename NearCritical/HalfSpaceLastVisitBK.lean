module

public import NearCritical.HalfSpaceLastVisit
public import NearCritical.HalfSpaceMinimumBK

/-! The new last-visit/BK probability deduction in source prop.onearm_half_plus. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Last-intermediate-level decomposition and BK for actual domain connections.
The extended sum may be infinite; no summability or probability bound is assumed. -/
theorem connectionToSet_last_height_bk {d : ℕ} (p : unitInterval)
    (S B : Set (Vertex d)) (x : Vertex d) (i : Fin d) (l : ℤ)
    (hx : x i ≤ l) (hB : ∀ y ∈ B, l ≤ y i) :
    percolation d p (connectionToSetEvent S x B) ≤
      ∑' u : Vertex d, if u i = l then
        percolation d p (connectionToSetEvent S x {u}) *
          percolation d p (connectionToSetEvent (S ∩ {z | l ≤ z i}) u B)
        else 0 := by
  let C := fun u : Vertex d ↦ {ω : Configuration d | u i = l ∧
    DisjointOccurrence (connectionToSetEvent S x {u})
      (connectionToSetEvent (S ∩ {z | l ≤ z i}) u B) ω}
  have hsub : connectionToSetEvent S x B ⊆ ⋃ u, C u := by
    intro ω hω
    obtain ⟨u, hul, hdis⟩ := connectionToSet_last_height_split S B x i l hx hB hω
    exact Set.mem_iUnion.mpr ⟨u, hul, hdis⟩
  calc
    _ ≤ percolation d p (⋃ u, C u) := measure_mono hsub
    _ ≤ ∑' u, percolation d p (C u) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro u
      by_cases hu : u i = l
      · rw [ite_eq_left hu]
        exact (measure_mono (show C u ⊆ {ω | DisjointOccurrence
          (connectionToSetEvent S x {u})
          (connectionToSetEvent (S ∩ {z | l ≤ z i}) u B) ω} from fun _ h ↦ h.2)).trans
          (connectionToSet_bk_ennreal p _ _ _ _ _ _)
      · have hempty : C u = ∅ := by
          ext ω
          simp only [C, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h ↦ hu h.1
        simp only [ite_eq_right hu, hempty, measure_empty, le_refl]

/-- Exact source Step1 half-space product sum, before pioneer reindexing. Cuts
are arbitrary integers, so the theorem does not assume a floor/ceiling identity. -/
theorem halfSpace_arm_last_height_bk {d : ℕ} (p : unitInterval)
    (i : Fin d) (a l n : ℤ) (x : Vertex d)
    (hal : a ≤ l) (hx : x i ≤ l) (hln : l ≤ n) :
    percolation d p (connectionToSetEvent {z | a ≤ z i} x {z | n ≤ z i}) ≤
      ∑' u : Vertex d, if u i = l then
        percolation d p (connectionToSetEvent {z | a ≤ z i} x {u}) *
          percolation d p (connectionToSetEvent {z | l ≤ z i} u {z | n ≤ z i})
        else 0 := by
  have heq : {z : Vertex d | a ≤ z i} ∩ {z | l ≤ z i} = {z | l ≤ z i} := by
    ext z
    constructor
    · exact fun hz ↦ hz.2
    · intro hz
      exact ⟨hal.trans hz, hz⟩
  simpa only [heq] using connectionToSet_last_height_bk p
    {z | a ≤ z i} {z | n ≤ z i} x i l hx (fun y hy ↦ hln.trans hy)

end NearCritical
