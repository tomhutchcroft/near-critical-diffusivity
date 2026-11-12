module
public import NearCritical.AppendixSourceRD

/-! Dominant coordinate and transverse gap from literal source RD membership. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped Classical

/-- Actual source RD membership supplies the geometric face chart data. -/
theorem sourceRD_face_chart {k n c : ℕ} {w : Fin (k+1) → ℤ}
    (hw : w ∈ (sourceRD n c : Finset (Fin (k+1) → ℤ))) :
    1 ≤ sParam c w ∧ sParam c w ≤ c ∧
      ∃ i : Fin (k+1), (w i).natAbs = c + sourceR c w ∧
        ∀ j : Fin (k+1), j ≠ i → (w j).natAbs ≤ c - sParam c w := by
  obtain ⟨i,hi,hdom⟩ := sourceRD_exists_dominant hw
  have hm := mem_sourceRD.mp hw
  have hbase := hm.1.2
  have hgap := hm.2
  unfold sourceR sParam at hgap
  have hspos : 1 ≤ sParam c w := by unfold sParam; omega
  have hsle : sParam c w ≤ c := by unfold sParam; omega
  refine ⟨hspos,hsle,i,?_,?_⟩
  · unfold sourceR
    omega
  · intro j hji
    obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq hji
    have hj : (w j).natAbs ≤ secondMax w := by
      rw [secondMax_eq_sup_succAbove hdom,← ha]
      exact Finset.le_sup (f := fun b : Fin k => (w (i.succAbove b)).natAbs)
        (Finset.mem_univ a)
    unfold sParam
    omega

end NearCritical.AppendixVariance
