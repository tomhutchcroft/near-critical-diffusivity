module

public import NearCritical.SlabPioneerReflection

/-! Exact vertical shift of the actual homogeneous infinite-law slab mass.
No stationarity of a fixed finite cutoff is asserted. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set

theorem slabPioneerMass_shift {d : ℕ} (p : unitInterval) (i : Fin d)
    (m n k j h : ℤ) :
    slabPioneerMass p i (m+h) (n+h) (k+h) (j+h) = slabPioneerMass p i m n k j := by
  let a : Vertex d := Pi.single i h
  have hstart : (Pi.single i (k+h) : Vertex d) = a+Pi.single i k := by
    ext t
    by_cases ht : t=i
    · subst t
      simp [a,add_comm]
    · simp [a,ht]
  unfold slabPioneerMass
  rw [← (Equiv.addLeft a).tsum_eq]
  apply tsum_congr
  intro u
  have hcond : ((Equiv.addLeft a) u) i = j+h ↔ u i = j := by
    change (a+u) i = j+h ↔ u i = j
    simp only [a,Pi.add_apply,Pi.single_eq_same]
    omega
  by_cases hu : u i = j
  · rw [ite_eq_left (hcond.mpr hu),ite_eq_left hu,hstart]
    have H := connectionToSet_probability_translation p a (Pi.single i k)
      (finiteHeightSlab i m n) {u}
    rw [translate_finiteHeightSlab_shift,Set.image_singleton] at H
    simpa only [Equiv.coe_addLeft, a, Pi.single_eq_same] using H
  · rw [ite_eq_right (fun h ↦ hu (hcond.mp h)),ite_eq_right hu]

/-- Move an arbitrary bottom layer to zero without changing the actual law. -/
lemma slabPioneerMass_bottom_shift {d : ℕ} (p : unitInterval) (i : Fin d) (a j : ℤ) :
    slabPioneerMass p i a j a j = slabPioneerMass p i 0 (j-a) 0 (j-a) := by
  simpa only [zero_add,sub_add_cancel] using slabPioneerMass_shift p i 0 (j-a) 0 (j-a) a

end NearCritical
