module

public import NearCritical.SlabPioneerConvolution
public import NearCritical.LatticeInversion

/-! Actual infinite-law slab translations and reflection. No truncated
stationarity or reflection of a fixed finite cutoff is asserted. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set

lemma translate_finiteHeightSlab_shift {d : ℕ} (i : Fin d) (m n : ℤ)
    (a : Vertex d) :
    (fun z => a+z) '' finiteHeightSlab i m n =
      finiteHeightSlab i (m+a i) (n+a i) := by
  ext z
  constructor
  · rintro ⟨y,hy,rfl⟩
    change m ≤ y i ∧ y i ≤ n at hy
    change m+a i ≤ a i+y i ∧ a i+y i ≤ n+a i
    omega
  · intro hz
    refine ⟨-a+z,?_,by simp⟩
    change m+a i ≤ z i ∧ z i ≤ n+a i at hz
    change m ≤ -a i+z i ∧ -a i+z i ≤ n
    omega

lemma invert_finiteHeightSlab {d : ℕ} (i : Fin d) (m n : ℤ) :
    Neg.neg '' finiteHeightSlab i m n = finiteHeightSlab i (-n) (-m) := by
  ext z
  constructor
  · rintro ⟨y,hy,rfl⟩
    change m ≤ y i ∧ y i ≤ n at hy
    change -n ≤ -y i ∧ -y i ≤ -m
    omega
  · intro hz
    refine ⟨-z,?_,by simp⟩
    change -n ≤ z i ∧ z i ≤ -m at hz
    change m ≤ -z i ∧ -z i ≤ n
    omega

theorem slab_connection_probability_reflection {d : ℕ} (p : unitInterval)
    (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    percolation d p (connectionToSetEvent (finiteHeightSlab i m n)
      (Pi.single i (m+n)-x) {Pi.single i (m+n)-y}) =
    percolation d p (connectionToSetEvent (finiteHeightSlab i m n) x {y}) := by
  let a : Vertex d := Pi.single i (m+n)
  have hinv := connectionToSet_probability_inversion p x (finiteHeightSlab i m n) {y}
  rw [invert_finiteHeightSlab,Set.image_singleton] at hinv
  have htrans := connectionToSet_probability_translation p a (-x)
    (finiteHeightSlab i (-n) (-m)) {-y}
  rw [translate_finiteHeightSlab_shift,Set.image_singleton] at htrans
  have hlow : -n+a i = m := by simp [a]
  have hhigh : -m+a i = n := by simp [a]
  rw [hlow,hhigh] at htrans
  simpa only [a,sub_eq_add_neg] using htrans.trans hinv

theorem slabPioneerMass_reflection {d : ℕ} (p : unitInterval) (i : Fin d)
    (m n k j : ℤ) :
    slabPioneerMass p i m n (m+n-k) (m+n-j) = slabPioneerMass p i m n k j := by
  let a : Vertex d := Pi.single i (m+n)
  have hstart : (Pi.single i (m+n-k) : Vertex d) = a-Pi.single i k := by
    ext t
    by_cases ht : t=i
    · subst t
      simp [a]
    · simp [a,ht]
  unfold slabPioneerMass
  rw [← (slabReverseLabels a).tsum_eq]
  apply tsum_congr
  intro u
  have hcond : ((slabReverseLabels a) u) i = m+n-j ↔ u i = j := by
    change (a-u) i = m+n-j ↔ u i = j
    simp only [a,Pi.sub_apply,Pi.single_eq_same]
    omega
  by_cases hu : u i = j
  · rw [ite_eq_left (hcond.mpr hu),ite_eq_left hu,hstart]
    exact slab_connection_probability_reflection p i m n (Pi.single i k) u
  · rw [ite_eq_right (fun h => hu (hcond.mp h)),ite_eq_right hu]

end NearCritical
