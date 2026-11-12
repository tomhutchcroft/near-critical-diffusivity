module

public import NearCritical.SlabTubeChart
public import NearCritical.Section10Section9Geometry

/-! The parent-coordinate chart identifies both endpoint cubes and their
hearts with the corresponding shapes in the Section 9 estimate. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10

/-- The parent coordinate chart is a bijection on lattice sites. -/
def slabChartEquiv {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool) : Vertex d ≃ Vertex d :=
  if rev then
    let i := Fin.castLE hd e.2
    let reflection : Vertex d ≃ Vertex d :=
      ⟨reflVertex i, reflVertex i, reflVertex_reflVertex i, reflVertex_reflVertex i⟩
    reflection.trans (Equiv.addLeft (coarseShift n (bondTip e)))
  else Equiv.addLeft (coarseShift n e.1)

theorem slabChartEquiv_apply {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (x : Vertex d) : slabChartEquiv hd n e rev x = slabChartVertex hd n e rev x := by
  cases rev <;> rfl

theorem slabChartVertex_injective {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool) :
    Function.Injective (slabChartVertex hd n e rev) := by
  intro x y h
  apply (slabChartEquiv hd n e rev).injective
  simpa only [slabChartEquiv_apply] using h

lemma slabChartVertex_abs_sub {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (x c : Vertex d) (j : Fin d) :
    |((slabChartVertex hd n e rev x j - slabChartVertex hd n e rev c j : ℤ) : ℝ)| =
      |((x j - c j : ℤ) : ℝ)| := by
  cases rev
  · simp [slabChartVertex, Pi.add_apply]
  · by_cases h : j = Fin.castLE hd e.2
    · subst j
      simp only [slabChartVertex, Bool.true_eq, if_true, Pi.add_apply, reflVertex, Function.update_self]
      have he : coarseShift n (bondTip e) (Fin.castLE hd e.2) + -x (Fin.castLE hd e.2) -
          (coarseShift n (bondTip e) (Fin.castLE hd e.2) + -c (Fin.castLE hd e.2)) =
          -(x (Fin.castLE hd e.2) - c (Fin.castLE hd e.2)) := by ring
      rw [he, Int.cast_neg, abs_neg]
    · simp [slabChartVertex, Pi.add_apply, reflVertex, Function.update_of_ne h]

theorem mem_typicalCube_slabChart_iff {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (e : Bond 2) (rev : Bool) (x c : Vertex d) :
    slabChartVertex hd n e rev x ∈ typicalCube n (slabChartVertex hd n e rev c) ↔ x ∈ typicalCube n c := by
  rw [mem_typicalCube_iff_int hn, mem_typicalCube_iff_int hn]
  apply forall_congr'
  intro j
  rw [halfSide_iff hn, halfSide_iff hn]
  simp only [neg_div, ← abs_lt, slabChartVertex_abs_sub]

theorem mem_typicalHeart_slabChart_iff {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (e : Bond 2) (rev : Bool) (x c : Vertex d) (cc : ℝ) :
    slabChartVertex hd n e rev x ∈ typicalHeart n (slabChartVertex hd n e rev c) cc ↔
      x ∈ typicalHeart n c cc := by
  simp only [typicalHeart, Finset.mem_filter, mem_typicalCube_slabChart_iff hd hn,
    slabChartVertex_abs_sub]

theorem slabChartVertex_centres {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool) :
    let i := Fin.castLE hd e.2
    slabChartVertex hd n e rev (0 : Vertex d) =
        coarseShift n (if rev then bondTip e else e.1) ∧
      slabChartVertex hd n e rev (farCenter n (0 : Vertex d) i) =
        coarseShift n (if rev then e.1 else bondTip e) := by
  have href : reflVertex (Fin.castLE hd e.2)
      (farCenter n (0 : Vertex d) (Fin.castLE hd e.2)) =
      -farCenter n (0 : Vertex d) (Fin.castLE hd e.2) := by
    ext j
    by_cases h : j = Fin.castLE hd e.2
    · subst j
      simp [reflVertex]
    · simp [reflVertex, Function.update_of_ne h, farCenter_apply_ne n (0 : Vertex d) _ h]
  have hz : reflVertex (Fin.castLE hd e.2) (0 : Vertex d) = 0 := by
    ext j
    simp [reflVertex, Function.update_apply]
  cases rev
  · simp [slabChartVertex, coarseShift_bondTip hd, farCenter]
  · change (coarseShift n (bondTip e) + reflVertex (Fin.castLE hd e.2) 0 =
        coarseShift n (bondTip e)) ∧
      (coarseShift n (bondTip e) + reflVertex (Fin.castLE hd e.2)
        (farCenter n (0 : Vertex d) (Fin.castLE hd e.2)) = coarseShift n e.1)
    rw [hz, add_zero, href, coarseShift_bondTip hd]
    simp [farCenter]

end NearCritical
