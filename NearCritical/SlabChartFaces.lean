module

public import NearCritical.SlabChartRegularity

/-! The chart preserves the regularity region and the full cube boundary.
At the face used for sprinkling it reverses the axial sign when needed. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

theorem mem_typicalInnerCube_slabChart_iff {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (e : Bond 2) (rev : Bool) (x c : Vertex d) :
    slabChartVertex hd n e rev x ∈ typicalInnerCube n (slabChartVertex hd n e rev c) ↔
      x ∈ typicalInnerCube n c := by
  simp only [typicalInnerCube, Finset.mem_filter, mem_typicalCube_slabChart_iff hd hn,
    slabChartVertex_abs_sub]

/-- A point of the cube is on its boundary iff one coordinate has the
extremal absolute offset. -/
theorem mem_typicalBoundary_iff_abs {d : ℕ} (n : ℕ) (c x : Vertex d) :
    x ∈ typicalBoundary n c ↔ x ∈ typicalCube n c ∧
      ∃ j, |((x j - c j : ℤ) : ℝ)| = ((n-1)/2 : ℕ) := by
  have h (a : ℤ) (b : ℕ) :
      |(a : ℝ)| = (b : ℝ) ↔ a = (b : ℤ) ∨ a = -(b : ℤ) := by
    constructor
    · intro ha
      by_cases hneg : a < 0
      · right
        rw [abs_of_neg (by exact_mod_cast hneg)] at ha
        have he : -a = (b : ℤ) := by exact_mod_cast ha
        omega
      · left
        rw [abs_of_nonneg (by exact_mod_cast (le_of_not_gt hneg))] at ha
        exact_mod_cast ha
    · rintro (ha | ha)
      · simp [ha]
      · simp [ha]
  constructor
  · intro hx
    obtain ⟨⟨j,s⟩, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hQ,hs⟩ := Finset.mem_filter.mp hx
    refine ⟨hQ,j,(h _ _).2 ?_⟩
    cases s
    · exact Or.inr hs
    · exact Or.inl hs
  · rintro ⟨hQ,j,hx⟩
    rcases (h _ _).1 hx with hs | hs
    · exact Finset.mem_biUnion.mpr ⟨(j,true), Finset.mem_univ _, Finset.mem_filter.mpr ⟨hQ,hs⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(j,false), Finset.mem_univ _, Finset.mem_filter.mpr ⟨hQ,hs⟩⟩

theorem mem_typicalBoundary_slabChart_iff {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (e : Bond 2) (rev : Bool) (x c : Vertex d) :
    slabChartVertex hd n e rev x ∈ typicalBoundary n (slabChartVertex hd n e rev c) ↔
      x ∈ typicalBoundary n c := by
  simp only [mem_typicalBoundary_iff_abs, mem_typicalCube_slabChart_iff hd hn, slabChartVertex_abs_sub]

theorem slabChartVertex_sub {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (x c : Vertex d) (j : Fin d) :
    slabChartVertex hd n e rev x j - slabChartVertex hd n e rev c j =
      if rev = true ∧ j = Fin.castLE hd e.2 then -(x j - c j) else x j - c j := by
  cases rev
  · simp [slabChartVertex, Pi.add_apply]
  · by_cases h : j = Fin.castLE hd e.2
    · subst j
      simp [slabChartVertex, Pi.add_apply, reflVertex] <;> ring
    · simp [slabChartVertex, Pi.add_apply, reflVertex, Function.update_of_ne h, h]

theorem mem_typicalSplitFace_slabChart_axis_iff {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (e : Bond 2) (rev : Bool) (x c : Vertex d) (sign plus : Bool) :
    let i := Fin.castLE hd e.2
    slabChartVertex hd n e rev x ∈ typicalSplitFace n (slabChartVertex hd n e rev c)
      (i, if rev then !sign else sign) plus ↔ x ∈ typicalSplitFace n c (i, sign) plus := by
  intro i
  let m : ℤ := (((n-1)/2 : ℕ) : ℤ)
  have hax :
      (slabChartVertex hd n e rev x i - slabChartVertex hd n e rev c i =
        if (if rev then !sign else sign) then m else -m) ↔
      (x i - c i = if sign then m else -m) := by
    rw [slabChartVertex_sub]
    cases rev <;> cases sign <;> simp [i] <;> omega
  have htrans (j : Fin d) (hj : j ≠ i) :
      slabChartVertex hd n e rev x j - slabChartVertex hd n e rev c j = x j - c j := by
    rw [slabChartVertex_sub, if_neg (fun h => hj h.2)]
  simp only [typicalSplitFace, typicalFace, Finset.mem_filter, mem_typicalCube_slabChart_iff hd hn]
  change (_ ∧ (slabChartVertex hd n e rev x i - slabChartVertex hd n e rev c i =
    if (if rev then !sign else sign) then m else -m)) ∧ _ ↔
    (_ ∧ (x i - c i = if sign then m else -m)) ∧ _
  rw [hax]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  exact imp_congr_right (fun hj => by rw [htrans j hj])

end NearCritical
