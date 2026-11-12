module

public import NearCritical.SlabUpperBlockGeometry
public import NearCritical.Section10TubeArithmetic

/-! The coarse endpoints agree with the two fine cube centres, and no
third cube can meet the tube. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10

theorem coarseShift_bondTip {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) :
    coarseShift (d := d) n (bondTip e) =
      farCenter n (coarseShift n e.1) (Fin.castLE hd e.2) := by
  ext j
  by_cases hj : j.val < 2
  · let c : Fin 2 := ⟨j.val, hj⟩
    have hcast : Fin.castLE hd c = j := Fin.ext rfl
    rw [← hcast, coarseShift_apply hd]
    by_cases h : c = e.2
    · rw [h, farCenter_apply_self, coarseShift_apply hd]
      simp [bondTip] <;> ring
    · have hne : Fin.castLE hd c ≠ Fin.castLE hd e.2 :=
        fun h' => h (Fin.ext (congrArg (fun j : Fin d => j.val) h'))
      rw [farCenter_apply_ne _ _ _ hne, coarseShift_apply hd]
      simp [bondTip, h]
  · have hne : j ≠ Fin.castLE hd e.2 := by
      intro he
      apply hj
      rw [he]
      exact e.2.isLt
    rw [farCenter_apply_ne _ _ _ hne]
    simp [coarseShift, hj]

/-- A cube meeting the tube of a coarse edge is one of its endpoint cubes. -/
theorem slabCube_meets_slabTube {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    {x : Vertex d} {u v : Vertex 2} {i : Fin 2}
    (hT : x ∈ slabTube n u i) (hQ : x ∈ slabCube n v) :
    v = u ∨ v = bondTip (u,i) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htrans (c : Fin 2) (hc : c ≠ i) : v c = u c := by
    by_contra h
    have h₁ := hT.2 (Fin.castLE hd c) (fun hv => hc (Fin.ext hv))
    have h₂ := hQ (Fin.castLE hd c)
    rw [coarseShift_apply hd] at h₁ h₂
    push_cast at h₁ h₂
    rw [abs_lt] at h₁ h₂
    rcases int_sep h with h | h
    · have h' : (v c : ℝ) + 1 ≤ (u c : ℝ) := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_left h' hnR.le]
    · have h' : (u c : ℝ) + 1 ≤ (v c : ℝ) := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_left h' hnR.le]
  have h₁ := hT.1 (Fin.castLE hd i) rfl
  have h₂ := hQ (Fin.castLE hd i)
  rw [coarseShift_apply hd] at h₁ h₂
  push_cast at h₁ h₂
  rw [abs_lt] at h₂
  have haxis : v i = u i ∨ v i = u i + 1 := by
    by_contra h
    have h' : v i + 1 ≤ u i ∨ u i + 2 ≤ v i := by omega
    rcases h' with h' | h'
    · have h'' : (v i : ℝ) + 1 ≤ (u i : ℝ) := by exact_mod_cast h'
      nlinarith [mul_le_mul_of_nonneg_left h'' hnR.le]
    · have h'' : (u i : ℝ) + 2 ≤ (v i : ℝ) := by exact_mod_cast h'
      nlinarith [mul_le_mul_of_nonneg_left h'' hnR.le]
  rcases haxis with h | h
  · left
    ext c
    by_cases hc : c = i
    · simpa [hc] using h
    · exact htrans c hc
  · right
    ext c
    by_cases hc : c = i
    · simpa [hc, bondTip] using h
    · simpa [bondTip, hc] using htrans c hc

end NearCritical
