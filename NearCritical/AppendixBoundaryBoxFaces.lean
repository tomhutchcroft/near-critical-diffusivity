module
public import NearCritical.AppendixBoundarySideFace
public import NearCritical.HalfSpaceLastVisitBK

/-! Step R3a of the repaired route to eq.boundary_0_mean_segment: the side-face
mass of a finite domain is at most the plane mass times the cited slab mean.
* `last_exit_real`: real-valued, finite-sum form of the verified last-height BK
  decomposition `connectionToSet_last_height_bk`.
* `side_face_mass_le`: for a finite domain `Bx ∋ 0` with `w k ≤ R` on `Bx`,
  `Σ_{y∈Bx, y k=R} P[0 ↔_Bx y] ≤ (Σ_{u∈Bx, u k=R-h} P[0 ↔_Bx u]) · (A+B)/h`.
  It combines the last exit at the plane `{z k = R-h}` with R1
  (`side_face_mass_le_slab_mean`) on `Bx ∩ {z k ≥ R-h}`.
This replaces the source's false containment Q' ⊆ Q_z (main.tex ~6303). -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical ENNReal
open NearCritical.Section8

lemma connectionToSetEvent_empty_of_target_not_mem {d : ℕ} (S : Set (Vertex d))
    (x y : Vertex d) (hy : y ∉ S) : connectionToSetEvent S x {y} = ∅ := by
  ext ω
  simp only [Set.mem_empty_iff_false,iff_false]
  rintro ⟨_,z,hz,hzS,_⟩
  rw [Set.mem_singleton_iff] at hz
  rw [hz] at hzS
  exact hy hzS

/-- Real-valued last-exit BK over a finite domain. -/
theorem last_exit_real {d : ℕ} (p : unitInterval) (B : Finset (Vertex d)) (x y : Vertex d)
    (k : Fin d) (l : ℤ) (hx : x k ≤ l) (hy : l ≤ y k) :
    (percolation d p).real (connectionToSetEvent (B : Set (Vertex d)) x {y}) ≤
      ∑ u ∈ B, if u k = l then
        (percolation d p).real (connectionToSetEvent (B : Set (Vertex d)) x {u}) *
        (percolation d p).real (connectionToSetEvent ((B : Set (Vertex d)) ∩ {z | l ≤ z k}) u {y})
        else 0 := by
  have hbk := connectionToSet_last_height_bk p (B : Set (Vertex d)) {y} x k l hx
    (by
      intro y' hy'
      rw [Set.mem_singleton_iff.mp hy']
      exact hy)
  rw [tsum_eq_sum (s := B) (fun u hu ↦ ?_)] at hbk
  · have hterm : ∀ u ∈ B, (if u k = l then
        percolation d p (connectionToSetEvent (B : Set (Vertex d)) x {u}) *
        percolation d p (connectionToSetEvent ((B : Set (Vertex d)) ∩ {z | l ≤ z k}) u {y})
        else 0) ≠ ∞ := by
      intro u _
      split_ifs
      · exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
      · exact ENNReal.zero_ne_top
    have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hterm) hbk
    rw [ENNReal.toReal_sum hterm] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl (fun u _ => ?_)))
    split_ifs <;> simp [ENNReal.toReal_mul,measureReal_def]
  · have hu' : u ∉ (B : Set (Vertex d)) := hu
    rw [connectionToSetEvent_empty_of_target_not_mem _ x u hu']
    simp

/-- Side-face mass of a finite domain, bounded by the plane mass times the cited slab
mean. Applied below to each positive side face; negative faces follow by reflection. -/
theorem side_face_mass_le {d : ℕ} (i₀ k : Fin d) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (arm : HalfSpaceCriticalArmInput i₀ A) (second : SlabBoundarySecondMomentUpper i₀ B)
    (h : ℕ) (hh : 1 ≤ h) (R : ℕ) (hhR : h ≤ R) (Bx : Finset (Vertex d))
    (hBk : ∀ w ∈ Bx, w k ≤ (R : ℤ)) :
    ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)), (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Bx : Set (Vertex d)) 0 {y}) ≤
      (∑ u ∈ Bx.filter (fun u => u k = (R : ℤ)-h), (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Bx : Set (Vertex d)) 0 {u}))*((A+B)/(h : ℝ)) := by
  set l : ℤ := (R : ℤ)-h with hl
  let P := fun (S : Set (Vertex d)) (a b : Vertex d) =>
    (percolation d (criticalPoint d)).real (connectionToSetEvent S a {b})
  let M : ℝ := (A+B)/(h : ℝ)
  have hl0 : (0 : Vertex d) k ≤ l := by
    simp only [Pi.zero_apply]
    omega
  -- the inner sum from a plane point is controlled by R1
  have hinner : ∀ u ∈ Bx, u k = l →
      ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)),
        P ((Bx : Set (Vertex d)) ∩ {z | l ≤ z k}) u y ≤ M := by
    intro u hu hul
    let Rz := Bx.filter (fun z => l ≤ z k)
    have huRz : u ∈ Rz := Finset.mem_filter.mpr ⟨hu,le_of_eq hul.symm⟩
    have hR : ∀ w ∈ Rz, u k ≤ w k ∧ w k ≤ u k+h := by
      intro w hw
      obtain ⟨hwB,hwl⟩ := Finset.mem_filter.mp hw
      have := hBk w hwB
      rw [hul]
      constructor
      · exact hwl
      · omega
    have hR1 := side_face_mass_le_slab_mean i₀ k A B hA hB arm second h hh Rz u huRz hR
    have hcoe : ((Rz : Finset (Vertex d)) : Set (Vertex d)) =
        (Bx : Set (Vertex d)) ∩ {z | l ≤ z k} := by
      ext z
      simp [Rz]
    have hset : Rz.filter (fun y => y k = u k+h) = Bx.filter (fun y => y k = (R : ℤ)) := by
      ext y
      simp only [Rz,Finset.mem_filter]
      rw [hul]
      constructor
      · rintro ⟨⟨hyB,_⟩,hyk⟩
        refine ⟨hyB,?_⟩
        omega
      · rintro ⟨hyB,hyk⟩
        refine ⟨⟨hyB,?_⟩,?_⟩
        · omega
        · omega
    rw [hset,hcoe] at hR1
    exact hR1
  have hM : 0 ≤ M := div_nonneg (by linarith) (Nat.cast_nonneg h)
  calc ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)), P (Bx : Set (Vertex d)) 0 y
      ≤ ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)), ∑ u ∈ Bx, (if u k = l then
          P (Bx : Set (Vertex d)) 0 u * P ((Bx : Set (Vertex d)) ∩ {z | l ≤ z k}) u y
          else 0) := by
        apply Finset.sum_le_sum
        intro y hy
        have hyk : y k = (R : ℤ) := (Finset.mem_filter.mp hy).2
        exact last_exit_real (criticalPoint d) Bx 0 y k l hl0 (by omega)
    _ = ∑ u ∈ Bx, ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)), (if u k = l then
          P (Bx : Set (Vertex d)) 0 u * P ((Bx : Set (Vertex d)) ∩ {z | l ≤ z k}) u y
          else 0) := Finset.sum_comm
    _ ≤ ∑ u ∈ Bx, (if u k = l then P (Bx : Set (Vertex d)) 0 u * M else 0) := by
        apply Finset.sum_le_sum
        intro u hu
        by_cases hul : u k = l
        · simp only [if_pos hul]
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hinner u hu hul) measureReal_nonneg
        · simp [hul]
    _ = (∑ u ∈ Bx.filter (fun u => u k = l), P (Bx : Set (Vertex d)) 0 u)*M := by
        rw [Finset.sum_filter,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        split_ifs <;> simp

end NearCritical
