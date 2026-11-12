module

public import NearCritical.SlabChartCubes
public import NearCritical.NestRegularBoundary

/-! Regularity of a boundary point is invariant under the chart. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

theorem latticeDistance_slabChart {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (x y : Vertex d) :
    latticeDistance (slabChartVertex hd n e rev x) (slabChartVertex hd n e rev y) =
      latticeDistance x y := by
  apply le_antisymm
  · apply (dist_pi_le_iff (latticeDistance_nonneg x y)).2
    intro j
    rw [Real.dist_eq]
    change |(slabChartVertex hd n e rev x j : ℝ) - (slabChartVertex hd n e rev y j : ℝ)| ≤ _
    rw [← Int.cast_sub, slabChartVertex_abs_sub]
    simpa only [← Int.cast_sub, Real.dist_eq, vertexReal] using
      (dist_pi_le_iff (latticeDistance_nonneg x y)).1 (le_refl (latticeDistance x y)) j
  · apply (dist_pi_le_iff (latticeDistance_nonneg _ _)).2
    intro j
    rw [Real.dist_eq]
    change |(x j : ℝ) - (y j : ℝ)| ≤ _
    rw [← Int.cast_sub, ← slabChartVertex_abs_sub hd n e rev x y j]
    simpa only [← Int.cast_sub, Real.dist_eq, vertexReal] using
      (dist_pi_le_iff (latticeDistance_nonneg (slabChartVertex hd n e rev x)
        (slabChartVertex hd n e rev y))).1 (le_refl
          (latticeDistance (slabChartVertex hd n e rev x) (slabChartVertex hd n e rev y))) j

theorem sourceRegularPoint_slabChart_iff {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (e : Bond 2) (rev : Bool)
    (F S B : Finset (Vertex d)) (r : ℕ) (δ : ℝ) (x : Vertex d) :
    let f := slabChartVertex hd n e rev
    sourceRegularPoint (F.image f) (S.image f) (B.image f) r δ (f x) ↔
      sourceRegularPoint F S B r δ x := by
  intro f
  have hf : Function.Injective f := slabChartVertex_injective hd n e rev
  have h₁ : regularityEnergyOne (F.image f) (S.image f) r (f x) = regularityEnergyOne F S r x := by
    unfold regularityEnergyOne
    rw [← Finset.image_sdiff F S hf, Finset.sum_image (fun _ _ _ _ h => hf h)]
    apply Finset.sum_congr rfl
    intro y _
    rw [show latticeDistance (f x) (f y) = latticeDistance x y from
      latticeDistance_slabChart hd n e rev x y]
  have h₂ : regularityEnergyTwo (F.image f) (B.image f) r (f x) = regularityEnergyTwo F B r x := by
    unfold regularityEnergyTwo
    rw [← Finset.image_inter F B hf, Finset.sum_image (fun _ _ _ _ h => hf h)]
    apply Finset.sum_congr rfl
    intro y _
    rw [show latticeDistance (f x) (f y) = latticeDistance x y from
      latticeDistance_slabChart hd n e rev x y]
  unfold sourceRegularPoint
  rw [h₁,h₂, ← Finset.image_inter F B hf, Finset.mem_image]
  have hm : (∃ y ∈ F ∩ B, f y = f x) ↔ x ∈ F ∩ B := by
    constructor
    · rintro ⟨y, hy, he⟩
      exact hf he ▸ hy
    · exact fun hx => ⟨x,hx,rfl⟩
  rw [hm]

end NearCritical
