module

public import NearCritical.SlabChartFaces
public import NearCritical.SlabStepBoundaryData

/-! The regular patches read by the slab rule are the chart images of
the regular patches of the first-copy cube clusters. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

theorem mem_chartCluster_apply {d : ℕ} (φ : Vertex d ≃ Vertex d) (C : Finset (Vertex d))
    (x : Vertex d) : φ x ∈ chartCluster φ C ↔ x ∈ C := by
  simp [chartCluster, Finset.mem_map_equiv]

theorem chartCluster_eq_of_mem {d : ℕ} (φ : Vertex d ≃ Vertex d) (C C' : Finset (Vertex d))
    (h : ∀ x, φ x ∈ C' ↔ x ∈ C) : chartCluster φ C = C' := by
  ext y
  obtain ⟨x,rfl⟩ := φ.surjective y
  rw [mem_chartCluster_apply, h]

theorem chartCluster_card {d : ℕ} (φ : Vertex d ≃ Vertex d) (C : Finset (Vertex d)) :
    (chartCluster φ C).card = C.card :=
  Finset.card_map _

theorem chartCluster_image_card {d : ℕ} (φ : Vertex d ≃ Vertex d)
    (C : Finset (Finset (Vertex d))) :
    (C.image (chartCluster φ)).card = C.card :=
  Finset.card_image_of_injective _ (chartCluster_injective φ)

theorem slabRegularPatch_chart {d : ℕ} (hd : 2 ≤ d) (typ : TypicalParameters)
    {n : ℕ} (hn : 0 < n) (e : Bond 2) (rev : Bool) (c : Vertex d)
    (F C : Finset (Vertex d)) (sign plus : Bool) :
    let φ := slabChartEquiv hd n e rev
    let i := Fin.castLE hd e.2
    chartCluster φ (slabRegularPatch typ n c F C (i, sign) plus) =
      slabRegularPatch typ n (φ c) (chartCluster φ F) (chartCluster φ C)
        (i, if rev then !sign else sign) plus := by
  intro φ i
  have hI : chartCluster φ (typicalInnerCube n c) = typicalInnerCube n (φ c) :=
    chartCluster_eq_of_mem φ _ _ (fun x => by
      simpa only [φ, slabChartEquiv_apply] using mem_typicalInnerCube_slabChart_iff hd hn e rev x c)
  have hB : chartCluster φ (typicalBoundary n c) = typicalBoundary n (φ c) :=
    chartCluster_eq_of_mem φ _ _ (fun x => by
      simpa only [φ, slabChartEquiv_apply] using mem_typicalBoundary_slabChart_iff hd hn e rev x c)
  have hImage (U : Finset (Vertex d)) : U.image (slabChartVertex hd n e rev) = chartCluster φ U := by
    rw [chartCluster, Finset.map_eq_image]
    exact congrArg (fun g : Vertex d → Vertex d => U.image g)
      (funext fun x => (slabChartEquiv_apply hd n e rev x).symm)
  apply chartCluster_eq_of_mem
  intro x
  have hreg := sourceRegularPoint_slabChart_iff hd n e rev F (typicalInnerCube n c)
    (typicalBoundary n c) typ.regularRadius typ.regularTolerance x
  change sourceRegularPoint (F.image _) ((typicalInnerCube n c).image _)
    ((typicalBoundary n c).image _) _ _ (slabChartVertex hd n e rev x) ↔ _ at hreg
  rw [hImage, hImage, hImage, hI, hB, ← slabChartEquiv_apply] at hreg
  change sourceRegularPoint (chartCluster φ F) (typicalInnerCube n (φ c)) (typicalBoundary n (φ c))
    typ.regularRadius typ.regularTolerance (φ x) ↔ _ at hreg
  have hface : φ x ∈ typicalSplitFace n (φ c) (i, if rev then !sign else sign) plus ↔
      x ∈ typicalSplitFace n c (i, sign) plus := by
    simpa only [φ, slabChartEquiv_apply] using mem_typicalSplitFace_slabChart_axis_iff hd hn e rev x c sign plus
  simp only [slabRegularPatch, Finset.mem_filter, Finset.mem_inter, mem_chartCluster_apply, hface, hreg]

theorem slabRegularPatch_chart_card {d : ℕ} (hd : 2 ≤ d) (typ : TypicalParameters)
    {n : ℕ} (hn : 0 < n) (e : Bond 2) (rev : Bool) (c : Vertex d)
    (F C : Finset (Vertex d)) (sign plus : Bool) :
    let φ := slabChartEquiv hd n e rev
    let i := Fin.castLE hd e.2
    (slabRegularPatch typ n (φ c) (chartCluster φ F) (chartCluster φ C)
      (i, if rev then !sign else sign) plus).card =
    (slabRegularPatch typ n c F C (i, sign) plus).card := by
  intro φ i
  rw [← slabRegularPatch_chart hd typ hn e rev c F C sign plus, chartCluster_card]

theorem slabRegularPatch_pullback_card {d : ℕ} (hd : 2 ≤ d) (typ : TypicalParameters)
    {n : ℕ} (hn : 0 < n) (e : Bond 2) (rev : Bool) (c : Vertex d)
    (F C : Finset (Vertex d)) (sign plus : Bool) :
    let φ := slabChartEquiv hd n e rev
    let i := Fin.castLE hd e.2
    (slabRegularPatch typ n c (chartCluster φ.symm F) (chartCluster φ.symm C)
      (i, sign) plus).card =
    (slabRegularPatch typ n (φ c) F C (i, if rev then !sign else sign) plus).card := by
  intro φ i
  have h := slabRegularPatch_chart_card hd typ hn e rev c
    (chartCluster φ.symm F) (chartCluster φ.symm C) sign plus
  change (slabRegularPatch typ n (φ c) (chartCluster φ (chartCluster φ.symm F))
    (chartCluster φ (chartCluster φ.symm C)) (i, if rev then !sign else sign) plus).card = _ at h
  have hF : chartCluster φ (chartCluster φ.symm F) = F := by
    simpa only [Equiv.symm_symm] using chartCluster_symm φ.symm F
  have hC : chartCluster φ (chartCluster φ.symm C) = C := by
    simpa only [Equiv.symm_symm] using chartCluster_symm φ.symm C
  rw [hF,hC] at h
  exact h.symm

end NearCritical
