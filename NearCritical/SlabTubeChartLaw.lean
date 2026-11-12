module

public import NearCritical.SlabStepOffspring

/-! The edge rule can compute in the coordinate system of the parent cube.
This allows both orientations of a coarse edge to use the origin estimate. -/
@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Section10
open scoped Classical

/-- Restrict both layers along a bond map. -/
def pullbackLayerPair {d : ℕ} (f : Bond d → Bond d)
    (z : Configuration d × Configuration d) : Configuration d × Configuration d :=
  (z.1 ∘ f, z.2 ∘ f)

theorem slab_tubeBlock_chart_prob_eq {d : ℕ} (n R : ℕ) (A : Finset (Bond d))
    (e : boxBonds (centeredBox 2 R)) (a s : I)
    (f : Bond d → Bond d) (hf : Function.Injective f) (U : Finset (LBond d))
    (hU : ∀ k ∈ U, f k.2 ∈ A ∧ bondIn (slabTube n e.1.1 e.1.2) (f k.2))
    (P : Configuration d × Configuration d → Prop) (hP : ReadsOnly U P) :
    (rsν d n A R a s (Sum.inr e))
      {y | P (pullbackLayerPair f (slabTubePair n A R e y))} =
    ((percolation d a).prod (percolation d s)) {z | P z} := by
  let Bx := centeredBox 2 R
  let B₁ := slabSprinkleBlocks n A Bx (Sum.inr e)
  let B₂ := slabStripBlocks n A Bx (Sum.inr e)
  let T := A.filter (bondIn (slabTube n e.1.1 e.1.2))
  let G : Set (Configuration d × Configuration d) := {z | P z}
  let g : Configuration d → Configuration d := fun z => z ∘ f
  have hg : Measurable g := measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hgmap (p : I) : Measure.map g (percolation d p) = percolation d p := by
    unfold percolation
    exact Measure.map_infinitePi_infinitePi_of_inj hf
  have hmap : Measure.map (pullbackLayerPair f) ((percolation d a).prod (percolation d s)) =
      (percolation d a).prod (percolation d s) := by
    change Measure.map (Prod.map g g) _ = _
    rw [← Measure.map_prod_map _ _ hg hg, hgmap, hgmap]
  have hmeas : Measurable (pullbackLayerPair f) := hg.prodMap hg
  have hG : MeasurableSet G := hP.measurableSet
  have hTc : ∀ b ∈ T, ((b,true) : Bond d × Bool) ∈ B₁ ∨ ((b,true) : Bond d × Bool) ∈ B₂ := by
    intro b hb
    obtain ⟨hbA, hbT⟩ := Finset.mem_filter.mp hb
    by_cases hC : ∃ v ∈ Bx, bondIn (slabCube n v) b
    · right
      simp [B₂, slabStripBlocks, hbA, hbT, hC]
    · left
      have hC' : ∀ v ∈ Bx, ¬ bondIn (slabCube n v) b := fun v hv h => hC ⟨v,hv,h⟩
      simpa [B₁, slabSprinkleBlocks, hbA, hbT] using hC'
  have hTs : ∀ b ∈ T, ((b,false) : Bond d × Bool) ∈ B₁ ∧ ((b,false) : Bond d × Bool) ∉ B₂ := by
    intro b hb
    obtain ⟨hbA, hbT⟩ := Finset.mem_filter.mp hb
    simp [B₁, B₂, slabSprinkleBlocks, slabStripBlocks, hbA, hbT]
  have hloc (z z' : Configuration d × Configuration d) (hc : ∀ b ∈ T, z.1 b = z'.1 b)
      (hs : ∀ b ∈ T, z.2 b = z'.2 b) :
      z ∈ pullbackLayerPair f ⁻¹' G ↔ z' ∈ pullbackLayerPair f ⁻¹' G := by
    change P (pullbackLayerPair f z) ↔ P (pullbackLayerPair f z')
    apply Iff.of_eq
    apply hP
    rintro ⟨j, b⟩ hb
    have hbT : f b ∈ T := Finset.mem_filter.mpr (hU _ hb)
    cases j
    · exact hc _ hbT
    · exact hs _ hbT
  have h := tubeBlock_prob_eq_prod a s B₁ B₂ (pullbackLayerPair f ⁻¹' G)
    (hmeas hG) T T hTc hTs hloc
  change _ = ((percolation d a).prod (percolation d s)) G
  rw [← hmap, Measure.map_apply hmeas hG]
  exact h

end NearCritical
