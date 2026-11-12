module

public import NearCritical.SlabResampledNestInputs

/-! The fixed set of the slab resampling, and where the second copy is read.

* `slabStripBonds n A Bx`: ambient bonds lying in some tube of the box and inside
  some cube of the box (the strips).
* `slabKfix n A R` := cube bonds that are NOT strip bonds. With this fixed set the
  resampled configuration keeps the first copy on every non-strip cube bond.
* `resample_second_copy_in_strip`: every critical-layer index at which
  `resampleLayers` (with `Kfix = slabKfix`) reads the SECOND sample belongs to
  `slabStripBlocks … (inr e)` for some tube `e`. So the configuration `rsCfg`
  depends on the second sample only through bits owned by tube blocks.
* `resample_first_copy_off_strip`: at every other index it reads the first sample.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open scoped Classical
open Section10

variable {d : ℕ}

/-- Ambient bonds in a tube of the box and inside a cube of the box. -/
def slabStripBonds (n : ℕ) (A : Finset (Bond d)) (Bx : Finset (Vertex 2)) : Finset (Bond d) :=
  A.filter fun b => ∃ e : boxBonds Bx, bondIn (slabTube n e.1.1 e.1.2) b ∧
    ∃ v ∈ Bx, bondIn (slabCube n v) b

/-- Cube bonds outside the strips. -/
def slabKfix (n : ℕ) (A : Finset (Bond d)) (R : ℕ) : Finset (Bond d) :=
  cubeBonds (centeredBox 2 R) (fun v => typicalCube n (coarseShift (d := d) n v)) \
    slabStripBonds n A (centeredBox 2 R)

lemma slabKfix_subset (n : ℕ) (A : Finset (Bond d)) (R : ℕ) :
    slabKfix n A R ⊆
      cubeBonds (centeredBox 2 R) (fun v => typicalCube n (coarseShift (d := d) n v)) :=
  Finset.sdiff_subset

/-- The second sample is read only on strip-block indices. -/
theorem resample_second_copy_in_strip (n : ℕ) (A : Finset (Bond d)) (R : ℕ) (cc : ℝ)
    (ω : Bond d × Bool → Bool) (x : Bond d × Bool)
    (hx : x ∈ layerSet (cubeBonds (centeredBox 2 R)
      (fun v => typicalCube n (coarseShift (d := d) n v))))
    (hnot : x ∉ layerReveal (centeredBox 2 R)
      (fun v => typicalCube n (coarseShift (d := d) n v))
      (fun v => typicalHeart n (coarseShift (d := d) n v) cc) (slabKfix n A R) ω) :
    ∃ e : boxBonds (centeredBox 2 R),
      x ∈ slabStripBlocks (d := d) n A (centeredBox 2 R) (Sum.inr e) := by
  obtain ⟨b, c⟩ := x
  obtain ⟨hc, hb⟩ := (mem_layerSet _ _).mp hx
  simp only at hc hb
  subst hc
  have hbK : b ∉ slabKfix n A R := fun hK => hnot (by
    unfold layerReveal
    exact (mem_layerSet _ _).mpr ⟨rfl, Finset.mem_union_right _ hK⟩)
  have hstrip : b ∈ slabStripBonds n A (centeredBox 2 R) := by
    by_contra hns
    exact hbK (Finset.mem_sdiff.mpr ⟨hb, hns⟩)
  obtain ⟨hbA, e, htube, v, hv, hcube⟩ := Finset.mem_filter.mp hstrip
  refine ⟨e, ?_⟩
  simp only [slabStripBlocks, Finset.mem_product, Finset.mem_filter, Finset.mem_singleton,
    and_true]
  exact ⟨hbA, htube, v, hv, hcube⟩

/-- Off the unrevealed cube bonds the composite is the first sample. -/
theorem resample_first_copy_off_strip (s : Finset (Vertex 2)) (Q H : Vertex 2 → Finset (Vertex d))
    (Kfix : Finset (Bond d)) (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (x : Bond d × Bool)
    (hx : ¬ (x ∈ layerSet (cubeBonds s Q) ∧ x ∉ layerReveal s Q H Kfix q.1)) :
    resampleLayers s Q H Kfix q x = q.1 x := by
  unfold resampleLayers resampleOn
  rw [if_neg hx]

end NearCritical
