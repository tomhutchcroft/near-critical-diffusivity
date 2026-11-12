module

public import NearCritical.SlabResampleConfig
public import NearCritical.SlabStripBlocks
public import NearCritical.Section10PreGoodCombine

/-! Site-step probability: a cube block under the two-layer law sees critical
percolation.

* `criticalLayer_law`: the critical layer of a two-layer sample has law `P_a`.
* `blockConfig B y`: the configuration read from a block (closed elsewhere).
* `block_prob_eq_percolation`: if an event `G` depends only on a finite set `T`
  of bonds whose critical-layer indices lie in the block `B`, then the block law
  gives `{y | blockConfig B y ∈ G}` probability `P_a[G]`.
* `cubeBlock_pregood_prob`: for the slab cube block (ambient bonds containing the
  cube), the probability that the cube is pre-good is the critical probability
  `P_a[IsPreGoodCube typ n (coarseShift n v)]`.

So the site and root bounds of the slab nest rule reduce to the pre-good
probability at `p_c` (prop.proba.pregood).
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set ProbabilityTheory
open scoped Classical
open Section10

variable {d : ℕ}

lemma measurable_criticalLayer : Measurable (criticalLayer (d := d)) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem criticalLayer_law (a s : I) :
    Measure.map criticalLayer (Measure.infinitePi (sprinkleLaw (d := d) a s)) =
      percolation d a := by
  have hf : Function.Injective (fun e : Bond d => ((e, true) : Bond d × Bool)) :=
    fun e e' h => (Prod.mk.inj h).1
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := sprinkleLaw (d := d) a s) hf
  have hμ : (fun e : Bond d => sprinkleLaw (d := d) a s (e, true)) =
      fun _ : Bond d => bernoulliMeasure true false a := by
    funext e
    simp [sprinkleLaw]
  rw [hμ] at h
  exact h

/-- Configuration read from a block; closed off the block. -/
def blockConfig (B : Finset (Bond d × Bool)) (y : B → Bool) : Configuration d :=
  fun b => if h : (b, true) ∈ B then y ⟨(b, true), h⟩ else false

theorem block_prob_eq_percolation (a s : I) (B : Finset (Bond d × Bool))
    (G : Set (Configuration d)) (hG : MeasurableSet G) (T : Finset (Bond d))
    (hT : ∀ b ∈ T, ((b, true) : Bond d × Bool) ∈ B)
    (hloc : ∀ ω η : Configuration d, (∀ b ∈ T, ω b = η b) → (ω ∈ G ↔ η ∈ G)) :
    Measure.pi (fun e : B => sprinkleLaw a s (e : Bond d × Bool)) {y | blockConfig B y ∈ G} =
      percolation d a G := by
  have hr : Measure.map (Finset.restrict B) (Measure.infinitePi (sprinkleLaw (d := d) a s)) =
      Measure.pi (fun e : B => sprinkleLaw a s (e : Bond d × Bool)) :=
    Measure.infinitePi_map_restrict _
  rw [← criticalLayer_law a s, Measure.map_apply measurable_criticalLayer hG, ← hr,
    Measure.map_apply (Finset.measurable_restrict B) MeasurableSet.of_discrete]
  congr 1
  ext ω
  simp only [mem_preimage, mem_setOf_eq]
  refine hloc _ _ fun b hb => ?_
  unfold blockConfig criticalLayer
  rw [dif_pos (hT b hb)]
  rfl

theorem cubeBlock_pregood_prob {n : ℕ} (hn : 0 < n) (a s : I) (A : Finset (Bond d))
    (Bx : Finset (Vertex 2)) (v : Bx) (typ : TypicalParameters)
    (hA : ∀ b : Bond d, bondIn (slabCube n v.1) b → b ∈ A) :
    Measure.pi (fun e : slabSprinkleBlocks (d := d) n A Bx (Sum.inl v) =>
        sprinkleLaw a s (e : Bond d × Bool))
      {y | IsPreGoodCube typ n (coarseShift (d := d) n v.1) (blockConfig _ y)} =
    percolation d a {ω | IsPreGoodCube typ n (coarseShift (d := d) n v.1) ω} := by
  refine block_prob_eq_percolation a s _ {ω | IsPreGoodCube typ n (coarseShift (d := d) n v.1) ω}
    (measurableSet_isPreGoodCube typ n _)
    (internalBondSet (typicalCube n (coarseShift (d := d) n v.1))) ?_
    (fun ω η h => isPreGoodCube_iff_of_internal_agree typ n _ ω η h)
  intro b hb
  have hin := (internalBond_iff_bondIn hn v.1 b).mp hb
  simp only [slabSprinkleBlocks, Finset.mem_product, Finset.mem_filter, Finset.mem_singleton,
    and_true]
  exact ⟨hA b hin, hin⟩

end NearCritical
