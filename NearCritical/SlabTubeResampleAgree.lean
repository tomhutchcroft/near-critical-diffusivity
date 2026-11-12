module

public import NearCritical.SlabStepOffspring
public import NearCritical.SlabKfix
public import NearCritical.SlabTubeEndCubes

/-! On the bonds that the offspring paths can use, the local tube
sample agrees with the global resampled configuration. -/
@[expose] public section
noncomputable section

namespace NearCritical

open scoped Classical
open Section10

theorem slabTubePair_sprinkle_agrees {d : ℕ} (n R : ℕ) (A : Finset (Bond d))
    (e : boxBonds (centeredBox 2 R)) (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (b : Bond d) (hbA : b ∈ A) (hbT : bondIn (slabTube n e.1.1 e.1.2) b) :
    (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e))).2 b = q.1 (b, false) := by
  have h₁ : (b,false) ∈ slabSprinkleBlocks n A (centeredBox 2 R) (Sum.inr e) := by
    simp [slabSprinkleBlocks, hbA, hbT]
  have h₂ : (b,false) ∉ slabStripBlocks n A (centeredBox 2 R) (Sum.inr e) := by
    simp [slabStripBlocks]
  unfold slabTubePair sprinkleLayer tubeLayers
  dsimp only
  rw [dif_neg h₂, dif_pos h₁] <;> rfl

/-- A tube bond outside the two endpoint reveal masks has the same critical
bit in the tube block and the composite sample. -/
theorem slabTubePair_critical_agrees {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (R : ℕ) (A : Finset (Bond d)) (cc : ℝ) (e : boxBonds (centeredBox 2 R))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) (b : Bond d)
    (hbA : b ∈ A) (hbT : bondIn (slabTube n e.1.1 e.1.2) b)
    (hBase : b ∉ heartRevealSet (typicalCube n (coarseShift n e.1.1))
      (typicalHeart n (coarseShift n e.1.1) cc) (criticalLayer q.1))
    (hTip : b ∉ heartRevealSet (typicalCube n (coarseShift n (bondTip e.1)))
      (typicalHeart n (coarseShift n (bondTip e.1)) cc) (criticalLayer q.1)) :
    (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e))).1 b =
      resampleLayers (centeredBox 2 R) (fun v => typicalCube n (coarseShift n v))
        (fun v => typicalHeart n (coarseShift n v) cc) (slabKfix n A R) q (b,true) := by
  let Bx := centeredBox 2 R
  let Q := fun v => typicalCube n (coarseShift (d := d) n v)
  let H := fun v => typicalHeart n (coarseShift (d := d) n v) cc
  have hReveal (v : Vertex 2) : b ∉ heartRevealSet (Q v) (H v) (criticalLayer q.1) := by
    intro h
    have hbQ := (internalBond_iff_bondIn hn v b).1 (heartRevealSet_subset _ _ _ h)
    rcases slabCube_meets_slabTube hd hn hbT.1 hbQ.1 with hv | hv
    · subst v
      exact hBase h
    · subst v
      exact hTip h
  by_cases hC : ∃ v ∈ Bx, bondIn (slabCube n v) b
  · obtain ⟨v, hv, hbQ⟩ := hC
    have hb₂ : (b,true) ∈ slabStripBlocks n A Bx (Sum.inr e) := by
      simp [slabStripBlocks, hbA, hbT, show ∃ v ∈ Bx, bondIn (slabCube n v) b from ⟨v, hv, hbQ⟩]
    have hbC : (b,true) ∈ layerSet (cubeBonds Bx Q) :=
      (mem_layerSet _ _).2 ⟨rfl, Finset.mem_biUnion.mpr
        ⟨v, hv, (internalBond_iff_bondIn hn v b).2 hbQ⟩⟩
    have hbS : b ∈ slabStripBonds n A Bx :=
      Finset.mem_filter.mpr ⟨hbA, e, hbT, v, hv, hbQ⟩
    have hNot : (b,true) ∉ layerReveal Bx Q H (slabKfix n A R) q.1 := by
      intro h
      have hr := ((mem_layerSet _ _).1 h).2
      rcases Finset.mem_union.mp hr with h | h
      · obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp h
        exact hReveal w hw
      · exact (Finset.mem_sdiff.mp h).2 hbS
    unfold slabTubePair criticalLayer tubeLayers resampleLayers resampleOn
    dsimp only
    rw [dif_pos hb₂, if_pos ⟨hbC, hNot⟩] <;> rfl
  · have hC' : ∀ v ∈ Bx, ¬ bondIn (slabCube n v) b :=
      fun v hv hb => hC ⟨v, hv, hb⟩
    have hb₁ : (b,true) ∈ slabSprinkleBlocks n A Bx (Sum.inr e) := by
      simpa [slabSprinkleBlocks, hbA, hbT] using hC'
    have hb₂ : (b,true) ∉ slabStripBlocks n A Bx (Sum.inr e) := by
      simpa [slabStripBlocks, hbA, hbT] using hC
    have hbC : (b,true) ∉ layerSet (cubeBonds Bx Q) := by
      intro h
      obtain ⟨v, hv, hbQ⟩ := Finset.mem_biUnion.mp ((mem_layerSet _ _).1 h).2
      exact hC ⟨v, hv, (internalBond_iff_bondIn hn v b).1 hbQ⟩
    rw [resample_first_copy_off_strip _ _ _ _ _ _ (fun h => hbC h.1)]
    unfold slabTubePair criticalLayer tubeLayers
    dsimp only
    rw [dif_neg hb₂, dif_pos hb₁] <;> rfl

/-- The full step view, including its opened pivots, agrees with the view
computed on the composite layers. Each half tube excludes the opposite cube. -/
theorem slab_stepView_resample_eq {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (R : ℕ) (A : Finset (Bond d)) (cc : ℝ) (e : boxBonds (centeredBox 2 R))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) (M L V : Finset (Vertex d))
    (hM : (M : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hL : (L : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hV : (V : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hA : ∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A) :
    let Q := fun v => typicalCube n (coarseShift (d := d) n v)
    let H := fun v => typicalHeart n (coarseShift (d := d) n v) cc
    let F := fun v => heartClusterUnion (criticalLayer q.1) (Q v) (H v)
    let u := e.1.1
    let v := bondTip e.1
    let ω := resampleLayers (centeredBox 2 R) Q H (slabKfix n A R) q
    Disjoint L (Q v) → Disjoint V (Q u) → Disjoint M (Q u) → Disjoint M (Q v) →
      stepView M L V (Q u) (F u) (Q v) (F v) (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e))) =
        stepView M L V (Q u) (F u) (Q v) (F v) (criticalLayer ω, sprinkleLayer q.1) := by
  intro Q H F u v ω hLV hVu hMu hMv
  apply stepView_readsOnly
  have hTube {U : Finset (Vertex d)} {b : Bond d}
      (hU : (U : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
      (hb : b ∈ internalBondSet U) : bondIn (slabTube n e.1.1 e.1.2) b :=
    ⟨hU ((mem_internalBondSet U b).mp hb).1, hU ((mem_internalBondSet U b).mp hb).2⟩
  have hAvoid {U : Finset (Vertex d)} {b : Bond d} {w : Vertex 2}
      (hU : Disjoint U (Q w)) (hb : b ∈ internalBondSet U) :
      b ∉ heartRevealSet (Q w) (H w) (criticalLayer q.1) := fun h =>
    Finset.disjoint_left.mp hU ((mem_internalBondSet U b).mp hb).1
      ((mem_internalBondSet (Q w) b).mp (heartRevealSet_subset _ _ _ h)).1
  have hCritical (b : Bond d) (hb : bondIn (slabTube n e.1.1 e.1.2) b)
      (hbu : b ∉ heartRevealSet (Q u) (H u) (criticalLayer q.1))
      (hbv : b ∉ heartRevealSet (Q v) (H v) (criticalLayer q.1)) :
      (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e))).1 b = criticalLayer ω b :=
    slabTubePair_critical_agrees hd hn R A cc e q b (hA b hb) hb hbu hbv
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_union.mp hb with hb | hb
    · rcases Finset.mem_union.mp hb with hb | hb
      · obtain ⟨hi, hr⟩ := Finset.mem_sdiff.mp hb
        exact hCritical b (hTube hL hi) hr (hAvoid hLV hi)
      · obtain ⟨hi, hr⟩ := Finset.mem_sdiff.mp hb
        exact hCritical b (hTube hV hi) (hAvoid hVu hi) hr
    · exact hCritical b (hTube hM hb) (hAvoid hMu hb) (hAvoid hMv hb)
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
    exact slabTubePair_sprinkle_agrees n R A e q b (hA b (hTube hM hb)) (hTube hM hb)

end NearCritical
