module

public import NearCritical.SlabLayersLaw

/-! Tube-step probability: a tube block sees the product law `P_a ⊗ P_s`.

A tube block consists of first-copy bits on a finite index set `B₁` and
second-copy bits on a finite index set `B₂` (its strips). `tubeLayers y` is the
two-layer sample read from the block: the second copy on `B₂`, the first copy on
`B₁ ∖ B₂`, closed elsewhere.

`tubeBlock_prob_eq_prod`: if an event `G` on (critical configuration, sprinkle
configuration) depends only on the critical bits of a set `Tc` of bonds whose
critical indices lie in `B₁ ∪ B₂`, and on the sprinkle bits of a set `Ts` of bonds
whose sprinkle indices lie in `B₁ ∖ B₂`, then the block law gives
`{y | (criticalLayer (tubeLayers y), sprinkleLayer (tubeLayers y)) ∈ G}`
probability `(P_a ⊗ P_s)(G)`.

This transfers estimates stated under `P_{p_c} ⊗ P_q` for fixed revealed sets
(`Section10.origin_offspring_failure_le`) to the tube blocks of the resampled
slab sample.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set ProbabilityTheory
open scoped Classical

variable {d : ℕ}

/-- Two-layer sample read from a tube block. -/
def tubeLayers (B₁ B₂ : Finset (Bond d × Bool)) (y : (B₁ → Bool) × (B₂ → Bool)) :
    Bond d × Bool → Bool :=
  fun k => if h : k ∈ B₂ then y.2 ⟨k, h⟩ else if h' : k ∈ B₁ then y.1 ⟨k, h'⟩ else false

theorem tubeBlock_prob_eq_prod (a s : I) (B₁ B₂ : Finset (Bond d × Bool))
    (G : Set (Configuration d × Configuration d)) (hG : MeasurableSet G)
    (Tc Ts : Finset (Bond d))
    (hTc : ∀ b ∈ Tc, ((b, true) : Bond d × Bool) ∈ B₁ ∨ ((b, true) : Bond d × Bool) ∈ B₂)
    (hTs : ∀ b ∈ Ts, ((b, false) : Bond d × Bool) ∈ B₁ ∧ ((b, false) : Bond d × Bool) ∉ B₂)
    (hloc : ∀ z z' : Configuration d × Configuration d, (∀ b ∈ Tc, z.1 b = z'.1 b) →
      (∀ b ∈ Ts, z.2 b = z'.2 b) → (z ∈ G ↔ z' ∈ G)) :
    ((Measure.pi fun e : B₁ => sprinkleLaw a s (e : Bond d × Bool)).prod
        (Measure.pi fun e : B₂ => sprinkleLaw a s (e : Bond d × Bool)))
      {y | (criticalLayer (tubeLayers B₁ B₂ y), sprinkleLayer (tubeLayers B₁ B₂ y)) ∈ G} =
    ((percolation d a).prod (percolation d s)) G := by
  have hr1 : Measure.map (Finset.restrict B₁) (Measure.infinitePi (sprinkleLaw (d := d) a s)) =
      Measure.pi (fun e : B₁ => sprinkleLaw a s (e : Bond d × Bool)) :=
    Measure.infinitePi_map_restrict _
  have hr2 : Measure.map (Finset.restrict B₂) (Measure.infinitePi (sprinkleLaw (d := d) a s)) =
      Measure.pi (fun e : B₂ => sprinkleLaw a s (e : Bond d × Bool)) :=
    Measure.infinitePi_map_restrict _
  have hmap : Measure.map (Prod.map (Finset.restrict B₁) (Finset.restrict B₂))
      ((Measure.infinitePi (sprinkleLaw (d := d) a s)).prod
        (Measure.infinitePi (sprinkleLaw (d := d) a s))) =
      (Measure.pi fun e : B₁ => sprinkleLaw a s (e : Bond d × Bool)).prod
        (Measure.pi fun e : B₂ => sprinkleLaw a s (e : Bond d × Bool)) := by
    rw [← Measure.map_prod_map _ _ (Finset.measurable_restrict B₁)
      (Finset.measurable_restrict B₂), hr1, hr2]
  have hpair : Measurable (fun ω : Bond d × Bool → Bool => (criticalLayer ω, sprinkleLayer ω)) :=
    measurable_criticalLayer.prodMk measurable_sprinkleLayer
  obtain ⟨hσm, hσ⟩ := resample_infinite_law (sprinkleLaw (d := d) a s) B₂
    (fun _ => (∅ : Finset (Bond d × Bool))) (fun _ => Finset.empty_subset _) (fun _ _ _ => rfl)
  have hset : Prod.map (Finset.restrict B₁) (Finset.restrict B₂) ⁻¹'
      {y | (criticalLayer (tubeLayers B₁ B₂ y), sprinkleLayer (tubeLayers B₁ B₂ y)) ∈ G} =
      resampleOn B₂ (fun _ => (∅ : Finset (Bond d × Bool))) ⁻¹'
        ((fun ω : Bond d × Bool → Bool => (criticalLayer ω, sprinkleLayer ω)) ⁻¹' G) := by
    ext q
    change (criticalLayer (tubeLayers B₁ B₂ (Prod.map (Finset.restrict B₁) (Finset.restrict B₂) q)),
        sprinkleLayer (tubeLayers B₁ B₂
          (Prod.map (Finset.restrict B₁) (Finset.restrict B₂) q))) ∈ G ↔
      (criticalLayer (resampleOn B₂ (fun _ => (∅ : Finset (Bond d × Bool))) q),
        sprinkleLayer (resampleOn B₂ (fun _ => (∅ : Finset (Bond d × Bool))) q)) ∈ G
    refine hloc _ _ (fun b hb => ?_) (fun b hb => ?_)
    · change tubeLayers B₁ B₂ (Prod.map (Finset.restrict B₁) (Finset.restrict B₂) q) (b, true) =
        resampleOn B₂ (fun _ => (∅ : Finset (Bond d × Bool))) q (b, true)
      unfold tubeLayers resampleOn
      by_cases h2 : ((b, true) : Bond d × Bool) ∈ B₂
      · rw [dif_pos h2, if_pos ⟨h2, Finset.notMem_empty _⟩]
        rfl
      · have h1 := (hTc b hb).resolve_right h2
        rw [dif_neg h2, dif_pos h1, if_neg (fun h => h2 h.1)]
        rfl
    · change tubeLayers B₁ B₂ (Prod.map (Finset.restrict B₁) (Finset.restrict B₂) q) (b, false) =
        resampleOn B₂ (fun _ => (∅ : Finset (Bond d × Bool))) q (b, false)
      unfold tubeLayers resampleOn
      obtain ⟨h1, h2⟩ := hTs b hb
      rw [dif_neg h2, dif_pos h1, if_neg (fun h => h2 h.1)]
      rfl
  calc ((Measure.pi fun e : B₁ => sprinkleLaw a s (e : Bond d × Bool)).prod
        (Measure.pi fun e : B₂ => sprinkleLaw a s (e : Bond d × Bool)))
        {y | (criticalLayer (tubeLayers B₁ B₂ y), sprinkleLayer (tubeLayers B₁ B₂ y)) ∈ G}
      = ((Measure.infinitePi (sprinkleLaw (d := d) a s)).prod
          (Measure.infinitePi (sprinkleLaw (d := d) a s)))
          (Prod.map (Finset.restrict B₁) (Finset.restrict B₂) ⁻¹'
            {y | (criticalLayer (tubeLayers B₁ B₂ y), sprinkleLayer (tubeLayers B₁ B₂ y)) ∈ G}) := by
        rw [← hmap, Measure.map_apply ((Finset.measurable_restrict B₁).prodMap
          (Finset.measurable_restrict B₂)) MeasurableSet.of_discrete]
    _ = ((Measure.infinitePi (sprinkleLaw (d := d) a s)).prod
          (Measure.infinitePi (sprinkleLaw (d := d) a s)))
          (resampleOn B₂ (fun _ => (∅ : Finset (Bond d × Bool))) ⁻¹'
            ((fun ω : Bond d × Bool → Bool => (criticalLayer ω, sprinkleLayer ω)) ⁻¹' G)) := by
        rw [hset]
    _ = (Measure.map (resampleOn B₂ (fun _ => (∅ : Finset (Bond d × Bool))))
          ((Measure.infinitePi (sprinkleLaw (d := d) a s)).prod
            (Measure.infinitePi (sprinkleLaw (d := d) a s))))
          ((fun ω : Bond d × Bool → Bool => (criticalLayer ω, sprinkleLayer ω)) ⁻¹' G) :=
        (Measure.map_apply hσm (hpair hG)).symm
    _ = (Measure.infinitePi (sprinkleLaw (d := d) a s))
          ((fun ω : Bond d × Bool → Bool => (criticalLayer ω, sprinkleLayer ω)) ⁻¹' G) := by
        rw [hσ]
    _ = (Measure.map (fun ω : Bond d × Bool → Bool => (criticalLayer ω, sprinkleLayer ω))
          (Measure.infinitePi (sprinkleLaw (d := d) a s))) G :=
        (Measure.map_apply hpair hG).symm
    _ = _ := by rw [layers_law]

end NearCritical
