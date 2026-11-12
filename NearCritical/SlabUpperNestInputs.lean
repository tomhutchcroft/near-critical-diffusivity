module

public import NearCritical.ExplorationNestInvariant
public import NearCritical.SlabUpperRunInvariant

/-! prop.slab.upper from a NEST RULE on the slab blocks.

`SlabNestInputs d n R a s S F κ` packages, on the coarse box `centeredBox 2 R`
with the literal blocks `slabSprinkleBlocks n A`:
* a `NestRule` (root nest, site test, child nest through a tube);
* the three per-step bounds (root nest exists, site test passes, child nest
  exists for EVERY parent nest), each for every sample with only the fresh block
  resampled;
* a semantic predicate `Q ω v ℓ` holding for the root nest, propagated by the
  child-nest step into a cube that passed the site test, and implying
  `slabNestJoined`.

`SlabNestInputs.reachFar_ge`: `θ <= P_{a or s}[reach far at scale 2nR - n]`.
`slab_upper_of_nestInputs`: prop.slab.upper, `p_c(slab) - p_c <= C/n^2`, from
such inputs at `p = p_c + lam/n^2` and the cited planar mixed input.

The per-step bound is NOT proved here.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Function
open scoped ENNReal Classical

variable {d : ℕ}

structure SlabNestInputs (d n R : ℕ) (a s : I) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (κ : Measure Bool) where
  A : Finset (Bond d)
  L : Type
  Ru : NestRule (centeredBox 2 R) (boxBonds (centeredBox 2 R))
    (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R)
    (fun i => slabSprinkleBlocks (d := d) n A (centeredBox 2 R) i → Bool) L
  proot : ∀ x : ∀ j, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) j → Bool,
    κ {true} ≤ Measure.pi (fun e : slabSprinkleBlocks (d := d) n A (centeredBox 2 R) (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R)) =>
        sprinkleLaw a s (e : Bond d × Bool))
      {y | (Ru.rootNest (update x (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R)) y)).isSome = true}
  psite : ∀ z (x : ∀ j, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) j → Bool),
    κ {true} ≤ Measure.pi (fun e : slabSprinkleBlocks (d := d) n A (centeredBox 2 R) (Sum.inl z) =>
        sprinkleLaw a s (e : Bond d × Bool))
      {y | Ru.siteOK z (update x (Sum.inl z) y) = true}
  pedge : ∀ e z ℓ (x : ∀ j, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) j → Bool),
    κ {true} ≤ Measure.pi (fun e' : slabSprinkleBlocks (d := d) n A (centeredBox 2 R) (Sum.inr e) =>
        sprinkleLaw a s (e' : Bond d × Bool))
      {y | (Ru.childNest e z ℓ (update x (Sum.inr e) y)).isSome = true}
  Q : (Bond d × Bool → Bool) → centeredBox 2 R → L → Prop
  rootQ : ∀ ω ℓ, Ru.rootNest (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = some ℓ →
    Q ω ⟨0, zero_mem_centeredBox_two R⟩ ℓ
  rootSite : ∀ ω ℓ,
    Ru.rootNest (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = some ℓ →
    Ru.siteOK (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R)
      (blockFamily (X := fun _ => Bool) (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true
  edgeQ : ∀ ω e z ℓ ℓ',
    Ru.siteOK z
      (blockFamily (X := fun _ => Bool) (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
    Q ω (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ →
    Ru.childNest e z ℓ (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = some ℓ' →
    Q ω z ℓ'
  join : ∀ ω v ℓ, Q ω v ℓ → slabNestJoined n S F (sprinkleConfiguration ω) (v : Vertex 2)

theorem SlabNestInputs.reachFar_ge (hd : 2 ≤ d) {n R : ℕ} (hn : 0 < n) {a s : I}
    {S : Set (Vertex d)} {F : Finset (Vertex d)} {κ : Measure Bool} [IsProbabilityMeasure κ]
    {θ : ℝ≥0∞} (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (X : SlabNestInputs d n R a s S F κ) :
    θ ≤ percolation d (orParameter a s) (restrictedReachFarEvent S F (2 * n * R - n)) := by
  refine reachFar_ge_of_nestRule (boxEnds (centeredBox 2 R))
    (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) (boxInnerBoundary (centeredBox 2 R))
    (Measure.infinitePi (sprinkleLaw (d := d) a s)) sprinkleConfiguration
    measurable_sprinkleConfiguration
    (by rw [orParameter_eq_symm_mul a s]; exact map_sprinkleConfiguration a s)
    (fun i => Measure.pi (fun e : slabSprinkleBlocks (d := d) n X.A (centeredBox 2 R) i =>
      sprinkleLaw a s (e : Bond d × Bool))) κ
    (blockFamily (slabSprinkleBlocks n X.A (centeredBox 2 R)))
    (measurable_blockFamily _)
    (infinitePi_map_blockFamily (sprinkleLaw a s) _
      (slabSprinkleBlocks_disjoint hd hn X.A (centeredBox 2 R)))
    X.Ru X.proot X.psite X.pedge X.Q X.rootQ X.rootSite
    (fun q e z ℓ ℓ' _ => X.edgeQ q e z ℓ ℓ') ?_
    (mixedValue_box_ge (centeredBox 2 R) (zero_mem_centeredBox_two R) κ hθ)
  intro ω v ℓ hv hQ
  obtain ⟨x, hx, w, hw, hr⟩ := X.join ω v ℓ hQ
  refine ⟨x, hx, w, ?_, hr⟩
  simp only [boxInnerBoundary, Finset.mem_filter] at hv
  obtain ⟨y, hy, hadj⟩ := hv.2
  obtain ⟨c, hc⟩ := exists_coord_abs_ge_of_innerBoundary v.2 hy hadj
  exact vertexSize_ge_of_mem_slabCube hd hc hw

/-- prop.slab.upper from nest-rule inputs at `p = p_c + lam / n^2`. -/
theorem slab_upper_of_nestInputs (hd : 2 ≤ d) {lam : ℝ} (hlam : 0 < lam) (n₀ : ℕ)
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞} (hθ0 : θ ≠ 0)
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : I,
      (p : ℝ) = (criticalPoint d : ℝ) + lam / (n : ℝ) ^ 2 →
        ∃ s : I, orParameter (criticalPoint d) s = p ∧ ∃ F : Finset (Vertex d),
          ∀ R, Nonempty (SlabNestInputs d n R (criticalPoint d) s (slabVertices d 2 n) F κ)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        C / (n : ℝ) ^ 2 := by
  refine slab_upper_inverse_square_of_reachFar hlam n₀ ?_
  intro n hn0 hn p hp
  obtain ⟨s, hsp, F, hX⟩ := hmodel n hn0 hn p hp
  refine ⟨F, θ, hθ0, fun N => ?_⟩
  have h := (hX N).some.reachFar_ge hd (by omega) hθ
  rw [hsp] at h
  exact h.trans (measure_mono
    (restrictedReachFarEvent_antitone _ F (le_two_mul_sub N n hn)))

end NearCritical
