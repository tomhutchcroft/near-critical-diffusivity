module

public import NearCritical.SlabUpperShiftedSlab
public import NearCritical.SlabResampleConfig
public import NearCritical.ProductBlockLaw
public import NearCritical.SlabStripBlocks

/-! prop.slab.upper from a nest rule on the RESAMPLED slab sample.

Sample: two independent two-layer samples `(ω, ω')`. Configuration
`rsCfg`: the critical layer of `ω`, with the bits of cube bonds not revealed by
the heart clusters (and not in the fixed set `Kfix`) replaced by those of `ω'`,
OR-ed with the sprinkle layer of `ω`. Blocks `rsΦ`: block `i` reads `ω` on
`slabSprinkleBlocks i` and `ω'` on `slabStripBlocks i`.

`ResampledSlabNestInputs` packages a `NestRule` on these blocks with its three
per-step bounds and a propagated predicate implying `slabNestJoined` for
`rsCfg`. `ResampledSlabNestInputs.reachFar_ge` and
`slab_upper_of_resampledNestInputs` (in the shifted slab, then translated)
conclude prop.slab.upper. This is the version of `SlabNestInputs` in which a
tube step can read the unrevealed critical bits of its strips, as in the source
(main.tex 4054-4075, 6086-6088).

The per-step bounds are NOT proved here.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Function
open scoped ENNReal Classical
open Section10

variable {d : ℕ}

/-- Block sample space of the resampled slab sample. -/
abbrev rsΩ (d n : ℕ) (A : Finset (Bond d)) (R : ℕ)
    (i : centeredBox 2 R ⊕ boxBonds (centeredBox 2 R)) : Type :=
  (slabSprinkleBlocks (d := d) n A (centeredBox 2 R) i → Bool) ×
    (slabStripBlocks (d := d) n A (centeredBox 2 R) i → Bool)

/-- Block laws. -/
abbrev rsν (d n : ℕ) (A : Finset (Bond d)) (R : ℕ) (a s : I)
    (i : centeredBox 2 R ⊕ boxBonds (centeredBox 2 R)) : Measure (rsΩ d n A R i) :=
  (Measure.pi fun e : slabSprinkleBlocks (d := d) n A (centeredBox 2 R) i =>
      sprinkleLaw a s (e : Bond d × Bool)).prod
    (Measure.pi fun e : slabStripBlocks (d := d) n A (centeredBox 2 R) i =>
      sprinkleLaw a s (e : Bond d × Bool))

/-- Block map. -/
def rsΦ (d n : ℕ) (A : Finset (Bond d)) (R : ℕ)
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) :
    ∀ i, rsΩ d n A R i :=
  fun i => (blockFamily (X := fun _ => Bool) (slabSprinkleBlocks n A (centeredBox 2 R)) q.1 i,
    blockFamily (X := fun _ => Bool) (slabStripBlocks n A (centeredBox 2 R)) q.2 i)

/-- The resampled configuration. -/
def rsCfg (d n R : ℕ) (cc : ℝ) (Kfix : Finset (Bond d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) : Configuration d :=
  sprinkleConfiguration (resampleLayers (centeredBox 2 R)
    (fun v => typicalCube n (coarseShift (d := d) n v))
    (fun v => typicalHeart n (coarseShift (d := d) n v) cc) Kfix q)

structure ResampledSlabNestInputs (d n R : ℕ) (a s : I) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (κ : Measure Bool) where
  A : Finset (Bond d)
  cc : ℝ
  Kfix : Finset (Bond d)
  hK : Kfix ⊆ cubeBonds (centeredBox 2 R) (fun v => typicalCube n (coarseShift (d := d) n v))
  L : Type
  Ru : NestRule (centeredBox 2 R) (boxBonds (centeredBox 2 R))
    (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) (rsΩ d n A R) L
  proot : ∀ x : ∀ j, rsΩ d n A R j,
    κ {true} ≤ rsν d n A R a s (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R))
      {y | (Ru.rootNest (update x
        (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R)) y)).isSome = true}
  psite : ∀ z (x : ∀ j, rsΩ d n A R j),
    κ {true} ≤ rsν d n A R a s (Sum.inl z)
      {y | Ru.siteOK z (update x (Sum.inl z) y) = true}
  pedge : ∀ e z ℓ (x : ∀ j, rsΩ d n A R j),
    κ {true} ≤ rsν d n A R a s (Sum.inr e)
      {y | (Ru.childNest e z ℓ (update x (Sum.inr e) y)).isSome = true}
  Q : ((Bond d × Bool → Bool) × (Bond d × Bool → Bool)) → centeredBox 2 R → L → Prop
  rootQ : ∀ q ℓ, Ru.rootNest (rsΦ d n A R q) = some ℓ →
    Q q ⟨0, zero_mem_centeredBox_two R⟩ ℓ
  rootSite : ∀ q ℓ, Ru.rootNest (rsΦ d n A R q) = some ℓ →
    Ru.siteOK (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) (rsΦ d n A R q) = true
  edgeQ : ∀ q e z ℓ ℓ',
    (z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) →
    Ru.siteOK z (rsΦ d n A R q) = true →
    Q q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ →
    Ru.childNest e z ℓ (rsΦ d n A R q) = some ℓ' → Q q z ℓ'
  join : ∀ q v ℓ, Q q v ℓ → slabNestJoined n S F (rsCfg d n R cc Kfix q) (v : Vertex 2)

theorem ResampledSlabNestInputs.reachFar_ge (hd : 2 ≤ d) {n R : ℕ} (hn : 0 < n) {a s : I}
    {S : Set (Vertex d)} {F : Finset (Vertex d)} {κ : Measure Bool} [IsProbabilityMeasure κ]
    {θ : ℝ≥0∞} (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (X : ResampledSlabNestInputs d n R a s S F κ) :
    θ ≤ percolation d (orParameter a s) (restrictedReachFarEvent S F (2 * n * R - n)) := by
  have hH : ∀ v ∈ centeredBox 2 R,
      typicalHeart n (coarseShift (d := d) n v) X.cc ⊆ typicalCube n (coarseShift (d := d) n v) :=
    fun v _ => Finset.filter_subset _ _
  have hlaw := resampleLayers_law (centeredBox 2 R)
    (fun v => typicalCube n (coarseShift (d := d) n v))
    (fun v => typicalHeart n (coarseShift (d := d) n v) X.cc) hH X.Kfix X.hK a s
  have hblocks := productBlocks_law (sprinkleLaw (d := d) a s)
    (slabSprinkleBlocks n X.A (centeredBox 2 R)) (slabStripBlocks n X.A (centeredBox 2 R))
    (slabSprinkleBlocks_disjoint hd hn X.A (centeredBox 2 R))
    (slabStripBlocks_disjoint hd hn X.A (centeredBox 2 R))
  refine reachFar_ge_of_nestRule (boxEnds (centeredBox 2 R))
    (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) (boxInnerBoundary (centeredBox 2 R))
    ((Measure.infinitePi (sprinkleLaw (d := d) a s)).prod
      (Measure.infinitePi (sprinkleLaw (d := d) a s)))
    (rsCfg d n R X.cc X.Kfix) (measurable_sprinkleConfiguration.comp hlaw.1)
    (resampledConfig_law (centeredBox 2 R) _ _ hH X.Kfix X.hK a s)
    (rsν d n X.A R a s) κ (rsΦ d n X.A R) hblocks.1 hblocks.2
    X.Ru X.proot X.psite X.pedge X.Q X.rootQ X.rootSite X.edgeQ ?_
    (mixedValue_box_ge (centeredBox 2 R) (zero_mem_centeredBox_two R) κ hθ)
  intro q v ℓ hv hQ
  obtain ⟨x, hx, w, hw, hr⟩ := X.join q v ℓ hQ
  refine ⟨x, hx, w, ?_, hr⟩
  simp only [boxInnerBoundary, Finset.mem_filter] at hv
  obtain ⟨y, hy, hadj⟩ := hv.2
  obtain ⟨c, hc⟩ := exists_coord_abs_ge_of_innerBoundary v.2 hy hadj
  exact vertexSize_ge_of_mem_slabCube hd hc hw

/-- prop.slab.upper from resampled nest-rule inputs in the shifted slab. -/
theorem slab_upper_of_resampledNestInputs (hd : 2 ≤ d) {lam : ℝ} (hlam : 0 < lam) (n₀ : ℕ)
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞} (hθ0 : θ ≠ 0)
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : I,
      (p : ℝ) = (criticalPoint d : ℝ) + lam / (n : ℝ) ^ 2 →
        ∃ s : I, orParameter (criticalPoint d) s = p ∧ ∃ F : Finset (Vertex d),
          ∀ R, Nonempty (ResampledSlabNestInputs d n R (criticalPoint d) s
            (shiftedSlab d n) F κ)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        C / (n : ℝ) ^ 2 := by
  refine slab_upper_inverse_square_of_reachFar hlam n₀ ?_
  intro n hn0 hn p hp
  obtain ⟨s, hsp, F, hX⟩ := hmodel n hn0 hn p hp
  refine ⟨F.image (fun z => slabShift d n + z), θ, hθ0, fun N => ?_⟩
  obtain ⟨N', hN'⟩ : ∃ N' : ℕ, N' = N + vertexSize (slabShift d n) := ⟨_, rfl⟩
  have h := (hX N').some.reachFar_ge hd (by omega) hθ
  rw [hsp] at h
  have h1 := h.trans (measure_mono
    (restrictedReachFarEvent_antitone _ F (le_two_mul_sub N' n hn)))
  have h2 := restrictedReachFar_translate p (slabShift d n) (shiftedSlab d n) F
    (N := N') (M := N) (by omega)
  rw [slabShift_image] at h2
  exact h1.trans h2

end NearCritical
