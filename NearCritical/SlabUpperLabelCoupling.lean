module

public import NearCritical.SlabUpperCoupled
public import NearCritical.SlabUpperBlockLaw
public import NearCritical.SlabUpperMixedPlanar
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! Uniform-label coupling for prop.slab.upper (source sprinkling).

Each bond carries an independent uniform label `U_e ∈ [0,1]`; the `q`-configuration
is `{e : U_e ≤ q}`, so ALL levels `p_c ≤ p` live on one space, monotonically.
* `map_labelConfiguration`: the `p`-configuration has law `percolation d p`.
* `labelConfiguration_mono`: `q ≤ q'` ⇒ `q`-open ⇒ `q'`-open.
* `infinitePi_map_blockLabels`: labels on pairwise-disjoint finite bond blocks are
  independent with product-uniform law (generic `μ`).
* `coupledRenormalizedExploration_of_labelBlocks`: label blocks on a ℤ² box +
  grimmett1999 input + success rule (may read p_c- AND p-level information of
  revealed blocks) + nest semantics ⇒ `CoupledRenormalizedExploration`. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory ProbabilityTheory Finset unitInterval
open scoped ENNReal

variable {d : ℕ}

/-! Generic block law for i.i.d. coordinates. -/

def blockLabels {ι α : Type*} (B : ι → Finset (Bond d)) (ω : Bond d → α) : ∀ i, B i → α :=
  fun _ e => ω e

lemma measurable_blockLabels {ι α : Type*} [MeasurableSpace α] (B : ι → Finset (Bond d)) :
    Measurable (blockLabels (α := α) B) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem infinitePi_map_blockLabels {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (B : ι → Finset (Bond d)) (hB : Pairwise fun i j => Disjoint (B i) (B j)) :
    Measure.map (blockLabels B) (Measure.infinitePi fun _ : Bond d => μ) =
      Measure.pi (fun i => Measure.pi (fun _ : B i => μ)) := by
  have hf : Function.Injective (fun s : (Σ i, B i) => (s.2 : Bond d)) :=
    Subtype.val_injective.comp (blockSigmaEquiv B hB).injective
  have h1 : Measure.map (fun (ω : Bond d → α) (s : Σ i, B i) => ω s.2)
      (Measure.infinitePi fun _ : Bond d => μ) =
      Measure.infinitePi (fun _ : (Σ i, B i) => μ) :=
    Measure.map_infinitePi_infinitePi_of_inj hf
  have h2 : Measure.map (MeasurableEquiv.piCurry (fun (i : ι) (_ : B i) => α))
      (Measure.infinitePi (fun _ : (Σ i, B i) => μ)) =
      Measure.infinitePi (fun i : ι => Measure.infinitePi (fun _ : B i => μ)) :=
    Measure.infinitePi_map_piCurry (fun (i : ι) (_ : B i) => μ)
  have hg : Measurable (fun (ω : Bond d → α) (s : Σ i, B i) => ω s.2) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hcomp : blockLabels (α := α) B =
      (MeasurableEquiv.piCurry (fun (i : ι) (_ : B i) => α)) ∘
        (fun (ω : Bond d → α) (s : Σ i, B i) => ω s.2) := rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) hg, h1, h2]
  simp_rw [Measure.infinitePi_eq_pi]

/-! Threshold coupling. -/

def labelThreshold (p : I) (u : I) : Bool := decide (u ≤ p)

lemma labelThreshold_preimage_true (p : I) : labelThreshold p ⁻¹' {true} = Set.Iic p := by
  ext u
  simp [labelThreshold]

lemma labelThreshold_preimage_false (p : I) : labelThreshold p ⁻¹' {false} = Set.Ioi p := by
  ext u
  simp [labelThreshold]

lemma measurable_labelThreshold (p : I) : Measurable (labelThreshold p) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · rw [labelThreshold_preimage_false]
    exact measurableSet_Ioi
  · rw [labelThreshold_preimage_true]
    exact measurableSet_Iic

lemma coe_toNNReal_eq_ofReal (q : I) :
    ((unitInterval.toNNReal q : NNReal) : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := by
  simpa only [unitInterval.coe_toNNReal] using
    (ENNReal.ofReal_coe_nnreal (p := unitInterval.toNNReal q)).symm

theorem map_labelThreshold (p : I) :
    (volume : Measure I).map (labelThreshold p) = bernoulliMeasure true false p := by
  classical
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_labelThreshold p) (measurableSet_singleton b),
    bernoulliMeasure_apply p (measurableSet_singleton b)]
  cases b
  · rw [labelThreshold_preimage_false, unitInterval.volume_Ioi]
    have h := coe_toNNReal_eq_ofReal (σ p)
    rw [unitInterval.coe_symm_eq] at h
    simp [h]
  · rw [labelThreshold_preimage_true, unitInterval.volume_Iic]
    simp [coe_toNNReal_eq_ofReal p]

/-- The `p`-configuration read off the labels. -/
def labelConfiguration (p : I) (ω : Bond d → I) : Configuration d :=
  fun e => labelThreshold p (ω e)

lemma measurable_labelConfiguration (p : I) :
    Measurable (labelConfiguration (d := d) p) :=
  measurable_pi_iff.2 fun e => (measurable_labelThreshold p).comp (measurable_pi_apply e)

theorem map_labelConfiguration (p : I) :
    Measure.map (labelConfiguration p) (Measure.infinitePi fun _ : Bond d => (volume : Measure I)) =
      percolation d p := by
  unfold percolation
  rw [show labelConfiguration (d := d) p = fun ω e => labelThreshold p (ω e) from rfl,
    Measure.infinitePi_map_pi _ (fun _ => measurable_labelThreshold p)]
  simp_rw [map_labelThreshold]

lemma labelConfiguration_mono {p q : I} (hpq : p ≤ q) (ω : Bond d → I) (e : Bond d)
    (h : labelConfiguration p ω e = true) : labelConfiguration q ω e = true := by
  simp only [labelConfiguration, labelThreshold, decide_eq_true_eq] at h ⊢
  exact h.trans hpq

/-! Constructor. -/

theorem coupledRenormalizedExploration_of_labelBlocks (p : I) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (N : ℕ) (Bx : Finset (Vertex 2)) (h0 : (0 : Vertex 2) ∈ Bx)
    (B : Bx ⊕ boxBonds Bx → Finset (Bond d))
    (hB : Pairwise fun i j => Disjoint (B i) (B j))
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞}
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (succ : ExploreState Bx (boxBonds Bx) → (∀ i, B i → I) → Bool)
    (local_succ : ∀ st i (x x' : ∀ j, B j → I),
      ExploreInv (boxEnds Bx) (⟨0, h0⟩ : Bx) st →
      exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx) st = some i →
      (∀ j ∈ insert i (exploreRevealed st), x j = x' j) → succ st x = succ st x')
    (measurable_succ : ∀ st, Measurable (succ st))
    (prob_succ : ∀ st i (x : ∀ j, B j → I),
      ExploreInv (boxEnds Bx) (⟨0, h0⟩ : Bx) st →
      exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx) st = some i →
      κ {true} ≤ Measure.pi (fun _ : B i => (volume : Measure I))
        {y | succ st (Function.update x i y) = true})
    (good : ∀ ω : Bond d → I, explorePayoff (boxInnerBoundary Bx)
      (adaptiveRun (exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx))
        (exploreNext (boxEnds Bx) (⟨0, h0⟩ : Bx)) succ
        (Fintype.card (Bx ⊕ boxBonds Bx)) ⟨∅, ∅, ∅, ∅, ∅⟩ (blockLabels B ω)) ≠ 0 →
      labelConfiguration p ω ∈ restrictedReachFarEvent S F N) :
    Nonempty (CoupledRenormalizedExploration d p S F N θ) :=
  ⟨{ Vx := Bx
     Ed := boxBonds Bx
     ends := boxEnds Bx
     root := ⟨0, h0⟩
     target := boxInnerBoundary Bx
     Ω₀ := Bond d → I
     P := Measure.infinitePi fun _ : Bond d => (volume : Measure I)
     cfg := labelConfiguration p
     measurable_cfg := measurable_labelConfiguration p
     map_cfg := map_labelConfiguration p
     Ω := fun i => B i → I
     ν := fun i => Measure.pi (fun _ : B i => (volume : Measure I))
     κ := κ
     Φ := blockLabels B
     measurable_Φ := measurable_blockLabels B
     map_Φ := infinitePi_map_blockLabels volume B hB
     succ := succ
     local_succ := local_succ
     measurable_succ := measurable_succ
     prob_succ := prob_succ
     good := good
     mixed_ge := mixedValue_box_ge Bx h0 κ hθ }⟩

end NearCritical
