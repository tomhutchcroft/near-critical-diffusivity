module

public import NearCritical.ResamplingInfinite
public import NearCritical.SlabSiteResample
public import NearCritical.SlabUpperOrParameter
public import NearCritical.SlabUpperSprinkleCoupling

/-! The resampled two-layer configuration for a finite family of cubes.

For cubes `Q j ⊇ H j` (`j ∈ s`) and a FIXED set `Kfix` of bonds (those cube bonds
on which no second copy is used):

* `unionReveal`: the union of the heart reveal sets of the cubes, enlarged by
  `Kfix`; it is a stopping set (`unionReveal_stopping`) and every cube keeps its
  heart union (`unionReveal_heartUnion`).
* `resampleLayers`: on the two-layer sample space `Bond d × Bool → Bool`
  (`true` = critical layer, `false` = sprinkle), use the SECOND sample on the
  critical-layer bits of cube bonds outside `unionReveal` of the first sample,
  and the first sample everywhere else.
* `resampleLayers_law`: it is measurable and maps the product of two independent
  two-layer laws to the two-layer law.
* `resampledConfig_law`: the resulting configuration (`critical layer ∨
  sprinkle`) has law `P_{a or s}`.
* `resampleLayers_heartUnion`, `resampleLayers_isPreGoodCube`: every cube has the
  heart union, and for typical cubes the pre-good status, of the first sample.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set
open scoped Classical
open Section10

variable {d : ℕ} {κ : Type*}

/-- Critical-layer indices of a set of bonds. -/
def layerSet (A : Finset (Bond d)) : Finset (Bond d × Bool) :=
  A.image fun e => ((e, true) : Bond d × Bool)

lemma mem_layerSet (A : Finset (Bond d)) (x : Bond d × Bool) :
    x ∈ layerSet A ↔ x.2 = true ∧ x.1 ∈ A := by
  unfold layerSet
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    exact ⟨rfl, he⟩
  · rintro ⟨h2, h1⟩
    obtain ⟨e, b⟩ := x
    simp only at h2 h1
    subst h2
    exact Finset.mem_image.mpr ⟨e, h1, rfl⟩

/-- The critical layer of a two-layer sample. -/
def criticalLayer (ω : Bond d × Bool → Bool) : Configuration d := fun e => ω (e, true)

/-- Union of the heart reveal sets, enlarged by the fixed set `Kfix`. -/
def unionReveal (s : Finset κ) (Q H : κ → Finset (Vertex d)) (Kfix : Finset (Bond d))
    (ω : Configuration d) : Finset (Bond d) :=
  (s.biUnion fun j => heartRevealSet (Q j) (H j) ω) ∪ Kfix

/-- All internal bonds of the cubes. -/
def cubeBonds (s : Finset κ) (Q : κ → Finset (Vertex d)) : Finset (Bond d) :=
  s.biUnion fun j => internalBondSet (Q j)

theorem unionReveal_subset (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (Kfix : Finset (Bond d)) (hK : Kfix ⊆ cubeBonds s Q) (ω : Configuration d) :
    unionReveal s Q H Kfix ω ⊆ cubeBonds s Q := by
  intro e he
  rcases Finset.mem_union.mp he with h | h
  · obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨j, hj, heartRevealSet_subset _ _ _ hej⟩
  · exact hK h

theorem unionReveal_heartUnion (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (hH : ∀ j ∈ s, H j ⊆ Q j) (Kfix : Finset (Bond d)) (ω ω' : Configuration d)
    (hagree : ∀ e ∈ unionReveal s Q H Kfix ω, ω' e = ω e) (j : κ) (hj : j ∈ s) :
    heartClusterUnion ω' (Q j) (H j) = heartClusterUnion ω (Q j) (H j) ∧
      heartRevealSet (Q j) (H j) ω' = heartRevealSet (Q j) (H j) ω :=
  heartRevealSet_stopping (Q j) (H j) (hH j hj) ω ω' fun e he =>
    hagree e (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hj, he⟩))

theorem unionReveal_stopping (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (hH : ∀ j ∈ s, H j ⊆ Q j) (Kfix : Finset (Bond d)) (ω ω' : Configuration d)
    (hagree : ∀ e ∈ unionReveal s Q H Kfix ω, ω' e = ω e) :
    unionReveal s Q H Kfix ω' = unionReveal s Q H Kfix ω := by
  unfold unionReveal
  congr 1
  exact Finset.biUnion_congr rfl fun j hj =>
    (unionReveal_heartUnion s Q H hH Kfix ω ω' hagree j hj).2

/-- The two-layer stopping set. -/
def layerReveal (s : Finset κ) (Q H : κ → Finset (Vertex d)) (Kfix : Finset (Bond d))
    (ω : Bond d × Bool → Bool) : Finset (Bond d × Bool) :=
  layerSet (unionReveal s Q H Kfix (criticalLayer ω))

/-- Second sample on unrevealed critical-layer cube bits, first sample elsewhere. -/
def resampleLayers (s : Finset κ) (Q H : κ → Finset (Vertex d)) (Kfix : Finset (Bond d)) :
    (Bond d × Bool → Bool) × (Bond d × Bool → Bool) → Bond d × Bool → Bool :=
  resampleOn (layerSet (cubeBonds s Q)) (layerReveal s Q H Kfix)

lemma layerReveal_subset (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (Kfix : Finset (Bond d)) (hK : Kfix ⊆ cubeBonds s Q) (ω : Bond d × Bool → Bool) :
    layerReveal s Q H Kfix ω ⊆ layerSet (cubeBonds s Q) := by
  intro x hx
  unfold layerReveal at hx
  rw [mem_layerSet] at hx ⊢
  exact ⟨hx.1, unionReveal_subset s Q H Kfix hK _ hx.2⟩

lemma layerReveal_stopping (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (hH : ∀ j ∈ s, H j ⊆ Q j) (Kfix : Finset (Bond d)) (ω ω' : Bond d × Bool → Bool)
    (hagree : ∀ x ∈ layerReveal s Q H Kfix ω, ω' x = ω x) :
    layerReveal s Q H Kfix ω' = layerReveal s Q H Kfix ω := by
  unfold layerReveal
  rw [unionReveal_stopping s Q H hH Kfix (criticalLayer ω) (criticalLayer ω') fun e he =>
    hagree (e, true) ((mem_layerSet _ _).mpr ⟨rfl, he⟩)]

theorem resampleLayers_law (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (hH : ∀ j ∈ s, H j ⊆ Q j) (Kfix : Finset (Bond d)) (hK : Kfix ⊆ cubeBonds s Q) (a p : I) :
    Measurable (resampleLayers s Q H Kfix) ∧
    Measure.map (resampleLayers s Q H Kfix)
        ((Measure.infinitePi (sprinkleLaw (d := d) a p)).prod
          (Measure.infinitePi (sprinkleLaw (d := d) a p))) =
      Measure.infinitePi (sprinkleLaw (d := d) a p) :=
  resample_infinite_law (sprinkleLaw (d := d) a p) (layerSet (cubeBonds s Q))
    (layerReveal s Q H Kfix) (layerReveal_subset s Q H Kfix hK)
    (layerReveal_stopping s Q H hH Kfix)

/-- The resampled configuration has law `P_{a or p}`. -/
theorem resampledConfig_law (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (hH : ∀ j ∈ s, H j ⊆ Q j) (Kfix : Finset (Bond d)) (hK : Kfix ⊆ cubeBonds s Q) (a p : I) :
    Measure.map (fun q => sprinkleConfiguration (resampleLayers s Q H Kfix q))
        ((Measure.infinitePi (sprinkleLaw (d := d) a p)).prod
          (Measure.infinitePi (sprinkleLaw (d := d) a p))) =
      percolation d (orParameter a p) := by
  obtain ⟨hmeas, hlaw⟩ := resampleLayers_law s Q H hH Kfix hK a p
  have hcomp : (fun q => sprinkleConfiguration (resampleLayers s Q H Kfix q)) =
      sprinkleConfiguration ∘ resampleLayers s Q H Kfix := rfl
  rw [hcomp, ← Measure.map_map measurable_sprinkleConfiguration hmeas, hlaw,
    map_sprinkleConfiguration, orParameter_eq_symm_mul]

/-- The critical layer of the composite agrees with the first sample on the
reveal set. -/
lemma resampleLayers_agree (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (Kfix : Finset (Bond d)) (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) :
    ∀ e ∈ unionReveal s Q H Kfix (criticalLayer q.1),
      criticalLayer (resampleLayers s Q H Kfix q) e = criticalLayer q.1 e := by
  intro e he
  have hmem : ((e, true) : Bond d × Bool) ∈ layerReveal s Q H Kfix q.1 :=
    (mem_layerSet _ _).mpr ⟨rfl, he⟩
  change resampleOn _ _ q (e, true) = q.1 (e, true)
  unfold resampleOn
  rw [if_neg (fun h => h.2 hmem)]

theorem resampleLayers_heartUnion (s : Finset κ) (Q H : κ → Finset (Vertex d))
    (hH : ∀ j ∈ s, H j ⊆ Q j) (Kfix : Finset (Bond d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) (j : κ) (hj : j ∈ s) :
    heartClusterUnion (criticalLayer (resampleLayers s Q H Kfix q)) (Q j) (H j) =
      heartClusterUnion (criticalLayer q.1) (Q j) (H j) :=
  (unionReveal_heartUnion s Q H hH Kfix _ _ (resampleLayers_agree s Q H Kfix q) j hj).1

set_option maxHeartbeats 800000 in
theorem resampleLayers_isPreGoodCube (s : Finset κ) (a : TypicalParameters) (t : ℕ)
    (z : κ → Vertex d) (Kfix : Finset (Bond d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool)) (j : κ) (hj : j ∈ s) :
    IsPreGoodCube a t (z j) (criticalLayer (resampleLayers s (fun j => typicalCube t (z j))
        (fun j => typicalHeart t (z j) a.heartRatio) Kfix q)) ↔
      IsPreGoodCube a t (z j) (criticalLayer q.1) := by
  have hagree := resampleLayers_agree s (fun j => typicalCube t (z j))
    (fun j => typicalHeart t (z j) a.heartRatio) Kfix q
  have hloc : ∀ e ∈ heartRevealSet (typicalCube t (z j)) (typicalHeart t (z j) a.heartRatio)
      (criticalLayer q.1),
      criticalLayer q.1 e = criticalLayer (resampleLayers s (fun j => typicalCube t (z j))
        (fun j => typicalHeart t (z j) a.heartRatio) Kfix q) e := by
    intro e he
    refine (hagree e ?_).symm
    unfold unionReveal
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hj, he⟩)
  exact (isPreGoodCube_iff_of_heartReveal_agree a t (z j) _ _ hloc).symm

end NearCritical
