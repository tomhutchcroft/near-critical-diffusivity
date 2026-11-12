module

public import NearCritical.HeartRevealStopping
public import NearCritical.Section10TypicalIncident

/-! The site test is unchanged by resampling.

The typical cluster family of a cube, and hence `IsPreGoodCube`, depends only on
the configuration on the heart-union reveal set
(`Section10.isPreGoodCube_iff_of_union_reveal_agree`). Therefore:

* `typicalClusterFamily_eq_of_heartReveal_agree`,
  `isPreGoodCube_iff_of_heartReveal_agree`: two configurations agreeing on
  `heartRevealSet` of the first have the same typical family and the same
  pre-good status;
* `resample_typicalClusterFamily`, `resample_isPreGoodCube`: the composite
  "first copy on the reveal set (and a fixed set `K`), second copy elsewhere" has
  the typical family and pre-good status of the first copy.

With `cube_resample_law` this gives: the site test of the composite
configuration is a function of the cube's first-copy block, with the original
law.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open scoped Classical
open Section10

variable {d : ℕ}

theorem typicalClusterFamily_eq_of_heartReveal_agree (a : TypicalParameters) (t : ℕ)
    (z : Vertex d) (ω η : Configuration d)
    (hagree : ∀ e ∈ heartRevealSet (typicalCube t z) (typicalHeart t z a.heartRatio) ω,
      ω e = η e) :
    typicalClusterFamily a t z ω = typicalClusterFamily a t z η :=
  typicalClusterFamily_eq_of_union_reveal_agree a t z _ ω η rfl hagree

theorem isPreGoodCube_iff_of_heartReveal_agree (a : TypicalParameters) (t : ℕ)
    (z : Vertex d) (ω η : Configuration d)
    (hagree : ∀ e ∈ heartRevealSet (typicalCube t z) (typicalHeart t z a.heartRatio) ω,
      ω e = η e) :
    IsPreGoodCube a t z ω ↔ IsPreGoodCube a t z η :=
  isPreGoodCube_iff_of_union_reveal_agree a t z _ ω η rfl hagree

lemma resample_agree_on_heartReveal (Q H : Finset (Vertex d))
    (K : Finset (internalBondSet Q))
    (q : (internalBondSet Q → Bool) × (internalBondSet Q → Bool)) :
    ∀ e ∈ heartRevealSet Q H (reconstructInterior Q q.1),
      reconstructInterior Q q.1 e =
        reconstructInterior Q (resample (cubeReveal Q H K) q) e := by
  intro e he
  have heQ := heartRevealSet_subset Q H _ he
  rw [reconstructInterior_apply Q q.1 e heQ, reconstructInterior_apply Q _ e heQ]
  have hmem : (⟨e, heQ⟩ : internalBondSet Q) ∈ cubeReveal Q H K q.1 := by
    unfold cubeReveal
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  unfold resample
  rw [if_pos hmem]

theorem resample_typicalClusterFamily (a : TypicalParameters) (t : ℕ) (z : Vertex d)
    (K : Finset (internalBondSet (typicalCube t z)))
    (q : (internalBondSet (typicalCube t z) → Bool) ×
      (internalBondSet (typicalCube t z) → Bool)) :
    typicalClusterFamily a t z (reconstructInterior (typicalCube t z)
        (resample (cubeReveal (typicalCube t z) (typicalHeart t z a.heartRatio) K) q)) =
      typicalClusterFamily a t z (reconstructInterior (typicalCube t z) q.1) :=
  (typicalClusterFamily_eq_of_heartReveal_agree a t z _ _
    (resample_agree_on_heartReveal _ _ K q)).symm

theorem resample_isPreGoodCube (a : TypicalParameters) (t : ℕ) (z : Vertex d)
    (K : Finset (internalBondSet (typicalCube t z)))
    (q : (internalBondSet (typicalCube t z) → Bool) ×
      (internalBondSet (typicalCube t z) → Bool)) :
    IsPreGoodCube a t z (reconstructInterior (typicalCube t z)
        (resample (cubeReveal (typicalCube t z) (typicalHeart t z a.heartRatio) K) q)) ↔
      IsPreGoodCube a t z (reconstructInterior (typicalCube t z) q.1) :=
  (isPreGoodCube_iff_of_heartReveal_agree a t z _ _
    (resample_agree_on_heartReveal _ _ K q)).symm

end NearCritical
