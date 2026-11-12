module

public import NearCritical.SlabResampledNestInputs
public import NearCritical.SlabSiteBound

/-! Site test and root nest of the slab nest rule, with their per-step bounds.

On the block spaces `rsΩ` of the resampled slab sample:

* `slabCubeConfig x v`: the critical configuration read from the first-copy block
  of the cube `v` (closed elsewhere);
* `slabSiteOK typ v x`: the cube `v` is pre-good in `slabCubeConfig x v`;
* `rootNestOf typ k ω` / `slabRootNest typ k x`: if the root cube is pre-good and
  has at least `k` typical clusters, a `k`-subset of its typical family together
  with its heart union (the nest data `L`), otherwise `none`.

Proved: locality (`slabSiteOK_local`, `slabRootNest_local`), `slabRootNest_site`
(root nest exists ⇒ root site test passes), and the bounds `slab_psite`,
`slab_proot` on `rsν` from the pre-good probability at `p_c` (in the form of the
conclusion of `Section10.pregood_eventually`), the latter under
`k <= countLower (2n)^(d-6)`.

These are the fields `site_local`, `root_local`, `rootSite`, `psite`, `proot` of
the slab `NestRule` / `ResampledSlabNestInputs`. The child nest and the edge
bound are NOT here.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set Function
open scoped Classical ENNReal
open Section10

variable {d : ℕ}

/-- Nest data: the `k` clusters and the heart union of the cube. -/
abbrev SlabNest (d : ℕ) : Type := Finset (Finset (Vertex d)) × Finset (Vertex d)

/-- Critical configuration read from the first-copy block of the cube `v`. -/
def slabCubeConfig (d n : ℕ) (A : Finset (Bond d)) (R : ℕ) (x : ∀ i, rsΩ d n A R i)
    (v : centeredBox 2 R) : Configuration d :=
  blockConfig (slabSprinkleBlocks (d := d) n A (centeredBox 2 R) (Sum.inl v)) (x (Sum.inl v)).1

/-- Site test: the cube is pre-good. -/
def slabSiteOK (d n : ℕ) (A : Finset (Bond d)) (R : ℕ) (typ : TypicalParameters)
    (v : centeredBox 2 R) (x : ∀ i, rsΩ d n A R i) : Bool :=
  decide (IsPreGoodCube typ n (coarseShift (d := d) n v.1) (slabCubeConfig d n A R x v))

/-- Root nest from a critical configuration of the cube centred at `c`. -/
def rootNestOf (typ : TypicalParameters) (n k : ℕ) (c : Vertex d) (ω : Configuration d) :
    Option (SlabNest d) :=
  if h : IsPreGoodCube typ n c ω ∧ k ≤ (typicalClusterFamily typ n c ω).card then
    some (Classical.choose (Finset.exists_subset_card_eq h.2),
      heartClusterUnion ω (typicalCube n c) (typicalHeart n c typ.heartRatio))
  else none

lemma rootNestOf_isSome (typ : TypicalParameters) (n k : ℕ) (c : Vertex d)
    (ω : Configuration d) :
    (rootNestOf typ n k c ω).isSome = true ↔
      IsPreGoodCube typ n c ω ∧ k ≤ (typicalClusterFamily typ n c ω).card := by
  unfold rootNestOf
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Root nest of the slab rule. -/
def slabRootNest (d n : ℕ) (A : Finset (Bond d)) (R : ℕ) (typ : TypicalParameters) (k : ℕ)
    (x : ∀ i, rsΩ d n A R i) : Option (SlabNest d) :=
  rootNestOf typ n k (coarseShift (d := d) n (0 : Vertex 2))
    (slabCubeConfig d n A R x ⟨0, zero_mem_centeredBox_two R⟩)

lemma slabSiteOK_local (n : ℕ) (A : Finset (Bond d)) (R : ℕ) (typ : TypicalParameters)
    (z : centeredBox 2 R) (x x' : ∀ i, rsΩ d n A R i) (h : x (Sum.inl z) = x' (Sum.inl z)) :
    slabSiteOK d n A R typ z x = slabSiteOK d n A R typ z x' := by
  unfold slabSiteOK slabCubeConfig
  rw [h]

lemma slabRootNest_local (n : ℕ) (A : Finset (Bond d)) (R : ℕ) (typ : TypicalParameters)
    (k : ℕ) (x x' : ∀ i, rsΩ d n A R i)
    (h : x (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R)) =
      x' (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R))) :
    slabRootNest d n A R typ k x = slabRootNest d n A R typ k x' := by
  unfold slabRootNest slabCubeConfig
  rw [h]

lemma slabRootNest_site (n : ℕ) (A : Finset (Bond d)) (R : ℕ) (typ : TypicalParameters)
    (k : ℕ) (x : ∀ i, rsΩ d n A R i) (ℓ : SlabNest d)
    (h : slabRootNest d n A R typ k x = some ℓ) :
    slabSiteOK d n A R typ ⟨0, zero_mem_centeredBox_two R⟩ x = true := by
  have hs : (slabRootNest d n A R typ k x).isSome = true := by rw [h]; rfl
  unfold slabRootNest at hs
  have := ((rootNestOf_isSome typ n k _ _).mp hs).1
  unfold slabSiteOK
  exact decide_eq_true this

/-- An event on the first component has the first marginal's probability. -/
lemma prod_fst_preimage {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [IsProbabilityMeasure ν] (S : Set X)
    (hS : MeasurableSet S) : (μ.prod ν) (Prod.fst ⁻¹' S) = μ S := by
  have h : Prod.fst ⁻¹' S = S ×ˢ (univ : Set Y) := by
    ext y
    simp
  rw [h, Measure.prod_prod, measure_univ, mul_one]

theorem slab_psite {n : ℕ} (hn : 0 < n) (s : I) (A : Finset (Bond d)) (R : ℕ)
    (typ : TypicalParameters)
    (hA : ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A)
    {η : ℝ} (κ : Measure Bool) (hκ : κ {true} ≤ ENNReal.ofReal (1 - η))
    (hpre : ∀ c : Vertex d, 1 - η ≤ ∫ ω, (if IsPreGoodCube typ n c ω then (1:ℝ) else 0)
      ∂(percolation d (criticalPoint d)))
    (z : centeredBox 2 R) (x : ∀ j, rsΩ d n A R j) :
    κ {true} ≤ rsν d n A R (criticalPoint d) s (Sum.inl z)
      {y | slabSiteOK d n A R typ z (update x (Sum.inl z) y) = true} := by
  have hset : {y : rsΩ d n A R (Sum.inl z) |
      slabSiteOK d n A R typ z (update x (Sum.inl z) y) = true} =
      Prod.fst ⁻¹' {y₁ | IsPreGoodCube typ n (coarseShift (d := d) n z.1)
        (blockConfig (slabSprinkleBlocks (d := d) n A (centeredBox 2 R) (Sum.inl z)) y₁)} := by
    ext y
    simp only [mem_setOf_eq, mem_preimage, slabSiteOK, slabCubeConfig, update_self,
      decide_eq_true_eq]
  rw [hset, prod_fst_preimage _ _ _ MeasurableSet.of_discrete]
  exact cubeBlock_site_bound hn s A (centeredBox 2 R) z typ (hA z.1 z.2) κ hκ (hpre _)

theorem slab_proot {n : ℕ} (hn : 0 < n) (s : I) (A : Finset (Bond d)) (R : ℕ)
    (typ : TypicalParameters) (k : ℕ)
    (hk : (k : ℝ) ≤ typ.countLower * (2 * (n : ℝ)) ^ (d - 6))
    (hA : ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A)
    {η : ℝ} (κ : Measure Bool) (hκ : κ {true} ≤ ENNReal.ofReal (1 - η))
    (hpre : ∀ c : Vertex d, 1 - η ≤ ∫ ω, (if IsPreGoodCube typ n c ω then (1:ℝ) else 0)
      ∂(percolation d (criticalPoint d)))
    (x : ∀ j, rsΩ d n A R j) :
    κ {true} ≤ rsν d n A R (criticalPoint d) s
        (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R))
      {y | (slabRootNest d n A R typ k (update x
        (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R)) y)).isSome = true} := by
  refine (slab_psite hn s A R typ hA κ hκ hpre ⟨0, zero_mem_centeredBox_two R⟩ x).trans
    (measure_mono ?_)
  intro y hy
  simp only [mem_setOf_eq, slabSiteOK, decide_eq_true_eq] at hy
  simp only [mem_setOf_eq]
  unfold slabRootNest
  refine (rootNestOf_isSome typ n k _ _).mpr ⟨hy, ?_⟩
  have hc := hy.1
  have : (k : ℝ) ≤ ((typicalClusterFamily typ n (coarseShift (d := d) n (0 : Vertex 2))
      (slabCubeConfig d n A R (update x
        (Sum.inl (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R)) y)
        ⟨0, zero_mem_centeredBox_two R⟩)).card : ℝ) := hk.trans hc
  exact_mod_cast this

end NearCritical
