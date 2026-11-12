module

public import NearCritical.SlabUpperSprinkleCoupling

/-! Independent blocks of a PAIR of independent samples.

`pi_zip_law`: for finitely many countable discrete factors, zipping two
independent product samples gives the product of the pair laws.

`productBlocks_law`: let `(ω, ω')` be two independent samples of an infinite
product law on `K → Bool`. If block `i` reads `ω` on `B₁ i` and `ω'` on `B₂ i`,
with the `B₁ i` pairwise disjoint and the `B₂ i` pairwise disjoint, then the
blocks are independent: the block map has law
`Π_i (law of ω on B₁ i) ⊗ (law of ω' on B₂ i)`.

Used for the resampled slab sample: a cube block reads first-copy bits, a tube
block reads first-copy bits and second-copy strip bits.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Set
open scoped Classical

theorem pi_zip_law {ιb : Type*} [Fintype ιb] {X Y : ιb → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    [∀ i, Countable (X i)] [∀ i, Countable (Y i)]
    [∀ i, MeasurableSingletonClass (X i)] [∀ i, MeasurableSingletonClass (Y i)]
    (ν₁ : ∀ i, Measure (X i)) (ν₂ : ∀ i, Measure (Y i))
    [∀ i, IsProbabilityMeasure (ν₁ i)] [∀ i, IsProbabilityMeasure (ν₂ i)] :
    Measure.map (fun q : (∀ i, X i) × (∀ i, Y i) => fun i => (q.1 i, q.2 i))
        ((Measure.pi ν₁).prod (Measure.pi ν₂)) =
      Measure.pi (fun i => (ν₁ i).prod (ν₂ i)) := by
  refine Measure.ext_of_singleton fun w => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton w)]
  have hpre : (fun q : (∀ i, X i) × (∀ i, Y i) => fun i => (q.1 i, q.2 i)) ⁻¹' {w} =
      ({fun i => (w i).1} : Set (∀ i, X i)) ×ˢ ({fun i => (w i).2} : Set (∀ i, Y i)) := by
    ext ⟨x, y⟩
    simp only [mem_preimage, mem_singleton_iff, mem_prod]
    constructor
    · intro h
      subst h
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  rw [hpre, Measure.prod_prod, Measure.pi_singleton, Measure.pi_singleton, Measure.pi_singleton,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hw : ({w i} : Set (X i × Y i)) = ({(w i).1} : Set (X i)) ×ˢ ({(w i).2} : Set (Y i)) := by
    rw [Set.singleton_prod_singleton]
  rw [hw, Measure.prod_prod]

theorem productBlocks_law {K ιb : Type*} [Fintype ιb] [DecidableEq ιb]
    (μ : K → Measure Bool) [∀ k, IsProbabilityMeasure (μ k)]
    (B₁ B₂ : ιb → Finset K)
    (h₁ : Pairwise fun i j => Disjoint (B₁ i) (B₁ j))
    (h₂ : Pairwise fun i j => Disjoint (B₂ i) (B₂ j)) :
    Measurable (fun q : (K → Bool) × (K → Bool) => fun i =>
      (blockFamily (X := fun _ => Bool) B₁ q.1 i, blockFamily (X := fun _ => Bool) B₂ q.2 i)) ∧
    Measure.map (fun q : (K → Bool) × (K → Bool) => fun i =>
        (blockFamily (X := fun _ => Bool) B₁ q.1 i, blockFamily (X := fun _ => Bool) B₂ q.2 i))
        ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) =
      Measure.pi (fun i => (Measure.pi fun e : B₁ i => μ e).prod
        (Measure.pi fun e : B₂ i => μ e)) := by
  have hpm : Measurable (Prod.map (blockFamily (X := fun _ => Bool) B₁)
      (blockFamily (X := fun _ => Bool) B₂)) :=
    (measurable_blockFamily B₁).prodMap (measurable_blockFamily B₂)
  have hzip : Measurable (fun q : (∀ i, B₁ i → Bool) × (∀ i, B₂ i → Bool) =>
      fun i => (q.1 i, q.2 i)) := Measurable.of_discrete
  have hcomp : (fun q : (K → Bool) × (K → Bool) => fun i =>
      (blockFamily (X := fun _ => Bool) B₁ q.1 i, blockFamily (X := fun _ => Bool) B₂ q.2 i)) =
      (fun q : (∀ i, B₁ i → Bool) × (∀ i, B₂ i → Bool) => fun i => (q.1 i, q.2 i)) ∘
        Prod.map (blockFamily (X := fun _ => Bool) B₁) (blockFamily (X := fun _ => Bool) B₂) :=
    rfl
  refine ⟨by rw [hcomp]; exact hzip.comp hpm, ?_⟩
  rw [hcomp, ← Measure.map_map hzip hpm,
    ← Measure.map_prod_map _ _ (measurable_blockFamily B₁) (measurable_blockFamily B₂),
    infinitePi_map_blockFamily μ B₁ h₁, infinitePi_map_blockFamily μ B₂ h₂]
  exact pi_zip_law _ _

end NearCritical
