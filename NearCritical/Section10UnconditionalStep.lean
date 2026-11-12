module

public import NearCritical.Section10MoveReduction

/-! The success probability of a step is an unconditional probability when the
step reads no revealed bond.

`localSuccessProbability_eq_of_fresh`: if `P` reads only bonds of the fresh
block `T`, none of them revealed, then for every reveal value `eta`
`localSuccessProbability p q T (bitSet eta P) = P_{p x q}[P]`.

`NestLayout.view_readsOnly_readSet` and `NestLayout.moveSuccess_eq`: for a
lattice step whose read set is disjoint from the reveal bonds, the success
probability in `hmove` is the plain product-law probability that the sprinkling
cluster is typical. (Disjointness itself is a geometric fact about the layout,
not proved here.)
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
open MeasureTheory

theorem localSuccessProbability_eq_of_fresh {d : ℕ} (p q : unitInterval)
    {S T : Finset (LBond d)} (η : S → Bool) (P : Configuration d × Configuration d → Prop)
    (U : Finset (LBond d)) (hP : ReadsOnly U P) (hUT : U ⊆ T) (hUS : Disjoint U S) :
    localSuccessProbability p q T (bitSet η P) =
      ∫ z : Configuration d × Configuration d, (if P z then (1:ℝ) else 0)
        ∂((percolation d p).prod (percolation d q)) := by
  unfold localSuccessProbability
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  have hiff : (T.restrict (layerVal z) ∈ (bitSet η P : Set (T → Bool))) ↔ P z := by
    have heq : P (gluePair η (T.restrict (layerVal z))) = P z := by
      refine hP _ _ (fun e he => ?_)
      rw [layerVal_gluePair, dif_neg (Finset.disjoint_left.mp hUS he), dif_pos (hUT he)]
      rfl
    show P (gluePair η (T.restrict (layerVal z))) ↔ P z
    rw [heq]
  show (if (T.restrict (layerVal z)) ∈ (bitSet η P : Set (T → Bool)) then (1:ℝ) else 0) =
    if P z then (1:ℝ) else 0
  simp only [hiff]

variable {D d : ℕ} (Λ : NestLayout D d)

theorem NestLayout.view_readsOnly_readSet (F : Λ.Φ₀) (ℓ : RouteLabel D) :
    ReadsOnly (Λ.readSet F ℓ) (Λ.view F ℓ) := by
  refine ReadsOnly.pair ?_ ?_
  · exact (stepView_readsOnly _ _ _ _ _ _ _).mono Finset.subset_union_left
  · intro z z' hz
    refine Finset.filter_congr (fun y hy => ?_)
    have hmem : ((y, Λ.i₀) : Bond d) ∈ (Λ.exitPts ℓ).image (fun y => ((y, Λ.i₀) : Bond d)) :=
      Finset.mem_image_of_mem _ hy
    have h1 : z.1 (y, Λ.i₀) = z'.1 (y, Λ.i₀) :=
      hz ((false, (y, Λ.i₀)) : LBond d) (Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))
    have h2 : z.2 (y, Λ.i₀) = z'.2 (y, Λ.i₀) :=
      hz ((true, (y, Λ.i₀)) : LBond d) (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmem)))
    unfold sprinkleOrConfiguration
    rw [h1, h2]

/-- For a step reading no revealed bond, the success probability of `hmove` is
the unconditional probability of typicality. -/
theorem NestLayout.moveSuccess_eq (p q : unitInterval) (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X)
    (hfresh : Disjoint (Λ.readSet G.1 ℓ) (Λ.S₀ G.1)) :
    localSuccessProbability p q (Λ.Bl₀ G.1 ℓ)
        (bitSet G.2 (fun z => Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z))) =
      ∫ z : Configuration d × Configuration d,
        (if Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z) then (1:ℝ) else 0)
          ∂((percolation d p).prod (percolation d q)) := by
  refine localSuccessProbability_eq_of_fresh p q G.2 _ (Λ.readSet G.1 ℓ)
    ((Λ.view_readsOnly_readSet G.1 ℓ).comp _) ?_ hfresh
  intro e he
  exact Finset.mem_sdiff.mpr ⟨he, Finset.disjoint_left.mp hfresh he⟩

/-- A predicate reading finitely many layered bonds is a measurable event. -/
theorem ReadsOnly.measurableSet {d : ℕ} {U : Finset (LBond d)}
    {P : Configuration d × Configuration d → Prop} (hP : ReadsOnly U P) :
    MeasurableSet {z : Configuration d × Configuration d | P z} := by
  have he : {z : Configuration d × Configuration d | P z} =
      (fun z => U.restrict (layerVal z)) ⁻¹'
        (bitSet (S := (∅ : Finset (LBond d))) (T := U) (fun e => (Finset.notMem_empty e.1 e.2).elim) P) := by
    ext z
    have heq : P (gluePair (S := (∅ : Finset (LBond d))) (T := U)
        (fun e => (Finset.notMem_empty e.1 e.2).elim) (U.restrict (layerVal z))) = P z := by
      refine hP _ _ (fun e he => ?_)
      rw [layerVal_gluePair, dif_neg (by simp), dif_pos he]
      rfl
    show P z ↔ P (gluePair _ (U.restrict (layerVal z)))
    rw [heq]
  rw [he]
  exact ((Finset.measurable_restrict U).comp measurable_layerVal)
    (Set.toFinite _).measurableSet

/-- **Success probability of a moving step from the two failure probabilities.** -/
theorem NestLayout.moveSuccess_ge (p q : unitInterval) (G : Λ.Φ) (ℓ : RouteLabel D) (x : Λ.X)
    (hfresh : Disjoint (Λ.readSet G.1 ℓ) (Λ.S₀ G.1))
    (hMOff : (Λ.fam G ℓ.target).card ≤ Λ.MOff)
    (hMcoal : (Λ.faceAll G ℓ x.2).card ≤ Λ.Mcoal) (hk : 10 ≤ 2 * Λ.k ^ 4) {ε₁ ε₂ : ℝ}
    (hoff : ((percolation d p).prod (percolation d q)).real
      {z | ¬ 2 * Λ.k ^ 4 ≤ (sprinklingOffspring (Λ.view G.1 ℓ z).1.1 (Λ.view G.1 ℓ z).1.2.1
        (sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)) (Λ.fam G ℓ.target) (Λ.tgt G ℓ)
        (svPivots (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
          (Λ.tgt G ℓ))).card} ≤ ε₁)
    (hdiam : ((percolation d p).prod (percolation d q)).real
      {z | ¬ svDiameter (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
        (Λ.tgt G ℓ) ≤ Λ.Kdiam} ≤ ε₂) :
    1 - ε₁ - ε₂ ≤ localSuccessProbability p q (Λ.Bl₀ G.1 ℓ)
      (bitSet G.2 (fun z => Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z))) := by
  rw [Λ.moveSuccess_eq p q G ℓ x hfresh]
  have hmeas : MeasurableSet {z : Configuration d × Configuration d |
      Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z)} :=
    ReadsOnly.measurableSet ((Λ.view_readsOnly_readSet G.1 ℓ).comp _)
  have hind : (fun z : Configuration d × Configuration d =>
      if Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z) then (1:ℝ) else 0) =
      Set.indicator {z | Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z)} (fun _ => (1:ℝ)) := by
    funext z
    simp only [Set.indicator, Set.mem_setOf_eq]
  rw [hind, integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
  have hcompl : ((percolation d p).prod (percolation d q)).real
      {z | Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z)}ᶜ =
      1 - ((percolation d p).prod (percolation d q)).real
        {z | Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z)} := by
    rw [measureReal_compl hmeas]
    simp
  have hsub : {z : Configuration d × Configuration d |
      Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z)}ᶜ ⊆
      {z | ¬ 2 * Λ.k ^ 4 ≤ (sprinklingOffspring (Λ.view G.1 ℓ z).1.1 (Λ.view G.1 ℓ z).1.2.1
        (sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)) (Λ.fam G ℓ.target) (Λ.tgt G ℓ)
        (svPivots (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
          (Λ.tgt G ℓ))).card} ∪
      {z | ¬ svDiameter (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
        (Λ.tgt G ℓ) ≤ Λ.Kdiam} := by
    intro z hz
    by_contra hne
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hne
    exact hz ((Λ.moveTypical_view_iff G ℓ x z hMOff hMcoal).mpr ⟨hk, hne.1, hne.2⟩)
  have h1 := (measureReal_mono (μ := (percolation d p).prod (percolation d q)) hsub
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  linarith

end NearCritical.Section10
