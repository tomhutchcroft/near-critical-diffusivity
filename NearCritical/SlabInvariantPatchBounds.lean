module

public import NearCritical.SlabPatchChart
public import NearCritical.SlabStepGuardSizes
public import NearCritical.SlabNestInvariant

/-! The slab invariant and a pre-good target supply the per-cluster
boundary counts for both orientations of an actual edge. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

theorem slabChartEdge_centres {d : ℕ} (hd : 2 ≤ d) (n R : ℕ)
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R)
    (hz : z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) :
    let φ := slabChartEquiv hd n e.1 (slabEdgeReverse e z)
    let i := Fin.castLE hd e.1.2
    φ (0 : Vertex d) = coarseShift n (otherEnd (boxEnds (centeredBox 2 R)) e z).1 ∧
      φ (farCenter n 0 i) = coarseShift n z.1 := by
  have hne := bondTip_ne_base e.1
  have hends : (boxEnds (centeredBox 2 R) e).1 ≠ (boxEnds (centeredBox 2 R) e).2 :=
    fun h => hne (congrArg Subtype.val h).symm
  rcases hz with rfl | rfl
  · have h := slabChartVertex_centres hd n e.1 true
    simpa [slabEdgeReverse, otherEnd, boxEnds, slabChartEquiv_apply] using h
  · have h := slabChartVertex_centres hd n e.1 false
    have hrev : slabEdgeReverse e (boxEnds (centeredBox 2 R) e).2 = false := by
      simp [slabEdgeReverse, boxEnds, hne]
    have ha : otherEnd (boxEnds (centeredBox 2 R)) e (boxEnds (centeredBox 2 R) e).2 =
        (boxEnds (centeredBox 2 R) e).1 := if_neg hends
    dsimp only
    rw [hrev, ha]
    simpa only [slabChartEquiv_apply, boxEnds, Bool.false_eq_true, if_false] using h

theorem typicalFamily_chart_pairwiseDisjoint {d : ℕ} (typ : TypicalParameters) (n : ℕ)
    (c : Vertex d) (ω : Configuration d) (φ : Vertex d ≃ Vertex d)
    (C : Finset (Finset (Vertex d))) (hC : C ⊆ typicalClusterFamily typ n c ω) :
    (C.image (chartCluster φ) : Set (Finset (Vertex d))).PairwiseDisjoint id := by
  intro X hX Y hY hne
  obtain ⟨X',hX',rfl⟩ := Finset.mem_image.mp hX
  obtain ⟨Y',hY',rfl⟩ := Finset.mem_image.mp hY
  apply (Finset.disjoint_map φ.toEmbedding).2
  exact finiteClusterFamily_disjoint _ _
    ((mem_typicalClusterFamily _ _ _ _ _).mp (hC hX')).1
    ((mem_typicalClusterFamily _ _ _ _ _).mp (hC hY')).1
    (fun he => hne (congrArg (chartCluster φ) he))

set_option maxHeartbeats 900000 in
theorem slab_patch_bounds_of_invariant {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (R : ℕ) (A : Finset (Bond d)) (typ : TypicalParameters) (k : ℕ)
    (S : Set (Vertex d)) (F : Finset (Vertex d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) (ℓ : SlabNest d)
    (hz : z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2)
    (hsite : slabSiteOK d n A R typ z (rsΦ d n A R q) = true)
    (hq : slabQ d n A R typ k S F q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ) :
    SlabPatchBounds typ n k (Fin.castLE hd e.1.2)
      (slabStepBoundaryData hd n R A typ e z ℓ (rsΦ d n A R q)) := by
  let a := otherEnd (boxEnds (centeredBox 2 R)) e z
  let ω := slabCubeConfig d n A R (rsΦ d n A R q)
  let rev := slabEdgeReverse e z
  let φ := slabChartEquiv hd n e.1 rev
  let i := Fin.castLE hd e.1.2
  let c := fun v : centeredBox 2 R => coarseShift (d := d) n v.1
  let H := fun v => heartClusterUnion (ω v) (typicalCube n (c v)) (typicalHeart n (c v) typ.heartRatio)
  let fam := fun v => typicalClusterFamily typ n (c v) (ω v)
  let D := slabStepBoundaryData hd n R A typ e z ℓ (rsΦ d n A R q)
  obtain ⟨hcard, hnest, hheart, _⟩ := hq
  change ℓ.1 ⊆ fam a at hnest
  change ℓ.2 = H a at hheart
  have hgood : IsPreGoodCube typ n (c z) (ω z) := by
    exact of_decide_eq_true hsite
  obtain ⟨hcentre₁,hcentre₃⟩ := slabChartEdge_centres hd n R e z hz
  change φ 0 = c a at hcentre₁
  change φ (farCenter n 0 i) = c z at hcentre₃
  have hD₁ : D.parentHeart = chartCluster φ.symm (H a) :=
    congrArg (chartCluster φ.symm) hheart
  have hD₃ : D.childHeart = chartCluster φ.symm (H z) := rfl
  have hp (v : centeredBox 2 R) (w : Vertex d) (hc : φ w = c v)
      (C : Finset (Vertex d)) (sign plus : Bool) :
      (slabRegularPatch typ n w (chartCluster φ.symm (H v)) (chartCluster φ.symm C)
        (i, sign) plus).card =
      (typicalRegularPatch typ n (c v) (ω v) C (i, if rev then !sign else sign) plus).card := by
    have h := slabRegularPatch_pullback_card hd typ hn e.1 rev w (H v) C sign plus
    change _ = (slabRegularPatch typ n (φ w) (H v) C
      (i, if rev then !sign else sign) plus).card at h
    rw [hc] at h
    exact h
  have hsCard (C : Finset (Vertex d)) :
      (D.source typ n i (chartCluster φ.symm C)).card =
      (typicalRegularPatch typ n (c a) (ω a) C (i, if rev then !true else true) true).card := by
    unfold SlabStepBoundaryData.source
    rw [hD₁]
    exact hp a 0 hcentre₁ C true true
  have htCard (C : Finset (Vertex d)) (plus : Bool) :
      (slabRegularPatch typ n (farCenter n 0 i) D.childHeart (chartCluster φ.symm C)
        (i,false) plus).card =
      (typicalRegularPatch typ n (c z) (ω z) C (i, if rev then !false else false) plus).card :=
    hp z (farCenter n 0 i) hcentre₃ C false plus
  have hSsub (C : Finset (Vertex d)) : D.source typ n i C ⊆ C :=
    fun _ h => (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).1
  have hTsub (C : Finset (Vertex d)) : D.target typ n i C ⊆ C := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
    · exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (chartCluster_image_card φ.symm ℓ.1).trans hcard
  · change _ ≤ (((fam z).image (chartCluster φ.symm)).card : ℝ)
    rw [chartCluster_image_card]
    exact hgood.1
  · intro C hC E hE hne
    exact Finset.disjoint_of_subset_left (hSsub C) (Finset.disjoint_of_subset_right (hSsub E)
      (typicalFamily_chart_pairwiseDisjoint typ n (c a) (ω a) φ.symm ℓ.1 hnest hC hE hne))
  · intro C hC E hE hne
    exact Finset.disjoint_of_subset_left (hTsub C) (Finset.disjoint_of_subset_right (hTsub E)
      (typicalFamily_chart_pairwiseDisjoint typ n (c z) (ω z) φ.symm (fam z) (fun _ hx => hx) hC hE hne))
  · intro C hC
    obtain ⟨C',hC',rfl⟩ := Finset.mem_image.mp hC
    rw [hsCard]
    exact (((mem_typicalClusterFamily _ _ _ _ _).mp (hnest hC')).2.2.2.2.2.2.1 _ _).1
  · intro C hC
    obtain ⟨C',hC',rfl⟩ := Finset.mem_image.mp hC
    rw [hsCard]
    exact (((mem_typicalClusterFamily _ _ _ _ _).mp (hnest hC')).2.2.2.2.2.2.1 _ _).2
  · intro C hC
    obtain ⟨C',hC',rfl⟩ := Finset.mem_image.mp hC
    have hp' := (((mem_typicalClusterFamily _ _ _ _ _).mp hC').2.2.2.2.2.2.1
      (i, if rev then !false else false) true).1
    rw [← htCard C' true] at hp'
    exact hp'.trans (Nat.cast_le.mpr (Finset.card_le_card Finset.subset_union_left))
  · intro C hC
    obtain ⟨C',hC',rfl⟩ := Finset.mem_image.mp hC
    have hT := ((mem_typicalClusterFamily _ _ _ _ _).mp hC').2.2.2.2.2.2.1
    have h₁ := (hT (i, if rev then !false else false) true).2
    have h₂ := (hT (i, if rev then !false else false) false).2
    rw [← htCard C' true] at h₁
    rw [← htCard C' false] at h₂
    unfold SlabStepBoundaryData.target
    have hUnion := Nat.cast_le (α := ℝ) |>.2 (Finset.card_union_le
      (slabRegularPatch typ n (farCenter n 0 i) D.childHeart (chartCluster φ.symm C') (i,false) true)
      (slabRegularPatch typ n (farCenter n 0 i) D.childHeart (chartCluster φ.symm C') (i,false) false))
    push_cast at hUnion
    exact hUnion.trans (by linarith)

end NearCritical
