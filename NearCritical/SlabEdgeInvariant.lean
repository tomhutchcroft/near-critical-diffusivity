module

public import NearCritical.SlabInvariantArrival

/-! Propagation of the slab exploration invariant along a successful
concrete child step. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

set_option maxHeartbeats 900000 in
theorem slabChildNest_edgeQ_of_shape {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (R : ℕ) (A : Finset (Bond d)) (typ : TypicalParameters) (k : ℕ) (hk : 0 < k)
    (S : Set (Vertex d)) (F : Finset (Vertex d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) (ℓ ℓ' : SlabNest d)
    (hz : z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2)
    (hsite : slabSiteOK d n A R typ z (rsΦ d n A R q) = true)
    (hq : slabQ d n A R typ k S F q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ)
    (hA : ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A)
    (hA' : ∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A)
    (hTube : slabTube n e.1.1 e.1.2 ⊆ S)
    (hCube : (typicalCube n (coarseShift (d := d) n z.1) : Set (Vertex d)) ⊆ S)
    (r : ℕ) (δ cSize CB KA : ℝ)
    (hshape : SlabOffspringShape typ n k (Fin.castLE hd e.1.2)
      (slabStepBoundaryData hd n R A typ e z ℓ (rsΦ d n A R q)) r δ cSize CB KA)
    (hchild : slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ (rsΦ d n A R q) = some ℓ') :
    slabQ d n A R typ k S F q z ℓ' := by
  let rev := slabEdgeReverse e z
  let φ := slabChartEquiv hd n e.1 rev
  let i := Fin.castLE hd e.1.2
  let M := section9FiniteMiddle i n
  let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
  let V := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
  let Q₁ := section9FiniteEndCube i n 0
  let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
  let D := slabStepBoundaryData hd n R A typ e z ℓ (rsΦ d n A R q)
  let p := pullbackLayerPair (slabChartBond hd n e.1 rev)
    (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e)))
  let selector := slabStepChildNest M L V Q₁ D.parentHeart Q₃ D.childHeart
    D.parentNest D.childCandidates (D.source typ n i) (D.target typ n i) p hk hshape.parentCard
  have hmap : selector.map (fun result => (result.2.image (chartCluster φ), chartCluster φ D.childHeart)) =
      some ℓ' := by
    have hg : (z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) ∧
        slabSiteOK d n A R typ z (rsΦ d n A R q) = true ∧
          SlabOffspringShape typ n k i D r δ cSize CB KA := ⟨hz,hsite,hshape⟩
    unfold slabChildNest slabChildNestOfBlocks at hchild
    rw [dif_pos hg] at hchild
    exact hchild
  cases hs : selector with
  | none => simp [hs] at hmap
  | some pair =>
    obtain ⟨C, children⟩ := pair
    have heq : (children.image (chartCluster φ), chartCluster φ D.childHeart) = ℓ' := by
      simpa only [hs, Option.map_some, Option.some.injEq] using hmap
    subst ℓ'
    have hspec := slabStepChildNest_spec M L V Q₁ D.parentHeart Q₃ D.childHeart
      D.parentNest D.childCandidates (D.source typ n i) (D.target typ n i) p hk hshape.parentCard hs
    obtain ⟨hC,hsize,hsub⟩ := hspec
    let ω := slabCubeConfig d n A R (rsΦ d n A R q) z
    let c := coarseShift (d := d) n z.1
    let fam := typicalClusterFamily typ n c ω
    have hCancel (W : Finset (Vertex d)) : chartCluster φ (chartCluster φ.symm W) = W := by
      simpa only [Equiv.symm_symm] using chartCluster_symm φ.symm W
    let v := stepView M L V Q₁ D.parentHeart Q₃ D.childHeart p
    let U := sprinklingTargetBoundary D.parentNest (D.source typ n i)
    have hmem (E : Finset (Vertex d)) (hE : E ∈ children) : chartCluster φ E ∈ fam := by
      have hE' : E ∈ D.childCandidates :=
        ((mem_sprinklingOffspring v.1 v.2.1 (D.source typ n i C) D.childCandidates
          (D.target typ n i) (v.2.2.1 U (sprinklingTargetBoundary D.childCandidates (D.target typ n i)))
          E).1 (hsub hE)).1
      obtain ⟨E',hE',rfl⟩ := Finset.mem_image.mp hE'
      rwa [hCancel]
    refine ⟨(chartCluster_image_card φ children).trans hsize, ?_, ?_, ?_⟩
    · intro E hE
      obtain ⟨E',hE',rfl⟩ := Finset.mem_image.mp hE
      exact hmem E' hE'
    · change chartCluster φ (chartCluster φ.symm
        (heartClusterUnion ω (typicalCube n c) (typicalHeart n c typ.heartRatio))) = _
      exact hCancel _
    · intro E hE w hw
      obtain ⟨E',hE',rfl⟩ := Finset.mem_image.mp hE
      have hC' : C ∈ ℓ.1.image (chartCluster φ.symm) := hC
      obtain ⟨C₀,hC₀,hCeq⟩ := Finset.mem_image.mp hC'
      obtain ⟨x,hx,y,hy,hpath⟩ := slab_invariant_child_arrival hd hn R A typ k S F q e z ℓ hz hq hA hA'
        C E' (hsub hE')
      have hx' : φ x ∈ C₀ := by
        have hx'' := (mem_chartCluster_apply φ C x).2 hx
        rwa [← hCeq, hCancel] at hx''
      obtain ⟨a,ha,hstart⟩ := hq.2.2.2 C₀ hC₀ _ hx'
      have hy' := (mem_chartCluster_apply φ E' y).2 hy
      have hEf := hmem E' hE'
      change chartCluster φ E' ∈ typicalClusterFamily typ n (coarseShift n z.1)
        (slabCubeConfig d n A R (rsΦ d n A R q) z) at hEf
      rw [slabCubeConfig_typicalFamily hn A R typ q z (hA z.1 z.2)] at hEf
      have hend := typicalCluster_connected_rsCfg n R typ (slabKfix n A R) q z.1 z.2 S hCube _ hEf hy' hw
      exact ⟨a,ha,hstart.trans ((SimpleGraph.Reachable.mono (restrictedGraph_mono _ hTube) hpath).trans hend)⟩

/-- The edge field needed by the shifted-slab exploration, using the same
constants and child rule as the probability estimate. -/
theorem slabChildNest_edgeQ_shifted {d : ℕ} (hd : 6 ≤ d) (hd₂ : 2 ≤ d)
    {n : ℕ} (hn : 0 < n) (hp0 : 0 < (criticalPoint d : ℝ)) (hp1 : (criticalPoint d : ℝ) < 1)
    (R : ℕ) (A : Finset (Bond d)) (typ : TypicalParameters) (k : ℕ) (hk : 0 < k)
    (F : Finset (Vertex d))
    (hA : ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A)
    (hA' : ∀ (e : boxBonds (centeredBox 2 R)) b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A)
    (hb : 0 ≤ typ.boundaryLower) (hc : 0 ≤ typ.countLower)
    {δ cSize CB KA : ℝ} (hδ : typ.regularTolerance ≤ δ)
    (hKA : 4 * (k : ℝ) * typ.boundaryUpper ≤ KA) (hCB : 8 * typ.boundaryUpper ≤ CB)
    (hS : cSize ≤ 4 * (k : ℝ) * typ.boundaryLower)
    (hT : cSize ≤ 4 * typ.countLower * typ.boundaryLower * (2 * (n : ℝ)) ^ (d - 6))
    (hST : cSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2) :
    ∀ q e z ℓ ℓ', (z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) →
      slabSiteOK d n A R typ z (rsΦ d n A R q) = true →
      slabQ d n A R typ k (shiftedSlab d n) F q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ →
      slabChildNest hd₂ n R A typ k hk typ.regularRadius δ cSize CB KA e z ℓ (rsΦ d n A R q) = some ℓ' →
      slabQ d n A R typ k (shiftedSlab d n) F q z ℓ' := by
  intro q e z ℓ ℓ' hz hsite hq hchild
  have hshape := slab_invariant_shape hd hd₂ hn hp0 hp1 R A typ k (shiftedSlab d n) F
    q e z ℓ hz hsite hq hA hb hc hδ hKA hCB hS hT hST
  refine slabChildNest_edgeQ_of_shape hd₂ hn R A typ k hk (shiftedSlab d n) F q e z ℓ ℓ' hz
    hsite hq hA (hA' e) (slabTube_subset_shiftedSlab n e.1.1 e.1.2) ?_ _ _ _ _ _ hshape hchild
  intro x hx
  exact slabCube_subset_shiftedSlab n z.1 ((mem_typicalCube_coarseShift hn z.1 x).1 hx)

end NearCritical
