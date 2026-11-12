module

public import NearCritical.SlabChartHeart
public import NearCritical.SlabInvariantPatchBounds
public import NearCritical.SlabCubeCorrespondence

/-! The endpoint heart records of a valid move are jointly realized in the
pullback of the original first-copy configuration. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

theorem slab_chart_realizes_endpoint_hearts {d : ℕ} (hd : 2 ≤ d) (typ : TypicalParameters)
    {n : ℕ} (hn : 0 < n) (e : Bond 2) (rev : Bool) (ω : Configuration d) :
    let i := Fin.castLE hd e.2
    let φ := slabChartEquiv hd n e rev
    let ω₀ : Configuration d := fun b => ω (slabChartBond hd n e rev b)
    ∀ c : Vertex d, chartCluster φ.symm
      (heartClusterUnion ω (typicalCube n (φ c)) (typicalHeart n (φ c) typ.heartRatio)) =
      heartClusterUnion ω₀ (typicalCube n c) (typicalHeart n c typ.heartRatio) := by
  intro i φ ω₀ c
  let f := slabChartVertex hd n e rev
  have hImage (U : Finset (Vertex d)) : U.image f = chartCluster φ U := by
    rw [chartCluster, Finset.map_eq_image]
    exact congrArg (fun g : Vertex d → Vertex d => U.image g)
      (funext fun x => (slabChartEquiv_apply hd n e rev x).symm)
  have hQ : (typicalCube n c).image f = typicalCube n (φ c) := by
    rw [hImage]
    exact chartCluster_eq_of_mem φ _ _ (fun x => by
      simpa only [φ, slabChartEquiv_apply] using mem_typicalCube_slabChart_iff hd hn e rev x c)
  have hH : (typicalHeart n c typ.heartRatio).image f = typicalHeart n (φ c) typ.heartRatio := by
    rw [hImage]
    exact chartCluster_eq_of_mem φ _ _ (fun x => by
      simpa only [φ, slabChartEquiv_apply] using mem_typicalHeart_slabChart_iff hd hn e rev x c typ.heartRatio)
  ext x
  have h := mem_heartClusterUnion_slabChart_iff hd n e rev ω (typicalCube n c) (typicalHeart n c typ.heartRatio) x
  change f x ∈ heartClusterUnion ω ((typicalCube n c).image f) ((typicalHeart n c typ.heartRatio).image f) ↔ _ at h
  rw [hQ,hH] at h
  simpa only [chartCluster, Finset.mem_map_equiv, Equiv.symm_symm, φ, f, slabChartEquiv_apply] using h

set_option maxHeartbeats 900000 in
theorem slab_invariant_reveal_ne_zero {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (hp0 : 0 < (criticalPoint d : ℝ)) (hp1 : (criticalPoint d : ℝ) < 1)
    (R : ℕ) (A : Finset (Bond d)) (typ : TypicalParameters)
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) (ℓ : SlabNest d)
    (hz : z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2)
    (ω : Configuration d) :
    let a := otherEnd (boxEnds (centeredBox 2 R)) e z
    let Q := fun v : centeredBox 2 R => typicalCube n (coarseShift (d := d) n v.1)
    let H := fun v : centeredBox 2 R => typicalHeart n (coarseShift (d := d) n v.1) typ.heartRatio
    let D := slabStepBoundaryData hd n R A typ e z ℓ (rsΦ d n A R q)
    let i := Fin.castLE hd e.1.2
    ℓ.2 = heartClusterUnion ω (Q a) (H a) →
    heartClusterUnion (slabCubeConfig d n A R (rsΦ d n A R q) z) (Q z) (H z) =
      heartClusterUnion ω (Q z) (H z) →
    percolation d (criticalPoint d) (section9RevealEvent
      (section9FiniteEndCube i n 0) (typicalHeart n 0 typ.heartRatio)
      (section9FiniteEndCube i n (2*(n : ℝ))) (typicalHeart n (farCenter n 0 i) typ.heartRatio)
      D.parentHeart D.childHeart) ≠ 0 := by
  intro a Q H D i hparent hchild
  let rev := slabEdgeReverse e z
  let φ := slabChartEquiv hd n e.1 rev
  let ω₀ : Configuration d := fun b => ω (slabChartBond hd n e.1 rev b)
  obtain ⟨ha,hz'⟩ := slabChartEdge_centres hd n R e z hz
  change φ 0 = coarseShift n a.1 at ha
  change φ (farCenter n 0 i) = coarseShift n z.1 at hz'
  have h₁ : D.parentHeart = heartClusterUnion ω₀ (typicalCube n 0) (typicalHeart n 0 typ.heartRatio) := by
    change chartCluster φ.symm ℓ.2 = _
    rw [hparent]
    have h := slab_chart_realizes_endpoint_hearts hd typ hn e.1 rev ω (0 : Vertex d)
    change chartCluster φ.symm (heartClusterUnion ω (typicalCube n (φ 0))
      (typicalHeart n (φ 0) typ.heartRatio)) = _ at h
    rw [ha] at h
    exact h
  have h₃ : D.childHeart = heartClusterUnion ω₀ (typicalCube n (farCenter n 0 i))
      (typicalHeart n (farCenter n 0 i) typ.heartRatio) := by
    change chartCluster φ.symm (heartClusterUnion (slabCubeConfig d n A R (rsΦ d n A R q) z)
      (Q z) (H z)) = _
    rw [hchild]
    have h := slab_chart_realizes_endpoint_hearts hd typ hn e.1 rev ω (farCenter n 0 i)
    change chartCluster φ.symm (heartClusterUnion ω (typicalCube n (φ (farCenter n 0 i)))
      (typicalHeart n (φ (farCenter n 0 i)) typ.heartRatio)) = _ at h
    rw [hz'] at h
    exact h
  rw [← typicalCube_zero_eq_endCube hn i, ← typicalCube_far_eq_endCube hn i, h₁, h₃]
  exact revealEvent_ne_zero_of_realised (criticalPoint d) hp0 hp1 _ _ _ _
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) ω₀

set_option maxHeartbeats 900000 in
/-- A genuine exploration move satisfies the guard on the concrete rule. -/
theorem slab_invariant_shape {d : ℕ} (hd : 6 ≤ d) (hd₂ : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (hp0 : 0 < (criticalPoint d : ℝ)) (hp1 : (criticalPoint d : ℝ) < 1)
    (R : ℕ) (A : Finset (Bond d)) (typ : TypicalParameters) (k : ℕ)
    (S : Set (Vertex d)) (F : Finset (Vertex d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) (ℓ : SlabNest d)
    (hz : z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2)
    (hsite : slabSiteOK d n A R typ z (rsΦ d n A R q) = true)
    (hq : slabQ d n A R typ k S F q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ)
    (hA : ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A)
    (hb : 0 ≤ typ.boundaryLower) (hc : 0 ≤ typ.countLower)
    {δ cSize CB KA : ℝ} (hδ : typ.regularTolerance ≤ δ)
    (hKA : 4 * (k : ℝ) * typ.boundaryUpper ≤ KA) (hCB : 8 * typ.boundaryUpper ≤ CB)
    (hS : cSize ≤ 4 * (k : ℝ) * typ.boundaryLower)
    (hT : cSize ≤ 4 * typ.countLower * typ.boundaryLower * (2 * (n : ℝ)) ^ (d - 6))
    (hST : cSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2) :
    SlabOffspringShape typ n k (Fin.castLE hd₂ e.1.2)
      (slabStepBoundaryData hd₂ n R A typ e z ℓ (rsΦ d n A R q)) typ.regularRadius δ cSize CB KA := by
  let a := otherEnd (boxEnds (centeredBox 2 R)) e z
  have hbound := slab_patch_bounds_of_invariant hd₂ hn R A typ k S F q e z ℓ hz hsite hq
  apply slabOffspringShape_of_patches hd typ hn k _ _ hbound hb hc hδ hKA hCB hS hT hST
  exact slab_invariant_reveal_ne_zero hd₂ hn hp0 hp1 R A typ q e z ℓ hz (criticalLayer q.1)
    (hq.2.2.1.trans (slabCubeConfig_heartUnion hn A R typ.heartRatio q a (hA a.1 a.2)))
    (slabCubeConfig_heartUnion hn A R typ.heartRatio q z (hA z.1 z.2))

end NearCritical
