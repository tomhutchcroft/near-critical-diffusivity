module

public import NearCritical.SlabChartReveal
public import NearCritical.SlabInvariantReveal

/-! Successful tube paths in parent coordinates belong to the actual
resampled configuration of the slab. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

theorem slabEdge_sites {R : ℕ} (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R)
    (hz : z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) :
    let rev := slabEdgeReverse e z
    (otherEnd (boxEnds (centeredBox 2 R)) e z).1 = (if rev then bondTip e.1 else e.1.1) ∧
      z.1 = (if rev then e.1.1 else bondTip e.1) := by
  have hn := bondTip_ne_base e.1
  have hends : (boxEnds (centeredBox 2 R) e).1 ≠ (boxEnds (centeredBox 2 R) e).2 :=
    fun he => hn (congrArg Subtype.val he).symm
  rcases hz with rfl | rfl
  · simp [slabEdgeReverse, otherEnd, boxEnds]
  · have hrev : slabEdgeReverse e (boxEnds (centeredBox 2 R) e).2 = false := by
      simp [slabEdgeReverse, boxEnds, hn]
    have ha : otherEnd (boxEnds (centeredBox 2 R)) e (boxEnds (centeredBox 2 R) e).2 =
        (boxEnds (centeredBox 2 R) e).1 := if_neg hends
    dsimp only
    rw [hrev, ha]
    exact ⟨rfl,rfl⟩

set_option maxHeartbeats 900000 in
theorem slabStepView_invariant_eq {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (R : ℕ) (A : Finset (Bond d)) (typ : TypicalParameters) (k : ℕ)
    (S : Set (Vertex d)) (F : Finset (Vertex d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) (ℓ : SlabNest d)
    (hz : z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2)
    (hq : slabQ d n A R typ k S F q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ)
    (hA : ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A)
    (hA' : ∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A) :
    let rev := slabEdgeReverse e z
    let i := Fin.castLE hd e.1.2
    let M := section9FiniteMiddle i n
    let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
    let V := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let D := slabStepBoundaryData hd n R A typ e z ℓ (rsΦ d n A R q)
    let g := slabChartBond hd n e.1 rev
    let ω := resampleLayers (centeredBox 2 R) (fun v => typicalCube n (coarseShift n v))
      (fun v => typicalHeart n (coarseShift n v) typ.heartRatio) (slabKfix n A R) q
    stepView M L V Q₁ D.parentHeart Q₃ D.childHeart
      (pullbackLayerPair g (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e)))) =
    stepView M L V Q₁ D.parentHeart Q₃ D.childHeart
      (pullbackLayerPair g (criticalLayer ω, sprinkleLayer q.1)) := by
  intro rev i M L V Q₁ Q₃ D g ω
  let T := sprinklingTube i n (-(5:ℝ)/8) (5/8)
  let a := otherEnd (boxEnds (centeredBox 2 R)) e z
  let φ := slabChartEquiv hd n e.1 rev
  let Q := fun v : Vertex 2 => typicalCube n (coarseShift (d := d) n v)
  let H := fun v : Vertex 2 => typicalHeart n (coarseShift (d := d) n v) typ.heartRatio
  let U := fun v : Vertex 2 => heartClusterUnion (criticalLayer q.1) (Q v) (H v)
  obtain ⟨hsite₁,hsite₃⟩ := slabEdge_sites e z hz
  change a.1 = (if rev then bondTip e.1 else e.1.1) at hsite₁
  change z.1 = (if rev then e.1.1 else bondTip e.1) at hsite₃
  obtain ⟨hcentre₁,hcentre₃⟩ := slabChartEdge_centres hd n R e z hz
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : (L : Set (Vertex d)) ⊆ T := fun x hx =>
    sprinklingLeftTube_subset i hnR ((mem_section9FiniteTube i n _ _ (by norm_num) (by norm_num) x).1 hx)
  have hV : (V : Set (Vertex d)) ⊆ T := fun x hx =>
    sprinklingRightTube_subset i hnR ((mem_section9FiniteTube i n _ _ (by norm_num) (by norm_num) x).1 hx)
  have hML : M ⊆ L := by
    change section9FiniteMiddle i n ⊆ L
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_left
  have hMV : M ⊆ V := by
    change section9FiniteMiddle i n ⊆ V
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_right
  have hQ₁ (x : Vertex d) : x ∈ Q₁ ↔ φ x ∈ Q a.1 := by
    change x ∈ section9FiniteEndCube i n 0 ↔ _
    rw [← typicalCube_zero_eq_endCube hn i]
    have h := (mem_typicalCube_slabChart_iff hd hn e.1 rev x 0).symm
    rw [← slabChartEquiv_apply, ← slabChartEquiv_apply] at h
    change _ ↔ φ x ∈ typicalCube n (φ 0) at h
    rw [hcentre₁] at h
    exact h
  have hQ₃ (x : Vertex d) : x ∈ Q₃ ↔ φ x ∈ Q z.1 := by
    change x ∈ section9FiniteEndCube i n (2*(n : ℝ)) ↔ _
    rw [← typicalCube_far_eq_endCube hn i]
    have h := (mem_typicalCube_slabChart_iff hd hn e.1 rev x (farCenter n 0 i)).symm
    rw [← slabChartEquiv_apply, ← slabChartEquiv_apply] at h
    change _ ↔ φ x ∈ typicalCube n (φ (farCenter n 0 i)) at h
    rw [hcentre₃] at h
    exact h
  have hD₁ : D.parentHeart = chartCluster φ.symm (U a.1) :=
    congrArg (chartCluster φ.symm)
      (hq.2.2.1.trans (slabCubeConfig_heartUnion hn A R typ.heartRatio q a (hA a.1 a.2)))
  have hD₃ : D.childHeart = chartCluster φ.symm (U z.1) :=
    congrArg (chartCluster φ.symm) (slabCubeConfig_heartUnion hn A R typ.heartRatio q z (hA z.1 z.2))
  refine slab_chart_stepView_resample_eq hd hn R A typ.heartRatio e rev q M L V Q₁ D.parentHeart
    Q₃ D.childHeart hA' (fun x hx => hL (hML hx)) hL hV (origin_L_disjoint_far i)
    (origin_R_disjoint_near i) (Finset.disjoint_of_subset_left hMV (origin_R_disjoint_near i))
    (Finset.disjoint_of_subset_left hML (origin_L_disjoint_far i)) ?_ ?_ ?_ ?_
  · intro x
    change x ∈ Q₁ ↔ slabChartVertex hd n e.1 rev x ∈ Q (if rev then bondTip e.1 else e.1.1)
    rw [← hsite₁, ← slabChartEquiv_apply]
    exact hQ₁ x
  · intro x
    rw [hD₁]
    change x ∈ chartCluster φ.symm (U a.1) ↔ slabChartVertex hd n e.1 rev x ∈
      U (if rev then bondTip e.1 else e.1.1)
    rw [← hsite₁]
    simp only [chartCluster, Finset.mem_map_equiv, Equiv.symm_symm, φ, slabChartEquiv_apply] <;> rfl
  · intro x
    change x ∈ Q₃ ↔ slabChartVertex hd n e.1 rev x ∈ Q (if rev then e.1.1 else bondTip e.1)
    rw [← hsite₃, ← slabChartEquiv_apply]
    exact hQ₃ x
  · intro x
    rw [hD₃]
    change x ∈ chartCluster φ.symm (U z.1) ↔ slabChartVertex hd n e.1 rev x ∈
      U (if rev then e.1.1 else bondTip e.1)
    rw [← hsite₃]
    simp only [chartCluster, Finset.mem_map_equiv, Equiv.symm_symm, φ, slabChartEquiv_apply] <;> rfl

set_option maxHeartbeats 900000 in
/-- Every selected offspring has a path between its two actual regular
patches in the physical resampled tube. -/
theorem slab_invariant_child_arrival {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (R : ℕ) (A : Finset (Bond d)) (typ : TypicalParameters) (k : ℕ)
    (S : Set (Vertex d)) (F : Finset (Vertex d))
    (q : (Bond d × Bool → Bool) × (Bond d × Bool → Bool))
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) (ℓ : SlabNest d)
    (hz : z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2)
    (hq : slabQ d n A R typ k S F q (otherEnd (boxEnds (centeredBox 2 R)) e z) ℓ)
    (hA : ∀ v ∈ centeredBox 2 R, ∀ b : Bond d, bondIn (slabCube n v) b → b ∈ A)
    (hA' : ∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A) :
    let rev := slabEdgeReverse e z
    let i := Fin.castLE hd e.1.2
    let M := section9FiniteMiddle i n
    let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
    let V := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let D := slabStepBoundaryData hd n R A typ e z ℓ (rsΦ d n A R q)
    let g := slabChartBond hd n e.1 rev
    let f := slabChartEquiv hd n e.1 rev
    let v := stepView M L V Q₁ D.parentHeart Q₃ D.childHeart
      (pullbackLayerPair g (slabTubePair n A R e (rsΦ d n A R q (Sum.inr e))))
    let U := sprinklingTargetBoundary D.parentNest (D.source typ n i)
    ∀ C E : Finset (Vertex d),
      E ∈ sprinklingOffspring v.1 v.2.1 (D.source typ n i C) D.childCandidates (D.target typ n i)
        (v.2.2.1 U (sprinklingTargetBoundary D.childCandidates (D.target typ n i))) →
      ∃ x ∈ C, ∃ y ∈ E,
        (restrictedGraph (rsCfg d n R typ.heartRatio (slabKfix n A R) q)
          (slabTube n e.1.1 e.1.2)).Reachable (f x) (f y) := by
  intro rev i M L V Q₁ Q₃ D g f v U C E hE
  let Q := fun w : Vertex 2 => typicalCube n (coarseShift (d := d) n w)
  let H := fun w : Vertex 2 => typicalHeart n (coarseShift (d := d) n w) typ.heartRatio
  let K := slabKfix n A R
  let ω := resampleLayers (centeredBox 2 R) Q H K q
  let p := pullbackLayerPair g (criticalLayer ω, sprinkleLayer q.1)
  let T := sprinklingTube i n (-(5:ℝ)/8) (5/8)
  have hv : v = stepView M L V Q₁ D.parentHeart Q₃ D.childHeart p :=
    slabStepView_invariant_eq hd hn R A typ k S F q e z ℓ hz hq hA hA'
  rw [hv] at hE
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : (L : Set (Vertex d)) ⊆ T := fun x hx =>
    sprinklingLeftTube_subset i hnR ((mem_section9FiniteTube i n _ _ (by norm_num) (by norm_num) x).1 hx)
  have hV : (V : Set (Vertex d)) ⊆ T := fun x hx =>
    sprinklingRightTube_subset i hnR ((mem_section9FiniteTube i n _ _ (by norm_num) (by norm_num) x).1 hx)
  have hM : (M : Set (Vertex d)) ⊆ T := by
    intro x hx
    change x ∈ section9FiniteMiddle i n at hx
    rw [section9FiniteMiddle_eq_inter] at hx
    exact hL (Finset.mem_inter.mp hx).1
  obtain ⟨x,hx,y,hy,hr⟩ := slabStep_child_path M L V Q₁ D.parentHeart Q₃ D.childHeart U
    D.childCandidates (D.target typ n i) p T hL hV hM (D.source typ n i C) hE
  have hcfg : sprinkleOrConfiguration p.1 p.2 =
      fun b => rsCfg d n R typ.heartRatio K q (g b) := by
    funext b
    have hb : ω (g b, false) = q.1 (g b, false) := by
      apply resample_first_copy_off_strip
      simp [mem_layerSet]
    change (ω (g b,true) || q.1 (g b,false)) = (ω (g b,true) || ω (g b,false))
    rw [hb]
  rw [hcfg] at hr
  have hxC := (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
  have hyE : y ∈ E := by
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.mem_inter.mp (Finset.mem_filter.mp hy).1).1
    · exact (Finset.mem_inter.mp (Finset.mem_filter.mp hy).1).1
  refine ⟨x,hxC,y,hyE,?_⟩
  simpa only [f, slabChartEquiv_apply] using
    slabChart_reachable hd n e.1 rev (rsCfg d n R typ.heartRatio K q) hr

end NearCritical
