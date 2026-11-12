module

public import NearCritical.SlabStepBoundaryData
public import NearCritical.SlabChildWitness
public import NearCritical.SlabOriginOffspringBound
public import NearCritical.Section10Section9Geometry

/-! The concrete edge rule reads exactly the stored parent, the target
cube block and the fresh edge block. -/
@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Function Section10
open scoped Classical

def SlabStepBoundaryData.source {d : ℕ} (D : SlabStepBoundaryData d)
    (typ : TypicalParameters) (n : ℕ) (i : Fin d) (C : Finset (Vertex d)) : Finset (Vertex d) :=
  slabRegularPatch typ n 0 D.parentHeart C (i, true) true

def SlabStepBoundaryData.target {d : ℕ} (D : SlabStepBoundaryData d)
    (typ : TypicalParameters) (n : ℕ) (i : Fin d) (C : Finset (Vertex d)) : Finset (Vertex d) :=
  let c := farCenter n 0 i
  slabRegularPatch typ n c D.childHeart C (i, false) true ∪
    slabRegularPatch typ n c D.childHeart C (i, false) false

/-- Boundary and reveal conditions for the Section 9 offspring estimate.
They depend on the stored parent and target cube, before any tube is read. -/
structure SlabOffspringShape {d : ℕ} (typ : TypicalParameters) (n k : ℕ) (i : Fin d)
    (D : SlabStepBoundaryData d) (r : ℕ) (δ cSize CB KA : ℝ) : Prop where
  parentCard : D.parentNest.card = k
  revealNonzero : percolation d (criticalPoint d) (section9RevealEvent
    (section9FiniteEndCube i n 0) (typicalHeart n 0 typ.heartRatio)
    (section9FiniteEndCube i n (2*(n : ℝ))) (typicalHeart n (farCenter n 0 i) typ.heartRatio)
    D.parentHeart D.childHeart) ≠ 0
  sourceCore : ∀ x ∈ sprinklingTargetBoundary D.parentNest (D.source typ n i),
    x ∈ section8ExtensionPositiveFaceCore i n
  sourceRegular : ∀ x ∈ sprinklingTargetBoundary D.parentNest (D.source typ n i),
    sourceRegularPoint D.parentHeart (section8ExtensionSmallCube i n) (typicalBoundary n 0) r δ x
  targetCore : ∀ y ∈ D.childCandidates.biUnion (D.target typ n i),
    y ∈ section8ExtensionNegativeFaceCore i n
  targetRegular : ∀ y ∈ D.childCandidates.biUnion (D.target typ n i),
    sourceRegularPoint D.childHeart
      ((section8ExtensionSmallCube i n).image (affineReflection (Pi.single i (2*(n : ℤ)))))
      (typicalBoundary n (farCenter n 0 i)) r δ y
  targetDisjoint : Set.PairwiseDisjoint (D.childCandidates : Set (Finset (Vertex d))) (D.target typ n i)
  sourceUpper : ((sprinklingTargetBoundary D.parentNest (D.source typ n i)).card : ℝ) ≤ KA*(n : ℝ)^2
  targetUpper : ∀ C ∈ D.childCandidates, (((D.target typ n i C).card : ℕ) : ℝ) ≤ CB*(n : ℝ)^2
  sourceLower : cSize*(n : ℝ)^2 ≤ ((sprinklingTargetBoundary D.parentNest (D.source typ n i)).card : ℝ)
  targetLower : cSize*(n : ℝ)^2 ≤ ((D.childCandidates.biUnion (D.target typ n i)).card : ℝ)
  productLower : cSize*(n : ℝ)^((d : ℝ)-2) ≤
    ((sprinklingTargetBoundary D.parentNest (D.source typ n i)).card : ℝ) *
      ((D.childCandidates.biUnion (D.target typ n i)).card : ℝ)

/-- The deterministic edge calculation from its local inputs. -/
def slabChildNestOfBlocks {d : ℕ} (hd : 2 ≤ d) (n R : ℕ) (A : Finset (Bond d))
    (typ : TypicalParameters) (k : ℕ) (hk : 0 < k) (r : ℕ) (δ cSize CB KA : ℝ)
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R)
    (siteOK : Bool) (D : SlabStepBoundaryData d) (y : rsΩ d n A R (Sum.inr e)) : Option (SlabNest d) :=
  let rev := slabEdgeReverse e z
  let i := Fin.castLE hd e.1.2
  if h : (z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) ∧
      siteOK = true ∧ SlabOffspringShape typ n k i D r δ cSize CB KA then
    let ω := pullbackLayerPair (slabChartBond hd n e.1 rev) (slabTubePair n A R e y)
    let φ := slabChartEquiv hd n e.1 rev
    (slabStepChildNest (section9FiniteMiddle i n)
      (section9FiniteTube i n (-(5:ℝ)/8) (3/8)) (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
      (section9FiniteEndCube i n 0) D.parentHeart (section9FiniteEndCube i n (2*(n : ℝ))) D.childHeart
      D.parentNest D.childCandidates (D.source typ n i) (D.target typ n i) ω hk h.2.2.parentCard).map
      (fun result => (result.2.image (chartCluster φ), chartCluster φ D.childHeart))
  else some (∅, ∅)

/-- The child rule in the slab. The exploration invariant supplies the
guard on genuine edge moves. Other inputs get a dummy success. -/
def slabChildNest {d : ℕ} (hd : 2 ≤ d) (n R : ℕ) (A : Finset (Bond d))
    (typ : TypicalParameters) (k : ℕ) (hk : 0 < k) (r : ℕ) (δ cSize CB KA : ℝ)
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) (ℓ : SlabNest d)
    (x : ∀ j, rsΩ d n A R j) : Option (SlabNest d) :=
  slabChildNestOfBlocks hd n R A typ k hk r δ cSize CB KA e z
    (slabSiteOK d n A R typ z x) (slabStepBoundaryData hd n R A typ e z ℓ x) (x (Sum.inr e))

theorem slabChildNest_local {d : ℕ} (hd : 2 ≤ d) (n R : ℕ) (A : Finset (Bond d))
    (typ : TypicalParameters) (k : ℕ) (hk : 0 < k) (r : ℕ) (δ cSize CB KA : ℝ)
    (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) (ℓ : SlabNest d)
    (x x' : ∀ j, rsΩ d n A R j) (he : x (Sum.inr e) = x' (Sum.inr e))
    (hz : x (Sum.inl z) = x' (Sum.inl z)) :
    slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ x =
      slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ x' := by
  unfold slabChildNest
  rw [slabStepBoundaryData_local hd n R A typ e z ℓ x x' hz, slabSiteOK_local n A R typ z x x' hz, he]

/-- The edge rule has the failure probability of the offspring count on
valid inputs, and succeeds identically on inputs outside the guard. -/
theorem slabChildNest_failure_le {d : ℕ} (hd : 2 ≤ d) (n R : ℕ) (A : Finset (Bond d))
    (typ : TypicalParameters) (k : ℕ) (hk : 0 < k) (r : ℕ) (δ cSize CB KA : ℝ)
    (s : unitInterval) {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ (e : boxBonds (centeredBox 2 R)) (rev : Bool) (D : SlabStepBoundaryData d),
      let i := Fin.castLE hd e.1.2
      SlabOffspringShape typ n k i D r δ cSize CB KA →
      (rsν d n A R (criticalPoint d) s (Sum.inr e)).real
        {y | ¬ k*k ≤ (slabStepOffspring (section9FiniteMiddle i n)
          (section9FiniteTube i n (-(5:ℝ)/8) (3/8)) (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
          (section9FiniteEndCube i n 0) D.parentHeart (section9FiniteEndCube i n (2*(n : ℝ))) D.childHeart
          (sprinklingTargetBoundary D.parentNest (D.source typ n i)) D.childCandidates (D.target typ n i)
          (pullbackLayerPair (slabChartBond hd n e.1 rev) (slabTubePair n A R e y))).card} ≤ ε) :
    ∀ e z ℓ (x : ∀ j, rsΩ d n A R j),
      (rsν d n A R (criticalPoint d) s (Sum.inr e)).real
        {y | ¬ (slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ
          (update x (Sum.inr e) y)).isSome = true} ≤ ε := by
  intro e z ℓ x
  let rev := slabEdgeReverse e z
  let i := Fin.castLE hd e.1.2
  let D := slabStepBoundaryData hd n R A typ e z ℓ x
  have htarget (y : rsΩ d n A R (Sum.inr e)) : (update x (Sum.inr e) y) (Sum.inl z) = x (Sum.inl z) :=
    update_of_ne (by simp) _ _
  have hdata (y : rsΩ d n A R (Sum.inr e)) :
      slabStepBoundaryData hd n R A typ e z ℓ (update x (Sum.inr e) y) = D :=
    slabStepBoundaryData_local hd n R A typ e z ℓ _ _ (htarget y)
  have hsite (y : rsΩ d n A R (Sum.inr e)) :
      slabSiteOK d n A R typ z (update x (Sum.inr e) y) = slabSiteOK d n A R typ z x :=
    slabSiteOK_local n A R typ z _ _ (htarget y)
  by_cases hg : (z = (boxEnds (centeredBox 2 R) e).1 ∨ z = (boxEnds (centeredBox 2 R) e).2) ∧
      slabSiteOK d n A R typ z x = true ∧ SlabOffspringShape typ n k i D r δ cSize CB KA
  · convert hbound e rev D hg.2.2 using 2
    ext y
    change (¬ (slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ
      (update x (Sum.inr e) y)).isSome = true) ↔ _
    simp only [slabChildNest, hdata y, hsite y, update_self]
    unfold slabChildNestOfBlocks
    rw [dif_pos hg, Option.isSome_map, slabStepChildNest_isSome_iff] <;> rfl
  · have hempty : {y | ¬ (slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ
        (update x (Sum.inr e) y)).isSome = true} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, slabChildNest, hdata y, hsite y, update_self]
      unfold slabChildNestOfBlocks
      rw [dif_neg hg]
      simp
    rw [hempty, measureReal_empty]
    exact hε

/-- The paper's choice of parameters gives a uniform failure bound for the
concrete child rule on every edge and every stored parent. -/
theorem slabChildNest_quantitative {d : ℕ} (hd : 9 ≤ d) (asymptotics : TwoPointAsymptotics d)
    (rectangle : RestrictedRectangleLowerInput d) (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ k : ℕ, ∀ hk : 0 < k, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N₀ : ℕ, 16*(r+1) ≤ N₀ ∧ ∀ (n : ℕ), N₀ ≤ n →
      ∀ s : unitInterval, Lambda ≤ (s : ℝ)*(n : ℝ)^2 →
      ∀ (R : ℕ) (A : Finset (Bond d)),
      (∀ (e : boxBonds (centeredBox 2 R)) b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A) →
      ∀ (typ : TypicalParameters) e z ℓ (x : ∀ j, rsΩ d n A R j),
        (rsν d n A R (criticalPoint d) s (Sum.inr e)).real
          {y | ¬ (slabChildNest (show 2 ≤ d by omega) n R A typ k hk r δ cSize CB KA e z ℓ
            (update x (Sum.inr e) y)).isSome = true} ≤ ε := by
  obtain ⟨δ,hδ,h⟩ := slab_origin_offspring_failure_le hd asymptotics rectangle reimer
  refine ⟨δ,hδ,?_⟩
  intro r hr ε hε
  obtain ⟨cSize,hc,h⟩ := h r hr ε hε
  refine ⟨cSize,hc,?_⟩
  intro k hk
  obtain ⟨Lambda,hLambda,h⟩ := h (k*k)
  refine ⟨Lambda,hLambda,?_⟩
  intro CB KA hCB hKA
  obtain ⟨N₀,hN₀,h⟩ := h CB KA hCB hKA
  refine ⟨N₀,hN₀,?_⟩
  intro n hn s hs R A hA typ
  refine slabChildNest_failure_le (show 2 ≤ d by omega) n R A typ k hk r δ cSize CB KA s hε.le ?_
  intro e rev D i hD
  have hn0 : 0 < n := by omega
  have h₁ : typicalHeart n (0 : Vertex d) typ.heartRatio ⊆ section9FiniteEndCube i n 0 := by
    rw [← typicalCube_zero_eq_endCube hn0 i]
    exact Finset.filter_subset _ _
  have h₃ : typicalHeart n (farCenter n (0 : Vertex d) i) typ.heartRatio ⊆
      section9FiniteEndCube i n (2*(n : ℝ)) := by
    rw [← typicalCube_far_eq_endCube hn0 i]
    exact Finset.filter_subset _ _
  exact h n hn s hs R A e rev (hA e) D.childCandidates (D.target typ n i)
    _ _ D.parentHeart D.childHeart _ _ _
    h₁ h₃ hD.revealNonzero hD.sourceCore hD.sourceRegular hD.targetCore hD.targetRegular
    hD.targetDisjoint hD.sourceUpper hD.targetUpper hD.sourceLower hD.targetLower hD.productLower
    (k*k) (Nat.le_succ _)

/-- The real failure bound gives the exact probability field used by
`resampledSlabNestInputs_of_edge`. -/
theorem slabChildNest_pedge_of_failure_le {d : ℕ} (hd : 2 ≤ d) (n R : ℕ) (A : Finset (Bond d))
    (typ : TypicalParameters) (k : ℕ) (hk : 0 < k) (r : ℕ) (δ cSize CB KA : ℝ)
    (s : unitInterval) {ε : ℝ} (κ : Measure Bool) (hκ : κ {true} ≤ ENNReal.ofReal (1 - ε))
    (hfail : ∀ e z ℓ (x : ∀ j, rsΩ d n A R j),
      (rsν d n A R (criticalPoint d) s (Sum.inr e)).real
        {y | ¬ (slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ
          (update x (Sum.inr e) y)).isSome = true} ≤ ε) :
    ∀ e z ℓ (x : ∀ j, rsΩ d n A R j),
      κ {true} ≤ rsν d n A R (criticalPoint d) s (Sum.inr e)
        {y | (slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ
          (update x (Sum.inr e) y)).isSome = true} := by
  intro e z ℓ x
  let μ := rsν d n A R (criticalPoint d) s (Sum.inr e)
  let E : Set (rsΩ d n A R (Sum.inr e)) :=
    {y | (slabChildNest hd n R A typ k hk r δ cSize CB KA e z ℓ
      (update x (Sum.inr e) y)).isSome = true}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have h : μ.real Eᶜ ≤ ε := hfail e z ℓ x
  rw [measureReal_compl hE, probReal_univ] at h
  have hreal : 1 - ε ≤ μ.real E := by linarith
  exact hκ.trans ((ENNReal.ofReal_le_ofReal hreal).trans_eq (ENNReal.ofReal_toReal (measure_ne_top μ E)))

end NearCritical
