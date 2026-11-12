module
public import NearCritical.Section9CoalescenceConnection
public import NearCritical.Section9ConditionalPivots
public import NearCritical.Section9FreshEvent
public import NearCritical.Section9MiddleGeometry
public import NearCritical.Section8ReflectionGeometry

/-! Same oriented pivots share one right component. A single left certificate
is disjoint from the UNION of its two right certificates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The right certificates may overlap each other. Their union forces both
right target hits, and the actual full-component disjointness separates that
union from the one left certificate. -/
theorem section9_same_oriented_shared_pivots_occurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A Bᵢ Bⱼ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A Bᵢ e)
    (hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A Bⱼ e) :
    DisjointOccurrence
      (connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (Bᵢ : Set (Vertex d)) ∩
        connectionToSetEvent (R : Set (Vertex d)) e.2 (Bⱼ : Set (Vertex d))) ω := by
  obtain ⟨x,hx⟩ := he.2.2.2.1
  obtain ⟨hxC,hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨b,hb⟩ := he.2.2.2.2.1
  obtain ⟨hbC,hbB⟩ := Finset.mem_inter.mp hb
  obtain ⟨c,hc⟩ := hf.2.2.2.2.1
  obtain ⟨hcC,hcB⟩ := Finset.mem_inter.mp hc
  obtain ⟨S,hSo,hSb,hSf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxC).2
  obtain ⟨U,hUo,hUb,hUf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 b).mp hbC).2
  obtain ⟨V,hVo,hVb,hVf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 c).mp hcC).2
  have hRight (f : Bond d) (hf : f ∈ U ∪ V) :
      f.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2 :=
    (Finset.mem_union.mp hf).elim (hUb f) (hVb f)
  have hdis : Disjoint S (U ∪ V) :=
    disjoint_bond_certificates_of_disjoint_bases he.2.2.2.2.2 hSb hRight
  refine ⟨S,(↑(U ∪ V) : Set (Bond d)),S.finite_toSet,(U ∪ V).finite_toSet,?_,?_,?_⟩
  · exact Set.disjoint_left.mpr (Finset.disjoint_left.mp hdis)
  · intro θ hagree
    apply connectionToSetEvent_mono (Set.Subset.refl _)
      (Set.singleton_subset_iff.mpr hxA) e.1
    exact hSf θ (fun f hf => (hagree f hf).trans (hSo f hf))
  · intro θ hagree
    constructor
    · apply connectionToSetEvent_mono (Set.Subset.refl _)
        (Set.singleton_subset_iff.mpr hbB) e.2
      exact hUf θ (fun f hf =>
        (hagree f (Finset.mem_union_left V hf)).trans (hUo f hf))
    · apply connectionToSetEvent_mono (Set.Subset.refl _)
        (Set.singleton_subset_iff.mpr hcB) e.2
      exact hVf θ (fun f hf =>
        (hagree f (Finset.mem_union_right U hf)).trans (hVo f hf))

/-- Actual canonical same-oriented shared-pivot probabilities under the source
heart law split into one ordinary left hit and a JOINT ordinary right hit.
The source target-facing core is explicit. No independence of the overlapping
tubes, monotonicity of pivotality, or probability estimate is assumed. -/
theorem section9_source_same_oriented_shared_pivot_probability_le {d : ℕ} (p : unitInterval)
    (i : Fin d) (n : ℕ) (hn : 0 < n)
    (H₁ H₃ F₁ F₃ A Bᵢ Bⱼ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (hH₁ : H₁ ⊆ section9FiniteEndCube i n 0)
    (hH₃ : H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)))
    (hpos : percolation d p (section9RevealEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0)
    (_hA : A ⊆ section9FiniteEndCube i n 0)
    (_hBᵢ : ∀ b ∈ Bᵢ, b ∈ section8ExtensionNegativeFaceCore i n)
    (_hBⱼ : ∀ b ∈ Bⱼ, b ∈ section8ExtensionNegativeFaceCore i n) :
    let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let E := orientedLatticePairs (section9FiniteMiddle i n)
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    ν.real {ω | e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bᵢ ∧
      e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bⱼ} ≤
      (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))) *
      (percolation d p).real
        (connectionToSetEvent (R : Set (Vertex d)) e.2 (Bᵢ : Set (Vertex d)) ∩
          connectionToSetEvent (R : Set (Vertex d)) e.2 (Bⱼ : Set (Vertex d))) := by
  intro L R Q₁ Q₃ E ν
  let J : Set (Configuration d) := {ω | e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bᵢ ∧
    e ∈ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A Bⱼ}
  let X := connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))
  let Y := connectionToSetEvent (R : Set (Vertex d)) e.2 (Bᵢ : Set (Vertex d)) ∩
    connectionToSetEvent (R : Set (Vertex d)) e.2 (Bⱼ : Set (Vertex d))
  let S := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  have hJ : MeasurableSet J := by
    have hi : MeasurableSet {ω : Configuration d | e ∈ E ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A Bᵢ e} :=
      (MeasurableSet.const _).inter (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A Bᵢ e)
    have hj : MeasurableSet {ω : Configuration d | e ∈ E ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A Bⱼ e} :=
      (MeasurableSet.const _).inter (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A Bⱼ e)
    simpa only [J,sprinklingPivotalPairs,Finset.mem_filter,Set.inter_def,Set.mem_setOf_eq] using hi.inter hj
  have hlocal : ∀ ω θ : Configuration d, (∀ b ∈ S, ω b = θ b) → (ω ∈ J ↔ θ ∈ J) := by
    intro ω θ hagree
    have hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = θ b :=
      fun b hb => hagree b (Finset.mem_union_left _ hb)
    have hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = θ b :=
      fun b hb => hagree b (Finset.mem_union_right _ hb)
    simp only [J,Set.mem_setOf_eq,sprinklingPivotalPairs,Finset.mem_filter,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A Bᵢ ω θ hL hR e,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A Bⱼ ω θ hL hR e]
  have hfresh := section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
    S (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃
      (section9FiniteLeftTube_disjoint_third i hn) (section9FiniteRightTube_disjoint_first i hn)) J hJ hlocal
  have hsub : J ⊆ {ω | DisjointOccurrence X Y ω} := by
    intro ω hω
    exact section9_same_oriented_shared_pivots_occurrence ω L R Q₁ F₁ Q₃ F₃ A Bᵢ Bⱼ e
      (Finset.mem_filter.mp hω.1).2 (Finset.mem_filter.mp hω.2).2
  have hX : BK.Increasing X := connectionToSetEvent_increasing _ _ _
  have hY : BK.Increasing Y := by
    intro ω θ h hω
    exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
      connectionToSetEvent_increasing _ _ _ h hω.2⟩
  change ν.real J ≤ (percolation d p).real X*(percolation d p).real Y
  rw [hfresh]
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (percolation_bk d p X Y hX hY)

end NearCritical
