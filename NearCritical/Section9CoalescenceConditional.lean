module

public import NearCritical.Section9FreshEvent
public import NearCritical.Section9CoalescenceCaseThreeInclusion
public import NearCritical.Section9PivotalSupport
public import NearCritical.Section9PivotalCount

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Equality of two deleted components is measurable by testing membership
of every vertex. -/
theorem measurableSet_section9_same_component {d : ℕ} (R Q F : Finset (Vertex d))
    (a b : Vertex d) :
    MeasurableSet {ω | sprinklingUnexploredCluster ω R Q F a =
      sprinklingUnexploredCluster ω R Q F b} := by
  let A := fun z => {ω | z ∈ sprinklingUnexploredCluster ω R Q F a}
  let B := fun z => {ω | z ∈ sprinklingUnexploredCluster ω R Q F b}
  have hEq : {ω | sprinklingUnexploredCluster ω R Q F a =
      sprinklingUnexploredCluster ω R Q F b} = ⋂ z, (A z ∩ B z) ∪ ((A z)ᶜ ∩ (B z)ᶜ) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, A, B, Finset.ext_iff]
    constructor
    · intro h z
      by_cases hz : z ∈ sprinklingUnexploredCluster ω R Q F a
      · exact Or.inl ⟨hz, (h z).mp hz⟩
      · exact Or.inr ⟨hz, fun hb => hz ((h z).mpr hb)⟩
    · intro h z
      rcases h z with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact iff_of_true ha hb
      · exact iff_of_false ha hb
  rw [hEq]
  apply MeasurableSet.iInter
  intro z
  have ha : MeasurableSet (A z) := measurableSet_sprinklingUnexploredCluster_mem R Q F a z
  have hb : MeasurableSet (B z) := measurableSet_sprinklingUnexploredCluster_mem R Q F b z
  exact (ha.inter hb).union (ha.compl.inter hb.compl)

/-- A fixed Case 3 pivot-pair event retains its probability on a positive
reveal atom. All four component tests are local to the available bonds. -/
theorem section9_case_three_revealed_probability {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (x y : Vertex d) (e f : Vertex d × Vertex d) :
    let A : Set (Configuration d) := {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
        sprinklingUnexploredCluster ω R Q₃ F₃ f.2}
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real A = (percolation d p).real A := by
  intro A
  let S := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  refine section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃
    hH₁ hH₃ hpos S (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁)
    A ?_ ?_
  · exact (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ {x} B e).inter
      ((measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ {y} B f).inter
      ((measurableSet_sprinklingUnexploredClusters_disjoint L L Q₁ F₁ Q₁ F₁ e.1 f.1).inter
        (measurableSet_section9_same_component R Q₃ F₃ e.2 f.2)))
  · intro ω θ h
    have hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = θ b :=
      fun b hb => h b (Finset.mem_union_left _ hb)
    have hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = θ b :=
      fun b hb => h b (Finset.mem_union_right _ hb)
    simp only [A, Set.mem_setOf_eq,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ {x} B ω θ hL hR e,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ {y} B ω θ hL hR f,
      sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hL,
      sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ hR]

/-- Independent sprinkle coordinates can be adjoined after conditioning
the critical configuration on the actual reveal atom. -/
theorem section9_case_three_revealed_opened_probability {d : ℕ} (p q : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (x y : Vertex d) (e f : Vertex d × Vertex d) (j k : Bond d) :
    let A : Set (Configuration d) := {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
        sprinklingUnexploredCluster ω R Q₃ F₃ f.2}
    let O : Set (Configuration d) := {η | η j = true ∧ η k = true}
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real (A ×ˢ O) =
      ((percolation d p).prod (percolation d q)).real (A ×ˢ O) := by
  intro A O
  have h := section9_case_three_revealed_probability p L R Q₁ H₁ F₁ Q₃ H₃ F₃ B
    hH₁ hH₃ hLQ₃ hRQ₁ hpos x y e f
  simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  exact congrArg (fun r : ℝ => r * (percolation d q).real O) h

/-- The entire opened pivot sum is unchanged by the reveal atom. -/
theorem section9_case_three_revealed_opened_sum {d : ℕ} (p q : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (x y : Vertex d) (P : Finset (Vertex d × Vertex d)) (bond : (Vertex d × Vertex d) → Bond d) :
    let I := (P.product P).filter (fun ef => ef.1 ≠ ef.2)
    let A := fun (e f : Vertex d × Vertex d) => {ω : Configuration d |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
        sprinklingUnexploredCluster ω R Q₃ F₃ f.2}
    let O := fun (e f : Vertex d × Vertex d) => {η : Configuration d |
      η (bond e) = true ∧ η (bond f) = true}
    (∑ ef ∈ I, ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
      (A ef.1 ef.2 ×ˢ O ef.1 ef.2)) =
    ∑ ef ∈ I, ((percolation d p).prod (percolation d q)).real (A ef.1 ef.2 ×ˢ O ef.1 ef.2) := by
  intro I A O
  apply Finset.sum_congr rfl
  intro ef _
  exact section9_case_three_revealed_opened_probability p q L R Q₁ H₁ F₁ Q₃ H₃ F₃ B
    hH₁ hH₃ hLQ₃ hRQ₁ hpos x y ef.1 ef.2 (bond ef.1) (bond ef.2)

/-- On the actual reveal atom, the Case 3 coalescence event is bounded by
the same opened-pivot sum as for independent critical bonds. -/
theorem section9_case_three_revealed_event_le_opened_sum {d : ℕ} (q : unitInterval)
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (H₁ H₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (x y : Vertex d) (bond : (Vertex d × Vertex d) → Bond d)
    (hbond : ∀ e ∈ P, s((bond e).1, bondTip (bond e)) = s(e.1, e.2)) :
    let I := (P.product P).filter (fun ef => ef.1 ≠ ef.2)
    let A := fun ef : (Vertex d × Vertex d) × (Vertex d × Vertex d) =>
      {ω : Configuration d |
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B ef.1 ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B ef.2 ∧
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ ef.1.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ ef.2.1) ∧
        sprinklingUnexploredCluster ω R Q₃ F₃ ef.1.2 =
          sprinklingUnexploredCluster ω R Q₃ F₃ ef.2.2}
    let E := fun ef => A ef ×ˢ {η | η (bond ef.1) = true ∧ η (bond ef.2) = true}
    let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
    μ.real {ξη : Configuration d × Configuration d |
      let ω := ξη.1
      let η := ξη.2
      (section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ {x} B ∩
        section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty ∧
      (∀ e ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {x} B,
      ∀ f ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {y} B,
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
          (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) ∧
        Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
          (sprinklingUnexploredCluster ω L Q₁ F₁ f.1))} ≤
      ∑ ef ∈ I, ((percolation d (criticalPoint d)).prod (percolation d q)).real (E ef) := by
  intro I A E μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  refine (measureReal_mono (s₂ := ⋃ ef ∈ I, E ef) ?_ (measure_ne_top _ _)).trans ?_
  · rintro ⟨ω, η⟩ ⟨h, hexclude⟩
    obtain ⟨ef, hef, he, hf, hLL, hshared, heOpen, hfOpen⟩ :=
      section9_case_three_opened_witness ω η P L R Q₁ F₁ Q₃ F₃ B x y bond hbond h hexclude
    exact Set.mem_iUnion.mpr ⟨ef, Set.mem_iUnion.mpr
      ⟨hef, ⟨⟨he, hf, hLL, hshared⟩, heOpen, hfOpen⟩⟩⟩
  · refine (measureReal_biUnion_finset_le I E).trans_eq ?_
    exact section9_case_three_revealed_opened_sum (criticalPoint d) q L R Q₁ H₁ F₁ Q₃ H₃ F₃ B
      hH₁ hH₃ hLQ₃ hRQ₁ hpos x y P bond

end NearCritical
