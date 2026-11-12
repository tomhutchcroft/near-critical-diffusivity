module

public import NearCritical.Section9CoalescenceCaseTwoOpened
public import NearCritical.Section9PhysicalBond
public import NearCritical.Section9CoalescenceOpenedSum

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The critical event in the Case 2 sum is measurable and local to the
two available bond blocks, including its existential second pivot. -/
theorem section9_case_two_revealed_opened_probability {d : ℕ} (q : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (x y : Vertex d) (e : Vertex d × Vertex d) (b : Bond d) :
    let A : Set (Configuration d) := {ω | ∃ f : Vertex d × Vertex d,
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
        sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty}
    ((section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
      (A ×ˢ {η | η b = true}) = (percolation d (criticalPoint d)).real A * (q : ℝ) := by
  intro A
  let S := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  refine section9_revealed_single_opening q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos S
    (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁) A ?_ ?_ b
  · unfold A
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro f
    exact (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ {x} B e).inter
      ((measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ {y} B f).inter
      ((measurableSet_sprinklingUnexploredClusters_disjoint L L Q₁ F₁ Q₁ F₁ e.1 f.1).inter
        (by
        let U (ω : Configuration d) := sprinklingUnexploredCluster ω R Q₃ F₃ e.2
        let V (ω : Configuration d) := sprinklingUnexploredCluster ω L Q₁ F₁ f.1
        change MeasurableSet (fun ω : Configuration d => (U ω ∩ V ω).Nonempty)
        have he : (fun ω : Configuration d => (U ω ∩ V ω).Nonempty) =
            {ω | Disjoint (U ω) (V ω)}ᶜ := by
          funext ω
          exact propext Finset.not_disjoint_iff_nonempty_inter.symm
        rw [he]
        exact (measurableSet_sprinklingUnexploredClusters_disjoint R L Q₃ F₃ Q₁ F₁ e.2 f.1).compl)))
  · intro ω θ h
    have hL : ∀ j ∈ sprinklingAvailableBonds L Q₁ F₁, ω j = θ j :=
      fun j hj => h j (Finset.mem_union_left _ hj)
    have hR : ∀ j ∈ sprinklingAvailableBonds R Q₃ F₃, ω j = θ j :=
      fun j hj => h j (Finset.mem_union_right _ hj)
    simp only [A, Set.mem_setOf_eq,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ {x} B ω θ hL hR,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ {y} B ω θ hL hR,
      sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hL,
      sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ hR]

/-- The actual opened Case 2 cross event is covered by the single-pivot
union, under the conditional law or any other finite law. -/
theorem section9_case_two_event_le_union {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (x y : Vertex d) (bond : (Vertex d × Vertex d) → Bond d)
    (hbond : ∀ e ∈ P, s((bond e).1, bondTip (bond e)) = s(e.1, e.2)) :
    let A := fun e : Vertex d × Vertex d => {ω : Configuration d | ∃ f : Vertex d × Vertex d,
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
      (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
        sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty}
    let E := fun e => A e ×ˢ {η | η (bond e) = true}
    μ.real {ξη : Configuration d × Configuration d |
      let ω := ξη.1
      let η := ξη.2
      ∃ e ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {x} B,
      ∃ f ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {y} B,
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
        (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
          sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty} ≤
      ∑ e ∈ P, μ.real (E e) := by
  intro A E
  refine (measureReal_mono (s₂ := ⋃ e ∈ P, E e) ?_ (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le P E)
  rintro ⟨ω, η⟩ ⟨e, he, f, hf, hLL, hcross⟩
  obtain ⟨he0, heOpen⟩ := Finset.mem_filter.mp he
  obtain ⟨heP, hePivot⟩ := Finset.mem_filter.mp he0
  have hfPivot := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heP,
    ⟨⟨f, hePivot, hfPivot, hLL, hcross⟩, section9_bond_open_of_adj (hbond e heP) heOpen⟩⟩⟩

/-- The conditional probability of the actual cross event has the
Case 2 power after one fresh opening. -/
theorem section9_case_two_revealed_event_scaled {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ) ^ (-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        ∀ x y : Vertex d, x ∈ section9FiniteEndCube i n 0 → y ∈ section9FiniteEndCube i n 0 →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        μ.real {ξη : Configuration d × Configuration d |
          let ω := ξη.1
          let η := ξη.2
          ∃ e ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {x} B,
          ∃ f ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {y} B,
            Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
              (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
            (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
              sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty} ≤
          (B.card : ℝ) * K * (n : ℝ) ^ (6 - 2 * (d : ℝ)) := by
  obtain ⟨K, hK⟩ := section9_case_two_opened_sum_scaled hd asymptotics q₀
  refine ⟨K, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hB x y hx hy P μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  obtain ⟨bond, hbond⟩ := section9_middle_candidate_bond_map i n
  refine (section9_case_two_event_le_union μ P L R Q₁ F₁ Q₃ F₃ B x y bond hbond).trans ?_
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun e _ => ?_)))
    (hK i n hn L R Q₁ F₁ Q₃ F₃ B x y hx hy hB q hq bond)
  exact (section9_case_two_revealed_opened_probability q L R Q₁ H₁ F₁ Q₃ H₃ F₃ B
    hH₁ hH₃ hLQ₃ hRQ₁ hpos x y e (bond e)).trans
    (section9_case_one_opened_probability q _ (bond e)).symm

end NearCritical
