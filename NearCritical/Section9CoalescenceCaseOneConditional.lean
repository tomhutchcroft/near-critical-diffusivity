module

public import NearCritical.Section9CoalescenceSingleOpening
public import NearCritical.Section9PhysicalBond
public import NearCritical.Section9CoalescenceOpenedSum

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The shared-left critical event and a single opening under the
actual reveal law. -/
theorem section9_case_one_revealed_opened_probability {d : ℕ} (q : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (x y : Vertex d) (e : Vertex d × Vertex d) (b : Bond d) :
    let A : Set (Configuration d) := {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      (sprinklingUnexploredCluster ω L Q₁ F₁ x ∩
        sprinklingUnexploredCluster ω L Q₁ F₁ y).Nonempty}
    ((section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
      (A ×ˢ {η | η b = true}) = (percolation d (criticalPoint d)).real A * (q : ℝ) := by
  intro A
  let S := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  refine section9_revealed_single_opening q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos S
    (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁) A ?_ ?_ b
  · exact (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ {x} B e).inter
      (by
        let U (ω : Configuration d) := sprinklingUnexploredCluster ω L Q₁ F₁ x
        let V (ω : Configuration d) := sprinklingUnexploredCluster ω L Q₁ F₁ y
        change MeasurableSet (fun ω : Configuration d => (U ω ∩ V ω).Nonempty)
        have he : (fun ω : Configuration d => (U ω ∩ V ω).Nonempty) =
            {ω | Disjoint (U ω) (V ω)}ᶜ := by
          funext ω
          exact propext Finset.not_disjoint_iff_nonempty_inter.symm
        rw [he]
        exact (measurableSet_sprinklingUnexploredClusters_disjoint L L Q₁ F₁ Q₁ F₁ x y).compl)
  · intro ω θ h
    have hL : ∀ j ∈ sprinklingAvailableBonds L Q₁ F₁, ω j = θ j :=
      fun j hj => h j (Finset.mem_union_left _ hj)
    have hR : ∀ j ∈ sprinklingAvailableBonds R Q₃ F₃, ω j = θ j :=
      fun j hj => h j (Finset.mem_union_right _ hj)
    simp only [A, Set.mem_setOf_eq,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ {x} B ω θ hL hR,
      sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hL]

/-- The Case 1 event is covered by the opened single-pivot union. -/
theorem section9_case_one_event_le_union {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (x y : Vertex d) (bond : (Vertex d × Vertex d) → Bond d)
    (hbond : ∀ e ∈ P, s((bond e).1, bondTip (bond e)) = s(e.1, e.2)) :
    let A := fun e : Vertex d × Vertex d => {ω : Configuration d |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      (sprinklingUnexploredCluster ω L Q₁ F₁ x ∩
        sprinklingUnexploredCluster ω L Q₁ F₁ y).Nonempty}
    let E := fun e => A e ×ˢ {η | η (bond e) = true}
    μ.real {ξη : Configuration d × Configuration d |
      (sprinklingUnexploredCluster ξη.1 L Q₁ F₁ x ∩
        sprinklingUnexploredCluster ξη.1 L Q₁ F₁ y).Nonempty ∧
      (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {x} B).Nonempty} ≤
      ∑ e ∈ P, μ.real (E e) := by
  intro A E
  refine (measureReal_mono (s₂ := ⋃ e ∈ P, E e) ?_ (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le P E)
  rintro ⟨ω, η⟩ ⟨hxy, e, he⟩
  obtain ⟨he0, heOpen⟩ := Finset.mem_filter.mp he
  obtain ⟨heP, hePivot⟩ := Finset.mem_filter.mp he0
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heP,
    ⟨⟨hePivot, hxy⟩, section9_bond_open_of_adj (hbond e heP) heOpen⟩⟩⟩

/-- Case 1 on a positive reveal atom, with the root-pair kernel
retained for the final regularity estimate. -/
theorem section9_case_one_revealed_event_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C G : ℝ, 0 < C ∧ 0 < G ∧
      ∀ (i : Fin d) (n : ℕ), 0 < n → ∀ (q : unitInterval),
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        ∀ x y : Vertex d,
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        let H := (B.card : ℝ) * (C * ((n:ℝ)/8) ^ ((2:ℝ)-(d:ℝ)))
        let M := (2 * (d : ℝ)) * (G * (1 + (2 * (d : ℝ) * 3^(d-1)) * ((6*n : ℕ)+1 : ℝ)^2))
        let K := G^2 * (((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))) *
          (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ)))
        μ.real {ξη : Configuration d × Configuration d |
          (sprinklingUnexploredCluster ξη.1 L Q₁ F₁ x ∩
            sprinklingUnexploredCluster ξη.1 L Q₁ F₁ y).Nonempty ∧
          (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {x} B).Nonempty} ≤ H * (M * K) * (q : ℝ) := by
  obtain ⟨C, G, hC, hG, h⟩ := section9_case_one_critical_sum_le hd asymptotics
  refine ⟨C, G, hC, hG, ?_⟩
  intro i n hn q L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hL hB x y P μ H M K
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  obtain ⟨bond, hbond⟩ := section9_middle_candidate_bond_map i n
  refine (section9_case_one_event_le_union μ P L R Q₁ F₁ Q₃ F₃ B x y bond hbond).trans ?_
  rw [Finset.sum_congr rfl (fun e _ =>
    section9_case_one_revealed_opened_probability q L R Q₁ H₁ F₁ Q₃ H₃ F₃ B
      hH₁ hH₃ hLQ₃ hRQ₁ hpos x y e (bond e)), ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (h i n hn L R Q₁ F₁ Q₃ F₃ B x y hL hB) q.property.1

end NearCritical
