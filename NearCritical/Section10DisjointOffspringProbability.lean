module

public import NearCritical.Section10DisjointBridgeArms
public import NearCritical.Section9CoalescenceConditional
public import NearCritical.Section9CoalescenceOpenedSum
public import NearCritical.Section9MeanUpperScale

/-! The joint offspring estimate (H2) in a tube conditioned on its two hearts. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- Conditioning on the two heart-cluster reveals leaves the critical
disjoint-pivot event unchanged in probability. -/
theorem disjointPivotEvent_revealed_probability {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A₁ A₂ B₁ B₂ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (e f : Vertex d × Vertex d) :
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real
      (disjointPivotEvent L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ e f) =
    (percolation d p).real (disjointPivotEvent L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ e f) := by
  refine section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos _
    (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁) _ ?_ ?_
  · exact (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A₁ B₁ e).inter
      ((measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A₂ B₂ f).inter
      ((measurableSet_sprinklingUnexploredClusters_disjoint L L Q₁ F₁ Q₁ F₁ e.1 f.1).inter
      ((measurableSet_sprinklingUnexploredClusters_disjoint L R Q₁ F₁ Q₃ F₃ e.1 f.2).inter
      ((measurableSet_sprinklingUnexploredClusters_disjoint R L Q₃ F₃ Q₁ F₁ e.2 f.1).inter
        (measurableSet_sprinklingUnexploredClusters_disjoint R R Q₃ F₃ Q₃ F₃ e.2 f.2)))))
  · intro ω θ h
    have hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = θ b :=
      fun b hb => h b (Finset.mem_union_left _ hb)
    have hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = θ b :=
      fun b hb => h b (Finset.mem_union_right _ hb)
    simp only [disjointPivotEvent, Set.mem_setOf_eq,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A₁ B₁ ω θ hL hR e,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A₂ B₂ ω θ hL hR f,
      sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hL,
      sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ hR]

/-- Both selected targets are hit and the two full bridges are disjoint. -/
def disjointOffspringEvent {d : ℕ} (P : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ B : Finset (Vertex d)) :
    Set (Configuration d × Configuration d) :=
  {ξη | (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A₁ B₁).Nonempty ∧
    (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A₂ B₂).Nonempty ∧
    Disjoint (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A₁ B)
      (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A₂ B)}

/-- Repeated BK and independent sprinkling bound the actual joint hit by the
product of the two ordinary arm sums, including the two sprinkle factors. -/
theorem disjoint_offspring_probability_le {d : ℕ} (p q : unitInterval)
    (P : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A₁ A₂ B₁ B₂ B : Finset (Vertex d))
    (hB₁ : B₁ ⊆ B) (hB₂ : B₂ ⊆ B)
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (bond : (Vertex d × Vertex d) → Bond d)
    (hbond : ∀ e ∈ P, s((bond e).1, bondTip (bond e)) = s(e.1, e.2)) :
    let W (A T : Finset (Vertex d)) (e : Vertex d × Vertex d) :=
      (∑ x ∈ A, twoPoint d p e.1 x) * (∑ y ∈ T, twoPoint d p e.2 y)
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
      (disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ B) ≤
      ((∑ e ∈ P, W A₁ B₁ e) * (q : ℝ)) * ((∑ f ∈ P, W A₂ B₂ f) * (q : ℝ)) := by
  intro W
  let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let μ := ν.prod (percolation d q)
  let I := (P.product P).filter (fun ef => bond ef.1 ≠ bond ef.2)
  let F (ef : (Vertex d × Vertex d) × (Vertex d × Vertex d)) :=
    disjointPivotEvent L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ ef.1 ef.2 ×ˢ
      {η : Configuration d | η (bond ef.1) = true ∧ η (bond ef.2) = true}
  let G (ef : (Vertex d × Vertex d) × (Vertex d × Vertex d)) :=
    W A₁ B₁ ef.1 * W A₂ B₂ ef.2 * (q : ℝ)^2
  have hG ef : 0 ≤ G ef := by
    dsimp only [G, W]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (Finset.sum_nonneg fun _ _ => twoPoint_nonneg _ _ _)
        (Finset.sum_nonneg fun _ _ => twoPoint_nonneg _ _ _))
      (mul_nonneg (Finset.sum_nonneg fun _ _ => twoPoint_nonneg _ _ _)
        (Finset.sum_nonneg fun _ _ => twoPoint_nonneg _ _ _))) (sq_nonneg _)
  have hcover : disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ B ⊆ ⋃ ef ∈ I, F ef := by
    rintro ⟨ω, η⟩ ⟨⟨e, he⟩, ⟨f, hf⟩, hdis⟩
    obtain ⟨hsep, hLL, hLR, hRL, hRR⟩ := disjoint_bridges_pivots_separate ω η P L R Q₁ F₁ Q₃ F₃
      A₁ A₂ B₁ B₂ B hB₁ hB₂ e f he hf hdis
    obtain ⟨he₀, heopen⟩ := Finset.mem_filter.mp he
    obtain ⟨hf₀, hfopen⟩ := Finset.mem_filter.mp hf
    obtain ⟨heP, hepiv⟩ := Finset.mem_filter.mp he₀
    obtain ⟨hfP, hfpiv⟩ := Finset.mem_filter.mp hf₀
    have hne : bond e ≠ bond f := by
      intro heq
      apply hsep
      rw [← hbond e heP, ← hbond f hfP, heq]
    have hef : (e, f) ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heP, hfP⟩, hne⟩
    exact Set.mem_iUnion.mpr ⟨(e, f), Set.mem_iUnion.mpr ⟨hef,
      ⟨⟨hepiv, hfpiv, hLL, hLR, hRL, hRR⟩,
        section9_bond_open_of_adj (hbond e heP) heopen,
        section9_bond_open_of_adj (hbond f hfP) hfopen⟩⟩⟩
  change μ.real _ ≤ _
  calc
    _ ≤ μ.real (⋃ ef ∈ I, F ef) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ ef ∈ I, μ.real (F ef) := measureReal_biUnion_finset_le I F
    _ ≤ ∑ ef ∈ I, G ef := by
      apply Finset.sum_le_sum
      intro ef hef
      let C := disjointPivotEvent L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ ef.1 ef.2
      let O : Set (Configuration d) := {η | η (bond ef.1) = true ∧ η (bond ef.2) = true}
      have hne := (Finset.mem_filter.mp hef).2
      have heq : μ.real (F ef) = ((percolation d p).prod (percolation d q)).real (C ×ˢ O) := by
        have hc : ν.real C = (percolation d p).real C :=
          disjointPivotEvent_revealed_probability p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A₁ A₂ B₁ B₂
            hH₁ hH₃ hLQ₃ hRQ₁ hpos ef.1 ef.2
        change (ν.prod (percolation d q)).real (C ×ˢ O) = _
        simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
        exact congrArg (fun z : ℝ => z * (percolation d q).real O) hc
      have ho : ((percolation d p).prod (percolation d q)).real (C ×ˢ O) =
          (percolation d p).real C * (q : ℝ)^2 := by
        change (((percolation d p).prod (percolation d q)) (C ×ˢ O)).toReal = _
        rw [section9_critical_event_two_bond_opening p q C hne,
          ENNReal.toReal_mul, ENNReal.toReal_pow]
        rfl
      rw [heq, ho]
      exact mul_le_mul_of_nonneg_right
        (disjointPivotEvent_probability_le p L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ ef.1 ef.2)
        (sq_nonneg _)
    _ ≤ ∑ ef ∈ P.product P, G ef :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ef _ _ => hG ef)
    _ = (∑ ef ∈ P.product P, W A₁ B₁ ef.1 * W A₂ B₂ ef.2) * (q : ℝ)^2 := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [Finset.product_eq_sprod, Finset.sum_product, ← Finset.sum_mul_sum]
      ring

end NearCritical.Section10
