module

public import NearCritical.Section10ActualBridgeEvents
public import NearCritical.Section10DisjointOffspringScale

/-! The spread estimate for two next nests produced through one shared tube
with disjoint bridges. The two prescribed children may be different. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- A shared-tube joint occupation with disjoint full bridges is covered
by the H2 events of all possible representatives. -/
theorem svNext_disjoint_pair_occupation_le {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hML : M ⊆ L) (hMQ : Disjoint (M : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    (J J' T : Finset (Finset (Vertex d))) (X Y Z : Finset (Vertex d) → Finset (Vertex d))
    (k : ℕ) (P : Finset (Finset (Finset (Vertex d)))) (c c' : Finset (Vertex d))
    {K : ℝ}
    (hK : ∀ a ∈ J, ∀ b ∈ J', μ.real
      (disjointOffspringEvent (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃
        (X a) (Y b) (Z c) (Z c') (sprinklingTargetBoundary T Z)) ≤ K) :
    let B := sprinklingTargetBoundary T Z
    μ.real {z | (∃ N ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ z) J T X Z k P, c ∈ N.val) ∧
      (∃ N' ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ z) J' T Y Z k P, c' ∈ N'.val) ∧
      Disjoint (section9SprinklingCluster z.1 (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs M)
        L R Q₁ F₁ Q₃ F₃ (sprinklingTargetBoundary J X) B)
        (section9SprinklingCluster z.1 (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs M)
          L R Q₁ F₁ Q₃ F₃ (sprinklingTargetBoundary J' Y) B)} ≤
      (J.card:ℝ) * (J'.card:ℝ) * K := by
  intro B
  let F (ab : Finset (Vertex d) × Finset (Vertex d)) :=
    disjointOffspringEvent (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ (X ab.1) (Y ab.2) (Z c) (Z c') B
  refine (measureReal_mono (s₂ := ⋃ ab ∈ J.product J', F ab) ?_ (measure_ne_top _ _)).trans ?_
  · rintro ⟨ω, η⟩ ⟨⟨N, hN, hc⟩, ⟨N', hN', hc'⟩, hdis⟩
    obtain ⟨_, a, ha, hh⟩ := svNext_member_has_opened_target ω η M L R Q₁ F₁ Q₃ F₃ hML hMQ
      J T X Z hN hc
    obtain ⟨_, b, hb, hh'⟩ := svNext_member_has_opened_target ω η M L R Q₁ F₁ Q₃ F₃ hML hMQ
      J' T Y Z hN' hc'
    change Disjoint (section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
      L R Q₁ F₁ Q₃ F₃ (J.biUnion X) B)
      (section9SprinklingCluster ω (sprinkleOrConfiguration ω η) (orientedLatticePairs M)
        L R Q₁ F₁ Q₃ F₃ (J'.biUnion Y) B) at hdis
    rw [middle_sprinklingCluster_or_eq ω η M L R Q₁ F₁ Q₃ F₃ _ _ hML hMQ,
      middle_sprinklingCluster_or_eq ω η M L R Q₁ F₁ Q₃ F₃ _ _ hML hMQ,
      bridge_of_nest_eq_biUnion, bridge_of_nest_eq_biUnion] at hdis
    exact Set.mem_iUnion.mpr ⟨(a,b), Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
      hh, hh', hdis.mono (fun _ hz => Finset.mem_biUnion.mpr ⟨a, ha, hz⟩)
        (fun _ hz => Finset.mem_biUnion.mpr ⟨b, hb, hz⟩)⟩⟩
  · calc
      _ ≤ ∑ ab ∈ J.product J', μ.real (F ab) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ab ∈ J.product J', K := by
        apply Finset.sum_le_sum
        intro ab hab
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
        exact hK ab.1 ha ab.2 hb
      _ = _ := by simp [Finset.card_product, Nat.cast_mul, nsmul_eq_mul]

end NearCritical.Section10
