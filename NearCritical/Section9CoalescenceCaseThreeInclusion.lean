module

public import NearCritical.Section9CoalescenceOpenedSum
public import NearCritical.Section9PhysicalBond

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Once the other coalescence cases are excluded, the actual coalescence
event supplies a distinct candidate pair in the product-law sum. -/
theorem section9_case_three_opened_witness {d : ℕ} (ω η : Configuration d)
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (x y : Vertex d) (bond : (Vertex d × Vertex d) → Bond d)
    (hbond : ∀ e ∈ P, s((bond e).1, bondTip (bond e)) = s(e.1, e.2))
    (h : (section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ {x} B ∩
      section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty)
    (hexclude : ∀ e ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {x} B,
      ∀ f ∈ sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {y} B,
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
          (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
        Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
          (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) ∧
        Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
          (sprinklingUnexploredCluster ω L Q₁ F₁ f.1)) :
    ∃ ef ∈ (P.product P).filter (fun ef => ef.1 ≠ ef.2),
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B ef.1 ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B ef.2 ∧
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ ef.1.1)
        (sprinklingUnexploredCluster ω L Q₁ F₁ ef.2.1) ∧
      sprinklingUnexploredCluster ω R Q₃ F₃ ef.1.2 =
        sprinklingUnexploredCluster ω R Q₃ F₃ ef.2.2 ∧
      η (bond ef.1) = true ∧ η (bond ef.2) = true := by
  obtain ⟨e, he, f, hf, hshared⟩ :=
    section9_coalescence_shared_right ω η P L R Q₁ F₁ Q₃ F₃ B x y h hexclude
  have hLL := (hexclude e he f hf).1
  obtain ⟨he0, heOpen⟩ := Finset.mem_filter.mp he
  obtain ⟨hf0, hfOpen⟩ := Finset.mem_filter.mp hf
  obtain ⟨heP, hePivot⟩ := Finset.mem_filter.mp he0
  obtain ⟨hfP, hfPivot⟩ := Finset.mem_filter.mp hf0
  have hne : e ≠ f := by
    intro hEq
    exact section9_case_three_physical_ne ω L R Q₁ F₁ Q₃ F₃ B x y e f
      hePivot hfPivot hLL hshared (by rw [hEq])
  exact ⟨(e, f), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heP, hfP⟩, hne⟩,
    hePivot, hfPivot, hLL, hshared, section9_bond_open_of_adj (hbond e heP) heOpen,
    section9_bond_open_of_adj (hbond f hfP) hfOpen⟩

/-- The event with the other cases excluded is bounded by the finite
sum of opened pivot-pair probabilities. -/
theorem section9_case_three_probability_le_opened_sum {d : ℕ} (q : unitInterval)
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
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
    let μ := (percolation d (criticalPoint d)).prod (percolation d q)
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
      ∑ ef ∈ I, μ.real (E ef) := by
  intro I A E μ
  refine (measureReal_mono (s₂ := ⋃ ef ∈ I, E ef) ?_ (measure_ne_top _ _)).trans ?_
  · rintro ⟨ω, η⟩ ⟨h, hexclude⟩
    obtain ⟨ef, hef, he, hf, hLL, hshared, heOpen, hfOpen⟩ :=
      section9_case_three_opened_witness ω η P L R Q₁ F₁ Q₃ F₃ B x y bond hbond h hexclude
    exact Set.mem_iUnion.mpr ⟨ef, Set.mem_iUnion.mpr
      ⟨hef, ⟨⟨he, hf, hLL, hshared⟩, heOpen, hfOpen⟩⟩⟩
  · exact measureReal_biUnion_finset_le I E

end NearCritical
