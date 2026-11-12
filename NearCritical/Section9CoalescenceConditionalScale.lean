module

public import NearCritical.Section9CoalescenceConditional

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The Case 3 event on a positive reveal atom has the source per-root
decay, with the other coalescence cases excluded. -/
theorem section9_case_three_revealed_event_scaled {d : ℕ} (hd : 2 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ) ^ (-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        R ⊆ centeredBox d (3*n) → B ⊆ centeredBox d (3*n) →
        ∀ x y : Vertex d, x ∈ section9FiniteEndCube i n 0 → y ∈ section9FiniteEndCube i n 0 →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
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
          (B.card : ℝ) * K * (n : ℝ) ^ (-(2 : ℝ) * (d : ℝ) + 6) := by
  obtain ⟨K, hK⟩ := section9_case_three_opened_sum_scaled hd asymptotics q₀
  refine ⟨K, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hR hB x y hx hy P μ
  obtain ⟨bond, hbond⟩ := section9_middle_candidate_bond_map i n
  exact (section9_case_three_revealed_event_le_opened_sum q P L R Q₁ F₁ Q₃ F₃ B
    H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos x y bond hbond).trans
    (hK i n hn q hq L R Q₁ F₁ Q₃ F₃ B x y hR hB hx hy bond hbond)

end NearCritical
