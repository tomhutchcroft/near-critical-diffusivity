module

public import NearCritical.Section9DistinctTargets

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

/-- Covering the terminal boundary by target boundaries covers every actual
pivotal pair by the pivotal pairs of at least one target. -/
theorem section9_pivotal_pairs_subset_target_union {d : ℕ} {ι : Type*}
    (I : Finset ι) (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (target : ι → Finset (Vertex d)) (hcover : B ⊆ I.biUnion target)
    (ω : Configuration d) :
    sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A B ⊆
      I.biUnion (fun i => sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (target i)) := by
  intro e he
  obtain ⟨heE, hadj, heL, heR, hleft, hright, hdisj⟩ := Finset.mem_filter.mp he
  obtain ⟨z, hz⟩ := hright
  obtain ⟨hzR, hzB⟩ := Finset.mem_inter.mp hz
  obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp (hcover hzB)
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, Finset.mem_filter.mpr ⟨heE, ?_⟩⟩
  exact ⟨hadj, heL, heR, hleft, ⟨z, Finset.mem_inter.mpr ⟨hzR, hzi⟩⟩, hdisj⟩

/-- The source first moment M1 dominates the total pivotal count whenever
the target boundaries cover B. No disjointness is needed for this inequality. -/
theorem section9_pivotal_count_le_target_sum {d : ℕ} {ι : Type*}
    (I : Finset ι) (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (target : ι → Finset (Vertex d)) (hcover : B ⊆ I.biUnion target)
    (ω : Configuration d) :
    section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤
      ∑ i ∈ I, section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (target i) ω := by
  have h := (Finset.card_le_card
    (section9_pivotal_pairs_subset_target_union I E L R Q₁ F₁ Q₃ F₃ A B target hcover ω)).trans
      (Finset.card_biUnion_le)
  unfold section9PivotalCount
  exact_mod_cast h

end NearCritical
