module
public import NearCritical.Section9PivotalCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Unique left-boundary labels cannot overcount the actual pivotal pairs. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

/-- Actual pivotal pairs whose left component meets W in exactly the label x. -/
def section9UniqueLeftPivotalPairs {d : ℕ} (ω : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ W B : Finset (Vertex d))
    (x : Vertex d) : Finset (Vertex d × Vertex d) :=
  (sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ {x} B).filter fun e =>
    sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∩ W = {x}

/-- Pointwise counting of actual unique-left pivotal pairs is bounded by the
actual pivotal count. No law or conditional expectation is assumed. -/
theorem section9_unique_left_pivotal_count_le {d : ℕ} (ω : Configuration d)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ W A B : Finset (Vertex d)) :
    (∑ x ∈ A, ((section9UniqueLeftPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ W B x).card : ℝ)) ≤
      section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω := by
  let P := fun x => section9UniqueLeftPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ W B x
  have hdis : Set.PairwiseDisjoint (A : Set (Vertex d)) P := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro e hex hey
    have hx := (Finset.mem_filter.mp hex).2
    have hy := (Finset.mem_filter.mp hey).2
    have hs : ({x} : Finset (Vertex d)) = {y} := hx.symm.trans hy
    exact hxy (by simpa only [Finset.singleton_inj] using hs)
  have hsub : A.biUnion P ⊆ sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A B := by
    intro e he
    obtain ⟨x,hxA,hex⟩ := Finset.mem_biUnion.mp he
    have hePivot := (Finset.mem_filter.mp hex).1
    obtain ⟨heE,hp⟩ := Finset.mem_filter.mp hePivot
    rcases hp with ⟨hadj,heL,heR,hleft,hright,hcomponents⟩
    obtain ⟨y,hy⟩ := hleft
    obtain ⟨hyC,hyx⟩ := Finset.mem_inter.mp hy
    have hyx' : y = x := Finset.mem_singleton.mp hyx
    subst y
    exact Finset.mem_filter.mpr ⟨heE,hadj,heL,heR,
      ⟨x,Finset.mem_inter.mpr ⟨hyC,hxA⟩⟩,hright,hcomponents⟩
  have hNat : (∑ x ∈ A, (P x).card) ≤
      (sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A B).card := by
    rw [← Finset.card_biUnion hdis]
    exact Finset.card_le_card hsub
  change (∑ x ∈ A, ((P x).card : ℝ)) ≤
    ((sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A B).card : ℝ)
  exact_mod_cast hNat

end NearCritical
