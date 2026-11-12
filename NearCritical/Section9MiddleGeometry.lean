module

public import NearCritical.Section9FiniteGeometry
public import NearCritical.SprinklingPivots
import Mathlib.Tactic.Linarith

/-! The finite middle region and the actual joining-edge closedness geometry. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

def section9FiniteMiddle {d : ℕ} (i : Fin d) (n : ℕ) : Finset (Vertex d) :=
  section9FiniteTube i n (-(3:ℝ)/8) (3/8)

/-- Literal source S2 is exactly the overlap of its two tubes. -/
theorem section9FiniteMiddle_eq_inter {d : ℕ} (i : Fin d) (n : ℕ) :
    section9FiniteMiddle i n =
      section9FiniteTube i n (-(5:ℝ)/8) (3/8) ∩
        section9FiniteTube i n (-(3:ℝ)/8) (5/8) := by
  ext x
  simp only [section9FiniteMiddle, section9FiniteTube, Finset.mem_filter, Finset.mem_inter]
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · rintro ⟨hx, hl, hu, ht⟩
    exact ⟨⟨hx, by change (n:ℝ) + (-(5:ℝ)/8)*(n:ℝ) < (x i : ℝ); linarith,
      hu, ht⟩, ⟨hx, hl, by change (x i : ℝ) < (n:ℝ) + (5/8)*(n:ℝ); linarith, ht⟩⟩
  · rintro ⟨⟨hx, _, hu, ht⟩, ⟨_, hl, _, _⟩⟩
    exact ⟨hx, hl, hu, ht⟩

/-- The middle region is strictly beyond the first end cube. -/
theorem section9FiniteMiddle_disjoint_first {d : ℕ} (i : Fin d) {n : ℕ} (hn : 0 < n) :
    Disjoint (section9FiniteMiddle i n) (section9FiniteEndCube i n 0) := by
  apply Finset.disjoint_left.mpr
  intro x hx hq
  have hm := (Finset.mem_filter.mp hx).2
  have hc := (Finset.mem_filter.mp hq).2
  have hl := hm.1
  have hu := (hc i).2
  simp only [ite_true, sub_zero] at hu
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  linarith

/-- Actual finite source geometry supplies the closed joining edge of every
canonical critical pivot; closedness is a conclusion, never an input. -/
theorem section9FiniteMiddle_pivotal_closed {d : ℕ} {ω : Configuration d}
    (i : Fin d) {n : ℕ} (hn : 0 < n) (F₁ F₃ A B : Finset (Vertex d))
    {e : Vertex d × Vertex d}
    (he : e ∈ sprinklingPivotalPairs ω (orientedLatticePairs (section9FiniteMiddle i n))
      (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
      (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
      (section9FiniteEndCube i n 0) F₁ (section9FiniteEndCube i n (2*(n:ℝ))) F₃ A B) :
    ¬ (openGraph ω).Adj e.1 e.2 := by
  have hSL : section9FiniteMiddle i n ⊆ section9FiniteTube i n (-(5:ℝ)/8) (3/8) := by
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_left
  have hdis : Disjoint (section9FiniteMiddle i n : Set (Vertex d))
      (section9FiniteEndCube i n 0 : Set (Vertex d)) := by
    apply Set.disjoint_left.mpr
    intro x hx hq
    exact Finset.disjoint_left.mp (section9FiniteMiddle_disjoint_first i hn) hx hq
  exact middle_sprinklingPivotalPairs_closed _ _ _ _ _ _ _ _ _ hSL hdis he

end NearCritical
