module

public import NearCritical.NestChainPath
public import NearCritical.LatticeDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Finite realizations of the existing open-coordinate sprinkling shapes.
The containing box is only an enumeration device, not a truncation premise. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

def section9FiniteEndCube {d : ℕ} (i : Fin d) (n : ℕ) (center : ℝ) : Finset (Vertex d) :=
  (centeredBox d (3*n)).filter fun x => x ∈ sprinklingEndCube i n center

def section9FiniteTube {d : ℕ} (i : Fin d) (n : ℕ) (lo hi : ℝ) : Finset (Vertex d) :=
  (centeredBox d (3*n)).filter fun x => x ∈ sprinklingTube i n lo hi

/-- The enumeration box removes no vertex of the end-cube shape. -/
theorem mem_section9FiniteEndCube {d : ℕ} (i : Fin d) (n : ℕ) (center : ℝ)
    (hc : -2*(n:ℝ) ≤ center ∧ center ≤ 2*(n:ℝ)) (x : Vertex d) :
    x ∈ section9FiniteEndCube i n center ↔ x ∈ sprinklingEndCube i n center := by
  simp only [section9FiniteEndCube, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hx
    refine ⟨mem_centeredBox.mpr ?_, hx⟩
    intro j
    have hj := hx j
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hb : -3*(n:ℝ) ≤ (x j : ℝ) ∧ (x j : ℝ) ≤ 3*(n:ℝ) := by
      by_cases hji : j = i
      · subst j
        simp only [ite_true] at hj
        constructor <;> linarith [hc.1, hc.2]
      · simp only [hji, ite_false, sub_zero] at hj
        constructor <;> linarith
    constructor
    · exact_mod_cast hb.1
    · exact_mod_cast hb.2

/-- The enumeration box removes no vertex of any of the source tubes. -/
theorem mem_section9FiniteTube {d : ℕ} (i : Fin d) (n : ℕ) (lo hi : ℝ)
    (hlo : -1 ≤ lo) (hhi : hi ≤ 1) (x : Vertex d) :
    x ∈ section9FiniteTube i n lo hi ↔ x ∈ sprinklingTube i n lo hi := by
  simp only [section9FiniteTube, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hx
    refine ⟨mem_centeredBox.mpr ?_, hx⟩
    intro j
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hb : -3*(n:ℝ) ≤ (x j : ℝ) ∧ (x j : ℝ) ≤ 3*(n:ℝ) := by
      by_cases hji : j = i
      · subst j
        have hln := mul_le_mul_of_nonneg_right hlo hn
        have hhn := mul_le_mul_of_nonneg_right hhi hn
        constructor <;> nlinarith [hx.1, hx.2.1, hln, hhn]
      · obtain ⟨hl, hu⟩ := hx.2.2 j hji
        constructor <;> linarith
    constructor
    · exact_mod_cast hb.1
    · exact_mod_cast hb.2

/-- Finite T12 avoids the opposite end cube exactly as its set-valued shape. -/
theorem section9FiniteLeftTube_disjoint_third {d : ℕ} (i : Fin d) {n : ℕ} (hn : 0 < n) :
    Disjoint (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
      (section9FiniteEndCube i n (2*(n:ℝ))) := by
  apply Finset.disjoint_left.mpr
  intro x hx hq
  have hx' := (Finset.mem_filter.mp hx).2
  have hq' := (Finset.mem_filter.mp hq).2
  exact Set.disjoint_left.mp (sprinklingLeftTube_disjoint_third i (by exact_mod_cast hn)) hx' hq'

/-- Finite T23 avoids the first end cube, with no finite-mask disjointness premise. -/
theorem section9FiniteRightTube_disjoint_first {d : ℕ} (i : Fin d) {n : ℕ} (hn : 0 < n) :
    Disjoint (section9FiniteTube i n (-(3:ℝ)/8) (5/8)) (section9FiniteEndCube i n 0) := by
  apply Finset.disjoint_left.mpr
  intro x hx hq
  have hx' := (Finset.mem_filter.mp hx).2
  have hq' := (Finset.mem_filter.mp hq).2
  exact Set.disjoint_left.mp (sprinklingRightTube_disjoint_first i (by exact_mod_cast hn)) hx' hq'

end NearCritical
