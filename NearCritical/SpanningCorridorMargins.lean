module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Tactic

/-! NEW lem.arm.2dspanning: explicit normalized coordinate margins for
transferring the limiting embedded corridor and target into the discrete
source corridor. No probabilistic or scaling-limit claim. -/
@[expose] public section
namespace NearCritical
open scoped Classical

def realSpanningHeight {d : ℕ} (f : Fin d × Bool) (z : Fin d → ℝ) : ℝ :=
  if f.2 then z f.1 else -z f.1

/-- An actual sup-metric embedding error controls every coordinate error. -/
lemma spanning_embedding_coordinate_error {d : ℕ} {z w : Fin d → ℝ} {ε : ℝ}
    (h : dist z w ≤ ε) (i : Fin d) : |z i-w i| ≤ ε := by
  have hi := dist_le_pi_dist z w i
  rw [Real.dist_eq] at hi
  exact hi.trans h

/-- Changing face sign does not enlarge the selected-coordinate error. -/
lemma realSpanningHeight_sub_abs {d : ℕ} (f : Fin d × Bool) (z w : Fin d → ℝ) :
    |realSpanningHeight f z-realSpanningHeight f w| = |z f.1-w f.1| := by
  rcases f with ⟨i,s⟩
  cases s with
  | false =>
    change |-z i - -w i| = |z i-w i|
    rw [show -z i - -w i = -(z i-w i) by ring, abs_neg]
  | true => rfl

/-- The narrow limiting corridor has enough slack for an embedding error
of 1/32 in EVERY coordinate, with both face orientations. -/
theorem spanning_corridor_margin {d : ℕ} (f : Fin d × Bool) (z w : Fin d → ℝ)
    (herror : dist z w ≤ (1/32:ℝ))
    (hheight : -(1/4:ℝ) ≤ realSpanningHeight f w ∧ realSpanningHeight f w ≤ 5/2)
    (htransverse : ∀ j, j ≠ f.1 → |w j| ≤ (1/32:ℝ)) :
    -(3/8:ℝ) ≤ realSpanningHeight f z ∧ realSpanningHeight f z ≤ 3 ∧
      ∀ j, j ≠ f.1 → |z j| ≤ (1/8:ℝ) := by
  have hs : |realSpanningHeight f z-realSpanningHeight f w| ≤ (1/32:ℝ) := by
    rw [realSpanningHeight_sub_abs]
    exact spanning_embedding_coordinate_error herror f.1
  have hb := abs_le.mp hs
  refine ⟨by linarith [hheight.1],by linarith [hheight.2],?_⟩
  intro j hj
  have he := spanning_embedding_coordinate_error herror j
  have ht := htransverse j hj
  have ha : |z j| ≤ |z j-w j|+|w j| := by
    simpa only [sub_add_cancel] using abs_add_le (z j-w j) (w j)
  linarith

/-- A limiting endpoint within 1/32 of signed 2e_i remains in the source
1/8 target box after another 1/32 embedding error. -/
theorem spanning_target_margin {d : ℕ} (f : Fin d × Bool) (z w : Fin d → ℝ)
    (herror : dist z w ≤ (1/32:ℝ))
    (hheight : |realSpanningHeight f w-2| ≤ (1/32:ℝ))
    (htransverse : ∀ j, j ≠ f.1 → |w j| ≤ (1/32:ℝ)) :
    (15/8:ℝ) ≤ realSpanningHeight f z ∧ realSpanningHeight f z ≤ 17/8 ∧
      ∀ j, j ≠ f.1 → |z j| ≤ (1/8:ℝ) := by
  have hs : |realSpanningHeight f z-realSpanningHeight f w| ≤ (1/32:ℝ) := by
    rw [realSpanningHeight_sub_abs]
    exact spanning_embedding_coordinate_error herror f.1
  have hb := abs_le.mp hs
  have hw := abs_le.mp hheight
  refine ⟨by linarith,by linarith,?_⟩
  intro j hj
  have he := spanning_embedding_coordinate_error herror j
  have ht := htransverse j hj
  have ha : |z j| ≤ |z j-w j|+|w j| := by
    simpa only [sub_add_cancel] using abs_add_le (z j-w j) (w j)
  linarith

end NearCritical
