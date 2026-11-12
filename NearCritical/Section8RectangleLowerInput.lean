module
public import NearCritical.HalfSpaceTranslation
public import NearCritical.ThreePointDiagram

/-! The fixed-shape restricted rectangle theorem cited in source6209.
CH20 preprint Theorem12 / published Theorem4.2 is a literature input here,
not a proved theorem of this library. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Closed lattice rectangle with fixed positive aspect ratios. -/
def section8Rectangle {d : ℕ} (α β : Fin d → ℝ) (n : ℕ) : Set (Vertex d) :=
  {u | ∀ j, -α j*(n : ℝ) ≤ (u j : ℝ) ∧ (u j : ℝ) ≤ β j*(n : ℝ)}

/-- Cited fixed-shape rectangle lower input, including the clipped zero-distance
convention. It contains no unique-extension or source-tube lower bound. -/
def RestrictedRectangleLowerInput (d : ℕ) : Prop :=
  ∀ (α β : Fin d → ℝ), (∀ j, 0 < α j) → (∀ j, 0 < β j) →
    ∀ M : ℝ, 1 < M → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ u ∈ section8Rectangle α β n,
        c*(max 1 (latticeDistance 0 u))^((2 : ℝ)-(d : ℝ)) ≤
          (percolation d (criticalPoint d)).real
            (connectionToSetEvent (section8Rectangle (fun j => M*α j) (fun j => M*β j) n) 0 {u})

/-- Exact product-law translation makes the fixed-shape lower constant
uniform over all origins, without assuming stationarity of a restricted law. -/
theorem section8_translated_rectangle_lower {d : ℕ}
    (lower : RestrictedRectangleLowerInput d) (α β : Fin d → ℝ)
    (hα : ∀ j, 0 < α j) (hβ : ∀ j, 0 < β j) (M : ℝ) (hM : 1 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ a z : Vertex d,
      z-a ∈ section8Rectangle α β n →
      c*(max 1 (latticeDistance 0 (z-a)))^((2 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((fun u : Vertex d => a+u) ''
            section8Rectangle (fun j => M*α j) (fun j => M*β j) n) a {z}) := by
  obtain ⟨c,hc,hbound⟩ := lower α β hα hβ M hM
  refine ⟨c,hc,?_⟩
  intro n hn a z hzin
  have hcancel : a+(z-a) = z := by rw [add_comm,sub_add_cancel]
  have htarget : (fun u : Vertex d => a+u) '' ({z-a} : Set (Vertex d)) = {z} := by
    rw [Set.image_singleton,hcancel]
  have heq := congrArg ENNReal.toReal (connectionToSet_probability_translation
    (criticalPoint d) a 0
    (section8Rectangle (fun j => M*α j) (fun j => M*β j) n) {z-a})
  have heq' : (percolation d (criticalPoint d)).real
      (connectionToSetEvent ((fun u : Vertex d => a+u) ''
        section8Rectangle (fun j => M*α j) (fun j => M*β j) n) a {z}) =
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (section8Rectangle (fun j => M*α j) (fun j => M*β j) n) 0 {z-a}) := by
    simpa only [measureReal_def,add_zero,htarget] using heq
  rw [heq']
  exact hbound n hn (z-a) hzin

end NearCritical
