module

public import NearCritical.Section9CoalescenceCaseOneSum
public import NearCritical.Section9FreshEvent

@[expose] public section
namespace NearCritical
open MeasureTheory

/-- One independent sprinkle bit per candidate contributes one common
factor to a finite sum of critical event probabilities. -/
theorem section9_single_opening_sum {d : ℕ} {ι : Type*} (q : unitInterval)
    (P : Finset ι) (A : ι → Set (Configuration d)) (bond : ι → Bond d) :
    (∑ e ∈ P, ((percolation d (criticalPoint d)).prod (percolation d q)).real
      (A e ×ˢ {η | η (bond e) = true})) =
      (∑ e ∈ P, (percolation d (criticalPoint d)).real (A e)) * (q : ℝ) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun e _ => section9_case_one_opened_probability q (A e) (bond e)

/-- A single opening at rate O(n⁻²) cancels the quadratic pivot mass. -/
theorem section9_single_opening_mass_le {n H H₀ q q₀ : ℝ}
    (hn : 0 < n) (hH : 0 ≤ H) (hq : 0 ≤ q)
    (hMass : H ≤ H₀ * n ^ (2 : ℝ)) (hOpen : q ≤ q₀ * n ^ (-2 : ℝ)) :
    H * q ≤ H₀ * q₀ := by
  calc
    _ ≤ (H₀ * n ^ (2 : ℝ)) * (q₀ * n ^ (-2 : ℝ)) :=
      mul_le_mul hMass hOpen hq (hH.trans hMass)
    _ = (H₀ * q₀) * (n ^ (2 : ℝ) * n ^ (-2 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; norm_num

/-- A finite fresh critical event with one independent opening has
the original critical probability times the sprinkle rate. -/
theorem section9_revealed_single_opening {d : ℕ} (q : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (T : Finset (Bond d))
    (hd : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) T)
    (A : Set (Configuration d)) (hA : MeasurableSet A)
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ T, ω b = θ b) → (ω ∈ A ↔ θ ∈ A))
    (b : Bond d) :
    ((section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real
      (A ×ˢ {η | η b = true}) = (percolation d (criticalPoint d)).real A * (q : ℝ) := by
  have h := section9RevealedLaw_fresh_probability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    hH₁ hH₃ hpos T hd A hA hlocal
  calc
    _ = (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).real A * (q : ℝ) := by
      simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul,
        percolation_open_bond, ENNReal.toReal_ofReal q.property.1]
    _ = _ := congrArg (fun a : ℝ => a * (q : ℝ)) h

end NearCritical
