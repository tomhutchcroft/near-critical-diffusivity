module
public import NearCritical.Section8ExtensionSourceGeometry
public import NearCritical.Section8OutwardSurgery
public import NearCritical.CriticalPointInterior

/-! Literal source geometry discharges the unique-extension surgery guards.
This is Step 1 of Proposition extension, not the shifted connection lower bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Actual source Step1 for ordinary percolation, with all segment geometry
discharged from the source face/core definitions. -/
theorem section8_extension_source_surgery_probability {d : ℕ} (p : unitInterval)
    (i : Fin d) (n r : ℕ) (hn : 16*(r+1) ≤ n)
    (F W : Finset (Vertex d)) {x z : Vertex d}
    (hx : x ∈ section8ExtensionPositiveFaceCore i n)
    (hz : z ∈ section8ExtensionMiddleCore i n)
    (hW : W ⊆ section9FiniteEndCube i n 0) :
    let Q := section9FiniteEndCube i n 0
    let T := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    (min (p : ℝ) (1-(p : ℝ)))^(2*d*(r+1)) *
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} W
        (Function.update x i (x i+(r : ℤ)))) ≤
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} (W \ {x}) x) := by
  intro Q T
  obtain ⟨hwall,hIT,hzI⟩ := section8_extension_source_geometry i n r hn hx hz
  exact section8_outward_surgery_probability p T Q F W x i r z hwall hW hIT hzI

/-- Actual source Step1 under the positive two-heart reveal law. Source
T12 avoids Q3 by proved geometry, so no freshness or disjointness premise is added. -/
theorem section8_extension_source_surgery_revealed_probability {d : ℕ} (p : unitInterval)
    (i : Fin d) (n r : ℕ) (hn : 16*(r+1) ≤ n)
    (H₁ H₃ F₁ F₃ W : Finset (Vertex d)) {x z : Vertex d}
    (hH₁ : H₁ ⊆ section9FiniteEndCube i n 0)
    (hH₃ : H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)))
    (hpos : percolation d p (section9RevealEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0)
    (hx : x ∈ section8ExtensionPositiveFaceCore i n)
    (hz : z ∈ section8ExtensionMiddleCore i n)
    (hW : W ⊆ section9FiniteEndCube i n 0) :
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let T := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    (min (p : ℝ) (1-(p : ℝ)))^(2*d*(r+1)) *
      ν.real (section9AvoidanceEvent T T Q₁ F₁ {z} W
        (Function.update x i (x i+(r : ℤ)))) ≤
      ν.real (section9AvoidanceEvent T T Q₁ F₁ {z} (W \ {x}) x) := by
  intro Q₁ Q₃ T ν
  have hn0 : 0 < n := by omega
  obtain ⟨hwall,hIT,hzI⟩ := section8_extension_source_geometry i n r hn hx hz
  exact section8_outward_surgery_revealed_probability p T Q₁ F₁ W H₁ Q₃ H₃ F₃
    x i r z hH₁ hH₃ hpos (section9FiniteLeftTube_disjoint_third i hn0) hwall hW hIT hzI

/-- Under the actual two-point asymptotics, source Step1 has a strictly
positive coefficient depending only on d and r, uniformly over scales,
directions, heart data, forbidden sets and source face/core vertices. -/
theorem section8_extension_source_surgery_positive_critical_coefficient {d : ℕ}
    (hd : 2 < d) (asymptotics : TwoPointAsymptotics d) (r : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ W : Finset (Vertex d)) (x z : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 →
      H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      x ∈ section8ExtensionPositiveFaceCore i n → z ∈ section8ExtensionMiddleCore i n →
      W ⊆ section9FiniteEndCube i n 0 →
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let T := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      c * ν.real (section9AvoidanceEvent T T Q₁ F₁ {z} W
        (Function.update x i (x i+(r : ℤ)))) ≤
      ν.real (section9AvoidanceEvent T T Q₁ F₁ {z} (W \ {x}) x) := by
  let i₀ : Fin d := ⟨0,by omega⟩
  obtain ⟨hp0,hp1⟩ := criticalPoint_interior_of_twoPointAsymptotics hd i₀ asymptotics
  let c : ℝ := (min (criticalPoint d : ℝ) (1-(criticalPoint d : ℝ)))^(2*d*(r+1))
  have hc : 0 < c := pow_pos (lt_min hp0 (sub_pos.mpr hp1)) _
  refine ⟨c,hc,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ W x z hH₁ hH₃ hpos hx hz hW
  exact section8_extension_source_surgery_revealed_probability (criticalPoint d)
    i n r hn H₁ H₃ F₁ F₃ W hH₁ hH₃ hpos hx hz hW

end NearCritical
