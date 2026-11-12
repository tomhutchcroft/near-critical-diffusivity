module
public import NearCritical.Section8OutwardSegment
public import NearCritical.Section8SurgeryMaskCard

/-! Actual outward-segment surgery with scale-independent finite-energy cost. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- For the actual axial segment, connectivity, cardinality and forbidden
intersection follow from a supporting coordinate wall of Q. -/
theorem section8_outward_surgery_probability {d : ℕ} (p : unitInterval)
    (T Q F W : Finset (Vertex d)) (x : Vertex d) (i : Fin d) (r : ℕ) (z : Vertex d)
    (hwall : ∀ y ∈ Q, y i ≤ x i) (hW : W ⊆ Q)
    (hIT : section8OutwardSegment x i r ⊆ T) (hz : z ∉ section8OutwardSegment x i r) :
    (min (p : ℝ) (1-(p : ℝ)))^(2*d*(r+1)) *
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} W
        (Function.update x i (x i+(r : ℤ)))) ≤
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} (W \ {x}) x) := by
  obtain ⟨hx,hxr,hconnected,hIW⟩ := section8_outward_segment_structural_guards x i r Q F W hwall hW
  exact section8_unique_extension_uniform_surgery_probability p T Q F
    (section8OutwardSegment x i r) W x (Function.update x i (x i+(r : ℤ))) z r
    (section8_outward_segment_card x i r).le hIT hx hxr hz hIW hconnected

/-- The same actual axial comparison holds under the actual positive
heart-reveal law, with coefficient depending only on d,r,p. -/
theorem section8_outward_surgery_revealed_probability {d : ℕ} (p : unitInterval)
    (T Q F W H Q₃ H₃ F₃ : Finset (Vertex d))
    (x : Vertex d) (i : Fin d) (r : ℕ) (z : Vertex d)
    (hH : H ⊆ Q) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q H Q₃ H₃ F F₃) ≠ 0)
    (hTQ₃ : Disjoint T Q₃) (hwall : ∀ y ∈ Q, y i ≤ x i) (hW : W ⊆ Q)
    (hIT : section8OutwardSegment x i r ⊆ T) (hz : z ∉ section8OutwardSegment x i r) :
    let ν := section9RevealedLaw p Q H Q₃ H₃ F F₃
    (min (p : ℝ) (1-(p : ℝ)))^(2*d*(r+1)) *
      ν.real (section9AvoidanceEvent T T Q F {z} W (Function.update x i (x i+(r : ℤ)))) ≤
      ν.real (section9AvoidanceEvent T T Q F {z} (W \ {x}) x) := by
  intro ν
  obtain ⟨hx,hxr,hconnected,hIW⟩ := section8_outward_segment_structural_guards x i r Q F W hwall hW
  exact section8_unique_extension_uniform_surgery_revealed_probability p T Q F
    (section8OutwardSegment x i r) W H Q₃ H₃ F₃ x (Function.update x i (x i+(r : ℤ))) z r
    (section8_outward_segment_card x i r).le hH hH₃ hpos hTQ₃ hIT hx hxr hz hIW hconnected

end NearCritical
