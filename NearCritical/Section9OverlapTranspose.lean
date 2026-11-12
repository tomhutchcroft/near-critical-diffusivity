module
public import NearCritical.Section9OverlapMatching

/-! Transposition of the two original ordered pivotal candidates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Exchanging the candidate labels transposes the intersection matrix,
identifying the two original cross-singleton events exactly. -/
theorem section9_cross_singleton_event_transpose {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f =
      section9OverlapPatternEvent .rightLeft L R Q₁ F₁ Q₃ F₃ A B f e := by
  ext ω
  constructor
  · rintro ⟨he,hf,hLL,hLR,hRL,hRR⟩
    exact ⟨hf,he,hLL.symm,hRL.symm,by simpa only [Finset.inter_comm] using hLR,hRR.symm⟩
  · rintro ⟨hf,he,hLL,hLR,hRL,hRR⟩
    exact ⟨he,hf,hLL.symm,by simpa only [Finset.inter_comm] using hRL,hLR.symm,hRR.symm⟩

/-- The source Case III and Case V probability sums are equal under ANY
configuration measure; no spatial symmetry or product-law assumption is used. -/
theorem section9_cross_singleton_sums_transpose {d : ℕ} (μ : Measure (Configuration d))
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (∑ e ∈ E, ∑ f ∈ E, μ.real (section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f)) =
      ∑ e ∈ E, ∑ f ∈ E, μ.real (section9OverlapPatternEvent .rightLeft L R Q₁ F₁ Q₃ F₃ A B e f) := by
  calc
    _ = ∑ e ∈ E, ∑ f ∈ E,
        μ.real (section9OverlapPatternEvent .rightLeft L R Q₁ F₁ Q₃ F₃ A B f e) := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      rw [section9_cross_singleton_event_transpose]
    _ = _ := Finset.sum_comm

end NearCritical
