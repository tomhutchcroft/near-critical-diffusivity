module

public import NearCritical.Section9ConditionalLaw

/-! The actual random pivot count uses the heart unions of the same field.
Its finite reveal partition justifies measurability and conditional freezing. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

def section9AdaptivePivotalCount {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ Q₃ H₃ A B : Finset (Vertex d)) (ω : Configuration d) : ℝ :=
  section9PivotalCount E L R Q₁ (heartClusterUnion ω Q₁ H₁)
    Q₃ (heartClusterUnion ω Q₃ H₃) A B ω

lemma section9AdaptivePivotalCount_eq_sum {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ Q₃ H₃ A B : Finset (Vertex d)) (ω : Configuration d) :
    section9AdaptivePivotalCount E L R Q₁ H₁ Q₃ H₃ A B ω =
      ∑ F ∈ Q₁.powerset.product Q₃.powerset,
        (section9RevealEvent Q₁ H₁ Q₃ H₃ F.1 F.2).indicator
          (section9PivotalCount E L R Q₁ F.1 Q₃ F.2 A B) ω := by
  let Fω := (heartClusterUnion ω Q₁ H₁, heartClusterUnion ω Q₃ H₃)
  have hFω : Fω ∈ Q₁.powerset.product Q₃.powerset := Finset.mem_product.mpr
    ⟨Finset.mem_powerset.mpr (heartClusterUnion_subset ω Q₁ H₁),
      Finset.mem_powerset.mpr (heartClusterUnion_subset ω Q₃ H₃)⟩
  symm
  rw [Finset.sum_eq_single Fω]
  · have hω : ω ∈ section9RevealEvent Q₁ H₁ Q₃ H₃ Fω.1 Fω.2 := ⟨rfl,rfl⟩
    rw [Set.indicator_of_mem hω]
    rfl
  · intro F _ hne
    have hnot : ω ∉ section9RevealEvent Q₁ H₁ Q₃ H₃ F.1 F.2 := by
      intro h
      apply hne
      exact Prod.ext h.1.symm h.2.symm
    exact Set.indicator_of_notMem hnot _
  · intro hnot
    exact (hnot hFω).elim

private lemma adaptive_count_fun_eq_sum {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ Q₃ H₃ A B : Finset (Vertex d)) :
    section9AdaptivePivotalCount E L R Q₁ H₁ Q₃ H₃ A B = fun ω =>
      ∑ F ∈ Q₁.powerset.product Q₃.powerset,
        (section9RevealEvent Q₁ H₁ Q₃ H₃ F.1 F.2).indicator
          (section9PivotalCount E L R Q₁ F.1 Q₃ F.2 A B) ω := by
  funext ω
  exact section9AdaptivePivotalCount_eq_sum E L R Q₁ H₁ Q₃ H₃ A B ω

lemma measurable_section9AdaptivePivotalCount {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ Q₃ H₃ A B : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) :
    Measurable (section9AdaptivePivotalCount E L R Q₁ H₁ Q₃ H₃ A B) := by
  rw [adaptive_count_fun_eq_sum]
  exact (Q₁.powerset.product Q₃.powerset).measurable_fun_sum (fun F _ =>
    (measurable_section9PivotalCount E L R Q₁ F.1 Q₃ F.2 A B).indicator
      (measurableSet_section9RevealEvent Q₁ H₁ Q₃ H₃ F.1 F.2 hH₁ hH₃))

lemma integrable_section9AdaptivePivotalCount {d : ℕ} (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ Q₃ H₃ A B : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) :
    Integrable (section9AdaptivePivotalCount E L R Q₁ H₁ Q₃ H₃ A B) μ := by
  rw [adaptive_count_fun_eq_sum]
  exact integrable_finsetSum (Q₁.powerset.product Q₃.powerset) (fun F _ =>
    (integrable_section9PivotalCount μ E L R Q₁ F.1 Q₃ F.2 A B).indicator
      (measurableSet_section9RevealEvent Q₁ H₁ Q₃ H₃ F.1 F.2 hH₁ hH₃))

/-- On the actual revealed law, freezing F1/F3 does not change the integral
of the actual adaptive pivot count. This also handles zero atoms as zero laws. -/
theorem integral_section9AdaptivePivotalCount_revealed {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) :
    (∫ ω, section9AdaptivePivotalCount E L R Q₁ H₁ Q₃ H₃ A B ω
      ∂section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃) =
      section9PivotalMean (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃)
        E L R Q₁ F₁ Q₃ F₃ A B := by
  unfold section9PivotalMean
  apply integral_congr_ae
  filter_upwards [section9RevealedLaw_ae_values p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃] with ω hω
  simp only [section9AdaptivePivotalCount,hω.1,hω.2]

end NearCritical
