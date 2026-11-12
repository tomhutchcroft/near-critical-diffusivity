module

public import NearCritical.Section9CoalescenceCross

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Every actual coalescing pair has either a common left root component,
a cross intersection in one orientation, or the exclusions for Case 3. -/
theorem section9_coalescence_case_split {d : ℕ} (ω η : Configuration d)
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (x y : Vertex d)
    (h : (section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ {x} B ∩
      section9SprinklingCluster ω η P L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty) :
    let C := sprinklingUnexploredCluster ω L Q₁ F₁
    let D := sprinklingUnexploredCluster ω R Q₃ F₃
    let X := sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {x} B
    let Y := sprinkledPivotalPairs ω η P L R Q₁ F₁ Q₃ F₃ {y} B
    ((C x ∩ C y).Nonempty ∧ X.Nonempty) ∨
    (∃ e ∈ X, ∃ f ∈ Y, Disjoint (C e.1) (C f.1) ∧
      ((D e.2 ∩ C f.1).Nonempty ∨ (D f.2 ∩ C e.1).Nonempty)) ∨
    (∀ e ∈ X, ∀ f ∈ Y, Disjoint (C e.1) (C f.1) ∧
      Disjoint (C e.1) (D f.2) ∧ Disjoint (D e.2) (C f.1)) := by
  intro C D X Y
  by_cases hxy : Disjoint (C x) (C y)
  · have hLL (e) (he : e ∈ X) (f) (hf : f ∈ Y) : Disjoint (C e.1) (C f.1) := by
      have heP := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      have hfP := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
      exact section9_left_pivot_components_disjoint ω L R Q₁ F₁ Q₃ F₃ B x y e f heP hfP hxy
    by_cases hcross : ∃ e ∈ X, ∃ f ∈ Y,
        (D e.2 ∩ C f.1).Nonempty ∨ (D f.2 ∩ C e.1).Nonempty
    · obtain ⟨e, he, f, hf, hcross⟩ := hcross
      exact Or.inr (Or.inl ⟨e, he, f, hf, hLL e he f hf, hcross⟩)
    · refine Or.inr (Or.inr (fun e he f hf => ⟨hLL e he f hf, ?_, ?_⟩))
      · apply Disjoint.symm
        by_contra hn
        exact hcross ⟨e, he, f, hf, Or.inr (Finset.not_disjoint_iff_nonempty_inter.mp hn)⟩
      · by_contra hn
        exact hcross ⟨e, he, f, hf, Or.inl (Finset.not_disjoint_iff_nonempty_inter.mp hn)⟩
  · obtain ⟨e, he, _⟩ := section9_coalescence_open_pivot_witness ω η P L R Q₁ F₁ Q₃ F₃ B x y h
    exact Or.inl ⟨Finset.not_disjoint_iff_nonempty_inter.mp hxy, ⟨e, he⟩⟩

/-- The event decomposition under any finite law, keeping the two
orientations of Case 2 separate. -/
theorem section9_coalescence_probability_le_cases {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (x y : Vertex d) :
    let C := fun ω => sprinklingUnexploredCluster ω L Q₁ F₁
    let D := fun ω => sprinklingUnexploredCluster ω R Q₃ F₃
    let O := fun (ξη : Configuration d × Configuration d) z =>
      sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {z} B
    let A₁ := {ξη : Configuration d × Configuration d |
      (C ξη.1 x ∩ C ξη.1 y).Nonempty ∧ (O ξη x).Nonempty}
    let A₂ := fun a b => {ξη : Configuration d × Configuration d |
      ∃ e ∈ O ξη a, ∃ f ∈ O ξη b, Disjoint (C ξη.1 e.1) (C ξη.1 f.1) ∧
        (D ξη.1 e.2 ∩ C ξη.1 f.1).Nonempty}
    let H := {ξη : Configuration d × Configuration d |
      (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {x} B ∩
        section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ {y} B).Nonempty}
    let A₃ := {ξη ∈ H | ∀ e ∈ O ξη x, ∀ f ∈ O ξη y,
      Disjoint (C ξη.1 e.1) (C ξη.1 f.1) ∧ Disjoint (C ξη.1 e.1) (D ξη.1 f.2) ∧
      Disjoint (D ξη.1 e.2) (C ξη.1 f.1)}
    μ.real H ≤ μ.real A₁ + (μ.real (A₂ x y) + (μ.real (A₂ y x) + μ.real A₃)) := by
  intro C D O A₁ A₂ H A₃
  have hsub : H ⊆ A₁ ∪ (A₂ x y ∪ (A₂ y x ∪ A₃)) := by
    rintro ⟨ω, η⟩ h
    rcases section9_coalescence_case_split ω η P L R Q₁ F₁ Q₃ F₃ B x y h with
      h₁ | ⟨e, he, f, hf, hLL, hcross | hcross⟩ | h₃
    · exact Or.inl h₁
    · exact Or.inr (Or.inl ⟨e, he, f, hf, hLL, hcross⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨f, hf, e, he, hLL.symm, hcross⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h, h₃⟩))
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl
      ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _)))))

end NearCritical
