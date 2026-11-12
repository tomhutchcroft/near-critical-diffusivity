module
public import NearCritical.Section9PivotOpening

/-! Physical fresh successes produce actual opened critical pivotal pairs. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

/-- Reaching a target through a fresh physical pivot is counted by the actual
source pivo observable, even when different orientations share a bond. -/
theorem section9_physical_target_success_count_le {d : ℕ} {ι : Type*}
    (I : Finset ι) (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d))
    (targets : ι → Finset (Vertex d))
    (bond : (Vertex d × Vertex d) → Bond d)
    (hends : ∀ e ∈ E, s((bond e).1,bondTip (bond e)) = s(e.1,e.2))
    (ω ζ : Configuration d) :
    (∑ j ∈ I, if ∃ b ∈ (sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j)).image bond,
      ζ b = true then (1 : ℝ) else 0) ≤
      ((I.filter fun j => (sprinkledPivotalPairs ω (sprinkleOrConfiguration ω ζ)
        E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ) := by
  have htarget (j : ι)
      (h : ∃ b ∈ (sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j)).image bond,
        ζ b = true) :
      (sprinkledPivotalPairs ω (sprinkleOrConfiguration ω ζ)
        E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty := by
    obtain ⟨b,hb,hζ⟩ := h
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
    have hpair := hends e (Finset.mem_filter.mp he).1
    have hopen : (openGraph (sprinkleOrConfiguration ω ζ)).Adj e.1 e.2 := by
      refine ⟨bond e,by simp only [sprinkleOrConfiguration,hζ,Bool.or_true],?_⟩
      rcases Sym2.eq_iff.mp hpair with ⟨hb,ht⟩ | ⟨hb,ht⟩
      · exact Or.inl ⟨hb.symm,ht.symm⟩
      · exact Or.inr ⟨hb.symm,ht.symm⟩
    exact ⟨e,Finset.mem_filter.mpr ⟨he,hopen⟩⟩
  calc
    _ ≤ ∑ j ∈ I, if (sprinkledPivotalPairs ω (sprinkleOrConfiguration ω ζ)
        E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h h'
      · exact le_rfl
      · exact False.elim (h' (htarget j h))
      · norm_num
      · exact le_rfl
    _ = _ := by rw [← Finset.sum_filter]; simp

end NearCritical
