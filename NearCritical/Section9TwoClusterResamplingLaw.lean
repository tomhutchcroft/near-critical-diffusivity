module

public import NearCritical.Section9FiberFactorization

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Replacing a specified pair fiber's examined bonds by independent bits
factors the old revealed-data weight from a new finite observable. -/
theorem section9_fixed_two_cluster_resampling_factorization {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (G : Finset (Bond d))
    (F : (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) → ℝ)
    (H : (G → Bool) → ℝ) :
    let S := section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃
    let E := section9TwoClusterFiberEvent L R Q₁ F₁ Q₃ F₃ C₁ C₃ e
    (∫ ω, E.indicator (fun η => F (S.restrict η)) ω *
      (∫ ζ, H (G.restrict (resampleBonds S ω ζ)) ∂percolation d p) ∂percolation d p) =
      (∫ ω, E.indicator (fun η => F (S.restrict η)) ω ∂percolation d p) *
        (∫ ω, H (G.restrict ω) ∂percolation d p) := by
  intro S E
  have hd : Disjoint S (G \ S : Finset (Bond d)) := by
    apply Finset.disjoint_left.mpr
    intro b hb hf
    exact (Finset.mem_sdiff.mp hf).2 hb
  have hf := section9_two_cluster_fiber_fresh_factorization p L R Q₁ F₁ Q₃ F₃ C₁ C₃ e
    (G \ S) hd F (resampleAverage p G S H)
  rw [integral_resampleAverage] at hf
  simpa only [integral_resampleBonds] using hf

/-- The same factorization for the actual adaptive two-cluster mask,
proved by identifying the fixed mask on its original cluster fiber. -/
theorem section9_two_cluster_resampling_factorization {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (G : Finset (Bond d))
    (F : (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) → ℝ)
    (H : (G → Bool) → ℝ) :
    let S := section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃
    let E := section9TwoClusterFiberEvent L R Q₁ F₁ Q₃ F₃ C₁ C₃ e
    (∫ ω, E.indicator (fun η => F (S.restrict η)) ω *
      (∫ ζ, H (G.restrict (resampleBonds
        (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ))
        ∂percolation d p) ∂percolation d p) =
      (∫ ω, E.indicator (fun η => F (S.restrict η)) ω ∂percolation d p) *
        (∫ ω, H (G.restrict ω) ∂percolation d p) := by
  intro S E
  rw [← section9_fixed_two_cluster_resampling_factorization p L R Q₁ F₁ Q₃ F₃ C₁ C₃ e G F H]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hE : ω ∈ E
  · have hC : sprinklingUnexploredCluster ω L Q₁ F₁ e.1 = C₁ ∧
        sprinklingUnexploredCluster ω R Q₃ F₃ e.2 = C₃ := hE
    have hm := section9TwoClusterRevealBonds_eq_fiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ e ω hC.1 hC.2
    simp_rw [hm]
    rfl
  · simp only [E] at hE ⊢
    simp [hE]

end NearCritical
