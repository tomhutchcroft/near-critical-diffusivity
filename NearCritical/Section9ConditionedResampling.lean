module

public import NearCritical.Section9ResamplingLocalObservables
public import NearCritical.Section9ConditionalLaw

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Local finite-coordinate observables retain their expectations under
the actual positive heart-reveal law. -/
theorem section9RevealedLaw_local_expectation {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (T : Finset (Bond d))
    (hd : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) T)
    (f : Configuration d → ℝ)
    (hlocal : ∀ ω η, (∀ b ∈ T, ω b = η b) → f ω = f η) :
    (∫ ω, f ω ∂section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃) =
      ∫ ω, f ω ∂percolation d p := by
  let g := fun ξ : T → Bool => f (extendConfiguration T (fun _ => false) ξ)
  have he (ω : Configuration d) : g (T.restrict ω) = f ω := by
    apply (hlocal ω _ ?_).symm
    intro b hb
    simp [extendConfiguration, hb, Finset.restrict]
  have h := section9RevealedLaw_fresh_expectation p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos T hd g
  simpa only [he] using h

/-- Conditional two-cluster resampling factorization on the actual outer
heart-reveal atom, for finite observables of the available tube coordinates. -/
theorem section9_conditioned_two_cluster_factorization {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (e : Vertex d × Vertex d) (G : Finset (Bond d))
    (hG : G ⊆ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃)
    (F : ∀ C₁ C₃ : Finset (Vertex d),
      (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) → ℝ)
    (H : (G → Bool) → ℝ) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    (∫ ω, section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω *
      (∫ ζ, H (G.restrict (resampleBonds
        (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ))
        ∂percolation d p) ∂ν) =
      (∫ ω, section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω ∂ν) *
        (∫ ω, H (G.restrict ω) ∂ν) := by
  intro ν
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let W := section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F
  let K := fun ω : Configuration d => W ω *
    (∫ ζ, H (G.restrict (resampleBonds
      (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ)) ∂percolation d p)
  have hd := sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁
  have hWlocal := section9TwoClusterRevealWeight_local L R Q₁ F₁ Q₃ F₃ e F
  have hKlocal : ∀ ω η, (∀ b ∈ U, ω b = η b) → K ω = K η := by
    intro ω η hagree
    have hmask := section9TwoClusterRevealBonds_local L R Q₁ F₁ Q₃ F₃ e ω η hagree
    dsimp only [K, W]
    rw [hWlocal ω η hagree]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ζ
    congr 1
    funext b
    simp only [Finset.restrict]
    rw [hmask]
    unfold resampleBonds extendConfiguration
    split_ifs with hb
    · rfl
    · exact hagree b.val (hG b.property)
  have hHlocal : ∀ ω η, (∀ b ∈ U, ω b = η b) →
      H (G.restrict ω) = H (G.restrict η) := by
    intro ω η hagree
    congr 1
    funext b
    exact hagree b.val (hG b.property)
  have hK := section9RevealedLaw_local_expectation p Q₁ H₁ Q₃ H₃ F₁ F₃
    hH₁ hH₃ hpos U hd K hKlocal
  have hW := section9RevealedLaw_local_expectation p Q₁ H₁ Q₃ H₃ F₁ F₃
    hH₁ hH₃ hpos U hd W hWlocal
  have hH := section9RevealedLaw_local_expectation p Q₁ H₁ Q₃ H₃ F₁ F₃
    hH₁ hH₃ hpos U hd (fun ω => H (G.restrict ω)) hHlocal
  change (∫ ω, K ω ∂ν) = (∫ ω, W ω ∂ν) * (∫ ω, H (G.restrict ω) ∂ν)
  rw [hK, hW, hH]
  exact section9_adaptive_two_cluster_factorization p L R Q₁ F₁ Q₃ F₃ e G F H

end NearCritical
