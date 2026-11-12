module

public import NearCritical.Section9TwoClusterResamplingLaw

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

/-- Arbitrary observable of both explored clusters and their examined bits. -/
def section9TwoClusterRevealWeight {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (F : ∀ C₁ C₃ : Finset (Vertex d),
      (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) → ℝ)
    (ω : Configuration d) : ℝ :=
  F (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
    (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
    ((section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃
      (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)).restrict ω)

/-- Summed two-cluster resampling identity under the actual product law. -/
theorem section9_adaptive_two_cluster_factorization {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (G : Finset (Bond d))
    (F : ∀ C₁ C₃ : Finset (Vertex d),
      (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) → ℝ)
    (H : (G → Bool) → ℝ) :
    (∫ ω, section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω *
      (∫ ζ, H (G.restrict (resampleBonds
        (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ))
        ∂percolation d p) ∂percolation d p) =
      (∫ ω, section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω ∂percolation d p) *
        (∫ ω, H (G.restrict ω) ∂percolation d p) := by
  let I := L.powerset.product R.powerset
  let S := fun C : Finset (Vertex d) × Finset (Vertex d) =>
    section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C.1 C.2
  let E := fun C : Finset (Vertex d) × Finset (Vertex d) =>
    section9TwoClusterFiberEvent L R Q₁ F₁ Q₃ F₃ C.1 C.2 e
  let W := fun C (ω : Configuration d) =>
    (E C).indicator (fun η => F C.1 C.2 ((S C).restrict η)) ω
  have hlocal (C) (ω : Configuration d) :
      W C ω =
        (section9TwoClusterLocalFiber L R Q₁ F₁ Q₃ F₃ C.1 C.2 e).indicator
          (F C.1 C.2) ((S C).restrict ω) := by
    have he := section9_two_cluster_fiber_cylinder L R Q₁ F₁ Q₃ F₃ C.1 C.2 e
    have hm : ω ∈ E C ↔ (S C).restrict ω ∈
        section9TwoClusterLocalFiber L R Q₁ F₁ Q₃ F₃ C.1 C.2 e :=
      Set.ext_iff.mp he ω
    by_cases hω : ω ∈ E C
    · simp [W, hω, hm.mp hω]
    · have hn := mt hm.mpr hω
      simp [W, hω, hn]
  have hi (C) : Integrable (W C) (percolation d p) := by
    have hi := percolation_cylinder_integrable d p (S C)
      ((section9TwoClusterLocalFiber L R Q₁ F₁ Q₃ F₃ C.1 C.2 e).indicator (F C.1 C.2))
    exact hi.congr (ae_of_all _ (fun ω => (hlocal C ω).symm))
  have hk (C) : Integrable (fun ω => W C ω *
      (∫ ζ, H (G.restrict (resampleBonds (S C) ω ζ)) ∂percolation d p))
      (percolation d p) := by
    simp_rw [integral_resampleBonds, hlocal]
    exact integrable_two_block_product p _ _ _ _
  have hsum (ω : Configuration d) :
      (∑ C ∈ I, W C ω) = section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω := by
    let C₀ := (sprinklingUnexploredCluster ω L Q₁ F₁ e.1,
      sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
    rw [Finset.sum_eq_single C₀]
    · simp [W, E, S, C₀, section9TwoClusterFiberEvent, section9TwoClusterRevealWeight]
    · intro C _ hC
      have hn : ω ∉ E C := by
        intro h
        have hh : C₀ = C := Prod.ext h.1 h.2
        exact hC hh.symm
      simp [W, hn]
    · intro hn
      exact (hn (Finset.mem_product.mpr
        ⟨Finset.mem_powerset.mpr (sprinklingUnexploredCluster_subset ω L Q₁ F₁ e.1),
         Finset.mem_powerset.mpr (sprinklingUnexploredCluster_subset ω R Q₃ F₃ e.2)⟩)).elim
  have hp (ω : Configuration d) :
      section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω *
        (∫ ζ, H (G.restrict (resampleBonds
          (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ)) ∂percolation d p) =
      ∑ C ∈ I, W C ω *
        (∫ ζ, H (G.restrict (resampleBonds (S C) ω ζ)) ∂percolation d p) := by
    rw [← hsum ω, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro C _
    by_cases h : ω ∈ E C
    · have hm := section9TwoClusterRevealBonds_eq_fiberMask L R Q₁ F₁ Q₃ F₃ C.1 C.2 e ω h.1 h.2
      simp_rw [hm]
      rfl
    · simp [W, h]
  simp_rw [hp]
  rw [integral_finsetSum _ (fun C _ => hk C)]
  have hf (C) :
      (∫ ω, W C ω * (∫ ζ, H (G.restrict (resampleBonds (S C) ω ζ))
        ∂percolation d p) ∂percolation d p) =
      (∫ ω, W C ω ∂percolation d p) *
        (∫ ω, H (G.restrict ω) ∂percolation d p) :=
    section9_fixed_two_cluster_resampling_factorization p L R Q₁ F₁ Q₃ F₃ C.1 C.2 e G (F C.1 C.2) H
  simp_rw [hf]
  rw [← Finset.sum_mul]
  congr 1
  rw [← integral_finsetSum _ (fun C _ => hi C)]
  exact integral_congr_ae (ae_of_all _ hsum)

end NearCritical
