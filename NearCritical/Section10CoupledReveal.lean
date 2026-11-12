module

public import NearCritical.Section10ClusterConditioning
public import NearCritical.NestCoupledExit

/-! Section10: actual critical cluster reveals in the existing monotone thinning
coupling. The fresh observable here uses the supercritical configuration only. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
open MeasureTheory

/-- Both finite past samples may be revealed; the fresh supercritical block
remains independent, derived from the existing actual coupled block law. -/
theorem coupled_past_fresh_integral {d : ℕ} (p q : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T)
    (H : (S → Bool) × (S → Bool) → ℝ) (g : (T → Bool) → ℝ) :
    (∫ z : Configuration d × Configuration d,
      H (S.restrict z.1,S.restrict z.2)*g (T.restrict z.1)
        ∂((percolation d p).prod (percolation d q))) =
      (∫ z : Configuration d × Configuration d, H (S.restrict z.1,S.restrict z.2)
        ∂((percolation d p).prod (percolation d q))) *
      (∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p) := by
  have hf := percolation_coupled_block_integral p q S S T hd
    (fun η ζ ξ => H (η,ζ)*g ξ)
  simp_rw [integral_const_mul] at hf
  simp_rw [integral_mul_const] at hf
  have hg : (∫ ξ, g ξ ∂(Measure.pi (fun _ : T => ProbabilityTheory.bernoulliMeasure true false p))) =
      ∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p := by
    rw [integral_finite_bernoulli,← percolation_cylinder_expectation d p T g]
  rw [hg] at hf
  have hb := percolation_coupled_block_integral p q S S ∅ (by simp)
    (fun η ζ _ => H (η,ζ))
  simp only [integral_const,probReal_univ,one_smul] at hb
  rw [← hb] at hf
  exact hf

/-- Fresh supercritical coordinates outside the incident mask of ACTUAL
critical heart-cluster reveals have the unrestricted supercritical law. The
critical atom mass is identified using the exact existing thinning-map law. -/
theorem coupled_clusterReveal_fresh_factorization {d : ℕ} {J : Type*}
    (p q pc : unitInterval) (hpc : (pc:ℝ) = (p:ℝ)*(q:ℝ))
    (s : Finset J) (Q H F : J → Finset (Vertex d)) (hH : ∀ j ∈ s, H j ⊆ Q j)
    (T : Finset (Bond d)) (hd : Disjoint (clusterFamilyRevealBonds s Q F) T)
    (g : (T → Bool) → ℝ) :
    (∫ z : Configuration d × Configuration d,
      (clusterFamilyRevealEvent s Q H F).indicator (fun _ => (1:ℝ)) (thinConfiguration z) *
        g (T.restrict z.1) ∂((percolation d p).prod (percolation d q))) =
      (percolation d pc).real (clusterFamilyRevealEvent s Q H F) *
        (∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p) := by
  let S := clusterFamilyRevealBonds s Q F
  let A := clusterFamilyLocalEvent s Q H F
  let K : (S → Bool) × (S → Bool) → ℝ := fun η =>
    A.indicator (fun _ => (1:ℝ)) (fun e => η.1 e && η.2 e)
  have hc := clusterFamilyReveal_event_cylinder s Q H F hH
  have he (z : Configuration d × Configuration d) :
      K (S.restrict z.1,S.restrict z.2) =
        (clusterFamilyRevealEvent s Q H F).indicator (fun _ => (1:ℝ)) (thinConfiguration z) := by
    rw [hc]
    rfl
  have hf := coupled_past_fresh_integral p q S T hd K g
  simp_rw [he] at hf
  have hm := measurableSet_clusterFamilyRevealEvent s Q H F hH
  have hmass : (∫ z : Configuration d × Configuration d,
      (clusterFamilyRevealEvent s Q H F).indicator (fun _ => (1:ℝ)) (thinConfiguration z)
        ∂((percolation d p).prod (percolation d q))) =
      (percolation d pc).real (clusterFamilyRevealEvent s Q H F) := by
    calc
      _ = ∫ ω : Configuration d, (clusterFamilyRevealEvent s Q H F).indicator
          (fun _ => (1:ℝ)) ω
          ∂(((percolation d p).prod (percolation d q)).map thinConfiguration) :=
        (integral_map measurable_thinConfiguration.aemeasurable
          (measurable_const.indicator hm).aestronglyMeasurable).symm
      _ = _ := by
        rw [percolation_thin_map d p q pc hpc]
        exact integral_indicator_one hm
  rwa [hmass] at hf

/-- Positive critical reveal probability permits genuine conditional
normalization, with the fresh mean taken at the supercritical parameter p. -/
theorem coupled_clusterReveal_conditional_fresh_mean {d : ℕ} {J : Type*}
    (p q pc : unitInterval) (hpc : (pc:ℝ) = (p:ℝ)*(q:ℝ))
    (s : Finset J) (Q H F : J → Finset (Vertex d)) (hH : ∀ j ∈ s, H j ⊆ Q j)
    (T : Finset (Bond d)) (hd : Disjoint (clusterFamilyRevealBonds s Q F) T)
    (g : (T → Bool) → ℝ)
    (hprob : 0 < (percolation d pc).real (clusterFamilyRevealEvent s Q H F)) :
    (∫ z : Configuration d × Configuration d,
      (clusterFamilyRevealEvent s Q H F).indicator (fun _ => (1:ℝ)) (thinConfiguration z) *
        g (T.restrict z.1) ∂((percolation d p).prod (percolation d q))) /
        (percolation d pc).real (clusterFamilyRevealEvent s Q H F) =
      ∫ ω : Configuration d, g (T.restrict ω) ∂percolation d p := by
  rw [coupled_clusterReveal_fresh_factorization p q pc hpc s Q H F hH T hd g]
  field_simp [hprob.ne']

end NearCritical.Section10
