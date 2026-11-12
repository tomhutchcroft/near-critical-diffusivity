module

public import NearCritical.Section9RevealFiber
public import NearCritical.NestFreshTube

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

def section9TwoClusterFiberEvent {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    Set (Configuration d) :=
  {ω | sprinklingUnexploredCluster ω L Q₁ F₁ e.1 = C₁ ∧
    sprinklingUnexploredCluster ω R Q₃ F₃ e.2 = C₃}

def section9TwoClusterLocalFiber {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    Set (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) :=
  {ξ | extendConfiguration (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃)
    (fun _ => false) ξ ∈ section9TwoClusterFiberEvent L R Q₁ F₁ Q₃ F₃ C₁ C₃ e}

theorem section9_two_cluster_fiber_cylinder {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    section9TwoClusterFiberEvent L R Q₁ F₁ Q₃ F₃ C₁ C₃ e =
      (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃).restrict ⁻¹'
        section9TwoClusterLocalFiber L R Q₁ F₁ Q₃ F₃ C₁ C₃ e := by
  ext ω
  apply section9_two_cluster_fiber_local L R Q₁ F₁ Q₃ F₃ C₁ C₃ e
  intro b hb
  simp [extendConfiguration, hb, Finset.restrict]

/-- Arbitrary revealed-data weights on the two-cluster fiber factor from
finite observables on any disjoint unrevealed bond block. -/
theorem section9_two_cluster_fiber_fresh_factorization {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (T : Finset (Bond d))
    (hd : Disjoint (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃) T)
    (F : (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) → ℝ)
    (H : (T → Bool) → ℝ) :
    let S := section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃
    let E := section9TwoClusterFiberEvent L R Q₁ F₁ Q₃ F₃ C₁ C₃ e
    (∫ ω, E.indicator (fun η => F (S.restrict η)) ω * H (T.restrict ω) ∂percolation d p) =
      (∫ ω, E.indicator (fun η => F (S.restrict η)) ω ∂percolation d p) *
        (∫ ω, H (T.restrict ω) ∂percolation d p) := by
  intro S E
  let A := section9TwoClusterLocalFiber L R Q₁ F₁ Q₃ F₃ C₁ C₃ e
  have hE : E = S.restrict ⁻¹' A :=
    section9_two_cluster_fiber_cylinder L R Q₁ F₁ Q₃ F₃ C₁ C₃ e
  have hI (ω : Configuration d) :
      E.indicator (fun η => F (S.restrict η)) ω = A.indicator F (S.restrict ω) := by
    have hm : ω ∈ E ↔ S.restrict ω ∈ A := Set.ext_iff.mp hE ω
    by_cases hω : ω ∈ E
    · simp [hω, hm.mp hω]
    · have hn : S.restrict ω ∉ A := fun h => hω (hm.mpr h)
      simp [hω, hn]
  simp_rw [hI]
  rw [percolation_disjoint_block_integral p S T hd
    (fun z => A.indicator F z.1 * H z.2)]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  rw [integral_finite_bernoulli, integral_finite_bernoulli,
    ← percolation_cylinder_expectation d p S (A.indicator F),
    ← percolation_cylinder_expectation d p T H]

end NearCritical
