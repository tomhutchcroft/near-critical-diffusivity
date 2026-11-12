module
public import NearCritical.Section9FiberFactorization
public import NearCritical.FiniteBlockResampling

/-! The law of finite observables after closing the actual fixed fiber mask. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Closing the fixed examined mask makes an observable independent of the
actual cluster fiber. The original configuration is still sampled from the
actual product law; no conditional independence is assumed. -/
theorem section9_closed_fiber_observable_factorization {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (G : Finset (Bond d)) (f : (G → Bool) → ℝ) :
    let S := section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃
    let E := section9TwoClusterFiberEvent L R Q₁ F₁ Q₃ F₃ C₁ C₃ e
    (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω *
      f (G.restrict (resampleBonds S ω (fun _ => false))) ∂percolation d p) =
      (percolation d p).real E *
        (∫ ω, f (G.restrict (resampleBonds S ω (fun _ => false))) ∂percolation d p) := by
  intro S E
  let T := G \ S
  let H : (T → Bool) → ℝ := fun ξ =>
    f (mergeResampledBits G S (S.restrict (fun _ => false)) ξ)
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro b hbS hbT
    exact (Finset.mem_sdiff.mp hbT).2 hbS
  have hmap (ω : Configuration d) :
      H (T.restrict ω) = f (G.restrict (resampleBonds S ω (fun _ => false))) := by
    dsimp only [H,T]
    rw [resampleBonds_restrict]
  have hE : MeasurableSet E := by
    change MeasurableSet (section9TwoClusterFiberEvent L R Q₁ F₁ Q₃ F₃ C₁ C₃ e)
    rw [section9_two_cluster_fiber_cylinder]
    exact (Set.toFinite _).measurableSet.preimage (Finset.measurable_restrict _)
  have hmass : (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂percolation d p) =
      (percolation d p).real E := by
    simpa only [Set.indicator_apply,Pi.one_apply] using integral_indicator_one (μ := percolation d p) hE
  have hfact := section9_two_cluster_fiber_fresh_factorization p
    L R Q₁ F₁ Q₃ F₃ C₁ C₃ e T hdis (fun _ => (1 : ℝ)) H
  change (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω * H (T.restrict ω) ∂percolation d p) =
    (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂percolation d p) *
      (∫ ω, H (T.restrict ω) ∂percolation d p) at hfact
  rw [hmass] at hfact
  simpa only [hmap] using hfact

/-- Single actual deleted-cluster specialization, obtained with an empty
second exploration. No positivity of the fiber probability is required. -/
theorem section9_closed_single_cluster_observable_factorization {d : ℕ}
    (p : unitInterval) (L Q F C : Finset (Vertex d)) (root : Vertex d)
    (G : Finset (Bond d)) (f : (G → Bool) → ℝ) :
    let S := sprinklingClusterFiberMask L Q F C
    let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q F root = C}
    (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω *
      f (G.restrict (resampleBonds S ω (fun _ => false))) ∂percolation d p) =
      (percolation d p).real E *
        (∫ ω, f (G.restrict (resampleBonds S ω (fun _ => false))) ∂percolation d p) := by
  have hempty (ω : Configuration d) :
      sprinklingUnexploredCluster ω (∅ : Finset (Vertex d)) ∅ ∅ root = ∅ := by
    simp [sprinklingUnexploredCluster]
  have hmask : section9TwoClusterFiberMask L ∅ Q F ∅ ∅ C ∅ =
      sprinklingClusterFiberMask L Q F C := by
    simp [section9TwoClusterFiberMask,sprinklingClusterFiberMask]
  have hevent : section9TwoClusterFiberEvent L ∅ Q F ∅ ∅ C ∅ (root,root) =
      {ω : Configuration d | sprinklingUnexploredCluster ω L Q F root = C} := by
    ext ω
    simp [section9TwoClusterFiberEvent,hempty]
  simpa only [hmask,hevent] using section9_closed_fiber_observable_factorization p
    L ∅ Q F ∅ ∅ C ∅ (root,root) G f

end NearCritical
