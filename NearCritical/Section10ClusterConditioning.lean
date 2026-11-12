module

public import NearCritical.Section10TubeConditioning
public import NearCritical.Section9RevealSupport

/-! Section10: fresh tube products conditioned on an ACTUAL finite family of
heart-cluster reveals. Infinite-family G and monotone coupling remain separate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
open MeasureTheory
variable {J : Type*}

def clusterFamilyRevealBonds {d : ℕ} (s : Finset J)
    (Q F : J → Finset (Vertex d)) : Finset (Bond d) :=
  s.biUnion (fun j => clusterRevealBonds (Q j) (F j))

def clusterFamilyRevealEvent {d : ℕ} (s : Finset J)
    (Q H F : J → Finset (Vertex d)) : Set (Configuration d) :=
  {ω | ∀ j ∈ s, heartClusterUnion ω (Q j) (H j) = F j}

def clusterFamilyLocalEvent {d : ℕ} (s : Finset J)
    (Q H F : J → Finset (Vertex d)) : Set (clusterFamilyRevealBonds s Q F → Bool) :=
  {ξ | ∀ j ∈ s, heartClusterUnion
    (extendConfiguration (clusterFamilyRevealBonds s Q F) (fun _ => false) ξ) (Q j) (H j) = F j}

/-- Actual finite cluster-family history is determined by its explored incident
bonds, including closed boundary bonds. No entire-cube revelation is needed. -/
theorem clusterFamilyReveal_event_cylinder {d : ℕ} (s : Finset J)
    (Q H F : J → Finset (Vertex d)) (hH : ∀ j ∈ s, H j ⊆ Q j) :
    clusterFamilyRevealEvent s Q H F =
      (clusterFamilyRevealBonds s Q F).restrict ⁻¹' clusterFamilyLocalEvent s Q H F := by
  ext ω
  change (∀ j ∈ s, heartClusterUnion ω (Q j) (H j) = F j) ↔
    (∀ j ∈ s, heartClusterUnion
      (extendConfiguration (clusterFamilyRevealBonds s Q F) (fun _ => false)
        ((clusterFamilyRevealBonds s Q F).restrict ω)) (Q j) (H j) = F j)
  have heq (j : J) (hj : j ∈ s) : heartClusterUnion ω (Q j) (H j) = F j ↔
      heartClusterUnion
        (extendConfiguration (clusterFamilyRevealBonds s Q F) (fun _ => false)
          ((clusterFamilyRevealBonds s Q F).restrict ω)) (Q j) (H j) = F j := by
    apply heartClusterUnion_eq_iff_reveal_agree (Q j) (H j) (F j) (hH j hj)
    intro e he
    have heS : e ∈ clusterFamilyRevealBonds s Q F := Finset.mem_biUnion.mpr ⟨j,hj,he⟩
    simp [extendConfiguration,heS,Finset.restrict]
  exact ⟨fun h j hj => (heq j hj).mp (h j hj),fun h j hj => (heq j hj).mpr (h j hj)⟩

theorem measurableSet_clusterFamilyRevealEvent {d : ℕ} (s : Finset J)
    (Q H F : J → Finset (Vertex d)) (hH : ∀ j ∈ s, H j ⊆ Q j) :
    MeasurableSet (clusterFamilyRevealEvent s Q H F) := by
  rw [clusterFamilyReveal_event_cylinder s Q H F hH]
  exact (Set.toFinite (clusterFamilyLocalEvent s Q H F)).measurableSet.preimage
    (Finset.measurable_restrict (clusterFamilyRevealBonds s Q F))

/-- On the actual cluster-family reveal event, fresh tube observables factor
against the event probability under the actual infinite Bernoulli law. -/
theorem clusterFamilyReveal_freshTube_factorization {d : ℕ} (p : unitInterval)
    {ell : ℝ} (hell : 0 < ell) (ambient : Finset (Bond d)) (s : Finset J)
    (Q H F : J → Finset (Vertex d)) (hH : ∀ j ∈ s, H j ⊆ Q j)
    (tubes : Finset ((Fin d → ℤ) × Fin d))
    (f : ∀ e : (Fin d → ℤ) × Fin d,
      (freshCoarseTubeBonds ell ambient (clusterFamilyRevealBonds s Q F) e.1 e.2 → Bool) → ℝ) :
    (∫ ω : Configuration d, (clusterFamilyRevealEvent s Q H F).indicator (fun _ => (1:ℝ)) ω *
      (∏ e ∈ tubes, f e ((freshCoarseTubeBonds ell ambient
        (clusterFamilyRevealBonds s Q F) e.1 e.2).restrict ω)) ∂percolation d p) =
      (percolation d p).real (clusterFamilyRevealEvent s Q H F) *
        (∏ e ∈ tubes, ∫ ω : Configuration d, f e ((freshCoarseTubeBonds ell ambient
          (clusterFamilyRevealBonds s Q F) e.1 e.2).restrict ω) ∂percolation d p) := by
  let A := clusterFamilyLocalEvent s Q H F
  let S := clusterFamilyRevealBonds s Q F
  have hc := clusterFamilyReveal_event_cylinder s Q H F hH
  have hi (ω : Configuration d) :
      (clusterFamilyRevealEvent s Q H F).indicator (fun _ => (1:ℝ)) ω =
        A.indicator (fun _ => (1:ℝ)) (S.restrict ω) := by
    rw [hc]
    rfl
  have hf := percolation_reveal_freshTube_product p hell ambient S tubes
    (A.indicator (fun _ => (1:ℝ))) f
  simp_rw [← hi] at hf
  have hOne : (∫ ω : Configuration d,
      (clusterFamilyRevealEvent s Q H F).indicator (fun _ => (1:ℝ)) ω ∂percolation d p) =
        (percolation d p).real (clusterFamilyRevealEvent s Q H F) := by
    exact integral_indicator_one (measurableSet_clusterFamilyRevealEvent s Q H F hH)
  rwa [hOne] at hf

/-- Positive actual history probability gives a genuine conditional normalized
product identity. The source conditional product law is not a hypothesis. -/
theorem clusterFamilyReveal_conditional_freshTube_product {d : ℕ} (p : unitInterval)
    {ell : ℝ} (hell : 0 < ell) (ambient : Finset (Bond d)) (s : Finset J)
    (Q H F : J → Finset (Vertex d)) (hH : ∀ j ∈ s, H j ⊆ Q j)
    (tubes : Finset ((Fin d → ℤ) × Fin d))
    (f : ∀ e : (Fin d → ℤ) × Fin d,
      (freshCoarseTubeBonds ell ambient (clusterFamilyRevealBonds s Q F) e.1 e.2 → Bool) → ℝ)
    (hprob : 0 < (percolation d p).real (clusterFamilyRevealEvent s Q H F)) :
    (∫ ω : Configuration d, (clusterFamilyRevealEvent s Q H F).indicator (fun _ => (1:ℝ)) ω *
      (∏ e ∈ tubes, f e ((freshCoarseTubeBonds ell ambient
        (clusterFamilyRevealBonds s Q F) e.1 e.2).restrict ω)) ∂percolation d p) /
        (percolation d p).real (clusterFamilyRevealEvent s Q H F) =
      ∏ e ∈ tubes, ∫ ω : Configuration d, f e ((freshCoarseTubeBonds ell ambient
        (clusterFamilyRevealBonds s Q F) e.1 e.2).restrict ω) ∂percolation d p := by
  rw [clusterFamilyReveal_freshTube_factorization p hell ambient s Q H F hH tubes f]
  field_simp [hprob.ne']

end NearCritical.Section10
