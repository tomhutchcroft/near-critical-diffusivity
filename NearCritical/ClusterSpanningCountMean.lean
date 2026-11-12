module

public import NearCritical.ClusterSpanningWindow
public import NearCritical.ClusterCountConcentration

/-! Actual first mean for prop.num_spanning_new Steps1-2. The window count
uses the same graph/component predicate as the decoupling argument. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical

def spanningWindowProperty {d : ℕ} {φ : Type*}
    (faces : φ → Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a b : ℝ)
    (G : SimpleGraph (Vertex d)) (C : Finset (Vertex d)) : Prop :=
  P G C ∧ (∀ i, (C ∩ faces i).Nonempty) ∧ a < (C.card:ℝ) ∧ (C.card:ℝ) < b

/-- Exact actual window count mean, not a mean estimate supplied as input. -/
theorem spanningWindow_count_mean_eq {d : ℕ} {φ : Type*} (p : unitInterval)
    (Q Z : Finset (Vertex d)) (hZ : Z ⊆ Q) (faces : φ → Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a b : ℝ) :
    rootedPropertyCountMean p Q Z (spanningWindowProperty faces P a b) =
      ∑ x ∈ Z, (percolation d p).real (spanningPropertyWindowEvent Q faces x P a b) := by
  rw [rootedPropertyCountMean, integral_rootedPropertyCount p Q Z hZ]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [spanningPropertyWindowEvent_eq_rooted]
  rfl

/-- The strict upper window supplies the raw selected-component cap needed
by the actual variance and distinct-count theorems. -/
lemma spanningWindow_selected_volume_le {d : ℕ} {φ : Type*}
    (Q : Finset (Vertex d)) (faces : φ → Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a b : ℝ)
    (ω : Configuration d) (x : Vertex d)
    (h : rootedClusterProperty Q x (spanningWindowProperty faces P a b) ω) :
    ((finiteBoxCluster ω Q x).card:ℝ) ≤ b := h.2.2.2.le

/-- Actual Step1/Step2 mean sandwich with ONE upper cutoff chosen before all
boxes, root sets, labelled faces and component properties. Lower-volume and
spanning inputs are per-root actual probabilities; no mean is assumed. -/
theorem critical_spanningWindow_count_mean {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) (δ c Cs : ℝ) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Q Z : Finset (Vertex d)), Q ⊆ centeredBox d N →
      Z ⊆ Q → ∀ (φ : Type*) (faces : φ → Finset (Vertex d))
        (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a : ℝ),
      (∀ x ∈ Z, c/(N+1:ℝ)^2 ≤
        (percolation d (criticalPoint d)).real (finiteRootSpanningEvent Q faces x)) →
      (∀ x ∈ Z, (percolation d (criticalPoint d)).real (finiteRootSpanningEvent Q faces x) ≤
        Cs/(N+1:ℝ)^2) →
      (∀ x ∈ Z, δ*(percolation d (criticalPoint d)).real (finiteRootSpanningEvent Q faces x) ≤
        (percolation d (criticalPoint d)).real
          ({ω | rootedClusterProperty Q x P ω} ∩ finiteRootSpanningEvent Q faces x)) →
      (∀ x ∈ Z, (percolation d (criticalPoint d)).real
        ({ω | ((finiteBoxCluster ω Q x).card:ℝ) ≤ a} ∩ finiteRootSpanningEvent Q faces x) ≤
          (δ/4)*(percolation d (criticalPoint d)).real (finiteRootSpanningEvent Q faces x)) →
      ((δ*c/2)/(N+1:ℝ)^2)*(Z.card:ℝ) ≤
        rootedPropertyCountMean (criticalPoint d) Q Z
          (spanningWindowProperty faces P a (C*(N+1:ℝ)^4)) ∧
      rootedPropertyCountMean (criticalPoint d) Q Z
          (spanningWindowProperty faces P a (C*(N+1:ℝ)^4)) ≤
        (Cs/(N+1:ℝ)^2)*(Z.card:ℝ) := by
  obtain ⟨C,hC,hwindow⟩ := critical_spanningPropertyWindow_lower hd hA δ c hδ hc
  refine ⟨C,hC,?_⟩
  intro N Q Z hQ hZ φ faces P a hspanlo hspanhi hproperty hlow
  simp_rw [spanningWindow_count_mean_eq (criticalPoint d) Q Z hZ faces P a (C*(N+1:ℝ)^4)]
  constructor
  · calc
      _ = ∑ _x ∈ Z, (δ/2)*(c/(N+1:ℝ)^2) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ x ∈ Z, (percolation d (criticalPoint d)).real
          (spanningPropertyWindowEvent Q faces x P a (C*(N+1:ℝ)^4)) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (mul_le_mul_of_nonneg_left (hspanlo x hx) (by positivity : 0 ≤ δ/2)).trans
          (hwindow N Q hQ x (hZ hx) φ faces P a (hspanlo x hx) (hproperty x hx) (hlow x hx))
  · calc
      _ ≤ ∑ x ∈ Z, Cs/(N+1:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro x hx
        have hs : spanningPropertyWindowEvent Q faces x P a (C*(N+1:ℝ)^4) ⊆
            finiteRootSpanningEvent Q faces x := fun _ h => h.2.1
        exact (measureReal_mono hs).trans (hspanhi x hx)
      _ = _ := by simp [mul_comm]

end NearCritical
