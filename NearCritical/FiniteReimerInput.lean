module
public import NearCritical.CylinderBK

/-! The cited finite Reimer inequality as an explicit literature input.
Reimer, Proof of the van den Berg–Kesten conjecture (2000), supplies the
arbitrary-event BKR inequality. This module does not prove that theorem;
it proves its transfer to the project's actual lattice product law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- Cited finite Bernoulli BKR theorem, with arbitrary (possibly nonmonotone)
events. This explicit external input is distinct from the proved increasing BK. -/
def FiniteBernoulliBKRInput : Prop :=
  ∀ (E : Type) [Fintype E] (p : unitInterval) (A B : Set (E → Bool)),
    BK.eventProbability (p : ℝ) (BK.occurrenceEvent A B) ≤
      BK.eventProbability (p : ℝ) A * BK.eventProbability (p : ℝ) B

/-- The finite literature input gives standard full-configuration disjoint
occurrence for arbitrary cylinder events under actual lattice percolation. -/
theorem percolation_cylinder_reimer (reimer : FiniteBernoulliBKRInput)
    (d : ℕ) (p : unitInterval) (s : Finset (Bond d))
    (A B : Set ((e : s) → Bool)) :
    (percolation d p).real
        {ω | DisjointOccurrence ((s.restrict) ⁻¹' A) ((s.restrict) ⁻¹' B) ω} ≤
      (percolation d p).real ((s.restrict) ⁻¹' A) *
      (percolation d p).real ((s.restrict) ⁻¹' B) := by
  have heq : {ω | DisjointOccurrence ((s.restrict) ⁻¹' A) ((s.restrict) ⁻¹' B) ω} =
      (s.restrict) ⁻¹' BK.occurrenceEvent A B := by
    ext ω
    exact (disjointOccurrence_restrict_iff s A B ω).symm
  rw [heq]
  have h := reimer s p A B
  rw [eventProbability_cylinder d p s, eventProbability_cylinder d p s,
    eventProbability_cylinder d p s] at h
  exact h

/-- A finite-coordinate invariance proof is enough to apply the cited Reimer
input directly to full lattice events, without a monotonicity hypothesis. -/
theorem percolation_reimer_of_finite_locality (reimer : FiniteBernoulliBKRInput)
    (d : ℕ) (p : unitInterval) (s : Finset (Bond d))
    (A B : Set (Configuration d))
    (hA : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ A ↔ θ ∈ A))
    (hB : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ B ↔ θ ∈ B)) :
    (percolation d p).real {ω | DisjointOccurrence A B ω} ≤
      (percolation d p).real A * (percolation d p).real B := by
  let A₀ : Set ((b : s) → Bool) := {η | extendConfiguration s (fun _ => false) η ∈ A}
  let B₀ : Set ((b : s) → Bool) := {η | extendConfiguration s (fun _ => false) η ∈ B}
  have hAe : A = (s.restrict) ⁻¹' A₀ := by
    ext ω
    apply hA ω (extendConfiguration s (fun _ => false) (s.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  have hBe : B = (s.restrict) ⁻¹' B₀ := by
    ext ω
    apply hB ω (extendConfiguration s (fun _ => false) (s.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  rw [hAe,hBe]
  exact percolation_cylinder_reimer reimer d p s A₀ B₀

end NearCritical
