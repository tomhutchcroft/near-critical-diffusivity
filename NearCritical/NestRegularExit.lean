module

public import NearCritical.NestRegularBoundary
public import NearCritical.NestAuxiliaryExit

/-! Actual source regular boundary as the selected terminal exit set.
The ERE bounds are computed from the entire heart-touching cluster union. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Finite two-sample history representation of the actual regular boundary.
The critical bits are the AND of the open and independent retention bits. -/
def regularExitChoice {d : ℕ} (U Q heart excluded boundary face : Finset (Vertex d))
    (root : Vertex d) (r : ℕ) (δ : ℝ)
    (η : (internalBondSet U → Bool) × (internalBondSet U → Bool)) : Finset (Vertex d) :=
  sourceRegularBoundary (reconstructInterior U (thinConfiguration η))
    Q heart excluded boundary face root r δ

lemma regularExitChoice_eq_actual {d : ℕ}
    (U Q heart excluded boundary face : Finset (Vertex d)) (hQU : Q ⊆ U)
    (root : Vertex d) (r : ℕ) (δ : ℝ) (z : Configuration d × Configuration d) :
    regularExitChoice U Q heart excluded boundary face root r δ
      ((internalBondSet U).restrict z.1,(internalBondSet U).restrict z.2) =
      sourceRegularBoundary (thinConfiguration z) Q heart excluded boundary face root r δ := by
  exact (sourceRegularBoundary_reconstruct U Q heart excluded boundary face hQU
    (thinConfiguration z) root r δ).symm

/-- Literal regular-boundary exit mean, allowing the representative's root to
be selected from both revealed samples. Nonemptiness is the remaining source
regular-boundary lower-size obligation, not an input success-probability law. -/
theorem percolation_regular_exit_weighted_mean {d : ℕ} (p q : unitInterval)
    (hp : 0 < (p:ℝ)) (i : Fin d) (U Q heart excluded boundary face : Finset (Vertex d))
    (hQU : Q ⊆ U) {hi : ℤ} (hU : ∀ x ∈ U, x i ≤ hi) (hface : ∀ x ∈ face, x i = hi)
    (root : ((internalBondSet U → Bool) × (internalBondSet U → Bool)) → Vertex d)
    (r : ℕ) (δ : ℝ) (H : (internalBondSet U → Bool) × (internalBondSet U → Bool) → ℝ)
    (hlive : ∀ η, H η ≠ 0 →
      (regularExitChoice U Q heart excluded boundary face (root η) r δ η).Nonempty) :
    let history := fun z : Configuration d × Configuration d =>
      ((internalBondSet U).restrict z.1,(internalBondSet U).restrict z.2)
    let picked := fun z => sourceRegularBoundary (thinConfiguration z)
      Q heart excluded boundary face (root (history z)) r δ
    (∫ z, H (history z) *
      (if ∃ x ∈ picked z, z.1 (x,i) = true then (1-(1-(p:ℝ))^(picked z).card)⁻¹ else 0)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z, H (history z) ∂((percolation d p).prod (percolation d q)) := by
  dsimp only
  have h := percolation_coupled_exit_weighted_mean p q hp i U hU
    (internalBondSet U) (internalBondSet U) (fun _ he => he)
    (fun η => regularExitChoice U Q heart excluded boundary face (root η) r δ η)
    (fun η x hx => hface x (sourceRegularBoundary_subset_face _ _ _ _ _ _ _ _ _ hx)) H hlive
  simpa only [regularExitChoice_eq_actual U Q heart excluded boundary face hQU] using h

/-- The same concrete regular-boundary selection with arbitrary finite
history-dependent auxiliary sampling and outcome-dependent preceding weights.
This is the terminal factor removal needed for the source whole-chain weight. -/
theorem percolation_regular_auxiliary_exit_sum {d : ℕ} {A : Type*} [Fintype A]
    (p q : unitInterval) (hp : 0 < (p:ℝ)) (i : Fin d)
    (U Q heart excluded boundary face : Finset (Vertex d)) (hQU : Q ⊆ U)
    {hi : ℤ} (hU : ∀ x ∈ U, x i ≤ hi) (hface : ∀ x ∈ face, x i = hi)
    (root : ((internalBondSet U → Bool) × (internalBondSet U → Bool)) → A → Vertex d)
    (r : ℕ) (δ : ℝ)
    (K H : ((internalBondSet U → Bool) × (internalBondSet U → Bool)) → A → ℝ)
    (hlive : ∀ η a, K η a ≠ 0 → H η a ≠ 0 →
      (regularExitChoice U Q heart excluded boundary face (root η a) r δ η).Nonempty) :
    let history := fun z : Configuration d × Configuration d =>
      ((internalBondSet U).restrict z.1,(internalBondSet U).restrict z.2)
    let picked := fun z a => sourceRegularBoundary (thinConfiguration z)
      Q heart excluded boundary face (root (history z) a) r δ
    (∫ z, ∑ a, (K (history z) a * H (history z) a) *
      (if ∃ x ∈ picked z a, z.1 (x,i) = true then (1-(1-(p:ℝ))^(picked z a).card)⁻¹ else 0)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z, ∑ a, K (history z) a * H (history z) a
        ∂((percolation d p).prod (percolation d q)) := by
  dsimp only
  have h := percolation_auxiliary_exit_sum p q hp i U hU
    (internalBondSet U) (internalBondSet U) (fun _ he => he)
    (fun η a => regularExitChoice U Q heart excluded boundary face (root η a) r δ η)
    (fun η a x hx => hface x (sourceRegularBoundary_subset_face _ _ _ _ _ _ _ _ _ hx)) K H hlive
  simpa only [regularExitChoice_eq_actual U Q heart excluded boundary face hQU] using h

end NearCritical
