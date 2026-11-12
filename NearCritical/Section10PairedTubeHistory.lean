module

public import NearCritical.Section10PairedReveal
public import NearCritical.Section10TubeBonds

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- On a fixed paired exploration atom, the next tube may be selected
from the recorded history. Its unrevealed coordinates have their original law. -/
theorem paired_history_selected_tube_mean {d : ℕ} (p q : unitInterval)
    (ell : ℝ) (ambient revealed : Finset (Bond d))
    (history : (revealed → Bool) × (revealed → Bool))
    (chooseTube : ((revealed → Bool) × (revealed → Bool)) → (Fin d → ℤ) × Fin d) :
    let tube := chooseTube history
    let T := freshCoarseTubeBonds ell ambient revealed tube.1 tube.2
    let H := fun z : Configuration d × Configuration d =>
      ({history} : Set ((revealed → Bool) × (revealed → Bool))).indicator (fun _ => (1 : ℝ))
        (revealed.restrict z.1, revealed.restrict z.2)
    let μ := (percolation d p).prod (percolation d q)
    ∀ (g : (T → Bool) × (T → Bool) → ℝ), 0 < ∫ z, H z ∂μ →
      (∫ z, H z * g (T.restrict z.1, T.restrict z.2) ∂μ) / (∫ z, H z ∂μ) =
        ∫ z, g (T.restrict z.1, T.restrict z.2) ∂μ := by
  intro tube T H μ g hprob
  exact coupled_past_atom_fresh_pair_mean p q revealed T
    (revealed_disjoint_freshCoarseTubeBonds ell ambient revealed tube.1 tube.2)
    history (fun _ => g) hprob

end NearCritical.Section10
