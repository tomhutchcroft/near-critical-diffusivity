module

public import NearCritical.LatticeFullConductivity
public import NearCritical.DirichletSubadditivity

/-! The annealed finite-volume coordinate form of source lem.subadditive.
No infinite-volume limit or homogenization theorem is inferred. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

theorem annealedFull_rectangle_subadditivity {d : ℕ} {I : Type*}
    (s : Finset I) (lo hi : I → Vertex d)
    (hvalid : ∀ j ∈ s, ∀ k, lo j k ≤ hi j k)
    (hd : (s : Set I).PairwiseDisjoint (fun j => latticeRectangle (lo j) (hi j)))
    (p : unitInterval) (i : Fin d) :
    annealedFull (s.biUnion (fun j => latticeRectangle (lo j) (hi j))) i (p : ℝ) ≤
      ∑ j ∈ s, ((latticeRectangle (lo j) (hi j)).card : ℝ) /
        (s.biUnion (fun j => latticeRectangle (lo j) (hi j))).card *
        annealedFull (latticeRectangle (lo j) (hi j)) i (p : ℝ) := by
  classical
  let U := fun j => latticeRectangle (lo j) (hi j)
  let T := s.biUnion U
  let c := fun j => ((U j).card : ℝ) / T.card
  have hint : ∀ j ∈ s, Integrable
      (fun ω => c j * fullConductivity (U j) i ω) (percolation d p) :=
    fun j _ => (integrable_fullConductivity (U j) i p).const_mul (c j)
  change annealedFull T i (p : ℝ) ≤ ∑ j ∈ s, c j * annealedFull (U j) i (p : ℝ)
  rw [annealedFull_eq_integral]
  calc
    _ ≤ ∫ ω, ∑ j ∈ s, c j * fullConductivity (U j) i ω ∂percolation d p :=
      integral_mono (integrable_fullConductivity T i p)
        (integrable_finsetSum s hint)
        (fun ω => fullConductivity_rectangle_subadditivity s lo hi hvalid hd ω i)
    _ = ∑ j ∈ s, c j * annealedFull (U j) i (p : ℝ) := by
      rw [integral_finsetSum s hint]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, ← annealedFull_eq_integral]

end NearCritical
