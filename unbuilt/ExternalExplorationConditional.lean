module

public import NearCritical.ExternalFreshExploration
public import LatticeProb.Prob.ExplorationCond

/-!
Conditional fresh-read expectations from Lattice-Probability, pinned at
9d44b4d4670df393bb86ac5a4e042f215001cddf. License/NOTICE and source hashes
are retained under third_party/lattice-probability.

IsExploration.pred alone is weaker than a history-based decision rule.
ReadsOnlyRevealed is retained explicitly in the observed-history theorem.
No cluster-search construction or stopping/cost bound is supplied here.
-/
@[expose] public section
namespace NearCritical.External
open MeasureTheory ProbabilityTheory

/-- The next bond index is measurable with respect to the observed Bool prefix,
provided the algorithm really reads only its revealed history. -/
theorem bond_query_measurable_from_history {d : ℕ}
    (idx : ℕ → Configuration d → Bond d)
    (hreads : LatticeProb.ReadsOnlyRevealed idx) (n : ℕ) :
    Measurable[MeasurableSpace.comap
      (LatticeProb.revealedPrefix idx (fun _ => id) n) inferInstance] (idx n) := by
  exact LatticeProb.measurable_idx_comap_revealedPrefix hreads
    (fun _ => Function.injective_id) n

/-- A function of the next fresh bond value has its Bernoulli mean conditionally
on the observed prefix, under the actual project percolation law. -/
theorem fresh_bond_conditional_mean {d : ℕ} (p : unitInterval)
    (idx : ℕ → Configuration d → Bond d)
    (hidx : LatticeProb.IsExploration (X := fun _ : Bond d => Bool) idx)
    (n : ℕ) {f : Bool → ℝ} (hf : Integrable f (bernoulliMeasure true false p)) :
    (percolation d p)[fun ω => f (ω (idx n ω)) |
      MeasurableSpace.comap (LatticeProb.revealedPrefix idx (fun _ => id) n)
        inferInstance] =ᵐ[percolation d p]
      fun _ => ∫ v, f v ∂bernoulliMeasure true false p := by
  exact LatticeProb.condExp_revealed
    (fun _ : Bond d => bernoulliMeasure true false p) hidx
    (fun _ => measurable_id) (fun _ => Measure.map_id) n hf

end NearCritical.External
