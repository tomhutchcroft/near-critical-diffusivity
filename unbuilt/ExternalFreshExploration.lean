module

public import NearCritical.Bernoulli
public import LatticeProb.Prob.Exploration

/-!
Fresh predictable bond reads in the actual project model. Upstream source:
nitromannitol/Lattice-Probability at 9d44b4d4670df393bb86ac5a4e042f215001cddf.
License, notice and original hashes: third_party/lattice-probability/.

This theorem assumes an infinite nonrepeating exploration. It does not construct
a cluster exploration, its stopping rule, or the bound on queried bonds.
The wrapper and three new upstream dependencies await local native/axiom checks.
-/
@[expose] public section
namespace NearCritical.External
open MeasureTheory ProbabilityTheory

/-- A measurable predictable exploration that never repeats a bond reads IID
Bernoulli values under the project's actual bond-indexed percolation law. -/
theorem fresh_bond_reads_law {d : ℕ} (p : unitInterval)
    (idx : ℕ → Configuration d → Bond d)
    (hidx : LatticeProb.IsExploration (X := fun _ : Bond d => Bool) idx) :
    (percolation d p).map (fun ω n => ω (idx n ω)) =
      Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p) := by
  exact LatticeProb.map_revealed_of_const hidx

end NearCritical.External
