import NearCritical.ExternalUniqueness
import NearCritical.ExternalLawBridge

/-!
Almost-sure uniqueness of the infinite cluster for the project's own
percolation law, unconditionally: the imported Burton--Keane theorem
(`ExternalUniqueness`) transferred through the model-law bridge
(`ExternalLawBridge.percolation_map_edgeSetConfig`).

This discharges the named input `AEInfiniteClusterUniqueness d p` of the
chemical-distance and time-constant deductions.

-/

namespace NearCritical.External

/-- **Uniqueness of the infinite cluster** under `NearCritical.percolation d p`,
for every dimension and parameter. -/
theorem aeInfiniteClusterUniqueness (d : ℕ) (p : unitInterval) :
    NearCritical.AEInfiniteClusterUniqueness d p :=
  aeInfiniteClusterUniqueness_of_edgeSet_law d p (percolation_map_edgeSetConfig d p)

end NearCritical.External
