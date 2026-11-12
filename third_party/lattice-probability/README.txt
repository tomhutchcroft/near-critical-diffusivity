Imported from https://github.com/nitromannitol/Lattice-Probability
Commit: 9d44b4d4670df393bb86ac5a4e042f215001cddf
Apache-2.0 LICENSE retained verbatim. Sources retain original headers/namespaces.
manifest.json records exact original source hashes; files are unmodified.
Upstream Lean4.32.0; project Lean4.35.0. Compilation/axiom audit PENDING.

Five-file closure: maximal ergodic theorem, Birkhoff, Kingman, lattice Site,
and Akcoglu-Krengel mean convergence. The selected final theorem proves
existence of the mean limit along [0,n)^d for stationary measurable box
fields with 0<=f(A,w)<=C*card(A) and actual binary box-split subadditivity.
This can support source lem.basic / the named triadic full-energy mean-limit
input. It does not supply those hypotheses for NearCritical's actual full
Dirichlet statistic. Half-open versus centered odd cubes, energy normalization,
issued edges, and cofinal/triadic limit correspondence need explicit bridges.
It is only the multidimensional MEAN half; no multidimensional almost-sure
homogenization or Einstein/diffusivity relation is imported as established.
Kingman additionally supplies one-parameter almost-sure subadditive convergence.

Candidate project wrapper: NearCritical.ExternalSubadditiveErgodic.
Proposed native registration, for root coordinator review (NOT applied):
[[lean_lib]]
name = "LatticeProb"
roots = ["LatticeProb.Prob.AkcogluKrengel"]
globs = ["LatticeProb.+"]
Root aggregator/coverage and lakefile were not modified by this batch.

Additional batch:13 verbatim AkcogluKrengelAE files, now18 library files total.
round4-manifest.json records the additional hashes and complete dependency
order. Candidate wrapper NearCritical.ExternalSubadditiveAELimit preserves
additive shift composition and gives a potentially RANDOM almost-sure limit.
It adds no ergodicity or physical conductivity/diffusivity identification.
All new targets and2 final/wrapper axiom reports remain UNVERIFIED.
The separate mean file has a stale remark about AE support; the pinned library
does contain this AE development. No source text was changed to hide that.

Round6: three byte-exact fresh-coordinate exploration dependencies;21 sources total.
New actual-model wrapper NearCritical.ExternalFreshExploration retains all
IsExploration hypotheses. Native/axiom checks NOT RUN; round6 manifest records hashes.

Round7: byte-exact ExplorationCond companion;22 sources total. Stronger
ReadsOnlyRevealed supplies history-measurable indices; conditional fresh-read
mean wrapper in ExternalExplorationConditional remains locally UNCOMPILED.
