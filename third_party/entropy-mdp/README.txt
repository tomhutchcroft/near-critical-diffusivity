Selected source from https://github.com/RemyDegenne/entropy-mdp
Pinned commit611f5528b4d64035dac74f92da9eaa7831150180.
Fourteen unmodified files, original Apache LICENSE/copyright headers retained.
Original hashes in manifest.json. Upstream Lean4.34.0-rc2; project Lean4.35.0.
No local target/axiom verification yet; do not count these as accepted proofs.

Selected: Bernoulli KL calculus/data processing/Pinsker; KL-Bernstein and
variance transport; bounded/unbounded stopped-prefix KL chain rules plus
finite-prefix/stopping-time dependencies. MDP-specific algorithms/results
were excluded. The exact LML extension dependency is pinned to
dde3322b0a3978367029a100be43446ac8d04053 from upstream-lake-manifest.json;
nine files are separately vendored with their license under third_party/lml-kl.
No upstream unpinned main dependency is added to the project lake manifest.

Relevance: source FiniteHalfSpaceEntropicInput needs an exploration KL budget
under the LOWER parameter and a sqrt(max event probability) factor. Imported
stopped-prefix divergence and KL-Bernstein supply reusable machinery for those
steps. The candidate ExternalEntropyComparison gives a refined event bound
from an actual KL budget. It does not construct the percolation exploration,
prove fresh-query conditional laws, identify event probabilities, or derive
the expected queried-edge count from finiteHalfSpaceClusterSum.
