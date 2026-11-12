Source: https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation
Pinned commit: 795efb86f191735c5481675763537cfb4ff37e55
License: Apache-2.0; original LICENSE and NOTICE retained alongside this file.

Selected import: Percolation.Literature.SharpnessDCTProofs and its 17 local
transitive imports, copied into the original Percolation/ module namespace.
manifest.json records SHA256 hashes of the original source files.
Upstream Lean: 4.32.0. Project Lean/Mathlib: 4.35.0.

Build and audit from the project root:
  sh analysis/external-code-build.sh
The script compiles in dependency order against existing local Mathlib artifacts
and does not change Lake dependencies, global imports or other workers' modules.

Public entry point: NearCritical.ExternalPercolation
Result: NearCritical.External.subcritical_exponential_decay.
This retains upstream bondPercolation (sets of Sym2 edges), siteToBoundary
(inner boundary of a centered cube), and criticalProb. It does NOT yet identify
these with NearCritical's positive-coordinate bond-indexed product law,
ordinaryArmEvent, or criticalPoint. A measure-preserving encoding and
probability-law/arm/critical-point correspondence are required before using it to
discharge any existing standard-input field. No high-dimensional exponent,
uniform near-critical exponential rate, chemical shape theorem, homogenization
or main paper theorem is supplied by this import.

The wrapper also contains deterministic graph/connection/infinite-cluster
identities and encoding measurability; the wrapper target has passed and
its actual-import axiom audit and native build are deferred under the
coordinator's verified host-memory-pressure guidance. Neither is claimed passed. The unresolved critical-point bridge is substantive:
NearCritical.criticalPoint is an infimum in unitInterval, while upstream
criticalProb is a real infimum with an explicit union with {1}.

Additional source batch: nine files for Burton-Keane uniqueness and finite
surgery multiplicity, now27 Percolation files total. round2-manifest.json
records exact new source hashes and closure. New sources/ExternalUniqueness
are UNCOMPILED; original18+ExternalPercolation direct targets passed.
The model pushforward still needs proof; see round2-notes and prepared6audit.
