OpenAI math finite-search source subset, Apache-2.0 (LICENSE retained).
Pinned commit4eaee87548250b2682affda7d05d947c05554bae; original source hashes/manifests retained unchanged.
Current eight OAI working copies and ExternalFiniteLeafLaw now have an UNVERIFIED
import/module-header-only local port. Exact pre-port copies, source/proof-text
hashes and patch are in import-hygiene/. Proof/declaration text is preserved;
module/public API, Native and axiom checks after this port have NOT RUN.
Original LICENSE and earlier original archives remain unchanged.

Historical import-round notes below describe pre-port byte-exact sources,
which are archived in import-hygiene/baseline/, not the current working headers.
Model and Exploration.SearchTree provide labelled-bond graphs, finite binary
query trees, lazyDFS compilation, validity and no-repeat proofs. This subset
does not include target-search correctness, exhaustive-search or score bounds.
Local actual-bond specialization is ExternalFiniteSearch; no graph-law or
halfspace-event identification is claimed. Native checks NOT RUN.

Round10 adds Exploration.State byte-exact: exact frontier exposure with
reachability invariants, adequate finite-edge fuel and queried-edge incidence.
Three files total. ExternalExactExposure finite actual-bond wrapper candidate
retains labelled restricted-graph scope; native/axiom checks NOT RUN.

Round15 adds Divergence/MulLogDivScaled/QueryTree minimal entropy closure3.
Six byte-exact OpenAI source files total. Finite leaf entropy identity and
quadratic charge bounds retained; local SearchTree transcript conversion in
ExternalFiniteTranscript remains UNCOMPILED. Actual leaf-law/KL bridge open.

Round16: Density and PushMass exact sources added; adapted BitWeight in
NearCritical/ExternalFiniteLeafLaw with only dependency reduction and one
verbatim Delta helper. Original .lean.txt sources, patch and hashes retained.
All theorem proof bodies unchanged. Native and actual-law measure bridge pending.
