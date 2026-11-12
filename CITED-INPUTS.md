# Cited inputs of the main theorems

The three main theorems (`slab_theorem` and `diffusivity_theorem` in
`NearCritical/MainDiffusivity.lean`, `time_constant_from_inputs` in
`NearCritical/MainResults.lean`) are proved from the
premises listed here and from nothing else: the axiom audit shows only
`propext`, `Classical.choice` and `Quot.sound`, and there is no `sorry`.
Each premise below is an explicit hypothesis of the Lean statement (a `Prop`
argument, never an `axiom`). It stands for a result that the paper itself cites
from the literature. None of these cited results is formalized here, so the
theorems are **not unconditional**.

All statements are for dimension `d = e + 7` with `2 ≤ e`, i.e. `d ≥ 9`.

Notation: `p_c = criticalPoint d`; `psi_p(H_n) = halfSpacePioneerMass p i n`
is the expected number of height-`n` vertices connected to a boundary vertex
inside the half-space.

## Used by all three theorems

| Lean premise | Statement | Reference given in the paper |
|---|---|---|
| `TwoPointAsymptotics d` | Assumption (A): `tau_{p_c}(0,x) ~ A |x|^{2-d}` | the paper's standing assumption (A) |
| `PanisHalfSpaceTwoPointUpper d C` | half-space two-point upper bound at `p_c` | lem.halfspace_twopoint; Panis 2026, Thm 1.4 |
| `HalfSpaceCriticalArmInput i Ar` (all axes) | `P_{p_c}[0 <-> height n in H] ≤ Ar / n^3` | eq.onearm_half; CH20 Prop. 3.1 / van Engelenburg et al., Thm 1.2 |
| `hpioneerLower` | `c ≤ psi_{p_c}(H_n)` for `n ≥ 1` | eq.expansion_2; Hutchcroft 2023, Thm 2.3 |
| pioneer upper bound (see note 3) | `psi_{p_c}(H_n) ≤ C` for `n ≥ 1` | eq.expansion_2 / eq.expansion_12 at `p_c` |
| `RestrictedRectangleLowerInput d` | restricted two-point lower bound in fixed-shape rectangles | lem.box_twopoint; Chatterjee–Hanson 2020 (CH20), Thm 12 |
| `FiniteBernoulliBKRInput` | the van den Berg–Kesten–Reimer inequality for arbitrary events on finitely many bits | Reimer's theorem |
| `Section7.HalfSpaceLongPathMoment d K` | bounded expected length of the longest half-space path | CHS23 (105); main.tex 1514–1517 |
| `ClusterSizeInput d α A c` | small-volume bound for clusters conditioned on an arm, for `λ` up to a cap | eq.cluster_size (see note 1) |
| `OrdinaryArmWindowInput d Carm` | one-arm bound `≤ C / n^2` for `p ≤ p_c + n^{-2}` | eq.onearm_super |

## Additional premises of `slab_theorem` (thm.slab)

| Lean premise | Statement | Reference |
|---|---|---|
| `Grimmett1999PlanarMixedInput` | planar mixed site–bond percolation with high density percolates | Grimmett 1999 |
| `WeightedPositiveHeightPioneerDecay p_c j Cdec cdec` (all axes) | `p psi_p(H_m)` bounded at `p_c`, `m ≥ 1` | eq.expansion_12; Hutchcroft 2023, Thm 2.3 |

## Additional premises of `time_constant_from_inputs` (thm.time_constant)

| Lean premise | Statement | Reference |
|---|---|---|
| `RayExponentialConnectionBound` (`hHMS`) | subcritical exponential decay along a ray, rate `c sqrt(p_c - q)` | lem.chem.HMS; Hutchcroft 2023, Thm 1.1 |
| `AEConnectedChemicalLimit` (`hlimit`) | existence of the chemical time constant `M p` | eq.chem.timeconstant; Garet–Marchand 2004, Cor. 3.3 |
| `hunit`, `hreflect`, `UniformChemicalLowerTail` (`hGM`) | the chemical norm `N p`, its lattice symmetries, and its large-deviation lower tail | eq.chem.GM07; Garet–Marchand 2007 |

## Additional premises of `diffusivity_theorem` (thm.main)

| Lean premise | Statement | Reference |
|---|---|---|
| `HalfSpacePioneerExponentialInput j BX bX` (all axes) | `p psi_p(H_m) ≤ B exp(-b sqrt(p_c - p) m)` for `p_c/2 ≤ p ≤ p_c` | eq.expansion_12; Hutchcroft 2023, Thm 2.3 |
| `UpperPowerBound p_c (densityReal d) 1` (`hθ`) | `theta(p) ≤ C (p - p_c)` | mean-field density upper bound (the lower bound is proved) |
| `VariableSpeedSampleEinsteinInput d` | quenched invariance principle for the variable-speed walk on the infinite cluster, with limiting variance given by the Einstein relation | lem.basic and the cited invariance principle |

## Notes

1. `ClusterSizeInput` restricts `λ` to a range `λ ≤ λ₀` supplied with the
   citation. The source display eq.cluster_size is stated for all large `λ`,
   where it cannot hold; only small `λ` is used.
2. The older statement `variableSpeedSamplePath_diffusivity_two_sided_from_inputs`
   also takes `ExponentialClockPoissonInput` (exponential waiting times give
   Poisson counts). That is proved in
   `NearCritical/VariableSpeedWalkPoissonClock.lean`, and the final theorem in
   `MainDiffusivity.lean` supplies it.
3. The pioneer upper bound is a separate premise (`hpioneerUpper`) only in
   `time_constant_from_inputs`. In `slab_theorem` and `diffusivity_theorem` it
   is derived from the eq.expansion_12 premise listed for that theorem, taken
   at `p = p_c`. The earlier statements `slab_theorem_from_inputs` and
   `variableSpeedSamplePath_diffusivity_two_sided` take both.

## Proved here rather than cited

These were premises at earlier stages and are now theorems: uniqueness of the
infinite cluster, `0 < p_c`, the mean-field lower bound `theta(p) ≥ p - p_c`,
the tree-graph inequality, both nearest-neighbour slab moments (lem.Nn_moments),
the depth-zero pioneer bound, and the split-crossing estimate (proved directly
on the lattice, with no scaling limit).

## What the diffusivity theorem says

thm.main is proved in its random-walk form: for every `p > p_c` there is `v`
such that the rescaled variable-speed walk on the infinite cluster has Gaussian
one-time marginals of variance `v` in every coordinate, and
`c (p - p_c)^2 ≤ v ≤ C (p - p_c)^2`. The Gaussian limit and its identification
with the Einstein-relation coefficient are the cited premise
`VariableSpeedSampleEinsteinInput`; the two-sided bound on that coefficient is
what is proved.
