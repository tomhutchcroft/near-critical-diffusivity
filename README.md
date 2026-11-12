# Near-critical percolation in high dimensions: Lean formalization

A Lean 4 / Mathlib formalization of the main theorems of

> Chenlin Gu, Tom Hutchcroft, Xiaoran Li, *Diffusivity and metric exponents for
> slightly supercritical percolation in high dimensions*.

## Status

The three main theorems are proved **modulo results the paper cites from the
literature**. Each cited result is an explicit hypothesis of the Lean statement
(never an `axiom`), and [`CITED-INPUTS.md`](CITED-INPUTS.md) lists every one
with the reference it stands for. None of the cited results is formalized
here, so the theorems are not unconditional.

There is no `sorry` and no `axiom` declaration in the library; the main
theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

| Paper | Lean statement | File |
|---|---|---|
| Theorem (diffusivity), `sigma^2(p) ≍ (p - p_c)^2` | `NearCritical.diffusivity_theorem` | `NearCritical/MainDiffusivity.lean` |
| Theorem (time constant), `mu(p) ≍ (p - p_c)^{-1/2}` | `NearCritical.time_constant_from_inputs` | `NearCritical/MainResults.lean` |
| Theorem (slab critical points), both `≍ n^{-2}` | `NearCritical.slab_theorem` | `NearCritical/MainDiffusivity.lean` |

All statements are for dimension `d ≥ 9`.

## Build

Lean and Mathlib are pinned to v4.35.0 (`lean-toolchain`, `lake-manifest.json`).

```sh
lake exe cache get
lake build
lake env lean MainAxioms.lean
```

`lake build` compiles the library including the main theorems. The last
command prints the axioms each main theorem depends on. A full build of this
library takes several hours.

## Layout

- `NearCritical/` — the formalization. `NearCritical.lean` and
  `NearCritical/MainDiffusivity.lean` are the roots of the default build.
- `Percolation/`, `OAI/`, `LeanMachineLearning/`, `Essakine2026Tight/`,
  `LatticeProb/` — third-party Lean code used by the formalization, with
  provenance and licences under `third_party/` (all Apache-2.0).
- `unbuilt/` — draft files that are not part of the library and have not been
  compiled.

About 120 files in `NearCritical/` are not needed by the main theorems
(earlier routes and supporting material); they are kept for reference.
