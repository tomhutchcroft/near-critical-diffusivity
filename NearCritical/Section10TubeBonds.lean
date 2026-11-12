module

public import NearCritical.Section10TubeGeometry
public import NearCritical.BulkDomain
public import NearCritical.NestCubeWeights

/-! Section10 lem.skl.independent: actual finite tube-coordinate blocks.
The source random explored-cluster conditioning must still be identified. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
open MeasureTheory

/-- Literal E(T) within a finite ambient lattice bond set: both endpoints lie
in the exact source tube. This is not the larger issued-edge convention E+(T). -/
def coarseTubeBondMask {d : ℕ} (ell : ℝ) (ambient : Finset (Bond d))
    (a : Fin d → ℤ) (i : Fin d) : Finset (Bond d) :=
  ambient.filter (fun e => e.1 ∈ coarseTubeVertices ell a i ∧
    bondTip e ∈ coarseTubeVertices ell a i)

theorem mem_coarseTubeBondMask {d : ℕ} (ell : ℝ) (ambient : Finset (Bond d))
    (a : Fin d → ℤ) (i : Fin d) (e : Bond d) :
    e ∈ coarseTubeBondMask ell ambient a i ↔ e ∈ ambient ∧
      e.1 ∈ coarseTubeVertices ell a i ∧ bondTip e ∈ coarseTubeVertices ell a i := by
  simp only [coarseTubeBondMask,Finset.mem_filter]

/-- Actual internal tube bond sets inherit the proved vertex separation. -/
theorem coarseTubeBondMask_disjoint {d : ℕ} {ell : ℝ} (hell : 0 < ell)
    (ambient : Finset (Bond d)) (a b : Fin d → ℤ) (i j : Fin d)
    (hne : (a,i) ≠ (b,j)) :
    Disjoint (coarseTubeBondMask ell ambient a i) (coarseTubeBondMask ell ambient b j) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Set.disjoint_left.mp (coarseTubeVertices_disjoint hell a b i j hne)
    ((mem_coarseTubeBondMask ell ambient a i e).mp he).2.1
    ((mem_coarseTubeBondMask ell ambient b j e).mp hf).2.1

/-- Fresh coordinates after deleting a fixed set of revealed bonds. -/
def freshCoarseTubeBonds {d : ℕ} (ell : ℝ) (ambient revealed : Finset (Bond d))
    (a : Fin d → ℤ) (i : Fin d) : Finset (Bond d) :=
  coarseTubeBondMask ell ambient a i \ revealed

/-- Deleting revealed coordinates cannot create interactions between tubes. -/
theorem freshCoarseTubeBonds_disjoint {d : ℕ} {ell : ℝ} (hell : 0 < ell)
    (ambient revealed : Finset (Bond d)) (a b : Fin d → ℤ) (i j : Fin d)
    (hne : (a,i) ≠ (b,j)) :
    Disjoint (freshCoarseTubeBonds ell ambient revealed a i)
      (freshCoarseTubeBonds ell ambient revealed b j) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp (coarseTubeBondMask_disjoint hell ambient a b i j hne)
    (Finset.mem_sdiff.mp he).1 (Finset.mem_sdiff.mp hf).1

/-- The retained coordinates are physically disjoint from the reveal mask. -/
theorem revealed_disjoint_freshCoarseTubeBonds {d : ℕ} (ell : ℝ)
    (ambient revealed : Finset (Bond d)) (a : Fin d → ℤ) (i : Fin d) :
    Disjoint revealed (freshCoarseTubeBonds ell ambient revealed a i) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact (Finset.mem_sdiff.mp hf).2 he

/-- Full finite-observable product factorization under the ACTUAL Bernoulli
law, on the literal disjoint fresh tube masks. Revealed is fixed here; random
exploration atoms require an additional locality/conditional-law argument. -/
theorem percolation_freshCoarseTube_product {d : ℕ} (p : unitInterval)
    {ell : ℝ} (hell : 0 < ell) (ambient revealed : Finset (Bond d))
    (s : Finset ((Fin d → ℤ) × Fin d))
    (f : ∀ e : (Fin d → ℤ) × Fin d, (freshCoarseTubeBonds ell ambient revealed e.1 e.2 → Bool) → ℝ) :
    (∫ ω : Configuration d, ∏ e ∈ s,
      f e ((freshCoarseTubeBonds ell ambient revealed e.1 e.2).restrict ω) ∂percolation d p) =
      ∏ e ∈ s, ∫ ω : Configuration d,
        f e ((freshCoarseTubeBonds ell ambient revealed e.1 e.2).restrict ω) ∂percolation d p := by
  apply percolation_disjoint_block_product p s
    (fun e => freshCoarseTubeBonds ell ambient revealed e.1 e.2) _ f
  intro e _ f _ hef
  exact freshCoarseTubeBonds_disjoint hell ambient revealed e.1 f.1 e.2 f.2 hef

end NearCritical.Section10
