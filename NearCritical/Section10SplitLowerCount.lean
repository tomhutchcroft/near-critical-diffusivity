module

public import NearCritical.Section10SplitCrossing
public import NearCritical.Section10PropertyUnion

/-! Lower split-face counts on the all-faces crossing event.

* `crossSplit t f pl R x`: `x` is joined, inside the split corridor of the
  face `f` and half `pl`, to the far end at height `N + R`.
* `crossAll t R x`: this holds for all `4d` pairs `(f, pl)`.
* `SplitCrossInput d c`: the CITED-level input, the analogue of
  eq:2d_spanning_cross of the source with the `4d` split faces
  `partial°_{i,±}` (source rmk.num_bd.sub, from the cited super-Brownian
  scaling limit): `P_{p_c}[crossAll t t x] >= c / t^2` for roots `x` in
  `Lambda_{t/16}`. NOT proved here.
* `crossAll_lower_failure`: on `crossAll`, the probability that some split face
  carries fewer than `b` cluster points is at most `4 d * floor(b) * alpha * beta`,
  where `alpha` bounds the one-arm probability to distance `r < R` and `beta`
  bounds `P[C(x)` meets a split face`]`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- Crossing of one split corridor. -/
def crossSplit {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) (R : ℕ) (x : Vertex d) :
    Set (Configuration d) :=
  {ω | ∃ y₀ ∈ splitTarget t f pl R, ∃ w : (openGraph ω).Walk x y₀,
    ∀ z ∈ w.support, z ∈ splitCorridor t f pl R}

/-- Crossing of all `4d` split corridors. -/
def crossAll {d : ℕ} (t R : ℕ) (x : Vertex d) : Set (Configuration d) :=
  {ω | ∀ i : (Fin d × Bool) × Bool, ω ∈ crossSplit t i.1 i.2 R x}

/-- The `4d`-leaf analogue of eq:2d_spanning_cross, at sufficiently
large scales. The split patches can be empty at small lattice scales. -/
def SplitCrossInput (d : ℕ) (c : ℝ) : Prop :=
  ∃ T : ℕ, ∀ (t : ℕ), T ≤ t → ∀ x ∈ centeredBox d ((t - 1) / 32),
    c / (t : ℝ) ^ 2 ≤ (percolation d (criticalPoint d)).real (crossAll t t x)

noncomputable def SplitCrossInput.threshold {d : ℕ} {c : ℝ} (h : SplitCrossInput d c) : ℕ :=
  Classical.choose h

theorem SplitCrossInput.crossing {d : ℕ} {c : ℝ} (h : SplitCrossInput d c)
    (t : ℕ) (ht : h.threshold ≤ t) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) :
    c / (t : ℝ) ^ 2 ≤ (percolation d (criticalPoint d)).real (crossAll t t x) :=
  Classical.choose_spec h t ht x hx

theorem crossAll_lower_failure {d : ℕ} (p : unitInterval) (t : ℕ) (ht : 1 ≤ t) (R : ℕ)
    {x : Vertex d} (hx : x ∈ typicalCube t (0 : Vertex d)) {r : ℝ} (hr : r < (R : ℝ))
    {α β b : ℝ} (hb : 0 ≤ b)
    (hα : ∀ y : Vertex d, (percolation d p).real (extrinsicRadiusArmEvent y r) ≤ α)
    (hβ : ∀ i : (Fin d × Bool) × Bool, (percolation d p).real
      {ω | (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
        typPatch t (0 : Vertex d) i).Nonempty} ≤ β) :
    (percolation d p).real (crossAll t R x ∩ {ω | ¬ ∀ i : (Fin d × Bool) × Bool,
        b ≤ ((finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
          typPatch t (0 : Vertex d) i).card : ℝ)}) ≤
      4 * (d : ℝ) * ((⌊b⌋₊ : ℝ) * α * β) := by
  set μ := percolation d p with hμ
  have hα0 : 0 ≤ α := measureReal_nonneg.trans (hα x)
  have hsub : crossAll t R x ∩ {ω | ¬ ∀ i : (Fin d × Bool) × Bool,
        b ≤ ((finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
          typPatch t (0 : Vertex d) i).card : ℝ)} ⊆
      ⋃ i ∈ (Finset.univ : Finset ((Fin d × Bool) × Bool)),
        ({ω | ∃ y₀ ∈ splitTarget t i.1 i.2 R, ∃ w : (openGraph ω).Walk x y₀,
            ∀ z ∈ w.support, z ∈ splitCorridor t i.1 i.2 R} ∩
          {ω | (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
            typicalSplitFace t (0 : Vertex d) i.1 i.2).card ≤ ⌊b⌋₊}) := by
    rintro ω ⟨hall, hnot⟩
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hnot
    obtain ⟨i, hi⟩ := hnot
    refine Set.mem_biUnion (Finset.mem_univ i) ⟨hall i, ?_⟩
    show (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
      typicalSplitFace t (0 : Vertex d) i.1 i.2).card ≤ ⌊b⌋₊
    exact Nat.le_floor hi.le
  refine (measureReal_mono (μ := μ) hsub (measure_ne_top μ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset ((Fin d × Bool) × Bool)),
      μ.real ({ω | ∃ y₀ ∈ splitTarget t i.1 i.2 R, ∃ w : (openGraph ω).Walk x y₀,
            ∀ z ∈ w.support, z ∈ splitCorridor t i.1 i.2 R} ∩
          {ω | (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
            typicalSplitFace t (0 : Vertex d) i.1 i.2).card ≤ ⌊b⌋₊}) ≤
      (⌊b⌋₊ : ℝ) * α * β := by
    intro i _
    refine (splitCrossing_small_count_le p t ht i.1 i.2 R hx hr ⌊b⌋₊ hα).trans ?_
    exact mul_le_mul_of_nonneg_left (hβ i) (mul_nonneg (Nat.cast_nonneg _) hα0)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

end NearCritical.Section10
