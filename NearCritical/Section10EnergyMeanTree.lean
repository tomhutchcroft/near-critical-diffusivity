module

public import NearCritical.Section8PairDiagrams
public import NearCritical.Section8EnergyMoments
public import NearCritical.Section10MarkCard

/-! First step of prop:Ef1 / prop:Ef2: the conditional energy means are bounded
by the weighted tree-diagram sum over the heart annulus divided by the hitting
probability.

`weighted_pair_sum_le`: for a nonnegative weight vanishing off the annulus,
`sum_{y in Q} f y P[x, y in fC] <= sum_{y in annulus} f y (G x G y +
 sum_u G u tau(u,x) tau(u,y))` (from `heartPair_probability_le_annulus_tree`).
`energyOne_mean_le_tree`, `energyTwo_mean_le_tree`: the two means, via the exact
formulas of `Section8EnergyMoments`.
`typ_energyOne_mean_le_tree`, `typ_energyTwo_mean_le_tree`: the instances for
the origin typical cube and a marked boundary point (heart ratio at most 1/16,
`t >= 64`), i.e. the left sides of `hm1`, `hm2`.

NOT proved here: the numerical bounds on `annulusG`, `annulusTau` and the sums,
and the lower bound on the hitting probability.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory NearCritical.Section8
open scoped Classical

/-- Tree-diagram bound of the pair probability, as a function of the second point. -/
def pairTree {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d)) (x y : Vertex d) : ℝ :=
  annulusG p Q H x * annulusG p Q H y +
    ∑ u ∈ heartAnnulus Q H, annulusG p Q H u * annulusTau p Q H u x * annulusTau p Q H u y

theorem weighted_pair_sum_le {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    {x : Vertex d} (hx : x ∈ heartAnnulus Q H) (f : Vertex d → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hz : ∀ y ∈ Q, y ∉ heartAnnulus Q H → f y = 0) :
    ∑ y ∈ Q, f y * (percolation d p).real (heartPairEvent Q H x y) ≤
      ∑ y ∈ heartAnnulus Q H, f y * pairTree p Q H x y := by
  rw [← Finset.sum_subset (heartAnnulus_subset Q H)
    (fun y hy hny => by rw [hz y hy hny, zero_mul])]
  exact Finset.sum_le_sum fun y hy =>
    mul_le_mul_of_nonneg_left (heartPair_probability_le_annulus_tree p Q H x y hx hy) (hf y)

theorem energyOne_mean_le_tree {d : ℕ} (p : unitInterval) (Q H excluded : Finset (Vertex d))
    (hH : H ⊆ Q) (hex : H ⊆ excluded) (r : ℕ) {x : Vertex d} (hx : x ∈ heartAnnulus Q H) :
    heartConditionalMean p Q H (fun F => regularityEnergyOne F excluded r x) x ≤
      (∑ y ∈ heartAnnulus Q H, energyOneWeight excluded r x y * pairTree p Q H x y) /
        (percolation d p).real (heartEvent Q H x) := by
  rw [energyOne_conditional_mean_exact p Q H excluded hH r x]
  refine div_le_div_of_nonneg_right
    (weighted_pair_sum_le p Q H hx _ (energyOneWeight_nonneg excluded r x) ?_) measureReal_nonneg
  intro y hy hny
  have hyH : y ∈ H := by
    by_contra h
    exact hny (Finset.mem_sdiff.mpr ⟨hy, fun h' => h (Finset.mem_sdiff.mp h').1⟩)
  unfold energyOneWeight
  rw [if_neg (not_not.mpr (hex hyH))]

theorem energyTwo_mean_le_tree {d : ℕ} (p : unitInterval)
    (Q H cubeBoundary : Finset (Vertex d)) (hH : H ⊆ Q)
    (hdisj : ∀ y ∈ cubeBoundary, y ∉ H) (r : ℕ) {x : Vertex d}
    (hx : x ∈ heartAnnulus Q H) :
    heartConditionalMean p Q H (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤
      (∑ y ∈ heartAnnulus Q H, energyTwoWeight cubeBoundary r x y * pairTree p Q H x y) /
        (percolation d p).real (heartEvent Q H x) := by
  rw [energyTwo_conditional_mean_exact p Q H cubeBoundary hH r x]
  refine div_le_div_of_nonneg_right
    (weighted_pair_sum_le p Q H hx _ (energyTwoWeight_nonneg cubeBoundary r x) ?_)
    measureReal_nonneg
  intro y hy hny
  have hyH : y ∈ H := by
    by_contra h
    exact hny (Finset.mem_sdiff.mpr ⟨hy, fun h' => h (Finset.mem_sdiff.mp h').1⟩)
  unfold energyTwoWeight
  rw [if_neg (fun hb => hdisj y hb hyH)]

theorem typicalHeart_subset_cube {d : ℕ} (t : ℕ) (z : Vertex d) (cc : ℝ) :
    typicalHeart t z cc ⊆ typicalCube t z := Finset.filter_subset _ _

theorem typicalHeart_subset_inner {d : ℕ} (t : ℕ) (z : Vertex d) {cc : ℝ} (hcc : cc ≤ 3 / 4) :
    typicalHeart t z cc ⊆ typicalInnerCube t z := by
  intro x hx
  obtain ⟨hxQ, hxh⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxQ, fun j => ?_⟩
  have h1 := hxh j
  have h2 : cc * (t : ℝ) ≤ 3 / 4 * (t : ℝ) :=
    mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg t)
  linarith

theorem typicalBoundary_not_heart {d : ℕ} (t : ℕ) (ht : 64 ≤ t) {cc : ℝ} (hcc : cc ≤ 1 / 16)
    {y : Vertex d} (hy : y ∈ typicalBoundary t (0 : Vertex d)) :
    y ∉ typicalHeart t (0 : Vertex d) cc := by
  intro hyH
  obtain ⟨f, _, hf⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨_, hfe⟩ := Finset.mem_filter.mp hf
  obtain ⟨_, hyh⟩ := Finset.mem_filter.mp hyH
  have h1 := hyh f.1
  obtain ⟨N, hN⟩ : ∃ N, (t - 1) / 2 = N := ⟨_, rfl⟩
  rw [hN] at hfe
  have hint : |y f.1 - (0 : Vertex d) f.1| = (N : ℤ) := by
    rw [hfe]
    split_ifs
    · exact abs_of_nonneg (Int.natCast_nonneg N)
    · rw [abs_neg]
      exact abs_of_nonneg (Int.natCast_nonneg N)
  have hreal : |((y f.1 - (0 : Vertex d) f.1 : ℤ) : ℝ)| = (N : ℝ) := by
    rw [← Int.cast_abs, hint]
    simp
  rw [hreal] at h1
  have htR : (64:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hNt : (t : ℝ) ≤ 2 * (N : ℝ) + 2 := by
    exact_mod_cast (show t ≤ 2 * N + 2 by omega)
  have h2 : cc * (t : ℝ) ≤ 1 / 16 * (t : ℝ) :=
    mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg t)
  linarith

theorem typMark_mem_annulus {d : ℕ} (t : ℕ) (ht : 64 ≤ t) {cc : ℝ} (hcc : cc ≤ 1 / 16)
    {x : Vertex d} (hx : x ∈ typMark t (0 : Vertex d)) :
    x ∈ heartAnnulus (typicalCube t 0) (typicalHeart t 0 cc) :=
  Finset.mem_sdiff.mpr ⟨typMark_subset_cube t 0 hx, fun h =>
    typicalBoundary_not_heart t ht hcc (typMark_subset_boundary t 0 hx) (Finset.mem_sdiff.mp h).1⟩

theorem typ_energyOne_mean_le_tree {d : ℕ} (t : ℕ) (ht : 64 ≤ t) {cc : ℝ} (hcc : cc ≤ 1 / 16)
    (r : ℕ) {x : Vertex d} (hx : x ∈ typMark t (0 : Vertex d)) :
    heartConditionalMean (criticalPoint d) (typicalCube t 0) (typicalHeart t 0 cc)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) r x) x ≤
      (∑ y ∈ heartAnnulus (typicalCube t 0) (typicalHeart t 0 cc),
          energyOneWeight (typicalInnerCube t 0) r x y *
            pairTree (criticalPoint d) (typicalCube t 0) (typicalHeart t 0 cc) x y) /
        (percolation d (criticalPoint d)).real
          (heartEvent (typicalCube t 0) (typicalHeart t 0 cc) x) :=
  energyOne_mean_le_tree _ _ _ _ (typicalHeart_subset_cube t 0 cc)
    (typicalHeart_subset_inner t 0 (by linarith)) r (typMark_mem_annulus t ht hcc hx)

theorem typ_energyTwo_mean_le_tree {d : ℕ} (t : ℕ) (ht : 64 ≤ t) {cc : ℝ} (hcc : cc ≤ 1 / 16)
    (r : ℕ) {x : Vertex d} (hx : x ∈ typMark t (0 : Vertex d)) :
    heartConditionalMean (criticalPoint d) (typicalCube t 0) (typicalHeart t 0 cc)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) r x) x ≤
      (∑ y ∈ heartAnnulus (typicalCube t 0) (typicalHeart t 0 cc),
          energyTwoWeight (typicalBoundary t 0) r x y *
            pairTree (criticalPoint d) (typicalCube t 0) (typicalHeart t 0 cc) x y) /
        (percolation d (criticalPoint d)).real
          (heartEvent (typicalCube t 0) (typicalHeart t 0 cc) x) :=
  energyTwo_mean_le_tree _ _ _ _ (typicalHeart_subset_cube t 0 cc)
    (fun y hy => typicalBoundary_not_heart t ht hcc hy) r (typMark_mem_annulus t ht hcc hx)

end NearCritical.Section10
