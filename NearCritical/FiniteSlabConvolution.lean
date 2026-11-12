module

public import NearCritical.FiniteSlabPioneer

/-! NEW finite-cutoff pioneer convolution, retaining actual forward rows and
backward columns. No stationarity of a fixed finite cutoff is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- The maximum of an actual finite simple path stays in U. Its two pieces
lie in the SAME cutoff with a smaller upper slab boundary, and have disjoint
finite forcing certificates under arbitrary outside assignments. -/
theorem finiteSlab_connection_maximum_split {d : ℕ} {ω : Configuration d}
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x y : Vertex d)
    (hω : ω ∈ finiteSlabConnectionEvent U i m n x y) :
    ∃ u ∈ U, max (x i) (y i) ≤ u i ∧ u i ≤ n ∧
      DisjointOccurrence (finiteSlabConnectionEvent U i m (u i) x u)
        (finiteSlabConnectionEvent U i m (u i) y u) ω := by
  let S := finiteHeightSlab i m n ∩ (U : Set (Vertex d))
  obtain ⟨hx, z, hz, _, ⟨w⟩⟩ := hω
  have hzy : z = y := hz
  subst z
  have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h ↦ h.1
  let q : (openGraph ω).Walk x y := (w.toPath : (restrictedGraph ω S).Walk x y).mapLe hle
  have hq : q.IsPath := w.toPath.property.mapLe _
  have hqS : ∀ z ∈ q.support, z ∈ S := by
    simpa only [q, SimpleGraph.Walk.support_mapLe_eq_support] using
      restrictedWalk_support (w.toPath : (restrictedGraph ω S).Walk x y) hx
  obtain ⟨u, hu, hmin⟩ := q.support.toFinset.exists_min_image (fun z ↦ -(z i)) ⟨x, by simp⟩
  have hu' : u ∈ q.support := List.mem_toFinset.mp hu
  have hmax : ∀ z ∈ q.support, z i ≤ u i := by
    intro z hz
    have h := hmin z (List.mem_toFinset.mpr hz)
    omega
  refine ⟨u, (hqS u hu').2, max_le (hmax x q.start_mem_support) (hmax y q.end_mem_support),
    (hqS u hu').1.2, ?_⟩
  let T := finiteHeightSlab i m (u i) ∩ (U : Set (Vertex d))
  have hsplit := simplePath_split_occurrence q hq hu' T T {y}
    (fun z hz ↦ ⟨⟨(hqS z (q.support_takeUntil_subset_support hu' hz)).1.1,
      hmax z (q.support_takeUntil_subset_support hu' hz)⟩,
      (hqS z (q.support_takeUntil_subset_support hu' hz)).2⟩)
    (fun z hz ↦ ⟨⟨(hqS z (q.support_dropUntil_subset_support hu' hz)).1.1,
      hmax z (q.support_dropUntil_subset_support hu' hz)⟩,
      (hqS z (q.support_dropUntil_subset_support hu' hz)).2⟩) rfl
  rw [connectionToSetEvent_singleton_symm T u y] at hsplit
  exact hsplit

private lemma finiteSlab_height_regroup {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (a b : ℤ) (f : Vertex d → ℝ) :
    (∑ z ∈ U, if a ≤ z i ∧ z i ≤ b then f z else 0) =
      ∑ h ∈ Finset.Icc a b, ∑ z ∈ U, if z i = h then f z else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [eq_comm]

/-- Actual finite-union/BK product bound, grouped by the chosen top cut and
intermediate vertex inside U. No probability decomposition is a premise. -/
theorem finiteSlab_connection_maximum_bk {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    (percolation d p).real (finiteSlabConnectionEvent U i m n x y) ≤
      ∑ h ∈ Finset.Icc (max (x i) (y i)) n, ∑ z ∈ U, if z i = h then
        (percolation d p).real (finiteSlabConnectionEvent U i m h x z) *
          (percolation d p).real (finiteSlabConnectionEvent U i m h y z) else 0 := by
  let C := fun z : Vertex d ↦ {ω : Configuration d | max (x i) (y i) ≤ z i ∧ z i ≤ n ∧
    DisjointOccurrence (finiteSlabConnectionEvent U i m (z i) x z)
      (finiteSlabConnectionEvent U i m (z i) y z) ω}
  have hsub : finiteSlabConnectionEvent U i m n x y ⊆ ⋃ z ∈ U, C z := by
    intro ω hω
    obtain ⟨z, hzU, hxy, hzn, hdis⟩ := finiteSlab_connection_maximum_split U i m n x y hω
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzU, hxy, hzn, hdis⟩⟩
  calc
    _ ≤ (percolation d p).real (⋃ z ∈ U, C z) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ z ∈ U, (percolation d p).real (C z) := measureReal_biUnion_finset_le U C
    _ ≤ ∑ z ∈ U, if max (x i) (y i) ≤ z i ∧ z i ≤ n then
        (percolation d p).real (finiteSlabConnectionEvent U i m (z i) x z) *
          (percolation d p).real (finiteSlabConnectionEvent U i m (z i) y z) else 0 := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : max (x i) (y i) ≤ z i ∧ z i ≤ n
      · rw [ite_eq_left hz]
        exact (measureReal_mono (show C z ⊆ {ω | DisjointOccurrence
          (finiteSlabConnectionEvent U i m (z i) x z)
          (finiteSlabConnectionEvent U i m (z i) y z) ω} from fun _ h ↦ h.2.2) (measure_ne_top _ _)).trans
          (connectionToSet_bk p _ _ x y {z} {z})
      · have hempty : C z = ∅ := by
          ext ω
          simp only [C, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h ↦ hz ⟨h.1, h.2.1⟩
        simp only [ite_eq_right hz, hempty, measureReal_empty, le_refl]
    _ = _ := by
      rw [finiteSlab_height_regroup]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z i = h
      · rw [ite_eq_left hz, ite_eq_left hz, hz]
      · simp only [ite_eq_right hz]

private lemma finiteSlab_sum_ite_sum {Y H : Type*} (U : Finset Y) (J : Finset H)
    (P : Y → Prop) [DecidablePred P] (g : Y → H → ℝ) :
    (∑ y ∈ U, if P y then ∑ h ∈ J, g y h else 0) =
      ∑ h ∈ J, ∑ y ∈ U, if P y then g y h else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : P y <;> simp [hy]

/-- Pure finite regrouping: the backward factor remains the ACTUAL column
mass in the SAME U. No finite-cutoff stationarity or reflection is used. -/
lemma finiteSlab_double_plane_sum {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m h j : ℤ) (x : Vertex d) :
    (∑ y ∈ U, if y i = j then ∑ z ∈ U, if z i = h then
      (percolation d p).real (finiteSlabConnectionEvent U i m h x z) *
        (percolation d p).real (finiteSlabConnectionEvent U i m h y z) else 0 else 0) =
      ∑ z ∈ U, if z i = h then
        (percolation d p).real (finiteSlabConnectionEvent U i m h x z) *
          finiteSlabColumnMean p U i m h j z else 0 := by
  calc
    _ = ∑ y ∈ U, ∑ z ∈ U, if z i = h then
        (percolation d p).real (finiteSlabConnectionEvent U i m h x z) *
          (if y i = j then (percolation d p).real (finiteSlabConnectionEvent U i m h y z) else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y i = j <;> simp [hy]
    _ = ∑ z ∈ U, ∑ y ∈ U, if z i = h then
        (percolation d p).real (finiteSlabConnectionEvent U i m h x z) *
          (if y i = j then (percolation d p).real (finiteSlabConnectionEvent U i m h y z) else 0)
        else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z i = h
      · simp only [ite_eq_left hz, finiteSlabColumnMean, Finset.mul_sum]
      · simp only [ite_eq_right hz, Finset.sum_const_zero]

/-- Finite-cutoff row convolution with independent forward boundary rows and
backward boundary-start columns. This is a proved probability inequality. -/
theorem finiteSlabRowMean_convolution {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteSlabRowMean p U i m n x j ≤
      ∑ h ∈ Finset.Icc (max (x i) j) n, ∑ z ∈ U, if z i = h then
        (percolation d p).real (finiteSlabConnectionEvent U i m h x z) *
          finiteSlabColumnMean p U i m h j z else 0 := by
  calc
    _ ≤ ∑ y ∈ U, if y i = j then ∑ h ∈ Finset.Icc (max (x i) j) n,
        ∑ z ∈ U, if z i = h then
          (percolation d p).real (finiteSlabConnectionEvent U i m h x z) *
            (percolation d p).real (finiteSlabConnectionEvent U i m h y z) else 0 else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y i = j
      · rw [ite_eq_left hy, ite_eq_left hy]
        simpa only [hy] using finiteSlab_connection_maximum_bk p U i m n x y
      · simp only [ite_eq_right hy, le_refl]
    _ = ∑ h ∈ Finset.Icc (max (x i) j) n, ∑ y ∈ U, if y i = j then
        ∑ z ∈ U, if z i = h then
          (percolation d p).real (finiteSlabConnectionEvent U i m h x z) *
            (percolation d p).real (finiteSlabConnectionEvent U i m h y z) else 0 else 0 :=
      finiteSlab_sum_ite_sum U (Finset.Icc (max (x i) j) n) (fun y : Vertex d ↦ y i = j) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      exact finiteSlab_double_plane_sum p U i m h j x

/-- The counterpart for backward columns is endpoint reversal in the SAME
cutoff, not stationarity of a finite model. -/
theorem finiteSlabColumnMean_convolution {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n k : ℤ) (y : Vertex d) :
    finiteSlabColumnMean p U i m n k y ≤
      ∑ h ∈ Finset.Icc (max k (y i)) n, ∑ z ∈ U, if z i = h then
        finiteSlabColumnMean p U i m h k z *
          (percolation d p).real (finiteSlabConnectionEvent U i m h y z) else 0 := by
  rw [finiteSlabColumnMean_eq_rowMean]
  have h := finiteSlabRowMean_convolution p U i m n y k
  simpa only [max_comm, mul_comm] using h

/-- Group the actual convolution against separately bounded forward top-target
rows and backward top-start columns. No identification of those families is used. -/
theorem finiteSlabRowMean_le_boundary_products {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    (F G : ℤ → ℝ)
    (hG : ∀ h ∈ Finset.Icc (max (x i) j) n, 0 ≤ G h)
    (hforward : ∀ h ∈ Finset.Icc (max (x i) j) n, finiteSlabRowMean p U i m h x h ≤ F h)
    (hbackward : ∀ h ∈ Finset.Icc (max (x i) j) n, ∀ z ∈ U, z i = h →
      finiteSlabColumnMean p U i m h j z ≤ G h) :
    finiteSlabRowMean p U i m n x j ≤ ∑ h ∈ Finset.Icc (max (x i) j) n, F h * G h := by
  apply (finiteSlabRowMean_convolution p U i m n x j).trans
  apply Finset.sum_le_sum
  intro h hh
  calc
    _ ≤ ∑ z ∈ U, if z i = h then
        (percolation d p).real (finiteSlabConnectionEvent U i m h x z) * G h else 0 := by
      apply Finset.sum_le_sum
      intro z hzU
      by_cases hz : z i = h
      · rw [ite_eq_left hz, ite_eq_left hz]
        exact mul_le_mul_of_nonneg_left (hbackward h hh z hzU hz) measureReal_nonneg
      · simp only [ite_eq_right hz, le_refl]
    _ = finiteSlabRowMean p U i m h x h * G h := by
      unfold finiteSlabRowMean
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z i = h <;> simp [hz]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hforward h hh) (hG h hh)

/-- Source maximal-function step for the cutoff: each off-diagonal row is
bounded by the number of top cuts times M², using BOTH boundary families. -/
theorem finiteSlabRowMean_le_cut_count_mul_sq {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) (M : ℝ)
    (hM : 0 ≤ M)
    (hforward : ∀ h ∈ Finset.Icc (max (x i) j) n, finiteSlabRowMean p U i m h x h ≤ M)
    (hbackward : ∀ h ∈ Finset.Icc (max (x i) j) n, ∀ z ∈ U, z i = h →
      finiteSlabColumnMean p U i m h j z ≤ M) :
    finiteSlabRowMean p U i m n x j ≤
      ((Finset.Icc (max (x i) j) n).card : ℝ) * M ^ 2 := by
  simpa only [Finset.sum_const, nsmul_eq_mul, pow_two] using
    finiteSlabRowMean_le_boundary_products p U i m n x j (fun _ ↦ M) (fun _ ↦ M)
      (fun _ _ ↦ hM) hforward hbackward

/-- The backward-column counterpart, preserving the same finite cutoff. -/
theorem finiteSlabColumnMean_le_cut_count_mul_sq {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n k : ℤ) (y : Vertex d) (M : ℝ)
    (hM : 0 ≤ M)
    (hforward : ∀ h ∈ Finset.Icc (max k (y i)) n, finiteSlabRowMean p U i m h y h ≤ M)
    (hbackward : ∀ h ∈ Finset.Icc (max k (y i)) n, ∀ z ∈ U, z i = h →
      finiteSlabColumnMean p U i m h k z ≤ M) :
    finiteSlabColumnMean p U i m n k y ≤
      ((Finset.Icc (max k (y i)) n).card : ℝ) * M ^ 2 := by
  rw [finiteSlabColumnMean_eq_rowMean, max_comm k (y i)]
  apply finiteSlabRowMean_le_cut_count_mul_sq p U i m n y k M hM
  · simpa only [max_comm] using hforward
  · simpa only [max_comm] using hbackward

end NearCritical
