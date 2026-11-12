module

public import NearCritical.ClusterRevealSupport

/-! The cluster-conditioned union bound behind the `delta n^2` argument of
`lem.arm.2dspanning` (lower count of boundary points).

* `cluster_event_fresh_prob`: for a fixed value `C` of the root's cluster in
  `U`, an event local on bonds disjoint from the explored bonds of `C` is
  independent of `{C_U(root) = C}`.
* `cluster_conditioned_count_bound`: let `A C y` be events, each local on a
  finite set `T C` of bonds unexplored by `C`, with `P(A C y) <= alpha`. Then

    `P[ |C_U(root) ∩ F| <= m  and  some y in C_U(root) ∩ F has A (C_U(root)) y ]
        <= m * alpha * P[ C_U(root) ∩ F nonempty ]`.

  In the source `F` is a split face, `A C y` is "y has an open arm of diameter
  `7n/8` avoiding `C`" (so `alpha <~ n^-2`), `m = delta n^2` and
  `P[C ∩ F nonempty] <= P[x <-> boundary] <~ n^-2`, giving `<~ delta n^-2`.

No hypothesis beyond locality, measurability and the uniform bound.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

theorem cluster_event_fresh_prob {d : ℕ} (p : unitInterval) (U C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) (T : Finset (Bond d))
    (hd : Disjoint (clusterRevealBonds U C) T) (A : Set (Configuration d))
    (hA : MeasurableSet A)
    (hloc : ∀ ω θ : Configuration d, (∀ b ∈ T, ω b = θ b) → (ω ∈ A ↔ θ ∈ A)) :
    (percolation d p).real ({ω | finiteBoxCluster ω U root = C} ∩ A) =
      (percolation d p).real {ω | finiteBoxCluster ω U root = C} * (percolation d p).real A := by
  have hE : MeasurableSet {ω : Configuration d | finiteBoxCluster ω U root = C} :=
    measurableSet_clusterReveal_event U C root hroot
  let g : (T → Bool) → ℝ := fun ξ =>
    A.indicator (fun _ => (1 : ℝ)) (extendConfiguration T (fun _ => false) ξ)
  have hg : ∀ ω : Configuration d, g (T.restrict ω) = A.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hEq := hloc ω (extendConfiguration T (fun _ => false) (T.restrict ω)) (by
      intro b hb
      simp [extendConfiguration, hb, Finset.restrict])
    simp only [g, Set.indicator_apply, ← hEq]
  have h := clusterReveal_fresh_factorization p U C root hroot T hd (fun _ => (1 : ℝ)) g
  simp_rw [hg] at h
  have hprod : (fun ω : Configuration d =>
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun _ => (1 : ℝ)) ω * A.indicator (fun _ => (1 : ℝ)) ω) =
      (({η | finiteBoxCluster η U root = C} : Set (Configuration d)) ∩ A).indicator
        (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h1 : ω ∈ ({η | finiteBoxCluster η U root = C} : Set (Configuration d)) <;>
      by_cases h2 : ω ∈ A <;> simp [Set.indicator, h1, h2]
  rw [hprod] at h
  have hI : ∀ S : Set (Configuration d), MeasurableSet S →
      (∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂percolation d p) = (percolation d p).real S := by
    intro S hS
    rw [integral_indicator_const _ hS, smul_eq_mul, mul_one]
  rw [← hI _ (hE.inter hA), ← hI _ hE, ← hI _ hA]
  exact h

theorem cluster_conditioned_count_bound {d : ℕ} (p : unitInterval) (U F : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) (T : Finset (Vertex d) → Finset (Bond d))
    (hT : ∀ C, Disjoint (clusterRevealBonds U C) (T C))
    (A : Finset (Vertex d) → Vertex d → Set (Configuration d))
    (hA : ∀ C y, MeasurableSet (A C y))
    (hloc : ∀ C y (ω θ : Configuration d), (∀ b ∈ T C, ω b = θ b) → (ω ∈ A C y ↔ θ ∈ A C y))
    {α : ℝ} (hα : ∀ C y, (percolation d p).real (A C y) ≤ α) (m : ℕ) :
    (percolation d p).real
      {ω | (finiteBoxCluster ω U root ∩ F).card ≤ m ∧
        ∃ y ∈ finiteBoxCluster ω U root ∩ F, ω ∈ A (finiteBoxCluster ω U root) y} ≤
      (m : ℝ) * α * (percolation d p).real {ω | (finiteBoxCluster ω U root ∩ F).Nonempty} := by
  set μ := percolation d p with hμ
  set good : Finset (Finset (Vertex d)) := U.powerset.filter
    (fun C => (C ∩ F).card ≤ m ∧ (C ∩ F).Nonempty) with hgood
  have hEm : ∀ C, MeasurableSet {ω : Configuration d | finiteBoxCluster ω U root = C} :=
    fun C => measurableSet_clusterReveal_event U C root hroot
  have hsub : {ω : Configuration d | (finiteBoxCluster ω U root ∩ F).card ≤ m ∧
        ∃ y ∈ finiteBoxCluster ω U root ∩ F, ω ∈ A (finiteBoxCluster ω U root) y} ⊆
      ⋃ C ∈ good, ⋃ y ∈ C ∩ F, ({ω | finiteBoxCluster ω U root = C} ∩ A C y) := by
    rintro ω ⟨hcard, y, hy, hAy⟩
    have hCU : finiteBoxCluster ω U root ∈ U.powerset := by
      rw [Finset.mem_powerset]
      unfold finiteBoxCluster
      exact Finset.filter_subset _ _
    refine Set.mem_biUnion (Finset.mem_filter.mpr ⟨hCU, hcard, ⟨y, hy⟩⟩) ?_
    exact Set.mem_biUnion hy ⟨rfl, hAy⟩
  have h1 := measureReal_mono (μ := μ) hsub (measure_ne_top μ _)
  have h2 : μ.real (⋃ C ∈ good, ⋃ y ∈ C ∩ F,
        ({ω | finiteBoxCluster ω U root = C} ∩ A C y)) ≤
      ∑ C ∈ good, ∑ y ∈ C ∩ F, μ.real ({ω | finiteBoxCluster ω U root = C} ∩ A C y) :=
    (measureReal_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum (fun C _ => measureReal_biUnion_finset_le _ _))
  have h3 : ∑ C ∈ good, ∑ y ∈ C ∩ F, μ.real ({ω | finiteBoxCluster ω U root = C} ∩ A C y) ≤
      ∑ C ∈ good, (m : ℝ) * α * μ.real {ω | finiteBoxCluster ω U root = C} := by
    refine Finset.sum_le_sum (fun C hC => ?_)
    obtain ⟨_, hcard, hne⟩ := Finset.mem_filter.mp hC
    have hα0 : 0 ≤ α := measureReal_nonneg.trans (hα C hne.choose)
    have hterm : ∀ y ∈ C ∩ F, μ.real ({ω | finiteBoxCluster ω U root = C} ∩ A C y) ≤
        μ.real {ω | finiteBoxCluster ω U root = C} * α := by
      intro y _
      rw [cluster_event_fresh_prob p U C root hroot (T C) (hT C) (A C y) (hA C y) (hloc C y)]
      exact mul_le_mul_of_nonneg_left (hα C y) measureReal_nonneg
    calc ∑ y ∈ C ∩ F, μ.real ({ω | finiteBoxCluster ω U root = C} ∩ A C y)
        ≤ ∑ _y ∈ C ∩ F, μ.real {ω | finiteBoxCluster ω U root = C} * α :=
          Finset.sum_le_sum hterm
      _ = ((C ∩ F).card : ℝ) * (μ.real {ω | finiteBoxCluster ω U root = C} * α) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (μ.real {ω | finiteBoxCluster ω U root = C} * α) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (mul_nonneg measureReal_nonneg hα0)
      _ = (m : ℝ) * α * μ.real {ω | finiteBoxCluster ω U root = C} := by ring
  have hdisj : (good : Set (Finset (Vertex d))).PairwiseDisjoint
      (fun C => {ω : Configuration d | finiteBoxCluster ω U root = C}) := by
    intro C _ C' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h h'
    exact hne (h.symm.trans h')
  have h4 : ∑ C ∈ good, μ.real {ω | finiteBoxCluster ω U root = C} ≤
      μ.real {ω | (finiteBoxCluster ω U root ∩ F).Nonempty} := by
    rw [← measureReal_biUnion_finset hdisj (fun C _ => hEm C)]
    refine measureReal_mono ?_ (measure_ne_top μ _)
    intro ω hω
    obtain ⟨C, hC, hωC⟩ := Set.mem_iUnion₂.mp hω
    have hCeq : finiteBoxCluster ω U root = C := hωC
    show (finiteBoxCluster ω U root ∩ F).Nonempty
    rw [hCeq]
    exact (Finset.mem_filter.mp hC).2.2
  have hα0 : 0 ≤ α := measureReal_nonneg.trans (hα ∅ root)
  calc μ.real _ ≤ ∑ C ∈ good, (m : ℝ) * α * μ.real {ω | finiteBoxCluster ω U root = C} :=
        h1.trans (h2.trans h3)
    _ = (m : ℝ) * α * ∑ C ∈ good, μ.real {ω | finiteBoxCluster ω U root = C} := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (mul_nonneg (Nat.cast_nonneg m) hα0)

end NearCritical
