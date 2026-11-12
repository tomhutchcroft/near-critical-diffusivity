module

public import NearCritical.Section10DiameterFailure
public import NearCritical.ConnectionToSet

/-! The upper face counts of Step 1 of `prop.proba.pregood`, by Markov.

`BoxFaceFirstMoment d B` is the cited-level input (source eq.expansion_11 and
its off-centre analogue): for every root `x` of `centeredBox d N` and every
face, the expected number of points of the cluster of `x` on that face is at
most `B`, i.e. `sum_{y in face} P_{p_c}[x <->_{Lambda_N} y] <= B`.

* `face_count_failure_le`: `P[some face has more than K cluster points] <= 2 d B / K`.
* `stepOne_upper_failure`: for the origin typical cube, on any event of
  probability at least `c/(N+1)^2`, the upper face counts of def.spanning.z
  fail with probability at most `a₃ P[S]`, provided `d B <= 2 a₃ c C_b`. This
  is the hypothesis `hup` of `stepOne_property_of_failures`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- Cited-level boundary first moment in a box. -/
def BoxFaceFirstMoment (d : ℕ) (B : ℝ) : Prop :=
  ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N → ∀ f : Fin d × Bool,
    ∑ y ∈ signedCubeFace d N f, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y}) ≤ B

lemma mem_cluster_iff_conn {d : ℕ} (ω : Configuration d) (U : Finset (Vertex d))
    {x : Vertex d} (hx : x ∈ U) (y : Vertex d) :
    y ∈ finiteBoxCluster ω U x ↔ ω ∈ connectionToSetEvent (U : Set (Vertex d)) x {y} := by
  rw [mem_finiteBoxCluster]
  constructor
  · rintro ⟨hy, hr⟩
    exact ⟨hx, y, rfl, hy, hr⟩
  · rintro ⟨_, y', hy', hyU, hr⟩
    have : y' = y := hy'
    subst this
    exact ⟨hyU, hr⟩

theorem face_count_failure_le {d : ℕ} {B : ℝ} (hB : BoxFaceFirstMoment d B) (N : ℕ)
    (x : Vertex d) (hx : x ∈ centeredBox d N) {K : ℝ} (hK : 0 < K) :
    (percolation d (criticalPoint d)).real
      {ω | ¬ ∀ f : Fin d × Bool,
        ((finiteBoxCluster ω (centeredBox d N) x ∩ signedCubeFace d N f).card : ℝ) ≤ K} ≤
      2 * (d : ℝ) * (B / K) := by
  set μ := percolation d (criticalPoint d) with hμ
  have hface : ∀ f : Fin d × Bool, μ.real {ω |
      K ≤ ((finiteBoxCluster ω (centeredBox d N) x ∩ signedCubeFace d N f).card : ℝ)} ≤
      B / K := by
    intro f
    have hmeas : ∀ y, MeasurableSet
        (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y}) :=
      fun y => measurableSet_connectionToSetEvent _ _ _
    have hint : ∀ y ∈ signedCubeFace d N f, Integrable
        (Set.indicator (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y})
          (fun _ => (1:ℝ))) μ :=
      fun y _ => (integrable_const (1:ℝ)).indicator (hmeas y)
    have hcard : ∀ ω : Configuration d,
        ((finiteBoxCluster ω (centeredBox d N) x ∩ signedCubeFace d N f).card : ℝ) =
        ∑ y ∈ signedCubeFace d N f,
          Set.indicator (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y})
            (fun _ => (1:ℝ)) ω := by
      intro ω
      have hfilter : finiteBoxCluster ω (centeredBox d N) x ∩ signedCubeFace d N f =
          (signedCubeFace d N f).filter
            (fun y => ω ∈ connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y}) := by
        ext y
        rw [Finset.mem_inter, Finset.mem_filter, mem_cluster_iff_conn ω _ hx y]
        exact and_comm
      rw [hfilter, Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [Set.indicator]
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
      (f := fun ω => ∑ y ∈ signedCubeFace d N f,
        Set.indicator (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y})
          (fun _ => (1:ℝ)) ω)
      (Filter.Eventually.of_forall (fun ω => Finset.sum_nonneg (fun y _ => by
        simp only [Set.indicator]
        split_ifs <;> norm_num)))
      (integrable_finset_sum _ hint) K
    rw [integral_finset_sum _ hint] at hmarkov
    have hsum : ∑ y ∈ signedCubeFace d N f, ∫ ω,
        Set.indicator (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y})
          (fun _ => (1:ℝ)) ω ∂μ ≤ B := by
      refine le_trans (le_of_eq ?_) (hB N x hx f)
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [integral_indicator_const _ (hmeas y), smul_eq_mul, mul_one]
    have hset : {ω : Configuration d |
        K ≤ ((finiteBoxCluster ω (centeredBox d N) x ∩ signedCubeFace d N f).card : ℝ)} =
        {ω | K ≤ ∑ y ∈ signedCubeFace d N f,
          Set.indicator (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y})
            (fun _ => (1:ℝ)) ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, hcard ω]
    rw [hset, le_div_iff₀ hK, mul_comm]
    exact hmarkov.trans hsum
  have hsub : {ω : Configuration d | ¬ ∀ f : Fin d × Bool,
        ((finiteBoxCluster ω (centeredBox d N) x ∩ signedCubeFace d N f).card : ℝ) ≤ K} ⊆
      ⋃ f ∈ (Finset.univ : Finset (Fin d × Bool)), {ω |
        K ≤ ((finiteBoxCluster ω (centeredBox d N) x ∩ signedCubeFace d N f).card : ℝ)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hω
    obtain ⟨f, hf⟩ := hω
    exact Set.mem_biUnion (Finset.mem_univ f) hf.le
  refine (measureReal_mono (μ := μ) hsub (measure_ne_top μ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ f ∈ (Finset.univ : Finset (Fin d × Bool)), μ.real {ω |
        K ≤ ((finiteBoxCluster ω (centeredBox d N) x ∩ signedCubeFace d N f).card : ℝ)}
      ≤ ∑ _f ∈ (Finset.univ : Finset (Fin d × Bool)), B / K :=
        Finset.sum_le_sum (fun f _ => hface f)
    _ = 2 * (d : ℝ) * (B / K) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring

/-- **Upper face-count failure of Step 1 at the origin typical cube.** -/
theorem stepOne_upper_failure {d : ℕ} {B : ℝ} (hB0 : 0 ≤ B) (hB : BoxFaceFirstMoment d B)
    (typ : TypicalParameters) (hbU : 0 < typ.boundaryUpper) (t N : ℕ) (ht : 1 ≤ t)
    (hN : (t - 1) / 2 = N) (x : Vertex d) (hx : x ∈ centeredBox d N)
    (S : Set (Configuration d)) {c a₃ : ℝ} (hc : 0 ≤ c) (ha₃ : 0 ≤ a₃)
    (hS : c / (N + 1 : ℝ) ^ 2 ≤ (percolation d (criticalPoint d)).real S)
    (hrel : (d : ℝ) * B ≤ 2 * a₃ * c * typ.boundaryUpper) :
    (percolation d (criticalPoint d)).real (S ∩ {ω | ¬ ∀ face : Fin d × Bool,
        ((finiteBoxCluster ω (centeredBox d N) x ∩ typicalFace t (0 : Vertex d) face).card : ℝ) ≤
          typ.boundaryUpper * (2 * (t : ℝ)) ^ 2}) ≤
      a₃ * (percolation d (criticalPoint d)).real S := by
  have hfaces : typicalFace t (0 : Vertex d) = signedCubeFace d N := by
    funext f
    rw [typicalFace_zero t ht, hN]
  have htR : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hK : 0 < typ.boundaryUpper * (2 * (t : ℝ)) ^ 2 := by positivity
  rw [hfaces]
  refine (measureReal_mono (μ := percolation d (criticalPoint d)) Set.inter_subset_right
    (measure_ne_top _ _)).trans ?_
  refine (face_count_failure_le hB N x hx hK).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hS ha₃)
  have hNt : ((N : ℝ) + 1) ≤ (t : ℝ) := by
    have : N + 1 ≤ t := by omega
    exact_mod_cast this
  have hNpos : (0:ℝ) < (N : ℝ) + 1 := by positivity
  have hid : 2 * (d : ℝ) * (B / (typ.boundaryUpper * (2 * (t : ℝ)) ^ 2)) =
      (d : ℝ) * B / (2 * typ.boundaryUpper * (t : ℝ) ^ 2) := by
    field_simp
  rw [hid, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ((N : ℝ) + 1) ^ 2 ≤ (t : ℝ) ^ 2 := pow_le_pow_left₀ hNpos.le hNt 2
  have hdB : 0 ≤ (d : ℝ) * B := by positivity
  calc (d : ℝ) * B * ((N : ℝ) + 1) ^ 2 ≤ (2 * a₃ * c * typ.boundaryUpper) * (t : ℝ) ^ 2 :=
        mul_le_mul hrel hsq (by positivity) (hdB.trans hrel)
    _ = a₃ * c * (2 * typ.boundaryUpper * (t : ℝ) ^ 2) := by ring

end NearCritical.Section10
