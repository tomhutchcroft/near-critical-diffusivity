module

public import NearCritical.Section10PropertyUnion
public import NearCritical.Section7FaceDiameter

/-! The diameter failure of Step 1 of `prop.proba.pregood`, from the cited
longest-path moment.

* `faceDiameter_failure_le`: at `p_c`, for a root `x` of `centeredBox d N`,
  `P[rin(C_N(x)) > 2T] <= 2 d K / T`, from the tail input `FaceReachTail`
  (a Markov consequence of the cited `eq.chemical_finite_moment`) and the
  triangle inequality at the root (`Section7.faceDiameter_of_not_far`).
* `stepOne_diam_failure`: for the origin typical cube (`N = (t-1)/2`,
  `K_spn (2t)^2 = 2T`), on any event `S` of probability at least `c/(N+1)^2`,
  the diameter condition of def.spanning.z fails with probability at most
  `a₁ P[S]`, provided `d K <= a₁ c K_spn`. This is the hypothesis `hdiam` of
  `stepOne_property_of_failures`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem faceDiameter_failure_le {d : ℕ} {K : ℝ}
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (N : ℕ) (x : Vertex d) (hx : x ∈ centeredBox d N) {T : ℝ} (hT : 0 < T) :
    (percolation d (criticalPoint d)).real
      {ω | ¬ ((spanningFaceDiameter
        (restrictedGraph ω (finiteBoxCluster ω (centeredBox d N) x : Set (Vertex d)))
        (finiteBoxCluster ω (centeredBox d N) x) (signedCubeFace d N) : ℝ) ≤ 2 * T)} ≤
      2 * (d : ℝ) * (K / T) := by
  have hsub : {ω : Configuration d | ¬ ((spanningFaceDiameter
        (restrictedGraph ω (finiteBoxCluster ω (centeredBox d N) x : Set (Vertex d)))
        (finiteBoxCluster ω (centeredBox d N) x) (signedCubeFace d N) : ℝ) ≤ 2 * T)} ⊆
      ⋃ f ∈ (Finset.univ : Finset (Fin d × Bool)), Section7.farFaceEvent N x f T := by
    intro ω hω
    by_contra hne
    apply hω
    have hfar : ∀ f : Fin d × Bool, ω ∉ Section7.farFaceEvent N x f T := by
      intro f hf
      exact hne (Set.mem_biUnion (Finset.mem_univ f) hf)
    exact Section7.faceDiameter_of_not_far ω N x hT.le hfar
  refine (measureReal_mono (μ := percolation d (criticalPoint d)) hsub
    (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ f ∈ (Finset.univ : Finset (Fin d × Bool)),
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T)
      ≤ ∑ _f ∈ (Finset.univ : Finset (Fin d × Bool)), K / T :=
        Finset.sum_le_sum (fun f _ => htail N x hx f T hT)
    _ = 2 * (d : ℝ) * (K / T) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring

/-- **Diameter failure of Step 1 at the origin typical cube.** -/
theorem stepOne_diam_failure {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (typ : TypicalParameters) (hdU : 0 < typ.diameterUpper) (t N : ℕ) (ht : 1 ≤ t)
    (hN : (t - 1) / 2 = N) (x : Vertex d) (hx : x ∈ centeredBox d N)
    (S : Set (Configuration d)) {c a₁ : ℝ} (hc : 0 ≤ c) (ha₁ : 0 ≤ a₁)
    (hS : c / (N + 1 : ℝ) ^ 2 ≤ (percolation d (criticalPoint d)).real S)
    (hrel : (d : ℝ) * K ≤ a₁ * c * typ.diameterUpper) :
    (percolation d (criticalPoint d)).real (S ∩ {ω | ¬
        ((spanningFaceDiameter
          (restrictedGraph ω (finiteBoxCluster ω (centeredBox d N) x : Set (Vertex d)))
          (finiteBoxCluster ω (centeredBox d N) x) (typicalFace t (0 : Vertex d)) : ℝ) ≤
          typ.diameterUpper * (2 * (t : ℝ)) ^ 2)}) ≤
      a₁ * (percolation d (criticalPoint d)).real S := by
  have hfaces : typicalFace t (0 : Vertex d) = signedCubeFace d N := by
    funext f
    rw [typicalFace_zero t ht, hN]
  have htR : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  set T : ℝ := typ.diameterUpper * (2 * (t : ℝ)) ^ 2 / 2 with hTdef
  have hT : 0 < T := by positivity
  have h2T : typ.diameterUpper * (2 * (t : ℝ)) ^ 2 = 2 * T := by
    rw [hTdef]
    ring
  rw [hfaces, h2T]
  refine (measureReal_mono (μ := percolation d (criticalPoint d)) Set.inter_subset_right
    (measure_ne_top _ _)).trans ?_
  refine (faceDiameter_failure_le htail N x hx hT).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hS ha₁)
  have hNt : ((N : ℝ) + 1) ≤ (t : ℝ) := by
    have : N + 1 ≤ t := by omega
    exact_mod_cast this
  have hNpos : (0:ℝ) < (N : ℝ) + 1 := by positivity
  have hid : 2 * (d : ℝ) * (K / T) = (d : ℝ) * K / (typ.diameterUpper * (t : ℝ) ^ 2) := by
    rw [hTdef]
    field_simp
  rw [hid, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ((N : ℝ) + 1) ^ 2 ≤ (t : ℝ) ^ 2 := pow_le_pow_left₀ hNpos.le hNt 2
  have hdK : 0 ≤ (d : ℝ) * K := by positivity
  calc (d : ℝ) * K * ((N : ℝ) + 1) ^ 2 ≤ (a₁ * c * typ.diameterUpper) * (t : ℝ) ^ 2 :=
        mul_le_mul hrel hsq (by positivity) (hdK.trans hrel)
    _ = a₁ * c * (typ.diameterUpper * (t : ℝ) ^ 2) := by ring

end NearCritical.Section10
