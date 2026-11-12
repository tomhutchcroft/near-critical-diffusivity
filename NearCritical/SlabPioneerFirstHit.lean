module

public import NearCritical.Section8FirstExit
public import NearCritical.SlabPioneerConvolution
public import NearCritical.HalfSpacePioneerReduction

/-! A half-space path to a fixed layer splits at its first visit to the
layer into a slab prefix and a half-space suffix. -/
@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory
open scoped Classical ENNReal

theorem halfSpace_connection_le_slab_first_hit {d : ℕ} (p : unitInterval) (i : Fin d)
    {n : ℕ} (hn : 1 ≤ n) (y : Vertex d) (hy : y i = (n : ℤ)) :
    let H : Set (Vertex d) := {z | 0 ≤ z i}
    let S := finiteHeightSlab i 0 (n : ℤ)
    percolation d p (connectionToSetEvent H 0 {y}) ≤
      ∑' u : Vertex d, if u i = (n : ℤ) then
        percolation d p (connectionToSetEvent S 0 {u}) *
          percolation d p (connectionToSetEvent H u {y}) else 0 := by
  intro H S
  let D : Set (Vertex d) := {z | z i < (n : ℤ)}
  let μ := percolation d p
  let E (u : Vertex d) : Set (Configuration d) := if u i = (n : ℤ) then
    {ω | DisjointOccurrence (connectionToSetEvent S 0 {u}) (connectionToSetEvent H u {y}) ω}
    else ∅
  have hcover : connectionToSetEvent H 0 {y} ⊆ ⋃ u, E u := by
    rintro ω ⟨h0H, z, hz, _, ⟨w⟩⟩
    have hzy : z = y := hz
    subst z
    have hle : restrictedGraph ω H ≤ openGraph ω := fun _ _ h => h.1
    let r : (openGraph ω).Walk 0 y := w.toPath.val.mapLe hle
    have hr : r.IsPath := w.toPath.property.mapLe _
    have hrH : ∀ v ∈ r.support, v ∈ H := by
      simpa only [r, SimpleGraph.Walk.support_mapLe_eq_support] using
        restrictedWalk_support w.toPath.val h0H
    have h0D : (0 : Vertex d) ∈ D := by
      change (0 : ℤ) < n
      omega
    have hyD : y ∉ D := by change ¬ y i < (n : ℤ); omega
    obtain ⟨z, u, hzu, a, b, hzD, huD, hab, ha⟩ := Section8.walk_first_exit D r h0D hyD
    have hab' : (a.concat hzu).append b = r := by
      simpa only [SimpleGraph.Walk.concat_append] using hab
    have hu : u i = (n : ℤ) := by
      have hstep := openGraph_adj_height_bounds hzu i
      change z i < (n : ℤ) at hzD
      change ¬ u i < (n : ℤ) at huD
      omega
    have haS : ∀ v ∈ (a.concat hzu).support, v ∈ S := by
      intro v hv
      have hvH := hrH v (hab' ▸ (a.concat hzu).support_subset_support_append_left b hv)
      change 0 ≤ v i at hvH
      refine ⟨hvH, ?_⟩
      rw [SimpleGraph.Walk.support_concat] at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact (ha v hv : v i < (n : ℤ)).le
      · have hvu : v = u := by simpa only [List.mem_singleton] using hv
        rw [hvu, hu]
    have hbH : ∀ v ∈ b.support, v ∈ H := fun v hv =>
      hrH v (hab' ▸ (a.concat hzu).support_subset_support_append_right b hv)
    have hdis : (a.concat hzu).edges.Disjoint b.edges :=
      ((SimpleGraph.Walk.isTrail_append (a.concat hzu) b).mp (hab'.symm ▸ hr.isTrail)).2.2
    apply Set.mem_iUnion.mpr
    refine ⟨u, ?_⟩
    dsimp only [E]
    rw [if_pos hu]
    exact disjointOpenWalks_occurrence (a.concat hzu) b hdis S H {u} {y} haS hbH rfl rfl
  calc
    _ ≤ μ (⋃ u, E u) := measure_mono hcover
    _ ≤ ∑' u, μ (E u) := measure_iUnion_le _
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro u
      by_cases hu : u i = (n : ℤ)
      · simp only [E, if_pos hu]
        exact connectionToSet_bk_ennreal p _ _ _ _ _ _
      · simp [E, hu]


/-- Sum the first-hit inequality over endpoints. A uniform bound on the
same-height half-space mass bounds the cost of the suffix. -/
theorem halfSpacePioneerMass_le_slab_mul_plane {d : ℕ} (p : unitInterval) (i : Fin d)
    {n : ℕ} (hn : 1 ≤ n) (M : ℝ≥0∞)
    (hM : ∀ u : Vertex d, u i = (n : ℤ) →
      (∑' y : Vertex d, if y i = (n : ℤ) then percolation d p
        (connectionToSetEvent {z | 0 ≤ z i} u {y}) else 0) ≤ M) :
    halfSpacePioneerMass p i (n : ℤ) ≤ slabPioneerMass p i 0 (n : ℤ) 0 (n : ℤ) * M := by
  let H : Set (Vertex d) := {z | 0 ≤ z i}
  let S := finiteHeightSlab i 0 (n : ℤ)
  let P (u : Vertex d) := if u i = (n : ℤ) then
    percolation d p (connectionToSetEvent S 0 {u}) else 0
  let Q (u y : Vertex d) := if y i = (n : ℤ) then
    percolation d p (connectionToSetEvent H u {y}) else 0
  have hp : (∑' u, P u) = slabPioneerMass p i 0 (n : ℤ) 0 (n : ℤ) := by
    simp only [P, slabPioneerMass, Pi.single_zero, S]
  rw [← halfSpace_prefix_sum p i (n : ℤ), ← hp]
  calc
    _ ≤ ∑' y, ∑' u, P u * Q u y := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases hy : y i = (n : ℤ)
      · rw [if_pos hy]
        refine (halfSpace_connection_le_slab_first_hit p i hn y hy).trans_eq ?_
        apply tsum_congr
        intro u
        by_cases hu : u i = (n : ℤ) <;> simp [P, Q, H, S, hu, hy]
      · simp [hy]
    _ = ∑' u, ∑' y, P u * Q u y := ENNReal.tsum_comm
    _ = ∑' u, P u * ∑' y, Q u y := by
      apply tsum_congr
      intro u
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' u, P u * M := by
      apply ENNReal.tsum_le_tsum
      intro u
      by_cases hu : u i = (n : ℤ)
      · exact mul_le_mul' le_rfl (hM u hu)
      · simp [P, hu]
    _ = _ := ENNReal.tsum_mul_right

end NearCritical
