module

public import NearCritical.SplitCrossMoatBudget
public import NearCritical.SplitCrossOutwardRays

/-! An outside tube for the cluster reveal, built by adjoining the two
outward segments to the vertex-deleted base tube. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical

/-- The base connection less its BK deletion loss gives a connection
between the exit tips, in a finite tube inside the common outside graph.
A terminal without a branch uses a segment of length zero. -/
theorem outside_tube_connection_lower {d : ℕ} (p : unitInterval)
    (U T F : Finset (Vertex d)) (hTU : T ⊆ U)
    (a b : Vertex d) (i j : Fin d) (n m : ℕ)
    (ha : ∀ k ≤ n, starTip a i k ∈ U \ F)
    (hb : ∀ k ≤ m, starTip b j k ∈ U \ F)
    (haT : starTip a i n ∈ T) (hbT : starTip b j m ∈ T)
    (c : ℝ)
    (hc : c + moatDeletionLoss p T F (starTip a i n) (starTip b j m) ≤
      (percolation d p).real (connectionToSetEvent (T : Set (Vertex d))
        (starTip a i n) {starTip b j m})) :
    ∃ D : Finset (Vertex d), D ⊆ U \ F ∧ a ∈ D ∧ b ∈ D ∧
      (p : ℝ)^(n + m) * c ≤
        (percolation d p).real (connectionToSetEvent (D : Set (Vertex d)) a {b}) := by
  let Sa := (Finset.range (n + 1)).image (starTip a i)
  let Sb := (Finset.range (m + 1)).image (starTip b j)
  let D := (T \ F) ∪ (Sa ∪ Sb)
  have hD : D ⊆ U \ F := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxT, hxF⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨hTU hxT, hxF⟩
    · rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        exact ha k (by have := Finset.mem_range.mp hk; omega)
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
        exact hb k (by have := Finset.mem_range.mp hk; omega)
  have haD (k : ℕ) (hk : k ≤ n) : starTip a i k ∈ D :=
    Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩))
  have hbD (k : ℕ) (hk : k ≤ m) : starTip b j k ∈ D :=
    Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩))
  have hzero (k : Fin d) : coordinateRay k 0 = (0 : Vertex d) := by
    ext l
    by_cases hl : l = k <;> simp [coordinateRay, hl]
  refine ⟨D, hD, by simpa [starTip, hzero] using haD 0 (Nat.zero_le _),
    by simpa [starTip, hzero] using hbD 0 (Nat.zero_le _), ?_⟩
  have haF : starTip a i n ∈ T \ F := Finset.mem_sdiff.mpr
    ⟨haT, (Finset.mem_sdiff.mp (ha n le_rfl)).2⟩
  have hbF : starTip b j m ∈ T \ F := Finset.mem_sdiff.mpr
    ⟨hbT, (Finset.mem_sdiff.mp (hb m le_rfl)).2⟩
  have hdel := vertex_deletion_probability_cost p T F (starTip a i n) (starTip b j m) haF hbF
  change _ ≤ (percolation d p).real (connectionToSetEvent (T \ F : Finset (Vertex d))
      (starTip a i n) {starTip b j m}) + moatDeletionLoss p T F (starTip a i n) (starTip b j m) at hdel
  have hbase : c ≤ (percolation d p).real
      (connectionToSetEvent (T \ F : Finset (Vertex d)) (starTip a i n) {starTip b j m}) := by
    linarith
  have hmono : (T \ F : Finset (Vertex d)) ⊆ D := Finset.subset_union_left
  have hset : ((T \ F : Finset (Vertex d)) : Set (Vertex d)) ⊆ (D : Set (Vertex d)) :=
    fun _ hz => hmono hz
  have hprob := hbase.trans (measureReal_mono
    (connectionToSetEvent_mono hset subset_rfl (starTip a i n))
    (measure_ne_top (percolation d p) _))
  exact (mul_le_mul_of_nonneg_left hprob (pow_nonneg p.2.1 _)).trans
    (outward_rays_connection_lower p D a b i j n m haD hbD)

end NearCritical.SplitCrossDirect
