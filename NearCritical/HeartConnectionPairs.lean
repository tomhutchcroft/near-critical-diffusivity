module

public import NearCritical.HeartConnectionCount

/-! Exact actual second moment before the NEW lem.Y_secondmoment estimates.
Pairs are ordered; the diagonal is the first moment, not a cardinality bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical

private lemma count_as_connection_indicators {d : ℕ} (Q heart : Finset (Vertex d))
    (x : Vertex d) (hxQ : x ∈ Q) (ω : Configuration d) :
    heartConnectionCount Q heart x ω = ∑ y ∈ heart,
      if ω ∈ connectionToSetEvent (Q : Set (Vertex d)) x {y} then (1:ℝ) else 0 := by
  rw [heartConnectionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  have he : y ∈ finiteBoxCluster ω Q x ↔
      ω ∈ connectionToSetEvent (Q : Set (Vertex d)) x {y} := by
    constructor
    · intro hy
      obtain ⟨hyQ,hxy⟩ := (mem_finiteBoxCluster ω Q x y).mp hy
      exact ⟨hxQ,y,rfl,hyQ,hxy⟩
    · rintro ⟨_hx,z,hz,hzQ,hxz⟩
      have heq : z = y := hz
      subst z
      exact (mem_finiteBoxCluster ω Q x y).mpr ⟨hzQ,hxz⟩
  simp only [he]

/-- Exact actual Y second moment as the FULL ordered-pair joint probability
sum. No independence or tree-graph inequality enters this identity. -/
theorem integral_heartConnectionCount_sq_pairs {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (x : Vertex d) (hxQ : x ∈ Q) :
    (∫ ω, (heartConnectionCount Q heart x ω)^2 ∂percolation d p) =
      ∑ y ∈ heart, ∑ z ∈ heart, (percolation d p).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y} ∩
          connectionToSetEvent (Q : Set (Vertex d)) x {z}) := by
  let E := fun y : Vertex d => connectionToSetEvent (Q : Set (Vertex d)) x {y}
  let I := fun y (ω : Configuration d) => if ω ∈ E y then (1:ℝ) else 0
  have hm (y z : Vertex d) : MeasurableSet (E y ∩ E z) :=
    (measurableSet_connectionToSetEvent _ _ _).inter (measurableSet_connectionToSetEvent _ _ _)
  have hp (y z : Vertex d) (ω : Configuration d) :
      I y ω * I z ω = if ω ∈ E y ∩ E z then (1:ℝ) else 0 := by
    by_cases hy : ω ∈ E y <;> by_cases hz : ω ∈ E z <;> simp [I,hy,hz]
  have hi (y z : Vertex d) : Integrable (fun ω => I y ω * I z ω) (percolation d p) := by
    simp_rw [hp]
    apply ((integrable_const (μ := percolation d p) (1:ℝ)).indicator (hm y z)).congr
    filter_upwards [] with ω
    by_cases hω : ω ∈ E y ∩ E z <;> simp [hω]
  have hY (ω : Configuration d) :
      (heartConnectionCount Q heart x ω)^2 = ∑ y ∈ heart, ∑ z ∈ heart, I y ω * I z ω := by
    have hc : heartConnectionCount Q heart x ω = ∑ y ∈ heart, I y ω :=
      count_as_connection_indicators Q heart x hxQ ω
    rw [hc, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _hy
    rw [Finset.mul_sum]
  simp_rw [hY]
  rw [integral_finsetSum heart (fun y _ => integrable_finsetSum heart (fun z _ => hi y z))]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [integral_finsetSum heart (fun z _ => hi y z)]
  apply Finset.sum_congr rfl
  intro z _hz
  simp_rw [hp]
  simpa [Set.indicator,E] using integral_indicator_one (μ := percolation d p) (hm y z)

/-- Diagonal joint events equal singleton events exactly. Off-diagonal pairs
remain ordered, with no missing factor two or substituted |heart| term. -/
theorem integral_heartConnectionCount_sq_diag_offdiag {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (x : Vertex d) (hxQ : x ∈ Q) :
    (∫ ω, (heartConnectionCount Q heart x ω)^2 ∂percolation d p) =
      (∫ ω, heartConnectionCount Q heart x ω ∂percolation d p) +
      ∑ y ∈ heart, ∑ z ∈ heart, if y = z then 0 else (percolation d p).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y} ∩
          connectionToSetEvent (Q : Set (Vertex d)) x {z}) := by
  rw [integral_heartConnectionCount_sq_pairs p Q heart x hxQ,
    integral_heartConnectionCount p Q heart x hxQ]
  have he (y : Vertex d) (hy : y ∈ heart) :
      (∑ z ∈ heart, (percolation d p).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y} ∩
          connectionToSetEvent (Q : Set (Vertex d)) x {z})) =
      (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {y}) +
      ∑ z ∈ heart, if y = z then 0 else (percolation d p).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y} ∩
          connectionToSetEvent (Q : Set (Vertex d)) x {z}) := by
    rw [← Finset.sum_erase_add _ _ hy]
    simp only [Set.inter_self]
    have hz : (∑ z ∈ heart, if y = z then (0:ℝ) else (percolation d p).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y} ∩
          connectionToSetEvent (Q : Set (Vertex d)) x {z})) =
        ∑ z ∈ heart.erase y, (percolation d p).real
          (connectionToSetEvent (Q : Set (Vertex d)) x {y} ∩
            connectionToSetEvent (Q : Set (Vertex d)) x {z}) := by
      rw [← Finset.sum_erase_add _ _ hy]
      simp only [ite_true,add_zero]
      apply Finset.sum_congr rfl
      intro z hz
      rw [if_neg (Ne.symm (Finset.mem_erase.mp hz).1)]
    rw [hz]
    ring
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl he

end NearCritical
