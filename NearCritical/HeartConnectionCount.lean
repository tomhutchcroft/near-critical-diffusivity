module

public import NearCritical.HeartMembershipBK

/-! Finite-target connection count for the lower branch of NEW PxinfC.
For the source Y the target parameter must be the inner boundary of H.
Identifying its positive event with the full H-cluster union for x outside H
requires a separate boundary-hitting bridge. No diagram bound is asserted. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

/-- Number of actual Q-cluster vertices in the finite heart. -/
def heartConnectionCount {d : ℕ} (Q heart : Finset (Vertex d)) (x : Vertex d)
    (ω : Configuration d) : ℝ :=
  ((heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card:ℝ)

lemma heartConnectionCount_eq_sum {d : ℕ} (Q heart : Finset (Vertex d))
    (x : Vertex d) (ω : Configuration d) :
    heartConnectionCount Q heart x ω =
      ∑ y ∈ heart, if y ∈ finiteBoxCluster ω Q x then (1:ℝ) else 0 := by
  rw [Finset.sum_boole]
  rfl

/-- The source positive-count event is exactly actual fC membership. -/
theorem heartConnectionCount_pos_iff {d : ℕ} (Q heart : Finset (Vertex d))
    (hheart : heart ⊆ Q) (x : Vertex d) (hxQ : x ∈ Q) (ω : Configuration d) :
    0 < heartConnectionCount Q heart x ω ↔ x ∈ heartClusterUnion ω Q heart := by
  rw [heartClusterUnion_mem_connection ω Q heart hheart x]
  constructor
  · intro hp
    have hc : 0 < (heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card := by
      change 0 < ((heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card:ℝ) at hp
      exact_mod_cast hp
    obtain ⟨y,hy⟩ := Finset.card_pos.mp hc
    obtain ⟨hyH,hyC⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyQ,hxy⟩ := (mem_finiteBoxCluster ω Q x y).mp hyC
    exact ⟨hxQ,y,hyH,hyQ,hxy⟩
  · rintro ⟨_hxQ,y,hyH,hyQ,hxy⟩
    have hc : 0 < (heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card :=
      Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr
        ⟨hyH,(mem_finiteBoxCluster ω Q x y).mpr ⟨hyQ,hxy⟩⟩⟩
    change 0 < ((heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card:ℝ)
    exact_mod_cast hc

/-- All real observables of actual Y, including its square, are integrable
by finite internal-coordinate support, without a supplied moment hypothesis. -/
lemma integrable_heartConnectionCount_observable {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (x : Vertex d) (f : ℝ → ℝ) :
    Integrable (fun ω => f (heartConnectionCount Q heart x ω)) (percolation d p) := by
  have hi := percolation_cylinder_integrable d p (internalBondSet Q)
    (fun ξ => f (heartConnectionCount Q heart x (reconstructInterior Q ξ)))
  apply hi.congr
  filter_upwards [] with ω
  have he := finiteBoxCluster_eq_of_internal_agree Q Q (fun _ hz => hz) ω _
    (reconstructInterior_restrict_agree Q ω) x
  simp only [heartConnectionCount, ← he]

private lemma cluster_mem_connection_singleton {d : ℕ} (Q : Finset (Vertex d))
    (x y : Vertex d) (hxQ : x ∈ Q) :
    {ω : Configuration d | y ∈ finiteBoxCluster ω Q x} =
      connectionToSetEvent (Q : Set (Vertex d)) x {y} := by
  ext ω
  constructor
  · intro hy
    obtain ⟨hyQ,hxy⟩ := (mem_finiteBoxCluster ω Q x y).mp hy
    exact ⟨hxQ,y,rfl,hyQ,hxy⟩
  · rintro ⟨_hx,z,hz,hzQ,hxz⟩
    have he : z = y := hz
    subst z
    exact (mem_finiteBoxCluster ω Q x y).mpr ⟨hzQ,hxz⟩

/-- Exact first moment of actual Y as the sum of restricted singleton
connection probabilities appearing in source lem.Y_firstmoment. -/
theorem integral_heartConnectionCount {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (x : Vertex d) (hxQ : x ∈ Q) :
    (∫ ω, heartConnectionCount Q heart x ω ∂percolation d p) =
      ∑ y ∈ heart, (percolation d p).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y}) := by
  have hm (y : Vertex d) : MeasurableSet {ω : Configuration d | y ∈ finiteBoxCluster ω Q x} := by
    rw [cluster_mem_connection_singleton Q x y hxQ]
    exact measurableSet_connectionToSetEvent _ _ _
  have hi (y : Vertex d) : Integrable
      (fun ω : Configuration d => if y ∈ finiteBoxCluster ω Q x then (1:ℝ) else 0)
      (percolation d p) := by
    apply ((integrable_const (μ := percolation d p) (1:ℝ)).indicator (hm y)).congr
    filter_upwards [] with ω
    by_cases hω : y ∈ finiteBoxCluster ω Q x <;> simp [hω]
  simp_rw [heartConnectionCount_eq_sum]
  rw [integral_finsetSum heart (fun y _ => hi y)]
  apply Finset.sum_congr rfl
  intro y _hy
  have he : (∫ ω, if y ∈ finiteBoxCluster ω Q x then (1:ℝ) else 0
      ∂percolation d p) = (percolation d p).real
        {ω : Configuration d | y ∈ finiteBoxCluster ω Q x} := by
    simpa [Set.indicator, Set.mem_ofPred_eq] using
      (integral_indicator_one (μ := percolation d p) (hm y))
  rw [cluster_mem_connection_singleton Q x y hxQ] at he
  exact he

/-- A raw uniform restricted two-point lower bound yields the actual first
moment lower bound. Its source box geometry still requires instantiation. -/
theorem integral_heartConnectionCount_lower {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (x : Vertex d) (hxQ : x ∈ Q) {a : ℝ}
    (hconn : ∀ y ∈ heart, a ≤ (percolation d p).real
      (connectionToSetEvent (Q : Set (Vertex d)) x {y})) :
    a*(heart.card:ℝ) ≤ ∫ ω, heartConnectionCount Q heart x ω ∂percolation d p := by
  rw [integral_heartConnectionCount p Q heart x hxQ]
  calc
    _ = ∑ _y ∈ heart, a := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum hconn

end NearCritical
