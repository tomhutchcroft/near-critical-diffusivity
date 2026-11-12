module
public import NearCritical.HeartConnectionSecondMoment
public import NearCritical.HalfSpaceSubcritical

/-! Finite-domain form of Appendix lem.Nn_mean_upper, with the SLAB retained.
The cited second moment is an explicit standard input; the first-moment
bound is derived from the actual count and actual half-space arm event. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

def slabTopTargets {d : ℕ} (Q : Finset (Vertex d)) (i : Fin d) (n : ℕ) : Finset (Vertex d) :=
  Q.filter (fun y => y i = (n : ℤ))

/-- STANDARD finite restriction of source lem.Nn_moments, van2025one Lemmas
4.1/4.2: the actual count in any finite subdomain of the slab is bounded
pointwise by the cited full slab count. No first-moment estimate is supplied. -/
def SlabBoundarySecondMomentUpper {d : ℕ} (i : Fin d) (B : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ Q : Finset (Vertex d),
    (∀ y ∈ Q, 0 ≤ y i ∧ y i ≤ (n : ℤ)) →
    (∫ ω, (heartConnectionCount Q (slabTopTargets Q i n) 0 ω)^2
      ∂percolation d (criticalPoint d)) ≤ B*(n : ℝ)

/-- Actual finite slab count mean, from the cited second moment and boundary
arm upper input. All integrability and the Cauchy--Schwarz bridge are proved. -/
theorem finite_slab_count_mean_le {d : ℕ} (i : Fin d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (arm : HalfSpaceCriticalArmInput i A)
    (second : SlabBoundarySecondMomentUpper i B)
    (n : ℕ) (hn : 1 ≤ n) (Q : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Q)
    (hQ : ∀ y ∈ Q, 0 ≤ y i ∧ y i ≤ (n : ℤ)) :
    (∫ ω, heartConnectionCount Q (slabTopTargets Q i n) 0 ω
      ∂percolation d (criticalPoint d)) ≤ (A+B)/(n : ℝ) := by
  let p := criticalPoint d
  let T := slabTopTargets Q i n
  let m := ∫ ω, heartConnectionCount Q T 0 ω ∂percolation d p
  let s := ∫ ω, (heartConnectionCount Q T 0 ω)^2 ∂percolation d p
  let P := (percolation d p).real {ω | (0 : Vertex d) ∈ heartClusterUnion ω Q T}
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hT : T ⊆ Q := Finset.filter_subset _ _
  have hm0 : 0 ≤ m := integral_nonneg (fun ω => by dsimp [heartConnectionCount]; positivity)
  have hsB : s ≤ B*(n : ℝ) := second n hn Q hQ
  have hP : P ≤ A/(n : ℝ)^3 := by
    have he : {ω : Configuration d | (0 : Vertex d) ∈ heartClusterUnion ω Q T} ⊆
        connectionToSetEvent {z : Vertex d | 0 ≤ z i} 0 {z | (n : ℤ) ≤ z i} := by
      intro ω hω
      have hc := (heartClusterUnion_mem_connection ω Q T hT 0).mp hω
      apply connectionToSetEvent_mono (fun z hz => (hQ z hz).1) (fun z hz => ?_) 0 hc
      have hz' := (Finset.mem_filter.mp hz).2
      exact hz'.ge
    have hp := ENNReal.toReal_mono ENNReal.ofReal_ne_top (arm n hn)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ A/(n : ℝ)^3)] at hp
    exact (measureReal_mono he (measure_ne_top _ _)).trans hp
  by_cases hm : 0 < m
  · have hs : 0 < s := integral_heartConnectionCount_sq_pos p Q T 0 hm
    have hcs : m^2/s ≤ P := heartClusterUnion_probability_lower_second_moment p Q T hT 0 h0 hm
    have hms : m^2 ≤ (A/(n : ℝ)^3)*(B*(n : ℝ)) :=
      ((div_le_iff₀ hs).mp hcs).trans (mul_le_mul hP hsB hs.le (by positivity))
    have he : (A/(n : ℝ)^3)*(B*(n : ℝ)) = A*B/(n : ℝ)^2 := by
      field_simp [ne_of_gt hnpos]
      <;> ring
    rw [he] at hms
    have hmn : (m*(n : ℝ))^2 ≤ A*B := by
      simpa only [mul_pow] using (le_div_iff₀ (pow_pos hnpos 2)).mp hms
    have hab : A*B ≤ (A+B)^2 := by
      nlinarith [mul_nonneg hA hB,sq_nonneg A,sq_nonneg B]
    apply (le_div_iff₀ hnpos).mpr
    change m*(n : ℝ) ≤ A+B
    nlinarith [hmn.trans hab]
  · have hmzero : m = 0 := le_antisymm (le_of_not_gt hm) hm0
    change m ≤ _
    rw [hmzero]
    positivity

/-- The literal finite top-plane probability sum has the same uniform bound.
This is slab-confined, not a full-half-space plane-mass estimate. -/
theorem finite_slab_plane_mass_le {d : ℕ} (i : Fin d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (arm : HalfSpaceCriticalArmInput i A)
    (second : SlabBoundarySecondMomentUpper i B)
    (n : ℕ) (hn : 1 ≤ n) (Q : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Q)
    (hQ : ∀ y ∈ Q, 0 ≤ y i ∧ y i ≤ (n : ℤ)) :
    ∑ y ∈ slabTopTargets Q i n, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (Q : Set (Vertex d)) 0 {y}) ≤ (A+B)/(n : ℝ) := by
  rw [← integral_heartConnectionCount (criticalPoint d) Q (slabTopTargets Q i n) 0 h0]
  exact finite_slab_count_mean_le i A B hA hB arm second n hn Q h0 hQ

end NearCritical.Section8
