module

public import NearCritical.HeartConnectionCount

/-! Finite-target connection count second-moment inequality for eq.PxinfC_CS.
The source target is boundary H; identifying its union with the full H union
for an exterior root is a separate geometric bridge. Numerical estimates
remain separate obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical

lemma heartConnectionCount_le_sq {d : ℕ} (Q heart : Finset (Vertex d))
    (x : Vertex d) (ω : Configuration d) :
    heartConnectionCount Q heart x ω ≤ (heartConnectionCount Q heart x ω)^2 := by
  unfold heartConnectionCount
  have h := Nat.le_mul_self (heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card
  have hr : ((heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card:ℝ) ≤
      ((heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card:ℝ) *
      ((heart.filter (fun y => y ∈ finiteBoxCluster ω Q x)).card:ℝ) := by
    exact_mod_cast h
  simpa only [pow_two] using hr

/-- Positivity of the actual second moment is derived from the actual mean,
using the integer-valued count rather than assuming a denominator bound. -/
lemma integral_heartConnectionCount_sq_pos {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (x : Vertex d)
    (hm : 0 < ∫ ω, heartConnectionCount Q heart x ω ∂percolation d p) :
    0 < ∫ ω, (heartConnectionCount Q heart x ω)^2 ∂percolation d p := by
  exact hm.trans_le (integral_mono
    (integrable_heartConnectionCount_observable p Q heart x (fun z => z))
    (integrable_heartConnectionCount_observable p Q heart x (fun z => z^2))
    (heartConnectionCount_le_sq Q heart x))

/-- Literal source Cauchy--Schwarz probability lower bound for actual fC.
All integrability and the positive denominator are derived for actual Y. -/
theorem heartClusterUnion_probability_lower_second_moment {d : ℕ} (p : unitInterval)
    (Q heart : Finset (Vertex d)) (hheart : heart ⊆ Q) (x : Vertex d) (hxQ : x ∈ Q)
    (hm : 0 < ∫ ω, heartConnectionCount Q heart x ω ∂percolation d p) :
    (∫ ω, heartConnectionCount Q heart x ω ∂percolation d p)^2 /
        (∫ ω, (heartConnectionCount Q heart x ω)^2 ∂percolation d p) ≤
      (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} := by
  let Y := heartConnectionCount Q heart x
  let m := ∫ ω, Y ω ∂percolation d p
  let s := ∫ ω, (Y ω)^2 ∂percolation d p
  let t := m/s
  let I := fun ω : Configuration d => if 0 < Y ω then (1:ℝ) else 0
  have hs : 0 < s := integral_heartConnectionCount_sq_pos p Q heart x hm
  have hi : Integrable I (percolation d p) :=
    integrable_heartConnectionCount_observable p Q heart x (fun z => if 0 < z then 1 else 0)
  have hy : Integrable Y (percolation d p) :=
    integrable_heartConnectionCount_observable p Q heart x (fun z => z)
  have hy2 : Integrable (fun ω => (Y ω)^2) (percolation d p) :=
    integrable_heartConnectionCount_observable p Q heart x (fun z => z^2)
  have hp (ω : Configuration d) :
      (if 0 < Y ω then (1-t*Y ω)^2 else 0) = I ω-(2*t)*Y ω+t^2*(Y ω)^2 := by
    by_cases hpos : 0 < Y ω
    · simp only [I,if_pos hpos]
      ring
    · have hn : 0 ≤ Y ω := by dsimp [Y,heartConnectionCount]; positivity
      have hz : Y ω = 0 := le_antisymm (le_of_not_gt hpos) hn
      simp [I,hpos,hz]
  have hnon : 0 ≤ ∫ ω, I ω-(2*t)*Y ω+t^2*(Y ω)^2 ∂percolation d p := by
    apply integral_nonneg
    intro ω
    change 0 ≤ I ω-(2*t)*Y ω+t^2*(Y ω)^2
    rw [← hp ω]
    split_ifs <;> positivity
  have hI : (∫ ω, I ω ∂percolation d p) =
      (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} := by
    have hmeas := measurableSet_heartClusterUnion_member Q heart hheart x
    have he := integral_indicator_one (μ := percolation d p) hmeas
    have heq : I = fun ω => if x ∈ heartClusterUnion ω Q heart then (1:ℝ) else 0 := by
      funext ω
      simp only [I,Y,heartConnectionCount_pos_iff Q heart hheart x hxQ ω]
    rw [heq]
    simpa [Set.indicator,Set.mem_ofPred_eq] using he
  have hadd := integral_add (hi.sub (hy.const_mul (2*t))) (hy2.const_mul (t^2))
  have hsub := integral_sub hi (hy.const_mul (2*t))
  dsimp only [Pi.sub_apply, Pi.add_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul, integral_const_mul, hI] at hnon
  change 0 ≤ (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} -
    (2*t)*m+t^2*s at hnon
  have he : (2*t)*m-t^2*s = m^2/s := by
    dsimp [t]
    field_simp [ne_of_gt hs]
    <;> ring
  change m^2/s ≤ _
  linarith

end NearCritical
