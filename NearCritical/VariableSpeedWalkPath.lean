module

public import NearCritical.VariableSpeedWalkMarginal
public import Mathlib.Topology.Order.Cadlag

@[expose] public section
noncomputable section

namespace NearCritical

open Filter Set
open scoped Topology Classical

/-- A nonexplosive proposal clock. Arrival zero represents the initial
state, with one proposal at each subsequent arrival. -/
structure VariableSpeedJumpClock where
  arrival : ℕ → ℝ
  start : arrival 0 = 0
  strictMono_arrival : StrictMono arrival
  diverges : Tendsto arrival atTop atTop

namespace VariableSpeedJumpClock

theorem exists_next (c : VariableSpeedJumpClock) (t : ℝ) :
    ∃ n : ℕ, t < c.arrival (n+1) := by
  obtain ⟨n,hn⟩ := ((tendsto_atTop.1 c.diverges) (t+1)).exists
  exact ⟨n,(show t < t+1 by linarith).trans_le
    (hn.trans (c.strictMono_arrival.monotone (Nat.le_succ n)))⟩

/-- The number of proposals already made, including one at time `t`
when `t` is an arrival. The extension to negative times is zero. -/
def count (c : VariableSpeedJumpClock) (t : ℝ) : ℕ :=
  Nat.find (exists_next c t)

theorem count_lt_next (c : VariableSpeedJumpClock) (t : ℝ) :
    t < c.arrival (c.count t+1) := Nat.find_spec (exists_next c t)

theorem count_le_iff_lt_next (c : VariableSpeedJumpClock) {t : ℝ} {n : ℕ} :
    c.count t ≤ n ↔ t < c.arrival (n+1) := by
  constructor
  · intro h
    exact (c.count_lt_next t).trans_le (c.strictMono_arrival.monotone (Nat.succ_le_succ h))
  · exact Nat.find_min' (exists_next c t)

theorem count_eq_of_window (c : VariableSpeedJumpClock) {t : ℝ} {n : ℕ}
    (hlo : n = 0 ∨ c.arrival n ≤ t) (hhi : t < c.arrival (n+1)) :
    c.count t = n := by
  apply (Nat.find_eq_iff (exists_next c t)).mpr
  refine ⟨hhi,?_⟩
  intro m hm
  rcases hlo with rfl | hn
  · omega
  · exact not_lt_of_ge ((c.strictMono_arrival.monotone (by omega : m+1 ≤ n)).trans hn)

theorem count_eq_of_le_lt_next (c : VariableSpeedJumpClock) {t u : ℝ}
    (ht : t ≤ u) (hu : u < c.arrival (c.count t+1)) :
    c.count u = c.count t := by
  apply (Nat.find_eq_iff (exists_next c u)).mpr
  refine ⟨hu,?_⟩
  intro n hn hn'
  exact (Nat.find_min (exists_next c t) hn) (ht.trans_lt hn')

theorem exists_weak_next (c : VariableSpeedJumpClock) (t : ℝ) :
    ∃ n : ℕ, t ≤ c.arrival (n+1) :=
  (exists_next c t).imp fun _ h => h.le

/-- The count immediately before the given time. -/
def leftCount (c : VariableSpeedJumpClock) (t : ℝ) : ℕ :=
  Nat.find (exists_weak_next c t)

theorem leftCount_le_next (c : VariableSpeedJumpClock) (t : ℝ) :
    t ≤ c.arrival (c.leftCount t+1) :=
  Nat.find_spec (exists_weak_next c t)

theorem leftCount_zero_or_lt (c : VariableSpeedJumpClock) (t : ℝ) :
    c.leftCount t = 0 ∨ c.arrival (c.leftCount t) < t := by
  by_cases h : c.leftCount t = 0
  · exact Or.inl h
  · right
    have hlt : c.leftCount t-1 < Nat.find (exists_weak_next c t) := by
      change c.leftCount t-1 < c.leftCount t
      omega
    have hnot := Nat.find_min (exists_weak_next c t) hlt
    have he : c.leftCount t-1+1 = c.leftCount t := by omega
    exact lt_of_not_ge (by simpa only [he] using hnot)

theorem count_isCadlag (c : VariableSpeedJumpClock) : IsCadlag c.count := by
  constructor
  · intro t
    have hhi : ∀ᶠ u in 𝓝[>] t, u < c.arrival (c.count t+1) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (c.count_lt_next t))
    have he : ∀ᶠ u in 𝓝[>] t, c.count u = c.count t := by
      filter_upwards [self_mem_nhdsWithin, hhi] with u hu hnext
      exact c.count_eq_of_le_lt_next (le_of_lt hu) hnext
    exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  · intro t
    refine ⟨c.leftCount t,?_⟩
    have hlo : ∀ᶠ u in 𝓝[<] t, c.leftCount t = 0 ∨ c.arrival (c.leftCount t) ≤ u := by
      rcases c.leftCount_zero_or_lt t with h0 | ht
      · exact Eventually.of_forall fun _ => Or.inl h0
      · have h : ∀ᶠ u in 𝓝[<] t, c.arrival (c.leftCount t) < u :=
          nhdsWithin_le_nhds (Ioi_mem_nhds ht)
        exact h.mono fun _ hu => Or.inr hu.le
    have he : ∀ᶠ u in 𝓝[<] t, c.count u = c.leftCount t := by
      filter_upwards [self_mem_nhdsWithin, hlo] with u hu hprev
      exact c.count_eq_of_window hprev (lt_of_lt_of_le hu (c.leftCount_le_next t))
    exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)

/-- Positive waiting times with divergent partial sums yield the
nonexplosive arrival clock used in uniformization. -/
def ofWaitingTimes (s : ℕ → ℝ) (hs : ∀ n, 0 < s n)
    (hdiv : Tendsto (fun n => ∑ j ∈ Finset.range n, s j) atTop atTop) :
    VariableSpeedJumpClock where
  arrival n := ∑ j ∈ Finset.range n, s j
  start := by simp
  strictMono_arrival := strictMono_nat_of_lt_succ fun n => by
    rw [Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (hs n)
  diverges := hdiv

end VariableSpeedJumpClock

/-- A sample path of the variable-speed walk under uniformization. Each
clock arrival proposes one directed bond and a closed bond gives a hold. -/
def variableSpeedJumpPath {d : ℕ} (ω : Configuration d) (x : Vertex d)
    (c : VariableSpeedJumpClock) (dirs : ℕ → Fin d × Bool) (t : ℝ) : Vertex d :=
  variableSpeedEndpoint ω (c.count t) x (fun k => dirs k.val)

theorem variableSpeedJumpPath_isCadlag {d : ℕ} (ω : Configuration d) (x : Vertex d)
    (c : VariableSpeedJumpClock) (dirs : ℕ → Fin d × Bool) :
    IsCadlag (variableSpeedJumpPath ω x c dirs) := by
  exact c.count_isCadlag.continuous_comp
    (continuous_of_discreteTopology
      (f := fun n => variableSpeedEndpoint ω n x (fun k => dirs k.val)))

theorem variableSpeedJumpPath_reachable {d : ℕ} (ω : Configuration d) (x : Vertex d)
    (c : VariableSpeedJumpClock) (dirs : ℕ → Fin d × Bool) (t : ℝ) :
    (openGraph ω).Reachable x (variableSpeedJumpPath ω x c dirs t) :=
  variableSpeedEndpoint_reachable ω (c.count t) x (fun k => dirs k.val)

end NearCritical
