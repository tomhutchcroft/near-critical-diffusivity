module

public import NearCritical.ChemicalThinning
public import NearCritical.BK
public import NearCritical.Slab

/-! Parameter monotonicity for the actual infinite Bernoulli law, and the
qualitative phase consequences of the existing critical-point definitions. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set

/-- Thinning never opens a bond that was closed in the original sample. -/
lemma thinConfiguration_le_left {E : Type*} (z : (E → Bool) × (E → Bool)) :
    BK.ConfigLE (thinConfiguration z) z.1 := by
  intro e he
  cases hval : z.1 e
  · simp [thinConfiguration, hval] at he
  · rfl

/-- Arbitrary measurable increasing events are monotone in the Bernoulli
parameter; the event may depend on infinitely many lattice bonds. -/
theorem percolation_increasing_event_mono {d : ℕ} {A : Set (Configuration d)}
    (hA : MeasurableSet A) (hinc : BK.Increasing A)
    {p q : unitInterval} (hpq : p ≤ q) :
    percolation d p A ≤ percolation d q A := by
  by_cases hq : (q : ℝ) = 0
  · have heq : p = q := by
      apply Subtype.ext
      exact le_antisymm hpq (by simpa [hq] using p.2.1)
    simp [heq]
  · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.2.1 (Ne.symm hq)
    let r : unitInterval := ⟨(p : ℝ) / (q : ℝ),
      div_nonneg p.2.1 q.2.1, (div_le_one hqpos).mpr hpq⟩
    have hr : (p : ℝ) = (q : ℝ) * (r : ℝ) := by
      dsimp [r]
      field_simp
    rw [← percolation_thin_map d q r p hr, Measure.map_apply measurable_thinConfiguration hA]
    calc
      _ ≤ ((percolation d q).prod (percolation d r)) (A ×ˢ Set.univ) := by
        apply measure_mono
        intro z hz
        exact ⟨hinc (thinConfiguration_le_left z) hz, Set.mem_univ _⟩
      _ = _ := by rw [Measure.prod_prod]; simp

lemma percolation_increasing_event_real_mono {d : ℕ} {A : Set (Configuration d)}
    (hA : MeasurableSet A) (hinc : BK.Increasing A)
    {p q : unitInterval} (hpq : p ≤ q) :
    (percolation d p).real A ≤ (percolation d q).real A :=
  ENNReal.toReal_mono (measure_ne_top _ _) (percolation_increasing_event_mono hA hinc hpq)

lemma increasing_connectionEvent {d : ℕ} (x y : Vertex d) :
    BK.Increasing (connectionEvent x y) := by
  intro ω η h hω
  exact SimpleGraph.Reachable.mono (openGraph_mono h) hω

lemma increasing_infiniteClusterEvent (d : ℕ) :
    BK.Increasing (infiniteClusterEvent d) := by
  intro ω η h hω
  exact hω.mono (cluster_mono h 0)

lemma twoPoint_monotone (d : ℕ) (x y : Vertex d) :
    Monotone (fun p ↦ twoPoint d p x y) := by
  intro p q hpq
  exact percolation_increasing_event_real_mono (measurableSet_connectionEvent x y)
    (increasing_connectionEvent x y) hpq

lemma density_monotone (d : ℕ) : Monotone (density d) := by
  intro p q hpq
  exact percolation_increasing_event_real_mono (measurableSet_infiniteClusterEvent d)
    (increasing_infiniteClusterEvent d) hpq

lemma increasing_restrictedInfiniteEvent (d : ℕ) (S : Set (Vertex d)) :
    BK.Increasing (restrictedInfiniteEvent d S) := by
  intro ω η h hω
  apply hω.mono
  intro y hy
  apply SimpleGraph.Reachable.mono (G := restrictedGraph ω S) (G' := restrictedGraph η S) _ hy
  rintro u v ⟨huv, hu, hv⟩
  exact ⟨openGraph_mono h huv, hu, hv⟩

lemma restrictedDensity_monotone (d : ℕ) (S : Set (Vertex d)) :
    Monotone (restrictedDensity d S) := by
  intro p q hpq
  exact percolation_increasing_event_real_mono (measurableSet_restrictedInfiniteEvent d S)
    (increasing_restrictedInfiniteEvent d S) hpq

lemma criticalPoint_le_of_density_pos {d : ℕ} {p : unitInterval}
    (hp : 0 < density d p) : criticalPoint d ≤ p := sInf_le hp

/-- Strictly below the critical point the origin has zero probability of
belonging to an infinite cluster. No statement at criticality is asserted. -/
theorem density_eq_zero_below_critical {d : ℕ} {p : unitInterval}
    (hp : p < criticalPoint d) : density d p = 0 := by
  apply le_antisymm _ ENNReal.toReal_nonneg
  by_contra h
  exact (not_le_of_gt hp) (criticalPoint_le_of_density_pos (lt_of_not_ge h))

/-- Positivity above criticality follows from actual parameter monotonicity,
not from the infimum definition alone. -/
theorem density_pos_above_critical {d : ℕ} {p : unitInterval}
    (hp : criticalPoint d < p) : 0 < density d p := by
  obtain ⟨q, hq, hqp⟩ := sInf_lt_iff.mp hp
  exact lt_of_lt_of_le hq (density_monotone d hqp.le)

lemma restrictedCriticalPoint_le_of_density_pos {d : ℕ} {S : Set (Vertex d)}
    {p : unitInterval} (hp : 0 < restrictedDensity d S p) :
    restrictedCriticalPoint d S ≤ p := sInf_le hp

theorem restrictedDensity_eq_zero_below_critical {d : ℕ} {S : Set (Vertex d)}
    {p : unitInterval} (hp : p < restrictedCriticalPoint d S) :
    restrictedDensity d S p = 0 := by
  apply le_antisymm _ ENNReal.toReal_nonneg
  by_contra h
  exact (not_le_of_gt hp) (restrictedCriticalPoint_le_of_density_pos (lt_of_not_ge h))

theorem restrictedDensity_pos_above_critical {d : ℕ} {S : Set (Vertex d)}
    {p : unitInterval} (hp : restrictedCriticalPoint d S < p) :
    0 < restrictedDensity d S p := by
  obtain ⟨q, hq, hqp⟩ := sInf_lt_iff.mp hp
  exact lt_of_lt_of_le hq (restrictedDensity_monotone d S hqp.le)

end NearCritical
