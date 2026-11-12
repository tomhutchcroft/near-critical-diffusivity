module

public import NearCritical.ChemicalDistance
public import NearCritical.InfiniteClusterHarris
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Topology.Order.LiminfLimsup

/-! The paper-specific chemical converse (lem.chem.converse), conditional only
on explicitly named standard uniqueness and connected-subsequence convergence
inputs. These inputs are propositions, not axioms or claims of discharged
literature theorems. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The extended intrinsic-distance sublevel event at a real threshold. A finite
integer distance must be at most t; disconnected vertices are excluded. -/
def chemicalShortEvent {d : ℕ} (x y : Vertex d) (t : ℝ) : Set (Configuration d) :=
  {ω | ∃ m : ℕ, (m : ℝ) ≤ t ∧ ω ∈ chemicalConnectionEvent x y m}

lemma measurableSet_chemicalShortEvent {d : ℕ} (x y : Vertex d) (t : ℝ) :
    MeasurableSet (chemicalShortEvent x y t) := by
  unfold chemicalShortEvent
  simp only [ofPred_exists, ofPred_and]
  exact MeasurableSet.iUnion fun m ↦ (MeasurableSet.const _).inter
    (measurableSet_chemicalConnectionEvent x y m)

lemma chemicalShortEvent_iff_distance {d : ℕ} (ω : Configuration d)
    (x y : Vertex d) (t : ℝ) :
    ω ∈ chemicalShortEvent x y t ↔ (openGraph ω).Reachable x y ∧
      ((chemicalDistance ω x y).toNat : ℝ) ≤ t := by
  constructor
  · rintro ⟨m, hm, hdist⟩
    rw [chemicalConnectionEvent_eq_distance] at hdist
    have hfin : chemicalDistance ω x y ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt hdist (ENat.natCast_lt_top m))
    have hnat : ((chemicalDistance ω x y).toNat : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast ENat.toNat_le_of_le_natCast hdist
    exact ⟨SimpleGraph.edist_ne_top_iff_reachable.mp hfin, hnat.trans hm⟩
  · rintro ⟨hconn, ht⟩
    refine ⟨(chemicalDistance ω x y).toNat, ht, ?_⟩
    rw [chemicalConnectionEvent_eq_distance]
    exact le_of_eq (ENat.natCast_toNat
      (SimpleGraph.edist_ne_top_iff_reachable.mpr hconn)).symm

/-- For nonnegative real thresholds this is exactly the source floor convention. -/
lemma chemicalShortEvent_eq_floor {d : ℕ} (x y : Vertex d) {t : ℝ} (ht : 0 ≤ t) :
    chemicalShortEvent x y t = chemicalConnectionEvent x y ⌊t⌋₊ := by
  ext ω
  constructor
  · rintro ⟨m, hm, hdist⟩
    exact chemicalConnectionEvent_mono_length x y ((Nat.le_floor_iff ht).mpr hm) hdist
  · intro h
    exact ⟨⌊t⌋₊, Nat.floor_le ht, h⟩

/-- Standard uniqueness input: any two vertices in infinite clusters are
connected, almost surely under the actual percolation measure. -/
def AEInfiniteClusterUniqueness (d : ℕ) (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂percolation d p, ∀ x y : Vertex d,
    ω ∈ infiniteClusterAtEvent x → ω ∈ infiniteClusterAtEvent y →
      (openGraph ω).Reachable x y

/-- Standard Garet–Marchand input, source eq.chem.timeconstant, Corollary 3.3
of garet2004asymptotic: normalized distances converge along connected n.
The toNat convention outside connections is irrelevant to this restricted filter. -/
def AEConnectedChemicalLimit (d : ℕ) (p : unitInterval) (u : Vertex d) (μ : ℝ) : Prop :=
  ∀ᵐ ω ∂percolation d p,
    Tendsto (fun n : ℕ ↦ ((chemicalDistance ω 0 (n • u)).toNat : ℝ) / (n : ℝ))
      (atTop ⊓ principal {n : ℕ | (openGraph ω).Reachable 0 (n • u)}) (𝓝 μ)

lemma chemical_eventually_short_on_infinite {d : ℕ} {p : unitInterval}
    {u : Vertex d} {μ a : ℝ} (huniq : AEInfiniteClusterUniqueness d p)
    (hlimit : AEConnectedChemicalLimit d p u μ) (ha : μ < a) :
    ∀ᵐ ω ∂percolation d p, ∀ᶠ n : ℕ in atTop,
      ω ∈ infiniteClusterAtEvent (0 : Vertex d) ∩ infiniteClusterAtEvent (n • u) →
        ω ∈ chemicalShortEvent 0 (n • u) (a * (n : ℝ)) := by
  filter_upwards [huniq, hlimit] with ω huniqω hlimitω
  have he := eventually_inf_principal.mp (hlimitω.eventually (gt_mem_nhds ha))
  filter_upwards [he, eventually_gt_atTop 0] with n hn hnpos
  intro hboth
  have hconn := huniqω 0 (n • u) hboth.1 hboth.2
  apply (chemicalShortEvent_iff_distance ω 0 (n • u) _).mpr
  refine ⟨hconn, ?_⟩
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  exact ((div_lt_iff₀ hnreal).mp (hn hconn)).le

/-- The bad events in the source proof have probability tending to zero. -/
theorem chemical_converse_bad_probability_tendsto {d : ℕ} {p : unitInterval}
    {u : Vertex d} {μ a : ℝ} (huniq : AEInfiniteClusterUniqueness d p)
    (hlimit : AEConnectedChemicalLimit d p u μ) (ha : μ < a) :
    Tendsto (fun n : ℕ ↦ (percolation d p).real
      ((infiniteClusterAtEvent (0 : Vertex d) ∩ infiniteClusterAtEvent (n • u)) \
        chemicalShortEvent 0 (n • u) (a * (n : ℝ)))) atTop (𝓝 0) := by
  have he := chemical_eventually_short_on_infinite huniq hlimit ha
  have hmeas (n : ℕ) : MeasurableSet
      ((infiniteClusterAtEvent (0 : Vertex d) ∩ infiniteClusterAtEvent (n • u)) \
        chemicalShortEvent 0 (n • u) (a * (n : ℝ))) :=
    ((measurableSet_infiniteClusterAtEvent 0).inter
      (measurableSet_infiniteClusterAtEvent (n • u))).diff
        (measurableSet_chemicalShortEvent 0 (n • u) _)
  have hzero := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := percolation d p) (L := atTop) (A := (∅ : Set (Configuration d)))
    MeasurableSet.empty hmeas (by
      filter_upwards [he] with ω hω
      filter_upwards [hω] with n hn
      simp only [Set.mem_sdiff, mem_empty_iff_false, iff_false]
      intro hbad
      exact hbad.2 (hn hbad.1))
  simp only [measure_empty] at hzero
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hzero
  simpa only [measure_empty, ENNReal.toReal_zero, Measure.real, Function.comp_def] using hr

/-- Source lem.chem.converse: the new probability deduction from explicitly
named standard uniqueness and Garet–Marchand convergence inputs. -/
theorem chemical_converse_liminf {d : ℕ} {p : unitInterval} {u : Vertex d} {μ a : ℝ}
    (huniq : AEInfiniteClusterUniqueness d p) (hlimit : AEConnectedChemicalLimit d p u μ)
    (ha : μ < a) :
    density d p ^ 2 ≤ liminf
      (fun n : ℕ ↦ (percolation d p).real (chemicalShortEvent 0 (n • u) (a * (n : ℝ)))) atTop := by
  let P := fun n : ℕ ↦ (percolation d p).real (chemicalShortEvent 0 (n • u) (a * (n : ℝ)))
  let B := fun n : ℕ ↦ (percolation d p).real
    ((infiniteClusterAtEvent (0 : Vertex d) ∩ infiniteClusterAtEvent (n • u)) \
      chemicalShortEvent 0 (n • u) (a * (n : ℝ)))
  have hB : Tendsto B atTop (𝓝 0) := chemical_converse_bad_probability_tendsto huniq hlimit ha
  have hbound (n : ℕ) : density d p ^ 2 ≤ P n + B n := by
    have hdecomp := measureReal_inter_add_sdiff₀ (μ := percolation d p)
      (s := infiniteClusterAtEvent (0 : Vertex d) ∩ infiniteClusterAtEvent (n • u))
      (measurableSet_chemicalShortEvent 0 (n • u) (a * (n : ℝ))).nullMeasurableSet
    have hsub := measureReal_mono (μ := percolation d p)
      (inter_subset_right :
        (infiniteClusterAtEvent (0 : Vertex d) ∩ infiniteClusterAtEvent (n • u)) ∩
          chemicalShortEvent 0 (n • u) (a * (n : ℝ)) ⊆ _)
    have hFKG := infiniteCluster_intersection_probability d p 0 (n • u)
    calc
      _ ≤ (percolation d p).real (infiniteClusterAtEvent 0 ∩ infiniteClusterAtEvent (n • u)) := hFKG
      _ = _ := hdecomp.symm
      _ ≤ _ := add_le_add hsub le_rfl
  have hupper : IsBoundedUnder (· ≤ ·) atTop P :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n ↦
      (measureReal_le_one : P n ≤ 1))
  have hlower : IsBoundedUnder (· ≥ ·) atTop P :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n ↦
      (measureReal_nonneg : 0 ≤ P n))
  apply (le_liminf_iff hupper.isCoboundedUnder_ge hlower).mpr
  intro b hb
  have he := hB.eventually (gt_mem_nhds (sub_pos.mpr hb))
  filter_upwards [he] with n hn
  change b < P n
  linarith [hbound n]

/-- The source lower bound on the liminf is strictly positive above pc. -/
theorem chemical_converse_liminf_pos {d : ℕ} {p : unitInterval} {u : Vertex d} {μ a : ℝ}
    (hp : criticalPoint d < p) (huniq : AEInfiniteClusterUniqueness d p)
    (hlimit : AEConnectedChemicalLimit d p u μ) (ha : μ < a) :
    0 < liminf
      (fun n : ℕ ↦ (percolation d p).real (chemicalShortEvent 0 (n • u) (a * (n : ℝ)))) atTop :=
  lt_of_lt_of_le (pow_pos (density_pos_above_critical hp) 2)
    (chemical_converse_liminf huniq hlimit ha)

/-- The literal floor-threshold source statement, including theta(p)^2>0.
The nonnegative mu input is supplied by the cited norm/time-constant theorem. -/
theorem chemical_converse {d : ℕ} {p : unitInterval} {u : Vertex d} {μ a : ℝ}
    (hp : criticalPoint d < p) (hμ : 0 ≤ μ)
    (huniq : AEInfiniteClusterUniqueness d p) (hlimit : AEConnectedChemicalLimit d p u μ)
    (ha : μ < a) :
    density d p ^ 2 ≤ liminf
      (fun n : ℕ ↦ (percolation d p).real
        (chemicalConnectionEvent 0 (n • u) ⌊a * (n : ℝ)⌋₊)) atTop ∧
      0 < density d p ^ 2 := by
  have h := chemical_converse_liminf huniq hlimit ha
  have hapos : 0 ≤ a := hμ.trans ha.le
  have heq : (fun n : ℕ ↦ (percolation d p).real
      (chemicalShortEvent 0 (n • u) (a * (n : ℝ)))) =
      (fun n : ℕ ↦ (percolation d p).real
        (chemicalConnectionEvent 0 (n • u) ⌊a * (n : ℝ)⌋₊)) := by
    funext n
    rw [chemicalShortEvent_eq_floor _ _ (mul_nonneg hapos (Nat.cast_nonneg n))]
  rw [heq] at h
  exact ⟨h, pow_pos (density_pos_above_critical hp) 2⟩

end NearCritical
