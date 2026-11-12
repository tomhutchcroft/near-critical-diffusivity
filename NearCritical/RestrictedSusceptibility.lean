module

public import NearCritical.HalfSpaceArmGeometry
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Actual countable first moment for restricted clusters. Domain-checked
connections agree with raw restricted reachability only when the starting
point belongs to the domain; this premise is retained explicitly. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Genuine extended nonnegative total connection mass under a configuration law. -/
def restrictedConnectionMass {d : ℕ} (μ : Measure (Configuration d))
    (S : Set (Vertex d)) (x : Vertex d) : ℝ≥0∞ :=
  ∑' y : Vertex d, μ (connectionToSetEvent S x {y})

/-- Domain-checked cardinality: zero outside S, actual cluster size inside S. -/
def restrictedClusterSize {d : ℕ} (S : Set (Vertex d)) (x : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑' y : Vertex d, if ω ∈ connectionToSetEvent S x {y} then 1 else 0

lemma restricted_reachable_iff_connection {d : ℕ} (S : Set (Vertex d))
    (ω : Configuration d) (x y : Vertex d) (hx : x ∈ S) :
    (restrictedGraph ω S).Reachable x y ↔ ω ∈ connectionToSetEvent S x {y} := by
  constructor
  · rintro ⟨w⟩
    exact ⟨hx,y,rfl,restrictedWalk_support w hx y w.end_mem_support,⟨w⟩⟩
  · rintro ⟨_,z,hz,_,hp⟩
    have hzy : z = y := hz
    simpa only [hzy] using hp

private lemma measurable_restricted_indicator {d : ℕ} (S : Set (Vertex d))
    (x y : Vertex d) :
    Measurable (fun ω : Configuration d ↦
      if ω ∈ connectionToSetEvent S x {y} then (1 : ℝ≥0∞) else 0) :=
  measurable_const.piecewise (measurableSet_connectionToSetEvent S x {y}) measurable_const

lemma measurable_restrictedClusterSize {d : ℕ} (S : Set (Vertex d)) (x : Vertex d) :
    Measurable (restrictedClusterSize S x) := by
  unfold restrictedClusterSize
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup (fun t : Finset (Vertex d) ↦
    t.measurable_fun_sum (fun y _ ↦ measurable_restricted_indicator S x y))

/-- Countable first-moment identity under the actual given law, without any
finite-expectation or probability bound premise. -/
theorem lintegral_restrictedClusterSize {d : ℕ} (μ : Measure (Configuration d))
    (S : Set (Vertex d)) (x : Vertex d) :
    ∫⁻ ω, restrictedClusterSize S x ω ∂μ = restrictedConnectionMass μ S x := by
  unfold restrictedClusterSize restrictedConnectionMass
  rw [lintegral_tsum (fun y ↦ (measurable_restricted_indicator S x y).aemeasurable)]
  apply tsum_congr
  intro y
  simpa only [Set.indicator, one_mul] using
    lintegral_indicator_const (μ := μ) (measurableSet_connectionToSetEvent S x {y}) (1 : ℝ≥0∞)

/-- Starting inside S is essential: raw restrictedGraph has a reflexive isolated
vertex even outside S, whereas the domain-checked size above is then zero. -/
lemma restrictedClusterSize_eq_count {d : ℕ} (S : Set (Vertex d))
    (ω : Configuration d) (x : Vertex d) (hx : x ∈ S) :
    restrictedClusterSize S x ω =
      Measure.count {y : Vertex d | (restrictedGraph ω S).Reachable x y} := by
  have hm : MeasurableSet {y : Vertex d | (restrictedGraph ω S).Reachable x y} :=
    (Set.to_countable _).measurableSet
  have hi := lintegral_indicator_const (μ := Measure.count) hm (1 : ℝ≥0∞)
  rw [lintegral_count] at hi
  calc
    _ = ∑' y : Vertex d, if (restrictedGraph ω S).Reachable x y then (1 : ℝ≥0∞) else 0 := by
      unfold restrictedClusterSize
      apply tsum_congr
      intro y
      rw [← restricted_reachable_iff_connection S ω x y hx]
    _ = _ := by simpa only [Set.indicator, Set.mem_ofPred_eq, one_mul] using hi

/-- Finite actual expected cluster size rules out the actual restricted infinite
cluster. The desired zero-event conclusion is derived, not assumed. -/
theorem restrictedInfiniteEvent_measure_zero_of_connectionMass_ne_top {d : ℕ}
    (μ : Measure (Configuration d)) (S : Set (Vertex d)) (h0 : (0 : Vertex d) ∈ S)
    (hfinite : restrictedConnectionMass μ S 0 ≠ ∞) :
    μ (restrictedInfiniteEvent d S) = 0 := by
  have hint : (∫⁻ ω, restrictedClusterSize S 0 ω ∂μ) ≠ ∞ := by
    rwa [lintegral_restrictedClusterSize]
  have hae := ae_lt_top (measurable_restrictedClusterSize S 0) hint
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hae] with ω hω
  intro hinf
  have htop : restrictedClusterSize S 0 ω = ∞ := by
    rw [restrictedClusterSize_eq_count S ω 0 h0]
    exact Measure.count_apply_infinite hinf
  exact hω.ne htop

end NearCritical
