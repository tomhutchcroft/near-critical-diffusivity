module
public import NearCritical.Section8HeartCovariance

/-! Section 8, Lemma nisnmfs. Actual finite weighted heart observables and
conditional moments; no covariance, moment identity or variance bound premise. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

def eventIndicator {d : ℕ} (A : Set (Configuration d)) (ω : Configuration d) : ℝ :=
  if ω ∈ A then 1 else 0

def weightedHeartStatistic {d : ℕ} (Q H : Finset (Vertex d)) (f : Vertex d → ℝ)
    (ω : Configuration d) : ℝ := ∑ y ∈ Q, f y * eventIndicator (heartEvent Q H y) ω

def weightedHeartConditionalMean {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (f : Vertex d → ℝ) : ℝ :=
  (∫ ω, eventIndicator (heartEvent Q H x) ω * weightedHeartStatistic Q H f ω ∂percolation d p) /
    (percolation d p).real (heartEvent Q H x)

/-- Normalized conditional second moment minus squared conditional mean.
On a null conditioning event this definition assigns zero by real division. -/
def weightedHeartConditionalVariance {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (f : Vertex d → ℝ) : ℝ :=
  (∫ ω, eventIndicator (heartEvent Q H x) ω * (weightedHeartStatistic Q H f ω)^2 ∂percolation d p) /
    (percolation d p).real (heartEvent Q H x) - (weightedHeartConditionalMean p Q H x f)^2

private lemma indicator_mul {d : ℕ} (A B : Set (Configuration d)) (ω : Configuration d) :
    eventIndicator A ω * eventIndicator B ω = eventIndicator (A ∩ B) ω := by
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [eventIndicator,ha,hb]

private lemma integrable_indicator {d : ℕ} (p : unitInterval) (A : Set (Configuration d))
    (hA : MeasurableSet A) : Integrable (eventIndicator A) (percolation d p) := by
  have he : eventIndicator A = A.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : ω ∈ A <;> simp [eventIndicator,Set.indicator,h]
  rw [he]
  exact (integrable_const (μ := percolation d p) (1:ℝ)).indicator hA

private lemma integral_indicator {d : ℕ} (p : unitInterval) (A : Set (Configuration d))
    (hA : MeasurableSet A) :
    (∫ ω, eventIndicator A ω ∂percolation d p) = (percolation d p).real A := by
  simpa [eventIndicator,Set.indicator] using integral_indicator_one (μ := percolation d p) hA

/-- Literal finite weighted sum over actual fC, not an abstract random set. -/
lemma weightedHeartStatistic_eq_union {d : ℕ} (Q H : Finset (Vertex d)) (hH : H ⊆ Q)
    (f : Vertex d → ℝ) (ω : Configuration d) :
    weightedHeartStatistic Q H f ω = ∑ y ∈ Q, if y ∈ heartClusterUnion ω Q H then f y else 0 := by
  unfold weightedHeartStatistic
  apply Finset.sum_congr rfl
  intro y _hy
  rw [eventIndicator,heartEvent_iff_union_member Q H hH y ω]
  split <;> simp_all

/-- Finite internal-coordinate reconstruction derives integrability of EVERY
real function of the indicator and weighted statistic; no measurability input. -/
lemma integrable_weightedHeart_function {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (f : Vertex d → ℝ) (g : ℝ → ℝ → ℝ) :
    Integrable (fun ω => g (eventIndicator (heartEvent Q H x) ω) (weightedHeartStatistic Q H f ω))
      (percolation d p) := by
  have hi := percolation_cylinder_integrable d p (internalBondSet Q)
    (fun η => g (eventIndicator (heartEvent Q H x) (reconstructInterior Q η))
      (weightedHeartStatistic Q H f (reconstructInterior Q η)))
  apply hi.congr
  filter_upwards [] with ω
  have he (y : Vertex d) : ω ∈ heartEvent Q H y ↔
      reconstructInterior Q ((internalBondSet Q).restrict ω) ∈ heartEvent Q H y :=
    connectionToSetEvent_iff_of_internalBondSet_agree Q (Q : Set (Vertex d)) Subset.rfl
      ω _ (reconstructInterior_restrict_agree Q ω) y (H : Set (Vertex d))
  simp only [eventIndicator,weightedHeartStatistic,← he]

/-- Actual first restricted moment, source eq.suheboi. -/
theorem weightedHeart_first_moment {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (f : Vertex d → ℝ) :
    (∫ ω, eventIndicator (heartEvent Q H x) ω * weightedHeartStatistic Q H f ω ∂percolation d p) =
      ∑ y ∈ Q, f y * (percolation d p).real (heartPairEvent Q H x y) := by
  have he (ω : Configuration d) : eventIndicator (heartEvent Q H x) ω * weightedHeartStatistic Q H f ω =
      ∑ y ∈ Q, f y * eventIndicator (heartPairEvent Q H x y) ω := by
    unfold weightedHeartStatistic
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    calc
      _ = f y * (eventIndicator (heartEvent Q H x) ω * eventIndicator (heartEvent Q H y) ω) := by ring
      _ = _ := by rw [indicator_mul]; rfl
  simp_rw [he]
  have hi (y : Vertex d) : Integrable
      (fun ω => f y * eventIndicator (heartPairEvent Q H x y) ω) (percolation d p) :=
    (integrable_indicator p (heartPairEvent Q H x y)
      ((measurableSet_heartEvent Q H x).inter (measurableSet_heartEvent Q H y))).const_mul (f y)
  rw [integral_finsetSum Q (fun y _ => hi y)]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [integral_const_mul,integral_indicator p (heartPairEvent Q H x y)
    ((measurableSet_heartEvent Q H x).inter (measurableSet_heartEvent Q H y))]

/-- Actual second restricted moment, including the diagonal terms. -/
theorem weightedHeart_second_moment {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (f : Vertex d → ℝ) :
    (∫ ω, eventIndicator (heartEvent Q H x) ω * (weightedHeartStatistic Q H f ω)^2 ∂percolation d p) =
      ∑ y ∈ Q, ∑ z ∈ Q, f y*f z * (percolation d p).real (heartTripleEvent Q H x y z) := by
  have hm (y z : Vertex d) : MeasurableSet (heartTripleEvent Q H x y z) :=
    ((measurableSet_heartEvent Q H x).inter (measurableSet_heartEvent Q H y)).inter
      (measurableSet_heartEvent Q H z)
  have hi (y z : Vertex d) := (integrable_indicator p _ (hm y z)).const_mul (f y*f z)
  have he (ω : Configuration d) : eventIndicator (heartEvent Q H x) ω * (weightedHeartStatistic Q H f ω)^2 =
      ∑ y ∈ Q, ∑ z ∈ Q, f y*f z * eventIndicator (heartTripleEvent Q H x y z) ω := by
    unfold weightedHeartStatistic
    rw [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    calc
      _ = (f y*f z) * ((eventIndicator (heartEvent Q H x) ω * eventIndicator (heartEvent Q H y) ω) *
        eventIndicator (heartEvent Q H z) ω) := by ring
      _ = _ := by rw [indicator_mul,indicator_mul]; rfl
  simp_rw [he]
  rw [integral_finsetSum Q (fun y _ => integrable_finsetSum Q (fun z _ => hi y z))]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [integral_finsetSum Q (fun z _ => hi y z)]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [integral_const_mul,integral_indicator p _ (hm y z)]

/-- For positive conditioning mass, the definition is exactly the normalized
actual centered square, hence is the literal conditional variance. -/
theorem weightedHeart_variance_eq_centered {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (f : Vertex d → ℝ)
    (hq : 0 < (percolation d p).real (heartEvent Q H x)) :
    weightedHeartConditionalVariance p Q H x f =
      (∫ ω, eventIndicator (heartEvent Q H x) ω *
        (weightedHeartStatistic Q H f ω-weightedHeartConditionalMean p Q H x f)^2 ∂percolation d p) /
      (percolation d p).real (heartEvent Q H x) := by
  let m := weightedHeartConditionalMean p Q H x f
  have h2 := integrable_weightedHeart_function p Q H x f (fun a z => a*z^2)
  have h1 := integrable_weightedHeart_function p Q H x f (fun a z => a*z)
  have h0 := integrable_weightedHeart_function p Q H x f (fun a _ => a)
  have he : (∫ ω, eventIndicator (heartEvent Q H x) ω * (weightedHeartStatistic Q H f ω-m)^2 ∂percolation d p) =
      (∫ ω, eventIndicator (heartEvent Q H x) ω * (weightedHeartStatistic Q H f ω)^2 ∂percolation d p) -
      (2*m)*(∫ ω, eventIndicator (heartEvent Q H x) ω * weightedHeartStatistic Q H f ω ∂percolation d p) +
      m^2*(percolation d p).real (heartEvent Q H x) := by
    calc
      _ = ∫ ω, (eventIndicator (heartEvent Q H x) ω * (weightedHeartStatistic Q H f ω)^2 -
          (2*m)*(eventIndicator (heartEvent Q H x) ω * weightedHeartStatistic Q H f ω) +
          m^2*eventIndicator (heartEvent Q H x) ω) ∂percolation d p := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = _ := by
        have hadd := integral_add (h2.sub (h1.const_mul (2*m))) (h0.const_mul (m^2))
        have hsub := integral_sub h2 (h1.const_mul (2*m))
        simp only [Pi.add_apply,Pi.sub_apply] at hadd hsub
        rw [hadd,hsub,integral_const_mul,integral_const_mul,
          integral_indicator p _ (measurableSet_heartEvent Q H x)]
  change weightedHeartConditionalVariance p Q H x f = _ / _
  rw [he]
  dsimp [weightedHeartConditionalVariance,m,weightedHeartConditionalMean]
  field_simp [ne_of_gt hq] <;> ring

/-- Exact finite covariance expansion of the normalized actual variance. -/
theorem weightedHeart_variance_numerator {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (f : Vertex d → ℝ)
    (hq : 0 < (percolation d p).real (heartEvent Q H x)) :
    ((percolation d p).real (heartEvent Q H x))^2 * weightedHeartConditionalVariance p Q H x f =
      ∑ y ∈ Q, ∑ z ∈ Q, f y*f z *
        ((percolation d p).real (heartEvent Q H x)*(percolation d p).real (heartTripleEvent Q H x y z) -
        (percolation d p).real (heartPairEvent Q H x y)*(percolation d p).real (heartPairEvent Q H x z)) := by
  have hsquare : (∑ y ∈ Q, f y*(percolation d p).real (heartPairEvent Q H x y))^2 =
      ∑ y ∈ Q, ∑ z ∈ Q, f y*f z *
        ((percolation d p).real (heartPairEvent Q H x y)*(percolation d p).real (heartPairEvent Q H x z)) := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _hy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    ring
  calc
    _ = (percolation d p).real (heartEvent Q H x)*
        (∫ ω, eventIndicator (heartEvent Q H x) ω*(weightedHeartStatistic Q H f ω)^2 ∂percolation d p) -
        (∫ ω, eventIndicator (heartEvent Q H x) ω*weightedHeartStatistic Q H f ω ∂percolation d p)^2 := by
      dsimp [weightedHeartConditionalVariance,weightedHeartConditionalMean]
      field_simp [ne_of_gt hq] <;> ring
    _ = _ := by
      rw [weightedHeart_first_moment,weightedHeart_second_moment,hsquare,
        Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro z _hz
      ring

/-- Literal source Lemma nisnmfs. Null conditioning events are assigned zero;
for positive mass the preceding theorem identifies actual centered variance. -/
theorem weightedHeart_conditional_variance_bound {d : ℕ} (p : unitInterval)
    (Q H : Finset (Vertex d)) (x : Vertex d) (f : Vertex d → ℝ) (hf : ∀ y ∈ Q, 0 ≤ f y) :
    weightedHeartConditionalVariance p Q H x f ≤
      (∑ y ∈ Q, ∑ z ∈ Q, f y*f z*(percolation d p).real (heartBranchEvent Q H x y z)) /
        (percolation d p).real (heartEvent Q H x) := by
  by_cases hz : (percolation d p).real (heartEvent Q H x) = 0
  · simp [weightedHeartConditionalVariance,weightedHeartConditionalMean,hz]
  · have hq : 0 < (percolation d p).real (heartEvent Q H x) :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
    have hn := weightedHeart_variance_numerator p Q H x f hq
    have hb := heart_weighted_covariance_sum_le p Q H x f hf
    rw [← hn] at hb
    apply (le_div_iff₀ hq).mpr
    have hh : (percolation d p).real (heartEvent Q H x) *
        ((percolation d p).real (heartEvent Q H x)*weightedHeartConditionalVariance p Q H x f) ≤
        (percolation d p).real (heartEvent Q H x) *
          (∑ y ∈ Q, ∑ z ∈ Q, f y*f z*(percolation d p).real (heartBranchEvent Q H x y z)) := by
      nlinarith [hb]
    have h := (mul_le_mul_iff_right₀ hq).mp hh
    nlinarith

end NearCritical.Section8
