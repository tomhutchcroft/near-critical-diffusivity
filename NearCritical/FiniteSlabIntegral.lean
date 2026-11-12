module

public import NearCritical.FiniteSlabDifferential
public import NearCritical.PercolationEndpoints
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! NEW finite-cutoff source eq.A.integral prerequisite. Only genuine finite
row polynomials are differentiated. The actual Russo upper expression is a
continuous finite polynomial envelope, not an assumed infinite-mass derivative. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

private lemma restrictedGraph_allClosed (d : ℕ) (S : Set (Vertex d)) :
    restrictedGraph (fun _ : Bond d ↦ false) S = ⊥ := by
  ext x y
  simp [restrictedGraph, openGraph_allClosed]

/-- At the actual p=0 law, distinct endpoints cannot be connected in the
confined graph. Domain-checked nil paths are not incorrectly discarded. -/
lemma finiteSlabConnection_probability_zero_of_ne {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x y : Vertex d) (hxy : x ≠ y) :
    (percolation d 0).real (finiteSlabConnectionEvent U i m n x y) = 0 := by
  have hnot : (fun _ : Bond d ↦ false) ∉ finiteSlabConnectionEvent U i m n x y := by
    rintro ⟨_, z, hz, _, hpath⟩
    have hzy : z = y := hz
    subst z
    rw [restrictedGraph_allClosed, SimpleGraph.reachable_bot] at hpath
    exact hxy hpath
  simp [Measure.real, Measure.dirac_apply', finiteSlabConnectionEvent_measurable, hnot]

/-- The actual finite polynomial has zero initial value when the source and
target layers are distinct, regardless of cutoff membership or slab endpoints. -/
theorem finiteSlabRowExpectation_zero_of_layer_ne {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) (hxj : x i ≠ j) :
    finiteSlabRowExpectation 0 U i m n x j = 0 := by
  have hzero := finiteSlabRowMean_eq_expectation (0 : unitInterval) U i m n x j
  rw [Set.Icc.coe_zero] at hzero
  rw [← hzero]
  unfold finiteSlabRowMean
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hyj : y i = j
  · rw [ite_eq_left hyj]
    apply finiteSlabConnection_probability_zero_of_ne U i m n x y
    intro hxy
    exact hxj (by simpa only [hxy] using hyj)
  · exact ite_eq_right hyj

/-- Literal source k<n zero initial value; equality k=n is excluded because
an actual in-domain nil connection may have nonzero initial value. -/
theorem finiteSlab_top_row_zero {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (n k : ℤ) (hkn : k < n) :
    finiteSlabRowExpectation 0 U i 0 n (Pi.single i k) n = 0 := by
  apply finiteSlabRowExpectation_zero_of_layer_ne
  simpa only [Pi.single_eq_same] using ne_of_lt hkn

private lemma finiteSlabRowDerivative_continuous {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    Continuous (fun q : ℝ ↦ (finiteSlabRowPolynomial U i m n x j).derivative.eval q) := by
  simpa only [Polynomial.coe_aeval_eq_eval] using
    ((finiteSlabRowPolynomial U i m n x j).derivative.contDiff_aeval
      (𝕜 := ℝ) (1 : WithTop ℕ∞)).continuous

/-- Finite FTC with the EXHIBITED polynomial derivative, on arbitrary real
oriented intervals. There is no regularity premise for an infinite A. -/
theorem finiteSlabRowExpectation_sub_eq_integral_derivative {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) (a b : ℝ) :
    finiteSlabRowExpectation b U i m n x j - finiteSlabRowExpectation a U i m n x j =
      ∫ q in a..b, (finiteSlabRowPolynomial U i m n x j).derivative.eval q := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun q _ ↦ finiteSlabRowExpectation_hasDerivAt q U i m n x j)
  exact (finiteSlabRowDerivative_continuous U i m n x j).intervalIntegrable a b

/-- Clearly generic analytic envelope interface: a POINTWISE derivative
bound and genuine integrability imply its integral bound for the actual finite
polynomial. No boundary ratio or desired integrated estimate is a premise. -/
theorem finiteSlabRowExpectation_sub_le_integral_envelope {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ q ∈ Ioo a b,
      deriv (fun s ↦ finiteSlabRowExpectation s U i m n x j) q ≤ g q) :
    finiteSlabRowExpectation b U i m n x j - finiteSlabRowExpectation a U i m n x j ≤
      ∫ q in a..b, g q := by
  rw [finiteSlabRowExpectation_sub_eq_integral_derivative]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hab
    ((finiteSlabRowDerivative_continuous U i m n x j).intervalIntegrable a b) hg
  intro q hq
  rw [← (finiteSlabRowExpectation_hasDerivAt q U i m n x j).deriv]
  exact hbound q hq

/-- The generic envelope interface from ZERO for a distinct target layer. -/
theorem finiteSlabRowExpectation_le_integral_envelope_from_zero {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    (hxj : x i ≠ j) {p : ℝ} (hp : 0 ≤ p) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 p)
    (hbound : ∀ q ∈ Ioo 0 p,
      deriv (fun s ↦ finiteSlabRowExpectation s U i m n x j) q ≤ g q) :
    finiteSlabRowExpectation p U i m n x j ≤ ∫ q in 0..p, g q := by
  have h := finiteSlabRowExpectation_sub_le_integral_envelope U i m n x j hp g hg hbound
  simpa only [finiteSlabRowExpectation_zero_of_layer_ne U i m n x j hxj, sub_zero] using h

/-- Canonical finite polynomial extension of the ACTUAL two-orientation
Russo edge/row upper expression. Its unit-interval interpretation is below. -/
def finiteSlabRussoRowEnvelope {d : ℕ} (q : ℝ) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) : ℝ :=
  ∑ e : internalBondSet U,
    (BK.eventProbability q (finiteSlabLocalConnectionEvent U i m n x e.val.1) *
      finiteSlabRowExpectation q U i m n (bondTip e.val) j +
    BK.eventProbability q (finiteSlabLocalConnectionEvent U i m n x (bondTip e.val)) *
      finiteSlabRowExpectation q U i m n e.val.1 j)

private lemma finiteSlab_eventProbability_continuous {E : Type*} [Fintype E]
    (A : Set (E → Bool)) : Continuous (fun q : ℝ ↦ BK.eventProbability q A) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (finiteExpectation_hasDerivAt q (fun η ↦ if η ∈ A then (1 : ℝ) else 0)).continuousAt

/-- The ACTUAL Russo upper expression has a continuous finite polynomial
extension, so its interval integral is genuinely integrable. -/
theorem finiteSlabRussoRowEnvelope_continuous {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    Continuous (fun q ↦ finiteSlabRussoRowEnvelope q U i m n x j) := by
  unfold finiteSlabRussoRowEnvelope
  apply continuous_finsetSum
  intro e he
  apply Continuous.add
  · exact (finiteSlab_eventProbability_continuous _).mul
      (finiteSlabRowExpectation_contDiff 1 U i m n (bondTip e.val) j).continuous
  · exact (finiteSlab_eventProbability_continuous _).mul
      (finiteSlabRowExpectation_contDiff 1 U i m n e.val.1 j).continuous

/-- On the unit interval every factor is exactly its actual infinite-law
finite-domain probability/row mean. No cutoff stationarity is used. -/
theorem finiteSlabRussoRowEnvelope_eq_actual {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteSlabRussoRowEnvelope (p : ℝ) U i m n x j =
      ∑ e : internalBondSet U,
        ((percolation d p).real (finiteSlabConnectionEvent U i m n x e.val.1) *
          finiteSlabRowMean p U i m n (bondTip e.val) j +
        (percolation d p).real (finiteSlabConnectionEvent U i m n x (bondTip e.val)) *
          finiteSlabRowMean p U i m n e.val.1 j) := by
  simp only [finiteSlabRussoRowEnvelope, BK.eventProbability, ← finiteSlabConnectionEvent_probability,
    ← finiteSlabRowMean_eq_expectation]

/-- Specialization of the ALREADY PROVED actual finite Russo inequality. -/
theorem finiteSlabRowExpectation_deriv_le_russoEnvelope {d : ℕ}
    (p : unitInterval) (hp : (p : ℝ) ≠ 1) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    deriv (fun s ↦ finiteSlabRowExpectation s U i m n x j) (p : ℝ) ≤
      finiteSlabRussoRowEnvelope (p : ℝ) U i m n x j := by
  rw [finiteSlabRussoRowEnvelope_eq_actual]
  exact finiteSlabRowExpectation_deriv_le p hp U i m n x j

/-- Actual finite Russo integration between TWO parameters, including upper
endpoint1: the reciprocal guard is discharged only on the open interval. -/
theorem finiteSlabRowExpectation_sub_le_integral_russo {d : ℕ}
    (a b : unitInterval) (hab : a ≤ b) (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteSlabRowExpectation (b : ℝ) U i m n x j -
      finiteSlabRowExpectation (a : ℝ) U i m n x j ≤
        ∫ q in (a : ℝ)..(b : ℝ), finiteSlabRussoRowEnvelope q U i m n x j := by
  apply finiteSlabRowExpectation_sub_le_integral_envelope U i m n x j hab
    (fun q ↦ finiteSlabRussoRowEnvelope q U i m n x j)
    ((finiteSlabRussoRowEnvelope_continuous U i m n x j).intervalIntegrable _ _)
  intro q hq
  let p : unitInterval := ⟨q, a.2.1.trans hq.1.le, hq.2.le.trans b.2.2⟩
  exact finiteSlabRowExpectation_deriv_le_russoEnvelope p
    (ne_of_lt (hq.2.trans_le b.2.2)) U i m n x j

/-- Finite counterpart of source eq.A.integral: actual row at p is at most
the integral of its actual two-orientation edge/row Russo upper expression.
The initial value zero is PROVED from distinct layers, not assumed. -/
theorem finiteSlabRowMean_le_integral_russo {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    (hxj : x i ≠ j) :
    finiteSlabRowMean p U i m n x j ≤
      ∫ q in 0..(p : ℝ), finiteSlabRussoRowEnvelope q U i m n x j := by
  rw [finiteSlabRowMean_eq_expectation]
  have h := finiteSlabRowExpectation_sub_le_integral_russo (0 : unitInterval) p p.2.1 U i m n x j
  rw [Set.Icc.coe_zero] at h
  change finiteSlabRowExpectation (p : ℝ) U i m n x j -
    finiteSlabRowExpectation 0 U i m n x j ≤
      ∫ q in 0..(p : ℝ), finiteSlabRussoRowEnvelope q U i m n x j at h
  simpa only [finiteSlabRowExpectation_zero_of_layer_ne U i m n x j hxj, sub_zero] using h

/-- Literal finite top-target specialization k<n, with canonical cutoff and
actual source coordinate. Passage to infinite A and half-prefactor estimates
remain separate obligations; no infinite derivative is introduced. -/
theorem finiteSlab_top_row_le_integral_russo {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (n k : ℤ) (hkn : k < n) :
    finiteSlabRowMean p U i 0 n (Pi.single i k) n ≤
      ∫ q in 0..(p : ℝ), finiteSlabRussoRowEnvelope q U i 0 n (Pi.single i k) n := by
  apply finiteSlabRowMean_le_integral_russo
  simpa only [Pi.single_eq_same] using ne_of_lt hkn

end NearCritical
