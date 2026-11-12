module

public import NearCritical.BulkPercolation
public import NearCritical.SqrtDifferentialIntegration

/-! The bulk perturbation integration step in the paper's logarithm removal.
The square root is integrated rigorously even where the conductivity vanishes. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset BernoulliCalculus
open scoped Classical

lemma finiteExpectationProfile_mask_continuous {E : Type*} [Fintype E]
    (M : Finset E) (p : ℝ) (F : (E → Bool) → ℝ) :
    Continuous (fun s ↦ finiteExpectationProfile (maskProfile M p s) F) := by
  unfold finiteExpectationProfile
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro e _
  have hc : Continuous (fun s ↦ maskProfile M p s e) := by
    by_cases he : e ∈ M
    · simp only [maskProfile, ite_eq_left he]
      exact continuous_id
    · simp only [maskProfile, ite_eq_right he]
      exact continuous_const
  cases ω e
  · exact continuous_const.sub hc
  · exact hc

lemma annealedMaskedRelaxed_nonneg {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) {p s : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ annealedMaskedRelaxed U i M p s := by
  apply finiteExpectationProfile_nonneg _ (localRelaxedConductivity_nonneg U i)
  intro e
  dsimp [maskProfile]
  split <;> constructor <;> assumption

/-- The source's masked square-root integration, with all constants explicit.
Only the proved finite-volume quantities appear; no arm estimate is assumed. -/
theorem annealedMaskedRelaxed_sqrt_integral {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) (M : Finset (IssuedBond U))
    {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < 1) :
    Real.sqrt (annealedMaskedRelaxed U i M p b) ≤
      Real.sqrt (annealedMaskedRelaxed U i M p a) +
      ((1 / (Real.sqrt a * (1-b))) / 2) *
        ∫ x in a..b, Real.sqrt (annealedMaskedB U i M p x) := by
  apply sqrt_differential_integral_percolation_factor hab ha hb
    (finiteExpectationProfile_mask_continuous M p (localRelaxedConductivity U i)).continuousOn
  · intro x hx
    exact (finiteExpectationProfile_russo M p x
      (ne_of_lt (hx.2.trans hb)) (localRelaxedConductivity U i)).differentiableAt
  · intro x hx
    exact annealedMaskedRelaxed_nonneg U i M hp hp1 (ha.le.trans hx.1) (hx.2.trans hb.le)
  · exact (finiteExpectationProfile_mask_continuous M p (localMaskedB U i M)).continuousOn
  · intro x hx
    exact annealedMaskedRelaxed_differential_inequality hU i M hp hp1
      (ha.trans hx.1) (hx.2.trans hb)

/-- Source eq.upper_step1_delta's finite-volume perturbation term. At the upper
endpoint the inhomogeneous law agrees exactly with ordinary percolation. -/
theorem annealedBulkRelaxed_sqrt_integral {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) (h δ : ℝ)
    {a p : ℝ} (hap : a ≤ p) (ha : 0 < a) (hp : p < 1) :
    Real.sqrt (annealedRelaxed U i p) ≤
      Real.sqrt (annealedMaskedRelaxed U i (bulkBondMask U i h δ) p a) +
      ((1 / (Real.sqrt a * (1-p))) / 2) *
        ∫ x in a..p, Real.sqrt (annealedMaskedB U i (bulkBondMask U i h δ) p x) := by
  have H := annealedMaskedRelaxed_sqrt_integral hU i (bulkBondMask U i h δ)
    (ha.le.trans hap) hp.le hap ha hp
  simpa only [annealedMaskedRelaxed_self] using H

end NearCritical
