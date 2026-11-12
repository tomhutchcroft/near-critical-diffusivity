module

public import NearCritical.Mecke
public import NearCritical.NetworkEdgeUpdate
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-! Analytic finite-volume differential-inequality machinery. Geometric
localization to the two-arm event is an explicit input, not proved here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset BernoulliCalculus

lemma finiteExpectation_nonneg {E : Type*} [Fintype E] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {f : (E → Bool) → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ finiteExpectation p f := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg (hf ω)
  apply Finset.prod_nonneg
  intro e _
  split <;> linarith

lemma finiteExpectation_mono {E : Type*} [Fintype E] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {f g : (E → Bool) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    finiteExpectation p f ≤ finiteExpectation p g := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_right (hfg ω)
  apply Finset.prod_nonneg
  intro e _
  split <;> linarith

lemma finiteExpectation_sum {E I : Type*} [Fintype E] [Fintype I]
    (p : ℝ) (f : I → (E → Bool) → ℝ) :
    finiteExpectation p (fun ω ↦ ∑ i, f i ω) = ∑ i, finiteExpectation p (f i) := by
  classical
  simp only [finiteExpectation, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma finiteExpectation_const_mul {E : Type*} [Fintype E]
    (p c : ℝ) (f : (E → Bool) → ℝ) :
    finiteExpectation p (fun ω ↦ c * f ω) = c * finiteExpectation p f := by
  classical
  simp only [finiteExpectation, mul_assoc, Finset.mul_sum]

/-- Weighted Cauchy--Schwarz on an arbitrary finite set, allowing zero weights. -/
lemma weighted_sum_cauchySchwarz {I : Type*} [Fintype I]
    (w f g : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i * g i) ≤
      Real.sqrt (∑ i, w i * (f i) ^ 2) * Real.sqrt (∑ i, w i * (g i) ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset I)
    (fun i ↦ Real.sqrt (w i) * f i) (fun i ↦ Real.sqrt (w i) * g i)
  have hcross (i : I) : (Real.sqrt (w i) * f i) * (Real.sqrt (w i) * g i) =
      w i * f i * g i := by
    calc
      _ = (Real.sqrt (w i)) ^ 2 * (f i * g i) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i)]; ring
  have hsqf (i : I) : (Real.sqrt (w i) * f i) ^ 2 = w i * (f i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hsqg (i : I) : (Real.sqrt (w i) * g i) ^ 2 = w i * (g i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  simpa only [hcross, hsqf, hsqg] using h

/-- Cauchy--Schwarz jointly over configurations and the finite edge set. -/
lemma finiteExpectation_edges_cauchySchwarz {E : Type*} [Fintype E] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (c f g : (E → Bool) → E → ℝ)
    (hc : ∀ ω e, 0 ≤ c ω e) :
    (∑ e, finiteExpectation p (fun ω ↦ c ω e * f ω e * g ω e)) ≤
      Real.sqrt (∑ e, finiteExpectation p (fun ω ↦ c ω e * (f ω e) ^ 2)) *
      Real.sqrt (∑ e, finiteExpectation p (fun ω ↦ c ω e * (g ω e) ^ 2)) := by
  classical
  let w : E × (E → Bool) → ℝ := fun i ↦ weight p i.2 * c i.2 i.1
  have hw (i : E × (E → Bool)) : 0 ≤ w i := by
    apply mul_nonneg _ (hc i.2 i.1)
    apply Finset.prod_nonneg
    intro e _
    split <;> linarith
  have h := weighted_sum_cauchySchwarz w (fun i ↦ f i.2 i.1) (fun i ↦ g i.2 i.1) hw
  have hsum (k : (E → Bool) → E → ℝ) :
      (∑ i : E × (E → Bool), w i * k i.2 i.1) =
        ∑ e, finiteExpectation p (fun ω ↦ c ω e * k ω e) := by
    simp only [Fintype.sum_prod_type, finiteExpectation, w, weight]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have hleft : (∑ i : E × (E → Bool), w i * f i.2 i.1 * g i.2 i.1) =
      ∑ e, finiteExpectation p (fun ω ↦ c ω e * f ω e * g ω e) := by
    simpa only [mul_assoc] using hsum (fun ω e ↦ f ω e * g ω e)
  rw [hleft, hsum (fun ω e ↦ (f ω e) ^ 2), hsum (fun ω e ↦ (g ω e) ^ 2)] at h
  exact h

/-- Mecke converts squared gradients in the forced-open configuration back
into the energy in the original configuration. -/
lemma mecke_square_sum {E : Type*} [Fintype E] (p : ℝ)
    (g : (E → Bool) → E → ℝ) :
    p * (∑ e, finiteExpectation p (fun ω ↦ (g (forceOpen e ω) e) ^ 2)) =
      finiteExpectation p (fun ω ↦ ∑ e, (if ω e then 1 else 0) * (g ω e) ^ 2) := by
  classical
  rw [finiteExpectation_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have h := finiteExpectation_mecke p e (fun ω ↦ (g ω e) ^ 2)
  simpa only [mul_comm] using h.symm

/-- Analytic core of `prop.inequality_diff`. The pointwise increment formula
`hinc` is the explicit geometric localization input. In the paper its cutoff is
(1-a(e)) times the two-arm indicator. No assertion of that localization is
hidden in this theorem. The parameter r is inverse volume. -/
theorem finite_differential_inequality {E : Type*} [Fintype E]
    {p r : ℝ} (hp : 0 < p) (hp1 : p < 1) (hr : 0 ≤ r)
    (F : (E → Bool) → ℝ) (g c : (E → Bool) → E → ℝ)
    (hc0 : ∀ ω e, 0 ≤ c ω e) (hc1 : ∀ ω e, c ω e ≤ 1)
    (henergy : ∀ ω, F ω = r * ∑ e, (if ω e then 1 else 0) * (g ω e) ^ 2)
    (hinc : ∀ ω e, F (forceOpen e ω) - F ω =
      (r * c ω e) * g (forceOpen e ω) e * g ω e) :
    deriv (fun q ↦ finiteExpectation q F) p ≤
      Real.sqrt (finiteExpectation p F) *
        Real.sqrt (∑ e, finiteExpectation p (fun ω ↦ r * c ω e * (g ω e) ^ 2)) /
        (Real.sqrt p * (1 - p)) := by
  classical
  let I : ℝ := ∑ e, finiteExpectation p (fun ω ↦ r * c ω e * (g (forceOpen e ω) e) ^ 2)
  let B : ℝ := ∑ e, finiteExpectation p (fun ω ↦ r * c ω e * (g ω e) ^ 2)
  let A : ℝ := finiteExpectation p F
  have hAeq : A = r * finiteExpectation p
      (fun ω ↦ ∑ e, (if ω e then 1 else 0) * (g ω e) ^ 2) := by
    change finiteExpectation p F = _
    rw [funext henergy]
    exact finiteExpectation_const_mul p r _
  have hA : 0 ≤ A := by
    apply finiteExpectation_nonneg hp.le hp1.le
    intro ω
    rw [henergy]
    apply mul_nonneg hr
    apply Finset.sum_nonneg
    intro e _
    apply mul_nonneg _ (sq_nonneg _)
    split <;> norm_num
  have hIle : I ≤ r * ∑ e, finiteExpectation p (fun ω ↦ (g (forceOpen e ω) e) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    rw [← finiteExpectation_const_mul]
    apply finiteExpectation_mono hp.le hp1.le
    intro ω
    have hrc : r * c ω e ≤ r := by nlinarith [hc1 ω e]
    exact mul_le_mul_of_nonneg_right hrc (sq_nonneg _)
  have hmecke := mecke_square_sum p g
  have hIA : I ≤ A / p := by
    apply hIle.trans
    apply le_of_eq
    apply (eq_div_iff hp.ne').mpr
    rw [hAeq]
    nlinarith [congrArg (fun z : ℝ ↦ r * z) hmecke]
  have hcs := finiteExpectation_edges_cauchySchwarz hp.le hp1.le
    (fun ω e ↦ r * c ω e) (fun ω e ↦ g (forceOpen e ω) e) g
    (fun ω e ↦ mul_nonneg hr (hc0 ω e))
  have hsum : (∑ e, finiteExpectation p (fun ω ↦ F (forceOpen e ω) - F ω)) ≤
      Real.sqrt (A / p) * Real.sqrt B := by
    simp_rw [hinc]
    exact hcs.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hIA) (Real.sqrt_nonneg B))
  have hd := (finiteExpectation_russo p (ne_of_lt hp1) F).deriv
  rw [hd]
  have hfinal := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (sub_nonneg.mpr hp1.le))
  change (1 - p)⁻¹ * _ ≤ Real.sqrt A * Real.sqrt B / (Real.sqrt p * (1 - p))
  calc
    _ ≤ (1 - p)⁻¹ * (Real.sqrt (A / p) * Real.sqrt B) := hfinal
    _ = _ := by rw [Real.sqrt_div hA]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

end NearCritical

namespace NearCritical.Network
open Finset NearCritical.BernoulliCalculus
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : NearCritical.Network V E)

/-- The auxiliary term b in `eq.defbb`, with an explicit support event and
inverse-volume factor r. The geometric support is supplied separately. -/
def binaryAuxiliary (boundary : Set V) (data : V → ℝ)
    (support : (E → Bool) → E → Prop) (r p : ℝ) : ℝ :=
  NearCritical.finiteExpectation p (fun η ↦ r * ∑ e,
    (1 - binaryWeights η e) *
      (G.gradient (G.binaryMinimizer boundary data η) e) ^ 2 *
      if support η e then 1 else 0)

/-- The differential inequality for actual finite-network conductance. The
hypothesis `hsupport` must be proved by the two-arm/pivotal geometry; this
conditional analytic theorem does not assert that missing geometric result. -/
theorem binaryConductance_differential_inequality_of_support
    (boundary : Set V) (data : V → ℝ) (support : (E → Bool) → E → Prop)
    {p r : ℝ} (hp : 0 < p) (hp1 : p < 1) (hr : 0 ≤ r)
    (hsupport : ∀ η e, G.binaryConductance boundary data (forceOpen e η) ≠
      G.binaryConductance boundary data η → support η e) :
    deriv (fun q ↦ NearCritical.finiteExpectation q
      (fun η ↦ r * G.binaryConductance boundary data η)) p ≤
      Real.sqrt (NearCritical.finiteExpectation p (fun η ↦ r * G.binaryConductance boundary data η)) *
        Real.sqrt (G.binaryAuxiliary boundary data support r p) /
        (Real.sqrt p * (1 - p)) := by
  classical
  let g : (E → Bool) → E → ℝ := fun η e ↦ G.gradient (G.binaryMinimizer boundary data η) e
  let c : (E → Bool) → E → ℝ := fun η e ↦
    (1 - binaryWeights η e) * if support η e then 1 else 0
  have hc0 : ∀ η e, 0 ≤ c η e := by
    intro η e
    apply mul_nonneg (sub_nonneg.mpr (binaryWeights_le_one η e))
    split <;> norm_num
  have hc1 : ∀ η e, c η e ≤ 1 := by
    intro η e
    dsimp [c]
    split <;> have h := binaryWeights_nonneg η e <;> nlinarith
  have henergy : ∀ η, r * G.binaryConductance boundary data η =
      r * ∑ e, (if η e then 1 else 0) * (g η e) ^ 2 := by
    intro η
    rw [G.binaryConductance_eq_energy]
    rfl
  have hinc : ∀ η e, r * G.binaryConductance boundary data (forceOpen e η) -
      r * G.binaryConductance boundary data η = (r * c η e) * g (forceOpen e η) e * g η e := by
    intro η e
    by_cases hs : support η e
    · have hm := G.binaryConductance_opening_identity boundary data η e
      dsimp [c, g]
      rw [ite_eq_left hs]
      nlinarith [congrArg (fun z : ℝ ↦ r * z) hm]
    · have heq : G.binaryConductance boundary data (forceOpen e η) =
          G.binaryConductance boundary data η := by
        by_contra h
        exact hs (hsupport η e h)
      simp [c, hs, heq]
  have h := NearCritical.finite_differential_inequality hp hp1 hr
    (fun η ↦ r * G.binaryConductance boundary data η) g c hc0 hc1 henergy hinc
  have hB : (∑ e, NearCritical.finiteExpectation p (fun η ↦ r * c η e * (g η e) ^ 2)) =
      G.binaryAuxiliary boundary data support r p := by
    rw [binaryAuxiliary, NearCritical.finiteExpectation_const_mul,
      NearCritical.finiteExpectation_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [← NearCritical.finiteExpectation_const_mul]
    congr 1
    funext η
    dsimp [c, g]
    ring
  rw [hB] at h
  exact h

/-- Volume-normalized form of the preceding conditional analytic theorem.
This is the normalization a(U)=energy(U)/|U| used in the source. -/
theorem binaryConductance_volume_differential_inequality_of_support
    (boundary : Set V) (data : V → ℝ) (support : (E → Bool) → E → Prop)
    {p volume : ℝ} (hp : 0 < p) (hp1 : p < 1) (hvolume : 0 < volume)
    (hsupport : ∀ η e, G.binaryConductance boundary data (forceOpen e η) ≠
      G.binaryConductance boundary data η → support η e) :
    deriv (fun q ↦ NearCritical.finiteExpectation q
      (fun η ↦ G.binaryConductance boundary data η / volume)) p ≤
      Real.sqrt (NearCritical.finiteExpectation p (fun η ↦ G.binaryConductance boundary data η / volume)) *
        Real.sqrt (G.binaryAuxiliary boundary data support volume⁻¹ p) /
        (Real.sqrt p * (1 - p)) := by
  have h := G.binaryConductance_differential_inequality_of_support boundary data support
    hp hp1 (inv_nonneg.mpr hvolume.le) hsupport
  have hf : (fun η ↦ volume⁻¹ * G.binaryConductance boundary data η) =
      (fun η ↦ G.binaryConductance boundary data η / volume) := by
    funext η
    ring
  rw [hf] at h
  exact h

end NearCritical.Network
