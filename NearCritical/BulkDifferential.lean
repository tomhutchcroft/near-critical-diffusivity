module

public import NearCritical.InhomogeneousExpectation
public import NearCritical.DifferentialInequality
public import NearCritical.LatticeCanonicalMinimizer
public import NearCritical.BulkDomain

/-! Masked differential inequality for the paper's bulk perturbation.
Only M varies. Mecke is used only on M, with its common parameter s;
the full energy still includes all issued bonds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset BernoulliCalculus
open scoped Classical

lemma finiteExpectationProfile_nonneg {E : Type*} [Fintype E] {q : E → ℝ}
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) {f : (E → Bool) → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ finiteExpectationProfile q f := by
  apply sum_nonneg
  intro ω _
  apply mul_nonneg (hf ω)
  apply prod_nonneg
  intro e _
  split <;> linarith [(hq e).1, (hq e).2]

lemma finiteExpectationProfile_mono {E : Type*} [Fintype E] {q : E → ℝ}
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) {f g : (E → Bool) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    finiteExpectationProfile q f ≤ finiteExpectationProfile q g := by
  apply sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_right (hfg ω)
  apply prod_nonneg
  intro e _
  split <;> linarith [(hq e).1, (hq e).2]

lemma finiteExpectationProfile_const_mul {E : Type*} [Fintype E]
    (q : E → ℝ) (c : ℝ) (f : (E → Bool) → ℝ) :
    finiteExpectationProfile q (fun ω ↦ c * f ω) = c * finiteExpectationProfile q f := by
  simp only [finiteExpectationProfile, mul_assoc, mul_sum]

lemma finiteExpectationProfile_finsetSum {E J : Type*} [Fintype E]
    (q : E → ℝ) (M : Finset J) (f : J → (E → Bool) → ℝ) :
    finiteExpectationProfile q (fun ω ↦ ∑ e ∈ M, f e ω) =
      ∑ e ∈ M, finiteExpectationProfile q (f e) := by
  simp only [finiteExpectationProfile, sum_mul]
  rw [sum_comm]

lemma weighted_finset_cauchySchwarz {J : Type*} (S : Finset J)
    (w f g : J → ℝ) (hw : ∀ j ∈ S, 0 ≤ w j) :
    (∑ j ∈ S, w j * f j * g j) ≤
      Real.sqrt (∑ j ∈ S, w j * (f j)^2) * Real.sqrt (∑ j ∈ S, w j * (g j)^2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun j ↦ Real.sqrt (w j) * f j) (fun j ↦ Real.sqrt (w j) * g j)
  have hc : (∑ j ∈ S, (Real.sqrt (w j) * f j) * (Real.sqrt (w j) * g j)) =
      ∑ j ∈ S, w j * f j * g j := by
    apply sum_congr rfl
    intro j hj
    calc
      _ = (Real.sqrt (w j))^2 * (f j * g j) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw j hj)]; ring
  have hsq (k : J → ℝ) : (∑ j ∈ S, (Real.sqrt (w j) * k j)^2) =
      ∑ j ∈ S, w j * (k j)^2 := by
    apply sum_congr rfl
    intro j hj
    rw [mul_pow, Real.sq_sqrt (hw j hj)]
  rw [hc, hsq f, hsq g] at h
  exact h

lemma profile_mask_cauchySchwarz {E : Type*} [Fintype E] {q : E → ℝ}
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (M : Finset E)
    (c f g : (E → Bool) → E → ℝ) (hc : ∀ ω e, 0 ≤ c ω e) :
    (∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ c ω e * f ω e * g ω e)) ≤
      Real.sqrt (∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ c ω e * (f ω e)^2)) *
      Real.sqrt (∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ c ω e * (g ω e)^2)) := by
  let w : E × (E → Bool) → ℝ := fun j ↦ profileWeight q j.2 * c j.2 j.1
  have hw (j : E × (E → Bool)) (_ : j ∈ M.product univ) : 0 ≤ w j := by
    apply mul_nonneg _ (hc j.2 j.1)
    apply prod_nonneg
    intro e _
    split <;> linarith [(hq e).1, (hq e).2]
  have h := weighted_finset_cauchySchwarz (M.product univ) w
    (fun j ↦ f j.2 j.1) (fun j ↦ g j.2 j.1) hw
  have hsum (k : (E → Bool) → E → ℝ) :
      (∑ j ∈ M.product univ, w j * k j.2 j.1) =
        ∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ c ω e * k ω e) := by
    have hp : (∑ j ∈ M.product univ, w j * k j.2 j.1) =
        ∑ e ∈ M, ∑ ω : E → Bool, w (e, ω) * k ω e := by
      convert! Finset.sum_product M (univ : Finset (E → Bool))
        (fun j ↦ w j * k j.2 j.1) using 1
    rw [hp]
    simp only [finiteExpectationProfile, w, profileWeight]
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro ω _
    ring
  have hleft : (∑ j ∈ M.product univ, w j * f j.2 j.1 * g j.2 j.1) =
      ∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ c ω e * f ω e * g ω e) := by
    simpa only [mul_assoc] using hsum (fun ω e ↦ f ω e * g ω e)
  rw [hleft, hsum (fun ω e ↦ (f ω e)^2), hsum (fun ω e ↦ (g ω e)^2)] at h
  exact h

/-- Analytic core of prop.inequality_diff_delta. Its full energy contains all E,
whereas the derivative and auxiliary term contain exactly M. -/
theorem finite_bulk_differential_inequality {E : Type*} [Fintype E]
    (M : Finset E) {p s r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hs : 0 < s) (hs1 : s < 1) (hr : 0 ≤ r)
    (F : (E → Bool) → ℝ) (g c : (E → Bool) → E → ℝ)
    (hc0 : ∀ ω e, 0 ≤ c ω e) (hc1 : ∀ ω e, c ω e ≤ 1)
    (henergy : ∀ ω, F ω = r * ∑ e, (if ω e then 1 else 0) * (g ω e)^2)
    (hinc : ∀ ω e, F (forceOpen e ω) - F ω =
      (r * c ω e) * g (forceOpen e ω) e * g ω e) :
    deriv (fun t ↦ finiteExpectationProfile (maskProfile M p t) F) s ≤
      Real.sqrt (finiteExpectationProfile (maskProfile M p s) F) *
        Real.sqrt (∑ e ∈ M, finiteExpectationProfile (maskProfile M p s)
          (fun ω ↦ r * c ω e * (g ω e)^2)) / (Real.sqrt s * (1-s)) := by
  let q := maskProfile M p s
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := by
    intro e
    dsimp [q, maskProfile]
    split <;> exact ⟨by positivity, by linarith⟩
  let A := finiteExpectationProfile q F
  let I := ∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ r * c ω e * (g (forceOpen e ω) e)^2)
  let B := ∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ r * c ω e * (g ω e)^2)
  have hAeq : A = r * finiteExpectationProfile q
      (fun ω ↦ ∑ e, (if ω e then 1 else 0) * (g ω e)^2) := by
    change finiteExpectationProfile q F = _
    rw [funext henergy, finiteExpectationProfile_const_mul]
  have hA : 0 ≤ A := by
    apply finiteExpectationProfile_nonneg hq
    intro ω
    rw [henergy]
    apply mul_nonneg hr
    apply sum_nonneg
    intro e _
    apply mul_nonneg _ (sq_nonneg _)
    split <;> norm_num
  have hIle : I ≤ r * ∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ (g (forceOpen e ω) e)^2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro e _
    rw [← finiteExpectationProfile_const_mul]
    apply finiteExpectationProfile_mono hq
    intro ω
    exact mul_le_mul_of_nonneg_right (by nlinarith [hc1 ω e]) (sq_nonneg _)
  have hmecke : s * (∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ (g (forceOpen e ω) e)^2)) =
      finiteExpectationProfile q (fun ω ↦ ∑ e ∈ M, (if ω e then 1 else 0) * (g ω e)^2) := by
    rw [finiteExpectationProfile_finsetSum, mul_sum]
    apply sum_congr rfl
    intro e he
    have h := finiteExpectationProfile_mask_mecke M p s e he (fun ω ↦ (g ω e)^2)
    simpa only [mul_comm] using h.symm
  have hpartial : finiteExpectationProfile q (fun ω ↦ ∑ e ∈ M, (if ω e then 1 else 0) * (g ω e)^2) ≤
      finiteExpectationProfile q (fun ω ↦ ∑ e, (if ω e then 1 else 0) * (g ω e)^2) := by
    apply finiteExpectationProfile_mono hq
    intro ω
    apply sum_le_sum_of_subset_of_nonneg (subset_univ M)
    intro e _ _
    apply mul_nonneg _ (sq_nonneg _)
    split <;> norm_num
  have hIA : I ≤ A / s := by
    apply hIle.trans
    apply (le_div_iff₀ hs).mpr
    rw [mul_assoc, mul_comm _ s, hmecke, hAeq]
    exact mul_le_mul_of_nonneg_left hpartial hr
  have hcs := profile_mask_cauchySchwarz hq M
    (fun ω e ↦ r * c ω e) (fun ω e ↦ g (forceOpen e ω) e) g
    (fun ω e ↦ mul_nonneg hr (hc0 ω e))
  have hsum : (∑ e ∈ M, finiteExpectationProfile q (fun ω ↦ F (forceOpen e ω)-F ω)) ≤
      Real.sqrt (A/s) * Real.sqrt B := by
    simp_rw [hinc]
    exact hcs.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hIA) (Real.sqrt_nonneg B))
  have hd := (finiteExpectationProfile_russo M p s (ne_of_lt hs1) F).deriv
  rw [hd]
  have hfinal := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (sub_nonneg.mpr hs1.le))
  change (1-s)⁻¹ * _ ≤ Real.sqrt A * Real.sqrt B / (Real.sqrt s * (1-s))
  calc
    _ ≤ (1-s)⁻¹ * (Real.sqrt (A/s) * Real.sqrt B) := hfinal
    _ = _ := by rw [Real.sqrt_div hA]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

end NearCritical

namespace NearCritical
open Finset BernoulliCalculus
open scoped Classical

/-- The bulk auxiliary summand retains the old configuration and full-domain
minimizer; only the edge summation is restricted. -/
def localMaskedB {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (η : IssuedBond U → Bool) : ℝ :=
  (U.card : ℝ)⁻¹ * ∑ e ∈ M,
    (1 - Network.binaryWeights η e) *
      ((issuedNetwork U).gradient
        ((issuedNetwork U).binaryMinimizer (twoFaceBoundary U i) (coordinateData i) η) e)^2 *
      if localTwoArm U i η e then 1 else 0

def annealedMaskedRelaxed {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (p s : ℝ) : ℝ :=
  finiteExpectationProfile (maskProfile M p s) (localRelaxedConductivity U i)

def annealedMaskedB {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (p s : ℝ) : ℝ :=
  finiteExpectationProfile (maskProfile M p s) (localMaskedB U i M)

lemma annealedMaskedRelaxed_self {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (p : ℝ) :
    annealedMaskedRelaxed U i M p p = annealedRelaxed U i p := by
  simp only [annealedMaskedRelaxed, maskProfile_self, finiteExpectationProfile_const,
    annealedRelaxed]

/-- The paper's new bulk perturbation inequality, with arbitrary finite mask M.
Pivotal support is discharged by the actual lattice two-arm theorem. -/
theorem annealedMaskedRelaxed_differential_inequality {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) (M : Finset (IssuedBond U))
    {p s : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 < s) (hs1 : s < 1) :
    deriv (annealedMaskedRelaxed U i M p) s ≤
      Real.sqrt (annealedMaskedRelaxed U i M p s) *
        Real.sqrt (annealedMaskedB U i M p s) / (Real.sqrt s * (1-s)) := by
  let G := issuedNetwork U
  let boundary := twoFaceBoundary U i
  let data : DomainVertex U → ℝ := coordinateData i
  let r : ℝ := (U.card : ℝ)⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr (Nat.cast_nonneg _)
  let g : (IssuedBond U → Bool) → IssuedBond U → ℝ :=
    fun η e ↦ G.gradient (G.binaryMinimizer boundary data η) e
  let c : (IssuedBond U → Bool) → IssuedBond U → ℝ :=
    fun η e ↦ (1 - Network.binaryWeights η e) * if localTwoArm U i η e then 1 else 0
  have hc0 : ∀ η e, 0 ≤ c η e := by
    intro η e
    apply mul_nonneg (sub_nonneg.mpr (Network.binaryWeights_le_one η e))
    split <;> norm_num
  have hc1 : ∀ η e, c η e ≤ 1 := by
    intro η e
    dsimp [c]
    split <;> have h := Network.binaryWeights_nonneg η e <;> nlinarith
  have henergy : ∀ η, r * G.binaryConductance boundary data η =
      r * ∑ e, (if η e then 1 else 0) * (g η e)^2 := by
    intro η
    rw [G.binaryConductance_eq_energy]
    rfl
  have hinc : ∀ η e, r * G.binaryConductance boundary data (forceOpen e η) -
      r * G.binaryConductance boundary data η = (r * c η e) * g (forceOpen e η) e * g η e := by
    intro η e
    by_cases hsupport : localTwoArm U i η e
    · have hm := G.binaryConductance_opening_identity boundary data η e
      dsimp [c, g]
      rw [ite_eq_left hsupport]
      nlinarith [congrArg (fun z : ℝ ↦ r * z) hm]
    · have heq : G.binaryConductance boundary data (forceOpen e η) =
          G.binaryConductance boundary data η := by
        by_contra hchange
        exact hsupport (localConductance_pivotal_support hU i η e hchange)
      simp [c, hsupport, heq]
  have h := finite_bulk_differential_inequality M hp hp1 hs hs1 hr
    (fun η ↦ r * G.binaryConductance boundary data η) g c hc0 hc1 henergy hinc
  have hF : (fun η ↦ r * G.binaryConductance boundary data η) = localRelaxedConductivity U i := by
    funext η
    rw [localRelaxedConductivity_eq_binary]
    dsimp [r, G, boundary, data]
    ring
  have hB : (∑ e ∈ M, finiteExpectationProfile (maskProfile M p s)
      (fun η ↦ r * c η e * (g η e)^2)) = annealedMaskedB U i M p s := by
    unfold annealedMaskedB localMaskedB
    rw [finiteExpectationProfile_const_mul, finiteExpectationProfile_finsetSum, mul_sum]
    apply sum_congr rfl
    intro e _
    rw [← finiteExpectationProfile_const_mul]
    congr 1
    funext η
    dsimp [c, g, r, G, boundary, data]
    ring
  rw [hF, hB] at h
  exact h

end NearCritical
