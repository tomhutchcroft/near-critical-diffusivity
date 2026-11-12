module

public import NearCritical.HalfSpaceSubcritical
public import NearCritical.HalfSpaceInteriorBounds

/-! NEW quantitative Step2 arm bounds and discharge of Step3's finite-arm
prerequisite. Cited inputs remain explicit; no new arm conclusion is a premise. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

lemma halfSpacePioneerMass_mono {d : ℕ} {p q : unitInterval} (hpq : p ≤ q)
    (i : Fin d) (m : ℤ) : halfSpacePioneerMass p i m ≤ halfSpacePioneerMass q i m := by
  unfold halfSpacePioneerMass
  apply ENNReal.tsum_le_tsum
  intro u
  by_cases hu : u i = -m
  · rw [ite_eq_left hu, ite_eq_left hu]
    exact percolation_increasing_event_mono (measurableSet_connectionToSetEvent _ _ _)
      (connectionToSetEvent_increasing _ _ _) hpq
  · simp only [ite_eq_right hu, le_refl]

/-- Extend the PROVED all-depth pioneer bound to all subcritical parameters.
The zero-layer estimate is supplied by Bounds/PioneerZeroLayer, never assumed. -/
theorem halfSpace_pioneer_uniform_subcritical {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (m : ℕ) :
    halfSpacePioneerMass p i (m : ℤ) ≤ ENNReal.ofReal (4 * B / (criticalPoint d : ℝ) ^ 2) := by
  let pHalf : unitInterval := ⟨(criticalPoint d : ℝ) / 2, by
    constructor
    · exact (half_pos hpc).le
    · linarith [(criticalPoint d).2.2]⟩
  have hHalfLE : pHalf ≤ criticalPoint d := by
    change (criticalPoint d : ℝ) / 2 ≤ (criticalPoint d : ℝ)
    linarith
  let q := max p pHalf
  have hpq : p ≤ q := le_max_left _ _
  have hqlo : (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) :=
    show (pHalf : ℝ) ≤ (q : ℝ) from le_max_right _ _
  have hqpc : q ≤ criticalPoint d := max_le hp hHalfLE
  exact (halfSpacePioneerMass_mono hpq i (m : ℤ)).trans
    (halfSpace_pioneer_uniform_of_weighted q i hB hb hpc hqlo (pioneers q hqlo hqpc) m)

/-- Explicit dimension/input-dependent constant for the source interior arm bound. -/
def halfSpaceInteriorArmConstant (d : ℕ) (A B b : ℝ) : ℝ :=
  8 * (4 * B / (criticalPoint d : ℝ) ^ 2) *
    (8 * A * (2 * B / (criticalPoint d : ℝ)) + Real.exp (b / 3))

private lemma interior_origin_scale_bound {C b N R t : ℝ}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hN : 0 < N) (hR : 0 < R)
    (ht : 0 ≤ t) (hNR : N ≤ 2 * R) :
    C / R ^ 3 * Real.exp (-(b / 6) * t * R) ≤
      8 * C / N ^ 3 * Real.exp (-(b / 12) * t * N) := by
  have hcube : C / R ^ 3 ≤ 8 * C / N ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hR 3) (pow_pos hN 3)).mpr
    calc
      C * N ^ 3 ≤ C * (2 * R) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le hNR 3) hC
      _ = _ := by ring
  have hdec : Real.exp (-(b / 6) * t * R) ≤ Real.exp (-(b / 12) * t * N) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hNR (mul_nonneg hb ht)
    nlinarith
  exact mul_le_mul hcube hdec (Real.exp_nonneg _) (by positivity)

/-- NEW source Step2, including the exponential factor and all subcritical p.
Only literal cited L1/L2 and pc>0 are premises; the interior arm bound is derived. -/
theorem halfSpace_interior_subcritical {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ))
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (x : Vertex d) (k n : ℕ)
    (hx : x i = (k : ℤ)) (hn : 1 ≤ n) (hk : 2 * k ≤ n) :
    percolation d p (connectionToSetEvent {z | 0 ≤ z i} x {z | (n : ℤ) ≤ z i}) ≤
      ENNReal.ofReal (halfSpaceInteriorArmConstant d A B b * (k + 1 : ℝ) / (n : ℝ) ^ 3 *
        Real.exp (-(b / 12) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ))) := by
  let U : ℝ := 4 * B / (criticalPoint d : ℝ) ^ 2
  let C : ℝ := 8 * A * (2 * B / (criticalPoint d : ℝ)) + Real.exp (b / 3)
  let t := Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hN : 0 < (n : ℝ) := by positivity
  have hkn : 2 * (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
  have hnz : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  calc
    _ ≤ ∑ j ∈ Finset.Icc 0 (x i),
        halfSpacePioneerMass p i (x i - j) * halfSpaceArmProbability p i ((n : ℤ) - j) :=
      halfSpace_interior_arm_le_pioneer_sum p i x (n : ℤ)
    _ ≤ ∑ _j ∈ Finset.Icc 0 (x i), ENNReal.ofReal
        (U * (8 * C / (n : ℝ) ^ 3 * Real.exp (-(b / 12) * t * (n : ℝ)))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 : 0 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjk : j ≤ (k : ℤ) := by simpa only [hx] using (Finset.mem_Icc.mp hj).2
      have hdiff : 0 ≤ x i - j := sub_nonneg.mpr (Finset.mem_Icc.mp hj).2
      have hψ : halfSpacePioneerMass p i (x i - j) ≤ ENNReal.ofReal U := by
        simpa only [Int.toNat_of_nonneg hdiff] using
          halfSpace_pioneer_uniform_subcritical i hB hb hpc pioneers p hp (x i - j).toNat
      let r : ℕ := ((n : ℤ) - j).toNat
      have hrz : (r : ℤ) = (n : ℤ) - j := Int.toNat_of_nonneg (by omega)
      have hr : 1 ≤ r := by omega
      have hR : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
      have hNR : (n : ℝ) ≤ 2 * (r : ℝ) := by
        have h : (n : ℤ) ≤ 2 * (r : ℤ) := by omega
        exact_mod_cast h
      have hθ := halfSpace_origin_subcritical i hA hB hb hpc criticalArm pioneers p hp r hr
      change halfSpaceArmProbability p i (r : ℤ) ≤ ENNReal.ofReal
        (C / (r : ℝ) ^ 3 * Real.exp (-(b / 6) * t * (r : ℝ))) at hθ
      have hθ' := hθ.trans (ENNReal.ofReal_le_ofReal
        (interior_origin_scale_bound hC hb.le hN hR ht hNR))
      rw [hrz] at hθ'
      exact (mul_le_mul' hψ hθ').trans_eq (ENNReal.ofReal_mul hU).symm
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (f := fun _j : ℤ ↦
        U * (8 * C / (n : ℝ) ^ 3 * Real.exp (-(b / 12) * t * (n : ℝ))))
        (fun _ _ ↦ by positivity), Finset.sum_const, nsmul_eq_mul]
      have hc : (Finset.Icc (0 : ℤ) (x i)).card = k + 1 := by rw [hx, Int.card_Icc]; omega
      rw [hc]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      dsimp [halfSpaceInteriorArmConstant, U, C, t]
      ring

lemma halfSpaceInteriorArmConstant_pos {d : ℕ} {A B b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hpc : 0 < (criticalPoint d : ℝ)) :
    0 < halfSpaceInteriorArmConstant d A B b := by
  unfold halfSpaceInteriorArmConstant
  positivity

/-- Actual real-probability form of the NEW full subcritical interior estimate. -/
theorem halfSpace_interior_subcritical_real {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ))
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (x : Vertex d) (k n : ℕ)
    (hx : x i = (k : ℤ)) (hn : 1 ≤ n) (hk : 2 * k ≤ n) :
    (percolation d p).real (connectionToSetEvent {z | 0 ≤ z i} x {z | (n : ℤ) ≤ z i}) ≤
      halfSpaceInteriorArmConstant d A B b * (k + 1 : ℝ) / (n : ℝ) ^ 3 *
        Real.exp (-(b / 12) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ)) := by
  have hK := halfSpaceInteriorArmConstant_pos (b := b) hA hB hpc
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (halfSpace_interior_subcritical i hA hB hb hpc criticalArm pioneers p hp x k n hx hn hk)
  have hnonneg : 0 ≤ halfSpaceInteriorArmConstant d A B b * (k + 1 : ℝ) / (n : ℝ) ^ 3 *
      Real.exp (-(b / 12) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ)) := by positivity
  rw [ENNReal.toReal_ofReal hnonneg] at h
  exact h

/-- Discarding the exponential gives the NEW subcritical arm input required
by entropic transfer. The actual probability estimate is a conclusion. -/
theorem halfSpace_interior_subcritical_power {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ))
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (x : Vertex d) (k n : ℕ)
    (hx : x i = (k : ℤ)) (hn : 1 ≤ n) (hk : 2 * k ≤ n) :
    (percolation d p).real (connectionToSetEvent {z | 0 ≤ z i} x {z | (n : ℤ) ≤ z i}) ≤
      halfSpaceInteriorArmConstant d A B b * ((k + 1 : ℝ) / (n : ℝ) ^ 3) := by
  have hK := halfSpaceInteriorArmConstant_pos (b := b) hA hB hpc
  have hexp : Real.exp (-(b / 12) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have hnonneg : 0 ≤ (b / 12) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ) := by positivity
      nlinarith)
  calc
    _ ≤ _ := halfSpace_interior_subcritical_real i hA hB hb hpc criticalArm pioneers p hp x k n hx hn hk
    _ ≤ halfSpaceInteriorArmConstant d A B b * (k + 1 : ℝ) / (n : ℝ) ^ 3 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ halfSpaceInteriorArmConstant d A B b * (k + 1 : ℝ) / (n : ℝ) ^ 3 by positivity)
    _ = _ := by ring

/-- Actual finite-domain arm bound: finite paths are included in the proved
full half-space event, for every counting radius R. -/
theorem finiteHalfSpaceArmProbability_upper_of_standard_inputs {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ))
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (k n R : ℕ)
    (hn : 1 ≤ n) (hk : 2 * k ≤ n) :
    finiteHalfSpaceArmProbability i p k n R ≤
      halfSpaceInteriorArmConstant d A B b * ((k + 1 : ℝ) / (n : ℝ) ^ 3) := by
  have hsub : finiteHalfSpaceArmEvent i k n R ⊆
      connectionToSetEvent {z | 0 ≤ z i} (halfSpaceArmBase i k) {z | (n : ℤ) ≤ z i} :=
    connectionToSetEvent_mono (fun _ h ↦ h.1) (Subset.refl _) _
  exact (measureReal_mono hsub).trans (halfSpace_interior_subcritical_power i hA hB hb hpc
    criticalArm pioneers p hp (halfSpaceArmBase i k) k n (by simp [halfSpaceArmBase]) hn hk)

/-- Both NEW lower-transfer fields are now DISCHARGED. Premises are the
literal cited critical arm/p-weighted positive-depth pioneer bounds and pc>0. -/
theorem halfSpaceLowerTransferPrerequisites_of_standard_inputs {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ))
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    HalfSpaceLowerTransferPrerequisites i (halfSpaceInteriorArmConstant d A B b)
      ((4 * B / (criticalPoint d : ℝ) ^ 2) *
        (4 * B / (criticalPoint d : ℝ) ^ 2 + 2 * B / ((criticalPoint d : ℝ) * b))) := by
  apply halfSpaceLowerTransferPrerequisites_of_arm_and_pioneers i hB hb hpc
  · intro q hqlo hqhi
    exact pioneers q hqlo hqhi.le
  · intro q k n R hn hk _ _ hqhi
    exact finiteHalfSpaceArmProbability_upper_of_standard_inputs i hA hB hb hpc
      criticalArm pioneers q hqhi.le k n R hn hk

/-- NEW supercritical half-space estimate with all earlier NEW arm/cluster
premises discharged. Only named STANDARD L1/L2/finite DM and 0<pc<1 remain. -/
theorem halfSpace_entropic_transfer_of_standard_inputs {d : ℕ} (i : Fin d)
    {E A B b : ℝ} (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval) (k n : ℕ), 1 ≤ n → 2 * k ≤ n →
      (criticalPoint d : ℝ) < (p : ℝ) →
      (p : ℝ) ≤ (criticalPoint d : ℝ) + ((n : ℝ) ^ 2)⁻¹ →
      (percolation d p).real (halfSpaceArmEvent i k n) ≤ K * ((k + 1 : ℝ) / (n : ℝ) ^ 3) := by
  apply halfSpace_entropic_transfer_of_arm_and_pioneers i hE
    (halfSpaceInteriorArmConstant_pos hA hB hpc) hB hb hpc hpc1 entropic
  · intro q hqlo hqhi
    exact pioneers q hqlo hqhi.le
  · intro q k n R hn hk _ _ hqhi
    exact finiteHalfSpaceArmProbability_upper_of_standard_inputs i hA hB hb hpc
      criticalArm pioneers q hqhi.le k n R hn hk

end NearCritical
