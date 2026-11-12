module

public import NearCritical.FiniteTwoPhaseSlabBootstrap
public import NearCritical.FiniteTwoPhaseSlabWeightedConvolutionSharp
public import NearCritical.TwoPhaseSlabExhaustion
public import NearCritical.TwoPhaseSlabMonotonicity

/-! NEW actual infinite two-phase slab exponential bound. The finite maximum
bound, sharp remaining-height convolution and actual ENNReal cutoff exhaustion
supply the estimate. Lower p is lifted to max(p,pc) by proved actual monotonicity,
so the final statement retains the whole source parameter range. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- The infinite mixed slab estimate for the p>=pc branch, with ONE amplitude,
rate normalization and window before all upper parameters and slab heights. -/
theorem twoPhaseSlabPioneerMass_nearCritical_above_critical {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (q : unitInterval), q ≤ criticalPoint d →
        ∀ (m n : ℕ) (p : unitInterval), criticalPoint d ≤ p →
          (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/((m+1 : ℝ)*(n+1 : ℝ)) →
          ∀ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∀ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
            twoPhaseSlabPioneerMass i p q m n k j ≤ ENNReal.ofReal
              (C*((n : ℝ)+1-(j : ℝ))*Real.exp
                (-C⁻¹*twoPhaseSlabDistance m k j*
                  Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)))) := by
  obtain ⟨M,c,ε0,hM,hc,hε0,hmax⟩ :=
    finiteTwoPhaseBoundaryMaximum_nearCritical i hB hb hpc hpc1 pioneers
  let C : ℝ := 1+4*M^2+1/c
  let ε : ℝ := min ε0 ((1-(criticalPoint d : ℝ))/2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hε : 0 < ε := lt_min hε0 (by linarith)
  have hεle : ε ≤ ε0 := min_le_left _ _
  have hεcap : ε ≤ (1-(criticalPoint d : ℝ))/2 := min_le_right _ _
  have hamp : (2*M)^2 ≤ C := by
    have hinv : 0 ≤ 1/c := by positivity
    dsimp [C]
    nlinarith
  have hrate : C⁻¹ ≤ c := by
    rw [← one_div]
    apply (div_le_iff₀ hC).mpr
    have hbase : 1/c ≤ C := by dsimp [C]; nlinarith [sq_nonneg M]
    have hprod := (div_le_iff₀ hc).mp hbase
    nlinarith
  let P : unitInterval := ⟨((criticalPoint d : ℝ)+1)/2, by
    constructor <;> linarith [(criticalPoint d).2.1,(criticalPoint d).2.2]⟩
  have hP : (P : ℝ) < 1 := by dsimp [P]; linarith
  have hpcP : criticalPoint d ≤ P := by
    change (criticalPoint d : ℝ) ≤ ((criticalPoint d : ℝ)+1)/2
    linarith
  refine ⟨C,ε,hC,hε,?_⟩
  intro q hq m n p hpcp hpwindow k _hk j hj
  let H : ℝ := (m+1 : ℝ)*(n+1 : ℝ)
  have hH1 : 1 ≤ H := by
    dsimp [H]
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m),(Nat.cast_nonneg n : (0 : ℝ) ≤ n),
      mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hdelta : ((p : ℝ)-(criticalPoint d : ℝ))*H ≤ ε := by
    apply (le_div_iff₀ hH).mp
    dsimp [H]
    linarith
  have hpP : p ≤ P := by
    have hgap : 0 ≤ (p : ℝ)-(criticalPoint d : ℝ) := sub_nonneg.mpr hpcp
    have hscale := mul_nonneg (sub_nonneg.mpr hH1) hgap
    change (p : ℝ) ≤ ((criticalPoint d : ℝ)+1)/2
    nlinarith
  have hpboot : (p : ℝ) ≤ (criticalPoint d : ℝ)+ε0/((m+1 : ℝ)*(n+1 : ℝ)) := by
    have hquot : (p : ℝ)-(criticalPoint d : ℝ) ≤ ε0/H :=
      (le_div_iff₀ hH).mpr (hdelta.trans hεle)
    dsimp [H] at hquot
    linarith
  have hqP : q ≤ P := hq.trans hpcP
  let L : ℝ := (n : ℝ)+1-(j : ℝ)
  have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  have hL : 0 ≤ L := by dsimp [L]; linarith
  let z : ℝ := twoPhaseSlabDistance m k j*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))
  have hz : 0 ≤ z := by
    dsimp [z,twoPhaseSlabDistance]
    exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hexp : Real.exp (-c*z) ≤ Real.exp (-C⁻¹*z) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hrate hz
    linarith
  have hcoef : L*(2*M)^2 ≤ C*L := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hamp hL
  rw [twoPhaseSlabPioneerMass_eq_iSup_finiteRows]
  apply iSup_le
  intro R
  apply ENNReal.ofReal_le_ofReal
  let U := latticeSupCube d R
  let x : Vertex d := Pi.single i k
  by_cases hx : x ∈ U
  · have hf := finiteTwoPhaseSlabRowMean_le_boundaryMaximum_sq_remaining_height_decay
      p q P hP hpP hqP c hc.le U i m n n le_rfl x hx j hj
    have hbound := hmax q hq U m n p hpcp hpboot
    have hnon := finiteTwoPhaseBoundaryMaximum_nonneg q c (p : ℝ) U i m n
    have hsquare := (sq_le_sq₀ hnon (by positivity : (0 : ℝ) ≤ 2*M)).mpr hbound
    have he : -(c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
        twoPhaseSlabDistance m k j) = -c*z := by dsimp [z]; ring
    have hfinite : finiteTwoPhaseSlabRowMean p q U i m n x j ≤
        L*(finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m n)^2*Real.exp (-c*z) := by
      simpa only [x,Pi.single_eq_same,he,L,Int.cast_natCast] using! hf
    have htarget : C*L*Real.exp (-C⁻¹*z) =
        C*((n : ℝ)+1-(j : ℝ))*Real.exp
          (-C⁻¹*twoPhaseSlabDistance m k j*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))) := by
      dsimp [L,z]
      congr 1
      congr 1
      ring
    apply (hfinite.trans ?_).trans_eq htarget
    calc
      _ ≤ (L*(2*M)^2)*Real.exp (-c*z) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare hL) (Real.exp_nonneg _)
      _ ≤ C*L*Real.exp (-C⁻¹*z) := mul_le_mul hcoef hexp
        (Real.exp_nonneg _) (mul_nonneg hC.le hL)
  · have hout : x ∉ finiteHeightSlab i 0 (n : ℤ) ∩ (U : Set (Vertex d)) := fun h ↦ hx h.2
    rw [finiteTwoPhaseSlabRowMean_zero_of_start_outside p q U i m n x j hout]
    exact mul_nonneg (mul_nonneg hC.le hL) (Real.exp_nonneg _)

/-- Full source range, including p<pc and p=0: increasing the ACTUAL lower
phase rate to max(p,pc) preserves the same upper q, interface, top and events.
The sole probability inputs are the explicit standard pioneer input/pc bounds. -/
theorem twoPhaseSlabPioneerMass_nearCritical {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (q : unitInterval), q ≤ criticalPoint d →
        ∀ (m n : ℕ) (p : unitInterval),
          (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/((m+1 : ℝ)*(n+1 : ℝ)) →
          ∀ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∀ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
            twoPhaseSlabPioneerMass i p q m n k j ≤ ENNReal.ofReal
              (C*((n : ℝ)+1-(j : ℝ))*Real.exp
                (-C⁻¹*twoPhaseSlabDistance m k j*
                  Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)))) := by
  obtain ⟨C,ε,hC,hε,hbound⟩ :=
    twoPhaseSlabPioneerMass_nearCritical_above_critical i hB hb hpc hpc1 pioneers
  refine ⟨C,ε,hC,hε,?_⟩
  intro q hq m n p hpwindow k hk j hj
  let p' : unitInterval := max p (criticalPoint d)
  have hpp' : p ≤ p' := le_max_left _ _
  have hpcp' : criticalPoint d ≤ p' := le_max_right _ _
  have hp'window : (p' : ℝ) ≤ (criticalPoint d : ℝ)+ε/((m+1 : ℝ)*(n+1 : ℝ)) := by
    change max (p : ℝ) (criticalPoint d : ℝ) ≤ _
    apply max_le hpwindow
    exact le_add_of_nonneg_right (by positivity)
  exact (twoPhaseSlabPioneerMass_mono_lower_parameter i q m n k j hpp').trans
    (hbound q hq m n p' hpcp' hp'window k hk j hj)

end NearCritical
