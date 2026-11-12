module
public import NearCritical.HomogeneousLogUpper
public import NearCritical.FiniteCubicUpper

/-! NEW uniform finite-volume prop.upper_log: actual rounded water cube,
seed admissibility and compact prefactor are discharged. Named STANDARD
literature inputs remain; no infinite-volume comparison is assumed or proved. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set

/-- Explicit logarithmic rounding comparison at the selected odd height. -/
lemma correlationHeight_log_bound {gap : ℝ} (hg : 0 < gap) (hs : gap ≤ 1/64) :
    1+Real.log (correlationHeight 1 gap : ℝ) ≤
      (1+1/Real.log 64)*|Real.log gap| := by
  have hs16 : gap ≤ 1/16 := by linarith
  have hg1 : gap ≤ 1 := by linarith
  have hu : 1 ≤ 1/gap := (le_div_iff₀ hg).mpr (by linarith)
  have hroot : Real.sqrt (1/gap) ≤ 1/gap := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith⟩
  have hhpos : (0:ℝ) < correlationHeight 1 gap := by
    exact_mod_cast oddCorrelationHeight_pos (Real.sqrt (1/gap))
  have hheight := (correlationHeight_bounds (by norm_num : (0:ℝ)<1) hg hs16).2
  have hlog : Real.log (correlationHeight 1 gap : ℝ) ≤ |Real.log gap| := by
    have h := Real.log_le_log hhpos (hheight.trans hroot)
    simpa [Real.log_div, abs_of_nonpos (Real.log_nonpos hg.le hg1)] using h
  have h64 : (0:ℝ) < Real.log 64 := Real.log_pos (by norm_num)
  have hlower : Real.log 64 ≤ |Real.log gap| := by
    have hi : 64 ≤ 1/gap := (le_div_iff₀ hg).mpr (by linarith)
    have h := Real.log_le_log (by norm_num : (0:ℝ)<64) hi
    simpa [Real.log_div, abs_of_nonpos (Real.log_nonpos hg.le hg1)] using h
  have hratio := div_le_div_of_nonneg_right hlower h64.le
  rw [div_self h64.ne', div_eq_mul_inv] at hratio
  simp only [one_div]
  nlinarith

/-- Uniform finite-volume logarithmic cubic bound from named standard inputs.
The SAME epsilon,D work for every transverse width. The cube radius is the
actual integer rounding, and no seed/window/probability envelope is a premise. -/
theorem homogeneous_finite_log_upper_of_standard_inputs {d : ℕ} (i : Fin d)
    {C G β E A B b : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β)
    (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d:ℝ)) (hpc1 : (criticalPoint d:ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ∀ (R : ℕ) (gap : ℝ), 0 < gap → gap ≤ ε →
      annealedRelaxed (waterCube d i (correlationRadius 1 gap) R) i
        ((criticalPoint d:ℝ)+gap) ≤ D*gap^3*|Real.log gap| := by
  obtain ⟨Q,c,hQ,hc,hupper⟩ := waterCube_homogeneous_log_upper_of_standard_inputs i
    hC hG hβ hE hA hB hb hpc hpc1 ordinary subordinary criticalArm pioneers entropic
  obtain ⟨ε0,hε0,hseed⟩ := correlation_seed_window hpc (by norm_num : (0:ℝ)<1) c
  let pc : ℝ := criticalPoint d
  let F : ℝ := (1/(Real.sqrt (pc/2)*(1-(pc+1)/2)))/2
  have htop : 0 < 1-(pc+1)/2 := by dsimp [pc]; linarith
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let J := 2/(c/2)^2+1
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  let Z := Q*(1+F*J)^2
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let L := 1+1/Real.log 64
  have hlog64 : (0:ℝ) < Real.log 64 := Real.log_pos (by norm_num)
  have hL : 0 < L := by dsimp [L]; positivity
  let D := 64*Z*L+1
  have hD : 0 < D := by dsimp [D]; positivity
  let ε := min ε0 (min (1/64) ((1-pc)/2))
  have hε : 0 < ε := by dsimp [ε,pc]; positivity
  refine ⟨ε,D,hε,hD,?_⟩
  intro R gap hg hsmall
  let H : ℝ := correlationHeight 1 gap
  let r := correlationRadius 1 gap
  let a := subcriticalSeedParameter pc c H
  let p := pc+gap
  have hs0 : gap ≤ ε0 := hsmall.trans (min_le_left _ _)
  have hs64 : gap ≤ 1/64 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs16 : gap ≤ 1/16 := by linarith
  have hstop : gap ≤ (1-pc)/2 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hseedwin := hseed gap hg hs0
  have ha : 0 < a := by dsimp [a,H,pc]; linarith [hseedwin.1]
  have hpbound : p ≤ (pc+1)/2 := by dsimp [p]; linarith
  have hp1 : p < 1 := by linarith
  have hp0 : 0 ≤ p := by dsimp [p,pc]; linarith
  let pU : unitInterval := ⟨p,hp0,hp1.le⟩
  have hh4 : 4 ≤ H := by
    exact correlationHeight_ge_of_gap_bound (by norm_num : (0:ℝ)<1) hg hs16
      (by norm_num : (0:ℝ)<4) (by norm_num; exact hs64)
  have heq : H = 2*(r:ℝ)+1 := correlationHeight_eq_radius 1 gap
  have hr : 1 ≤ r := by have h : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r; rw [heq] at hh4; exact_mod_cast (by linarith : (1:ℝ) ≤ r)
  have hwindow : p-pc ≤ 1/H^2 := by
    simpa only [p,add_sub_cancel_left] using correlationHeight_window (by norm_num : (0:ℝ)<1) hg hs16
  have Hupper := hupper r R pU hr (by change pc ≤ p; dsimp [p]; linarith) hp1
    (by simpa only [← heq] using hwindow) (by simpa only [← heq] using ha)
  have hfac : (1/(Real.sqrt a*(1-p)))/2 ≤ F :=
    compact_bulk_factor_le hpc hpc1 hseedwin.1 hpbound
  let f : ℝ := (1/(Real.sqrt a*(1-p)))/2
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hsq : (1+f*J)^2 ≤ (1+F*J)^2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_right hfac hJ
    change 1+f*J ≤ 1+F*J
    dsimp only [f]
    linarith only [h]
  have hlog : 0 ≤ 1+Real.log H := by have h := Real.log_nonneg (show 1 ≤ H by linarith); linarith
  have Hbound : annealedRelaxed (waterCube d i r R) i p ≤ Z*(1+Real.log H)/H^6 := by
    rw [← heq] at Hupper
    change annealedRelaxed (waterCube d i r R) i p ≤
      Q*(1+Real.log H)*(1+f*J)^2/H^6 at Hupper
    apply Hupper.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hm := mul_le_mul_of_nonneg_left hsq (mul_nonneg hQ.le hlog)
    dsimp [Z]
    nlinarith
  have hscale : 1/H^6 ≤ 64*gap^3 := by
    simpa only [one_pow,div_one] using correlationHeight_inverse_six (by norm_num : (0:ℝ)<1) hg hs16
  have hlogscale : 1+Real.log H ≤ L*|Real.log gap| := correlationHeight_log_bound hg hs64
  calc
    _ ≤ Z*(1+Real.log H)/H^6 := Hbound
    _ = Z*(1+Real.log H)*(1/H^6) := by ring
    _ ≤ Z*(L*|Real.log gap|)*(64*gap^3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlogscale hZ) hscale
        (by positivity) (by positivity)
    _ = (64*Z*L)*gap^3*|Real.log gap| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith : 64*Z*L ≤ D) (by positivity)) (abs_nonneg _)

end NearCritical
