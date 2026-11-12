module

public import NearCritical.Section10DifferenceSpectral
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Algebra.Ring.GeomSum
public import Lean.Elab.Tactic.Omega

/-! Uniform finite-horizon occupation for the actual paired lazy walk.
The singularity at the single origin is omitted only in the a.e. integral
comparison. No entrance or transience estimate is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

open MeasureTheory UnitAddTorus Set Metric
open scoped ComplexConjugate

/-- The displacement mass of the finite product of the paired step weights. -/
def differenceHistoryMass (D n : ℕ) (w : Fin D → ℤ) : ℝ := by
  classical
  exact ∑ h : Fin n → Option (Fin D) × Option (Fin D),
    if (∑ j, differenceStep D (h j)) = w then
      ∏ j, differenceStepWeight D (h j) else 0

private lemma historyMass_nonneg (D n : ℕ) (w : Fin D → ℤ) :
    0 ≤ differenceHistoryMass D n w := by
  classical
  unfold differenceHistoryMass
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · apply Finset.prod_nonneg
    intro j _
    unfold differenceStepWeight
    apply mul_nonneg <;> cases (h j).1 <;> cases (h j).2 <;>
      simp only [lazyCoordinateWeight] <;> positivity
  · exact le_rfl

private lemma historyMass_eq_coeff (D n : ℕ) (w : Fin D → ℤ) :
    (differenceHistoryMass D n w : ℂ) =
      mFourierCoeff (fun t => differenceCharacteristic D t ^ n) w := by
  classical
  rw [differenceHistory_fourierCoeff]
  unfold differenceHistoryMass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp [Complex.ofReal_prod]

private def greenCube (D : ℕ) : Set (Fin D → ℝ) :=
  {x | ∀ j, x j ∈ Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ) + 1)}

private lemma measurable_greenCube (D : ℕ) : MeasurableSet (greenCube D) := by
  have h := MeasurableSet.univ_pi' (fun _ : Fin D =>
    measurableSet_Ioc (a := -(1/2 : ℝ)) (b := -(1/2 : ℝ)+1))
  convert h using 1
  ext x
  simp [greenCube, Set.mem_pi]

private lemma abs_le_half_of_mem_cube {D : ℕ} {x : Fin D → ℝ}
    (hx : x ∈ greenCube D) (j : Fin D) : |x j| ≤ 1/2 :=
  abs_le.mpr ⟨(hx j).1.le, by linarith [(hx j).2]⟩

private lemma sq_norm_le_coordinate_sum {D : ℕ} (x : Fin D → ℝ) :
    ‖x‖^2 ≤ ∑ j, (x j)^2 := by
  have hsum : 0 ≤ ∑ j, (x j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnorm : ‖x‖ ≤ Real.sqrt (∑ j, (x j)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    apply (Real.le_sqrt (abs_nonneg _) hsum).mpr
    rw [sq_abs]
    exact Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin D))) =>
      sq_nonneg (x i)) (Finset.mem_univ j)
  have h := (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).mpr hnorm
  rwa [Real.sq_sqrt hsum] at h

private def greenMajorant (D : ℕ) (x : Fin D → ℝ) : ℝ :=
  ((D : ℝ)/4) * (‖x‖^2)⁻¹

private lemma integrable_greenMajorant {D : ℕ} (hD : 3 ≤ D) :
    IntegrableOn (greenMajorant D) (greenCube D) := by
  have hdim : Module.finrank ℝ (Fin D → ℝ) = D := by simp [Module.finrank_pi]
  have hd : 1 ≤ Module.finrank ℝ (Fin D → ℝ) := by omega
  have hα : (2 : ℝ) < Module.finrank ℝ (Fin D → ℝ) := by
    rw [hdim]
    exact_mod_cast (show 2 < D by omega)
  have hg : Measurable (greenMajorant D) :=
    measurable_const.mul (continuous_norm.pow 2).measurable.inv
  have hball : IntegrableOn (greenMajorant D) (ball (0 : Fin D → ℝ) 1) := by
    apply integrableOn_ball_of_norm_le_rpow (μ := volume) hd (C := (D : ℝ)/4) hα _
      hg.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two]
    exact le_of_eq (Real.norm_of_nonneg (by
      unfold greenMajorant
      positivity))
  apply hball.mono_set
  intro x hx
  rw [mem_ball, dist_zero_right]
  have hnorm : ‖x‖ ≤ 1/2 :=
    (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun j =>
      (Real.norm_eq_abs _).trans_le (abs_le_half_of_mem_cube hx j)
  linarith

private def cubeMultiplier (D : ℕ) (x : Fin D → ℝ) : ℝ :=
  (differenceCharacteristic D (fun j => (x j : AddCircle (1 : ℝ)))).re

private lemma continuous_cubeMultiplier (D : ℕ) : Continuous (cubeMultiplier D) := by
  have hq : Continuous (fun (x : Fin D → ℝ) j => (x j : AddCircle (1 : ℝ))) :=
    continuous_pi fun j => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply j)
  unfold cubeMultiplier differenceCharacteristic
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro a _
  exact continuous_const.mul ((mFourier (differenceStep D a)).continuous.comp hq)

private lemma cubeMultiplier_nonneg (D : ℕ) (x : Fin D → ℝ) : 0 ≤ cubeMultiplier D x := by
  simp only [cubeMultiplier, differenceCharacteristic_eq_normSq, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

private lemma geometric_majorized {D N : ℕ} (hD : 0 < D) {x : Fin D → ℝ}
    (hx : x ∈ greenCube D) (hx0 : x ≠ 0) :
    (∑ n ∈ Finset.range N, cubeMultiplier D x ^ n) ≤ greenMajorant D x := by
  have hgap : (4/(D : ℝ)) * ‖x‖^2 ≤ 1 - cubeMultiplier D x :=
    (mul_le_mul_of_nonneg_left (sq_norm_le_coordinate_sum x) (by positivity)).trans
      (differenceCharacteristic_spectral_gap hD x (abs_le_half_of_mem_cube hx))
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hbase : 0 < (4/(D : ℝ)) * ‖x‖^2 := by positivity
  have hden := hbase.trans_le hgap
  calc
    _ ≤ 1/(1 - cubeMultiplier D x) := by
      apply (le_div_iff₀ hden).mpr
      rw [geom_sum_mul_neg]
      exact sub_le_self _ (pow_nonneg (cubeMultiplier_nonneg D x) _)
    _ ≤ 1/((4/(D : ℝ)) * ‖x‖^2) :=
      one_div_le_one_div_of_le hbase hgap
    _ = _ := by
      unfold greenMajorant
      field_simp [hDr.ne', hnorm.ne'] <;> ring

private lemma norm_character {D : ℕ} (w : Fin D → ℤ) (t : UnitAddTorus (Fin D)) :
    ‖mFourier w t‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
    Finset.prod_const_one]

private lemma historyMass_le_integral (D n : ℕ) (w : Fin D → ℤ) :
    differenceHistoryMass D n w ≤ ∫ x in greenCube D, cubeMultiplier D x ^ n := by
  have h :=
    norm_integral_le_integral_norm (μ := (volume : Measure (Fin D → ℝ)).restrict (greenCube D))
      (fun x => mFourier (-w) (fun j => (x j : AddCircle (1 : ℝ))) •
        differenceCharacteristic D (fun j => (x j : AddCircle (1 : ℝ))) ^ n)
  unfold greenCube at h
  rw [← mFourierCoeff_eq_integral (a := fun _ : Fin D => -(1/2 : ℝ))
    (f := fun t => differenceCharacteristic D t ^ n) (n := w)] at h
  rw [← historyMass_eq_coeff, Complex.norm_of_nonneg (historyMass_nonneg D n w)] at h
  simpa only [smul_eq_mul, norm_mul, norm_pow, norm_character, one_mul,
    differenceCharacteristic_eq_normSq, Complex.norm_of_nonneg (Complex.normSq_nonneg _),
    greenCube, cubeMultiplier, Complex.ofReal_re] using h

/-- The total mass of visits to a fixed site up to any finite horizon is
bounded uniformly over the site and horizon in transverse dimension ≥3. -/
theorem differenceHistory_uniform_occupation {D : ℕ} (hD : 3 ≤ D) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (N : ℕ) (w : Fin D → ℤ),
      (∑ n ∈ Finset.range N, differenceHistoryMass D n w) ≤ G := by
  classical
  let G := ∫ x in greenCube D, greenMajorant D x
  refine ⟨G, integral_nonneg (fun x => by unfold greenMajorant; positivity), ?_⟩
  intro N w
  have hD' : 0 < D := by omega
  letI : Nonempty (Fin D) := ⟨⟨0, hD'⟩⟩
  let μ := (volume : Measure (Fin D → ℝ)).restrict (greenCube D)
  have hG : Integrable (greenMajorant D) μ := integrable_greenMajorant hD
  have hgeom : ∀ᵐ x ∂μ, (∑ n ∈ Finset.range N, cubeMultiplier D x ^ n) ≤
      greenMajorant D x := by
    filter_upwards [ae_restrict_mem (measurable_greenCube D),
      ae_restrict_of_ae (Measure.ae_ne volume (0 : Fin D → ℝ))] with x hx hx0
    exact geometric_majorized hD' hx hx0
  have hint (n : ℕ) (hn : n ∈ Finset.range N) :
      Integrable (fun x => cubeMultiplier D x ^ n) μ := by
    apply hG.mono' ((continuous_cubeMultiplier D).pow n).measurable.aestronglyMeasurable
    filter_upwards [hgeom] with x hx
    change ‖cubeMultiplier D x ^ n‖ ≤ greenMajorant D x
    rw [Real.norm_of_nonneg (pow_nonneg (cubeMultiplier_nonneg D x) n)]
    exact (Finset.single_le_sum (fun j _ => pow_nonneg (cubeMultiplier_nonneg D x) j) hn).trans hx
  calc
    _ ≤ ∑ n ∈ Finset.range N, ∫ x in greenCube D, cubeMultiplier D x ^ n :=
      Finset.sum_le_sum (fun n _ => historyMass_le_integral D n w)
    _ = ∫ x in greenCube D, ∑ n ∈ Finset.range N, cubeMultiplier D x ^ n :=
      (integral_finsetSum _ hint).symm
    _ ≤ G := integral_mono_ae (integrable_finsetSum _ hint) hG hgeom

end NearCritical.Section10
