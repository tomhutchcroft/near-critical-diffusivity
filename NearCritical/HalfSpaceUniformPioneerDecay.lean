module

public import NearCritical.HalfSpaceInteriorArmBounds
public import NearCritical.SlabPioneerExhaustion

/-! All-parameter, all-depth pioneer decay from literal weighted L2.
This is a prerequisite, not the NEW half-slab boundary-prefactor estimate. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped ENNReal

/-- Preserve the exponential factor when extending the cited positive-height,
p-weighted input to every subcritical parameter and to depth zero. -/
theorem halfSpace_pioneer_exponential_uniform_subcritical {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (m : ℕ) :
    halfSpacePioneerMass p i (m : ℤ) ≤ ENNReal.ofReal
      ((4 * B / (criticalPoint d : ℝ)^2) *
        Real.exp (-(b/2) * Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) * (m : ℝ))) := by
  by_cases hm : m = 0
  · subst m
    simpa using halfSpace_pioneer_uniform_subcritical i hB hb hpc pioneers p hp 0
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  let pHalf : unitInterval := ⟨(criticalPoint d : ℝ)/2, by
    constructor
    · exact (half_pos hpc).le
    · linarith [(criticalPoint d).2.2]⟩
  have hHalfLE : pHalf ≤ criticalPoint d := by
    change (criticalPoint d : ℝ)/2 ≤ (criticalPoint d : ℝ)
    linarith
  let q := max p pHalf
  have hpq : p ≤ q := le_max_left _ _
  have hqlo : (criticalPoint d : ℝ)/2 ≤ (q : ℝ) :=
    show (pHalf : ℝ) ≤ (q : ℝ) from le_max_right _ _
  have hqpc : q ≤ criticalPoint d := max_le hp hHalfLE
  have hgap : Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) ≤
      2 * Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)) := by
    by_cases hcase : pHalf ≤ p
    · dsimp only [q]
      rw [max_eq_left hcase]
      linarith [Real.sqrt_nonneg ((criticalPoint d : ℝ)-(p : ℝ))]
    · have hq : q = pHalf := max_eq_right (le_of_not_ge hcase)
      rw [hq]
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      rw [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hHalfLE)]
      dsimp [pHalf]
      linarith [p.2.1,(criticalPoint d).2.1]
  have hconstant : 2*B/(criticalPoint d : ℝ) ≤
      4*B/(criticalPoint d : ℝ)^2 := by
    apply (div_le_div_iff₀ hpc (sq_pos_of_pos hpc)).mpr
    have hpc1 := (criticalPoint d).2.2
    nlinarith [mul_nonneg (mul_nonneg hB.le hpc.le) (sub_nonneg.mpr hpc1),
      mul_nonneg hB.le hpc.le]
  have hexp : Real.exp (-b * Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)) * (m : ℝ)) ≤
      Real.exp (-(b/2) * Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) * (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hgap (mul_nonneg hb.le (Nat.cast_nonneg m))
    nlinarith
  calc
    _ ≤ halfSpacePioneerMass q i (m : ℤ) := halfSpacePioneerMass_mono hpq i _
    _ ≤ ENNReal.ofReal ((2*B/(criticalPoint d : ℝ)) *
        Real.exp (-b * Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)) * (m : ℝ))) :=
      positiveHeightPioneerDecay_of_weighted q i hB hpc hqlo
        (pioneers q hqlo hqpc) m hm1
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul hconstant hexp (Real.exp_nonneg _) (by positivity))

/-- Actual infinite slab-to-top mass is dominated by the genuine half-space
pioneer mass, by exact finite-cutoff exhaustion. No finiteness premise. -/
lemma slabPioneerMass_top_le_pioneer {d : ℕ} (p : unitInterval)
    (i : Fin d) (m n k : ℤ) :
    slabPioneerMass p i m n k n ≤ halfSpacePioneerMass p i (n-k) := by
  rw [slabPioneerMass_eq_iSup_finiteSlabRows]
  apply iSup_le
  intro R
  simpa only [Pi.single_eq_same] using
    finiteSlab_forward_ofReal_le_pioneer p (latticeSupCube d R) i m n (Pi.single i k)

/-- Exponential top-plane estimate at all subcritical parameters. The NEW
boundary-ratio improvement is deliberately not part of this statement. -/
theorem slabPioneerMass_top_exponential_subcritical {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (m n k : ℤ) (hkn : k ≤ n) :
    slabPioneerMass p i m n k n ≤ ENNReal.ofReal
      ((4*B/(criticalPoint d : ℝ)^2) *
        Real.exp (-(b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*
          ((n-k).toNat : ℝ))) := by
  have h := halfSpace_pioneer_exponential_uniform_subcritical i hB hb hpc
    pioneers p hp (n-k).toNat
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkn)] at h
  exact (slabPioneerMass_top_le_pioneer p i m n k).trans h

end NearCritical
