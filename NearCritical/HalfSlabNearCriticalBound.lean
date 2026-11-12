module

public import NearCritical.HalfSlabSubcriticalBound
public import NearCritical.FiniteSlabNearCriticalEnvelope
public import NearCritical.SlabCriticalLower

/-! NEW nearcritical half-slab boundary ratio. The import of SlabCriticalLower
is used only for its elementary inverse-square window comparison. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped ENNReal

/-- Actual finite pc-to-p integration, including nil paths: the critical
initial value is bounded, never asserted to be zero. -/
theorem finiteSlab_top_row_nearCritical_boundary_ratio {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (N : ℕ) (p : unitInterval), criticalPoint d ≤ p →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        ∀ (U : Finset (Vertex d)) (k : ℤ), k ∈ Finset.Icc (0 : ℤ) (N : ℤ) →
          finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤
            C*(((k : ℝ)+1)/(N+1 : ℝ)) := by
  obtain ⟨C0,hC0,hcritical⟩ := slabPioneerMass_subcritical_boundary_ratio i hB hb hpc pioneers
  obtain ⟨ε,D,hε,hD,hend,henv⟩ :=
    finiteSlabRussoRowEnvelope_nearCritical_bound_of_weighted i hB hb hpc hpc1
      (pioneers (criticalPoint d) (by linarith) le_rfl)
  refine ⟨ε,C0+ε*D,hε,by positivity,hend,?_⟩
  intro N p hcp hp U k hk
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hn1 : 0 < (N+1 : ℝ) := by positivity
  let R : ℝ := ((k : ℝ)+1)/(N+1 : ℝ)
  let T : ℝ := D*(N+1 : ℝ)*((k : ℝ)+1)
  let g : ℝ → ℝ := fun q ↦ finiteSlabRussoRowEnvelope q U i 0 (N : ℤ) (Pi.single i k) (N : ℤ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hstart : finiteSlabRowMean (criticalPoint d) U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤ C0*R := by
    apply finiteSlabRowMean_le_of_slabPioneerMass_le (criticalPoint d) U i 0 (N : ℤ)
      (Pi.single i k) (N : ℤ) (by dsimp [R]; positivity)
    have h := hcritical N (criticalPoint d) le_rfl k hk
    simpa only [Pi.single_eq_same,sub_self,Real.sqrt_zero,mul_zero,zero_mul,
      Real.exp_zero,mul_one,R] using h
  have hstep : finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) -
      finiteSlabRowMean (criticalPoint d) U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤
        ∫ q in (criticalPoint d : ℝ)..(p : ℝ), g q := by
    simpa only [finiteSlabRowMean_eq_expectation] using
      finiteSlabRowExpectation_sub_le_integral_russo (criticalPoint d) p hcp U i 0 (N : ℤ) (Pi.single i k) (N : ℤ)
  have hg : IntervalIntegrable g volume (criticalPoint d : ℝ) (p : ℝ) :=
    (finiteSlabRussoRowEnvelope_continuous U i 0 (N : ℤ) (Pi.single i k) (N : ℤ)).intervalIntegrable _ _
  have hpoint : ∀ q ∈ Icc (criticalPoint d : ℝ) (p : ℝ), g q ≤ T := by
    intro q hq
    let s : unitInterval := ⟨q,(criticalPoint d).2.1.trans hq.1,hq.2.trans p.2.2⟩
    have hcs : criticalPoint d ≤ s := hq.1
    have hsw : (s : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 := hq.2.trans hp
    exact henv N s hcs hsw U k hk
  have hint : (∫ q in (criticalPoint d : ℝ)..(p : ℝ), g q) ≤
      ((p : ℝ)-(criticalPoint d : ℝ))*T := by
    calc
      _ ≤ ∫ _q in (criticalPoint d : ℝ)..(p : ℝ), T :=
        intervalIntegral.integral_mono_on hcp hg intervalIntegrable_const hpoint
      _ = _ := by rw [intervalIntegral.integral_const]; rfl
  have hwindow : (p : ℝ)-(criticalPoint d : ℝ) ≤ ε/(N+1 : ℝ)^2 := by linarith
  have hinc : ((p : ℝ)-(criticalPoint d : ℝ))*T ≤ ε*D*R := by
    calc
      _ ≤ (ε/(N+1 : ℝ)^2)*T := mul_le_mul_of_nonneg_right hwindow hT
      _ = _ := by
        dsimp [T,R]
        field_simp [ne_of_gt hn1]
  have hdiff := hstep.trans (hint.trans hinc)
  change finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤ (C0+ε*D)*R
  calc
    _ = (finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) -
        finiteSlabRowMean (criticalPoint d) U i 0 (N : ℤ) (Pi.single i k) (N : ℤ)) +
        finiteSlabRowMean (criticalPoint d) U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) := by ring
    _ ≤ ε*D*R+C0*R := add_le_add hdiff hstart
    _ = _ := by ring

/-- The cutoff-uniform nearcritical ratio passes to actual infinite slab mass
without differentiating an infinite sum. -/
theorem slabPioneerMass_nearCritical_boundary_ratio {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (N : ℕ) (p : unitInterval), criticalPoint d ≤ p →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        ∀ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), slabPioneerMass p i 0 N k N ≤
          ENNReal.ofReal (C*(((k : ℝ)+1)/(N+1 : ℝ))) := by
  obtain ⟨ε,C,hε,hC,hend,hbound⟩ := finiteSlab_top_row_nearCritical_boundary_ratio i hB hb hpc hpc1 pioneers
  refine ⟨ε,C,hε,hC,hend,?_⟩
  intro N p hcp hp k hk
  rw [slabPioneerMass_eq_iSup_finiteSlabRows]
  apply iSup_le
  intro R
  exact ENNReal.ofReal_le_ofReal (hbound N p hcp hp (latticeSupCube d R) k hk)

/-- Unified source half-slab estimate: sqrt(pc-p)=0 above pc. Constants precede
ALL heights, parameters and starting layers; only cited standard input remains. -/
theorem slabPioneerMass_half_boundary_ratio_of_weighted {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ ε C c : ℝ, 0 < ε ∧ 0 < C ∧ 0 < c ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (N : ℕ) (p : unitInterval),
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        ∀ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), slabPioneerMass p i 0 N k N ≤
          ENNReal.ofReal (C*(((k : ℝ)+1)/(N+1 : ℝ))*
            Real.exp (-c*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ)))) := by
  obtain ⟨S,hS,hsub⟩ := slabPioneerMass_subcritical_boundary_ratio i hB hb hpc pioneers
  obtain ⟨ε,T,hε,hT,hend,hnear⟩ := slabPioneerMass_nearCritical_boundary_ratio i hB hb hpc hpc1 pioneers
  refine ⟨ε,max S T,b/4,hε,lt_of_lt_of_le hS (le_max_left _ _),by positivity,hend,?_⟩
  intro N p hp k hk
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hratio : 0 ≤ ((k : ℝ)+1)/(N+1 : ℝ) := by positivity
  by_cases hpcp : p ≤ criticalPoint d
  · exact (hsub N p hpcp k hk).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left S T) hratio) (Real.exp_nonneg _)))
  · have hcp : criticalPoint d ≤ p := (lt_of_not_ge hpcp).le
    have hsqrt : Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr hcp)
    rw [hsqrt]
    simp only [mul_zero,zero_mul,Real.exp_zero,mul_one]
    exact (hnear N p hcp hp k hk).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right S T) hratio))

/-- Literal positive-height N^-2 window, with its required factor-four shrink
exhibited explicitly instead of identifying two different window constants. -/
theorem slabPioneerMass_half_boundary_ratio_source_window {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ δ C c : ℝ, 0 < δ ∧ 0 < C ∧ 0 < c ∧ (criticalPoint d : ℝ)+δ < 1 ∧
      ∀ N : ℕ, 1 ≤ N → ∀ p : unitInterval,
        (p : ℝ) ≤ (criticalPoint d : ℝ)+δ/(N : ℝ)^2 →
        ∀ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), slabPioneerMass p i 0 N k N ≤
          ENNReal.ofReal (C*(((k : ℝ)+1)/(N+1 : ℝ))*
            Real.exp (-c*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ)))) := by
  obtain ⟨ε,C,c,hε,hC,hc,hend,hbound⟩ := slabPioneerMass_half_boundary_ratio_of_weighted i hB hb hpc hpc1 pioneers
  refine ⟨ε/4,C,c,by positivity,hC,hc,by linarith,?_⟩
  intro N hN p hp k hk
  apply hbound N p _ k hk
  have hwindow := slab_window_inverse_sq_lower hε.le N hN
  exact hp.trans (by linarith)

/-- Literal single-constant source convention: enlarge the amplitude constant
until its reciprocal is no larger than the already proved decay rate. -/
theorem slabPioneerMass_half_boundary_ratio_source {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ (criticalPoint d : ℝ)+δ < 1 ∧
      ∀ N : ℕ, 1 ≤ N → ∀ p : unitInterval,
        (p : ℝ) ≤ (criticalPoint d : ℝ)+δ/(N : ℝ)^2 →
        ∀ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), slabPioneerMass p i 0 N k N ≤
          ENNReal.ofReal (C*(((k : ℝ)+1)/(N+1 : ℝ))*
            Real.exp (-C⁻¹*((N : ℝ)-(k : ℝ))*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)))) := by
  obtain ⟨δ,C,c,hδ,hC,hc,hend,hbound⟩ :=
    slabPioneerMass_half_boundary_ratio_source_window i hB hb hpc hpc1 pioneers
  let Cstar : ℝ := C+1/c+1
  have hCstar : 0 < Cstar := by dsimp [Cstar]; positivity
  have hcinv : 0 ≤ (1 : ℝ)/c := by positivity
  have hlarge : C ≤ Cstar := by dsimp [Cstar]; linarith
  have hsmall : 1/c ≤ Cstar := by dsimp [Cstar]; linarith
  have hmul : 1 ≤ c*Cstar := by
    have h := (div_le_iff₀ hc).mp hsmall
    simpa only [mul_comm] using h
  have hrate : Cstar⁻¹ ≤ c := by
    have hdiv : (1 : ℝ)/Cstar ≤ c := (div_le_iff₀ hCstar).mpr hmul
    simpa only [one_div] using hdiv
  refine ⟨δ,Cstar,hδ,hCstar,hend,?_⟩
  intro N hN p hp k hk
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hkn : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
  have hratio : 0 ≤ ((k : ℝ)+1)/(N+1 : ℝ) := by positivity
  have hexp : Real.exp (-c*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ))) ≤
      Real.exp (-Cstar⁻¹*((N : ℝ)-(k : ℝ))*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (neg_le_neg hrate)
      (mul_nonneg (Real.sqrt_nonneg ((criticalPoint d : ℝ)-(p : ℝ))) (sub_nonneg.mpr hkn))
    convert h using 1 <;> ring
  exact (hbound N hN p hp k hk).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul (mul_le_mul_of_nonneg_right hlarge hratio) hexp (Real.exp_nonneg _)
      (mul_nonneg hCstar.le hratio)))

end NearCritical
