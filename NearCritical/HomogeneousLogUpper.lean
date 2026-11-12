module
public import NearCritical.HomogeneousLogIntegration
public import NearCritical.WaterCubeAuxiliaryPrior

/-! Actual homogeneous finite-volume prop.upper_log deduction from named
STANDARD literature inputs. Pointwise prior estimates are proved, not premises.
Height-window and seed admissibility remain explicit algebraic side conditions;
no infinite-volume or boundary-comparison claim is made. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

/-- Finite homogeneous conductivity upper bound with logarithm. Constants
precede scales/parameters; all NEW probability and differential steps used here
are discharged. The compact-interval prefactor and seed cutoff are explicit. -/
theorem waterCube_homogeneous_log_upper_of_standard_inputs {d : ℕ} (i : Fin d)
    {C G β E A B b : ℝ} (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β)
    (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d:ℝ)) (hpc1 : (criticalPoint d:ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ Q c : ℝ, 0 < Q ∧ 0 < c ∧ ∀ (r R : ℕ) (p : unitInterval), 1 ≤ r →
      criticalPoint d ≤ p → (p:ℝ) < 1 →
      (p:ℝ)-(criticalPoint d:ℝ) ≤ 1/(2*(r:ℝ)+1)^2 →
      0 < subcriticalSeedParameter (criticalPoint d:ℝ) c (2*(r:ℝ)+1) →
      annealedRelaxed (waterCube d i r R) i (p:ℝ) ≤
        Q*(1+Real.log (2*(r:ℝ)+1))*
          (1+((1/(Real.sqrt (subcriticalSeedParameter (criticalPoint d:ℝ) c (2*(r:ℝ)+1))*(1-(p:ℝ))))/2)*
            (2/(c/2)^2+1))^2/(2*(r:ℝ)+1)^6 := by
  obtain ⟨M,c,hM,hc,hprior⟩ := waterCube_aabb_log_prior_of_standard_inputs i hC hG hβ
    hE hA hB hb hpc hpc1 ordinary subordinary criticalArm pioneers entropic
  let Q := 2*(d:ℝ)*M
  have hd : (0:ℝ) < d := by exact_mod_cast (show 0 < d by have := i.isLt; omega)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨Q,c,hQ,hc,?_⟩
  intro r R p hr hpcp hp1 hw ha
  let H : ℝ := 2*(r:ℝ)+1
  let a := subcriticalSeedParameter (criticalPoint d:ℝ) c H
  have hH : 1 ≤ H := by dsimp [H]; linarith [show (0:ℝ) ≤ (r:ℝ) from Nat.cast_nonneg r]
  have hheight : ((2*r+1:ℕ):ℝ) = H := by dsimp [H]; push_cast; ring
  have hapc : a ≤ (criticalPoint d:ℝ) := subcriticalSeedParameter_le _ _ _
  have hsuball : ∀ q : unitInterval, q ≤ criticalPoint d →
      max (annealedRelaxed (waterCube d i r R) i (q:ℝ))
        (annealedB (waterCube d i r R) i (q:ℝ)) ≤
          (Q/H^2)*Real.log H*Real.exp (-c*H*Real.sqrt ((criticalPoint d:ℝ)-(q:ℝ))) := by
    intro q hq
    have h := (hprior q r R hr).2 hq
    rw [hheight] at h
    have he : Real.exp (-c*H*Real.sqrt ((criticalPoint d:ℝ)-(q:ℝ))) =
        Real.exp (-c*Real.sqrt ((criticalPoint d:ℝ)-(q:ℝ))*H) := by congr 1; ring
    rw [he]
    convert h using 1
    dsimp [Q,H]
    ring
  have hsupall : ∀ q : unitInterval, criticalPoint d ≤ q → (q:ℝ) ≤ (p:ℝ) →
      annealedB (waterCube d i r R) i (q:ℝ) ≤ (Q/H^2)*Real.log H := by
    intro q hq hqp
    by_cases heq : q = criticalPoint d
    · subst q
      have h := (le_max_right _ _).trans (hsuball (criticalPoint d) le_rfl)
      simpa using h
    · have hstrictq : criticalPoint d < q := lt_of_le_of_ne hq (Ne.symm heq)
      have hstrict : (criticalPoint d:ℝ) < (q:ℝ) := hstrictq
      have hwindow : (q:ℝ) ≤ (criticalPoint d:ℝ)+(((2*r+1:ℕ):ℝ)^2)⁻¹ := by
        rw [hheight]
        have hw' : (p:ℝ)-(criticalPoint d:ℝ) ≤ 1/H^2 := hw
        rw [one_div] at hw'
        linarith
      have h := (le_max_right _ _).trans ((hprior q r R hr).1 hstrict hwindow)
      rw [hheight] at h
      convert h using 1
      dsimp [Q,H]
      ring
  have ha0 : 0 < a := ha
  let aU : unitInterval := ⟨a,ha0.le,hapc.trans (criticalPoint d).2.2⟩
  have hstart := (le_max_left _ _).trans (hsuball aU hapc)
  apply annealedRelaxed_log_upper_of_prior_bounds (waterCube_nonempty d i r R) i
    hH hc hQ.le ha (show (criticalPoint d:ℝ) ≤ (p:ℝ) from hpcp) hp1 hw hstart
  · intro x hx
    let q : unitInterval := ⟨x,ha0.le.trans hx.1,hx.2.trans (criticalPoint d).2.2⟩
    exact (le_max_right _ _).trans (hsuball q hx.2)
  · intro x hx
    let q : unitInterval := ⟨x,(criticalPoint d).2.1.trans hx.1,hx.2.trans p.2.2⟩
    exact hsupall q hx.1 hx.2

end NearCritical
