module

public import NearCritical.FiniteSlabExponentialEnvelope
public import NearCritical.HalfSlabKernelBound

/-! NEW half-slab boundary ratio: actual finite Russo integration followed by
uniform ENNReal cutoff exhaustion. No desired probability envelope is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped ENNReal

def halfSlabIntegralCoefficient (d : ℕ) (B b : ℝ) : ℝ :=
  128*(d : ℝ)*(4*B/(criticalPoint d : ℝ)^2)^3*Real.exp (b/2)/(b/2)^2

/-- The nontrivial half-range of the source boundary-prefactor bound, at an
ARBITRARY finite cutoff. Every derivative envelope is supplied internally. -/
theorem finiteSlab_top_row_subcritical_half_range {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (U : Finset (Vertex d))
    (N : ℕ) (hN : 1 ≤ N) (k : ℤ) (hk : 0 ≤ k) (hhalf : 2*k ≤ (N : ℤ)) :
    finiteSlabRowMean p U i 0 (N : ℤ) (Pi.single i k) (N : ℤ) ≤
      halfSlabIntegralCoefficient d B b * (((k : ℝ)+1)/(N+1 : ℝ)) *
        Real.exp (-(b/4)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ))) := by
  let B0 : ℝ := 4*B/(criticalPoint d : ℝ)^2
  let c0 : ℝ := b/2
  let a : ℝ := c0*((N : ℝ)-(k : ℝ))
  let K : ℝ := 2*(d : ℝ)*B0^3*Real.exp c0*(N+1 : ℝ)*((k : ℝ)+1)
  let g : ℝ → ℝ := fun q ↦ finiteSlabRussoRowEnvelope q U i 0 (N : ℤ) (Pi.single i k) (N : ℤ)
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hhalfR : 2*(k : ℝ) ≤ N := by exact_mod_cast hhalf
  have hnk : 0 < (N : ℝ)-(k : ℝ) := by linarith
  have ha : 0 < a := mul_pos hc0 hnk
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hkn : k < (N : ℤ) := by omega
  have hkmem : k ∈ Finset.Icc (0 : ℤ) (N : ℤ) := Finset.mem_Icc.mpr ⟨hk,hkn.le⟩
  have hg : IntervalIntegrable g volume 0 (p : ℝ) :=
    (finiteSlabRussoRowEnvelope_continuous U i 0 (N : ℤ) (Pi.single i k) (N : ℤ)).intervalIntegrable _ _
  have hkernel : Continuous (fun q : ℝ ↦ K*Real.exp (-a*Real.sqrt ((criticalPoint d : ℝ)-q))) := by fun_prop
  have henv : ∀ q ∈ Icc (0 : ℝ) (p : ℝ), g q ≤
      K*Real.exp (-a*Real.sqrt ((criticalPoint d : ℝ)-q)) := by
    intro q hq
    let s : unitInterval := ⟨q,hq.1,hq.2.trans p.2.2⟩
    have hs : s ≤ criticalPoint d := hq.2.trans hp
    have h := finiteSlabRussoRowEnvelope_le_subcritical_exponential i hB hb hpc
      pioneers s hs U N k hkmem
    apply h.trans_eq
    dsimp [g,K,a,B0,c0,s]
    congr 2 <;> ring
  have hrow := finiteSlab_top_row_le_integral_russo p U i (N : ℤ) k hkn
  have hint : (∫ q in 0..(p : ℝ), g q) ≤
      K*((4/a^2)*Real.exp (-(a/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)))) := by
    calc
      _ ≤ ∫ q in 0..(p : ℝ), K*Real.exp (-a*Real.sqrt ((criticalPoint d : ℝ)-q)) :=
        intervalIntegral.integral_mono_on p.2.1 hg (hkernel.intervalIntegrable _ _) henv
      _ = K*(∫ q in 0..(p : ℝ), Real.exp (-a*Real.sqrt ((criticalPoint d : ℝ)-q))) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (subcritical_exp_sqrt_truncated_integral_le p.2.1 hp ha) hK
  let E : ℝ := Real.exp (-(b/4)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ)))
  let L : ℝ := 8*(d : ℝ)*B0^3*Real.exp c0/c0^2*((k : ℝ)+1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have he : Real.exp (-(a/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))) = E := by
    congr 1
    dsimp [a,c0]
    ring
  have hrewrite : K*((4/a^2)*Real.exp (-(a/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)))) =
      L*((N+1 : ℝ)/((N : ℝ)-(k : ℝ))^2)*E := by
    rw [he]
    dsimp [K,L,a]
    field_simp [ne_of_gt hc0,ne_of_gt hnk] <;> ring
  calc
    _ ≤ ∫ q in 0..(p : ℝ), g q := hrow
    _ ≤ K*((4/a^2)*Real.exp (-(a/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)))) := hint
    _ = L*((N+1 : ℝ)/((N : ℝ)-(k : ℝ))^2)*E := hrewrite
    _ ≤ L*(16/(N+1 : ℝ))*E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (half_slab_scale_ratio_le hN hk hhalf) hL) (Real.exp_nonneg _)
    _ = _ := by
      dsimp [L,E,halfSlabIntegralCoefficient,B0,c0]
      ring

/-- Pass the cutoff-uniform finite boundary ratio to the actual infinite slab.
Only ENNReal supremum order is used; infinite A is never differentiated. -/
theorem slabPioneerMass_subcritical_half_range {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (N : ℕ) (hN : 1 ≤ N)
    (k : ℤ) (hk : 0 ≤ k) (hhalf : 2*k ≤ (N : ℤ)) :
    slabPioneerMass p i 0 N k N ≤ ENNReal.ofReal
      (halfSlabIntegralCoefficient d B b * (((k : ℝ)+1)/(N+1 : ℝ)) *
        Real.exp (-(b/4)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ)))) := by
  rw [slabPioneerMass_eq_iSup_finiteSlabRows]
  apply iSup_le
  intro R
  exact ENNReal.ofReal_le_ofReal
    (finiteSlab_top_row_subcritical_half_range i hB hb hpc pioneers p hp (latticeSupCube d R) N hN k hk hhalf)

/-- Full subcritical boundary ratio, with ONE positive constant before every
height, parameter and starting layer. Includes zero height via the genuine
top estimate; it never applies the distinct-layer initial-zero argument there. -/
theorem slabPioneerMass_subcritical_boundary_ratio {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (p : unitInterval), p ≤ criticalPoint d →
      ∀ k ∈ Finset.Icc (0 : ℤ) (N : ℤ),
        slabPioneerMass p i 0 N k N ≤ ENNReal.ofReal
          (C*(((k : ℝ)+1)/(N+1 : ℝ))*
            Real.exp (-(b/4)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ)))) := by
  let B0 : ℝ := 4*B/(criticalPoint d : ℝ)^2
  let L : ℝ := halfSlabIntegralCoefficient d B b
  let C : ℝ := 1+2*B0+L
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hL : 0 ≤ L := by dsimp [L,halfSlabIntegralCoefficient]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N p hp k hk
  have hk0 : 0 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn : k ≤ (N : ℤ) := (Finset.mem_Icc.mp hk).2
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk0
  have hknR : (k : ℝ) ≤ N := by exact_mod_cast hkn
  let D : ℝ := ((k : ℝ)+1)/(N+1 : ℝ)
  let z : ℝ := Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hz : 0 ≤ z := mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hknR)
  have hzexp : -(b/4)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*((N : ℝ)-(k : ℝ)) =
      -(b/4)*z := by dsimp [z]; ring
  rw [hzexp]
  change slabPioneerMass p i 0 N k N ≤ ENNReal.ofReal (C*D*Real.exp (-(b/4)*z))
  by_cases hsmall : 1 ≤ N ∧ 2*k ≤ (N : ℤ)
  · have h := slabPioneerMass_subcritical_half_range i hB hb hpc pioneers p hp N hsmall.1 k hk0 hsmall.2
    have h' : slabPioneerMass p i 0 N k N ≤ ENNReal.ofReal (L*D*Real.exp (-(b/4)*z)) := by
      simpa only [L,D,z,mul_assoc] using h
    apply h'.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hD
    dsimp [C]
    linarith
  · have hDhalf : (1/2 : ℝ) ≤ D := by
      by_cases hN0 : N = 0
      · subst N
        have hkz : k = 0 := by omega
        subst k
        norm_num [D]
      · have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have hnothalf : ¬ 2*k ≤ (N : ℤ) := fun hh ↦ hsmall ⟨hN,hh⟩
        have hlarge : (N : ℝ) < 2*(k : ℝ) := by exact_mod_cast (lt_of_not_ge hnothalf)
        change (1/2 : ℝ) ≤ ((k : ℝ)+1)/(N+1 : ℝ)
        apply (le_div_iff₀ (by positivity : 0 < (N+1 : ℝ))).mpr
        linarith
    have hamp : B0 ≤ C*D := by
      calc
        _ = (2*B0)*(1/2 : ℝ) := by ring
        _ ≤ (2*B0)*D := mul_le_mul_of_nonneg_left hDhalf (by positivity)
        _ ≤ C*D := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hD
    have hdecay : Real.exp (-(b/2)*z) ≤ Real.exp (-(b/4)*z) := by
      apply Real.exp_le_exp.mpr
      have h := mul_nonneg hb.le hz
      nlinarith
    have htop := slabPioneerMass_top_exponential_subcritical i hB hb hpc pioneers p hp
      0 (N : ℤ) k hkn
    have hcast : ((((N : ℤ)-k).toNat : ℕ) : ℝ) = (N : ℝ)-(k : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (sub_nonneg.mpr hkn))
    have htop' : slabPioneerMass p i 0 N k N ≤ ENNReal.ofReal (B0*Real.exp (-(b/2)*z)) := by
      simpa only [B0,z,hcast,mul_assoc] using htop
    exact htop'.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul hamp hdecay (Real.exp_nonneg _) (mul_nonneg hC.le hD)))

end NearCritical
