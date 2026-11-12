module

public import NearCritical.SlabPioneerBoundaryBounds
public import NearCritical.HalfSpaceUniformPioneerDecay

/-! Separation-sensitive actual slab convolution. These bounds do not supply
the additional source half-slab boundary ratio. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset
open scoped ENNReal

/-- Keep the exponential separation factor when summing the actual slab
convolution, retaining the exact number of possible highest layers. -/
lemma slabPioneerMass_le_upper_boundary_count_exponential {d : ℕ}
    (p : unitInterval) (i : Fin d) (N : ℕ) (k j : ℤ)
    (hk : k ∈ Icc (0 : ℤ) (N : ℤ)) (hj : j ∈ Icc (0 : ℤ) (N : ℤ))
    {B r : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r)
    (htop : ∀ t ∈ Icc (0 : ℤ) (N : ℤ), ∀ a : ℤ, a ≤ t →
      slabPioneerMass p i 0 t a t ≤
        ENNReal.ofReal (B*Real.exp (-r*((t : ℝ)-(a : ℝ))))) :
    slabPioneerMass p i 0 N k j ≤ ENNReal.ofReal
      ((((N : ℤ)+1-max k j : ℤ) : ℝ)*B^2*
        Real.exp (-r*|(j : ℝ)-(k : ℝ)|)) := by
  have hcardZ : ((Icc (max k j) (N : ℤ)).card : ℤ) = (N : ℤ)+1-max k j := by
    rw [Int.card_Icc,Int.toNat_of_nonneg]
    have hku := (mem_Icc.mp hk).2
    have hju := (mem_Icc.mp hj).2
    omega
  have hcard : ((Icc (max k j) (N : ℤ)).card : ℝ) =
      (((N : ℤ)+1-max k j : ℤ) : ℝ) := by exact_mod_cast hcardZ
  have hterm (t : ℤ) (ht : t ∈ Icc (max k j) (N : ℤ)) :
      slabPioneerMass p i 0 t k t * slabPioneerMass p i 0 t j t ≤
        ENNReal.ofReal (B^2*Real.exp (-r*|(j : ℝ)-(k : ℝ)|)) := by
    have ht' := mem_Icc.mp ht
    have hkt : k ≤ t := le_trans (le_max_left _ _) ht'.1
    have hjt : j ≤ t := le_trans (le_max_right _ _) ht'.1
    have ht0 : t ∈ Icc (0 : ℤ) (N : ℤ) :=
      mem_Icc.mpr ⟨le_trans (mem_Icc.mp hk).1 hkt,ht'.2⟩
    have hktR : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkt
    have hjtR : (j : ℝ) ≤ (t : ℝ) := by exact_mod_cast hjt
    have habs : |(j : ℝ)-(k : ℝ)| ≤
        ((t : ℝ)-(k : ℝ))+((t : ℝ)-(j : ℝ)) :=
      abs_le.mpr ⟨by linarith,by linarith⟩
    have hexp : Real.exp (-r*((t : ℝ)-(k : ℝ))) *
        Real.exp (-r*((t : ℝ)-(j : ℝ))) ≤
        Real.exp (-r*|(j : ℝ)-(k : ℝ)|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left habs hr
      nlinarith
    calc
      _ ≤ ENNReal.ofReal (B*Real.exp (-r*((t : ℝ)-(k : ℝ)))) *
          ENNReal.ofReal (B*Real.exp (-r*((t : ℝ)-(j : ℝ)))) :=
        mul_le_mul' (htop t ht0 k hkt) (htop t ht0 j hjt)
      _ = ENNReal.ofReal (B^2*(Real.exp (-r*((t : ℝ)-(k : ℝ))) *
          Real.exp (-r*((t : ℝ)-(j : ℝ))))) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hB (Real.exp_nonneg _))]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hexp (sq_nonneg B))
  calc
    _ ≤ ∑ t ∈ Icc (max k j) (N : ℤ),
        slabPioneerMass p i 0 t k t * slabPioneerMass p i 0 t j t :=
      slabPioneerMass_convolution p i 0 N k j
    _ ≤ ∑ _t ∈ Icc (max k j) (N : ℤ),
        ENNReal.ofReal (B^2*Real.exp (-r*|(j : ℝ)-(k : ℝ)|)) := by
      apply sum_le_sum
      exact hterm
    _ = ENNReal.ofReal (((Icc (max k j) (N : ℤ)).card : ℝ)*
        (B^2*Real.exp (-r*|(j : ℝ)-(k : ℝ)|))) := by
      simp only [sum_const,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity)]
      simp [ENNReal.ofReal_mul (sq_nonneg B)]
    _ = _ := by rw [hcard]; congr 1; ring

/-- Instantiate the convolution estimate with the proved genuine all-parameter
pioneer decay. Only literal cited weighted positive-height L2 remains input. -/
theorem slabPioneerMass_subcritical_upper_boundary_exponential {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (N : ℕ) (k j : ℤ)
    (hk : k ∈ Icc (0 : ℤ) (N : ℤ)) (hj : j ∈ Icc (0 : ℤ) (N : ℤ)) :
    slabPioneerMass p i 0 N k j ≤ ENNReal.ofReal
      ((((N : ℤ)+1-max k j : ℤ) : ℝ)*(4*B/(criticalPoint d : ℝ)^2)^2*
        Real.exp (-((b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)))*
          |(j : ℝ)-(k : ℝ)|)) := by
  apply slabPioneerMass_le_upper_boundary_count_exponential p i N k j hk hj
    (by positivity) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  intro t _ a hat
  have h := slabPioneerMass_top_exponential_subcritical i hB hb hpc pioneers p hp
    0 t a hat
  have hcast : ((t-a).toNat : ℝ) = ((t-a : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (sub_nonneg.mpr hat))
  push_cast at hcast
  simpa only [hcast,neg_mul,mul_assoc] using h

/-- Reflection supplies the starting-boundary distance factor needed in the
NEW half-slab Russo integration, while retaining separation decay. -/
theorem slabPioneerMass_subcritical_start_boundary_exponential {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (N : ℕ) (k j : ℤ)
    (hk : k ∈ Icc (0 : ℤ) (N : ℤ)) (hj : j ∈ Icc (0 : ℤ) (N : ℤ)) :
    slabPioneerMass p i 0 N k j ≤ ENNReal.ofReal
      (((k+1 : ℤ) : ℝ)*(4*B/(criticalPoint d : ℝ)^2)^2*
        Real.exp (-((b/2)*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)))*
          |(j : ℝ)-(k : ℝ)|)) := by
  have hkr : (N : ℤ)-k ∈ Icc (0 : ℤ) (N : ℤ) := by
    have h := mem_Icc.mp hk
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hjr : (N : ℤ)-j ∈ Icc (0 : ℤ) (N : ℤ) := by
    have h := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have h := slabPioneerMass_subcritical_upper_boundary_exponential i hB hb hpc
    pioneers p hp N _ _ hkr hjr
  have hid : slabPioneerMass p i 0 N ((N : ℤ)-k) ((N : ℤ)-j) =
      slabPioneerMass p i 0 N k j := by
    simpa only [zero_add] using slabPioneerMass_reflection p i 0 N k j
  have habs : |((((N : ℤ)-j : ℤ) : ℝ))-((((N : ℤ)-k : ℤ) : ℝ))| =
      |(j : ℝ)-(k : ℝ)| := by
    push_cast
    rw [show (N : ℝ)-(j : ℝ)-((N : ℝ)-(k : ℝ)) = (k : ℝ)-(j : ℝ) by ring,
      abs_sub_comm]
  rw [hid,habs] at h
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast (show (N : ℤ)+1-max ((N : ℤ)-k) ((N : ℤ)-j) ≤ k+1 by omega)

end NearCritical
