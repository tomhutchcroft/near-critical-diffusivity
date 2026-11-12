module

public import NearCritical.SlabPioneerShift
public import NearCritical.HalfSlabSubcriticalBound
public import NearCritical.SlabLastInterfaceProbability

/-! NEW source critical base for the two-phase exponential bootstrap. The lower
profile is exactly pc; the upper profile is any q<=pc. No full profile BK or
near-critical mixed bootstrap is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- A rounded suffix of at least half the distance, up to one layer, retains
half the rate and costs only exp(a) when the square-root gap is at most one. -/
lemma twoPhase_suffix_exponential_rounding {a s ell dist : ℝ}
    (ha : 0 ≤ a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hround : dist ≤ 2*ell+2) :
    Real.exp (-a*s*ell) ≤ Real.exp a*Real.exp (-(a/2)*s*dist) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hround (mul_nonneg ha hs0)
  have h' := mul_le_mul_of_nonneg_left hs1 ha
  nlinarith

/-- At criticality the actual upper-boundary count has a uniform constant. -/
lemma slabPioneerMass_critical_upper_count {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (J : ℕ) (k t : ℤ) (hk : k ∈ Finset.Icc (0 : ℤ) (J : ℤ))
    (ht : t ∈ Finset.Icc (0 : ℤ) (J : ℤ)) :
    slabPioneerMass (criticalPoint d) i 0 J k t ≤ ENNReal.ofReal
      ((4*B/(criticalPoint d : ℝ)^2)^2*(((J : ℝ)-(t : ℝ))+1)) := by
  have h := slabPioneerMass_subcritical_upper_boundary_exponential i hB hb hpc pioneers
    (criticalPoint d) le_rfl J k t hk ht
  simp only [sub_self,Real.sqrt_zero,mul_zero,zero_mul,neg_zero,Real.exp_zero,mul_one] at h
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc : (((J : ℤ)+1-max k t : ℤ) : ℝ) ≤ (J : ℝ)-(t : ℝ)+1 := by
    exact_mod_cast (show (J : ℤ)+1-max k t ≤ (J : ℤ)-t+1 by omega)
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (4*B/(criticalPoint d : ℝ)^2))
  nlinarith

/-- The all-depth homogeneous half-slab bound applies to a strict upper block
starting at ANY integer layer, including a block of zero width. -/
lemma slabPioneerMass_pure_upper_block_bound {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : unitInterval), q ≤ criticalPoint d →
      ∀ a j : ℤ, a ≤ j →
        slabPioneerMass q i a j a j ≤ ENNReal.ofReal
          ((C/((j : ℝ)-(a : ℝ)+1))*
            Real.exp (-(b/4)*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*((j : ℝ)-(a : ℝ)))) := by
  obtain ⟨C,hC,hbound⟩ := slabPioneerMass_subcritical_boundary_ratio i hB hb hpc pioneers
  refine ⟨C,hC,?_⟩
  intro q hq a j haj
  have hNat : ((j-a).toNat : ℤ) = j-a := Int.toNat_of_nonneg (sub_nonneg.mpr haj)
  have hReal : ((j-a).toNat : ℝ) = (j : ℝ)-(a : ℝ) := by exact_mod_cast hNat
  have h := hbound (j-a).toNat q hq 0 (by simp)
  rw [slabPioneerMass_bottom_shift]
  have heq : slabPioneerMass q i 0 (j-a) 0 (j-a) =
      slabPioneerMass q i 0 ((j-a).toNat : ℤ) 0 ((j-a).toNat : ℤ) := by rw [hNat]
  rw [heq]
  simpa only [hReal,Int.cast_zero,zero_add,sub_zero,one_div,mul_one_div,div_eq_mul_inv,one_mul] using! h

/-- A common scalar cancellation for both interface cases. The prefix pays
at most two times the suffix width+one; the half-slab denominator cancels it. -/
lemma twoPhase_prefix_suffix_product_bound {P C b s ell dist : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hell : 0 ≤ ell)
    (hround : dist ≤ 2*ell+2) :
    (2*P*(ell+1))*((C/(ell+1))*Real.exp (-(b/4)*s*ell)) ≤
      (2*P*C*Real.exp (b/4))*Real.exp (-(b/8)*s*dist) := by
  have hden : ell+1 ≠ 0 := ne_of_gt (by linarith)
  have he := twoPhase_suffix_exponential_rounding (by positivity : 0 ≤ b/4) hs0 hs1 hround
  have hscale := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2*P*C)
  have hrate : (b/4)/2 = b/8 := by ring
  rw [hrate] at hscale
  convert hscale using 1 <;> field_simp <;> ring

/-- Literal source eq.M.mnbound at p=pc. ONE amplitude and rate precede ALL
interface/source/target heights and every upper parameter q<=pc. -/
theorem twoPhaseSlabPioneerMass_critical_initial_exponential {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (m k j : ℕ), k ≤ j →
      ∀ (q : unitInterval), q ≤ criticalPoint d →
        twoPhaseSlabPioneerMass i (criticalPoint d) q m j k j ≤ ENNReal.ofReal
          (M*Real.exp (-c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
            twoPhaseSlabDistance m k j)) := by
  let B0 : ℝ := 4*B/(criticalPoint d : ℝ)^2
  obtain ⟨C,hC,hblock⟩ := slabPioneerMass_pure_upper_block_bound i hB hb hpc pioneers
  let A : ℝ := 2*B0^2*C*Real.exp (b/4)
  let M : ℝ := 1+B0+A
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M,b/8,hM,by positivity,?_⟩
  intro m k j hkj q hq
  let s : ℝ := Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hgap : 0 ≤ (criticalPoint d : ℝ)-(q : ℝ) := sub_nonneg.mpr hq
  have hs1 : s ≤ 1 := by
    have hgap1 : (criticalPoint d : ℝ)-(q : ℝ) ≤ 1 := by
      linarith [(criticalPoint d).2.2,q.2.1]
    have hsquare : s^2 = (criticalPoint d : ℝ)-(q : ℝ) := Real.sq_sqrt hgap
    nlinarith
  have hkJ : (k : ℤ) ∈ Finset.Icc (0 : ℤ) (j : ℤ) := by simp; exact_mod_cast hkj
  have hdom : A ≤ M := by dsimp [M]; linarith
  have hfinish : ∀ dist : ℝ,
      ENNReal.ofReal (A*Real.exp (-(b/8)*s*dist)) ≤
        ENNReal.ofReal (M*Real.exp (-(b/8)*s*dist)) := by
    intro dist
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hdom (Real.exp_nonneg _))
  by_cases hjm : j ≤ m
  · have hd : twoPhaseSlabDistance (m : ℤ) k j = 0 :=
      twoPhaseSlabDistance_below (by exact_mod_cast (hkj.trans hjm)) (by exact_mod_cast hjm)
    have htop := slabPioneerMass_top_exponential_subcritical i hB hb hpc pioneers
      (criticalPoint d) le_rfl 0 j k (by exact_mod_cast hkj)
    have hcrit : slabPioneerMass (criticalPoint d) i 0 j k j ≤ ENNReal.ofReal B0 := by
      simpa only [B0,sub_self,Real.sqrt_zero,mul_zero,zero_mul,neg_zero,Real.exp_zero,mul_one] using htop
    have h := (twoPhaseSlabPioneerMass_le_homogeneous i (criticalPoint d) q hq m j k j).trans hcrit
    rw [hd]
    simp only [mul_zero,Real.exp_zero,mul_one]
    exact h.trans (ENNReal.ofReal_le_ofReal (by dsimp [M]; linarith))
  · have hmj : (m : ℤ) < (j : ℤ) := by exact_mod_cast (lt_of_not_ge hjm)
    by_cases hkm : k ≤ m
    · let ell : ℝ := (j : ℝ)-(m : ℝ)-1
      have hell : 0 ≤ ell := by dsimp [ell]; exact_mod_cast (show 0 ≤ (j : ℤ)-(m : ℤ)-1 by omega)
      have hmJ : (m : ℤ) ∈ Finset.Icc (0 : ℤ) (j : ℤ) := by simp; omega
      have hpref := slabPioneerMass_critical_upper_count i hB hb hpc pioneers j k m hkJ hmJ
      have hpref' : slabPioneerMass (criticalPoint d) i 0 j k m ≤
          ENNReal.ofReal (2*B0^2*(ell+1)) := by
        apply hpref.trans (ENNReal.ofReal_le_ofReal ?_)
        change B0^2*((j : ℝ)-(m : ℝ)+1) ≤ _
        have he : (j : ℝ)-(m : ℝ)+1 ≤ 2*(ell+1) := by dsimp [ell] at *; linarith
        nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg B0)]
      have hsuff := hblock q hq ((m : ℤ)+1) j (by omega)
      have hsuff' : slabPioneerMass q i ((m : ℤ)+1) j ((m : ℤ)+1) j ≤
          ENNReal.ofReal ((C/(ell+1))*Real.exp (-(b/4)*s*ell)) := by
        convert! hsuff using 1 <;> simp only [Int.cast_add,Int.cast_one,Int.cast_natCast]
        <;> dsimp [ell,s] <;> congr 1 <;> ring
      have hd := twoPhaseSlabDistance_crossing (m := (m : ℤ)) (k := (k : ℤ)) (j := (j : ℤ))
        (by exact_mod_cast hkm) (by omega)
      have hround : twoPhaseSlabDistance (m : ℤ) k j ≤ 2*ell+2 := by
        rw [hd]
        simp only [Int.cast_natCast]
        have hstep : (m : ℝ)+1 ≤ (j : ℝ) := by
          exact_mod_cast (show (m : ℤ)+1 ≤ (j : ℤ) by omega)
        dsimp [ell]
        linarith
      have hprod := mul_le_mul' hpref' hsuff'
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*B0^2*(ell+1))] at hprod
      have hraw := (twoPhaseSlabPioneerMass_last_interface_bound i m j k j
        (by positivity) (by exact_mod_cast hkm) hmj (criticalPoint d) q hq).trans hprod
      exact hraw.trans ((ENNReal.ofReal_le_ofReal
        (twoPhase_prefix_suffix_product_bound (sq_nonneg B0) hC.le hb.le hs0 hs1 hell hround)).trans
          (hfinish _))
    · let t : ℤ := twoPhaseUpperCut m k j
      have hmk : (m : ℤ) ≤ (k : ℤ) := by exact_mod_cast (le_of_lt (lt_of_not_ge hkm))
      obtain ⟨ht,hkt,htj⟩ := twoPhaseUpperCut_admissible hmk (by exact_mod_cast hkj) hmj
      have htJ : t ∈ Finset.Icc (0 : ℤ) (j : ℤ) := Finset.mem_Icc.mpr ⟨by dsimp [t]; omega,htj⟩
      let ell : ℝ := (j : ℝ)-(t : ℝ)
      have hell : 0 ≤ ell := by dsimp [ell]; exact_mod_cast (sub_nonneg.mpr htj)
      have hpref := slabPioneerMass_critical_upper_count i hB hb hpc pioneers j k t hkJ htJ
      have hpref' : slabPioneerMass (criticalPoint d) i 0 j k t ≤ ENNReal.ofReal (2*B0^2*(ell+1)) := by
        apply hpref.trans (ENNReal.ofReal_le_ofReal ?_)
        change B0^2*(ell+1) ≤ _
        nlinarith [mul_nonneg (sq_nonneg B0) (by linarith : 0 ≤ ell+1)]
      have hsuff := hblock q hq t j htj
      have hsuff' : slabPioneerMass q i t j t j ≤
          ENNReal.ofReal ((C/(ell+1))*Real.exp (-(b/4)*s*ell)) := by simpa only [ell,s,Int.cast_natCast] using! hsuff
      have hd : twoPhaseSlabDistance (m : ℤ) k j = (j : ℝ)-(k : ℝ) := by
        unfold twoPhaseSlabDistance
        have hkNat : (((k : ℤ)-(m : ℤ)).toNat : ℝ) = (k : ℝ)-(m : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hmk)
        have hjNat : (((j : ℤ)-(m : ℤ)).toNat : ℝ) = (j : ℝ)-(m : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ (j : ℤ)-(m : ℤ))
        rw [hkNat,hjNat,show (j : ℝ)-(m : ℝ)-((k : ℝ)-(m : ℝ)) = (j : ℝ)-(k : ℝ) by ring]
        exact abs_of_nonneg (by exact_mod_cast (show 0 ≤ (j : ℤ)-(k : ℤ) by omega))
      have hround : twoPhaseSlabDistance (m : ℤ) k j ≤ 2*ell+2 := by
        rw [hd]
        have h := twoPhaseUpperCut_gap hmk (by exact_mod_cast hkj) hmj
        dsimp [ell,t]
        exact_mod_cast h
      have hprod := mul_le_mul' hpref' hsuff'
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*B0^2*(ell+1))] at hprod
      have hraw := (twoPhaseSlabPioneerMass_midpoint_bound i m j k j (by positivity) hmk
        (by exact_mod_cast hkj) hmj (criticalPoint d) q hq).trans hprod
      exact hraw.trans ((ENNReal.ofReal_le_ofReal
        (twoPhase_prefix_suffix_product_bound (sq_nonneg B0) hC.le hb.le hs0 hs1 hell hround)).trans
          (hfinish _))

end NearCritical
