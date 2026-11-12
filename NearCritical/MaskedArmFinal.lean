module

public import NearCritical.MaskedArmTwoSegment
public import NearCritical.MaskedArmThreeSegment
public import NearCritical.MaskedArmPrefixDecay
public import NearCritical.MaskedArmScaleBounds
public import NearCritical.MaskedArmDepthFactor
public import NearCritical.MaskedArmCutAdmissibility
public import NearCritical.MaskedArmScalarClosure
public import NearCritical.TwoPhaseSlabNearCritical

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

private theorem maskedArm_middle_mass {d : ℕ} (i : Fin d) {C ε : ℝ}
    (bound : ∀ (q : unitInterval), q ≤ criticalPoint d →
      ∀ (m n : ℕ) (p : unitInterval),
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/((m+1 : ℝ)*(n+1 : ℝ)) →
        ∀ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ∀ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
          twoPhaseSlabPioneerMass i p q m n k j ≤ ENNReal.ofReal
            (C*((n : ℝ)+1-(j : ℝ))*Real.exp
              (-C⁻¹*twoPhaseSlabDistance m k j*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)))))
    (p q : unitInterval) (hq : q ≤ criticalPoint d) (m n : ℤ)
    (hm : 0 ≤ m) (hmn : m ≤ n)
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(((m : ℝ)+1)*((n : ℝ)+1))) :
    twoPhaseSlabPioneerMass i p q m n m n ≤ ENNReal.ofReal
      (C*Real.exp (-C⁻¹*twoPhaseSlabDistance m m n*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)))) := by
  have hn : 0 ≤ n := hm.trans hmn
  have hmZ : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  have hnZ : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  have hmR : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hmZ
  have hnR : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hnZ
  have hp' : (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/((m.toNat+1 : ℝ)*(n.toNat+1 : ℝ)) := by
    simpa only [hmR, hnR] using hp
  have h := bound q hq m.toNat n.toNat p hp'
    m (Finset.mem_Icc.mpr ⟨hm, by simpa only [hnZ] using hmn⟩)
    n (Finset.mem_Icc.mpr ⟨hn, by rw [hnZ]⟩)
  rw [hmZ, hnZ, hnR, show (n : ℝ)+1-(n : ℝ) = 1 by ring, mul_one] at h
  exact h

set_option maxHeartbeats 900000 in
/-- The masked positive-face arm has a uniform cubic depth factor and
exponential decay through the subcritical band. -/
theorem maskedWaterCube_positive_face_exponential {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (r R : ℕ) (p q : unitInterval) (x : DomainVertex (waterCube d i r R)),
      let H : ℕ := 2*r+1
      let k := x.val i+(r : ℤ)
      x.val ∈ waterCube d i r R → 2*k ≤ (H : ℤ) →
      q ≤ p → q ≤ criticalPoint d →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(H : ℝ)^2 →
      (bulkPercolation (waterCube d i r R) i (H : ℝ) δ p q).real
        (waterCubeFaceConnectionEvent i r R true x) ≤
          C*((k : ℝ)+1)/(H : ℝ)^3 *
            Real.exp (-(H : ℝ)*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))/C) := by
  obtain ⟨εp, Cp, hεp, hCp, hcap, hprefix⟩ :=
    maskedArm_prefix_envelope i hB hb hpc hpc1 pioneers
  obtain ⟨Cm, εm, hCm, hεm, hmiddle⟩ :=
    twoPhaseSlabPioneerMass_nearCritical i hB hb hpc hpc1 pioneers
  obtain ⟨Ct, εt, hCt, hεt, htwo⟩ :=
    maskedWaterCube_two_segment_decay i hB hb hCo hpc hpc1 pioneers ordinary
  let ε := min 1 (min εp (min εm εt))
  have hε : 0 < ε := lt_min zero_lt_one (lt_min hεp (lt_min hεm hεt))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεp' : ε ≤ εp := (min_le_right _ _).trans (min_le_left _ _)
  have hεm' : ε ≤ εm := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεt' : ε ≤ εt := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let P : unitInterval := ⟨(criticalPoint d : ℝ)+εp, ⟨by linarith, hcap.le⟩⟩
  let H₀ : ℝ := max 1 (2/(1-δ))
  let c := min (Cm⁻¹*(1-δ)/2) (Ct⁻¹*(1-δ)/2)
  let S := 4*Co/δ^2
  let K := 2*Cp/δ
  let M := Cm*Real.exp (Cm⁻¹)
  let T := Ct*Real.exp (Ct⁻¹)
  let A := K*M*S + T*S*(2/δ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hδ' : 0 < 1-δ := sub_pos.mpr hδ1
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨C, hC, hclose⟩ := maskedArm_close_scales hA hc (le_max_left 1 (2/(1-δ)))
  refine ⟨C, ε, hC, hε, ?_⟩
  intro r R p q x
  dsimp only
  intro hx hhalf hqp hq hp
  let H : ℕ := 2*r+1
  let k := x.val i+(r : ℤ)
  let m : ℤ := ⌊δ*((H : ℝ))/2⌋
  let n : ℤ := (H : ℤ)-m-1
  let s := Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))
  let U := waterCube d i r R
  let μ := bulkPercolation U i (H : ℝ) δ p q
  let u := μ.real (waterCubeFaceConnectionEvent i r R true x)
  have hH : 0 < H := by dsimp [H]; omega
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hH1 : 1 ≤ (H : ℝ) := by exact_mod_cast (show 1 ≤ H by omega)
  have hHs : 1 ≤ (H : ℝ)^2 := by nlinarith
  have hnorm : (H : ℝ) = 2*(r : ℝ)+1 := by dsimp [H] <;> push_cast <;> ring
  have hnormZ : (H : ℤ) = 2*(r : ℤ)+1 := by dsimp [H] <;> push_cast <;> ring
  have hk : 0 ≤ k := by
    have hh := (mem_rectangularBox.mp hx) i
    simp only [ite_true] at hh
    dsimp [k]
    omega
  have hkR : 0 ≤ (k : ℝ) := by exact_mod_cast hk
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by nlinarith [(criticalPoint d).property.2, q.property.1]⟩
  have hu : u ≤ 1 := by
    letI : IsProbabilityMeasure μ := by
      change IsProbabilityMeasure (percolationProfile d _)
      infer_instance
    exact measureReal_le_one
  change u ≤ C*((k : ℝ)+1)/(H : ℝ)^3*Real.exp (-(H : ℝ)*s/C)
  apply hclose hHR hkR hs hs1 hu
  intro hlarge
  have hlarge' : 2 ≤ (1-δ)*(H : ℝ) := by
    have h := (le_max_right (1 : ℝ) (2/(1-δ))).trans hlarge
    simpa only [mul_comm] using (div_le_iff₀ hδ').mp h
  obtain ⟨hm, hmn, hkn, hnH⟩ := maskedArm_cuts_admissible δ H k hδ.le hlarge' hhalf
  have hn : 0 ≤ n := hm.trans hmn
  have hpP : p ≤ P := by
    change (p : ℝ) ≤ (criticalPoint d : ℝ)+εp
    exact hp.trans (add_le_add_right ((div_le_self hε.le hHs).trans hεp') _)
  have hp1 : (p : ℝ) ≤ (criticalPoint d : ℝ)+((H : ℝ)^2)⁻¹ := by
    rw [← one_div]
    exact hp.trans (add_le_add_right (div_le_div_of_nonneg_right hε1 (sq_nonneg _)) _)
  have hp_m : (p : ℝ) ≤ (criticalPoint d : ℝ)+εm/(((m : ℝ)+1)*((n : ℝ)+1)) :=
    hp.trans (add_le_add_right ((div_le_div_of_nonneg_right hεm' (sq_nonneg _)).trans
      (maskedArm_window_le hH hm hmn hnH hεm.le)) _)
  have hp_t : (p : ℝ) ≤ (criticalPoint d : ℝ)+εt/(((m : ℝ)+1)*((n : ℝ)+1)) :=
    hp.trans (add_le_add_right ((div_le_div_of_nonneg_right hεt' (sq_nonneg _)).trans
      (maskedArm_window_le hH hm hmn hnH hεt.le)) _)
  have hsuff : Co/((H : ℝ)-(n : ℝ))^2 ≤ S/(H : ℝ)^2 :=
    maskedArm_suffix_scale_le hδ hH hCo
  have hdecay {a : ℝ} (ha : 0 ≤ a) (hac : c ≤ a*(1-δ)/2) (j : ℤ)
      (hj : 2*j ≤ (H : ℤ)) (hmj : m ≤ j) (hjn : j ≤ n) :
      Real.exp (-a*twoPhaseSlabDistance m j n*s) ≤
        Real.exp a*Real.exp (-c*(H : ℝ)*s) := by
    apply (maskedArm_middle_exp_le (δ := δ) ha hs hs1 hj hmj hjn).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hac (mul_nonneg hHR.le hs)
    nlinarith
  have hphysical_m : m = ⌊δ*(2*(r : ℝ)+1)/2⌋ := by
    change ⌊δ*(H : ℝ)/2⌋ = _
    rw [hnorm]
  have hphysical_n : n = (2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1 := by
    change (H : ℤ)-m-1 = _
    rw [hnormZ, hphysical_m] <;> push_cast <;> ring
  let D := Real.exp (-c*(H : ℝ)*s)
  by_cases hkm : k ≤ m
  · let X := Cp*(((k : ℝ)+1)/((m : ℝ)+1))
    let Y := Cm*Real.exp (-Cm⁻¹*twoPhaseSlabDistance m m n*s)
    have hmH : m < (H : ℤ) := hmn.trans_lt hnH
    have hp_p : (p : ℝ) ≤ (criticalPoint d : ℝ)+εp/(H : ℝ)^2 :=
      hp.trans (add_le_add_right (div_le_div_of_nonneg_right hεp' (sq_nonneg _)) _)
    have hxmass : slabPioneerMass p i 0 m k m ≤ ENNReal.ofReal X :=
      hprefix H m k p hk hkm hmH hp_p
    have hymass : twoPhaseSlabPioneerMass i p q m n m n ≤ ENNReal.ofReal Y :=
      maskedArm_middle_mass i hmiddle p q hq m n hm hmn hp_m
    have hX : 0 ≤ X := by
      dsimp [X]
      have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
      exact mul_nonneg hCp.le (div_nonneg (by positivity) (by linarith))
    have hY : 0 ≤ Y := by dsimp [Y]; positivity
    have h3 := maskedWaterCube_three_segment_le ordinary hCo i r R δ p q P
      hqp hcap hpP (by simpa only [H] using hp1) x hx hX hY
    dsimp only at h3
    rw [← hphysical_n, ← hphysical_m] at h3
    have h3' := h3 hm hkm hmn (by rw [← hnormZ]; exact hnH) hxmass hymass
    have h3'' : u ≤ X*Y*(Co/((H : ℝ)-(n : ℝ))^2) := by
      simpa only [u, μ, U, hnorm, waterCubeFaceConnectionEvent, ite_true] using h3'
    have hX' : X ≤ K*((k : ℝ)+1)/(H : ℝ) :=
      maskedArm_prefix_scale_le hδ hH hCp.le hk
    have hmhalf : 2*m ≤ (H : ℤ) := by
      have hf : (m : ℝ) ≤ δ*(H : ℝ)/2 := Int.floor_le _
      have hmul := mul_le_mul_of_nonneg_right hδ1.le hHR.le
      have h : 2*(m : ℝ) ≤ (H : ℝ) := by linarith only [hf, hmul]
      exact_mod_cast h
    have hY' : Y ≤ M*D := by
      dsimp [Y, M, D]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (hdecay (inv_nonneg.mpr hCm.le) (min_le_left _ _) m hmhalf le_rfl hmn) hCm.le
    calc
      u ≤ X*Y*(Co/((H : ℝ)-(n : ℝ))^2) := h3''
      _ ≤ (K*((k : ℝ)+1)/(H : ℝ))*(M*D)*(S/(H : ℝ)^2) :=
        mul_le_mul (mul_le_mul hX' hY' hY (by positivity)) hsuff
          (by positivity) (by positivity)
      _ = (K*M*S)*((k : ℝ)+1)/(H : ℝ)^3*D := by ring
      _ ≤ A*((k : ℝ)+1)/(H : ℝ)^3*D := by
        have hcoef : K*M*S ≤ A := le_add_of_nonneg_right (by positivity)
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) (Real.exp_nonneg _)
  · have hmk : m ≤ k := le_of_not_ge hkm
    have h2 := htwo r R δ p q P x
    dsimp only at h2
    rw [← hphysical_n, ← hphysical_m] at h2
    have h2' := h2 hx hm hn hk hkn hqp hq hcap hpP (by simpa only [H] using hp1) hp_t
    have h2'' : u ≤ Ct*Real.exp (-Ct⁻¹*twoPhaseSlabDistance m k n*s)*
        (Co/((H : ℝ)-(n : ℝ))^2) := by
      simpa only [u, μ, U, s, hnorm, waterCubeFaceConnectionEvent, ite_true] using h2'
    have hCt' : Ct*Real.exp (-Ct⁻¹*twoPhaseSlabDistance m k n*s) ≤ T*D := by
      dsimp [T, D]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (hdecay (inv_nonneg.mpr hCt.le) (min_le_right _ _) k hhalf hmk hkn) hCt.le
    have hdepth := maskedArm_inverse_height_le_depth hδ hH hmk
    calc
      u ≤ Ct*Real.exp (-Ct⁻¹*twoPhaseSlabDistance m k n*s)*
          (Co/((H : ℝ)-(n : ℝ))^2) := h2''
      _ ≤ (T*D)*(S/(H : ℝ)^2) := mul_le_mul hCt' hsuff (by positivity) (by positivity)
      _ = (T*S*D)*(1/(H : ℝ)^2) := by ring
      _ ≤ (T*S*D)*((2/δ)*((k : ℝ)+1)/(H : ℝ)^3) :=
        mul_le_mul_of_nonneg_left hdepth (by positivity)
      _ = (T*S*(2/δ))*((k : ℝ)+1)/(H : ℝ)^3*D := by ring
      _ ≤ A*((k : ℝ)+1)/(H : ℝ)^3*D := by
        have hcoef : T*S*(2/δ) ≤ A := le_add_of_nonneg_left (by positivity)
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) (Real.exp_nonneg _)

end NearCritical
