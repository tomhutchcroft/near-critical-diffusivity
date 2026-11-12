module

public import NearCritical.MaskedArmFinal

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

private theorem maskedArm_midpoint_exp_le {δ a s : ℝ} {H : ℕ} {k : ℤ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hk : 2*k ≤ (H : ℤ)+1)
    (hmk : ⌊δ*(H : ℝ)/2⌋ ≤ k)
    (hkn : k ≤ (H : ℤ)-⌊δ*(H : ℝ)/2⌋-1) :
    let m : ℤ := ⌊δ*(H : ℝ)/2⌋
    let n : ℤ := (H : ℤ)-m-1
    Real.exp (-a*twoPhaseSlabDistance m k n*s) ≤
      Real.exp (2*a)*Real.exp (-(a*(1-δ)/2)*(H : ℝ)*s) := by
  dsimp only
  let m : ℤ := ⌊δ*(H : ℝ)/2⌋
  let n : ℤ := (H : ℤ)-m-1
  have hmn : m ≤ n := hmk.trans hkn
  have hnR : ((n-m).toNat : ℝ) = (n : ℝ)-(m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hmn)
  have hkR : ((k-m).toNat : ℝ) = (k : ℝ)-(m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hmk)
  have hd : twoPhaseSlabDistance m k n = (n : ℝ)-(k : ℝ) := by
    have hle : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    rw [twoPhaseSlabDistance, hnR, hkR, show
      (n : ℝ)-(m : ℝ)-((k : ℝ)-(m : ℝ)) = (n : ℝ)-(k : ℝ) by ring,
      abs_of_nonneg (sub_nonneg.mpr hle)]
  have hfloor : (m : ℝ) ≤ δ*(H : ℝ)/2 := Int.floor_le _
  have hk' : 2*(k : ℝ) ≤ (H : ℝ)+1 := by exact_mod_cast hk
  have hn' : (n : ℝ) = (H : ℝ)-(m : ℝ)-1 := by dsimp only [n]; push_cast <;> rfl
  have hgap : (1-δ)*(H : ℝ)/4-1 ≤ twoPhaseSlabDistance m k n/2 := by
    rw [hd, hn']
    nlinarith
  have h := maskedArm_exp_one_layer_loss (a := 2*a) (by positivity) hs hs1 hgap
  change Real.exp (-a*twoPhaseSlabDistance m k n*s) ≤
    Real.exp (2*a)*Real.exp (-(a*(1-δ)/2)*(H : ℝ)*s)
  rwa [show -(2*a)*s*(twoPhaseSlabDistance m k n/2) =
      -a*twoPhaseSlabDistance m k n*s by ring,
    show -(2*a)*s*((1-δ)*(H : ℝ)/4) = -(a*(1-δ)/2)*(H : ℝ)*s by ring] at h

set_option maxHeartbeats 900000 in
/-- One additional integer layer beyond the lower half is allowed. This
covers either endpoint of the vertical bond straddling the midpoint. -/
theorem maskedWaterCube_positive_face_exponential_midpoint {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (r R : ℕ) (p q : unitInterval) (x : DomainVertex (waterCube d i r R)),
      let H : ℕ := 2*r+1
      let k := x.val i+(r : ℤ)
      x.val ∈ waterCube d i r R → 2*k ≤ (H : ℤ)+1 →
      q ≤ p → q ≤ criticalPoint d →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(H : ℝ)^2 →
      (bulkPercolation (waterCube d i r R) i (H : ℝ) δ p q).real
        (waterCubeFaceConnectionEvent i r R true x) ≤
          C*((k : ℝ)+1)/(H : ℝ)^3 *
            Real.exp (-(H : ℝ)*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))/C) := by
  obtain ⟨Cf, εf, hCf, hεf, hfar⟩ :=
    maskedWaterCube_positive_face_exponential i hB hb hCo hpc hpc1 pioneers ordinary δ hδ hδ1
  obtain ⟨Ct, εt, hCt, hεt, htwo⟩ :=
    maskedWaterCube_two_segment_decay i hB hb hCo hpc hpc1 pioneers ordinary
  let w := (1-(criticalPoint d : ℝ))/2
  have hw : 0 < w := by dsimp [w]; linarith
  let ε := min (min 1 w) (min εf εt)
  have hε : 0 < ε := lt_min (lt_min zero_lt_one hw) (lt_min hεf hεt)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hεw : ε ≤ w := (min_le_left _ _).trans (min_le_right _ _)
  have hεf' : ε ≤ εf := (min_le_right _ _).trans (min_le_left _ _)
  have hεt' : ε ≤ εt := (min_le_right _ _).trans (min_le_right _ _)
  have hP' : (criticalPoint d : ℝ)+w < 1 := by dsimp [w]; linarith
  let P : unitInterval := ⟨(criticalPoint d : ℝ)+w, ⟨by linarith, hP'.le⟩⟩
  let H₀ : ℝ := max 1 (4/(1-δ))
  let c := min (1/Cf) (Ct⁻¹*(1-δ)/2)
  let S := 4*Co/δ^2
  let T := Ct*Real.exp (2*Ct⁻¹)
  let A := Cf + T*S*(2/δ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hδ' : 0 < 1-δ := sub_pos.mpr hδ1
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨C, hC, hclose⟩ := maskedArm_close_scales hA hc (le_max_left 1 (4/(1-δ)))
  refine ⟨C, ε, hC, hε, ?_⟩
  intro r R p q x
  dsimp only
  intro hx hhalf hqp hq hp
  let H : ℕ := 2*r+1
  let k := x.val i+(r : ℤ)
  let m : ℤ := ⌊δ*(H : ℝ)/2⌋
  let n : ℤ := (H : ℤ)-m-1
  let s := Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))
  let U := waterCube d i r R
  let μ := bulkPercolation U i (H : ℝ) δ p q
  let u := μ.real (waterCubeFaceConnectionEvent i r R true x)
  have hH : 0 < H := by dsimp [H]; omega
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hH1 : 1 ≤ (H : ℝ) := by exact_mod_cast (show 1 ≤ H by omega)
  have hHs : 1 ≤ (H : ℝ)^2 := one_le_pow₀ hH1
  have hnorm : (H : ℝ) = 2*(r : ℝ)+1 := by dsimp [H] <;> push_cast <;> ring
  change (p : ℝ) ≤ (criticalPoint d : ℝ) + ε / (H : ℝ)^2 at hp
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
  let D := Real.exp (-c*(H : ℝ)*s)
  by_cases hf : 2*k ≤ (H : ℤ)
  · have hpf : (p : ℝ) ≤ (criticalPoint d : ℝ)+εf/(H : ℝ)^2 :=
      hp.trans (add_le_add_right (div_le_div_of_nonneg_right hεf' (sq_nonneg _)) _)
    have hb := hfar r R p q x hx hf hqp hq hpf
    have hcoef : Cf ≤ A := le_add_of_nonneg_right (by positivity)
    refine hb.trans (mul_le_mul ?_ ?_ (Real.exp_nonneg _) (by positivity))
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity))
        (by positivity)
    · change Real.exp (-(H : ℝ)*s/Cf) ≤ D
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (min_le_left (1/Cf) (Ct⁻¹*(1-δ)/2))
        (mul_nonneg hHR.le hs)
      calc
        -(H : ℝ)*s/Cf = -((1/Cf)*((H : ℝ)*s)) := by ring
        _ ≤ -(c*((H : ℝ)*s)) := neg_le_neg hh
        _ = -c*(H : ℝ)*s := by ring
  · have hhalf' : 2*k ≤ (H : ℤ)+1 := hhalf
    have hmid : 2*k = (H : ℤ)+1 := by omega
    have hmidR : 2*(k : ℝ) = (H : ℝ)+1 := by exact_mod_cast hmid
    have hlarge' : 4 ≤ (1-δ)*(H : ℝ) := by
      have h := (le_max_right (1 : ℝ) (4/(1-δ))).trans hlarge
      simpa only [mul_comm] using (div_le_iff₀ hδ').mp h
    obtain ⟨hm, hnH, _, _, _⟩ := maskedArm_cut_rounding δ H hδ.le
    have hfloor : (m : ℝ) ≤ δ*(H : ℝ)/2 := Int.floor_le _
    have hnR : (n : ℝ) = (H : ℝ)-(m : ℝ)-1 := by dsimp only [n]; push_cast <;> rfl
    have hmk : m ≤ k := by
      exact_mod_cast (show (m : ℝ) ≤ (k : ℝ) by nlinarith)
    have hkn : k ≤ n := by
      exact_mod_cast (show (k : ℝ) ≤ (n : ℝ) by nlinarith)
    have hmn := hmk.trans hkn
    have hn := hm.trans hmn
    have hpP : p ≤ P := by
      change (p : ℝ) ≤ (criticalPoint d : ℝ)+w
      exact hp.trans (add_le_add_right ((div_le_self hε.le hHs).trans hεw) _)
    have hp1 : (p : ℝ) ≤ (criticalPoint d : ℝ)+((H : ℝ)^2)⁻¹ := by
      rw [← one_div]
      exact hp.trans (add_le_add_right (div_le_div_of_nonneg_right hε1 (sq_nonneg _)) _)
    have hp_t : (p : ℝ) ≤ (criticalPoint d : ℝ)+εt/(((m : ℝ)+1)*((n : ℝ)+1)) :=
      hp.trans (add_le_add_right ((div_le_div_of_nonneg_right hεt' (sq_nonneg _)).trans
        (maskedArm_window_le hH hm hmn hnH hεt.le)) _)
    have hsuff : Co/((H : ℝ)-(n : ℝ))^2 ≤ S/(H : ℝ)^2 :=
      maskedArm_suffix_scale_le hδ hH hCo
    have hphysical_m : m = ⌊δ*(2*(r : ℝ)+1)/2⌋ := by
      change ⌊δ*(H : ℝ)/2⌋ = _
      rw [hnorm]
    have hphysical_n : n = (2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1 := by
      change (H : ℤ)-m-1 = _
      rw [hnormZ, hphysical_m] <;> push_cast <;> ring
    have h2 := htwo r R δ p q P x
    dsimp only at h2
    rw [← hphysical_n, ← hphysical_m] at h2
    have h2' := h2 hx hm hn hk hkn hqp hq hP' hpP (by simpa only [H] using hp1) hp_t
    have h2'' : u ≤ Ct*Real.exp (-Ct⁻¹*twoPhaseSlabDistance m k n*s)*
        (Co/((H : ℝ)-(n : ℝ))^2) := by
      simpa only [u, μ, U, s, hnorm, waterCubeFaceConnectionEvent, ite_true] using h2'
    have hE : Real.exp (-Ct⁻¹*twoPhaseSlabDistance m k n*s) ≤
        Real.exp (2*Ct⁻¹)*D := by
      apply (maskedArm_midpoint_exp_le (δ := δ) (inv_nonneg.mpr hCt.le)
        hs hs1 hhalf' hmk hkn).trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right
        (min_le_right (1/Cf) (Ct⁻¹*(1-δ)/2)) (mul_nonneg hHR.le hs)
      change -(Ct⁻¹*(1-δ)/2)*(H : ℝ)*s ≤ -c*(H : ℝ)*s
      nlinarith
    have hT' : Ct*Real.exp (-Ct⁻¹*twoPhaseSlabDistance m k n*s) ≤ T*D := by
      dsimp only [T]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hE hCt.le
    have hdepth := maskedArm_inverse_height_le_depth hδ hH hmk
    calc
      u ≤ Ct*Real.exp (-Ct⁻¹*twoPhaseSlabDistance m k n*s)*
          (Co/((H : ℝ)-(n : ℝ))^2) := h2''
      _ ≤ (T*D)*(S/(H : ℝ)^2) := mul_le_mul hT' hsuff (by positivity) (by positivity)
      _ = (T*S*D)*(1/(H : ℝ)^2) := by ring
      _ ≤ (T*S*D)*((2/δ)*((k : ℝ)+1)/(H : ℝ)^3) :=
        mul_le_mul_of_nonneg_left hdepth (by positivity)
      _ = (T*S*(2/δ))*((k : ℝ)+1)/(H : ℝ)^3*D := by ring
      _ ≤ A*((k : ℝ)+1)/(H : ℝ)^3*D := by
        have hcoef : T*S*(2/δ) ≤ A := le_add_of_nonneg_left hCf.le
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) (Real.exp_nonneg _)

end NearCritical
