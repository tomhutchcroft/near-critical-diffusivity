module

public import NearCritical.MaskedFullEnergySeed
public import NearCritical.MaskedBulkExponentialBound
public import NearCritical.BulkUpperFromEnvelopes
public import NearCritical.BulkArmWindowBounds
public import NearCritical.SubcriticalSeedWindow
public import NearCritical.HomogeneousLogIntegration
public import NearCritical.ConductivityUpperBound
public import NearCritical.FiniteCubicUpper

@[expose] public section
noncomputable section
namespace NearCritical
open Set Filter

private theorem seed_sqrt_of_one_add_log {A pc c H Q : ℝ}
    (hc : 0 < c) (hH : 1 ≤ H) (hQ : 0 ≤ Q)
    (hA : A ≤ Q*(1+Real.log H)/H^2 *
      Real.exp (-c*H*Real.sqrt (pc-subcriticalSeedParameter pc c H))) :
    Real.sqrt A ≤ Real.sqrt Q/H^3 := by
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have he : -c*H*Real.sqrt (pc-subcriticalSeedParameter pc c H) = -(7:ℝ)*Real.log H := by
    nlinarith [subcritical_seed_exponent (pc := pc) hc hH]
  rw [he, exp_neg_seven_log hHp] at hA
  have hlog : 1+Real.log H ≤ H := by linarith [Real.log_le_sub_one_of_pos hHp]
  have hseed : A ≤ Q/H^6 := calc
    A ≤ Q*(1+Real.log H)/H^2*(1/H^7) := hA
    _ ≤ Q*H/H^2*(1/H^7) := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hQ) (sq_nonneg _))
      (by positivity)
    _ = Q/H^8 := by field_simp [hHp.ne'] <;> ring
    _ ≤ Q/H^6 := by
      apply div_le_div_of_nonneg_left hQ (by positivity)
      calc
        H^6 = H^6*1 := by ring
        _ ≤ H^6*H^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH) (by positivity)
        _ = H^8 := by ring
  calc
    _ ≤ Real.sqrt (Q/H^6) := Real.sqrt_le_sqrt hseed
    _ = _ := by
      rw [Real.sqrt_div hQ]
      congr 1
      rw [show H^6 = (H^3)^2 by ring, Real.sqrt_sq (by positivity)]

/-- Uniform finite-volume upper bound in the actual masked proof. The full
seed and both auxiliary-energy regimes are supplied by the face estimates.
The same constants apply to every odd height and every transverse width. -/
theorem waterCube_finite_noLog_upper_of_standard_inputs {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧
      ∀ (r R : ℕ) (p : unitInterval),
      let H : ℝ := 2*(r : ℝ)+1
      (criticalPoint d : ℝ) ≤ (p : ℝ) →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/H^2 →
      annealedRelaxed (waterCube d i r R) i (p : ℝ) ≤ C/H^6 := by
  obtain ⟨Cs, εs, hCs, hεs, hseed⟩ :=
    waterCube_annealedBulkRelaxed_subcritical_exponential i hB hb hCo hpc hpc1
      pioneers ordinary δ hδ hδ1
  obtain ⟨Cb, εb, hCb, hεb, hBsub⟩ :=
    waterCube_annealedBulkB_subcritical_exponential i hB hb hCo hpc hpc1
      pioneers ordinary δ hδ hδ1
  let pc : ℝ := criticalPoint d
  let w := (1-pc)/2
  have hw : 0 < w := by dsimp [w, pc]; linarith
  let ε := min (min 1 w) (min εs εb)
  have hε : 0 < ε := lt_min (lt_min zero_lt_one hw) (lt_min hεs hεb)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hεw : ε ≤ w := (min_le_left _ _).trans (min_le_right _ _)
  have hεs' : ε ≤ εs := (min_le_right _ _).trans (min_le_left _ _)
  have hεb' : ε ≤ εb := (min_le_right _ _).trans (min_le_right _ _)
  let c := min (1/Cs) (1/(2*Cb))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcs : c ≤ 1/Cs := min_le_left _ _
  have hcb : c ≤ 1/(2*Cb) := min_le_right _ _
  let Co' := max 1 Co
  have hCo' : 1 ≤ Co' := le_max_left _ _
  have ordinary' : OrdinaryArmWindowInput d Co' := by
    intro p x n hn hp
    exact (ordinary p x n hn hp).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  let Qb := (d : ℝ)*(4*Co'/δ^2)^2
  have hQb : 0 ≤ Qb := by dsimp [Qb]; positivity
  let K := max (Real.sqrt Cb) (Real.sqrt Qb)
  have hK : 0 ≤ K := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  let Q : ℝ := (1/(Real.sqrt (pc/2)*(1-(pc+1)/2)))/2
  have hQ : 0 ≤ Q := by
    have htop : 0 < 1-(pc+1)/2 := by dsimp [pc]; linarith
    dsimp [Q]
    positivity
  let J := 2*K/c^2+K
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  let X := Real.sqrt Cs+Q*J
  have hX : 0 ≤ X := add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hQ hJ)
  obtain ⟨Hseed, hseedWindow⟩ := eventually_atTop.mp
    (subcriticalSeedParameter_eventually_window hpc c)
  let H₀ : ℝ := max 1 Hseed
  have hH₀ : 1 ≤ H₀ := le_max_left _ _
  let C := max (H₀^6) (X^2)
  have hC : 0 < C := (pow_pos (zero_lt_one.trans_le hH₀) 6).trans_le (le_max_left _ _)
  refine ⟨ε, C, hε, hε1, hC, ?_⟩
  intro r R p
  dsimp only
  intro hpcp hp
  let U := waterCube d i r R
  let H : ℝ := 2*(r : ℝ)+1
  let M := bulkBondMask U i H δ
  let a := subcriticalSeedParameter pc c H
  have hU : U.Nonempty := waterCube_nonempty d i r R
  have hH : 1 ≤ H := by
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    dsimp [H]
    linarith
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hHs : 1 ≤ H^2 := one_le_pow₀ hH
  have hpbound : (p : ℝ) ≤ (pc+1)/2 := by
    have hh : (p : ℝ) ≤ pc+w :=
      hp.trans (add_le_add_right ((div_le_self hε.le hHs).trans hεw) _)
    dsimp [w] at hh
    linarith
  have hp1 : (p : ℝ) < 1 := hpbound.trans_lt (by dsimp [pc]; linarith)
  have hpwin : (p : ℝ) ≤ pc+1/H^2 :=
    hp.trans (add_le_add_right (div_le_div_of_nonneg_right hε1 (sq_nonneg _)) _)
  have hpseed : (p : ℝ) ≤ pc+εs/H^2 :=
    hp.trans (add_le_add_right (div_le_div_of_nonneg_right hεs' (sq_nonneg _)) _)
  have hpB : (p : ℝ) ≤ pc+εb/H^2 :=
    hp.trans (add_le_add_right (div_le_div_of_nonneg_right hεb' (sq_nonneg _)) _)
  have hrate {a₀ t : ℝ} (ha₀ : c ≤ a₀) (ht : 0 ≤ t) :
      Real.exp (-a₀*H*t) ≤ Real.exp (-c*H*t) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right ha₀ (mul_nonneg hHp.le ht)
    nlinarith
  by_cases hlarge : H₀ ≤ H
  · have hawin : pc/2 ≤ a ∧ a ≤ pc :=
      hseedWindow H ((le_max_right 1 Hseed).trans hlarge)
    have ha : 0 < a := (by dsimp [pc]; positivity : 0 < pc/2).trans_le hawin.1
    let qa : unitInterval := ⟨a, ha.le, hawin.2.trans (le_of_lt hpc1)⟩
    have hseed' : annealedMaskedRelaxed U i M (p : ℝ) a ≤
        Cs*(1+Real.log H)/H^2*Real.exp (-H*Real.sqrt (pc-a)/Cs) :=
      hseed r R p qa (hawin.2.trans hpcp) hawin.2 hpseed
    have hseed'' : Real.sqrt (annealedMaskedRelaxed U i M (p : ℝ) a) ≤ Real.sqrt Cs/H^3 := by
      apply seed_sqrt_of_one_add_log (pc := pc) hc hH hCs.le
      apply hseed'.trans
      apply mul_le_mul_of_nonneg_left _ (by
        have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
        positivity)
      rw [show -H*Real.sqrt (pc-a)/Cs = -(1/Cs)*H*Real.sqrt (pc-a) by ring]
      exact hrate hcs (Real.sqrt_nonneg _)
    have hsub : ∀ x ∈ Icc a pc, Real.sqrt (annealedMaskedB U i M (p : ℝ) x) ≤
        (K/H)*Real.exp (-(c*H)*Real.sqrt (pc-x)) := by
      intro x hx
      let q : unitInterval := ⟨x, ha.le.trans hx.1, hx.2.trans hpc1.le⟩
      have hb' : annealedMaskedB U i M (p : ℝ) x ≤
          (Cb/H^2)*Real.exp (-H*Real.sqrt (pc-x)/Cb) :=
        hBsub r R p q (hx.2.trans hpcp) hx.2 hpB
      have hb'' : Real.sqrt (annealedMaskedB U i M (p : ℝ) x) ≤
          (Real.sqrt Cb/H)*Real.exp (-(1/(2*Cb))*H*Real.sqrt (pc-x)) := by
        have he : -H*Real.sqrt (pc-x)/Cb = -(1/Cb)*H*Real.sqrt (pc-x) := by ring
        rw [he] at hb'
        have hh := sqrt_exp_envelope hCb.le hHp hb'
        rw [show (1/Cb)/2 = 1/(2*Cb) by field_simp [hCb.ne'] <;> ring] at hh
        exact hh
      apply hb''.trans
      rw [show -(c*H)*Real.sqrt (pc-x) = -c*H*Real.sqrt (pc-x) by ring]
      exact mul_le_mul
        (div_le_div_of_nonneg_right (le_max_left _ _) hHp.le)
        (hrate hcb (Real.sqrt_nonneg _)) (Real.exp_nonneg _) (by positivity)
    have hsup : ∀ x ∈ Icc pc (p : ℝ), Real.sqrt (annealedMaskedB U i M (p : ℝ) x) ≤ K/H := by
      intro x hx
      let q : unitInterval := ⟨x, hpc.le.trans hx.1, hx.2.trans p.property.2⟩
      have hb' : annealedMaskedB U i M (p : ℝ) x ≤ Qb/H^2 :=
        waterCube_bulkB_window_of_standard_ordinary i hCo' ordinary' hδ hδ1.le r R p q
          hpwin (hx.2.trans hpwin)
      calc
        _ ≤ Real.sqrt (Qb/H^2) := Real.sqrt_le_sqrt hb'
        _ = Real.sqrt Qb/H := by rw [Real.sqrt_div hQb, Real.sqrt_sq hHp.le]
        _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hHp.le
    have hwindow : (p : ℝ)-pc ≤ 1/H^2 := by linarith
    have hfull := annealedRelaxed_upper_of_bulk_envelopes hU i δ
      hHp hc hK (Real.sqrt_nonneg Cs) hawin.2 hpcp ha hp1 hwindow hseed'' hsub hsup
    let Y : ℝ := Real.sqrt Cs+((1/(Real.sqrt a*(1-(p : ℝ))))/2)*J
    have hY : 0 ≤ Y := by dsimp [Y]; positivity
    have hYX : Y ≤ X := add_le_add_right
      (mul_le_mul_of_nonneg_right (compact_bulk_factor_le hpc hpc1 hawin.1 hpbound) hJ) _
    change annealedRelaxed U i (p : ℝ) ≤ C/H^6
    change annealedRelaxed U i (p : ℝ) ≤ Y^2/H^6 at hfull
    exact hfull.trans (div_le_div_of_nonneg_right
      (((sq_le_sq₀ hY hX).mpr hYX).trans (le_max_right _ _)) (by positivity))
  · have hpow : H^6 ≤ H₀^6 := pow_le_pow_left₀ hHp.le (lt_of_not_ge hlarge).le 6
    have hsmall : 1 ≤ C/H^6 := (le_div_iff₀ (pow_pos hHp 6)).mpr
      (by simpa only [one_mul] using hpow.trans (le_max_left _ _))
    exact ((annealedRelaxed_le_parameter U hU i p).trans p.property.2).trans hsmall

/-- The odd correlation scale converts the verified window bound into a
finite cubic bound uniform in the transverse width. -/
theorem waterCube_finite_cubic_upper_of_standard_inputs {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ sharp ε C : ℝ, 0 < sharp ∧ sharp ≤ 1 ∧ 0 < ε ∧ 0 < C ∧
      ∀ (R : ℕ) (gap : ℝ), 0 < gap → gap ≤ ε →
        annealedRelaxed (waterCube d i (correlationRadius sharp gap) R) i
          ((criticalPoint d : ℝ)+gap) ≤ C*gap^3 := by
  obtain ⟨sharp, K, hsharp, hsharp1, hK, hbound⟩ :=
    waterCube_finite_noLog_upper_of_standard_inputs i hB hb hCo hpc hpc1
      pioneers ordinary δ hδ hδ1
  let pc : ℝ := criticalPoint d
  let ε := min (sharp/16) ((1-pc)/2)
  have hε : 0 < ε := lt_min (by positivity) (by dsimp [pc]; linarith)
  let C := 64*K/sharp^3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨sharp, ε, C, hsharp, hsharp1, hε, hC, ?_⟩
  intro R gap hg hsmall
  have hsmall' : gap ≤ sharp/16 := hsmall.trans (min_le_left _ _)
  have hcap : gap ≤ (1-pc)/2 := hsmall.trans (min_le_right _ _)
  have hp0 : 0 ≤ pc+gap := add_nonneg hpc.le hg.le
  have hp1 : pc+gap ≤ 1 := by dsimp [pc] at hcap ⊢; linarith
  let p : unitInterval := ⟨pc+gap,hp0,hp1⟩
  let r := correlationRadius sharp gap
  let H : ℝ := correlationHeight sharp gap
  have hH : H = 2*(r : ℝ)+1 := correlationHeight_eq_radius sharp gap
  have hwin : (p : ℝ) ≤ pc+sharp/(2*(r : ℝ)+1)^2 := by
    rw [← hH]
    exact add_le_add_right (correlationHeight_window hsharp hg hsmall') _
  have hup := hbound r R p (le_add_of_nonneg_right hg.le) hwin
  rw [← hH] at hup
  calc
    _ ≤ K/H^6 := hup
    _ = K*(1/H^6) := by ring
    _ ≤ K*(64*gap^3/sharp^3) :=
      mul_le_mul_of_nonneg_left (correlationHeight_inverse_six hsharp hg hsmall') hK.le
    _ = C*gap^3 := by dsimp [C]; ring

end NearCritical
