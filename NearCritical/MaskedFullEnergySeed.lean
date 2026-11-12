module

public import NearCritical.MaskedArmExteriorHead
public import NearCritical.MaskedArmNegativeDecay
public import NearCritical.MaskedBulkTwoArmBK
public import NearCritical.WaterCubeEndpointDepths

@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

private theorem maskedSeed_far_scale {u C D H j l s : ℝ}
    (hC : 0 < C) (hCD : C ≤ D) (hH : 0 < H)
    (hj : 0 ≤ j) (hl : 0 ≤ l) (hjl : j ≤ l+1) (hs : 0 ≤ s)
    (hu : u ≤ C*(j+1)/H^3*Real.exp (-H*s/C)) :
    u ≤ (2*D*(l+1)/H^3)*Real.exp (-H*s/D) := by
  have hD : 0 < D := hC.trans_le hCD
  have hcoef : C*(j+1)/H^3 ≤ 2*D*(l+1)/H^3 := by
    apply div_le_div_of_nonneg_right _ (pow_nonneg hH.le _)
    calc
      C*(j+1) ≤ D*(2*(l+1)) := mul_le_mul hCD (by linarith) (by linarith) hD.le
      _ = _ := by ring
  have hfactor : 0 ≤ 2*D*(l+1)/H^3 := by
    positivity
  have hexp : Real.exp (-H*s/C) ≤ Real.exp (-H*s/D) := by
    apply Real.exp_le_exp.mpr
    have hi := one_div_le_one_div_of_le hC hCD
    have hm := mul_le_mul_of_nonneg_right hi (mul_nonneg hH.le hs)
    calc
      -H*s/C = -((1/C)*(H*s)) := by ring
      _ ≤ -((1/D)*(H*s)) := neg_le_neg hm
      _ = -H*s/D := by ring
  exact hu.trans (mul_le_mul hcoef hexp (Real.exp_nonneg _) hfactor)

set_option maxHeartbeats 1200000 in
/-- Full issued-edge energy under the actual masked law. The harmonic layer
sum retains a logarithm and allows the degenerate height-one box. -/
theorem waterCube_annealedBulkRelaxed_subcritical_exponential {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (r R : ℕ) (p q : unitInterval),
      let U := waterCube d i r R
      let H : ℝ := 2*(r : ℝ)+1
      q ≤ p → q ≤ criticalPoint d →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/H^2 →
      annealedMaskedRelaxed U i (bulkBondMask U i H δ) (p : ℝ) (q : ℝ) ≤
        C*(1+Real.log H)/H^2*Real.exp (-H*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))/C) := by
  obtain ⟨Cp, εp, hCp, hεp, hpos⟩ :=
    maskedWaterCube_positive_face_exponential_midpoint i hB hb hCo hpc hpc1
      pioneers ordinary δ hδ hδ1
  obtain ⟨Cn, εn, hCn, hεn, hneg⟩ :=
    maskedWaterCube_negative_face_exponential_midpoint i hB hb hCo hpc hpc1
      pioneers ordinary δ hδ hδ1
  let w := (1-(criticalPoint d : ℝ))/2
  have hw : 0 < w := by dsimp [w]; linarith
  let ε := min (min 1 w) (min εp εn)
  have hε : 0 < ε := lt_min (lt_min zero_lt_one hw) (lt_min hεp hεn)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hεw : ε ≤ w := (min_le_left _ _).trans (min_le_right _ _)
  have hεp' : ε ≤ εp := (min_le_right _ _).trans (min_le_left _ _)
  have hεn' : ε ≤ εn := (min_le_right _ _).trans (min_le_right _ _)
  have hcap : (criticalPoint d : ℝ)+w < 1 := by dsimp [w]; linarith
  let P : unitInterval := ⟨(criticalPoint d : ℝ)+w, ⟨by linarith, hcap.le⟩⟩
  let D := max 1 (max Cp Cn)
  let O := 4*max 1 Co
  let K := max (Real.exp 1) (4*D*O)
  let C := max D (2*(d : ℝ)*K)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have hC : 0 < C := hD.trans_le (le_max_left _ _)
  have hO : 0 ≤ O := mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
  have hK : 0 ≤ K := (Real.exp_nonneg _).trans (le_max_left _ _)
  refine ⟨C, ε, hC, hε, ?_⟩
  intro r R p q
  dsimp only
  intro hqp hq hp
  let U := waterCube d i r R
  let H : ℝ := 2*(r : ℝ)+1
  let N : ℕ := 2*r+1
  let μ := bulkPercolation U i H δ p q
  let s := Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))
  let E := Real.exp (-H*s/D)
  let F := fun (upper : Bool) (x : DomainVertex U) =>
    μ.real (waterCubeFaceConnectionEvent i r R upper x)
  let W : ℝ := ((2*R+1)^(d-1) : ℕ)
  have hW : 0 < W := by dsimp [W]; positivity
  have hH : 1 ≤ H := by
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    dsimp [H]
    linarith
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hHs : 1 ≤ H^2 := one_le_pow₀ hH
  have hN : (N : ℝ) = H := by dsimp [N, H] <;> push_cast <;> ring
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by nlinarith [(criticalPoint d).property.2, q.property.1]⟩
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (percolationProfile d _)
    infer_instance
  have hpP : p ≤ P := by
    change (p : ℝ) ≤ (criticalPoint d : ℝ)+w
    exact hp.trans (add_le_add_right ((div_le_self hε.le hHs).trans hεw) _)
  have hp1 : (p : ℝ) ≤ (criticalPoint d : ℝ)+((N : ℝ)^2)⁻¹ := by
    rw [hN, ← one_div]
    exact hp.trans (add_le_add_right (div_le_div_of_nonneg_right hε1 (sq_nonneg _)) _)
  have hp_pos : (p : ℝ) ≤ (criticalPoint d : ℝ)+εp/(N : ℝ)^2 := by
    rw [hN]
    exact hp.trans (add_le_add_right (div_le_div_of_nonneg_right hεp' (sq_nonneg _)) _)
  have hp_neg : (p : ℝ) ≤ (criticalPoint d : ℝ)+εn/(N : ℝ)^2 := by
    rw [hN]
    exact hp.trans (add_le_add_right (div_le_div_of_nonneg_right hεn' (sq_nonneg _)) _)
  have hnear (upper : Bool) (x : DomainVertex U) (l : ℕ)
      (hl : l ≤ waterCubeTargetDepth i r upper x.val) :
      F upper x ≤ O/((l : ℝ)+1)^2 := by
    apply (maskedWaterCube_face_probability_le_ordinary ordinary p q hqp i r R δ upper x hp1).trans
    have hlR : (l : ℝ) ≤ waterCubeTargetDepth i r upper x.val := by exact_mod_cast hl
    exact div_le_div_of_nonneg_left hO (by positivity)
      ((sq_le_sq₀ (by positivity) (by positivity)).mpr (add_le_add_left hlR 1))
  have hfarPos (x : DomainVertex U) (hx : x.val ∈ U) (j l : ℕ)
      (hj : waterCubeOppositeDepth i r true x.val = j)
      (hhalf : 2*j ≤ N+1) (hjl : j ≤ l+1) :
      F true x ≤ (2*D*((l : ℝ)+1)/H^3)*E := by
    obtain ⟨hlo, _⟩ := waterCube_sitesPlus_coordinate i r R x
    have hjZ : (j : ℤ) = x.val i+(r : ℤ) := by
      rw [← hj]
      simp only [waterCubeOppositeDepth, ite_true]
      exact Int.toNat_of_nonneg (by omega)
    have hjR : (j : ℝ) = ((x.val i+(r : ℤ) : ℤ) : ℝ) := by exact_mod_cast hjZ
    have hhalf' : 2*(x.val i+(r : ℤ)) ≤ (N : ℤ)+1 := by
      rw [← hjZ]
      exact_mod_cast hhalf
    have h := hpos r R p q x hx hhalf' hqp hq hp_pos
    exact maskedSeed_far_scale hCp ((le_max_left Cp Cn).trans (le_max_right _ _)) hHp
      (Nat.cast_nonneg j) (Nat.cast_nonneg l) (by exact_mod_cast hjl) hs
      (by simpa only [F, μ, ← hN, s, ← hjR] using h)
  have hfarNeg (x : DomainVertex U) (hx : x.val ∈ U) (j l : ℕ)
      (hk : 0 < x.val i+(r : ℤ)) (hj : waterCubeOppositeDepth i r false x.val = j)
      (hhalf : 2*j ≤ N+1) (hjl : j ≤ l+1) :
      F false x ≤ (2*D*((l : ℝ)+1)/H^3)*E := by
    obtain ⟨_, hhi⟩ := waterCube_sitesPlus_coordinate i r R x
    have hjZ : (j : ℤ) = (N : ℤ)-(x.val i+(r : ℤ)) := by
      rw [← hj]
      simp only [waterCubeOppositeDepth, Bool.false_eq_true, ite_false]
      rw [Int.toNat_of_nonneg (by omega)]
      dsimp [N]
      omega
    have hjR : (j : ℝ) = ((((N : ℤ)-(x.val i+(r : ℤ))) : ℤ) : ℝ) := by
      exact_mod_cast hjZ
    have hhalf' : 2*((N : ℤ)-(x.val i+(r : ℤ))) ≤ (N : ℤ)+1 := by
      rw [← hjZ]
      exact_mod_cast hhalf
    have h := hneg r R p q x hx hk hhalf' hqp hq hp_neg
    exact maskedSeed_far_scale hCn ((le_max_right Cp Cn).trans (le_max_right _ _)) hHp
      (Nat.cast_nonneg j) (Nat.cast_nonneg l) (by exact_mod_cast hjl) hs
      (by
        rw [hjR]
        simpa only [F, μ, ← hN, s] using h)
  have hArm (e : IssuedBond U) : μ.real {ω | sourceTwoArm U i ω e} ≤
      (K/H^3*E)*(1/(waterCubeBaseDepth i r e.val.1+1 : ℝ)) := by
    let l := waterCubeBaseDepth i r e.val.1
    let k := waterCubeLayer i r e.val.1
    let σ := waterCubeDirectionStep i e
    let t := (issuedNetwork U).tail e
    let z := (issuedNetwork U).head e
    have htU : t.val ∈ U := (Finset.mem_product.mp e.property).1
    have hk : k < N := waterCubeLayer_lt i r R htU
    have hσ : σ ≤ 1 := waterCubeDirectionStep_le_one i e
    change μ.real _ ≤ (K/H^3*E)*(1/(l+1 : ℝ))
    by_cases hr : r = 0
    · have hl : l = 0 := by simp [l, waterCubeBaseDepth, hr]
      have hH' : H = 1 := by simp [H, hr]
      have hE : Real.exp (-1) ≤ E := by
        apply Real.exp_le_exp.mpr
        change -1 ≤ -H*s/D
        rw [hH', neg_one_mul, neg_div]
        exact neg_le_neg ((div_le_iff₀ hD).mpr (by simpa using hs1.trans hD1))
      have hlow : 1 ≤ K*E := by
        calc
          1 = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
          _ ≤ _ := mul_le_mul (le_max_left _ _) hE (Real.exp_nonneg _) hK
      exact (measureReal_le_one : μ.real _ ≤ 1).trans
        (by simpa only [hl, hH', Nat.cast_zero, zero_add, one_pow, div_one, mul_one] using hlow)
    have hcoord := waterCube_endpoint_coordinates i r R e
    have hcoord' : t.val i = (k : ℤ)-(r : ℤ) ∧ z.val i = (k : ℤ)-(r : ℤ)+σ := hcoord
    have hdepth := waterCube_endpoint_depths i r R e
    have hdepth' : waterCubeOppositeDepth i r true t.val = k ∧
        waterCubeOppositeDepth i r true z.val = k+σ ∧
        waterCubeOppositeDepth i r false t.val = N-k ∧
        waterCubeOppositeDepth i r false z.val = N-k-σ := hdepth
    have hl : l = min k (2*r-k) := rfl
    have hhead (upper : Bool) (hzU : z.val ∉ U)
        (hz : z ∉ (if upper then positiveFace U i else negativeFace U i)) :
        F upper z ≤ F upper t := by
      have hsub := rectangularBox_exterior_head_connection_subset
        (fun j => if j=i then r else R) e _ hzU hz
      exact measureReal_mono hsub (measure_ne_top μ _)
    have hbk : μ.real {ω | sourceTwoArm U i ω e} ≤
        F false t*F true z + F true t*F false z :=
      bulk_sourceTwoArm_le_connectionProducts U i H δ p q P hcap hpP (hqp.trans hpP) e
    let Near := O/((l : ℝ)+1)^2
    let Far := (2*D*((l : ℝ)+1)/H^3)*E
    have hNear : 0 ≤ Near := by dsimp [Near]; positivity
    have hFar : 0 ≤ Far := by dsimp [Far]; positivity
    have hprod : F false t*F true z + F true t*F false z ≤ 2*(Near*Far) := by
      by_cases hhalf : k ≤ r
      · have hl' : l=k := hl.trans (min_eq_left (by omega))
        have hnt : F false t ≤ Near := hnear false t l (by
          change l ≤ waterCubeOppositeDepth i r true t.val
          rw [hdepth'.1, hl'])
        have hnz : F false z ≤ Near := hnear false z l (by
          change l ≤ waterCubeOppositeDepth i r true z.val
          rw [hdepth'.2.1, hl']
          omega)
        have hft : F true t ≤ Far :=
          hfarPos t htU k l hdepth'.1 (by dsimp [N]; omega) (by omega)
        have hfz : F true z ≤ Far := by
          by_cases hzU : z.val ∈ U
          · exact hfarPos z hzU (k+σ) l hdepth'.2.1 (by dsimp [N]; omega) (by omega)
          · apply (hhead true hzU ?_).trans hft
            intro hz
            have hc := rectangularBox_positiveFace_coordinate
              (fun j => if j=i then r else R) i hz
            simp only [ite_true] at hc
            omega
        calc
          _ ≤ Near*Far+Far*Near := add_le_add
            (mul_le_mul hnt hfz measureReal_nonneg hNear)
            (mul_le_mul hft hnz measureReal_nonneg hFar)
          _ = _ := by ring
      · have hl' : l=2*r-k := hl.trans (min_eq_right (by omega))
        have hnt : F true t ≤ Near := hnear true t l (by
          change l ≤ waterCubeOppositeDepth i r false t.val
          rw [hdepth'.2.2.1, hl']
          dsimp [N]
          omega)
        have hnz : F true z ≤ Near := hnear true z l (by
          change l ≤ waterCubeOppositeDepth i r false z.val
          rw [hdepth'.2.2.2, hl']
          dsimp [N]
          omega)
        have hft : F false t ≤ Far :=
          hfarNeg t htU (N-k) l (by omega) hdepth'.2.2.1
            (by dsimp [N]; omega) (by dsimp [N]; omega)
        have hfz : F false z ≤ Far := by
          by_cases hzU : z.val ∈ U
          · exact hfarNeg z hzU (N-k-σ) l (by omega) hdepth'.2.2.2
              (by dsimp [N]; omega) (by dsimp [N]; omega)
          · apply (hhead false hzU ?_).trans hft
            intro hz
            have hc := rectangularBox_negativeFace_coordinate
              (fun j => if j=i then r else R) i hz
            simp only [ite_true] at hc
            omega
        calc
          _ ≤ Far*Near+Near*Far := add_le_add
            (mul_le_mul hft hnz measureReal_nonneg hFar)
            (mul_le_mul hnt hfz measureReal_nonneg hNear)
          _ = _ := by ring
    refine hbk.trans (hprod.trans ?_)
    calc
      2*(Near*Far) = ((4*D*O)/H^3*E)*(1/(l+1 : ℝ)) := by
        dsimp [Near, Far]
        field_simp <;> ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  have hlog : 0 ≤ 1+Real.log H := by linarith [Real.log_nonneg hH]
  have hsum : (∑ e : IssuedBond U, μ.real {ω | sourceTwoArm U i ω e}) ≤
      (K/H^3*E)*(2*(d : ℝ)*W*(1+Real.log H)) := by
    calc
      _ ≤ ∑ e : IssuedBond U, (K/H^3*E)*(1/(waterCubeBaseDepth i r e.val.1+1 : ℝ)) :=
        Finset.sum_le_sum (fun e _ => hArm e)
      _ = _ := by rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [U, W, N, hN] using sum_issued_waterCube_inverse_depth_le i r R)
        (by positivity)
  have hU := waterCube_annealedBulkRelaxed_le_sourceTwoArm_probabilities d i r R δ p q
  have hWR : W = (2*(R : ℝ)+1)^(d-1) := by dsimp [W] <;> push_cast <;> ring
  change annealedMaskedRelaxed U i (bulkBondMask U i H δ) (p : ℝ) (q : ℝ) ≤
    C*(1+Real.log H)/H^2*Real.exp (-H*s/C)
  calc
    _ ≤ H^2/(H*W)*(∑ e : IssuedBond U, μ.real {ω | sourceTwoArm U i ω e}) := by
      simpa only [H, U, μ, hWR] using hU
    _ ≤ H^2/(H*W)*((K/H^3*E)*(2*(d : ℝ)*W*(1+Real.log H))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2*(d : ℝ)*K)*(1+Real.log H)/H^2*E := by
      field_simp [hHp.ne', hW.ne'] <;> ring
    _ ≤ _ := by
      refine mul_le_mul ?_ ?_ (Real.exp_nonneg _) (by positivity)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog) (sq_nonneg _)
      · change Real.exp (-H*s/D) ≤ Real.exp (-H*s/C)
        apply Real.exp_le_exp.mpr
        have hi := one_div_le_one_div_of_le hD (le_max_left D (2*(d : ℝ)*K))
        have hm := mul_le_mul_of_nonneg_right hi (mul_nonneg hHp.le hs)
        calc
          -H*s/D = -((1/D)*(H*s)) := by ring
          _ ≤ -((1/C)*(H*s)) := neg_le_neg hm
          _ = -H*s/C := by ring

end NearCritical
