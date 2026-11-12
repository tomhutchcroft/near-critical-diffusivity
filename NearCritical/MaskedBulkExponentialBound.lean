module

public import NearCritical.MaskedBulkTwoArmBK
public import NearCritical.MaskedBulkCountBound
public import NearCritical.MaskedArmNegativeDecay
public import NearCritical.TwoPhaseSlabMaskGeometry

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

private theorem maskedBulk_face_le_ordinary {d : ℕ} {Co : ℝ} (hCo : 0 ≤ Co)
    (ordinary : OrdinaryArmWindowInput d Co) (i : Fin d) (r R : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (p q : unitInterval) (hqp : q ≤ p)
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ)+(((2*r+1 : ℕ) : ℝ)^2)⁻¹)
    (upper : Bool) (x : DomainVertex (waterCube d i r R))
    (hx : x.val ∈ bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ) :
    (bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).real
      (waterCubeFaceConnectionEvent i r R upper x) ≤
        (4*Co/δ^2)/(2*(r : ℝ)+1)^2 := by
  let U := waterCube d i r R
  let H := 2*(r : ℝ)+1
  let μ := bulkPercolation U i H δ p q
  let D := waterCubeTargetDepth i r upper x.val
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨hxU, hnear⟩ := (mem_bulkVertices U i H δ x.val).mp hx
  rw [waterCube_twoFaceDistance_eq_min i r R x.val hxU] at hnear
  have hnear₀ : δ*H/2 < (x.val i : ℝ)+(r : ℝ) :=
    hnear.trans_le (min_le_left _ _)
  have hnear₁ : δ*H/2 < (r : ℝ)+1-(x.val i : ℝ) :=
    hnear.trans_le (min_le_right _ _)
  obtain ⟨hlo, hhi⟩ := waterCube_sitesPlus_coordinate i r R x
  have hD : δ*H/2 < (D : ℝ) := by
    cases upper
    · have he : (D : ℝ) = (x.val i : ℝ)+(r : ℝ) := by
        exact_mod_cast (show (D : ℤ) = x.val i+(r : ℤ) by
          dsimp [D, waterCubeTargetDepth, waterCubeOppositeDepth]
          exact Int.toNat_of_nonneg (by omega))
      rwa [he]
    · have he : (D : ℝ) = (r : ℝ)+1-(x.val i : ℝ) := by
        exact_mod_cast (show (D : ℤ) = (r : ℤ)+1-x.val i by
          dsimp [D, waterCubeTargetDepth, waterCubeOppositeDepth]
          exact Int.toNat_of_nonneg (by omega))
      rwa [he]
  have hδH : 0 < δ*H/2 := by positivity
  have hDp : 0 < (D : ℝ) := hδH.trans hD
  have hDpos : 0 < D := by exact_mod_cast hDp
  have hDnat : 1 ≤ D := by omega
  have hDH : (D : ℝ) ≤ ((2*r+1 : ℕ) : ℝ) := by
    exact_mod_cast waterCube_targetDepth_le_height i r R upper x
  have hpD : (p : ℝ) ≤ (criticalPoint d : ℝ)+((D : ℝ)^2)⁻¹ := by
    have hi : (((2*r+1 : ℕ) : ℝ)^2)⁻¹ ≤ ((D : ℝ)^2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hDp)
        ((sq_le_sq₀ hDp.le (hDp.le.trans hDH)).mpr hDH)
    exact hp.trans (add_le_add_right hi _)
  let E := extrinsicRadiusArmEvent x.val ((D : ℝ)/2)
  have hsubset : waterCubeFaceConnectionEvent i r R upper x ⊆ E :=
    waterCube_face_subset_extrinsicArm i r R upper x (by change (D : ℝ)/2 < D; linarith)
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (percolationProfile d _)
    infer_instance
  have hdom : μ.real E ≤ (percolation d p).real E := by
    change (bulkPercolation U i H δ p q).real E ≤ _
    rw [bulkPercolation_eq_masked]
    exact maskedPercolation_event_real_le_homogeneous _ p q p le_rfl hqp
      (measurableSet_extrinsicRadiusArmEvent _ _) (extrinsicRadiusArmEvent_increasing _ _)
  change μ.real _ ≤ (4*Co/δ^2)/H^2
  calc
    _ ≤ μ.real E := measureReal_mono hsubset (measure_ne_top μ E)
    _ ≤ (percolation d p).real E := hdom
    _ ≤ Co/(D : ℝ)^2 := ordinary p x.val D hDnat hpD
    _ ≤ Co/(δ*H/2)^2 :=
      div_le_div_of_nonneg_left hCo (sq_pos_of_pos hδH)
        ((sq_le_sq₀ hδH.le hDp.le).mpr hD.le)
    _ = _ := by field_simp <;> ring

private theorem maskedBulk_normalize_far {u C D H k s : ℝ}
    (hC : 0 < C) (hCD : C ≤ D) (hH : 1 ≤ H) (hk : 0 ≤ k) (hkH : k ≤ H)
    (hs : 0 ≤ s) (hu : u ≤ C*(k+1)/H^3*Real.exp (-H*s/C)) :
    u ≤ (2*D/H^2)*Real.exp (-H*s/D) := by
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hDp : 0 < D := hC.trans_le hCD
  have hcoef : C*(k+1)/H^3 ≤ 2*D/H^2 := by
    have hmul : C*(k+1) ≤ D*(2*H) :=
      mul_le_mul hCD (by linarith) (by linarith) hDp.le
    calc
      _ ≤ D*(2*H)/H^3 := div_le_div_of_nonneg_right hmul (by positivity)
      _ = _ := by field_simp <;> ring
  have hexp : Real.exp (-H*s/C) ≤ Real.exp (-H*s/D) := by
    apply Real.exp_le_exp.mpr
    have hi := one_div_le_one_div_of_le hC hCD
    have hm := mul_le_mul_of_nonneg_right hi (mul_nonneg hHp.le hs)
    calc
      -H*s/C = -((1/C)*(H*s)) := by ring
      _ ≤ -((1/D)*(H*s)) := neg_le_neg hm
      _ = -H*s/D := by ring
  exact hu.trans (mul_le_mul hcoef hexp (Real.exp_nonneg _) (by positivity))

set_option maxHeartbeats 1200000 in
/-- The actual masked auxiliary energy has no logarithmic loss. Both
orientations of every bulk bond contribute one exponentially small face
factor and one ordinary face factor. -/
theorem waterCube_annealedBulkB_subcritical_exponential {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (r R : ℕ) (p q : unitInterval),
      let H : ℝ := 2*(r : ℝ)+1
      q ≤ p → q ≤ criticalPoint d →
      (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/H^2 →
      annealedMaskedB (waterCube d i r R) i
        (bulkBondMask (waterCube d i r R) i H δ) (p : ℝ) (q : ℝ) ≤
          C/H^2*Real.exp (-H*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))/C) := by
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
  let D := max Cp Cn
  let O := 4*Co/δ^2
  let K := 4*O*D
  let C := max D ((d : ℝ)*K)
  have hD : 0 < D := hCp.trans_le (le_max_left _ _)
  have hC : 0 < C := hD.trans_le (le_max_left _ _)
  have hO : 0 ≤ O := by dsimp [O]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨C, ε, hC, hε, ?_⟩
  intro r R p q
  dsimp only
  intro hqp hq hp
  let U := waterCube d i r R
  let H : ℝ := 2*(r : ℝ)+1
  let N : ℕ := 2*r+1
  let M := bulkBondMask U i H δ
  let μ := bulkPercolation U i H δ p q
  let s := Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))
  let E := Real.exp (-H*s/D)
  let F := fun (upper : Bool) (x : DomainVertex U) =>
    μ.real (waterCubeFaceConnectionEvent i r R upper x)
  have hH : 1 ≤ H := by
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    dsimp [H]
    linarith
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hHs : 1 ≤ H^2 := one_le_pow₀ hH
  have hN : (N : ℝ) = H := by dsimp [N, H] <;> push_cast <;> ring
  have hs : 0 ≤ s := Real.sqrt_nonneg _
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
  have hnear (upper : Bool) (x : DomainVertex U) (hx : x.val ∈ bulkVertices U i H δ) :
      F upper x ≤ O/H^2 :=
    maskedBulk_face_le_ordinary hCo ordinary i r R δ hδ p q hqp hp1 upper x hx
  have hfarPos (x : DomainVertex U) (hx : x.val ∈ U)
      (hk : 2*(x.val i+(r : ℤ)) ≤ (N : ℤ)+1) :
      F true x ≤ (2*D/H^2)*E := by
    have hb := hpos r R p q x hx hk hqp hq hp_pos
    obtain ⟨hlo, hhi⟩ := waterCube_sitesPlus_coordinate i r R x
    have hk₀ : 0 ≤ ((x.val i+(r : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast (show 0 ≤ x.val i+(r : ℤ) by omega)
    have hkH : ((x.val i+(r : ℤ) : ℤ) : ℝ) ≤ H := by
      rw [← hN]
      exact_mod_cast (show x.val i+(r : ℤ) ≤ (N : ℤ) by dsimp [N]; omega)
    exact maskedBulk_normalize_far hCp (le_max_left _ _) hH hk₀ hkH hs
      (by simpa only [F, μ, ← hN, s] using hb)
  have hfarNeg (x : DomainVertex U) (hx : x.val ∈ U)
      (hk : 0 < x.val i+(r : ℤ))
      (hk' : 2*((N : ℤ)-(x.val i+(r : ℤ))) ≤ (N : ℤ)+1) :
      F false x ≤ (2*D/H^2)*E := by
    have hb := hneg r R p q x hx hk hk' hqp hq hp_neg
    obtain ⟨hlo, hhi⟩ := waterCube_sitesPlus_coordinate i r R x
    have hk₀ : 0 ≤ ((((N : ℤ)-(x.val i+(r : ℤ))) : ℤ) : ℝ) := by
      exact_mod_cast (show 0 ≤ (N : ℤ)-(x.val i+(r : ℤ)) by dsimp [N]; omega)
    have hkH : ((((N : ℤ)-(x.val i+(r : ℤ))) : ℤ) : ℝ) ≤ H := by
      rw [← hN]
      exact_mod_cast (show (N : ℤ)-(x.val i+(r : ℤ)) ≤ (N : ℤ) by omega)
    exact maskedBulk_normalize_far hCn (le_max_right _ _) hH hk₀ hkH hs
      (by simpa only [F, μ, ← hN, s] using hb)
  have hpositive (x : DomainVertex U) (hx : x.val ∈ bulkVertices U i H δ) :
      0 < x.val i+(r : ℤ) := by
    obtain ⟨hxU, hd⟩ := (mem_bulkVertices U i H δ x.val).mp hx
    rw [waterCube_twoFaceDistance_eq_min i r R x.val hxU] at hd
    have hδH : 0 < δ*H/2 := by positivity
    have h := hδH.trans (hd.trans_le (min_le_left _ _))
    exact_mod_cast h
  have hArm : ∀ e ∈ M, μ.real {ω | sourceTwoArm U i ω e} ≤ (K*E)/H^4 := by
    intro e he
    let t := (issuedNetwork U).tail e
    let z := (issuedNetwork U).head e
    have ht : t.val ∈ bulkVertices U i H δ :=
      ((mem_bulkBondMask U i H δ e).mp he).1
    have hz : z.val ∈ bulkVertices U i H δ :=
      ((mem_bulkBondMask U i H δ e).mp he).2
    have htU : t.val ∈ U := bulkVertices_subset U i H δ ht
    have hzU : z.val ∈ U := bulkVertices_subset U i H δ hz
    have hstep : t.val i ≤ z.val i ∧ z.val i ≤ t.val i+1 :=
      twoPhase_bond_height_step e.val i
    have hbk : μ.real {ω | sourceTwoArm U i ω e} ≤
        F false t*F true z + F true t*F false z :=
      bulk_sourceTwoArm_le_connectionProducts U i H δ p q P hcap hpP (hqp.trans hpP) e
    have hprod : F false t*F true z + F true t*F false z ≤
        2*((O/H^2)*((2*D/H^2)*E)) := by
      by_cases hhalf : t.val i+(r : ℤ) ≤ (r : ℤ)
      · have hft := hfarPos t htU (by dsimp [N]; omega)
        have hfz := hfarPos z hzU (by dsimp [N]; omega)
        have ha := mul_le_mul (hnear false t ht) hfz measureReal_nonneg (by positivity)
        have hb := mul_le_mul hft (hnear false z hz) measureReal_nonneg (by positivity)
        calc
          _ ≤ (O/H^2)*((2*D/H^2)*E) + ((2*D/H^2)*E)*(O/H^2) :=
            add_le_add ha hb
          _ = _ := by ring
      · have hft := hfarNeg t htU (hpositive t ht) (by dsimp [N]; omega)
        have hfz := hfarNeg z hzU (hpositive z hz) (by dsimp [N]; omega)
        have ha := mul_le_mul hft (hnear true z hz) measureReal_nonneg (by positivity)
        have hb := mul_le_mul (hnear true t ht) hfz measureReal_nonneg (by positivity)
        calc
          _ ≤ ((2*D/H^2)*E)*(O/H^2) + (O/H^2)*((2*D/H^2)*E) :=
            add_le_add ha hb
          _ = _ := by ring
    apply hbk.trans (hprod.trans_eq _)
    dsimp only [K]
    field_simp <;> ring
  have hcount := waterCube_annealedBulkB_le_of_uniform_twoArm d i r R δ p q (K*E)
    (mul_nonneg hK (Real.exp_nonneg _)) hArm
  change annealedMaskedB U i M (p : ℝ) (q : ℝ) ≤ C/H^2*Real.exp (-H*s/C)
  calc
    _ ≤ (d : ℝ)*(K*E)/H^2 := hcount
    _ = ((d : ℝ)*K)/H^2*E := by ring
    _ ≤ _ := by
      refine mul_le_mul (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
        ?_ (Real.exp_nonneg _) (by positivity)
      change Real.exp (-H*s/D) ≤ Real.exp (-H*s/C)
      apply Real.exp_le_exp.mpr
      have hi := one_div_le_one_div_of_le hD (le_max_left D ((d : ℝ)*K))
      have hm := mul_le_mul_of_nonneg_right hi (mul_nonneg hHp.le hs)
      calc
        -H*s/D = -((1/D)*(H*s)) := by ring
        _ ≤ -((1/C)*(H*s)) := neg_le_neg hm
        _ = -H*s/C := by ring

/-- The same bound expressed as the source auxiliary integral. -/
theorem waterCube_sourceBulkB_subcritical_exponential {d : ℕ} (i : Fin d)
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
      (∫ ω, sourceMaskedQuenchedB U i (bulkBondMask U i H δ) ω
        ∂bulkPercolation U i H δ p q) ≤
          C/H^2*Real.exp (-H*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))/C) := by
  obtain ⟨C, ε, hC, hε, h⟩ := waterCube_annealedBulkB_subcritical_exponential
    i hB hb hCo hpc hpc1 pioneers ordinary δ hδ hδ1
  refine ⟨C, ε, hC, hε, ?_⟩
  intro r R p q
  dsimp only
  intro hqp hq hp
  rw [← annealedBulkB_eq_sourceIntegral]
  exact h r R p q hqp hq hp

end NearCritical
