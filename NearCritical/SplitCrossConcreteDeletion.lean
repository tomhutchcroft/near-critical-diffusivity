module

public import NearCritical.SplitCrossConcreteMoatEstimates

/-! The outward length is chosen first, the star length may then be
increased, and the box scale absorbs all remote moat costs. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode Section8
open scoped Classical

/-- Uniformly over placements and every finite base tube inside its edge
region, the deletion loss is at most half the available base bound. -/
theorem concrete_moat_loss_eventually_small {d : ℕ} (hd : 7 ≤ d) (hd3 : 3 ≤ d)
    {G C : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper d C)
    (a : ℝ) (ha : 0 < a) :
    ∃ ρ : ℕ, 0 < ρ ∧ ∃ R₀ : ℕ, ∀ R ≥ R₀, ∃ t₀ : ℕ, ∀ t ≥ t₀,
      4096 ≤ t ∧ 512 * (4 * d - 1 + 1) * (R + 1 + ρ) ≤ t ∧
      2048 * (R + 1 + ρ) ≤ t ∧
      ((R + 1 + ρ : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ) ∧
      ∀ (x : Vertex d), x ∈ centeredBox d ((t - 1) / 32) →
      ∀ (axis : Fin d) (b : SplitTreeNode (4 * d) → Vertex d), (∀ v, b v ∈ nodeSites t x axis v) →
      ∀ (hL : 2 ≤ 4 * d) (v : SplitTreeNode (4 * d)), v ≠ root →
      ∀ i ∈ branchAxes hd3, ∀ j ∈ branchAxes hd3,
      ∀ T : Finset (Vertex d), T ⊆ crossingEdgeRegion t v →
        crossingTip b v j (R + 1 + ρ) ∈ T →
        moatDeletionLoss (criticalPoint d) T
          (treeMoatVertices (crossingBranches (4 * d)) b (branchAxes hd3) R 1)
          (crossingTip b (parent hL v) i (R + 1 + ρ)) (crossingTip b v j (R + 1 + ρ)) ≤
          (a / 2) * (t : ℝ) ^ crossingEdgeExponent d v := by
  let D : ℕ := 256 * (4 * d - 1 + 1)
  let q : ℝ := 1 / (4 * (D : ℝ))
  let Q : ℝ := 2 * G^2 + (2 * C) * G
  let B : ℝ := Q * max (q ^ ((2 : ℝ) - (d : ℝ))) (q ^ ((1 : ℝ) - (d : ℝ)))
  let ε : ℝ := a / (4 * (B + 1))
  have hD : 0 < D := by dsimp [D]; positivity
  have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hq : 0 < q := by dsimp [q]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hB : 0 ≤ B := mul_nonneg hQ ((Real.rpow_nonneg hq.le _).trans (le_max_left _ _))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : 4 * (B + 1) * ε = a := by
    dsimp [ε]
    field_simp
  obtain ⟨ρ, hρ, R₀, hown⟩ := ownMoat_green_mass_small (by omega : 4 ≤ d) 1 (by decide) ε hε
  refine ⟨ρ, hρ, R₀, ?_⟩
  intro R hR
  let n := R + 1 + ρ
  let M := crossingMoatSize d hd3 R
  have hM : 0 ≤ M := crossingMoatSize_nonneg d hd3 R
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hR' : 0 ≤ ((R + 1 + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨S, hS⟩ := exists_nat_gt (1 + M / ε + (2 * (n : ℝ) + ((R + 1 + 1 : ℕ) : ℝ)))
  let t₀ := max 4096 (max (512 * (4 * d - 1 + 1) * n) (max (2048 * n) (4 * D * S)))
  refine ⟨t₀, ?_⟩
  intro t ht
  have ht4096 : 4096 ≤ t := (le_max_left _ _).trans ht
  have hts : 512 * (4 * d - 1 + 1) * n ≤ t :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans ht
  have htl : 2048 * n ≤ t :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans ht
  have htS : 4 * D * S ≤ t :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans ht
  let s : ℝ := q * (t : ℝ)
  have hsD : 4 * (D : ℝ) * s = (t : ℝ) := by
    dsimp [s, q]
    field_simp
  have hsS : (S : ℝ) ≤ s := by
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 4 * (D : ℝ))).mp
    rw [hsD]
    exact_mod_cast htS
  have hMε : 0 ≤ M / ε := div_nonneg hM hε.le
  have hs : 1 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hrem : M / ε ≤ s^2 := by
    have hle : M / ε ≤ s := by linarith
    have hsq : s ≤ s^2 := by
      nlinarith only [mul_nonneg hspos.le (sub_nonneg.mpr hs)]
    exact hle.trans hsq
  have hremote : M / s^2 ≤ ε := by
    apply (div_le_iff₀ (sq_pos_of_pos hspos)).mpr
    have h' := (div_le_iff₀ hε).mp hrem
    simpa only [mul_comm] using h'
  have hfloorN : t ≤ D * (spineRadius (4 * d - 1) t + 1) := by
    change t ≤ D * (t / D + 1)
    rw [Nat.mul_add, Nat.mul_one]
    have hmod := Nat.mod_lt t hD
    have hdiv := Nat.mod_add_div t D
    omega
  have hfloorR : (t : ℝ) ≤ (D : ℝ) * ((spineRadius (4 * d - 1) t : ℝ) + 1) := by
    exact_mod_cast hfloorN
  have hfloor : 4 * s ≤ (spineRadius (4 * d - 1) t : ℝ) + 1 := by
    apply (mul_le_mul_iff_right₀ hD').mp
    calc
      _ = (t : ℝ) := by linarith only [hsD]
      _ ≤ _ := hfloorR
  have hgap : 2 * s + 2 * (n : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) ≤
      (spineRadius (4 * d - 1) t : ℝ) := by linarith
  have hgap' : (n : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) <
      (spineRadius (4 * d - 1) t : ℝ) := by linarith
  refine ⟨ht4096, hts, htl, hgap', ?_⟩
  intro x hx axis b hb hL v hv i hi j hj T hT hy
  let e := crossingEdgeExponent d v
  have hpow : q ^ e ≤ max (q ^ ((2 : ℝ) - (d : ℝ))) (q ^ ((1 : ℝ) - (d : ℝ))) := by
    cases v with
    | face k => exact le_max_right _ _
    | root | spine _ | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ => exact le_max_left _ _
  have htR : 0 ≤ (t : ℝ) := by positivity
  have hMpos : 0 ≤ ε + M / s^2 := add_nonneg hε.le (div_nonneg hM (sq_nonneg s))
  have hBε : B * (ε + ε) ≤ a / 2 := by nlinarith only [hεeq, hε.le]
  have h := concrete_moat_loss_le hd hd3 ht4096 x hx axis b hb R ρ hs hε.le hgap
    (fun z l hl => hown R hR z (branchAxes hd3) l hl) hG green hC panis hL v hv i j hi hj T hT hy
  change _ ≤ Q * s ^ e * (ε + M / s^2) at h
  refine h.trans ?_
  calc
    Q * s ^ e * (ε + M / s^2) = (Q * q ^ e) * (ε + M / s^2) * (t : ℝ) ^ e := by
      dsimp only [s]
      rw [Real.mul_rpow hq.le htR]
      ring
    _ ≤ B * (ε + M / s^2) * (t : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hQ) hMpos) (Real.rpow_nonneg htR _)
    _ ≤ B * (ε + ε) * (t : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right hremote ε) hB)
        (Real.rpow_nonneg htR _)
    _ ≤ (a / 2) * (t : ℝ) ^ e := mul_le_mul_of_nonneg_right hBε (Real.rpow_nonneg htR _)

end NearCritical.SplitCrossDirect
