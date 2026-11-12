module

public import NearCritical.Section10StepHypotheses

/-! The numeric size conditions of the Section 9 theorem for a lattice step,
from typicality and pre-goodness.

`NestLayout.step_sizes`: for a nest of `k` typical clusters in the site cube
and a pre-good target cube, in dimension `d >= 6` and `t >= 1`, if

  `4 k C_b <= KA`, `8 C_b <= CB`,
  `cSize <= 4 k c_b`, `cSize <= 4 c c_b (2t)^(d-6)`, `cSize <= 16 k c c_b^2`

then `|A| <= KA t^2`, `|tgt c| <= CB t^2`, `cSize t^2 <= |A|`,
`cSize t^2 <= |B|` and `cSize t^(d-2) <= |A||B|`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

variable {D d : ℕ} (Λ : NestLayout D d)

theorem NestLayout.tgt_card_le (G : Λ.Φ) (ℓ : RouteLabel D) {C : Finset (Vertex d)}
    (hC : C ∈ Λ.fam G ℓ.target) :
    ((Λ.tgt G ℓ C).card : ℝ) ≤ 2 * (Λ.typ.boundaryUpper * (2 * (Λ.t : ℝ)) ^ 2) := by
  have htyp := ((mem_typicalClusterFamily _ _ _ _ C).mp hC).2
  have ha := (htyp.2.2.2.2.2.1 (Λ.dir ℓ, false) true).2
  have hb := (htyp.2.2.2.2.2.1 (Λ.dir ℓ, false) false).2
  have hu : (Λ.tgt G ℓ C).card ≤
      (typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.target) (Λ.revealConfig G) C
        (Λ.dir ℓ, false) true).card +
      (typicalRegularPatch Λ.typ Λ.t (Λ.center ℓ.target) (Λ.revealConfig G) C
        (Λ.dir ℓ, false) false).card := Finset.card_union_le _ _
  have hu' := (Nat.cast_le (α := ℝ)).mpr hu
  push_cast at hu'
  linarith

theorem NestLayout.step_sizes (hd6 : 6 ≤ d) (ht1 : 1 ≤ Λ.t) (G : Λ.Φ) (ℓ : RouteLabel D)
    (pl : Bool) (nest : Finset (Finset (Vertex d))) (hnest : nest ⊆ Λ.fam G ℓ.site)
    (hgood : Λ.goodCube G ℓ.target)
    (hbL : 0 ≤ Λ.typ.boundaryLower) (hcL : 0 ≤ Λ.typ.countLower)
    {KA CB cSize : ℝ}
    (hKA : 4 * (nest.card : ℝ) * Λ.typ.boundaryUpper ≤ KA)
    (hCB : 8 * Λ.typ.boundaryUpper ≤ CB)
    (hc1 : cSize ≤ 4 * (nest.card : ℝ) * Λ.typ.boundaryLower)
    (hc2 : cSize ≤ 4 * Λ.typ.countLower * Λ.typ.boundaryLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (hc3 : cSize ≤ 16 * (nest.card : ℝ) * Λ.typ.countLower * Λ.typ.boundaryLower ^ 2) :
    ((sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card : ℝ) ≤ KA * (Λ.t : ℝ) ^ 2 ∧
    (∀ c ∈ Λ.fam G ℓ.target, ((Λ.tgt G ℓ c).card : ℝ) ≤ CB * (Λ.t : ℝ) ^ 2) ∧
    cSize * (Λ.t : ℝ) ^ 2 ≤ ((sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card : ℝ) ∧
    cSize * (Λ.t : ℝ) ^ 2 ≤
      ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) ∧
    cSize * (Λ.t : ℝ) ^ (((d : ℕ) : ℝ) - 2) ≤
      ((sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card : ℝ) *
      ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) := by
  set T : ℝ := (Λ.t : ℝ) with hT
  have hT1 : (1:ℝ) ≤ T := by
    rw [hT]
    exact_mod_cast ht1
  have hT0 : (0:ℝ) ≤ T := by linarith
  have hTsq : (0:ℝ) ≤ T ^ 2 := sq_nonneg T
  have hk0 : (0:ℝ) ≤ (nest.card : ℝ) := Nat.cast_nonneg _
  have hAle := Λ.srcBoundary_card_le G ℓ pl nest hnest
  have hAge := Λ.srcBoundary_card_ge G ℓ pl nest hnest
  have hBge := Λ.tgtBoundary_card_ge G ℓ hgood hbL
  rw [← hT] at hAle hAge hBge
  have hpow1 : (1:ℝ) ≤ (2 * T) ^ (d - 6) := one_le_pow₀ (by linarith)
  have hpowT : T ^ (d - 6) ≤ (2 * T) ^ (d - 6) := pow_le_pow_left₀ hT0 (by linarith) _
  have hTd0 : (0:ℝ) ≤ T ^ (d - 6) := pow_nonneg hT0 _
  have hA_lo : 4 * (nest.card : ℝ) * Λ.typ.boundaryLower * T ^ 2 ≤
      ((sprinklingTargetBoundary nest (Λ.src G ℓ pl)).card : ℝ) := by
    refine le_trans (le_of_eq ?_) hAge
    ring
  have hB_lo : Λ.typ.countLower * T ^ (d - 6) * (4 * Λ.typ.boundaryLower * T ^ 2) ≤
      ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) := by
    refine le_trans ?_ hBge
    have h4 : 4 * Λ.typ.boundaryLower * T ^ 2 = Λ.typ.boundaryLower * (2 * T) ^ 2 := by ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowT hcL) (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine hAle.trans ?_
    calc (nest.card : ℝ) * (Λ.typ.boundaryUpper * (2 * T) ^ 2)
        = (4 * (nest.card : ℝ) * Λ.typ.boundaryUpper) * T ^ 2 := by ring
      _ ≤ KA * T ^ 2 := mul_le_mul_of_nonneg_right hKA hTsq
  · intro c hc
    have h := Λ.tgt_card_le G ℓ hc
    rw [← hT] at h
    refine h.trans ?_
    calc 2 * (Λ.typ.boundaryUpper * (2 * T) ^ 2) = (8 * Λ.typ.boundaryUpper) * T ^ 2 := by ring
      _ ≤ CB * T ^ 2 := mul_le_mul_of_nonneg_right hCB hTsq
  · exact (mul_le_mul_of_nonneg_right hc1 hTsq).trans hA_lo
  · refine le_trans ?_ hBge
    calc cSize * T ^ 2
        ≤ (4 * Λ.typ.countLower * Λ.typ.boundaryLower * (2 * T) ^ (d - 6)) * T ^ 2 :=
          mul_le_mul_of_nonneg_right hc2 hTsq
      _ = Λ.typ.countLower * (2 * T) ^ (d - 6) * (Λ.typ.boundaryLower * (2 * T) ^ 2) := by ring
  · have hexp : ((d : ℕ) : ℝ) - 2 = ((d - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hexp, Real.rpow_natCast]
    have hdd : d - 2 = (d - 6) + 4 := by omega
    have ha0 : (0:ℝ) ≤ 4 * (nest.card : ℝ) * Λ.typ.boundaryLower * T ^ 2 := by positivity
    have hb0 : (0:ℝ) ≤ Λ.typ.countLower * T ^ (d - 6) * (4 * Λ.typ.boundaryLower * T ^ 2) := by
      positivity
    have hprod := mul_le_mul hA_lo hB_lo hb0 (ha0.trans hA_lo)
    refine le_trans ?_ hprod
    have hid : 4 * (nest.card : ℝ) * Λ.typ.boundaryLower * T ^ 2 *
        (Λ.typ.countLower * T ^ (d - 6) * (4 * Λ.typ.boundaryLower * T ^ 2)) =
        (16 * (nest.card : ℝ) * Λ.typ.countLower * Λ.typ.boundaryLower ^ 2) * T ^ (d - 2) := by
      rw [hdd, pow_add]
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hc3 (pow_nonneg hT0 _)

end NearCritical.Section10
