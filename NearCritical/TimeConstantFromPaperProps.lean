import NearCritical.ChemicalUpperReduced
import NearCritical.ChemicalTimeConstant
import NearCritical.ExternalUniquenessActual
import NearCritical.ExternalCriticalPointPos

/-!
`thm.time_constant` in dimension `d = D + 1 >= 9` (the source's range), with every Section 10
ingredient of the upper bound proved and the paper-internal inputs in paper
form.

`time_constant_sandwich_of_paper_props`:
`c / sqrt(p - p_c) <= mu(p) <= C / sqrt(p - p_c)` for all `p > p_c`, given

CITED inputs: the subcritical ray decay `hHMS`, the chemical limit `hlimit`
(which ties `mu` to the actual model), the norm normalisations and the lower
tail `hGM`.

PAPER-INTERNAL inputs (`hpaper`), for every `p` in `(p_c, p₁]`, with constants
`A_sp, A_sk, n0, rho, kappa` not depending on `p`: a sprinkle parameter `q` with
`p = p_c + (1 - p_c) q`, a mesh `l0 = 2t = n0 l_*(p)` with `t >= 9`, typicality
parameters, such that
* `prop.proba.k-nest` holds for the actual layout (moving steps succeed with
  conditional probability at least `1/rho`),
* `prop.proba.pregood` holds (`P_{p_c}[pre-good] >= 1/kappa`),
* the parameter relations hold (`k <= c l0^(d-6)`, length scales, exit bound).

PROVED and no longer assumed: `0 < p_c`, uniqueness of the infinite cluster, the
route law and its exponential intersection tails, the first and second moment
of the weight, Paley--Zygmund, the path extraction `lem.nw.path`, and all the
geometry of cubes and tubes.
-/

namespace NearCritical
open Set MeasureTheory Filter
open NearCritical.Section10
open scoped Classical

theorem time_constant_sandwich_of_paper_props {D : ℕ} (hD : 8 ≤ D) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧
    ∀ {cH CH : ℝ} (_hcH : 0 < cH)
      (_hHMS : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) ≤ (criticalPoint (D + 1) : ℝ) →
        RayExponentialConnectionBound (D + 1) q (Pi.single 0 1) CH
          (cH * Real.sqrt ((criticalPoint (D + 1) : ℝ) - (q : ℝ))))
      (M : unitInterval → ℝ) (N : unitInterval → Seminorm ℝ (Fin (D + 1) → ℝ))
      (_hlimit : ∀ p : unitInterval, criticalPoint (D + 1) < p →
        AEConnectedChemicalLimit (D + 1) p (Pi.single 0 1) (M p))
      (p₁ : unitInterval) (_h₁ : criticalPoint (D + 1) < p₁)
      (_hunit : ∀ p : unitInterval, criticalPoint (D + 1) < p →
        ∀ j, (N p) (Pi.single j 1) = 1)
      (_hreflect : ∀ p : unitInterval, criticalPoint (D + 1) < p → ∀ j x,
        (N p) (coordinateReflection j x) = (N p) x)
      (_hGM : ∀ p : unitInterval, criticalPoint (D + 1) < p → ∀ ε : ℝ, ε ∈ Ioo 0 1 →
        ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail (D + 1) p (N p) (M p) ε B R)
      {Asp Ask ϱ κ : ℝ} (_hAsp : 0 ≤ Asp) (_hAsk : 0 ≤ Ask) (_hϱ : 1 ≤ ϱ) (_hκ : 1 ≤ κ)
      (_hΛq : (ϱ * κ) ^ 2 * q0 < 1) (n0 : ℕ)
      (_hpaper : ∀ p : unitInterval, criticalPoint (D + 1) < p → p ≤ p₁ →
        ∃ (q : unitInterval) (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ)
          (hk : 0 < k) (MOff Mcoal Kdiam : ℕ),
          orParameter (criticalPoint (D + 1)) q = p ∧
          2 * t = n0 * chemicalCorrelationScale (D + 1) p ∧
          1 ≤ chemicalCorrelationScale (D + 1) p ∧
          2 * (typ.diameterUpper * (2 * (t : ℝ)) ^ 2) = Asp * ((2 * t : ℕ) : ℝ) ^ 2 ∧
          (Kdiam : ℝ) = Ask * ((2 * t : ℕ) : ℝ) ^ 2 ∧
          2 ≤ k ∧
          2 * (k : ℝ) ^ 4 ≤ typ.countLower * (2 * (t : ℝ)) ^ (D + 1 - 6) ∧
          (∀ m : ℕ, typ.boundaryLower * (2 * (t : ℝ)) ^ 2 ≤ (m : ℝ) →
            ((1 - (criticalPoint (D + 1) : ℝ)) * (1 - (q:ℝ))) ^ m ≤ 1 - ϱ⁻¹) ∧
          (∀ᶠ Mb in atTop, ∀ (γ : SourceRoute D Mb)
            (G : (actualLayout D typ t ht k hk MOff Mcoal Kdiam Mb).Φ) (t' : ℕ)
            (x : (actualLayout D typ t ht k hk MOff Mcoal Kdiam Mb).X),
            (actualLayout D typ t ht k hk MOff Mcoal Kdiam Mb).moveCtx G
              (routeLab Mb γ.position t') x → ϱ⁻¹ ≤
            localSuccessProbability (criticalPoint (D + 1)) q
              ((actualLayout D typ t ht k hk MOff Mcoal Kdiam Mb).Bl₀ G.1
                (routeLab Mb γ.position t'))
              (bitSet G.2 (fun z =>
                (actualLayout D typ t ht k hk MOff Mcoal Kdiam Mb).moveTypical G
                  (routeLab Mb γ.position t') x
                  ((actualLayout D typ t ht k hk MOff Mcoal Kdiam Mb).view G.1
                    (routeLab Mb γ.position t') z)))) ∧
          (∀ a : Vertex (D + 1), κ⁻¹ ≤
            ∫ ω, (if IsPreGoodCube typ t (coarseCenter t a) ω then (1:ℝ) else 0)
              ∂(percolation (D + 1) (criticalPoint (D + 1))))),
      ∃ cl Cu : ℝ, 0 < cl ∧ 0 < Cu ∧ ∀ p : unitInterval, criticalPoint (D + 1) < p →
        cl / Real.sqrt ((p : ℝ) - (criticalPoint (D + 1) : ℝ)) ≤ M p ∧
          M p ≤ Cu / Real.sqrt ((p : ℝ) - (criticalPoint (D + 1) : ℝ)) := by
  obtain ⟨q0, hq0, hq1, hmain⟩ := chemical_timeConstant_upper_reduced (by omega : 3 ≤ D)
  refine ⟨q0, hq0, hq1, ?_⟩
  intro cH CH hcH hHMS M N hlimit p₁ h₁ hunit hreflect hGM Asp Ask ϱ κ hAsp hAsk hϱ hκ hΛq n0
    hpaper
  have hpc : 0 < (criticalPoint (D + 1) : ℝ) :=
    External.criticalPoint_pos (Nat.succ_pos D)
  have huniq : ∀ p : unitInterval, AEInfiniteClusterUniqueness (D + 1) p :=
    fun p => External.aeInfiniteClusterUniqueness (D + 1) p
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = 4 * (Asp + Ask) * (n0 : ℝ) + 1 := ⟨_, rfl⟩
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀]
    have : 0 ≤ 4 * (Asp + Ask) * (n0 : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hAsp hAsk)) (Nat.cast_nonneg _)
    linarith
  have hKpos : 0 < max (2 * C₀) (|M p₁| + 1) :=
    lt_of_lt_of_le (by positivity : 0 < |M p₁| + 1) (le_max_right _ _)
  refine ⟨min (Real.sqrt ((criticalPoint (D + 1) : ℝ) / 2))
      (cH * (criticalPoint (D + 1) : ℝ) / 8), max (2 * C₀) (|M p₁| + 1),
    chemical_lower_constant_pos hpc hcH, hKpos, fun p hp => ⟨?_, ?_⟩⟩
  · exact chemical_timeConstant_lower_uniform (0 : Fin (D + 1)) hpc hcH hHMS p hp (huniq p)
      (hlimit p hp)
  · have hδ : 0 < (p : ℝ) - (criticalPoint (D + 1) : ℝ) := sub_pos.mpr hp
    have hsqrt : 0 < Real.sqrt ((p : ℝ) - (criticalPoint (D + 1) : ℝ)) := Real.sqrt_pos.mpr hδ
    by_cases hpp₁ : p ≤ p₁
    · by_cases hμ : 0 ≤ M p
      · obtain ⟨q, typ, t, ht, k, hk, MOff, Mcoal, Kdiam, hpq, hscale, hstar, hA, hB, hk2, hcount,
          hexitParam, hmove, hpre⟩ := hpaper p hp hpp₁
        have hGM' : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ,
            UniformChemicalLowerTail (D + 1) (orParameter (criticalPoint (D + 1)) q) (N p)
              (M p) ε B R := by
          intro ε h0 h1
          rw [hpq]
          exact hGM p hp ε ⟨h0, h1⟩
        have hup := hmain (criticalPoint (D + 1)) q (N p) (hunit p hp) (hreflect p hp) hμ hAsp
          hAsk hϱ hκ hΛq typ t ht k hk MOff Mcoal Kdiam hscale hstar hA hB hk2 hcount hexitParam
          hmove hpre hGM'
        rw [← hC₀] at hup
        have hscale_le := chemicalCorrelationScale_le (D + 1) p
        calc M p ≤ 2 * (C₀ * (chemicalCorrelationScale (D + 1) p : ℝ)) := hup
          _ ≤ 2 * (C₀ * (Real.sqrt ((p : ℝ) - (criticalPoint (D + 1) : ℝ)))⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscale_le hC₀nn)
              (by norm_num)
          _ = (2 * C₀) / Real.sqrt ((p : ℝ) - (criticalPoint (D + 1) : ℝ)) := by
            rw [div_eq_mul_inv]
            ring
          _ ≤ max (2 * C₀) (|M p₁| + 1) /
              Real.sqrt ((p : ℝ) - (criticalPoint (D + 1) : ℝ)) :=
            div_le_div_of_nonneg_right (le_max_left _ _) hsqrt.le
      · exact (le_of_not_ge hμ).trans (div_nonneg hKpos.le hsqrt.le)
    · have hmac := chemical_timeConstant_upper_macroscopic p₁ p h₁ (le_of_not_ge hpp₁)
        (Pi.single 0 1) (huniq p₁) (hlimit p₁ h₁) (hlimit p hp)
      exact hmac.trans (div_le_div_of_nonneg_right (le_max_right _ _) hsqrt.le)

end NearCritical
