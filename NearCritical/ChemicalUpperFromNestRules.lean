module

public import NearCritical.ChemicalCrossingAssembly
public import NearCritical.Section10Survivor

/-! Source `prop.chem.upper` from nest rules.

`chemical_timeConstant_upper_of_chain_certificates` assumed events `S_M` of
probability at least `c_A` inside the chain-certificate event. Here that
probability input is PROVED from the Section 10 weight argument
(`nestRule_crossing_probability`): the supercritical configuration is
`z.1 OR z.2` with `z.1 ~ P_{pc}` and `z.2 ~ P_q`, and `c_A = 1/8`.

Remaining hypothesis `hrule`: for all large `M` there is a `NestRule` (reveal,
step blocks, step rule with `1/rho <= s_t`, site indicators with second moment
at most `kappa`) all of whose survivor configurations carry a microscopic chain
certificate. That is the content of `prop.proba.pregood`, `prop.proba.k-nest`
and `lem.nw.path`. `hGM` is the cited chemical-distance lower tail already used
by the assembly.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter
open NearCritical.Section10

theorem chemical_timeConstant_upper_of_nestRules {d : ℕ} (hd : 3 ≤ d - 1) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧
    ∀ (pc q : unitInterval) (i : Fin d) (N : Seminorm ℝ (Fin d → ℝ))
      (_hunit : ∀ j, N (Pi.single j 1) = 1)
      (_hreflect : ∀ j x, N (coordinateReflection j x) = N x)
      {μ Asp Ask : ℝ} (_hμ : 0 ≤ μ) (_hAsp : 0 ≤ Asp) (_hAsk : 0 ≤ Ask)
      {ϱ κ : ℝ} (_hϱ : 1 ≤ ϱ) (_hκ : 1 ≤ κ) (_hΛq : (ϱ * κ) ^ 2 * q0 < 1)
      {ell0 n0 ellStar : ℕ} (_hscale : ell0 = n0 * ellStar) (_hstar : 1 ≤ ellStar)
      (a : ℕ → Vertex d) (r s : ℕ → ℕ) (_hr : Tendsto r atTop atTop)
      (_hs : ∀ M, 1 ≤ s M) (_hside : ∀ M, (M - 1) * ell0 + s M = 2 * r M + 1)
      (_hrule : ∀ᶠ M in atTop, ∃ (X Φ : Type) (_ : Fintype X) (_ : Fintype Φ)
        (R : NestRule (d - 1) M d pc q ϱ κ X Φ),
        ∀ z γ, lazyRouteSurvives γ.1.1 γ.2 → 0 < R.w γ (R.ρ z) →
          ChainSurvives (R.kernel γ (R.ρ z)) (2 * M) 0 (R.x₀ γ (R.ρ z)) z →
          sprinkleOrConfiguration z.1 z.2 ∈
            chemicalChainCertificateEvent (a M) (r M) i (Asp * (ell0 : ℝ) ^ 2)
              (Ask * (ell0 : ℝ) ^ 2) M)
      (_hGM : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ,
        UniformChemicalLowerTail d (orParameter pc q) N μ ε B R),
      μ ≤ 2 * ((4 * (Asp + Ask) * (n0 : ℝ) + 1) * (ellStar : ℝ)) := by
  obtain ⟨q0, C, M₀, hq0, hq1, hC, hmain⟩ := nestRule_crossing_probability hd
  refine ⟨q0, hq0, hq1, ?_⟩
  intro pc q i N hunit hreflect μ Asp Ask hμ hAsp hAsk ϱ κ hϱ hκ hΛq ell0 n0 ellStar hscale
    hstar a r s hr hs hside hrule hGM
  refine chemical_timeConstant_upper_of_chain_certificates (orParameter pc q) i N hunit
    hreflect hμ hAsp hAsk (by norm_num : (0:ℝ) < 1/8) hscale hstar a r s hr hs hside
    (fun M => chemicalChainCertificateEvent (a M) (r M) i (Asp * (ell0 : ℝ) ^ 2)
      (Ask * (ell0 : ℝ) ^ 2) M) (fun M => le_refl _) ?_ hGM
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C * (ϱ * κ) ^ 2 / (1 - (ϱ * κ) ^ 2 * q0) := ⟨_, rfl⟩
  filter_upwards [hrule, eventually_ge_atTop M₀, eventually_ge_atTop (max 1 ⌈K⌉₊)]
    with M hM hM0 hMK
  obtain ⟨X, Φ, instX, instΦ, R, hpath⟩ := hM
  have hM1 : 1 ≤ M := (le_max_left _ _).trans hMK
  have hMK' : K ≤ (M:ℝ) := (Nat.le_ceil K).trans (by exact_mod_cast (le_max_right _ _).trans hMK)
  have hpow : (M:ℝ) ≤ (M:ℝ) ^ (d - 1 - 1) :=
    le_self_pow₀ (by exact_mod_cast hM1) (by omega)
  exact hmain M hM0 pc q hϱ hκ R hΛq (by rw [← hK]; exact hMK'.trans hpow) _ hpath

end NearCritical
