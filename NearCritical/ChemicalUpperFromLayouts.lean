module

public import NearCritical.ChemicalUpperFromNestRules
public import NearCritical.Section10LatticeCertificate

/-! Source `prop.chem.upper` from lattice layouts.

`chemical_timeConstant_upper_of_layouts`: the time constant is at most
`2 (4 (A_sp + A_sk) n0 + 1) l_*` provided that for all large `M` there is a
`NestLayout` (cubes, half tubes, regions) such that

* PROBABILITY (the two paper-internal inputs, not proved):
  `hs`: every step of the lattice nest rule has conditional success probability
  at least `1/rho` (`prop.proba.k-nest`; trivially true outside the context of a
  `k`-nest of typical clusters), and `hsite`: `P[pre-good] >= 1/kappa`
  (`prop.proba.pregood`);
* GEOMETRY (deterministic facts about the layout, not yet proved for the actual
  tubes): route sites lie in the box, tubes lie in the support and avoid the
  far cube, the source half face lies in the left tube, bottom and exit faces
  match the box;
* PARAMETERS: `k <= c l0^(d-6)`, and the length scales `A_sp l0^2`, `A_sk l0^2`
  are those of the layout.

Everything else (route law and exponential intersection tails, mean and second
moment of the weight, Paley--Zygmund, extraction of the path) is proved. `hGM`
is the cited lower tail used by the time-constant assembly.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter
open NearCritical.Section10

theorem chemical_timeConstant_upper_of_layouts {d : ℕ} (hd : 3 ≤ d - 1) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧
    ∀ (pc q : unitInterval) (i : Fin d) (N : Seminorm ℝ (Fin d → ℝ))
      (_hunit : ∀ j, N (Pi.single j 1) = 1)
      (_hreflect : ∀ j x, N (coordinateReflection j x) = N x)
      {μ Asp Ask : ℝ} (_hμ : 0 ≤ μ) (_hAsp : 0 ≤ Asp) (_hAsk : 0 ≤ Ask)
      {ϱ κ : ℝ} (_hϱ : 1 ≤ ϱ) (_hκ : 1 ≤ κ) (_hΛq : (ϱ * κ) ^ 2 * q0 < 1)
      {ell0 n0 ellStar : ℕ} (_hscale : ell0 = n0 * ellStar) (_hstar : 1 ≤ ellStar)
      (a : ℕ → Vertex d) (r s : ℕ → ℕ) (_hr : Tendsto r atTop atTop)
      (_hs : ∀ M, 1 ≤ s M) (_hside : ∀ M, (M - 1) * ell0 + s M = 2 * r M + 1)
      (_hlayout : ∀ᶠ M in atTop, ∃ Λ : NestLayout (d - 1) d,
        Λ.i₀ = i ∧ Λ.top = M - 1 ∧
        2 * (Λ.typ.diameterUpper * (2 * (Λ.t : ℝ)) ^ 2) = Asp * (ell0 : ℝ) ^ 2 ∧
        (Λ.Kdiam : ℝ) = Ask * (ell0 : ℝ) ^ 2 ∧
        (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6) ∧
        (∀ (γ : SourceRoute (d - 1) M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ϱ⁻¹ ≤
          localSuccessProbability pc q (Λ.Bl₀ G.1 (routeLab M γ.position t))
            (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
              (Λ.view G.1 (routeLab M γ.position t) z)))) ∧
        (∀ st, κ⁻¹ ≤ coupledProb pc q (Λ.siteEvent st)) ∧
        (∀ γ : SourceRoute (d - 1) M, lazyRouteSurvives γ.1.1 γ.2 →
          ∀ t, t < 2 * M → (routeLab M γ.position t).site ∈ Λ.siteBox) ∧
        (∀ st ∈ Λ.siteBox, (Λ.Q st : Set (Vertex d)) ⊆
          (translateSites (a M) (chemicalCrossingSupport d (r M) Λ.i₀) : Set (Vertex d))) ∧
        (∀ γ : SourceRoute (d - 1) M, lazyRouteSurvives γ.1.1 γ.2 → ∀ t, t < 2 * M →
          ∀ ℓ : RouteLabel (d - 1), ℓ = routeLab M γ.position t → ℓ.isStep →
          ℓ.target ≠ ℓ.site →
          (Λ.L ℓ : Set (Vertex d)) ⊆
            (translateSites (a M) (chemicalCrossingSupport d (r M) Λ.i₀) : Set (Vertex d)) ∧
          (Λ.R ℓ : Set (Vertex d)) ⊆
            (translateSites (a M) (chemicalCrossingSupport d (r M) Λ.i₀) : Set (Vertex d)) ∧
          Disjoint (Λ.L ℓ : Set (Vertex d))
            (typicalCube Λ.t (Λ.center ℓ.target) : Set (Vertex d)) ∧
          Disjoint (Λ.R ℓ : Set (Vertex d))
            (typicalCube Λ.t (Λ.center ℓ.site) : Set (Vertex d)) ∧
          ∀ pl : Bool, typicalSplitFace Λ.t (Λ.center ℓ.site) (Λ.dir ℓ, true) pl ⊆ Λ.L ℓ) ∧
        (∀ st ∈ Λ.siteBox, st.1 = 0 →
          ∀ pt ∈ typicalFace Λ.t (Λ.center st) (Λ.i₀, false),
            ∃ x ∈ chemicalBottomFace d (r M) Λ.i₀, pt = a M + x) ∧
        (∀ st ∈ Λ.siteBox, st.1 = M - 1 →
          ∀ y ∈ typicalFace Λ.t (Λ.center st) (Λ.i₀, true),
            ∃ z' ∈ chemicalExitFace d (r M) Λ.i₀, bondTip (y, Λ.i₀) = a M + z'))
      (_hGM : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ,
        UniformChemicalLowerTail d (orParameter pc q) N μ ε B R),
      μ ≤ 2 * ((4 * (Asp + Ask) * (n0 : ℝ) + 1) * (ellStar : ℝ)) := by
  obtain ⟨q0, hq0, hq1, hmain⟩ := chemical_timeConstant_upper_of_nestRules hd
  refine ⟨q0, hq0, hq1, ?_⟩
  intro pc q i N hunit hreflect μ Asp Ask hμ hAsp hAsk ϱ κ hϱ hκ hΛq ell0 n0 ellStar hscale
    hstar a r s hr hs hside hlayout hGM
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  refine hmain pc q i N hunit hreflect hμ hAsp hAsk hϱ hκ hΛq hscale hstar a r s hr hs hside
    ?_ hGM
  filter_upwards [hlayout, eventually_ge_atTop 1] with M hM hM1
  obtain ⟨Λ, hi, htopeq, hA, hB, hcount, hsucc, hsite, hbox, hQD, hgeo, hbot, htop⟩ := hM
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ
  refine ⟨Λ.X, Σ F : Λ.Φ₀, (Λ.S₀ F → Bool), inferInstance, inferInstance,
    (Λ.rule M pc q ϱ κ hκ0 hsucc hsite).toNestRule, ?_⟩
  intro z γ hroute hw hsurv
  have h := Λ.certificate M hM1 pc q ϱ κ hκ0 hsucc hsite z γ hw hsurv (a M) (r M) htopeq
    (hbox γ hroute) hcount hQD (hgeo γ hroute) hbot htop
  rw [hA, hB, hi] at h
  exact h

end NearCritical
