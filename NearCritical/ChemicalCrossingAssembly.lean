module

public import NearCritical.ChemicalCrossingLength
public import NearCritical.ChemicalUpperReduction

/-! Conditional assembly of source lem.chem.crossing into prop.chem.upper.

`chemicalChainCertificateEvent` is the ACTUAL configuration event that the confined source box
contains a microscopic chain (`MicroscopicChainGeometry`, the deterministic lem.nw.path data)
from the bottom face, with an actual open terminal exit edge to the exit face and at most
`2M` pieces. We prove it is contained in the actual source crossing event (reusing the frozen
`microscopicChain_crossing_with_source_length`, which keeps and absorbs the terminal `+1`),
transfer probability lower bounds, and feed them into `chemical_timeConstant_upper_of_crossings`.

STATUS: conditional adapter. The probability input is a hypothesis
`c_A ≤ P[S_M]` for an arbitrary event family `S_M ⊆ chemicalChainCertificateEvent`. The source
obtains it from prop.nw.main: `S_M = A_L = {W ≥ 1/2}`, with surviving-chain extraction
supplying the certificate. That actual survival binding (canonical `W`, its `hmean/hpair`
under the Bernoulli law, and `W ≥ 1/2 ⇒` chain certificate) is NOT proved here and remains
open. prop.chem.upper therefore remains open. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter

/-- Actual chain-certified confined crossing: some bottom-face point `a+x` starts a microscopic
chain with intrinsic piece/bridge bounds `A, B` and `n+1 ≤ 2M` pieces, inside the open
configuration restricted to the translated source crossing support, ending at `y`, which has an
actual open edge to an exit-face point `a+z`. -/
def chemicalChainCertificateEvent {d : ℕ} (a : Vertex d) (r : ℕ) (i : Fin d) (A B : ℝ)
    (M : ℕ) : Set (Configuration d) :=
  {ω | ∃ x ∈ chemicalBottomFace d r i, ∃ z ∈ chemicalExitFace d r i, ∃ y : Vertex d,
    ∃ n : ℕ, n + 1 ≤ 2 * M ∧
      MicroscopicChainGeometry
        (restrictedGraph ω (translateSites a (chemicalCrossingSupport d r i) : Set (Vertex d)))
        A B n (a + x) y ∧
      (restrictedGraph ω (translateSites a (chemicalCrossingSupport d r i) :
        Set (Vertex d))).Adj y (a + z)}

/-- Chain certificates at the source scales give actual confined short crossings with
`K = (4(A_sp+A_sk)n₀+1)ℓ_*`. Deterministic. -/
theorem chemicalChainCertificate_subset_crossing {d R : ℕ} (a : Vertex d) (i : Fin d)
    {Asp Ask : ℝ} {M ell0 s n0 ellStar : ℕ} (hAsp : 0 ≤ Asp) (hAsk : 0 ≤ Ask)
    (hM : 2 ≤ M) (hscale : ell0 = n0 * ellStar) (hstar : 1 ≤ ellStar) (hs : 1 ≤ s)
    (hside : (M - 1) * ell0 + s = 2 * R + 1) :
    chemicalChainCertificateEvent a R i (Asp * (ell0 : ℝ) ^ 2) (Ask * (ell0 : ℝ) ^ 2) M ⊆
      chemicalBoxCrossingEvent a R i ((4 * (Asp + Ask) * (n0 : ℝ) + 1) * (ellStar : ℝ)) := by
  rintro ω ⟨x, hx, z, hz, y, n, hn, hchain, hexit⟩
  exact microscopicChain_crossing_with_source_length a i hAsp hAsk hx hz hchain hexit hn hM
    hscale hstar hs hside

/-- Probability transfer: any event contained in the chain-certificate event bounds the actual
source crossing probability from below. -/
theorem chemicalBoxCrossing_probability_ge_of_certificates {d R : ℕ} (p : unitInterval)
    (a : Vertex d) (i : Fin d) {Asp Ask c : ℝ} {M ell0 s n0 ellStar : ℕ}
    (hAsp : 0 ≤ Asp) (hAsk : 0 ≤ Ask) (hM : 2 ≤ M) (hscale : ell0 = n0 * ellStar)
    (hstar : 1 ≤ ellStar) (hs : 1 ≤ s) (hside : (M - 1) * ell0 + s = 2 * R + 1)
    {S : Set (Configuration d)}
    (hS : S ⊆ chemicalChainCertificateEvent a R i (Asp * (ell0 : ℝ) ^ 2)
      (Ask * (ell0 : ℝ) ^ 2) M)
    (hprob : c ≤ (percolation d p).real S) :
    c ≤ (percolation d p).real
      (chemicalBoxCrossingEvent a R i ((4 * (Asp + Ask) * (n0 : ℝ) + 1) * (ellStar : ℝ))) :=
  hprob.trans (measureReal_mono (μ := percolation d p)
    (hS.trans (chemicalChainCertificate_subset_crossing a i hAsp hAsk hM hscale hstar hs hside)))

/-- Conditional source prop.chem.upper: if, along the source scales `L(M) = (M-1)ℓ₀+s_M`,
events `S_M` of probability `≥ c_A` certify actual microscopic chains, then
`μ ≤ 2(4(A_sp+A_sk)n₀+1)ℓ_*`. The certificate probability (source: `A_L` from prop.nw.main
plus surviving-chain extraction) is retained as the explicit input `hprob`/`hS`; the GM lower
tail `hGM` is the named literature input already used by `chemical_timeConstant_upper_of_crossings`. -/
theorem chemical_timeConstant_upper_of_chain_certificates {d : ℕ} (p : unitInterval)
    (i : Fin d) (N : Seminorm ℝ (Fin d → ℝ))
    (hunit : ∀ j, N (Pi.single j 1) = 1)
    (hreflect : ∀ j x, N (coordinateReflection j x) = N x)
    {μ Asp Ask cA : ℝ} (hμ : 0 ≤ μ) (hAsp : 0 ≤ Asp) (hAsk : 0 ≤ Ask) (hcA : 0 < cA)
    {ell0 n0 ellStar : ℕ} (hscale : ell0 = n0 * ellStar) (hstar : 1 ≤ ellStar)
    (a : ℕ → Vertex d) (r s : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (hs : ∀ M, 1 ≤ s M) (hside : ∀ M, (M - 1) * ell0 + s M = 2 * r M + 1)
    (S : ℕ → Set (Configuration d))
    (hS : ∀ M, S M ⊆ chemicalChainCertificateEvent (a M) (r M) i (Asp * (ell0 : ℝ) ^ 2)
      (Ask * (ell0 : ℝ) ^ 2) M)
    (hprob : ∀ᶠ M in atTop, cA ≤ (percolation d p).real (S M))
    (hGM : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ,
      UniformChemicalLowerTail d p N μ ε B R) :
    μ ≤ 2 * ((4 * (Asp + Ask) * (n0 : ℝ) + 1) * (ellStar : ℝ)) := by
  have hK : 0 ≤ (4 * (Asp + Ask) * (n0 : ℝ) + 1) * (ellStar : ℝ) :=
    mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hAsp hAsk))
      (Nat.cast_nonneg _)) zero_le_one) (Nat.cast_nonneg _)
  have hscales : Tendsto (fun M => 2 * r M + 1) atTop atTop :=
    tendsto_atTop_mono (fun M => by omega) hr
  refine chemical_timeConstant_upper_of_crossings p i N hunit hreflect hμ hK hcA
    (fun M => 2 * r M + 1) hscales ?_ hGM
  filter_upwards [hprob, hr.eventually_ge_atTop 1, eventually_ge_atTop 2] with M hM hr1 hM2
  exact (chemicalBoxCrossing_probability_ge_of_certificates p (a M) i hAsp hAsk hM2 hscale
    hstar (hs M) (hside M) (hS M) hM).trans
    (chemicalBoxCrossing_probability_le_span p (a M) i _ hr1)

end NearCritical
