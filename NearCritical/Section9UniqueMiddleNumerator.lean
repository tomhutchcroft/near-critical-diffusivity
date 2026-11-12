module
public import NearCritical.Section9UniqueMiddleExitMoment
public import NearCritical.Section9FiniteLocalIntegrability
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! Large-scale lower bound for the actual positive-part source numerator. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The actual positive-part numerator has order n². The coefficients c and K
can be supplied by the right-hand avoidance bound; delta is already fixed.
Neither a moment estimate nor a favorable numerator event is assumed. -/
theorem section9_source_unique_middle_numerator_lower {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r →
      ∀ c : ℝ, 0 < c → ∀ K : ℝ, 0 ≤ K →
      ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 16*(r+1) ≤ N ∧
      ∀ (i : Fin d) (n : ℕ), N ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary : Finset (Vertex d)) (x : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      x ∈ section8ExtensionPositiveFaceCore i n →
      sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary r δ x →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let X₁ := fun ω => actualUniqueMiddleCount ω L Q₁ F₁ (F₁ ∩ boundary) x
        (section8ExtensionMiddleCore i n)
      a*(n : ℝ)^2 ≤ ∫ ω, max (c*X₁ ω - K*((n : ℝ)^((4 : ℝ)-(d : ℝ))*X₁ ω*
        ((sprinklingUnexploredCluster ω L Q₁ F₁ x ∩ section9ExitFace i n).card : ℝ))) 0 ∂ν := by
  obtain ⟨δ,hδ,hfirst⟩ := section9_source_unique_middle_first_moment_lower hd asymptotics rectangle
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  obtain ⟨K₂,hK₂,hsecond⟩ := section9_source_unique_middle_exit_moment_upper
    (by omega : 5 ≤ d) hG.le green
  refine ⟨δ,hδ,?_⟩
  intro r hr
  obtain ⟨c₁,hc₁,hlower⟩ := hfirst r hr
  intro c hc K hK
  let a : ℝ := c*c₁/2
  have ha : 0 < a := div_pos (mul_pos hc hc₁) (by norm_num)
  obtain ⟨N₀,hN₀⟩ := exists_nat_ge ((K*K₂)/a)
  let N := max (16*(r+1)) (max 1 N₀)
  refine ⟨a,ha,N,le_max_left _ _,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary x hH₁ hH₃ hpos hx hreg L Q₁ Q₃ ν X₁
  have hnScale : 16*(r+1) ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_trans (le_max_left 1 N₀) (le_max_right _ _)).trans hn
  have hn16 : 16 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hNn : (N₀ : ℝ) ≤ n := by
    exact_mod_cast (show N₀ ≤ n from (le_trans (le_max_right 1 N₀) (le_max_right _ _)).trans hn)
  have herror : K*K₂ ≤ a*(n : ℝ)^2 := by
    have hlin : K*K₂ ≤ (n : ℝ)*a := (div_le_iff₀ ha).mp (hN₀.trans hNn)
    have hsq : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
    exact hlin.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq ha.le)
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let C := fun ω : Configuration d => sprinklingUnexploredCluster ω L Q₁ F₁ x
  let X₂ := fun ω : Configuration d => (n : ℝ)^((4 : ℝ)-(d : ℝ))*X₁ ω*
    ((C ω ∩ section9ExitFace i n).card : ℝ)
  have hi (f : Finset (Vertex d) → ℝ) : Integrable (fun ω => f (C ω)) ν := by
    apply section9_finite_local_integrable ν (sprinklingAvailableBonds L Q₁ F₁)
    intro ω θ hagree
    exact congrArg f (sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ hagree x)
  have hi₁ : Integrable X₁ ν := by
    exact hi (fun S => if S ∩ (F₁ ∩ boundary) = {x} then
      ((S ∩ section8ExtensionMiddleCore i n).card : ℝ) else 0)
  have hi₂ : Integrable X₂ ν := by
    exact hi (fun S => (n : ℝ)^((4 : ℝ)-(d : ℝ))*
      (if S ∩ (F₁ ∩ boundary) = {x} then ((S ∩ section8ExtensionMiddleCore i n).card : ℝ) else 0)*
      ((S ∩ section9ExitFace i n).card : ℝ))
  have hiX : Integrable (fun ω => max (c*X₁ ω-K*X₂ ω) 0) ν := by
    exact hi (fun S => max (c*(if S ∩ (F₁ ∩ boundary) = {x} then
      ((S ∩ section8ExtensionMiddleCore i n).card : ℝ) else 0)-
      K*((n : ℝ)^((4 : ℝ)-(d : ℝ))*
        (if S ∩ (F₁ ∩ boundary) = {x} then ((S ∩ section8ExtensionMiddleCore i n).card : ℝ) else 0)*
        ((S ∩ section9ExitFace i n).card : ℝ))) 0)
  have hfirstActual : c₁*(n : ℝ)^2 ≤ ∫ ω, X₁ ω ∂ν :=
    hlower i n hnScale H₁ H₃ F₁ F₃ boundary x hH₁ hH₃ hpos hx hreg
  have hsecondActual : (∫ ω, X₂ ω ∂ν) ≤ K₂*(n : ℝ)^((9 : ℝ)-(d : ℝ)) :=
    hsecond i n hn16 H₁ H₃ F₁ F₃ (F₁ ∩ boundary) x hH₁ hH₃ hpos hx
  have hpow : (n : ℝ)^((9 : ℝ)-(d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnR (by
      have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
  have hsecondSmall : (∫ ω, X₂ ω ∂ν) ≤ K₂ :=
    hsecondActual.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hK₂)
  have hmono := integral_mono ((hi₁.const_mul c).sub (hi₂.const_mul K)) hiX
    (fun ω => le_max_left (c*X₁ ω-K*X₂ ω) 0)
  change (∫ ω, c*X₁ ω-K*X₂ ω ∂ν) ≤
    ∫ ω, max (c*X₁ ω-K*X₂ ω) 0 ∂ν at hmono
  rw [integral_sub (hi₁.const_mul c) (hi₂.const_mul K),integral_const_mul,integral_const_mul] at hmono
  have hf := mul_le_mul_of_nonneg_left hfirstActual hc.le
  have he := mul_le_mul_of_nonneg_left hsecondSmall hK
  change a*(n : ℝ)^2 ≤ ∫ ω, max (c*X₁ ω-K*X₂ ω) 0 ∂ν
  dsimp only [a] at herror ⊢
  nlinarith only [hf,he,hmono,herror]

end NearCritical
