module

public import NearCritical.Section10ConditionalFlow
public import NearCritical.Section10OverlapEnergy

/-! Section10 prop.nw.main: pair energy of conditional surviving-chain averages.
Path bounds are required only for nonzero contributions, allowing dead chains. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open scoped Classical BigOperators
variable {E I R C : Type*} [Fintype E] [Fintype I] [Fintype R] [Fintype C]

/-- Dead-chain values disappear from the exact pair expansion. -/
theorem weighted_path_energy_le_overlaps_of_nonzero (a : E → ℝ) (w : I → ℝ)
    (θ : I → E → ℝ) (P : I → Finset E) (hw : ∀ i, 0 ≤ w i)
    (hθ : ∀ i, w i ≠ 0 → ∀ e, |θ i e| ≤ if e ∈ P i then (1:ℝ) else 0)
    (hopen : ∀ i, w i ≠ 0 → ∀ e ∈ P i, a e = 1) :
    flowEnergy a (weightedFlow w θ) ≤
      ∑ i, ∑ j, w i*w j*((P i ∩ P j).card:ℝ) := by
  rw [flowEnergy_weighted_pairs]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hi : w i = 0
  · simp [hi]
  by_cases hj : w j = 0
  · simp [hj]
  exact mul_le_mul_of_nonneg_left
    (path_current_pair_energy_le_overlap a (θ i) (θ j) (P i) (P j)
      (hθ i hi) (hθ j hj) (hopen i hi)) (mul_nonneg (hw i) (hw j))

/-- Source factor four, without imposing a path-current bound on dead chains. -/
theorem normalized_path_energy_le_four_overlaps_of_nonzero (a : E → ℝ) (w : I → ℝ)
    (θ : I → E → ℝ) (P : I → Finset E) (hw : ∀ i, 0 ≤ w i)
    (hW : (1/2:ℝ) ≤ ∑ i, w i)
    (hθ : ∀ i, w i ≠ 0 → ∀ e, |θ i e| ≤ if e ∈ P i then (1:ℝ) else 0)
    (hopen : ∀ i, w i ≠ 0 → ∀ e ∈ P i, a e = 1) :
    flowEnergy a (normalizedFlow w θ) ≤
      4*(∑ i, ∑ j, w i*w j*((P i ∩ P j).card:ℝ)) := by
  let W := ∑ i, w i
  have hWp : 0 < W := by dsimp [W]; linarith
  have hn (i : I) (hi : w i/W ≠ 0) : w i ≠ 0 := by
    intro hz
    exact hi (by rw [hz,zero_div])
  have hb := weighted_path_energy_le_overlaps_of_nonzero a (fun i => w i/W) θ P
    (fun i => div_nonneg (hw i) hWp.le)
    (fun i hi => hθ i (hn i hi)) (fun i hi => hopen i (hn i hi))
  change flowEnergy a (normalizedFlow w θ) ≤ _ at hb
  have hWs : 0 < W^2 := by positivity
  have hinv : 1/W^2 ≤ (4:ℝ) := by
    apply (div_le_iff₀ hWs).mpr
    dsimp [W]
    nlinarith [sq_nonneg ((∑ i, w i)-(1/2:ℝ))]
  refine hb.trans ?_
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hp : 0 ≤ w i*w j*((P i ∩ P j).card:ℝ) :=
    mul_nonneg (mul_nonneg (hw i) (hw j)) (Nat.cast_nonneg _)
  calc
    _ = (1/W^2)*(w i*w j*((P i ∩ P j).card:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hinv hp

/-- Finite conditional chain-choice form of the source pair-overlap energy
bound. Product choice weights represent two independent choices given the
configuration; identification with the source chain law remains separate. -/
theorem normalized_conditional_energy_le_overlaps (a : E → ℝ)
    (μ ω : R → ℝ) (κ ζ : R → C → ℝ) (θ : R → C → E → ℝ)
    (P : R → C → Finset E)
    (hμ : ∀ r, 0 ≤ μ r) (hω : ∀ r, 0 ≤ ω r)
    (hκ : ∀ r c, 0 ≤ κ r c) (hζ : ∀ r c, 0 ≤ ζ r c)
    (hW : (1/2:ℝ) ≤ conditionalChainMass μ ω κ ζ)
    (hθ : ∀ r c, ζ r c ≠ 0 → ∀ e, |θ r c e| ≤ if e ∈ P r c then (1:ℝ) else 0)
    (hopen : ∀ r c, ζ r c ≠ 0 → ∀ e ∈ P r c, a e = 1) :
    flowEnergy a
      (normalizedFlow (conditionalChainWeight μ ω κ ζ) (fun i => θ i.1 i.2)) ≤
      4*(∑ i : R × C, ∑ j : R × C,
        μ i.1*ω i.1*μ j.1*ω j.1*
        (κ i.1 i.2*κ j.1 j.2*ζ i.1 i.2*ζ j.1 j.2)*
        ((P i.1 i.2 ∩ P j.1 j.2).card:ℝ)) := by
  have hw (i : R × C) : 0 ≤ conditionalChainWeight μ ω κ ζ i :=
    mul_nonneg (mul_nonneg (hμ i.1) (hω i.1)) (mul_nonneg (hκ i.1 i.2) (hζ i.1 i.2))
  have hs (i : R × C) (hi : conditionalChainWeight μ ω κ ζ i ≠ 0) : ζ i.1 i.2 ≠ 0 := by
    intro hz
    exact hi (by simp [conditionalChainWeight,hz])
  have hb := normalized_path_energy_le_four_overlaps_of_nonzero a
    (conditionalChainWeight μ ω κ ζ) (fun i => θ i.1 i.2) (fun i => P i.1 i.2) hw
    (by rwa [conditionalChainWeight_sum])
    (fun i hi => hθ i.1 i.2 (hs i hi)) (fun i hi => hopen i.1 i.2 (hs i hi))
  refine hb.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [conditionalChainWeight]
  ring

end NearCritical.Network
