module

public import NearCritical.Section10Flow

/-! Section10 prop.nw.main: the deterministic overlap-energy estimate.
The stochastic pair-process overlap estimate is a separate NEW obligation. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open scoped Classical BigOperators
variable {E I : Type*} [Fintype E] [Fintype I]

/-- Unit path currents have bilinear energy at most the number of COMMON
physical edges. Opposite traversal signs only decrease the bilinear term. -/
theorem path_current_pair_energy_le_overlap (a : E → ℝ) (θ ψ : E → ℝ)
    (P Q : Finset E)
    (hθ : ∀ e, |θ e| ≤ if e ∈ P then (1:ℝ) else 0)
    (hψ : ∀ e, |ψ e| ≤ if e ∈ Q then (1:ℝ) else 0)
    (hopen : ∀ e ∈ P, a e = 1) :
    (∑ e, θ e*ψ e/a e) ≤ ((P ∩ Q).card:ℝ) := by
  have hp (e : E) : θ e*ψ e/a e ≤ if e ∈ P ∩ Q then (1:ℝ) else 0 := by
    by_cases heP : e ∈ P
    · by_cases heQ : e ∈ Q
      · have ht : |θ e| ≤ 1 := by simpa only [if_pos heP] using hθ e
        have hq : |ψ e| ≤ 1 := by simpa only [if_pos heQ] using hψ e
        have hm : |θ e| * |ψ e| ≤ 1 := by
          simpa only [one_mul] using mul_le_mul ht hq (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        have hb : θ e*ψ e ≤ 1 :=
          (le_abs_self _).trans (by simpa only [abs_mul] using hm)
        simpa [heP,heQ,hopen e heP] using hb
      · have hz : ψ e = 0 := by
          apply abs_eq_zero.mp
          exact le_antisymm (by simpa only [if_neg heQ] using hψ e) (abs_nonneg _)
        simp [hz,heQ]
    · have hz : θ e = 0 := by
        apply abs_eq_zero.mp
        exact le_antisymm (by simpa only [if_neg heP] using hθ e) (abs_nonneg _)
      simp [hz,heP]
  calc
    _ ≤ ∑ e, if e ∈ P ∩ Q then (1:ℝ) else 0 := Finset.sum_le_sum (fun e _ => hp e)
    _ = _ := by
      have hf : (Finset.univ.filter (fun e : E => e ∈ P ∩ Q)) = P ∩ Q := by
        ext e
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rw [Finset.sum_boole,hf]

/-- The exact pair expansion plus current bounds gives the source unnormalized
energy estimate, with all ordered pairs and nonnegative weights retained. -/
theorem weighted_path_flow_energy_le_overlaps (a : E → ℝ) (α : I → ℝ)
    (θ : I → E → ℝ) (P : I → Finset E) (hα : ∀ i, 0 ≤ α i)
    (hθ : ∀ i e, |θ i e| ≤ if e ∈ P i then (1:ℝ) else 0)
    (hopen : ∀ i e, e ∈ P i → a e = 1) :
    flowEnergy a (weightedFlow α θ) ≤
      ∑ i, ∑ j, α i*α j*((P i ∩ P j).card:ℝ) := by
  rw [flowEnergy_weighted_pairs]
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  exact mul_le_mul_of_nonneg_left
    (path_current_pair_energy_le_overlap a (θ i) (θ j) (P i) (P j) (hθ i) (hθ j) (hopen i))
    (mul_nonneg (hα i) (hα j))

/-- On the source good-weight event W>=1/2, normalizing the flow costs at most
FOUR in energy. This factor is derived rather than assumed in the budget. -/
theorem normalized_path_flow_energy_le_four_overlaps (a : E → ℝ) (w : I → ℝ)
    (θ : I → E → ℝ) (P : I → Finset E) (hw : ∀ i, 0 ≤ w i)
    (hW : (1/2:ℝ) ≤ ∑ i, w i)
    (hθ : ∀ i e, |θ i e| ≤ if e ∈ P i then (1:ℝ) else 0)
    (hopen : ∀ i e, e ∈ P i → a e = 1) :
    flowEnergy a (normalizedFlow w θ) ≤
      4*(∑ i, ∑ j, w i*w j*((P i ∩ P j).card:ℝ)) := by
  let W := ∑ i, w i
  have hWp : 0 < W := by dsimp [W]; linarith
  have hWs : 0 < W^2 := by positivity
  have hinv : 1/W^2 ≤ (4:ℝ) := by
    apply (div_le_iff₀ hWs).mpr
    dsimp [W]
    nlinarith [sq_nonneg ((∑ i, w i)-(1/2:ℝ))]
  have hb := weighted_path_flow_energy_le_overlaps a (fun i => w i/W) θ P
    (fun i => div_nonneg (hw i) hWp.le) hθ hopen
  change flowEnergy a (normalizedFlow w θ) ≤ _ at hb
  refine hb.trans ?_
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro j _hj
  have hp : 0 ≤ w i*w j*((P i ∩ P j).card:ℝ) :=
    mul_nonneg (mul_nonneg (hw i) (hw j)) (Nat.cast_nonneg _)
  calc
    _ = (1/W^2)*(w i*w j*((P i ∩ P j).card:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hinv hp

end NearCritical.Network
