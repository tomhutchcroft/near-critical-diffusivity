module

public import NearCritical.CriticalBubble
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Finiteness of the actual critical triangle diagram from source assumption (A).
No triangle condition or spatial convolution bound is used as a premise. -/
@[expose] public section
namespace NearCritical

lemma twoPoint_symm {d : ℕ} (p : unitInterval) (x y : Vertex d) :
    twoPoint d p x y = twoPoint d p y x := by
  unfold twoPoint
  congr 1
  ext ω
  exact SimpleGraph.reachable_comm

private lemma small_mul_le_pair_rpow {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≤ b) (hac : a ≤ c) :
    a * b * c ≤ b ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) := by
  have hbc : 0 ≤ b * c := mul_nonneg hb hc
  have hs : a ≤ Real.sqrt (b * c) := (Real.le_sqrt ha hbc).mpr (by
    simpa only [pow_two] using mul_le_mul hab hac ha hb)
  calc
    a * b * c = a * (b * c) := by ring
    _ ≤ Real.sqrt (b * c) * (b * c) := mul_le_mul_of_nonneg_right hs hbc
    _ = (b * c) ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num,
        Real.rpow_add' hbc (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    _ = _ := Real.mul_rpow hb hc

/-- A nonnegative triple product is dominated by the three pair products
raised to 3/2. This elementary bound suffices for triangle convergence. -/
lemma triple_mul_le_pair_three_halves {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ) +
      b ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) +
      a ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) := by
  have hab0 := mul_nonneg (Real.rpow_nonneg ha (3 / 2 : ℝ)) (Real.rpow_nonneg hb (3 / 2 : ℝ))
  have hbc0 := mul_nonneg (Real.rpow_nonneg hb (3 / 2 : ℝ)) (Real.rpow_nonneg hc (3 / 2 : ℝ))
  have hac0 := mul_nonneg (Real.rpow_nonneg ha (3 / 2 : ℝ)) (Real.rpow_nonneg hc (3 / 2 : ℝ))
  rcases le_total a b with hab | hba
  · by_cases hac : a ≤ c
    · exact (small_mul_le_pair_rpow ha hb hc hab hac).trans (by linarith)
    · have h := small_mul_le_pair_rpow hc ha hb (le_of_not_ge hac)
        ((le_of_not_ge hac).trans hab)
      nlinarith
  · by_cases hbc : b ≤ c
    · have h := small_mul_le_pair_rpow hb ha hc hba hbc
      nlinarith
    · have h := small_mul_le_pair_rpow hc ha hb ((le_of_not_ge hbc).trans hba)
        (le_of_not_ge hbc)
      nlinarith

/-- Source's critical triangle diagram is summable when d>6 and (A) holds. -/
theorem critical_triangle_summable {d : ℕ} (hd : 6 < d) (h : TwoPointAsymptotics d) :
    Summable (fun z : Vertex d × Vertex d =>
      twoPoint d (criticalPoint d) 0 z.1 * twoPoint d (criticalPoint d) z.1 z.2 *
        twoPoint d (criticalPoint d) z.2 0) := by
  let f : Vertex d → ℝ := fun x => (twoPoint d (criticalPoint d) 0 x) ^ (3 / 2 : ℝ)
  have hf : Summable f := by
    apply critical_twoPoint_rpow_summable (by omega) h (3 / 2 : ℝ) (by norm_num)
    have hd' : (6 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hf0 : 0 ≤ f := fun x => Real.rpow_nonneg (twoPoint_nonneg _ _ _) _
  have hp := hf.mul_of_nonneg hf hf0 hf0
  have hinj1 : Function.Injective (fun z : Vertex d × Vertex d => (z.1, z.2 - z.1)) := by
    intro u v huv
    have h1 := congrArg Prod.fst huv
    have h2 := congrArg Prod.snd huv
    dsimp at h1 h2
    apply Prod.ext h1
    rw [h1] at h2
    exact add_right_cancel (by simpa only [sub_eq_add_neg] using h2)
  have hinj2 : Function.Injective (fun z : Vertex d × Vertex d => (z.2 - z.1, z.2)) := by
    intro u v huv
    have h1 := congrArg Prod.fst huv
    have h2 := congrArg Prod.snd huv
    dsimp at h1 h2
    apply Prod.ext _ h2
    rw [h2] at h1
    apply neg_injective
    exact add_left_cancel (by simpa only [sub_eq_add_neg] using h1)
  have hs := ((hp.comp_injective hinj1).add (hp.comp_injective hinj2)).add hp
  apply hs.of_nonneg_of_le (fun z => mul_nonneg
    (mul_nonneg (twoPoint_nonneg _ _ _) (twoPoint_nonneg _ _ _)) (twoPoint_nonneg _ _ _))
  intro z
  have hb := triple_mul_le_pair_three_halves
    (twoPoint_nonneg (criticalPoint d) 0 z.1)
    (twoPoint_nonneg (criticalPoint d) z.1 z.2)
    (twoPoint_nonneg (criticalPoint d) z.2 0)
  simpa only [Function.comp_def, Pi.add_apply, f,
    ← twoPoint_eq_displacement, twoPoint_symm (criticalPoint d) z.2 0] using hb

/-- An extended-nonnegative sum formulation makes finiteness explicit, avoiding
the zero-by-convention value of a nonsummable real tsum. -/
theorem critical_triangle_ennreal_lt_top {d : ℕ} (hd : 6 < d) (h : TwoPointAsymptotics d) :
    (∑' z : Vertex d × Vertex d, ENNReal.ofReal
      (twoPoint d (criticalPoint d) 0 z.1 * twoPoint d (criticalPoint d) z.1 z.2 *
        twoPoint d (criticalPoint d) z.2 0)) < ⊤ :=
  (critical_triangle_summable hd h).tsum_ofReal_lt_top

end NearCritical
