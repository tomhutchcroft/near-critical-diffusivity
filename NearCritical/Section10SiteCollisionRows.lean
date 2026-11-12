module

public import NearCritical.Section10FirstGoodDisjointRow

/-! Weighted site-collision bounds on a solo arrival and on a shared
arrival whose two incoming bridges are disjoint. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

private theorem integral_finite_union_of_rows {Ω X C : Type*}
    [MeasurableSpace Ω] [Fintype X] (μ : Measure Ω)
    (S : Finset C) (F : C → X → Prop) [decF : ∀ c y, Decidable (F c y)]
    (K : X → Ω → ℝ)
    (hK : ∀ y z, 0 ≤ K y z) (hI : ∀ y, Integrable (K y) μ)
    {a : ℝ} (ha : ∀ c ∈ S,
      (∫ z, ∑ y, if F c y then K y z else 0 ∂μ) ≤ a) :
    (∫ z, ∑ y, if ∃ c ∈ S, F c y then K y z else 0 ∂μ) ≤ (S.card : ℝ) * a := by
  let U (c : C) (z : Ω) := ∑ y, if F c y then K y z else 0
  have hU (c : C) : Integrable (U c) μ := by
    apply integrable_finsetSum
    intro y _
    by_cases h : F c y
    · simpa only [if_pos h] using hI y
    · simp only [if_neg h]
      exact integrable_zero Ω ℝ μ
  calc
    _ ≤ ∫ z, ∑ c ∈ S, U c z ∂μ := by
      let f (z : Ω) := ∑ y, if ∃ c ∈ S, F c y then K y z else 0
      let g (z : Ω) := ∑ c ∈ S, U c z
      refine integral_mono_of_nonneg (f := f) (g := g) ?_
        (integrable_finsetSum _ (fun c _ => hU c)) ?_
      · refine Filter.Eventually.of_forall fun z => ?_
        change 0 ≤ f z
        unfold f
        exact Finset.sum_nonneg fun y _ => by split_ifs <;> first | exact hK y z | exact le_rfl
      · refine Filter.Eventually.of_forall fun z => ?_
        change f z ≤ g z
        dsimp only [f, g, U]
        rw [Finset.sum_comm (s := S)]
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases he : ∃ c ∈ S, F c y
        · obtain ⟨c,hc,hcy⟩ := he
          rw [if_pos ⟨c,hc,hcy⟩]
          have h := Finset.single_le_sum (s := S) (f := fun c => if F c y then K y z else 0)
            (fun c _ => by split_ifs <;> first | exact hK y z | exact le_rfl) hc
          simpa only [if_pos hcy] using h
        · rw [if_neg he]
          exact Finset.sum_nonneg fun c _ => by split_ifs <;> first | exact hK y z | exact le_rfl
    _ = ∑ c ∈ S, ∫ z, U c z ∂μ := integral_finsetSum _ (fun c _ => hU c)
    _ ≤ ∑ _c ∈ S, a := Finset.sum_le_sum ha
    _ = _ := by simp [nsmul_eq_mul]

namespace NestLayout

variable {Ω X C : Type*} [MeasurableSpace Ω] [Fintype X]

/-- A fresh arrival overlaps an earlier, fixed nest with weighted mass
at most the number of its clusters times the one-child bound. -/
theorem firstGood_solo_site_collision_row_le
    (μ : Measure Ω) (nest : X → Finset C)
    (K : X → Ω → ℝ)
    (hK : ∀ y z, 0 ≤ K y z) (hI : ∀ y, Integrable (K y) μ)
    (N : Finset C) {a : ℝ}
    (hrow : ∀ c ∈ N, (∫ z, ∑ y : X, if c ∈ nest y then K y z else 0 ∂μ) ≤ a) :
    (∫ z, ∑ y : X, if (N ∩ nest y).Nonempty then K y z else 0 ∂μ) ≤
      (N.card : ℝ) * a := by
  have hmark (y : X) : (N ∩ nest y).Nonempty ↔ ∃ c ∈ N, c ∈ nest y := by
    simp only [Finset.Nonempty, Finset.mem_inter]
  simp_rw [hmark]
  exact integral_finite_union_of_rows μ N (fun c (y : X) => c ∈ nest y)
    (decF := fun c y => inferInstanceAs (Decidable (c ∈ nest y))) K hK hI hrow

/-- After disjoint bridges, a shared arrival can collide only by producing
the same child. Summing the H2 estimate along this diagonal pays one
factor of the size of the typical family. -/
theorem firstGood_disjoint_site_collision_row_le
    (μ : Measure Ω) (nest : X → Finset C)
    (K K' : X → Ω → ℝ)
    (g : Ω → ℝ)
    (hJ : ∀ (y : X × X) z, 0 ≤ g z * (K y.1 z * K' y.2 z))
    (hI : ∀ y : X × X, Integrable (fun z => g z * (K y.1 z * K' y.2 z)) μ)
    (S : Finset C) {a : ℝ} :
    let U (L : X → Ω → ℝ) (c : C) z :=
      ∑ y : X, if c ∈ nest y then L y z else 0
    (∀ c ∈ S, (∫ z, g z * (U K c z * U K' c z) ∂μ) ≤ a) →
    (∫ z, ∑ y : X × X,
      if (S ∩ (nest y.1 ∩ nest y.2)).Nonempty
      then g z * (K y.1 z * K' y.2 z) else 0 ∂μ) ≤ (S.card : ℝ) * a := by
  intro U hrow
  let J (y : X × X) z := g z * (K y.1 z * K' y.2 z)
  have hrow' (c : C) (hc : c ∈ S) :
      (∫ z, ∑ y : X × X, if c ∈ nest y.1 ∧ c ∈ nest y.2 then J y z else 0 ∂μ) ≤ a := by
    refine le_trans ?_ (hrow c hc)
    apply le_of_eq
    apply integral_congr_ae
    filter_upwards with z
    rw [Fintype.sum_prod_type]
    dsimp only [U]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
    by_cases hy : c ∈ nest y <;> by_cases hy' : c ∈ nest y' <;> simp [J, hy, hy']
  have hmark (y : X × X) : (S ∩ (nest y.1 ∩ nest y.2)).Nonempty ↔
      ∃ c ∈ S, c ∈ nest y.1 ∧ c ∈ nest y.2 := by
    simp only [Finset.Nonempty, Finset.mem_inter]
  change (∫ z, ∑ y : X × X,
    if (S ∩ (nest y.1 ∩ nest y.2)).Nonempty then J y z else 0 ∂μ) ≤ _
  simp_rw [hmark]
  exact integral_finite_union_of_rows μ S
    (fun c (y : X × X) => c ∈ nest y.1 ∧ c ∈ nest y.2)
    (decF := fun c y => inferInstanceAs (Decidable (c ∈ nest y.1 ∧ c ∈ nest y.2))) J hJ hI hrow'

end NestLayout
end NearCritical.Section10
