module

public import NearCritical.SplitCrossDirectDistinctLower

/-! Independent terminal choices turn the additive cluster-reveal error
into a sum of pair overlaps times the products of the other edge masses. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical BigOperators

variable {d : ℕ} {U : Finset (Vertex d)} {ι α : Type*}

/-- Sum a function of the tube list over independent choices for each edge. -/
def sumTubeChoices (Y : ι → Finset α) (E : ι → α → TEdge d U) :
    List ι → (List (TEdge d U) → ℝ) → ℝ
  | [], f => f []
  | i :: l, f => ∑ y ∈ Y i, sumTubeChoices Y E l (fun es => f (E i y :: es))

private theorem sumTubeChoices_add (Y : ι → Finset α) (E : ι → α → TEdge d U) :
    ∀ (l : List ι) (f g : List (TEdge d U) → ℝ),
      sumTubeChoices Y E l (fun es => f es + g es) = sumTubeChoices Y E l f + sumTubeChoices Y E l g
  | [], _, _ => rfl
  | i :: l, f, g => by
    simp only [sumTubeChoices, sumTubeChoices_add Y E l, Finset.sum_add_distrib]

private theorem sumTubeChoices_sub (Y : ι → Finset α) (E : ι → α → TEdge d U) :
    ∀ (l : List ι) (f g : List (TEdge d U) → ℝ),
      sumTubeChoices Y E l (fun es => f es - g es) = sumTubeChoices Y E l f - sumTubeChoices Y E l g
  | [], _, _ => rfl
  | i :: l, f, g => by
    simp only [sumTubeChoices, sumTubeChoices_sub Y E l, Finset.sum_sub_distrib]

private theorem sumTubeChoices_mul_left (Y : ι → Finset α) (E : ι → α → TEdge d U) (c : ℝ) :
    ∀ (l : List ι) (f : List (TEdge d U) → ℝ),
      sumTubeChoices Y E l (fun es => c * f es) = c * sumTubeChoices Y E l f
  | [], _ => rfl
  | i :: l, f => by
    simp only [sumTubeChoices, sumTubeChoices_mul_left Y E c l, Finset.mul_sum]

private theorem sumTubeChoices_mul_right (Y : ι → Finset α) (E : ι → α → TEdge d U) (c : ℝ)
    (l : List ι) (f : List (TEdge d U) → ℝ) :
    sumTubeChoices Y E l (fun es => f es * c) = sumTubeChoices Y E l f * c := by
  simp_rw [mul_comm _ c, sumTubeChoices_mul_left]

theorem sumTubeChoices_mono (Y : ι → Finset α) (E : ι → α → TEdge d U) :
    ∀ (l : List ι) (f g : List (TEdge d U) → ℝ), (∀ es, f es ≤ g es) →
      sumTubeChoices Y E l f ≤ sumTubeChoices Y E l g
  | [], f, g, h => h []
  | i :: l, f, g, h =>
    Finset.sum_le_sum (fun y _ => sumTubeChoices_mono Y E l _ _ (fun es => h (E i y :: es)))

def tubeChoiceMass (p : unitInterval) (Y : ι → Finset α) (E : ι → α → TEdge d U) (i : ι) : ℝ :=
  ∑ y ∈ Y i, (E i y).tau p

def tubeChoiceProduct (p : unitInterval) (Y : ι → Finset α) (E : ι → α → TEdge d U) (l : List ι) : ℝ :=
  (l.map (tubeChoiceMass p Y E)).prod

theorem tubeChoiceMass_nonneg (p : unitInterval) (Y : ι → Finset α) (E : ι → α → TEdge d U) (i : ι) :
    0 ≤ tubeChoiceMass p Y E i :=
  Finset.sum_nonneg (fun _ _ => measureReal_nonneg)

theorem tubeChoiceProduct_nonneg (p : unitInterval) (Y : ι → Finset α) (E : ι → α → TEdge d U)
    (l : List ι) : 0 ≤ tubeChoiceProduct p Y E l := by
  apply List.prod_nonneg
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact tubeChoiceMass_nonneg p Y E i

theorem sumTubeChoices_prod (p : unitInterval) (Y : ι → Finset α) (E : ι → α → TEdge d U) :
    ∀ l : List ι, sumTubeChoices Y E l (fun es => (es.map (fun e => e.tau p)).prod) =
      tubeChoiceProduct p Y E l
  | [] => rfl
  | i :: l => by
    simp only [sumTubeChoices, List.map_cons, List.prod_cons, sumTubeChoices_mul_left,
      sumTubeChoices_prod p Y E l, tubeChoiceProduct, tubeChoiceMass, Finset.sum_mul]

private theorem sumTubeChoices_posSum_le (p : unitInterval) (Y : ι → Finset α)
    (E : ι → α → TEdge d U) (δ : ℝ) (hδ : 0 ≤ δ) (i : ι) :
    ∀ l : List ι,
      (∀ j ∈ l, (∑ y ∈ Y i, ∑ z ∈ Y j, (E i y).overlap p (E j z)) ≤
        δ * tubeChoiceMass p Y E i * tubeChoiceMass p Y E j) →
      (∑ y ∈ Y i, sumTubeChoices Y E l (posSum p (E i y))) ≤
        (l.length : ℝ) * δ * tubeChoiceMass p Y E i * tubeChoiceProduct p Y E l
  | [], _ => by simp [sumTubeChoices, posSum]
  | j :: l, h => by
    have htail := sumTubeChoices_posSum_le p Y E δ hδ i l (fun k hk => h k (List.mem_cons_of_mem _ hk))
    have hj := h j (by simp)
    let P := tubeChoiceProduct p Y E l
    let mi := tubeChoiceMass p Y E i
    let mj := tubeChoiceMass p Y E j
    have hP : 0 ≤ P := tubeChoiceProduct_nonneg p Y E l
    have hmj : 0 ≤ mj := tubeChoiceMass_nonneg p Y E j
    calc
      _ = (∑ y ∈ Y i, ∑ z ∈ Y j, (E i y).overlap p (E j z)) * P +
          mj * ∑ y ∈ Y i, sumTubeChoices Y E l (posSum p (E i y)) := by
        simp only [sumTubeChoices, posSum, sumTubeChoices_add, sumTubeChoices_mul_left,
          sumTubeChoices_prod, Finset.sum_add_distrib]
        congr 1
        · simp only [P, Finset.sum_mul]
        · simp only [mj, tubeChoiceMass, Finset.mul_sum, Finset.sum_mul]
      _ ≤ (δ * mi * mj) * P + mj * ((l.length : ℝ) * δ * mi * P) :=
        add_le_add (mul_le_mul_of_nonneg_right hj hP) (mul_le_mul_of_nonneg_left htail hmj)
      _ = _ := by
        change _ = ((j :: l).length : ℝ) * δ * mi * (mj * P)
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Summing all pair errors over the independent choices costs at most
the square of the edge count times the relative pair error. -/
theorem sumTubeChoices_errTotal_le (p : unitInterval) (Y : ι → Finset α)
    (E : ι → α → TEdge d U) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpair : ∀ i j, i ≠ j →
      (∑ y ∈ Y i, ∑ z ∈ Y j, (E i y).overlap p (E j z)) ≤
        δ * tubeChoiceMass p Y E i * tubeChoiceMass p Y E j) :
    ∀ l : List ι, l.Nodup →
      sumTubeChoices Y E l (errTotal p) ≤ (l.length : ℝ)^2 * δ * tubeChoiceProduct p Y E l
  | [], _ => by simp [sumTubeChoices, errTotal]
  | i :: l, h => by
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp h
    have htail := sumTubeChoices_errTotal_le p Y E δ hδ hpair l hl
    have hpos := sumTubeChoices_posSum_le p Y E δ hδ i l
      (fun j hj => hpair i j (fun h => hi (h ▸ hj)))
    let mi := tubeChoiceMass p Y E i
    let P := tubeChoiceProduct p Y E l
    have hmi : 0 ≤ mi := tubeChoiceMass_nonneg p Y E i
    have hP : 0 ≤ P := tubeChoiceProduct_nonneg p Y E l
    calc
      _ = sumTubeChoices Y E l (errTotal p) * mi +
          ∑ y ∈ Y i, sumTubeChoices Y E l (posSum p (E i y)) := by
        simp only [sumTubeChoices, errTotal, sumTubeChoices_add, sumTubeChoices_mul_right,
          Finset.sum_add_distrib, mi, tubeChoiceMass, Finset.mul_sum]
      _ ≤ ((l.length : ℝ)^2 * δ * P) * mi + (l.length : ℝ) * δ * mi * P :=
        add_le_add (mul_le_mul_of_nonneg_right htail hmi) hpos
      _ = ((l.length : ℝ)^2 + (l.length : ℝ)) * (δ * (mi * P)) := by ring
      _ ≤ (((i :: l).length : ℝ)^2) * (δ * (mi * P)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith only [Nat.cast_nonneg (α := ℝ) l.length]
      _ = _ := by
        change _ = ((i :: l).length : ℝ)^2 * δ * (mi * P)
        ring

theorem sumTubeChoices_distinct_lower (p : unitInterval) (Y : ι → Finset α)
    (E : ι → α → TEdge d U) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpair : ∀ i j, i ≠ j →
      (∑ y ∈ Y i, ∑ z ∈ Y j, (E i y).overlap p (E j z)) ≤
        δ * tubeChoiceMass p Y E i * tubeChoiceMass p Y E j)
    (l : List ι) (hl : l.Nodup) :
    (1 - (l.length : ℝ)^2 * δ) * tubeChoiceProduct p Y E l ≤
      sumTubeChoices Y E l (fun es => (percolation d p).real (distinctLoc U (es.map TEdge.loc))) := by
  have h := sumTubeChoices_mono Y E l _ _ (distinct_edges_lower p)
  rw [sumTubeChoices_sub, sumTubeChoices_prod] at h
  have hErr := sumTubeChoices_errTotal_le p Y E δ hδ hpair l hl
  have hb := sub_le_sub_left hErr (tubeChoiceProduct p Y E l)
  rw [sub_mul, one_mul]
  exact hb.trans h

end NearCritical.SplitCrossDirect
