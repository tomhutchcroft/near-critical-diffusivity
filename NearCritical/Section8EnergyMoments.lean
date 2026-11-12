module
public import NearCritical.Section8ConditionalVariance
public import NearCritical.RegularityEnergyTails

/-! Section 8, the exact conditional expectation formulas preceding Ef1/Ef2.
The weights are the literal ERE1/ERE2 weights of the FULL heart-cluster union.
No quantitative mean, variance or diagram estimate is assumed or asserted. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

def energyOneWeight {d : ℕ} (excluded : Finset (Vertex d)) (r : ℕ) (x y : Vertex d) : ℝ :=
  if y ∉ excluded then (max (r:ℝ) (latticeDistance x y))^((2:ℤ)-(d:ℤ)) else 0

def energyTwoWeight {d : ℕ} (cubeBoundary : Finset (Vertex d)) (r : ℕ) (x y : Vertex d) : ℝ :=
  if y ∈ cubeBoundary then (max (r:ℝ) (latticeDistance x y))^((4:ℤ)-(d:ℤ)) else 0

lemma energyOneWeight_nonneg {d : ℕ} (excluded : Finset (Vertex d)) (r : ℕ) (x y : Vertex d) :
    0 ≤ energyOneWeight excluded r x y := by
  unfold energyOneWeight
  split_ifs <;> positivity

lemma energyTwoWeight_nonneg {d : ℕ} (cubeBoundary : Finset (Vertex d)) (r : ℕ) (x y : Vertex d) :
    0 ≤ energyTwoWeight cubeBoundary r x y := by
  unfold energyTwoWeight
  split_ifs <;> positivity

private lemma sum_indicator_eq_sum {α : Type*} [DecidableEq α]
    (Q F : Finset α) (hF : F ⊆ Q) (f : α → ℝ) :
    (∑ y ∈ Q, if y ∈ F then f y else 0) = ∑ y ∈ F, f y := by
  have he : Q.filter (fun y => y ∈ F) = F := by
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun hy => ⟨hF hy,hy⟩⟩
  rw [← Finset.sum_filter,he]

/-- Exact ERE1 as a weighted actual heart statistic, retaining the excluded S. -/
lemma weightedHeartStatistic_energyOne {d : ℕ} (Q H excluded : Finset (Vertex d))
    (hH : H ⊆ Q) (r : ℕ) (x : Vertex d) (ω : Configuration d) :
    weightedHeartStatistic Q H (energyOneWeight excluded r x) ω =
      regularityEnergyOne (heartClusterUnion ω Q H) excluded r x := by
  calc
    _ = ∑ y ∈ heartClusterUnion ω Q H, energyOneWeight excluded r x y :=
      (weightedHeartStatistic_eq_union Q H hH (energyOneWeight excluded r x) ω).trans
        (sum_indicator_eq_sum Q _ (heartClusterUnion_subset ω Q H) (energyOneWeight excluded r x))
    _ = _ := by
      unfold energyOneWeight regularityEnergyOne
      rw [← Finset.sum_filter]
      congr 1
      ext y
      simp

/-- Exact ERE2 uses the FULL cube boundary, not a truncated counting subface. -/
lemma weightedHeartStatistic_energyTwo {d : ℕ} (Q H cubeBoundary : Finset (Vertex d))
    (hH : H ⊆ Q) (r : ℕ) (x : Vertex d) (ω : Configuration d) :
    weightedHeartStatistic Q H (energyTwoWeight cubeBoundary r x) ω =
      regularityEnergyTwo (heartClusterUnion ω Q H) cubeBoundary r x := by
  calc
    _ = ∑ y ∈ heartClusterUnion ω Q H, energyTwoWeight cubeBoundary r x y :=
      (weightedHeartStatistic_eq_union Q H hH (energyTwoWeight cubeBoundary r x) ω).trans
        (sum_indicator_eq_sum Q _ (heartClusterUnion_subset ω Q H) (energyTwoWeight cubeBoundary r x))
    _ = _ := by
      unfold energyTwoWeight regularityEnergyTwo
      rw [← Finset.sum_filter]
      congr 1

private lemma conditionalMean_bridge {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (hH : H ⊆ Q) (x : Vertex d) (f : Vertex d → ℝ) (g : Finset (Vertex d) → ℝ)
    (hZ : ∀ ω : Configuration d, weightedHeartStatistic Q H f ω = g (heartClusterUnion ω Q H)) :
    weightedHeartConditionalMean p Q H x f = heartConditionalMean p Q H g x := by
  have hset : {ω : Configuration d | x ∈ heartClusterUnion ω Q H} = heartEvent Q H x := by
    ext ω
    exact (heartEvent_iff_union_member Q H hH x ω).symm
  unfold weightedHeartConditionalMean heartConditionalMean
  rw [hset]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [← hZ ω]
  by_cases hx : ω ∈ heartEvent Q H x
  · have hxF := (heartEvent_iff_union_member Q H hH x ω).mp hx
    simp [eventIndicator,hx,hxF]
  · have hxF : x ∉ heartClusterUnion ω Q H := fun h => hx
      ((heartEvent_iff_union_member Q H hH x ω).mpr h)
    simp [eventIndicator,hx,hxF]

/-- Literal actual conditional ERE1 mean as a weighted joint-membership sum.
The quantitative Ef1 bound is a separate diagram-estimate obligation. -/
theorem energyOne_conditional_mean_exact {d : ℕ} (p : unitInterval)
    (Q H excluded : Finset (Vertex d)) (hH : H ⊆ Q) (r : ℕ) (x : Vertex d) :
    heartConditionalMean p Q H (fun F => regularityEnergyOne F excluded r x) x =
      (∑ y ∈ Q, energyOneWeight excluded r x y * (percolation d p).real (heartPairEvent Q H x y)) /
        (percolation d p).real (heartEvent Q H x) := by
  rw [← conditionalMean_bridge p Q H hH x (energyOneWeight excluded r x)
    (fun F => regularityEnergyOne F excluded r x)
    (weightedHeartStatistic_energyOne Q H excluded hH r x)]
  unfold weightedHeartConditionalMean
  rw [weightedHeart_first_moment]

/-- Literal actual conditional ERE2 mean, preserving full-boundary weights. -/
theorem energyTwo_conditional_mean_exact {d : ℕ} (p : unitInterval)
    (Q H cubeBoundary : Finset (Vertex d)) (hH : H ⊆ Q) (r : ℕ) (x : Vertex d) :
    heartConditionalMean p Q H (fun F => regularityEnergyTwo F cubeBoundary r x) x =
      (∑ y ∈ Q, energyTwoWeight cubeBoundary r x y * (percolation d p).real (heartPairEvent Q H x y)) /
        (percolation d p).real (heartEvent Q H x) := by
  rw [← conditionalMean_bridge p Q H hH x (energyTwoWeight cubeBoundary r x)
    (fun F => regularityEnergyTwo F cubeBoundary r x)
    (weightedHeartStatistic_energyTwo Q H cubeBoundary hH r x)]
  unfold weightedHeartConditionalMean
  rw [weightedHeart_first_moment]

private lemma centeredMoment_bridge {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (hH : H ⊆ Q) (x : Vertex d) (f : Vertex d → ℝ) (g : Finset (Vertex d) → ℝ)
    (hZ : ∀ ω : Configuration d, weightedHeartStatistic Q H f ω = g (heartClusterUnion ω Q H))
    (hq : 0 < (percolation d p).real (heartEvent Q H x)) :
    heartCenteredMoment p Q H g x = (percolation d p).real (heartEvent Q H x) *
      weightedHeartConditionalVariance p Q H x f := by
  have hm := conditionalMean_bridge p Q H hH x f g hZ
  have he : heartCenteredMoment p Q H g x =
      ∫ ω, eventIndicator (heartEvent Q H x) ω *
        (weightedHeartStatistic Q H f ω-weightedHeartConditionalMean p Q H x f)^2 ∂percolation d p := by
    unfold heartCenteredMoment
    rw [← hm]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [← hZ ω]
    by_cases hx : ω ∈ heartEvent Q H x
    · have hxF := (heartEvent_iff_union_member Q H hH x ω).mp hx
      simp [eventIndicator,hx,hxF]
    · have hxF : x ∉ heartClusterUnion ω Q H := fun h => hx
        ((heartEvent_iff_union_member Q H hH x ω).mpr h)
      simp [eventIndicator,hx,hxF]
  have hc := weightedHeart_variance_eq_centered p Q H x f hq
  rw [← he] at hc
  have h := (eq_div_iff (ne_of_gt hq)).mp hc
  nlinarith

private lemma centeredMoment_le_branch_sum {d : ℕ} (p : unitInterval)
    (Q H : Finset (Vertex d)) (hH : H ⊆ Q) (x : Vertex d)
    (f : Vertex d → ℝ) (g : Finset (Vertex d) → ℝ)
    (hZ : ∀ ω : Configuration d, weightedHeartStatistic Q H f ω = g (heartClusterUnion ω Q H))
    (hf : ∀ y ∈ Q, 0 ≤ f y) (hq : 0 < (percolation d p).real (heartEvent Q H x)) :
    heartCenteredMoment p Q H g x ≤
      ∑ y ∈ Q, ∑ z ∈ Q, f y*f z*(percolation d p).real (heartBranchEvent Q H x y z) := by
  rw [centeredMoment_bridge p Q H hH x f g hZ hq]
  have h := mul_le_mul_of_nonneg_left (weightedHeart_conditional_variance_bound p Q H x f hf) hq.le
  have he : (percolation d p).real (heartEvent Q H x) *
      ((∑ y ∈ Q, ∑ z ∈ Q, f y*f z*(percolation d p).real (heartBranchEvent Q H x y z)) /
        (percolation d p).real (heartEvent Q H x)) =
      ∑ y ∈ Q, ∑ z ∈ Q, f y*f z*(percolation d p).real (heartBranchEvent Q H x y z) := by
    field_simp [ne_of_gt hq]
  exact h.trans_eq he

/-- Actual unnormalized conditional ERE1 moment bounded by literal A(y,z).
Numerical five-diagram estimates are separate, not supplied variance premises. -/
theorem energyOne_centeredMoment_le_branches {d : ℕ} (p : unitInterval)
    (Q H excluded : Finset (Vertex d)) (hH : H ⊆ Q) (r : ℕ) (x : Vertex d)
    (hq : 0 < (percolation d p).real (heartEvent Q H x)) :
    heartCenteredMoment p Q H (fun F => regularityEnergyOne F excluded r x) x ≤
      ∑ y ∈ Q, ∑ z ∈ Q, energyOneWeight excluded r x y * energyOneWeight excluded r x z *
        (percolation d p).real (heartBranchEvent Q H x y z) :=
  centeredMoment_le_branch_sum p Q H hH x (energyOneWeight excluded r x)
    (fun F => regularityEnergyOne F excluded r x)
    (weightedHeartStatistic_energyOne Q H excluded hH r x)
    (fun y _ => energyOneWeight_nonneg excluded r x y) hq

/-- ERE2 counterpart, retaining the full cube boundary in both weights. -/
theorem energyTwo_centeredMoment_le_branches {d : ℕ} (p : unitInterval)
    (Q H cubeBoundary : Finset (Vertex d)) (hH : H ⊆ Q) (r : ℕ) (x : Vertex d)
    (hq : 0 < (percolation d p).real (heartEvent Q H x)) :
    heartCenteredMoment p Q H (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤
      ∑ y ∈ Q, ∑ z ∈ Q, energyTwoWeight cubeBoundary r x y * energyTwoWeight cubeBoundary r x z *
        (percolation d p).real (heartBranchEvent Q H x y z) :=
  centeredMoment_le_branch_sum p Q H hH x (energyTwoWeight cubeBoundary r x)
    (fun F => regularityEnergyTwo F cubeBoundary r x)
    (weightedHeartStatistic_energyTwo Q H cubeBoundary hH r x)
    (fun y _ => energyTwoWeight_nonneg cubeBoundary r x y) hq

end NearCritical.Section8
