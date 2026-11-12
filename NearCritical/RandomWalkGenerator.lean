module

public import NearCritical.RectangleBoundary
public import NearCritical.Events
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The unit-conductance variable-speed generator of source eq.VSRW.
Each open nearest-neighbor bond has rate one; there is no degree normalization.
This module constructs rates and a uniformized one-step kernel, not a process. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory ProbabilityTheory
open scoped Classical

/-- The at most 2d nearest neighbors, indexed by positive bonds and predecessors. -/
def latticeNeighbors {d : ℕ} (x : Vertex d) : Finset (Vertex d) :=
  (univ.image (fun i : Fin d ↦ bondTip (x, i))) ∪
    (univ.image (fun i : Fin d ↦ bondPredecessor x i))

lemma mem_latticeNeighbors_iff {d : ℕ} (x y : Vertex d) :
    y ∈ latticeNeighbors x ↔ (openGraph (fun _ ↦ true)).Adj x y := by
  constructor
  · intro hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hy
      exact fullGraph_adj_tip x i
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hy
      exact fullGraph_adj_predecessor x i
  · rintro ⟨e, _, h | h⟩
    · apply mem_union.mpr
      left
      apply mem_image.mpr
      exact ⟨e.2, mem_univ _, by simpa [h.1] using h.2.symm⟩
    · apply mem_union.mpr
      right
      apply mem_image.mpr
      exact ⟨e.2, mem_univ _, by rw [h.2, predecessor_bondTip]; exact h.1.symm⟩

lemma card_latticeNeighbors_le {d : ℕ} (x : Vertex d) :
    (latticeNeighbors x).card ≤ 2 * d := by
  calc
    _ ≤ (univ.image (fun i : Fin d ↦ bondTip (x, i))).card +
        (univ.image (fun i : Fin d ↦ bondPredecessor x i)).card := card_union_le _ _
    _ ≤ (univ : Finset (Fin d)).card + (univ : Finset (Fin d)).card :=
      Nat.add_le_add (card_image_le) (card_image_le)
    _ = 2 * d := by simp [two_mul]

/-- Exactly the neighbors joined to x by an open uniquely indexed lattice bond. -/
def openNeighbors {d : ℕ} (ω : Configuration d) (x : Vertex d) : Finset (Vertex d) :=
  (latticeNeighbors x).filter (fun y ↦ (openGraph ω).Adj x y)

lemma mem_openNeighbors_iff {d : ℕ} (ω : Configuration d) (x y : Vertex d) :
    y ∈ openNeighbors ω x ↔ (openGraph ω).Adj x y := by
  constructor
  · exact fun h ↦ (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨(mem_latticeNeighbors_iff x y).mpr
      (openGraph_mono (fun _ _ ↦ rfl) h), h⟩

lemma self_not_mem_openNeighbors {d : ℕ} (ω : Configuration d) (x : Vertex d) :
    x ∉ openNeighbors ω x := by
  intro h
  exact ((mem_openNeighbors_iff ω x x).mp h).ne rfl

lemma card_openNeighbors_le {d : ℕ} (ω : Configuration d) (x : Vertex d) :
    (openNeighbors ω x).card ≤ 2 * d :=
  (card_filter_le _ _).trans (card_latticeNeighbors_le x)

/-- Off-diagonal unit rate on each open bond, zero otherwise. -/
def jumpRate {d : ℕ} (ω : Configuration d) (x y : Vertex d) : ℝ :=
  if y ∈ openNeighbors ω x then 1 else 0

lemma jumpRate_eq_one_iff {d : ℕ} (ω : Configuration d) (x y : Vertex d) :
    jumpRate ω x y = 1 ↔ (openGraph ω).Adj x y := by
  simp [jumpRate, mem_openNeighbors_iff]

lemma jumpRate_nonneg {d : ℕ} (ω : Configuration d) (x y : Vertex d) :
    0 ≤ jumpRate ω x y := by
  simp only [jumpRate]
  split <;> norm_num

lemma jumpRate_self {d : ℕ} (ω : Configuration d) (x : Vertex d) :
    jumpRate ω x x = 0 := by
  simp [jumpRate, self_not_mem_openNeighbors]

lemma jumpRate_symmetric {d : ℕ} (ω : Configuration d) (x y : Vertex d) :
    jumpRate ω x y = jumpRate ω y x := by
  simp only [jumpRate, mem_openNeighbors_iff]
  rw [SimpleGraph.adj_comm]

/-- Total departure rate: the open degree, not a constant normalized to one. -/
def totalJumpRate {d : ℕ} (ω : Configuration d) (x : Vertex d) : ℝ :=
  ((openNeighbors ω x).card : ℝ)

lemma totalJumpRate_nonneg {d : ℕ} (ω : Configuration d) (x : Vertex d) :
    0 ≤ totalJumpRate ω x := Nat.cast_nonneg _

lemma totalJumpRate_le {d : ℕ} (ω : Configuration d) (x : Vertex d) :
    totalJumpRate ω x ≤ 2 * (d : ℝ) := by
  unfold totalJumpRate
  exact_mod_cast card_openNeighbors_le ω x

lemma totalJumpRate_eq_sum {d : ℕ} (ω : Configuration d) (x : Vertex d) :
    totalJumpRate ω x = ∑ y ∈ latticeNeighbors x, jumpRate ω x y := by
  have hs : ∑ y ∈ openNeighbors ω x, jumpRate ω x y = totalJumpRate ω x := by
    calc
      _ = ∑ _y ∈ openNeighbors ω x, (1 : ℝ) := by
        apply sum_congr rfl
        intro y hy
        simp [jumpRate, hy]
      _ = _ := by simp [totalJumpRate]
  rw [← hs]
  exact sum_subset (filter_subset _ _) (fun y _ hy ↦ by simp [jumpRate, hy])

/-- Source eq.VSRW: sum over open bonds of the unnormalized increment. -/
def randomWalkGenerator {d : ℕ} (ω : Configuration d) (f : Vertex d → ℝ)
    (x : Vertex d) : ℝ :=
  ∑ y ∈ openNeighbors ω x, (f y - f x)

lemma randomWalkGenerator_eq_sum_rates {d : ℕ} (ω : Configuration d)
    (f : Vertex d → ℝ) (x : Vertex d) :
    randomWalkGenerator ω f x =
      ∑ y ∈ latticeNeighbors x, jumpRate ω x y * (f y - f x) := by
  unfold randomWalkGenerator
  calc
    _ = ∑ y ∈ openNeighbors ω x, jumpRate ω x y * (f y - f x) := by
      apply sum_congr rfl
      intro y hy
      simp [jumpRate, hy]
    _ = _ := sum_subset (filter_subset _ _) (fun y _ hy ↦ by simp [jumpRate, hy])

lemma randomWalkGenerator_const {d : ℕ} (ω : Configuration d) (c : ℝ) (x : Vertex d) :
    randomWalkGenerator ω (fun _ ↦ c) x = 0 := by
  simp [randomWalkGenerator]

/-- Uniformization at the deterministic bound 2d. Missing open neighbors give
holding mass at x, rather than increasing the rates of the remaining bonds. -/
def uniformizedWeight {d : ℕ} (ω : Configuration d) (x y : Vertex d) : ℝ :=
  if y = x then 1 - totalJumpRate ω x / (2 * (d : ℝ))
  else jumpRate ω x y / (2 * (d : ℝ))

lemma uniformizedWeight_nonneg {d : ℕ} (hd : 0 < d) (ω : Configuration d)
    (x y : Vertex d) : 0 ≤ uniformizedWeight ω x y := by
  have hden : 0 < 2 * (d : ℝ) := by positivity
  unfold uniformizedWeight
  split
  · exact sub_nonneg.mpr ((div_le_one hden).mpr (totalJumpRate_le ω x))
  · exact div_nonneg (jumpRate_nonneg ω x y) hden.le

lemma uniformizedWeight_eq_zero_of_not_mem {d : ℕ} (ω : Configuration d)
    (x y : Vertex d) (hy : y ∉ insert x (openNeighbors ω x)) :
    uniformizedWeight ω x y = 0 := by
  have hne : y ≠ x := fun h ↦ hy (mem_insert.mpr (Or.inl h))
  have hn : y ∉ openNeighbors ω x := fun h ↦ hy (mem_insert.mpr (Or.inr h))
  simp [uniformizedWeight, hne, jumpRate, hn]

lemma sum_uniformizedWeight {d : ℕ} (_hd : 0 < d) (ω : Configuration d) (x : Vertex d) :
    ∑ y ∈ insert x (openNeighbors ω x), uniformizedWeight ω x y = 1 := by
  rw [sum_insert (self_not_mem_openNeighbors ω x)]
  have hs : ∑ y ∈ openNeighbors ω x, uniformizedWeight ω x y =
      totalJumpRate ω x / (2 * (d : ℝ)) := by
    calc
      _ = ∑ _y ∈ openNeighbors ω x, 1 / (2 * (d : ℝ)) := by
        apply sum_congr rfl
        intro y hy
        have hne : y ≠ x := fun heq ↦ self_not_mem_openNeighbors ω x (heq ▸ hy)
        simp [uniformizedWeight, hne, jumpRate, hy]
      _ = _ := by simp [totalJumpRate, div_eq_mul_inv]
  rw [hs]
  simp [uniformizedWeight]

/-- A genuine finite-support probability distribution for each starting vertex. -/
def uniformizedPMF {d : ℕ} (hd : 0 < d) (ω : Configuration d) (x : Vertex d) :
    PMF (Vertex d) :=
  PMF.ofFinset (fun y ↦ ENNReal.ofReal (uniformizedWeight ω x y))
    (insert x (openNeighbors ω x)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ uniformizedWeight_nonneg hd ω x y),
        sum_uniformizedWeight hd ω x]
      simp)
    (fun y hy ↦ by rw [uniformizedWeight_eq_zero_of_not_mem ω x y hy]; simp)

lemma uniformizedPMF_apply {d : ℕ} (hd : 0 < d) (ω : Configuration d) (x y : Vertex d) :
    uniformizedPMF hd ω x y = ENNReal.ofReal (uniformizedWeight ω x y) := rfl

/-- The uniformized one-step Markov kernel, for a fixed environment. -/
def uniformizedKernel {d : ℕ} (hd : 0 < d) (ω : Configuration d) :
    Kernel (Vertex d) (Vertex d) :=
  Kernel.ofFunOfCountable (fun x ↦ (uniformizedPMF hd ω x).toMeasure)

instance uniformizedKernel_isMarkov {d : ℕ} (hd : 0 < d) (ω : Configuration d) :
    IsMarkovKernel (uniformizedKernel hd ω) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (uniformizedPMF hd ω x).toMeasure
    infer_instance

/-- Exact uniformization identity P f = f + L f/(2d), for every test function.
All sums are finite, so no integrability or boundedness premise is needed. -/
theorem uniformizedWeight_action {d : ℕ} (_hd : 0 < d) (ω : Configuration d)
    (f : Vertex d → ℝ) (x : Vertex d) :
    ∑ y ∈ insert x (openNeighbors ω x), uniformizedWeight ω x y * f y =
      f x + randomWalkGenerator ω f x / (2 * (d : ℝ)) := by
  rw [sum_insert (self_not_mem_openNeighbors ω x)]
  have hs : ∑ y ∈ openNeighbors ω x, uniformizedWeight ω x y * f y =
      (∑ y ∈ openNeighbors ω x, f y) / (2 * (d : ℝ)) := by
    rw [sum_div]
    apply sum_congr rfl
    intro y hy
    have hne : y ≠ x := fun heq ↦ self_not_mem_openNeighbors ω x (heq ▸ hy)
    simp [uniformizedWeight, hne, jumpRate, hy]
    ring
  rw [hs]
  simp only [uniformizedWeight, ite_eq_left, randomWalkGenerator, sum_sub_distrib,
    sum_const, nsmul_eq_mul, totalJumpRate]
  ring

end NearCritical
