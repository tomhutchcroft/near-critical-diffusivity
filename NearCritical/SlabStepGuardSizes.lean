module

public import NearCritical.SlabStepGuardRegularity

/-! The size bounds for the slab offspring estimate, obtained by summing
the bounds on the disjoint regular patches of the endpoint clusters. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical BigOperators

/-- Per-cluster patch bounds in parent coordinates. -/
structure SlabPatchBounds {d : ℕ} (typ : TypicalParameters) (n k : ℕ) (i : Fin d)
    (D : SlabStepBoundaryData d) : Prop where
  parentCard : D.parentNest.card = k
  targetCount : typ.countLower * (2 * (n : ℝ)) ^ (d - 6) ≤ (D.childCandidates.card : ℝ)
  sourceDisjoint : Set.PairwiseDisjoint (D.parentNest : Set (Finset (Vertex d))) (D.source typ n i)
  targetDisjoint : Set.PairwiseDisjoint (D.childCandidates : Set (Finset (Vertex d))) (D.target typ n i)
  sourceLower : ∀ C ∈ D.parentNest,
    typ.boundaryLower * (2 * (n : ℝ)) ^ 2 ≤ ((D.source typ n i C).card : ℝ)
  sourceUpper : ∀ C ∈ D.parentNest,
    ((D.source typ n i C).card : ℝ) ≤ typ.boundaryUpper * (2 * (n : ℝ)) ^ 2
  targetLower : ∀ C ∈ D.childCandidates,
    typ.boundaryLower * (2 * (n : ℝ)) ^ 2 ≤ ((D.target typ n i C).card : ℝ)
  targetUpper : ∀ C ∈ D.childCandidates,
    ((D.target typ n i C).card : ℝ) ≤ 2 * (typ.boundaryUpper * (2 * (n : ℝ)) ^ 2)

theorem SlabPatchBounds.size_bounds {d : ℕ} (hd : 6 ≤ d) (typ : TypicalParameters)
    (n k : ℕ) (i : Fin d) (D : SlabStepBoundaryData d) (h : SlabPatchBounds typ n k i D)
    (hb : 0 ≤ typ.boundaryLower) (hc : 0 ≤ typ.countLower) {δSize CB KA : ℝ}
    (hKA : 4 * (k : ℝ) * typ.boundaryUpper ≤ KA) (hCB : 8 * typ.boundaryUpper ≤ CB)
    (hS : δSize ≤ 4 * (k : ℝ) * typ.boundaryLower)
    (hT : δSize ≤ 4 * typ.countLower * typ.boundaryLower * (2 * (n : ℝ)) ^ (d - 6))
    (hST : δSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2) :
    let S := sprinklingTargetBoundary D.parentNest (D.source typ n i)
    let T := D.childCandidates.biUnion (D.target typ n i)
    (S.card : ℝ) ≤ KA * (n : ℝ)^2 ∧
      (∀ C ∈ D.childCandidates, ((D.target typ n i C).card : ℝ) ≤ CB * (n : ℝ)^2) ∧
      δSize * (n : ℝ)^2 ≤ (S.card : ℝ) ∧ δSize * (n : ℝ)^2 ≤ (T.card : ℝ) ∧
      δSize * (n : ℝ)^((d : ℝ) - 2) ≤ (S.card : ℝ) * (T.card : ℝ) := by
  intro S T
  let t : ℝ := n
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hsq : 0 ≤ t ^ 2 := sq_nonneg t
  have hsl : (k : ℝ) * (typ.boundaryLower * (2*t)^2) ≤ (S.card : ℝ) := by
    have he : S.card = ∑ C ∈ D.parentNest, (D.source typ n i C).card :=
      Finset.card_biUnion h.sourceDisjoint
    rw [he, Nat.cast_sum, ← h.parentCard, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum h.sourceLower
  have hsu : (S.card : ℝ) ≤ (k : ℝ) * (typ.boundaryUpper * (2*t)^2) := by
    have he : S.card = ∑ C ∈ D.parentNest, (D.source typ n i C).card :=
      Finset.card_biUnion h.sourceDisjoint
    rw [he, Nat.cast_sum, ← h.parentCard, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum h.sourceUpper
  have htl : (typ.countLower * (2*t)^(d-6)) * (typ.boundaryLower * (2*t)^2) ≤ (T.card : ℝ) := by
    have he : T.card = ∑ C ∈ D.childCandidates, (D.target typ n i C).card :=
      Finset.card_biUnion h.targetDisjoint
    rw [he, Nat.cast_sum]
    calc
      _ ≤ (D.childCandidates.card : ℝ) * (typ.boundaryLower * (2*t)^2) :=
        mul_le_mul_of_nonneg_right h.targetCount (by positivity)
      _ = ∑ _C ∈ D.childCandidates, typ.boundaryLower * (2*t)^2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum h.targetLower
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine hsu.trans ?_
    calc
      (k : ℝ) * (typ.boundaryUpper * (2*t)^2) = (4 * k * typ.boundaryUpper) * t^2 := by ring
      _ ≤ KA * t^2 := mul_le_mul_of_nonneg_right hKA hsq
  · intro C hC
    refine (h.targetUpper C hC).trans ?_
    calc
      2 * (typ.boundaryUpper * (2*t)^2) = (8 * typ.boundaryUpper) * t^2 := by ring
      _ ≤ CB * t^2 := mul_le_mul_of_nonneg_right hCB hsq
  · refine (mul_le_mul_of_nonneg_right hS hsq).trans ?_
    convert hsl using 1 <;> ring
  · refine (mul_le_mul_of_nonneg_right hT hsq).trans ?_
    convert htl using 1 <;> ring
  · have ha : (4 * (k : ℝ) * typ.boundaryLower) * t^2 ≤ (S.card : ℝ) := by
      convert hsl using 1 <;> ring
    have htpow : t^(d-6) ≤ (2*t)^(d-6) := pow_le_pow_left₀ ht (by linarith) _
    have hb' : (typ.countLower * t^(d-6)) * (4 * typ.boundaryLower * t^2) ≤ (T.card : ℝ) := by
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htpow hc) (by positivity)).trans ?_
      convert htl using 1 <;> ring
    have hprod := mul_le_mul ha hb' (by positivity) (by positivity : (0 : ℝ) ≤ S.card)
    have hexp : (d : ℝ) - 2 = ((d-2 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hexp, Real.rpow_natCast]
    change δSize * t^(d-2) ≤ _
    refine (mul_le_mul_of_nonneg_right hST (pow_nonneg ht _)).trans ?_
    have he : (d-2) = (d-6) + 4 := by omega
    rw [he, pow_add]
    convert hprod using 1 <;> ring

/-- Assemble the offspring shape from its realized reveal and the bounds on
the regular patches. -/
theorem slabOffspringShape_of_patches {d : ℕ} (hd : 6 ≤ d) (typ : TypicalParameters)
    {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin d) (D : SlabStepBoundaryData d)
    (h : SlabPatchBounds typ n k i D) (hb : 0 ≤ typ.boundaryLower) (hc : 0 ≤ typ.countLower)
    {δ δSize CB KA : ℝ} (hδ : typ.regularTolerance ≤ δ)
    (hKA : 4 * (k : ℝ) * typ.boundaryUpper ≤ KA) (hCB : 8 * typ.boundaryUpper ≤ CB)
    (hS : δSize ≤ 4 * (k : ℝ) * typ.boundaryLower)
    (hT : δSize ≤ 4 * typ.countLower * typ.boundaryLower * (2 * (n : ℝ)) ^ (d - 6))
    (hST : δSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2)
    (hreal : percolation d (criticalPoint d) (section9RevealEvent
      (section9FiniteEndCube i n 0) (typicalHeart n 0 typ.heartRatio)
      (section9FiniteEndCube i n (2*(n : ℝ))) (typicalHeart n (farCenter n 0 i) typ.heartRatio)
      D.parentHeart D.childHeart) ≠ 0) :
    SlabOffspringShape typ n k i D typ.regularRadius δ δSize CB KA := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := slab_step_patch_conditions typ hn i D hδ
  obtain ⟨ha,hc',hb',hd',he⟩ := h.size_bounds hd typ n k i D hb hc hKA hCB hS hT hST
  exact ⟨h.parentCard,hreal,h₁,h₂,h₃,h₄,h.targetDisjoint,ha,hc',hb',hd',he⟩

end NearCritical
