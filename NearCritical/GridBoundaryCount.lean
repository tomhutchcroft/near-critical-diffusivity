module

public import NearCritical.GridPatchBoundary
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-! Actual boundary-label fraction for the new mixed boundary-layer patch.
Bad labels are the existing first/last transverse coordinate flag. The proof
counts finite coordinate slices and a union; no boundary fraction is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset
open scoped Classical

/-- Fixing one admissible grid coordinate removes exactly its interval factor
from the actual finite product. This remains valid if another coordinate is empty. -/
lemma grid_coordinate_slice_card_mul {d : ℕ} (N : Vertex d) (k : Fin d) (a : ℤ)
    (ha : 0 ≤ a ∧ a ≤ N k - 1) :
    ((latticeRectangle 0 (fun j ↦ N j - 1)).filter (fun z ↦ z k = a)).card *
        (N k).toNat = (latticeRectangle 0 (fun j ↦ N j - 1)).card := by
  let t : Fin d → Finset ℤ := fun j ↦ Icc 0 (N j - 1)
  have hmem : a ∈ t k := Finset.mem_Icc.mpr ha
  have hcard : (t k).card = (N k).toNat := by
    simp only [t, Int.card_Icc, sub_zero, sub_add_cancel]
  change ((Fintype.piFinset t).filter (fun z ↦ z k = a)).card * (N k).toNat =
    (Fintype.piFinset t).card
  rw [Fintype.card_filter_piFinset_eq_of_mem t k hmem, Fintype.card_piFinset, ← hcard]
  exact Finset.prod_erase_mul univ (fun j ↦ (t j).card) (mem_univ k)

/-- The multiplied boundary count avoids all negative-exponent/dimension cases.
The inactive distinguished count may be arbitrary; N_i=1 is needed only below
for the positive-denominator fraction. First/last slices may overlap. -/
theorem gridBoundaryIndex_card_mul_le {d : ℕ} (i : Fin d) (N : Vertex d)
    (n : ℕ) (hn : 0 < n) (hN : ∀ k, k ≠ i → N k = (n : ℤ)) :
    ((latticeRectangle 0 (fun k ↦ N k - 1)).filter (gridBoundaryIndex i N)).card * n ≤
      2 * (d-1) * (latticeRectangle 0 (fun k ↦ N k - 1)).card := by
  let s := latticeRectangle 0 (fun k ↦ N k - 1)
  let J : Finset (Fin d) := univ.erase i
  let face := fun k : Fin d ↦ s.filter (fun z ↦ z k = 0) ∪
    s.filter (fun z ↦ z k = N k - 1)
  have hunion : s.filter (gridBoundaryIndex i N) = J.biUnion face := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzs, k, hki, hside⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_biUnion.mpr
      refine ⟨k, Finset.mem_erase.mpr ⟨hki, mem_univ _⟩, ?_⟩
      rcases hside with hzero | htop
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hzs,hzero⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hzs,htop⟩))
    · intro hz
      obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hz
      have hki := (Finset.mem_erase.mp hk).1
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨hzs,hzero⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzs,k,hki,Or.inl hzero⟩
      · obtain ⟨hzs,htop⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hzs,k,hki,Or.inr htop⟩
  have hbad : (s.filter (gridBoundaryIndex i N)).card ≤
      ∑ k ∈ J, ((s.filter (fun z ↦ z k = 0)).card +
        (s.filter (fun z ↦ z k = N k - 1)).card) := by
    rw [hunion]
    exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum
      (fun k _ ↦ Finset.card_union_le _ _))
  have hnZ : 0 < (n : ℤ) := by exact_mod_cast hn
  have hslice : ∀ k ∈ J,
      (s.filter (fun z ↦ z k = 0)).card * n = s.card ∧
      (s.filter (fun z ↦ z k = N k - 1)).card * n = s.card := by
    intro k hk
    have hkN := hN k (mem_erase.mp hk).1
    have hz : 0 ≤ N k - 1 := by omega
    constructor
    · have hh := grid_coordinate_slice_card_mul N k 0 ⟨le_rfl, hz⟩
      simpa only [hkN, Int.toNat_natCast] using hh
    · have hh := grid_coordinate_slice_card_mul N k (N k - 1) ⟨hz, le_rfl⟩
      simpa only [hkN, Int.toNat_natCast] using hh
  have hJ : J.card = d-1 := by
    dsimp only [J]
    rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ (∑ k ∈ J, ((s.filter (fun z ↦ z k = 0)).card +
        (s.filter (fun z ↦ z k = N k - 1)).card)) * n := Nat.mul_le_mul_right n hbad
    _ = ∑ k ∈ J, ((s.filter (fun z ↦ z k = 0)).card * n +
        (s.filter (fun z ↦ z k = N k - 1)).card * n) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact Nat.add_mul _ _ _
    _ = ∑ _k ∈ J, (s.card + s.card) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [(hslice k hk).1, (hslice k hk).2]
    _ = 2 * (d-1) * s.card := by
      simp only [Finset.sum_const, smul_eq_mul, hJ]
      ring

/-- Literal real fraction of actual bad grid labels. The denominator is proved
positive from N_i=1 and n>=1, rather than supplied as a fraction assumption. -/
theorem gridBoundaryIndex_fraction_le {d : ℕ} (i : Fin d) (N : Vertex d)
    (n : ℕ) (hn : 0 < n) (hNi : N i = 1) (hN : ∀ k, k ≠ i → N k = (n : ℤ)) :
    (((latticeRectangle 0 (fun k ↦ N k - 1)).filter (gridBoundaryIndex i N)).card : ℝ) /
        ((latticeRectangle 0 (fun k ↦ N k - 1)).card : ℝ) ≤
      2 * ((d-1 : ℕ) : ℝ) / (n : ℝ) := by
  have hposN : ∀ k, 0 < N k := by
    intro k
    by_cases hki : k = i
    · subst k; rw [hNi]; norm_num
    · rw [hN k hki]; exact_mod_cast hn
  have hs : (latticeRectangle 0 (fun k ↦ N k - 1)).Nonempty := by
    refine ⟨0, mem_latticeRectangle.mpr ?_⟩
    intro k
    have hk := hposN k
    constructor <;> simp only [Pi.zero_apply] <;> omega
  have hcard : 0 < ((latticeRectangle 0 (fun k ↦ N k - 1)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (div_le_div_iff₀ hcard hnR).mpr
  exact_mod_cast gridBoundaryIndex_card_mul_le i N n hn hN

/-- Dimension one has no transverse index, so the actual bad-label set is empty.
This needs no grid-count assumptions and avoids any d-2 exponent convention. -/
theorem gridBoundaryIndex_one_dim_empty (i : Fin 1) (N : Vertex 1) :
    (latticeRectangle 0 (fun k ↦ N k - 1)).filter (gridBoundaryIndex i N) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro z _
  rintro ⟨k, hki, _⟩
  exact hki (Subsingleton.elim k i)

end NearCritical
