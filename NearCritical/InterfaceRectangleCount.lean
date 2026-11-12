module

public import NearCritical.InterfaceGluing
public import NearCritical.RectangleBoundary
public import Mathlib.Data.Fintype.BigOperators

/-! Positive-direction interface counts, with the distinguished direction
excluded. These are issued edges, not the unoriented inner vertex boundary. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

lemma rectangle_tip_not_mem_iff {d : ℕ} {lo hi x : Vertex d}
    (hx : x ∈ latticeRectangle lo hi) (j : Fin d) :
    bondTip (x,j) ∉ latticeRectangle lo hi ↔ x j = hi j := by
  constructor
  · intro hn
    by_contra he
    apply hn
    apply mem_latticeRectangle.mpr
    intro k
    have hk := mem_latticeRectangle.mp hx k
    by_cases h : k = j
    · subst k
      simp only [bondTip, Function.update_self]
      omega
    · simpa [bondTip, h] using hk
  · intro he hm
    have hh := (mem_latticeRectangle.mp hm j).2
    simp only [bondTip, Function.update_self] at hh
    omega

lemma card_rectangle_upper_face {d : ℕ} (lo hi : Vertex d)
    (hv : ∀ j, lo j ≤ hi j) (j : Fin d) :
    ((latticeRectangle lo hi).filter (fun x => x j = hi j)).card =
      ∏ k ∈ (univ : Finset (Fin d)).erase j, (Icc (lo k) (hi k)).card := by
  exact Fintype.card_filter_piFinset_eq_of_mem _ _ (mem_Icc.mpr ⟨hv j, le_rfl⟩)

def transverseExitBonds {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    Finset (Bond d) := by
  classical
  exact (issuedBondSet U).filter (fun e => e.2 ≠ i ∧ bondTip e ∉ U)

/-- A patch constant in the distinguished direction can only jump across
transverse edges exiting its base tile. -/
theorem interfaceBonds_subset_transverseExitBonds {d : ℕ} {I : Type*}
    [DecidableEq I] (U : Finset (Vertex d)) (owner : Vertex d → I)
    (j : I) (i : Fin d) (ho : ∀ x ∈ U, owner x = j)
    (hi : ∀ x ∈ U, owner (bondTip (x,i)) = owner x) :
    interfaceBonds U owner ⊆ transverseExitBonds U i := by
  classical
  intro e he
  obtain ⟨he, hc⟩ := mem_filter.mp he
  have hx := (mem_product.mp he).1
  apply mem_filter.mpr
  refine ⟨he, ?_, ?_⟩
  · intro hei
    subst hei
    exact hc (hi e.1 hx)
  · intro ht
    exact hc ((ho _ ht).trans (ho _ hx).symm)

theorem card_transverseExitBonds_rectangle {d : ℕ} (lo hi : Vertex d)
    (i : Fin d) :
    (transverseExitBonds (latticeRectangle lo hi) i).card =
      ∑ j ∈ (univ : Finset (Fin d)).erase i,
        ((latticeRectangle lo hi).filter (fun x => x j = hi j)).card := by
  classical
  unfold transverseExitBonds issuedBondSet
  rw [card_filter, product_eq_sprod, sum_product, sum_comm]
  calc
    _ = ∑ j : Fin d, if j ≠ i then
        ((latticeRectangle lo hi).filter (fun x => x j = hi j)).card else 0 := by
      apply sum_congr rfl
      intro j _
      by_cases hji : j = i
      · simp [hji]
      · simp only [hji, ne_eq, not_false_eq_true, true_and, ↓reduceIte]
        rw [card_filter]
        apply sum_congr rfl
        intro x hx
        simp only [rectangle_tip_not_mem_iff hx j]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext j
      simp [ne_comm]

/-- Explicit face products control the number of interface edges in an
arbitrary translated rectangle. -/
theorem card_interfaceBonds_rectangle_le {d : ℕ} {I : Type*} [DecidableEq I]
    (lo hi : Vertex d) (hv : ∀ k, lo k ≤ hi k)
    (owner : Vertex d → I) (j : I) (i : Fin d)
    (ho : ∀ x ∈ latticeRectangle lo hi, owner x = j)
    (hiowner : ∀ x ∈ latticeRectangle lo hi,
      owner (bondTip (x,i)) = owner x) :
    (interfaceBonds (latticeRectangle lo hi) owner).card ≤
      ∑ k ∈ (univ : Finset (Fin d)).erase i,
        ∏ l ∈ (univ : Finset (Fin d)).erase k, (Icc (lo l) (hi l)).card := by
  calc
    _ ≤ (transverseExitBonds (latticeRectangle lo hi) i).card :=
      card_le_card (interfaceBonds_subset_transverseExitBonds _ owner j i ho hiowner)
    _ = _ := by
      rw [card_transverseExitBonds_rectangle]
      apply sum_congr rfl
      intro k _
      exact card_rectangle_upper_face lo hi hv k

/-- The explicit face count has the volume/width scaling in the paper.
Multiplying by the width avoids any division or positive-dimension side case. -/
theorem card_interfaceBonds_rectangle_mul_width_le {d : ℕ} {I : Type*}
    [DecidableEq I] (lo hi : Vertex d) (hv : ∀ k, lo k ≤ hi k)
    (owner : Vertex d → I) (j : I) (i : Fin d) (L : ℕ)
    (hwidth : ∀ k, k ≠ i → (Icc (lo k) (hi k)).card = L)
    (ho : ∀ x ∈ latticeRectangle lo hi, owner x = j)
    (hiowner : ∀ x ∈ latticeRectangle lo hi,
      owner (bondTip (x,i)) = owner x) :
    (interfaceBonds (latticeRectangle lo hi) owner).card * L ≤
      (d-1) * (latticeRectangle lo hi).card := by
  classical
  calc
    _ ≤ (∑ k ∈ (univ : Finset (Fin d)).erase i,
        ∏ l ∈ (univ : Finset (Fin d)).erase k, (Icc (lo l) (hi l)).card) * L :=
      Nat.mul_le_mul_right L (card_interfaceBonds_rectangle_le lo hi hv owner j i ho hiowner)
    _ = ∑ _k ∈ (univ : Finset (Fin d)).erase i, (latticeRectangle lo hi).card := by
      rw [sum_mul]
      apply sum_congr rfl
      intro k hk
      rw [← hwidth k (mem_erase.mp hk).1, mul_comm,
        mul_prod_erase univ (fun l : Fin d => (Icc (lo l) (hi l)).card) (mem_univ k)]
      exact (Fintype.card_piFinset _).symm
    _ = _ := by simp

end NearCritical
