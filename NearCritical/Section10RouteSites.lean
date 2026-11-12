module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-! Site sets of the Section10 coarse routes. At level j the source route visits
X_(j-1) and X_j; at zero these coincide. Duplicate sites are removed literally. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
variable {A : Type*}

def routeLevelSites (X : ℕ → A) (j : ℕ) : Finset (ℕ × A) :=
  {(j,X j),(j,X (j-1))}

def routeSites (M : ℕ) (X : ℕ → A) : Finset (ℕ × A) :=
  (Finset.range M).biUnion (routeLevelSites X)

/-- Exact source site membership, including the level-zero convention. -/
theorem mem_routeSites (M : ℕ) (X : ℕ → A) (j : ℕ) (y : A) :
    (j,y) ∈ routeSites M X ↔ j < M ∧ (y = X j ∨ y = X (j-1)) := by
  simp only [routeSites,routeLevelSites,Finset.mem_biUnion,Finset.mem_range,
    Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  aesop

/-- Every site with first coordinate j belongs to its two explicit slots. -/
theorem route_level_fiber_subset (M : ℕ) (X : ℕ → A) (j : ℕ) :
    (routeSites M X).filter (fun z => z.1 = j) ⊆ routeLevelSites X j := by
  intro z hz
  rcases z with ⟨k,y⟩
  have hk : k = j := (Finset.mem_filter.mp hz).2
  subst k
  obtain ⟨_,hy⟩ := (mem_routeSites M X j y).mp (Finset.mem_filter.mp hz).1
  rcases hy with hy | hy <;> simp [routeLevelSites,hy]

/-- The at-most-two-sites property is a consequence of the route definition. -/
theorem route_level_fiber_card_le_two (M : ℕ) (X : ℕ → A) (j : ℕ) :
    ((routeSites M X).filter (fun z => z.1 = j)).card ≤ 2 := by
  calc
    _ ≤ (routeLevelSites X j).card := Finset.card_le_card (route_level_fiber_subset M X j)
    _ ≤ 2 := by
      exact (Finset.card_insert_le _ _).trans (by simp)

/-- Literal common-level count N for the source route site sets. -/
def commonRouteLevels (M : ℕ) (X Y : ℕ → A) : Finset ℕ :=
  ((routeSites M X) ∩ (routeSites M Y)).image Prod.fst

/-- The deterministic common-site conclusion of lem.nw.EIT, with N computed
from the actual two route site sets rather than an assumed intersection budget. -/
theorem common_route_sites_card_le_two_levels (M : ℕ) (X Y : ℕ → A) :
    ((routeSites M X) ∩ (routeSites M Y)).card ≤ 2*(commonRouteLevels M X Y).card := by
  rw [Finset.card_eq_sum_card_image Prod.fst]
  calc
    _ ≤ ∑ j ∈ commonRouteLevels M X Y, 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hs : (((routeSites M X) ∩ (routeSites M Y)).filter (fun z => z.1 = j)) ⊆
          (routeSites M X).filter (fun z => z.1 = j) := by
        intro z hz
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_inter.mp (Finset.mem_filter.mp hz).1).1,(Finset.mem_filter.mp hz).2⟩
      exact (Finset.card_le_card hs).trans (route_level_fiber_card_le_two M X j)
    _ = _ := by simp [mul_comm]

end NearCritical.Section10
