module

public import NearCritical.RectangleBoundary
public import NearCritical.LatticeFaces

/-! Actual rectangle boundary geometry for the good tiles of the mixed
Dirichlet patch. Local two-face membership is a conclusion, not a hypothesis.
No grid, owner, mixture, or conductivity construction is introduced here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset
open scoped Classical

/-- A base point strictly above EVERY lower coordinate face is interior to U+.
Positive neighbors lie in U+; negative neighbors still lie in the base U. -/
theorem rectangle_strict_base_not_boundary {d : ℕ} {lo hi x : Vertex d}
    (hx : x ∈ latticeRectangle lo hi) (hlo : ∀ k, lo k < x k) :
    x ∉ boundarySites (sitesPlus (latticeRectangle lo hi)) := by
  have hpred : ∀ j, bondPredecessor x j ∈ latticeRectangle lo hi := by
    intro j
    apply mem_latticeRectangle.mpr
    intro k
    have hk := mem_latticeRectangle.mp hx k
    by_cases hkj : k = j
    · subst k
      simp only [bondPredecessor, Function.update_self]
      have hl := hlo j
      omega
    · simpa [bondPredecessor, hkj] using hk
  intro hb
  obtain ⟨_, y, hy, ⟨e, _, hends⟩⟩ := Finset.mem_filter.mp hb
  apply hy
  rcases e with ⟨b,j⟩
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact tip_mem_sitesPlus hx j
  · apply base_mem_sitesPlus
    have hp := hpred j
    have heq : bondPredecessor (bondTip (y,j)) j = y := predecessor_bondTip (y,j)
    rw [heq] at hp
    exact hp

/-- At a global boundary point that is interior in every transverse coordinate,
only the two distinguished extreme heights remain possible. -/
theorem rectangle_boundary_distinguished_extremes {d : ℕ} {lo hi x : Vertex d}
    (i : Fin d) (hb : x ∈ boundarySites (sitesPlus (latticeRectangle lo hi)))
    (htrans : ∀ k, k ≠ i → lo k < x k ∧ x k ≤ hi k) :
    x i = lo i ∨ x i = hi i + 1 := by
  by_cases hlow : x i = lo i
  · exact Or.inl hlow
  by_cases hhigh : x i = hi i + 1
  · exact Or.inr hhigh
  have hx : x ∈ sitesPlus (latticeRectangle lo hi) := (Finset.mem_filter.mp hb).1
  have hbounds := sitesPlus_coordinate_bounds (latticeRectangle lo hi) i
    (fun y hy ↦ mem_latticeRectangle.mp hy i) x hx
  have hall : ∀ k, lo k < x k ∧ x k ≤ hi k := by
    intro k
    by_cases hki : k = i
    · subst k
      omega
    · exact htrans k hki
  have hxbase : x ∈ latticeRectangle lo hi :=
    mem_latticeRectangle.mpr (fun k ↦ ⟨(hall k).1.le, (hall k).2⟩)
  exact False.elim (rectangle_strict_base_not_boundary hxbase (fun k ↦ (hall k).1) hb)

/-- Once a local full-boundary point is at a distinguished extremum, its actual
source two-face membership follows from the coordinate bounds on local U+. -/
theorem rectangle_extreme_mem_twoFace {d : ℕ} (lo hi : Vertex d) (i : Fin d)
    (x : DomainVertex (latticeRectangle lo hi))
    (hb : x ∈ fullBoundary (latticeRectangle lo hi))
    (hext : x.val i = lo i ∨ x.val i = hi i + 1) :
    x ∈ twoFaceBoundary (latticeRectangle lo hi) i := by
  have hbounds := sitesPlus_coordinate_bounds (latticeRectangle lo hi) i
    (fun y hy ↦ mem_latticeRectangle.mp hy i)
  rw [twoFaceBoundary_eq_union]
  rcases hext with hlow | hhigh
  · left
    refine ⟨hb, ?_⟩
    intro y hy
    rw [hlow]
    exact (hbounds y hy).1
  · right
    refine ⟨hb, ?_⟩
    intro y hy
    rw [hhigh]
    exact (hbounds y hy).2

/-- GOOD-tile boundary condition: common distinguished low/high, actual support
containment, and global transverse interior imply local SOURCE two-face boundary.
The local full boundary is derived from the outer boundary, not assumed. -/
theorem rectangle_global_boundary_mem_local_twoFace {d : ℕ}
    (globalLo globalHi localLo localHi : Vertex d) (i : Fin d)
    (hlow : localLo i = globalLo i) (hhigh : localHi i = globalHi i)
    (hsupport : sitesPlus (latticeRectangle localLo localHi) ⊆
      sitesPlus (latticeRectangle globalLo globalHi))
    (x : Vertex d) (hx : x ∈ sitesPlus (latticeRectangle localLo localHi))
    (hb : x ∈ boundarySites (sitesPlus (latticeRectangle globalLo globalHi)))
    (htrans : ∀ k, k ≠ i → globalLo k < x k ∧ x k ≤ globalHi k) :
    (⟨x,hx⟩ : DomainVertex (latticeRectangle localLo localHi)) ∈
      twoFaceBoundary (latticeRectangle localLo localHi) i := by
  have hlocal : (⟨x,hx⟩ : DomainVertex (latticeRectangle localLo localHi)) ∈
      fullBoundary (latticeRectangle localLo localHi) := by
    change x ∈ boundarySites (sitesPlus (latticeRectangle localLo localHi))
    exact boundarySites_of_subset hsupport hx hb
  have hext := rectangle_boundary_distinguished_extremes i hb htrans
  apply rectangle_extreme_mem_twoFace localLo localHi i ⟨x,hx⟩ hlocal
  simpa only [hlow,hhigh] using hext

/-- Base-set containment supplies the required support containment by the
already-proved sitesPlus_mono. No grid arithmetic or local face premise. -/
theorem rectangle_global_boundary_mem_local_twoFace_of_subset {d : ℕ}
    (globalLo globalHi localLo localHi : Vertex d) (i : Fin d)
    (hlow : localLo i = globalLo i) (hhigh : localHi i = globalHi i)
    (hsub : latticeRectangle localLo localHi ⊆ latticeRectangle globalLo globalHi)
    (x : Vertex d) (hx : x ∈ sitesPlus (latticeRectangle localLo localHi))
    (hb : x ∈ boundarySites (sitesPlus (latticeRectangle globalLo globalHi)))
    (htrans : ∀ k, k ≠ i → globalLo k < x k ∧ x k ≤ globalHi k) :
    (⟨x,hx⟩ : DomainVertex (latticeRectangle localLo localHi)) ∈
      twoFaceBoundary (latticeRectangle localLo localHi) i :=
  rectangle_global_boundary_mem_local_twoFace globalLo globalHi localLo localHi i
    hlow hhigh (sitesPlus_mono hsub) x hx hb htrans

end NearCritical
