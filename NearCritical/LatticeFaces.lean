module

public import NearCritical.LatticeDomain
public import Mathlib.Data.Finset.Max

/-! The source's top and bottom faces on U⁺. Their coordinate data are constant,
and both faces are nonempty when U is nonempty. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set

/-- The positive face in `eq.def.TopBottom`. -/
def positiveFace {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) : Set (DomainVertex U) :=
  {x | x ∈ fullBoundary U ∧ ∀ y ∈ sitesPlus U, y i ≤ x.val i}

/-- The negative face in `eq.def.TopBottom`. -/
def negativeFace {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) : Set (DomainVertex U) :=
  {x | x ∈ fullBoundary U ∧ ∀ y ∈ sitesPlus U, x.val i ≤ y i}

lemma twoFaceBoundary_eq_union {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    twoFaceBoundary U i = negativeFace U i ∪ positiveFace U i := by
  ext x
  simp only [twoFaceBoundary, negativeFace, positiveFace, mem_ofPred_eq, mem_union]
  tauto

lemma positiveFace_data_constant {d : ℕ} {U : Finset (Vertex d)} {i : Fin d}
    {x y : DomainVertex U} (hx : x ∈ positiveFace U i) (hy : y ∈ positiveFace U i) :
    coordinateData i x = coordinateData i y := by
  have hxy := hx.2 y.val y.property
  have hyx := hy.2 x.val x.property
  exact congrArg (fun n : ℤ ↦ (n : ℝ)) (le_antisymm hyx hxy)

lemma negativeFace_data_constant {d : ℕ} {U : Finset (Vertex d)} {i : Fin d}
    {x y : DomainVertex U} (hx : x ∈ negativeFace U i) (hy : y ∈ negativeFace U i) :
    coordinateData i x = coordinateData i y := by
  have hxy := hx.2 y.val y.property
  have hyx := hy.2 x.val x.property
  exact congrArg (fun n : ℤ ↦ (n : ℝ)) (le_antisymm hxy hyx)

lemma mem_boundarySites_of_max {d : ℕ} {S : Finset (Vertex d)} (i : Fin d)
    {x : Vertex d} (hx : x ∈ S) (hmax : ∀ y ∈ S, y i ≤ x i) : x ∈ boundarySites S := by
  classical
  apply mem_filter.mpr
  refine ⟨hx, bondTip (x, i), ?_, ?_⟩
  · intro ht
    have h := hmax (bondTip (x, i)) ht
    simp only [bondTip, Function.update_self] at h
    omega
  · exact ⟨(x, i), rfl, Or.inl ⟨rfl, rfl⟩⟩

lemma mem_boundarySites_of_min {d : ℕ} {S : Finset (Vertex d)} (i : Fin d)
    {x : Vertex d} (hx : x ∈ S) (hmin : ∀ y ∈ S, x i ≤ y i) : x ∈ boundarySites S := by
  classical
  let pred : Vertex d := Function.update x i (x i - 1)
  have htip : bondTip (pred, i) = x := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [bondTip, pred]
    · simp [bondTip, pred, Function.update_of_ne hj]
  apply mem_filter.mpr
  refine ⟨hx, pred, ?_, ?_⟩
  · intro hp
    have h := hmin pred hp
    simp only [pred, Function.update_self] at h
    omega
  · exact ⟨(pred, i), rfl, Or.inr ⟨rfl, htip.symm⟩⟩

lemma positiveFace_nonempty {d : ℕ} {U : Finset (Vertex d)} (hU : U.Nonempty) (i : Fin d) :
    (positiveFace U i).Nonempty := by
  classical
  obtain ⟨q, hq⟩ := hU
  have hs : (sitesPlus U).Nonempty := ⟨q, base_mem_sitesPlus hq⟩
  obtain ⟨x, hx, hmax⟩ := (sitesPlus U).exists_max_image (fun y ↦ y i) hs
  exact ⟨⟨x, hx⟩, mem_boundarySites_of_max i hx hmax, hmax⟩

lemma negativeFace_nonempty {d : ℕ} {U : Finset (Vertex d)} (hU : U.Nonempty) (i : Fin d) :
    (negativeFace U i).Nonempty := by
  classical
  obtain ⟨q, hq⟩ := hU
  have hs : (sitesPlus U).Nonempty := ⟨q, base_mem_sitesPlus hq⟩
  obtain ⟨x, hx, hmin⟩ := (sitesPlus U).exists_min_image (fun y ↦ y i) hs
  exact ⟨⟨x, hx⟩, mem_boundarySites_of_min i hx hmin, hmin⟩

lemma face_data_lt {d : ℕ} {U : Finset (Vertex d)} (hU : U.Nonempty) {i : Fin d}
    {x y : DomainVertex U} (hx : x ∈ negativeFace U i) (hy : y ∈ positiveFace U i) :
    coordinateData i x < coordinateData i y := by
  obtain ⟨q, hq⟩ := hU
  have hlo := hx.2 q (base_mem_sitesPlus hq)
  have hhi := hy.2 (bondTip (q, i)) (tip_mem_sitesPlus hq i)
  simp only [bondTip, Function.update_self] at hhi
  have hlt : x.val i < y.val i := by omega
  dsimp only [coordinateData]
  exact_mod_cast hlt

lemma face_data_range {d : ℕ} {U : Finset (Vertex d)} {i : Fin d}
    {x y : DomainVertex U} (hx : x ∈ negativeFace U i) (hy : y ∈ positiveFace U i)
    (z : DomainVertex U) :
    coordinateData i z ∈ Icc (coordinateData i x) (coordinateData i y) := by
  have hlo := hx.2 z.val z.property
  have hhi := hy.2 z.val z.property
  constructor <;> dsimp only [coordinateData]
  · exact_mod_cast hlo
  · exact_mod_cast hhi

end NearCritical
