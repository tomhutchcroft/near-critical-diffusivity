module

public import NearCritical.Section10RouteSites
public import NearCritical.Section10DifferenceRestart

/-! Deterministic comparison of common route levels with visits of the
actual difference history. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

/-- The finite set of all differences of two legal route steps.
A zero step is legal, so the set also includes either signed single step. -/
def routeDifferenceTrap (D : ℕ) : Finset (Fin D → ℤ) := by
  classical
  exact Finset.univ.image (differenceStep D)

def routeHistoryPosition {D M : ℕ} (x : Fin D → ℤ)
    (a : Fin M → Option (Fin D)) (j : ℕ) : Fin D → ℤ :=
  x + ∑ i, if i.val < j then lazyCoordinateStep D (a i) else 0

theorem routeHistoryPosition_sub {D M : ℕ} (x y : Fin D → ℤ)
    (a b : Fin M → Option (Fin D)) (j : ℕ) :
    routeHistoryPosition x a j - routeHistoryPosition y b j =
      (x-y) + differenceDisplacement (fun i => (a i,b i)) j := by
  unfold routeHistoryPosition differenceDisplacement
  have he (i : Fin M) :
      (if i.val < j then differenceStep D (a i,b i) else 0) =
        (if i.val < j then lazyCoordinateStep D (a i) else 0) -
          (if i.val < j then lazyCoordinateStep D (b i) else 0) := by
    split_ifs <;> simp [differenceStep]
  simp_rw [he, Finset.sum_sub_distrib]
  abel

theorem routeHistoryPosition_succ {D M j : ℕ} (x : Fin D → ℤ)
    (a : Fin M → Option (Fin D)) (hj : j < M) :
    routeHistoryPosition x a (j+1) =
      routeHistoryPosition x a j + lazyCoordinateStep D (a ⟨j,hj⟩) := by
  classical
  unfold routeHistoryPosition
  rw [add_assoc]
  congr 1
  have he (i : Fin M) :
      (if i.val < j+1 then lazyCoordinateStep D (a i) else 0) =
      (if i.val < j then lazyCoordinateStep D (a i) else 0) +
        (if i = ⟨j,hj⟩ then lazyCoordinateStep D (a i) else 0) := by
    by_cases hi : i = ⟨j,hj⟩
    · subst i
      simp
    · have hne : i.val ≠ j := fun hv => hi (Fin.ext hv)
      have hlt : i.val < j+1 ↔ i.val < j := by omega
      simp [hlt,hi]
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem routeHistoryPosition_current_from_slot {D M j : ℕ}
    (x z : Fin D → ℤ) (a : Fin M → Option (Fin D)) (hj : j < M)
    (hz : z = routeHistoryPosition x a j ∨ z = routeHistoryPosition x a (j-1)) :
    ∃ c : Option (Fin D), routeHistoryPosition x a j = z + lazyCoordinateStep D c := by
  rcases hz with h | h
  · exact ⟨none, by simp [h,lazyCoordinateStep]⟩
  · cases j with
    | zero => exact ⟨none, by simpa [lazyCoordinateStep] using h.symm⟩
    | succ j =>
      have hj' : j < M := by omega
      exact ⟨a ⟨j,hj'⟩, by rw [h]; simpa using routeHistoryPosition_succ x a hj'⟩

/-- A common site at level j already forces the current difference at j
into the finite trap. At level zero both slots are the starting site. -/
theorem commonRouteLevel_mem_differenceTrap {D M j : ℕ} (x y : Fin D → ℤ)
    (a b : Fin M → Option (Fin D))
    (hj : j ∈ commonRouteLevels M (routeHistoryPosition x a) (routeHistoryPosition y b)) :
    j < M ∧ (x-y) + differenceDisplacement (fun i => (a i,b i)) j ∈ routeDifferenceTrap D := by
  obtain ⟨⟨k,z⟩,hk,hkj⟩ := Finset.mem_image.mp hj
  change k = j at hkj
  subst k
  letI : DecidableEq (Fin D → ℤ) := fun a b => Classical.propDecidable (a = b)
  obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hk
  clear this
  obtain ⟨hjM,hxz⟩ := (mem_routeSites M (routeHistoryPosition x a) j z).mp hx
  obtain ⟨_,hyz⟩ := (mem_routeSites M (routeHistoryPosition y b) j z).mp hy
  obtain ⟨c,hc⟩ := routeHistoryPosition_current_from_slot x z a hjM hxz
  obtain ⟨d,hd⟩ := routeHistoryPosition_current_from_slot y z b hjM hyz
  refine ⟨hjM,?_⟩
  rw [← routeHistoryPosition_sub x y a b j, hc, hd]
  exact Finset.mem_image.mpr ⟨(c,d), Finset.mem_univ _, by unfold differenceStep; dsimp; abel⟩

/-- The level count is bounded by actual visits to the finite trap.
This comparison charges each common level directly to its own time. -/
theorem commonRouteLevels_card_le_differenceVisits {D M : ℕ} (x y : Fin D → ℤ)
    (a b : Fin M → Option (Fin D)) :
    (commonRouteLevels M (routeHistoryPosition x a) (routeHistoryPosition y b)).card ≤
      ∑ j ∈ Finset.range M,
        if (x-y) + differenceDisplacement (fun i => (a i,b i)) j ∈ routeDifferenceTrap D
        then 1 else 0 := by
  classical
  rw [Finset.sum_boole]
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hM,htrap⟩ := commonRouteLevel_mem_differenceTrap x y a b hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hM,htrap⟩

end NearCritical.Section10
