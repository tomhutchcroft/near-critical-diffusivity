module

public import NearCritical.SlabUpperThreshold

/-! Slab geometry for source prop.slab.upper: every vertex of the literal slab
`ℤ^k × {0,…,n}^{d-k}` is joined to the origin inside the slab in the all-open
configuration. This discharges the connectivity hypothesis of
`restrictedCriticalPoint_le_of_someInfinite` for `slabVertices`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

lemma slabVertices_update_mem {d k n : ℕ} {y : Vertex d} (hy : y ∈ slabVertices d k n)
    (i : Fin d) (t : ℤ) (ht : k ≤ i.val → 0 ≤ t ∧ t ≤ (n : ℤ)) :
    Function.update y i t ∈ slabVertices d k n := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    simpa using ht hj
  · simpa [Function.update_apply, hji] using hy j hj

/-- One positive coordinate step is an all-open restricted edge. -/
lemma allOpen_restricted_adj_succ {d : ℕ} {S : Set (Vertex d)} {v : Vertex d} (i : Fin d)
    (hv : v ∈ S) (hw : Function.update v i (v i + 1) ∈ S) :
    (restrictedGraph (fun _ ↦ true) S).Adj v (Function.update v i (v i + 1)) :=
  ⟨⟨(v, i), rfl, Or.inl ⟨rfl, rfl⟩⟩, hv, hw⟩

/-- Moving one coordinate from `0` to any admissible value stays in the slab. -/
lemma slab_reachable_update {d k n : ℕ} {y : Vertex d} (hy : y ∈ slabVertices d k n)
    (i : Fin d) (hyi : y i = 0) (t : ℤ) (ht : Function.update y i t ∈ slabVertices d k n) :
    (restrictedGraph (fun _ ↦ true) (slabVertices d k n)).Reachable y
      (Function.update y i t) := by
  revert ht
  refine Int.induction_on t ?_ ?_ ?_
  · intro _
    have h0 : Function.update y i 0 = y := by
      rw [← hyi]
      exact Function.update_eq_self i y
    rw [h0]
    try exact SimpleGraph.Reachable.refl y
  · intro m ih ht'
    have hmem : Function.update y i (m : ℤ) ∈ slabVertices d k n := by
      apply slabVertices_update_mem hy i
      intro hk
      have h := ht' i hk
      simp only [Function.update_self] at h
      constructor <;> omega
    have hv : Function.update (Function.update y i (m : ℤ)) i
        (Function.update y i (m : ℤ) i + 1) = Function.update y i ((m : ℤ) + 1) := by
      simp
    have hw : Function.update (Function.update y i (m : ℤ)) i
        (Function.update y i (m : ℤ) i + 1) ∈ slabVertices d k n := by
      rw [hv]
      exact ht'
    have hadj := allOpen_restricted_adj_succ i hmem hw
    rw [hv] at hadj
    exact (ih hmem).trans hadj.reachable
  · intro m ih ht'
    have hmem : Function.update y i (-(m : ℤ)) ∈ slabVertices d k n := by
      apply slabVertices_update_mem hy i
      intro hk
      have h := ht' i hk
      simp only [Function.update_self] at h
      constructor <;> omega
    have hv : Function.update (Function.update y i (-(m : ℤ) - 1)) i
        (Function.update y i (-(m : ℤ) - 1) i + 1) = Function.update y i (-(m : ℤ)) := by
      simp
    have hw : Function.update (Function.update y i (-(m : ℤ) - 1)) i
        (Function.update y i (-(m : ℤ) - 1) i + 1) ∈ slabVertices d k n := by
      rw [hv]
      exact hmem
    have hadj := allOpen_restricted_adj_succ i ht' hw
    rw [hv] at hadj
    exact (ih hmem).trans hadj.symm.reachable

/-- Every slab vertex is joined to the origin inside the slab when all bonds are open. -/
theorem slabVertices_allOpen_reachable {d k n : ℕ} {x : Vertex d}
    (hx : x ∈ slabVertices d k n) :
    (restrictedGraph (fun _ ↦ true) (slabVertices d k n)).Reachable 0 x := by
  have hzS : ∀ s : Finset (Fin d),
      (fun j ↦ if j ∈ s then x j else 0) ∈ slabVertices d k n := by
    intro s j hj
    by_cases h : j ∈ s
    · simpa [h] using hx j hj
    · simp [h]
  have key : ∀ s : Finset (Fin d),
      (restrictedGraph (fun _ ↦ true) (slabVertices d k n)).Reachable 0
        (fun j ↦ if j ∈ s then x j else 0) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h0 : (fun j : Fin d ↦ if j ∈ (∅ : Finset (Fin d)) then x j else (0 : ℤ)) = 0 := by
        funext j
        simp
      rw [h0]
      try exact SimpleGraph.Reachable.refl _
    · intro i s hi ih
      have hz : (fun j ↦ if j ∈ insert i s then x j else 0) =
          Function.update (fun j ↦ if j ∈ s then x j else 0) i (x i) := by
        funext j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [Function.update_apply, hji]
      have h := ih.trans (slab_reachable_update (hzS s) i (by simp [hi]) (x i)
        (slabVertices_update_mem (hzS s) i (x i) (fun hk ↦ hx i hk)))
      rw [← hz] at h
      exact h
  simpa using key Finset.univ

/-- prop.slab.upper threshold step on the literal slab: positive probability of an
infinite restricted cluster anywhere in the slab at `p > 0` bounds the actual slab
critical point by `p`. -/
theorem slab_restrictedCriticalPoint_le_of_someInfinite (d k n : ℕ) (p : unitInterval)
    (hp : 0 < (p : ℝ))
    (hpos : percolation d p (restrictedSomeInfiniteEvent (slabVertices d k n)) ≠ 0) :
    restrictedCriticalPoint d (slabVertices d k n) ≤ p :=
  restrictedCriticalPoint_le_of_someInfinite _ p hp
    (fun _ hx ↦ slabVertices_allOpen_reachable hx) hpos

end NearCritical
