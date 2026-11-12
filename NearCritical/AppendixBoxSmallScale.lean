module
public import NearCritical.SlabUpperGeometry
public import NearCritical.FiniteSurgeryProbability
public import NearCritical.BulkDomain
public import NearCritical.LatticeDomain
public import NearCritical.ConnectionToSet

/-! Finite-energy lower bound for restricted connections in the actual cube
`Λ_n = centeredBox d n`. With every internal bond of `Λ_n` open, the cube is
connected, so `P[x ↔_{Λ_n} y] ≥ min(p,1-p)^{#internal bonds}`. For the finitely
many scales below the threshold where the main argument of lem.box_twopoint_lower
applies, this gives a positive, scale-bounded constant. The proof adapts the
accepted slab argument `slabVertices_allOpen_reachable`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

lemma centeredBox_update_mem {d n : ℕ} {y : Vertex d} (hy : y ∈ centeredBox d n)
    (i : Fin d) (t : ℤ) (ht : -(n : ℤ) ≤ t ∧ t ≤ (n : ℤ)) :
    Function.update y i t ∈ centeredBox d n := by
  rw [mem_centeredBox] at hy ⊢
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using ht
  · simpa [Function.update_apply, hji] using hy j

/-- Moving one coordinate from `0` to any admissible value stays inside `Λ_n`. -/
lemma centeredBox_reachable_update {d n : ℕ} {y : Vertex d} (hy : y ∈ centeredBox d n)
    (i : Fin d) (hyi : y i = 0) (t : ℤ) (ht : Function.update y i t ∈ centeredBox d n) :
    (restrictedGraph (fun _ ↦ true) ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d))).Reachable
      y (Function.update y i t) := by
  revert ht
  refine Int.induction_on t ?_ ?_ ?_
  · intro _
    have h0 : Function.update y i 0 = y := by
      rw [← hyi]
      exact Function.update_eq_self i y
    rw [h0]
    try exact SimpleGraph.Reachable.refl y
  · intro m ih ht'
    have hti := (mem_centeredBox.mp ht') i
    simp only [Function.update_self] at hti
    have hmem : Function.update y i (m : ℤ) ∈ centeredBox d n :=
      centeredBox_update_mem hy i _ ⟨by omega,by omega⟩
    have hv : Function.update (Function.update y i (m : ℤ)) i
        (Function.update y i (m : ℤ) i + 1) = Function.update y i ((m : ℤ) + 1) := by
      simp
    have hw : Function.update (Function.update y i (m : ℤ)) i
        (Function.update y i (m : ℤ) i + 1) ∈
          ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) := by
      rw [hv]
      exact ht'
    have hadj := allOpen_restricted_adj_succ
      (S := ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d))) i (Finset.mem_coe.mpr hmem) hw
    rw [hv] at hadj
    exact (ih hmem).trans hadj.reachable
  · intro m ih ht'
    have hti := (mem_centeredBox.mp ht') i
    simp only [Function.update_self] at hti
    have hmem : Function.update y i (-(m : ℤ)) ∈ centeredBox d n :=
      centeredBox_update_mem hy i _ ⟨by omega,by omega⟩
    have hv : Function.update (Function.update y i (-(m : ℤ) - 1)) i
        (Function.update y i (-(m : ℤ) - 1) i + 1) = Function.update y i (-(m : ℤ)) := by
      simp
    have hw : Function.update (Function.update y i (-(m : ℤ) - 1)) i
        (Function.update y i (-(m : ℤ) - 1) i + 1) ∈
          ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) := by
      rw [hv]
      exact hmem
    have hadj := allOpen_restricted_adj_succ
      (S := ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d))) i (Finset.mem_coe.mpr ht') hw
    rw [hv] at hadj
    exact (ih hmem).trans hadj.symm.reachable

/-- Every vertex of `Λ_n` is joined to the origin inside `Λ_n` when all bonds are open. -/
theorem centeredBox_allOpen_reachable_zero {d n : ℕ} {x : Vertex d}
    (hx : x ∈ centeredBox d n) :
    (restrictedGraph (fun _ ↦ true) ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d))).Reachable
      0 x := by
  have hxb := mem_centeredBox.mp hx
  have hzS : ∀ s : Finset (Fin d),
      (fun j ↦ if j ∈ s then x j else 0) ∈ centeredBox d n := by
    intro s
    rw [mem_centeredBox]
    intro j
    by_cases h : j ∈ s
    · simpa [h] using hxb j
    · simp [h]
  have key : ∀ s : Finset (Fin d),
      (restrictedGraph (fun _ ↦ true)
        ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d))).Reachable 0
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
      have h := ih.trans (centeredBox_reachable_update (hzS s) i (by simp [hi]) (x i)
        (centeredBox_update_mem (hzS s) i (x i) (hxb i)))
      rw [← hz] at h
      exact h
  simpa using key Finset.univ

/-- Any two vertices of `Λ_n` are connected inside `Λ_n` in the all-open configuration. -/
theorem centeredBox_allOpen_reachable {d n : ℕ} {x y : Vertex d}
    (hx : x ∈ centeredBox d n) (hy : y ∈ centeredBox d n) :
    (restrictedGraph (fun _ ↦ true) ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d))).Reachable
      x y :=
  (centeredBox_allOpen_reachable_zero hx).symm.trans (centeredBox_allOpen_reachable_zero hy)

/-- Finite-energy lower bound for the actual restricted cube connection. -/
theorem centeredBox_connection_lower_allOpen {d : ℕ} (p : unitInterval) (n : ℕ)
    {x y : Vertex d} (hx : x ∈ centeredBox d n) (hy : y ∈ centeredBox d n) :
    (min (p : ℝ) (1-(p : ℝ)))^(internalBondSet (centeredBox d n)).card ≤
      (percolation d p).real
        (connectionToSetEvent ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
  let G := internalBondSet (centeredBox d n)
  let A : Set (G → Bool) := {ξ | ∀ b, ξ b = true}
  have hs := percolation_finite_surgery_probability p G G A Set.univ (by
    intro ω _
    refine ⟨fun b => if b ∈ G then true else ω b,?_,?_⟩
    · intro b hb
      simp [hb]
    · simp only [A,Set.mem_setOf_eq]
      intro b
      simp [Finset.restrict,b.2])
  have huniv : (percolation d p).real
      ((G.restrict : Configuration d → (G → Bool)) ⁻¹' Set.univ) = 1 := by
    rw [Set.preimage_univ]
    exact probReal_univ
  rw [huniv,mul_one] at hs
  refine hs.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro ω hω
  have hω' : ∀ c : G, G.restrict ω c = true := hω
  have hopen : ∀ b ∈ G, ω b = true := fun b hb => hω' ⟨b,hb⟩
  have hle : restrictedGraph (fun _ ↦ true)
        ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) ≤
      restrictedGraph ω ((centeredBox d n : Finset (Vertex d)) : Set (Vertex d)) := by
    rintro u v ⟨⟨e,_,hends⟩,hu,hv⟩
    have heG : e ∈ G := by
      apply (mem_internalBondSet _ e).mpr
      rcases hends with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact ⟨by rw [← h1]; exact hu,by rw [← h2]; exact hv⟩
      · exact ⟨by rw [← h1]; exact hv,by rw [← h2]; exact hu⟩
    exact ⟨⟨e,hopen e heG,hends⟩,hu,hv⟩
  exact ⟨hx,y,Set.mem_singleton y,hy,(centeredBox_allOpen_reachable hx hy).mono hle⟩

end NearCritical
