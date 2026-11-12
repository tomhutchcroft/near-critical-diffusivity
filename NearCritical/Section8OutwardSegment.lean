module
public import NearCritical.Section9Pivotal

/-! Actual axial segment geometry for the unique-extension surgery. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- The r+1 lattice vertices on the positive axial segment starting at x. -/
def section8OutwardSegment {d : ℕ} (x : Vertex d) (i : Fin d) (r : ℕ) : Finset (Vertex d) :=
  (Finset.range (r+1)).image fun (k : ℕ) => Function.update x i (x i+(k : ℤ))

/-- Positive axial shifts are distinct, so the segment has exactly r+1 vertices. -/
theorem section8_outward_segment_card {d : ℕ} (x : Vertex d) (i : Fin d) (r : ℕ) :
    (section8OutwardSegment x i r).card = r+1 := by
  have hinj : Function.Injective (fun k : ℕ => Function.update x i (x i+(k : ℤ))) := by
    intro a b hab
    have hi := congrFun hab i
    simp only [Function.update_self] at hi
    omega
  rw [section8OutwardSegment,Finset.card_image_of_injective _ hinj,Finset.card_range]

/-- Membership records the actual integer axial displacement; useful when
checking containment in a source tube or separation from a target. -/
theorem section8_mem_outward_segment {d : ℕ} (x y : Vertex d) (i : Fin d) (r : ℕ) :
    y ∈ section8OutwardSegment x i r ↔
      ∃ k : ℕ, k ≤ r ∧ y = Function.update x i (x i+(k : ℤ)) := by
  constructor
  · intro hy
    obtain ⟨k,hk,hky⟩ := Finset.mem_image.mp hy
    exact ⟨k,by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk,hky.symm⟩
  · rintro ⟨k,hk,rfl⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),rfl⟩

/-- A wall Q lying at or behind x leaves every positive segment edge
unexplored. Thus the actual static deleted-I graph connects x to every segment
vertex. Any forbidden set W⊆Q meets the segment only at x. -/
theorem section8_outward_segment_structural_guards {d : ℕ}
    (x : Vertex d) (i : Fin d) (r : ℕ) (Q F W : Finset (Vertex d))
    (hwall : ∀ y ∈ Q, y i ≤ x i) (hW : W ⊆ Q) :
    let I := section8OutwardSegment x i r
    x ∈ I ∧ Function.update x i (x i+(r : ℤ)) ∈ I ∧
      (∀ u ∈ I, (sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F).Reachable x u) ∧
      (∀ y ∈ I, y ∈ W → y = x) := by
  intro I
  let f : ℕ → Vertex d := fun k => Function.update x i (x i+(k : ℤ))
  have hf0 : f 0 = x := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [f]
    · simp [f,hj]
  have hmem (k : ℕ) (hk : k ≤ r) : f k ∈ I :=
    Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),rfl⟩
  have htip (k : ℕ) : bondTip (f k,i) = f (k+1) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [f,bondTip,Function.update_self,Nat.cast_add,Nat.cast_one]
      omega
    · simp [f,bondTip,hj]
  have hnextNotQ (k : ℕ) : f (k+1) ∉ Q := by
    intro hnext
    have hw := hwall _ hnext
    simp only [f,Function.update_self,Nat.cast_add,Nat.cast_one] at hw
    have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    omega
  have hstep (k : ℕ) (hk : k+1 ≤ r) :
      (sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F).Adj (f k) (f (k+1)) := by
    refine ⟨⟨(f k,i),rfl,Or.inl ⟨rfl,(htip k).symm⟩⟩,
      hmem k (by omega),hmem (k+1) hk,?_⟩
    intro he
    exact hnextNotQ k ((pair_mem_exploredEdgeSet (Q : Set (Vertex d))
      (F : Set (Vertex d)) (f k) (f (k+1))).mp he).2.1
  have hreach : ∀ k : ℕ, k ≤ r →
      (sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F).Reachable x (f k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hf0]
    | succ k ih =>
      intro hk
      exact (ih (by omega)).trans (hstep k (by omega)).reachable
  refine ⟨hf0 ▸ hmem 0 (by omega),hmem r le_rfl,?_,?_⟩
  · intro u hu
    obtain ⟨k,hk,hku⟩ := Finset.mem_image.mp hu
    have hkR : k ≤ r := by have := Finset.mem_range.mp hk; omega
    exact hku ▸ hreach k hkR
  · intro y hy hyW
    obtain ⟨k,hk,hky⟩ := Finset.mem_image.mp hy
    have hw := hwall y (hW hyW)
    rw [← hky] at hw
    simp only [Function.update_self] at hw
    have hk0 : k = 0 := by omega
    rw [hk0] at hky
    exact hky.symm.trans hf0

end NearCritical
