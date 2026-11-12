module

public import NearCritical.NetworkMaximumPrinciple
public import Mathlib.Algebra.Group.Indicator

/-! A nonzero voltage drop on an open edge cannot lie in a component with no
Dirichlet boundary. The proof uses a component-supported energy variation,
not a convention for the value on boundary-free components. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open Set Finset
open scoped Classical
variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

def positiveComponent (a : E → ℝ) (x : V) : Set V :=
  {v | (G.positiveGraph a univ).Reachable x v}

omit [Fintype E] in
lemma positiveComponent_edge_iff {a : E → ℝ} (x : V) (e : E) (he : 0 < a e) :
    G.tail e ∈ G.positiveComponent a x ↔ G.head e ∈ G.positiveComponent a x := by
  by_cases hne : G.tail e = G.head e
  · rw [hne]
  have hadj := G.positiveGraph_adj_of_edge (S := univ) e he hne (Set.mem_univ _) (Set.mem_univ _)
  exact ⟨fun ht ↦ ht.trans hadj.reachable, fun hh ↦ hh.trans hadj.symm.reachable⟩

omit [Fintype E] in
lemma positiveComponent_pairing_term {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (u : V → ℝ) (x : V) (e : E) :
    a e * G.gradient ((G.positiveComponent a x).indicator u) e * G.gradient u e =
      if G.tail e ∈ G.positiveComponent a x then a e * (G.gradient u e) ^ 2 else 0 := by
  classical
  by_cases he : a e = 0
  · simp [he]
  have hpos : 0 < a e := lt_of_le_of_ne (ha e) (Ne.symm he)
  have heq := G.positiveComponent_edge_iff x e hpos
  by_cases ht : G.tail e ∈ G.positiveComponent a x
  · have hh := heq.mp ht
    simp only [gradient, Set.indicator_of_mem ht, Set.indicator_of_mem hh, ite_eq_left ht]
    ring
  · have hh : G.head e ∉ G.positiveComponent a x := fun h ↦ ht (heq.mpr h)
    simp [gradient, ht, hh]

/-- The tail of an open edge with nonzero harmonic voltage drop reaches the
Dirichlet boundary. Degenerate conductances and isolated components are allowed. -/
theorem IsHarmonic.edge_nonzero_reaches_boundary {a : E → ℝ} {boundary : Set V} {u : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (ha : ∀ e, 0 ≤ a e) (e : E)
    (he : 0 < a e) (hgrad : G.gradient u e ≠ 0) :
    ∃ z ∈ boundary, (G.positiveGraph a univ).Reachable (G.tail e) z := by
  classical
  by_contra hn
  let C : Set V := G.positiveComponent a (G.tail e)
  have hC : ∀ z ∈ boundary, z ∉ C := by
    intro z hz hc
    exact hn ⟨z, hz, hc⟩
  have hp : G.pairing a (C.indicator u) u = 0 :=
    hu (C.indicator u) (by intro z hz; exact Set.indicator_of_notMem (hC z hz) u)
  have hsum : (∑ j, if G.tail j ∈ C then a j * (G.gradient u j) ^ 2 else 0) = 0 := by
    unfold pairing at hp
    simpa only [C, G.positiveComponent_pairing_term ha u (G.tail e)] using hp
  have hnterm (j : E) : 0 ≤ (if G.tail j ∈ C then a j * (G.gradient u j) ^ 2 else 0) := by
    split
    · exact mul_nonneg (ha j) (sq_nonneg _)
    · exact le_rfl
  have hz := (sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnterm j)).mp hsum e (Finset.mem_univ e)
  have ht : G.tail e ∈ C := SimpleGraph.Reachable.refl _
  rw [ite_eq_left ht] at hz
  have hsq : (G.gradient u e) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt he)
  exact hgrad (sq_eq_zero_iff.mp hsq)

/-- Both endpoints of the tested open edge reach the boundary, as required by
the two-arm support statement. -/
theorem IsHarmonic.edge_nonzero_both_reach_boundary {a : E → ℝ} {boundary : Set V} {u : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (ha : ∀ e, 0 ≤ a e) (e : E)
    (he : 0 < a e) (hgrad : G.gradient u e ≠ 0) :
    (∃ z ∈ boundary, (G.positiveGraph a univ).Reachable (G.tail e) z) ∧
    (∃ z ∈ boundary, (G.positiveGraph a univ).Reachable (G.head e) z) := by
  obtain ⟨z, hz, htail⟩ := hu.edge_nonzero_reaches_boundary G ha e he hgrad
  have hne : G.tail e ≠ G.head e := by
    intro h
    exact hgrad (by simp [gradient, h])
  have hadj := G.positiveGraph_adj_of_edge (S := univ) e he hne (Set.mem_univ _) (Set.mem_univ _)
  exact ⟨⟨z, hz, htail⟩, ⟨z, hz, hadj.symm.reachable.trans htail⟩⟩

end NearCritical.Network
