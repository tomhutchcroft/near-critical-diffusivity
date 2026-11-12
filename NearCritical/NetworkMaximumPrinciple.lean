module

public import NearCritical.Harmonic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A cut proof of boundary access for sublevel components of finite-network
harmonic potentials. The finite edge set may have zero weights. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open Set Finset
variable {V E : Type*} [Fintype E] (G : NearCritical.Network V E)

/-- The graph of positive-weight edges with both endpoints in S. Loops of the
network are discarded; they never affect energy or cut arguments. -/
def positiveGraph (a : E → ℝ) (S : Set V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ ∃ e, 0 < a e ∧
    ((G.tail e = x ∧ G.head e = y) ∨ (G.tail e = y ∧ G.head e = x))
  symm := ⟨by
    rintro x y ⟨hne, hx, hy, e, he, h | h⟩
    · exact ⟨hne.symm, hy, hx, e, he, Or.inr h⟩
    · exact ⟨hne.symm, hy, hx, e, he, Or.inl h⟩⟩
  loopless := ⟨by rintro x ⟨h, _⟩; exact h rfl⟩

omit [Fintype E] in
lemma positiveGraph_mono (a : E → ℝ) {S T : Set V} (hst : S ⊆ T) :
    G.positiveGraph a S ≤ G.positiveGraph a T := by
  rintro x y ⟨hne, hx, hy, e, he, h⟩
  exact ⟨hne, hst hx, hst hy, e, he, h⟩

omit [Fintype E] in
lemma positiveGraph_adj_of_edge {a : E → ℝ} {S : Set V} (e : E) (he : 0 < a e)
    (hne : G.tail e ≠ G.head e) (ht : G.tail e ∈ S) (hh : G.head e ∈ S) :
    (G.positiveGraph a S).Adj (G.tail e) (G.head e) :=
  ⟨hne, ht, hh, e, he, Or.inl ⟨rfl, rfl⟩⟩

omit [Fintype E] in
lemma positiveGraph_reachable_mem {a : E → ℝ} {S : Set V} {x y : V}
    (hx : x ∈ S) (hxy : (G.positiveGraph a S).Reachable x y) : y ∈ S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact hx
  | tail _ h _ => exact h.2.2.1

/-- Membership in a set closed under adjacency is preserved by connectivity. -/
lemma reachable_preserves_set {H : SimpleGraph V} {C : Set V}
    (hc : ∀ v w, H.Adj v w → v ∈ C → w ∈ C) {x y : V}
    (hx : x ∈ C) (hxy : H.Reachable x y) : y ∈ C := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact hx
  | tail _ h ih => exact hc _ _ h ih

def sublevelComponent (a : E → ℝ) (u : V → ℝ) (x : V) : Set V :=
  {y | (G.positiveGraph a {z | u z ≤ u x}).Reachable x y}

omit [Fintype E] in
lemma mem_sublevelComponent_self (a : E → ℝ) (u : V → ℝ) (x : V) :
    x ∈ G.sublevelComponent a u x := SimpleGraph.Reachable.refl x

omit [Fintype E] in
lemma sublevelComponent_le {a : E → ℝ} {u : V → ℝ} {x y : V}
    (hy : y ∈ G.sublevelComponent a u x) : u y ≤ u x :=
  G.positiveGraph_reachable_mem (S := {z | u z ≤ u x}) (x := x) (y := y) (show u x ≤ u x from le_rfl) hy

omit [Fintype E] in
lemma sublevelComponent_head_out {a : E → ℝ} {u : V → ℝ} {x : V} (e : E)
    (he : 0 < a e) (ht : G.tail e ∈ G.sublevelComponent a u x)
    (hh : G.head e ∉ G.sublevelComponent a u x) : u x < u (G.head e) := by
  by_contra! hle
  have hne : G.tail e ≠ G.head e := fun h ↦ hh (h ▸ ht)
  have hadj := G.positiveGraph_adj_of_edge (S := {z | u z ≤ u x}) e he hne (G.sublevelComponent_le ht) hle
  exact hh (ht.trans hadj.reachable)

omit [Fintype E] in
lemma sublevelComponent_tail_out {a : E → ℝ} {u : V → ℝ} {x : V} (e : E)
    (he : 0 < a e) (ht : G.tail e ∉ G.sublevelComponent a u x)
    (hh : G.head e ∈ G.sublevelComponent a u x) : u x < u (G.tail e) := by
  by_contra! hle
  have hne : G.tail e ≠ G.head e := fun h ↦ ht (h.symm ▸ hh)
  have hadj := G.positiveGraph_adj_of_edge (S := {z | u z ≤ u x}) e he hne hle (G.sublevelComponent_le hh)
  exact ht (hh.trans hadj.symm.reachable)

def cutIndicator (C : Set V) (v : V) : ℝ := by
  classical
  exact if v ∈ C then 1 else 0

def cutTerm (a : E → ℝ) (u : V → ℝ) (C : Set V) (e : E) : ℝ :=
  a e * G.gradient (cutIndicator C) e * G.gradient u e

omit [Fintype E] in
lemma sublevel_cutTerm_neg_tail {a : E → ℝ} {u : V → ℝ} {x : V} (e : E)
    (he : 0 < a e) (ht : G.tail e ∈ G.sublevelComponent a u x)
    (hh : G.head e ∉ G.sublevelComponent a u x) :
    G.cutTerm a u (G.sublevelComponent a u x) e < 0 := by
  have hlt : u (G.tail e) < u (G.head e) :=
    (G.sublevelComponent_le ht).trans_lt (G.sublevelComponent_head_out e he ht hh)
  simp only [cutTerm, gradient, cutIndicator, ite_eq_left ht, ite_eq_right hh]
  nlinarith [mul_pos he (sub_pos.mpr hlt)]

omit [Fintype E] in
lemma sublevel_cutTerm_neg_head {a : E → ℝ} {u : V → ℝ} {x : V} (e : E)
    (he : 0 < a e) (ht : G.tail e ∉ G.sublevelComponent a u x)
    (hh : G.head e ∈ G.sublevelComponent a u x) :
    G.cutTerm a u (G.sublevelComponent a u x) e < 0 := by
  have hlt : u (G.head e) < u (G.tail e) :=
    (G.sublevelComponent_le hh).trans_lt (G.sublevelComponent_tail_out e he ht hh)
  simp only [cutTerm, gradient, cutIndicator, ite_eq_right ht, ite_eq_left hh]
  nlinarith [mul_pos he (sub_pos.mpr hlt)]

omit [Fintype E] in
lemma sublevel_cutTerm_nonpos {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (u : V → ℝ) (x : V) (e : E) : G.cutTerm a u (G.sublevelComponent a u x) e ≤ 0 := by
  classical
  by_cases he : a e = 0
  · simp [cutTerm, he]
  have hpos : 0 < a e := lt_of_le_of_ne (ha e) (Ne.symm he)
  by_cases ht : G.tail e ∈ G.sublevelComponent a u x <;>
    by_cases hh : G.head e ∈ G.sublevelComponent a u x
  · simp [cutTerm, gradient, cutIndicator, ht, hh]
  · exact (G.sublevel_cutTerm_neg_tail e hpos ht hh).le
  · exact (G.sublevel_cutTerm_neg_head e hpos ht hh).le
  · simp [cutTerm, gradient, cutIndicator, ht, hh]

lemma IsHarmonic.cutTerm_eq_zero {a : E → ℝ} {boundary C : Set V} {u : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (hC : ∀ z ∈ boundary, z ∉ C)
    (hnonpos : ∀ e, G.cutTerm a u C e ≤ 0) (e : E) : G.cutTerm a u C e = 0 := by
  have hsum : ∑ j, G.cutTerm a u C j = 0 :=
    hu (cutIndicator C) (by intro z hz; simp [cutIndicator, hC z hz])
  exact (sum_eq_zero_iff_of_nonpos (fun j _ ↦ hnonpos j)).mp hsum e (mem_univ e)

/-- A sublevel component of a harmonic potential reaches the boundary whenever
its starting vertex reaches the boundary in the unrestricted positive graph. -/
theorem IsHarmonic.sublevel_reaches_boundary {a : E → ℝ} {boundary : Set V} {u : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (ha : ∀ e, 0 ≤ a e) {x y : V}
    (hxy : (G.positiveGraph a univ).Reachable x y) (hy : y ∈ boundary) :
    ∃ z ∈ boundary, (G.positiveGraph a {v | u v ≤ u x}).Reachable x z := by
  classical
  by_contra hn
  have hC : ∀ z ∈ boundary, z ∉ G.sublevelComponent a u x := by
    intro z hz hc
    exact hn ⟨z, hz, hc⟩
  have hzero (e : E) := hu.cutTerm_eq_zero G hC (G.sublevel_cutTerm_nonpos ha u x) e
  have hedge (e : E) (he : 0 < a e) :
      G.tail e ∈ G.sublevelComponent a u x ↔ G.head e ∈ G.sublevelComponent a u x := by
    constructor
    · intro ht
      by_contra hh
      have hneg := G.sublevel_cutTerm_neg_tail e he ht hh
      linarith [hzero e]
    · intro hh
      by_contra ht
      have hneg := G.sublevel_cutTerm_neg_head e he ht hh
      linarith [hzero e]
  have hclosed : ∀ v w, (G.positiveGraph a univ).Adj v w →
      v ∈ G.sublevelComponent a u x → w ∈ G.sublevelComponent a u x := by
    rintro v w ⟨_, _, _, e, he, h | h⟩ hv
    · rcases h with ⟨rfl, rfl⟩
      exact (hedge e he).mp hv
    · rcases h with ⟨rfl, rfl⟩
      exact (hedge e he).mpr hv
  have hymem := reachable_preserves_set hclosed (G.mem_sublevelComponent_self a u x) hxy
  exact hC y hy hymem

lemma IsHarmonic.neg {a : E → ℝ} {boundary : Set V} {u : V → ℝ}
    (hu : G.IsHarmonic a boundary u) : G.IsHarmonic a boundary (-u) := by
  intro w hw
  have h := hu w hw
  have heq : G.pairing a w (-u) = -G.pairing a w u := by
    simp only [pairing, gradient, Pi.neg_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq, h, neg_zero]

theorem IsHarmonic.superlevel_reaches_boundary {a : E → ℝ} {boundary : Set V} {u : V → ℝ}
    (hu : G.IsHarmonic a boundary u) (ha : ∀ e, 0 ≤ a e) {x y : V}
    (hxy : (G.positiveGraph a univ).Reachable x y) (hy : y ∈ boundary) :
    ∃ z ∈ boundary, (G.positiveGraph a {v | u x ≤ u v}).Reachable x z := by
  have h := (hu.neg G).sublevel_reaches_boundary G ha hxy hy
  simpa only [Pi.neg_apply, neg_le_neg_iff] using h

end NearCritical.Network
