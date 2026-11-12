module

public import NearCritical.Section10PathFlow
public import NearCritical.Section10OverlapEnergy
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! The simple-path current bound needed by Section10OverlapEnergy.
We select physical network edges, retaining either traversal orientation. -/
@[expose] public section
noncomputable section
namespace NearCritical.Network
open scoped Classical BigOperators
variable {V E : Type*} [Fintype V] [Fintype E]

/-- An actual positive-network trail carries a signed unit current bounded by
its selected physical-edge indicator. No edge multiplicity bound is assumed. -/
theorem positive_trail_current (G : Network V E) (a : E → ℝ)
    {x y : V} (w : (G.positiveGraph a Set.univ).Walk x y) (hw : w.IsTrail) :
    ∃ (P : Finset E) (θ : E → ℝ),
      (∀ e ∈ P, 0 < a e) ∧
      (∀ e ∈ P, s(G.tail e, G.head e) ∈ w.edges) ∧
      P.card ≤ w.length ∧
      (∀ e, |θ e| ≤ if e ∈ P then (1:ℝ) else 0) ∧
      FlowSupported a θ ∧
      (∀ v, G.flowDivergence θ v =
        (if x = v then (1:ℝ) else 0)-(if y = v then (1:ℝ) else 0)) := by
  revert hw
  induction w with
  | nil =>
    intro hw
    refine ⟨∅,fun _ => 0,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp
    · simp
    · simp
    · intro e _; rfl
    · intro v; simp [flowDivergence]
  | @cons x z y hadj w ih =>
    intro hw
    have htail : w.IsTrail := hw.of_cons
    have hnot : s(x,z) ∉ w.edges := by
      have hn : s(x,z) ∉ w.edges ∧ w.edges.Nodup := by
        simpa only [SimpleGraph.Walk.edges_cons,List.nodup_cons] using hw.edges_nodup
      exact hn.1
    obtain ⟨P,θ,hpos,hmap,hcard,hmag,hsupp,hdiv⟩ := ih htail
    obtain ⟨e,he,hends⟩ := hadj.2.2.2
    have hedge : s(G.tail e,G.head e) = s(x,z) := by
      rcases hends with ⟨ht,hh⟩ | ⟨ht,hh⟩
      · simp only [ht,hh]
      · simp only [ht,hh,Sym2.eq_swap]
    have heP : e ∉ P := by
      intro h
      exact hnot (hedge ▸ hmap e h)
    have hzero : θ e = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [if_neg heP] using hmag e) (abs_nonneg _)
    have hstep : ∃ δ : E → ℝ,
        (∀ j, j ≠ e → δ j = 0) ∧ |δ e| = 1 ∧
        (∀ v, G.flowDivergence δ v =
          (if x = v then (1:ℝ) else 0)-(if z = v then (1:ℝ) else 0)) := by
      rcases hends with ⟨ht,hh⟩ | ⟨ht,hh⟩
      · refine ⟨edgeUnitCurrent e,?_,?_,?_⟩
        · intro j hj; simp [edgeUnitCurrent,hj]
        · simp [edgeUnitCurrent]
        · intro v; rw [flowDivergence_edgeUnitCurrent,ht,hh]
      · refine ⟨fun j => -edgeUnitCurrent e j,?_,?_,?_⟩
        · intro j hj; simp [edgeUnitCurrent,hj]
        · simp [edgeUnitCurrent]
        · intro v
          rw [flowDivergence_neg,flowDivergence_edgeUnitCurrent,ht,hh]
          ring
    obtain ⟨δ,hδzero,hδmag,hδdiv⟩ := hstep
    have hnewmag (j : E) : |δ j+θ j| ≤ if j ∈ insert e P then (1:ℝ) else 0 := by
      by_cases hje : j = e
      · subst j
        simp only [hzero,add_zero,hδmag,Finset.mem_insert_self,if_true,le_refl]
      · rw [hδzero j hje,zero_add]
        simpa [hje] using hmag j
    refine ⟨insert e P,fun j => δ j+θ j,?_,?_,?_,hnewmag,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact he
      · exact hpos j hj
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [SimpleGraph.Walk.edges_cons,hedge]
        exact List.mem_cons_self
      · rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_of_mem _ (hmap j hj)
    · rw [Finset.card_insert_of_notMem heP,SimpleGraph.Walk.length_cons]
      omega
    · intro j haj
      have hjP : j ∉ insert e P := by
        intro hj
        have hp : 0 < a j := by
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact he
          · exact hpos j hj
        linarith
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [if_neg hjP] using hnewmag j) (abs_nonneg _)
    · intro v
      rw [flowDivergence_add,hδdiv,hdiv]
      ring

/-- A binary open trail between disjoint faces yields an actual supported unit
flow with energy at most its microscopic length. Both the indicator-current
bound and the energy bound are conclusions of the construction. -/
theorem positive_trail_boundary_current_energy (G : Network V E) (a : E → ℝ)
    (ha : ∀ e, a e = 0 ∨ a e = 1) (S T : Set V) (hST : Disjoint S T)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T)
    (w : (G.positiveGraph a Set.univ).Walk x y) (hw : w.IsTrail) :
    ∃ (P : Finset E) (θ : E → ℝ),
      G.IsBoundaryUnitFlow S T θ ∧ FlowSupported a θ ∧
      (∀ e, |θ e| ≤ if e ∈ P then (1:ℝ) else 0) ∧
      (∀ e ∈ P, a e = 1) ∧ P.card ≤ w.length ∧
      flowEnergy a θ ≤ (w.length:ℝ) := by
  obtain ⟨P,θ,hpos,hmap,hcard,hmag,hsupp,hdiv⟩ := positive_trail_current G a w hw
  have hopen (e : E) (he : e ∈ P) : a e = 1 := by
    rcases ha e with hz | ho
    · have hp := hpos e he
      linarith
    · exact ho
  have hecard : flowEnergy a θ ≤ (P.card:ℝ) := by
    have hb := path_current_pair_energy_le_overlap a θ θ P P hmag hmag hopen
    simpa only [Finset.inter_self,flowEnergy,pow_two] using hb
  refine ⟨P,θ,endpoint_charges_boundary_unit_flow G S T hST hx hy θ hdiv,
    hsupp,hmag,hopen,hcard,hecard.trans ?_⟩
  exact_mod_cast hcard

end NearCritical.Network
