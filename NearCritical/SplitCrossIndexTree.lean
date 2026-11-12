module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic.DeriveFintype

/-! The finite tree indexing the direct split-crossing construction. Each
leg has a cube-side entry branch and an exterior branch, with one terminal
on the far face and two interior dummy terminals. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SimpleGraph
open scoped Classical

def parentGraph {V : Type*} (parent : V → V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (parent u = v ∨ parent v = u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem parentGraph_isTree {V : Type*} [Fintype V]
    (root : V) (parent : V → V) (rank : V → ℕ)
    (hroot : parent root = root) (hRank : ∀ v, v ≠ root → rank (parent v) < rank v) :
    (parentGraph parent).IsTree := by
  classical
  let G := parentGraph parent
  have hne (v : V) (hv : v ≠ root) : v ≠ parent v := by
    intro h
    have hh := hRank v hv
    rw [← h] at hh
    exact (lt_irrefl _) hh
  have hreach : ∀ n (v : V), rank v = n → G.Reachable root v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hvr
      by_cases hv : v = root
      · subst v
        exact .refl _
      · have hsmall : rank (parent v) < n := by
          rw [← hvr]
          exact hRank v hv
        have hstep : G.Adj (parent v) v := ⟨(hne v hv).symm, Or.inr rfl⟩
        exact (ih _ hsmall _ rfl).trans hstep.reachable
  have hconn : G.Connected := (connected_iff_exists_forall_reachable (G := G)).mpr
    ⟨root, fun v => hreach (rank v) v rfl⟩
  let W := (Finset.univ : Finset V).erase root
  let edge (v : ↥W) : G.edgeSet :=
    ⟨s(v.val, parent v.val), (SimpleGraph.mem_edgeSet (G := G)).mpr
      ⟨hne _ (Finset.mem_erase.mp v.property).1, Or.inl rfl⟩⟩
  have hinj : Function.Injective edge := by
    intro u v h
    have hp : s(u.val, parent u.val) = s(v.val, parent v.val) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hp with ⟨huv, _⟩ | ⟨huv, hvu⟩
    · exact Subtype.ext huv
    · have hu := hRank u.val (Finset.mem_erase.mp u.property).1
      have hv := hRank v.val (Finset.mem_erase.mp v.property).1
      rw [hvu] at hu
      rw [← huv] at hv
      omega
  have hsurj : Function.Surjective edge := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b ∧ (parent a = b ∨ parent b = a) := (SimpleGraph.mem_edgeSet (G := G)).mp he
      rcases hab.2 with hp | hp
      · have ha : a ≠ root := by
          intro ha
          subst a
          exact hab.1 (hroot.symm.trans hp)
        refine ⟨⟨a, Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩⟩, Subtype.ext ?_⟩
        change s(a, parent a) = s(a,b)
        rw [hp]
      · have hb : b ≠ root := by
          intro hb
          subst b
          exact hab.1 (hp.symm.trans hroot)
        refine ⟨⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩⟩, Subtype.ext ?_⟩
        change s(b, parent b) = s(a,b)
        rw [hp, Sym2.eq_swap]
  refine (isTree_iff_connected_and_card).mpr ⟨hconn, ?_⟩
  rw [Nat.card_congr (Equiv.ofBijective edge ⟨hinj, hsurj⟩).symm,
    Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card]
  simpa [W] using (Finset.card_erase_add_one
    (s := (Finset.univ : Finset V)) (Finset.mem_univ root))

inductive SplitTreeNode (L : ℕ)
  | root
  | spine (k : Fin (L - 1))
  | entry (leg : Fin L)
  | exterior (leg : Fin L)
  | cubeDummy (leg : Fin L)
  | exteriorDummy (leg : Fin L)
  | face (leg : Fin L)
  deriving DecidableEq, Fintype

namespace SplitTreeNode

def parent {L : ℕ} (hL : 2 ≤ L) : SplitTreeNode L → SplitTreeNode L
  | root => root
  | spine k => if hk : k.val = 0 then root else spine ⟨k.val - 1, by have := k.isLt; omega⟩
  | entry leg => spine ⟨min leg.val (L - 2), by have := min_le_right leg.val (L - 2); omega⟩
  | exterior leg => entry leg
  | cubeDummy leg => entry leg
  | exteriorDummy leg => exterior leg
  | face leg => exterior leg

def rank {L : ℕ} : SplitTreeNode L → ℕ
  | root => 0
  | spine k => k.val + 1
  | entry _ => L + 1
  | exterior _ => L + 2
  | cubeDummy _ => L + 2
  | exteriorDummy _ => L + 3
  | face _ => L + 3

theorem parent_rank_lt {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L) (hv : v ≠ root) :
    rank (parent hL v) < rank v := by
  cases v with
  | root => exact (hv rfl).elim
  | spine k =>
    by_cases hk : k.val = 0
    · simp [parent, rank, hk]
    · simp [parent, rank, hk]
      omega
  | entry leg =>
    have hh := min_le_right leg.val (L - 2)
    simp [parent, rank]
  | exterior leg => simp [parent, rank]
  | cubeDummy leg => simp [parent, rank]
  | exteriorDummy leg => simp [parent, rank]
  | face leg => simp [parent, rank]

def graph {L : ℕ} (hL : 2 ≤ L) : SimpleGraph (SplitTreeNode L) := parentGraph (parent hL)

theorem graph_adj_iff {L : ℕ} (hL : 2 ≤ L) (u v : SplitTreeNode L) :
    (graph hL).Adj u v ↔ u ≠ v ∧ (parent hL u = v ∨ parent hL v = u) := Iff.rfl

theorem parent_adj {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L) (hv : v ≠ root) :
    (graph hL).Adj (parent hL v) v := by
  refine ⟨?_, Or.inr rfl⟩
  intro h
  have hh := parent_rank_lt hL v hv
  rw [h] at hh
  exact (lt_irrefl _) hh

theorem graph_isTree {L : ℕ} (hL : 2 ≤ L) : (graph hL).IsTree :=
  parentGraph_isTree root (parent hL) rank rfl (parent_rank_lt hL)

end SplitTreeNode
end NearCritical.SplitCrossDirect
