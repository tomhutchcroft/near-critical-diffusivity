module

public import NearCritical.Section9PivotalSupport
public import NearCritical.DisjointOccurrence

/-! Finite closed-bond forcing certificates for the nonmonotone avoidance step. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- All originally closed available bonds; explored edges are excluded. -/
def section9ClosedAvailableBonds {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) : Finset (Bond d) :=
  (sprinklingAvailableBonds T Q F).filter fun b => ω b = false

lemma sprinklingUnexplored_adj_available_bond {d : ℕ} {ω : Configuration d}
    (T Q F : Finset (Vertex d)) {x y : Vertex d}
    (h : (sprinklingUnexploredGraph ω T Q F).Adj x y) :
    ∃ b ∈ sprinklingAvailableBonds T Q F, ω b = true ∧
      ((x = b.1 ∧ y = bondTip b) ∨ (y = b.1 ∧ x = bondTip b)) := by
  obtain ⟨⟨b,hb,hends⟩,hx,hy,hnot⟩ := h
  have hi : b ∈ internalBondSet T := by
    apply (mem_internalBondSet T b).mpr
    rcases hends with ⟨hxb,hyt⟩ | ⟨hyb,hxt⟩
    · exact ⟨hxb ▸ hx,hyt ▸ hy⟩
    · exact ⟨hyb ▸ hy,hxt ▸ hx⟩
  have hn : b ∉ clusterRevealBonds Q F := by
    intro he
    have hp := (mem_clusterRevealBonds Q F b).mp he
    have hh := (pair_mem_exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d))
      b.1 (bondTip b)).mpr hp
    apply hnot
    rcases hends with ⟨hxb,hyt⟩ | ⟨hyb,hxt⟩
    · simpa only [hxb,hyt] using hh
    · simpa only [hyb,hxt,Sym2.eq_swap] using hh
  exact ⟨b,Finset.mem_sdiff.mpr ⟨hi,hn⟩,hb,hends⟩

/-- Fixing closed available coordinates allows edge closures but no new
open edge in the actual deleted graph. Explored coordinates are irrelevant. -/
theorem sprinklingUnexploredGraph_le_of_closed_agree {d : ℕ}
    (T Q F : Finset (Vertex d)) (ω θ : Configuration d)
    (hagree : ∀ b ∈ section9ClosedAvailableBonds ω T Q F, θ b = ω b) :
    sprinklingUnexploredGraph θ T Q F ≤ sprinklingUnexploredGraph ω T Q F := by
  intro x y h
  obtain ⟨b,hb,hθ,hends⟩ := sprinklingUnexplored_adj_available_bond T Q F h
  have hω : ω b = true := by
    cases hw : ω b with
    | false =>
      have hbc : b ∈ section9ClosedAvailableBonds ω T Q F := Finset.mem_filter.mpr ⟨hb,hw⟩
      have hbad : (false : Bool) = true := hw.symm.trans ((hagree b hbc).symm.trans hθ)
      cases hbad
    | true => rfl
  exact ⟨⟨b,hω,hends⟩,h.2⟩

/-- The closed mask universally forces no hit of V by the full component.
It is a genuine finite negative certificate, not an increasing-event claim. -/
theorem section9ClosedAvailable_forces_nonhit {d : ℕ} (ω : Configuration d)
    (T Q F V : Finset (Vertex d)) (root : Vertex d)
    (hnon : ¬ (sprinklingUnexploredCluster ω T Q F root ∩ V).Nonempty) :
    ForcesOn {θ | ¬ (sprinklingUnexploredCluster θ T Q F root ∩ V).Nonempty}
      ω (section9ClosedAvailableBonds ω T Q F : Set (Bond d)) := by
  intro θ hagree hhit
  obtain ⟨v,hv⟩ := hhit
  obtain ⟨hvC,hvV⟩ := Finset.mem_inter.mp hv
  obtain ⟨hvT,hrv⟩ := (mem_sprinklingUnexploredCluster θ T Q F root v).mp hvC
  have hle := sprinklingUnexploredGraph_le_of_closed_agree T Q F ω θ hagree
  apply hnon
  exact ⟨v,Finset.mem_inter.mpr
    ⟨(mem_sprinklingUnexploredCluster ω T Q F root v).mpr ⟨hvT,hrv.mono hle⟩,hvV⟩⟩

/-- A negative certificate uses only closed bonds, hence is disjoint from
every open-bond path certificate, regardless of its geometric support. -/
theorem section9ClosedAvailable_disjoint_open {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (P : Finset (Bond d)) (hP : ∀ b ∈ P, ω b = true) :
    Disjoint (section9ClosedAvailableBonds ω T Q F) P := by
  apply Finset.disjoint_left.mpr
  intro b hb hp
  have hc := (Finset.mem_filter.mp hb).2
  have hbad : (false : Bool) = true := hc.symm.trans (hP b hp)
  cases hbad

end NearCritical
