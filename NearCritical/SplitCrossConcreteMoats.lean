module

public import NearCritical.SplitCrossConcreteLayout

/-! At ball radius one the branch moat is just the union of the non-tip
vertices of its three arms. The concrete finite-energy event then agrees
with the arm-only pattern used by the lattice overcount theorem. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode
open scoped Classical

theorem mem_branchAxes_iff_portAxis {d : ℕ} (hd : 3 ≤ d) (i : Fin d) :
    i ∈ branchAxes hd ↔ ∃ j : Fin 3, crossingPortAxis hd j = i := by
  constructor
  · intro hi
    simp only [branchAxes, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨childPortSlot false, (crossingPortAxis_child hd false).trans h.symm⟩
    · exact ⟨childPortSlot true, (crossingPortAxis_child hd true).trans h.symm⟩
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact parentAxis_mem_branchAxes hd
    · exact childAxis_mem_branchAxes hd false
    · exact childAxis_mem_branchAxes hd true

private theorem mem_starNonTip_iff {d : ℕ} {b z : Vertex d} {axes : Finset (Fin d)} {n : ℕ} :
    z ∈ starNonTipVertices b axes n ↔
      ∃ i ∈ axes, ∃ k < n, starTip b i k = z := by
  constructor
  · intro hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    exact ⟨i, hi, k, Finset.mem_range.mp hk, rfl⟩
  · rintro ⟨i, hi, k, hk, rfl⟩
    exact Finset.mem_image.mpr ⟨(starTip b i k, i),
      Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩⟩,
      rfl⟩

theorem branchMoatVertices_one {d : ℕ} (b : Vertex d) (axes : Finset (Fin d)) (R : ℕ) :
    branchMoatVertices b axes R 1 = starNonTipVertices b axes (R + 1) := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hz
    · obtain ⟨i, hi, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      have hu0 : u = 0 := by
        ext j
        have hj := mem_centeredBox.mp hu j
        change -(0 : ℤ) ≤ u j ∧ u j ≤ 0 at hj
        change u j = 0
        omega
      subst u
      exact mem_starNonTip_iff.mpr ⟨i, hi, R, by omega, by simp⟩
  · exact Finset.mem_union_left _

theorem concreteCrossingLayout_Rm {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (b : SplitTreeNode (4 * d) → Vertex d) :
    (concreteCrossingLayout hd hL t x R).Rm (fun v => b v.val) =
      treeMoatVertices (crossingBranches (4 * d)) b (branchAxes hd) R 1 := by
  ext z
  constructor
  · intro hz
    obtain ⟨v, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_biUnion.mpr ⟨v.val, (mem_crossingBranches _).mpr v.property, ?_⟩
    rw [branchMoatVertices_one]
    exact mem_starNonTip_iff.mpr ⟨crossingPortAxis hd j,
      (mem_branchAxes_iff_portAxis hd _).mpr ⟨j, rfl⟩,
      k, Finset.mem_range.mp hk, (rayPt_eq_starTip _ _ _).symm⟩
  · intro hz
    obtain ⟨v, hv, hz⟩ := Finset.mem_biUnion.mp hz
    rw [branchMoatVertices_one] at hz
    obtain ⟨i, hi, k, hk, rfl⟩ := mem_starNonTip_iff.mp hz
    obtain ⟨j, rfl⟩ := (mem_branchAxes_iff_portAxis hd i).mp hi
    exact Finset.mem_biUnion.mpr ⟨⟨v, (mem_crossingBranches _).mp hv⟩, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rayPt_eq_starTip _ _ _⟩⟩⟩

theorem concreteCrossingLayout_St {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (b : SplitTreeNode (4 * d) → Vertex d) :
    (concreteCrossingLayout hd hL t x R).St (fun v => b v.val) =
      treeOpenBonds (crossingBranches (4 * d)) b (branchAxes hd) R 1 := by
  ext e
  constructor
  · intro he
    obtain ⟨v, _, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨j, _, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_biUnion.mpr ⟨v.val, (mem_crossingBranches _).mpr v.property, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨crossingPortAxis hd j,
      (mem_branchAxes_iff_portAxis hd _).mpr ⟨j, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨k, hk, congrArg (fun z => (z, crossingPortAxis hd j))
      (rayPt_eq_starTip _ _ _).symm⟩
  · intro he
    obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, rfl⟩ := (mem_branchAxes_iff_portAxis hd i).mp hi
    exact Finset.mem_biUnion.mpr ⟨⟨v, (mem_crossingBranches _).mp hv⟩, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨k, hk, congrArg (fun z => (z, crossingPortAxis hd j))
          (rayPt_eq_starTip _ _ _)⟩⟩⟩

theorem concreteCrossingLayout_Uout {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (b : SplitTreeNode (4 * d) → Vertex d) :
    (concreteCrossingLayout hd hL t x R).Uout (fun v => b v.val) = crossingOutside hd t b R 1 := by
  rw [Layout.Uout, concreteCrossingLayout_Rm]
  rfl

private theorem touchBonds_treeMoatVertices {d : ℕ} {ι : Type*} (I : Finset ι)
    (b : ι → Vertex d) (axes : Finset (Fin d)) (R r : ℕ) :
    touchBonds (treeMoatVertices I b axes R r) = treeGuardBonds I b axes R r := by
  ext e
  simp only [mem_touchBonds, treeMoatVertices, treeGuardBonds, branchGuardBonds, Finset.mem_biUnion]
  constructor
  · rintro (⟨i, hi, he⟩ | ⟨i, hi, he⟩)
    · exact ⟨i, hi, e.1, he, (External.mem_vertexIncidentBonds _ _).mpr (Or.inl rfl)⟩
    · exact ⟨i, hi, bondTip e, he, (External.mem_vertexIncidentBonds _ _).mpr (Or.inr rfl)⟩
  · rintro ⟨i, hi, v, hv, he⟩
    rcases (External.mem_vertexIncidentBonds _ _).mp he with h | h
    · exact Or.inl ⟨i, hi, by simpa [h] using hv⟩
    · exact Or.inr ⟨i, hi, by simpa [h] using hv⟩

theorem concreteCrossingLayout_patEv {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (b : SplitTreeNode (4 * d) → Vertex d) :
    patEv ((concreteCrossingLayout hd hL t x R).Rm (fun v => b v.val))
        ((concreteCrossingLayout hd hL t x R).St (fun v => b v.val)) =
      treeBranchPattern (crossingBranches (4 * d)) b (branchAxes hd) R 1 := by
  rw [concreteCrossingLayout_Rm, concreteCrossingLayout_St]
  ext ω
  simp only [patEv, Set.mem_ofPred_eq, touchBonds_treeMoatVertices, treeBranchPattern,
    Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext e
    exact h e.val e.property
  · intro h e he
    exact congrFun h ⟨e, he⟩

end NearCritical.SplitCrossDirect
