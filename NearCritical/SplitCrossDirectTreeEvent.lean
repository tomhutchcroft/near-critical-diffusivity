module

public import NearCritical.SplitCrossDirectSkeleton
public import NearCritical.ThreePointTreeGraphDerivation

/-! The `n`-point tree-graph bound in a finite domain (item B of the direct
proof of `SplitCrossInput`, probabilistic half).

* `treeEv D y n u S`: the nested disjoint-occurrence event of a root-branch
  tree of depth at most `n` joining `u` to the terminals `y i`, `i ∈ S`,
  inside `D`: either `S = {i}` and `u ↔ y i`, or there are a branch vertex
  `w ∈ D` and a partition `S = A ⊔ B` with
  `{u ↔ w} ∘ (treeEv n w A ∘ treeEv n w B)`.
* `treeEv_of_skel`, `mem_treeEv_of_reachable`: if `u ∈ D` is joined inside `D`
  to every terminal of a nonempty label set `S`, the configuration is in
  `treeEv D y S.card u S` (through a skeleton and walk certificates).
* `treeEv_increasing`.
* `treeBound`, `treeEv_probability_le`: the BK recursion
  `P[treeEv (n+1) u S] ≤ [S = {i}] τ(u, y i) +
     Σ_{w ∈ D} Σ_{A ⊂ S} τ(u,w) · bound n w A · bound n w (S \ A)`,
  with `τ` the restricted two-point function of `D`.
* `connections_probability_le_treeBound`: the `n`-point function is bounded by
  `treeBound`.

Only increasing-event BK is used. The existing code had the case of two
terminals (the tripod).
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ} {ι : Type*}

/-- Nested disjoint-occurrence event of a root-branch tree of depth `≤ n`. -/
def treeEv (D : Set (Vertex d)) (y : ι → Vertex d) :
    ℕ → Vertex d → Finset ι → Set (Configuration d)
  | 0, _, _ => ∅
  | n+1, u, S =>
    {ω | ∃ i, S = {i} ∧ ω ∈ connectionToSetEvent D u {y i}} ∪
    {ω | ∃ w ∈ D, ∃ A B : Finset ι, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = S ∧
      DisjointOccurrence (connectionToSetEvent D u {w})
        {θ | DisjointOccurrence (treeEv D y n w A) (treeEv D y n w B) θ} ω}

theorem treeEv_increasing (D : Set (Vertex d)) (y : ι → Vertex d) :
    ∀ (n : ℕ) (u : Vertex d) (S : Finset ι), BK.Increasing (treeEv D y n u S)
  | 0, _, _ => fun _ _ _ h => h.elim
  | n+1, u, S => by
    rintro ω θ hle (⟨i, hS, hω⟩ | ⟨w, hw, A, B, hA, hB, hAB, hS, hω⟩)
    · exact Or.inl ⟨i, hS, connectionToSetEvent_increasing D u {y i} hle hω⟩
    · exact Or.inr ⟨w, hw, A, B, hA, hB, hAB, hS,
        increasing_disjointOccurrence (connectionToSetEvent_increasing D u {w})
          (increasing_disjointOccurrence (treeEv_increasing D y n w A)
            (treeEv_increasing D y n w B)) hle hω⟩

/-- A skeleton inside `D` gives an open certificate forcing the tree event. -/
theorem treeEv_of_skel (D : Set (Vertex d)) (y : ι → Vertex d) {ω : Configuration d}
    {u : Vertex d} {S : Finset ι} {E : Set (Sym2 (Vertex d))} {W : Set (Vertex d)}
    (h : Skel (openGraph ω) y u S E W) : W ⊆ D → ∀ n, S.card ≤ n →
      ∃ F : Finset (Bond d), (∀ e ∈ F, ω e = true) ∧ (∀ e ∈ F, s(e.1, bondTip e) ∈ E) ∧
        ∀ θ : Configuration d, (∀ e ∈ F, θ e = true) → θ ∈ treeEv D y n u S := by
  induction h with
  | @leaf u i p hp =>
    intro hW n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
      have : 1 ≤ n := by simpa using hn
      omega⟩
    obtain ⟨F, hFo, hFe, hF⟩ := openWalk_certificate p D (fun z hz => hW hz)
    exact ⟨F, hFo, hFe, fun θ hθ => Or.inl ⟨i, rfl, hF θ hθ⟩⟩
  | @branch u w A B EA EB WA WB p hp hA hB d1 d2 d3 hAB ihA ihB =>
    intro hW n hn
    have hcard : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB
    have hApos := hA.nonempty.card_pos
    have hBpos := hB.nonempty.card_pos
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨Fp, hFpo, hFpe, hFp⟩ := openWalk_certificate p D
      (fun z hz => hW (Or.inl (Or.inl hz)))
    obtain ⟨FA, hFAo, hFAe, hFA⟩ := ihA (fun z hz => hW (Or.inl (Or.inr hz))) m (by omega)
    obtain ⟨FB, hFBo, hFBe, hFB⟩ := ihB (fun z hz => hW (Or.inr hz)) m (by omega)
    refine ⟨Fp ∪ FA ∪ FB, ?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp he with he | he
        · exact hFpo e he
        · exact hFAo e he
      · exact hFBo e he
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp he with he | he
        · exact Or.inl (Or.inl (hFpe e he))
        · exact Or.inl (Or.inr (hFAe e he))
      · exact Or.inr (hFBe e he)
    · intro θ hθ
      have hwD : w ∈ D := hW (Or.inl (Or.inl p.end_mem_support))
      refine Or.inr ⟨w, hwD, A, B, hA.nonempty, hB.nonempty, hAB, rfl,
        (Fp : Set (Bond d)), (FA : Set (Bond d)) ∪ (FB : Set (Bond d)),
        Fp.finite_toSet, FA.finite_toSet.union FB.finite_toSet, ?_, ?_, ?_⟩
      · refine Set.disjoint_left.mpr ?_
        rintro e hep (heA | heB)
        · exact d1 _ (hFpe e hep) (hFAe e heA)
        · exact d2 _ (hFpe e hep) (hFBe e heB)
      · intro η hη
        exact hFp η (fun e he => (hη e he).trans
          (hθ e (Finset.mem_union_left _ (Finset.mem_union_left _ he))))
      · apply Section8.forcesOn_disjointOccurrence_union FA.finite_toSet FB.finite_toSet
        · exact Set.disjoint_left.mpr (fun e heA heB =>
            Set.disjoint_left.mp d3 (hFAe e heA) (hFBe e heB))
        · intro η hη
          exact hFA η (fun e he => (hη e he).trans
            (hθ e (Finset.mem_union_left _ (Finset.mem_union_right _ he))))
        · intro η hη
          exact hFB η (fun e he => (hη e he).trans (hθ e (Finset.mem_union_right _ he)))

/-- **Root-branch decomposition.** -/
theorem mem_treeEv_of_reachable (D : Set (Vertex d)) (y : ι → Vertex d) {ω : Configuration d}
    {u : Vertex d} (hu : u ∈ D) {S : Finset ι} (hS : S.Nonempty)
    (hr : ∀ i ∈ S, (restrictedGraph ω D).Reachable u (y i)) :
    ω ∈ treeEv D y S.card u S := by
  obtain ⟨E, W, hsk⟩ := exists_skel (G := restrictedGraph ω D) y u S hS hr
  have hW : W ⊆ D := hsk.subset_of_closed (D := D)
    (fun a b (hab : (restrictedGraph ω D).Adj a b) _ => hab.2.2) hu
  have hle : restrictedGraph ω D ≤ openGraph ω := fun _ _ h => h.1
  have hsk' : Skel (openGraph ω) y u S E W := hsk.mono hle
  obtain ⟨F, hFo, _, hF⟩ := treeEv_of_skel D y hsk' hW S.card le_rfl
  exact hF ω hFo

/-- The tree-graph bound, as a recursion. -/
def treeBound (P : Vertex d → Vertex d → ℝ) (Dfin : Finset (Vertex d)) (y : ι → Vertex d) :
    ℕ → Vertex d → Finset ι → ℝ
  | 0, _, _ => 0
  | n+1, u, S =>
    (∑ i ∈ S, if S = {i} then P u (y i) else 0) +
    ∑ w ∈ Dfin, ∑ A ∈ S.powerset,
      if A.Nonempty ∧ (S \ A).Nonempty then
        P u w * treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) else 0

theorem treeEv_probability_le (p : unitInterval) (Dfin : Finset (Vertex d)) (y : ι → Vertex d) :
    ∀ (n : ℕ) (u : Vertex d) (S : Finset ι),
      (percolation d p).real (treeEv (Dfin : Set (Vertex d)) y n u S) ≤
        treeBound (fun a b => (percolation d p).real
          (connectionToSetEvent (Dfin : Set (Vertex d)) a {b})) Dfin y n u S
  | 0, u, S => by
    show (percolation d p).real (∅ : Set (Configuration d)) ≤ 0
    simp
  | n+1, u, S => by
    have ih := treeEv_probability_le p Dfin y n
    have hnn : ∀ w A, 0 ≤ (percolation d p).real (treeEv (Dfin : Set (Vertex d)) y n w A) :=
      fun _ _ => measureReal_nonneg
    refine (measureReal_union_le _ _).trans (add_le_add ?_ ?_)
    · by_cases hS : ∃ i, S = {i}
      · obtain ⟨i, rfl⟩ := hS
        rw [Finset.sum_singleton, if_pos rfl]
        refine measureReal_mono ?_ (measure_ne_top _ _)
        rintro ω ⟨j, hj, hω⟩
        have hij : i = j := Finset.singleton_injective hj
        exact hij ▸ hω
      · have hempty : {ω : Configuration d | ∃ i, S = {i} ∧
            ω ∈ connectionToSetEvent (Dfin : Set (Vertex d)) u {y i}} = ∅ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨i, hi, _⟩
          exact hS ⟨i, hi⟩
        rw [hempty, measureReal_empty]
        exact Finset.sum_nonneg (fun i _ => by
          split_ifs
          · exact measureReal_nonneg
          · exact le_rfl)
    · have hsub : {ω : Configuration d | ∃ w ∈ (Dfin : Set (Vertex d)), ∃ A B : Finset ι,
            A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = S ∧
            DisjointOccurrence (connectionToSetEvent (Dfin : Set (Vertex d)) u {w})
              {θ | DisjointOccurrence (treeEv (Dfin : Set (Vertex d)) y n w A)
                (treeEv (Dfin : Set (Vertex d)) y n w B) θ} ω} ⊆
          ⋃ w ∈ Dfin, ⋃ A ∈ S.powerset,
            (if A.Nonempty ∧ (S \ A).Nonempty then
              {ω : Configuration d | DisjointOccurrence
                (connectionToSetEvent (Dfin : Set (Vertex d)) u {w})
                {θ | DisjointOccurrence (treeEv (Dfin : Set (Vertex d)) y n w A)
                  (treeEv (Dfin : Set (Vertex d)) y n w (S \ A)) θ} ω} else ∅) := by
        rintro ω ⟨w, hw, A, B, hA, hB, hAB, hS, hω⟩
        have hBeq : S \ A = B := by
          rw [← hS, Finset.union_sdiff_cancel_left hAB]
        have hAS : A ∈ S.powerset := Finset.mem_powerset.mpr (hS ▸ Finset.subset_union_left)
        refine Set.mem_iUnion₂.mpr ⟨w, Finset.mem_coe.mp hw, Set.mem_iUnion₂.mpr ⟨A, hAS, ?_⟩⟩
        rw [if_pos ⟨hA, hBeq ▸ hB⟩, hBeq]
        exact hω
      refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
      refine (measureReal_biUnion_finset_le Dfin _).trans (Finset.sum_le_sum (fun w _ => ?_))
      refine (measureReal_biUnion_finset_le S.powerset _).trans
        (Finset.sum_le_sum (fun A _ => ?_))
      split_ifs with hc
      · refine (tripod_occurrence_probability_le p _ _ _
          (connectionToSetEvent_increasing _ _ _) (treeEv_increasing _ y n w A)
          (treeEv_increasing _ y n w (S \ A))).trans ?_
        have h1 := ih w A
        have h2 := ih w (S \ A)
        have hP : 0 ≤ (percolation d p).real
            (connectionToSetEvent (Dfin : Set (Vertex d)) u {w}) := measureReal_nonneg
        calc _ ≤ (percolation d p).real (connectionToSetEvent (Dfin : Set (Vertex d)) u {w}) *
              treeBound _ Dfin y n w A *
              (percolation d p).real (treeEv (Dfin : Set (Vertex d)) y n w (S \ A)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hP) (hnn w (S \ A))
          _ ≤ _ := mul_le_mul_of_nonneg_left h2
            (mul_nonneg hP ((hnn w A).trans h1))
      · rw [measureReal_empty]

/-- **`n`-point tree-graph bound in a finite domain.** -/
theorem connections_probability_le_treeBound (p : unitInterval) (Dfin : Finset (Vertex d))
    (y : ι → Vertex d) {u : Vertex d} (hu : u ∈ Dfin) {S : Finset ι} (hS : S.Nonempty) :
    (percolation d p).real {ω | ∀ i ∈ S,
        (restrictedGraph ω (Dfin : Set (Vertex d))).Reachable u (y i)} ≤
      treeBound (fun a b => (percolation d p).real
        (connectionToSetEvent (Dfin : Set (Vertex d)) a {b})) Dfin y S.card u S :=
  (measureReal_mono (fun ω hω =>
    mem_treeEv_of_reachable (Dfin : Set (Vertex d)) y (Finset.mem_coe.mpr hu) hS hω)
    (measure_ne_top _ _)).trans (treeEv_probability_le p Dfin y S.card u S)

end NearCritical.SplitCrossDirect
end
