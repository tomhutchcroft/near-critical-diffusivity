module

public import NearCritical.SplitCrossDirectDistinct

/-! Lower bound for distinct-cluster realisations (item D of the direct proof
of `SplitCrossInput`, assembled).

A `TEdge d U` is a restricted connection `a ↔ b in T` with `T ⊆ U`, `a ∈ U`.
For a list `es` of such edges let `τ_e = P[a_e ↔ b_e in T_e]`.

The overlap of an edge `f` with an edge `x` placed before it is

  `overlap f x = Σ_{w ∈ U} P[x occurs, a_x ↔ w in U] ·`
  `                  P[{a_f ↔ w in T_f} ∘ {w ↔ b_f in T_f}]`.

`distinct_edges_lower`: in additive form,

  `∏ τ_e - errTotal es ≤ P[all edges occur in pairwise disjoint U-clusters]`,

where `errTotal` is the sum over ordered pairs `(f, x)`, `x` after `f` in the
list, of `overlap f x` times the product of `τ` over the other edges
(`posSum`, `errTotal`). The additive form lets boundary terminals be summed
before the overlaps are estimated.

The proof iterates `distinct_step`; the error of a step is bounded with
`distinct_bk` after moving the hit vertex `w` into the event of the edge whose
cluster it lies in (`distinctLoc_inter_mem_subset`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ} {U : Finset (Vertex d)}

/-- Position sum: `Σ_i (∏_{j ≠ i} P[ev_j]) · P[ev_i, root_i ↔ w in U]`. -/
def hitSum (p : unitInterval) (w : Vertex d) : List (LocalEv d U) → ℝ
  | [] => 0
  | x :: t => (percolation d p).real (x.withTarget w).ev *
        (t.map (fun y => (percolation d p).real y.ev)).prod +
      (percolation d p).real x.ev * hitSum p w t

lemma hitSum_nonneg (p : unitInterval) (w : Vertex d) :
    ∀ L : List (LocalEv d U), 0 ≤ hitSum p w L
  | [] => le_rfl
  | x :: t => by
    show 0 ≤ (percolation d p).real (x.withTarget w).ev *
        (t.map (fun y => (percolation d p).real y.ev)).prod +
      (percolation d p).real x.ev * hitSum p w t
    refine add_nonneg (mul_nonneg measureReal_nonneg (List.prod_nonneg (fun r hr => ?_)))
      (mul_nonneg measureReal_nonneg (hitSum_nonneg p w t))
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hr
    exact measureReal_nonneg

/-- The hit event is bounded by the position sum. -/
theorem distinctLoc_hit_le (p : unitInterval) (w : Vertex d) :
    ∀ (L s : List (LocalEv d U)), (∀ x ∈ L, x.root ∈ U) →
      (percolation d p).real (distinctLoc U (s ++ L) ∩
        {ω | ∃ x ∈ L, w ∈ finiteBoxCluster ω U x.root}) ≤
      (s.map (fun y => (percolation d p).real y.ev)).prod * hitSum p w L
  | [], s, _ => by
    have hempty : distinctLoc U (s ++ []) ∩
        {ω | ∃ x ∈ ([] : List (LocalEv d U)), w ∈ finiteBoxCluster ω U x.root} = ∅ := by
      ext ω
      simp
    rw [hempty, measureReal_empty]
    show (0 : ℝ) ≤ _ * 0
    simp
  | x :: t, s, hroot => by
    have hsub : distinctLoc U (s ++ x :: t) ∩
        {ω | ∃ y ∈ x :: t, w ∈ finiteBoxCluster ω U y.root} ⊆
        distinctLoc U (s ++ x.withTarget w :: t) ∪
        (distinctLoc U ((s ++ [x]) ++ t) ∩ {ω | ∃ y ∈ t, w ∈ finiteBoxCluster ω U y.root}) := by
      rintro ω ⟨hd, y, hy, hwy⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Or.inl (distinctLoc_inter_mem_subset s t y (hroot y (by simp)) w ⟨hd, hwy⟩)
      · refine Or.inr ⟨?_, y, hy, hwy⟩
        rw [List.append_assoc]
        exact hd
    have h1 := distinct_bk p (s ++ x.withTarget w :: t)
    have h2 := distinctLoc_hit_le p w t (s ++ [x])
      (fun y hy => hroot y (List.mem_cons_of_mem _ hy))
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans ?_)
    have e1 : ((s ++ x.withTarget w :: t).map (fun y => (percolation d p).real y.ev)).prod =
        (s.map (fun y => (percolation d p).real y.ev)).prod *
          ((percolation d p).real (x.withTarget w).ev *
            (t.map (fun y => (percolation d p).real y.ev)).prod) := by
      rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons]
    have e2 : ((s ++ [x]).map (fun y => (percolation d p).real y.ev)).prod =
        (s.map (fun y => (percolation d p).real y.ev)).prod * (percolation d p).real x.ev := by
      rw [List.map_append, List.prod_append]
      simp
    rw [e1] at h1
    rw [e2] at h2
    show _ ≤ (s.map (fun y => (percolation d p).real y.ev)).prod *
      ((percolation d p).real (x.withTarget w).ev *
          (t.map (fun y => (percolation d p).real y.ev)).prod +
        (percolation d p).real x.ev * hitSum p w t)
    nlinarith [h1, h2]

/-- A tube edge. -/
structure TEdge (d : ℕ) (U : Finset (Vertex d)) where
  T : Set (Vertex d)
  hT : T ⊆ (U : Set (Vertex d))
  a : Vertex d
  b : Vertex d
  ha : a ∈ U

/-- The local event of a tube edge. -/
def TEdge.loc (e : TEdge d U) : LocalEv d U := connLoc U e.T e.hT e.a e.b

/-- The two-point function of a tube edge. -/
def TEdge.tau (p : unitInterval) (e : TEdge d U) : ℝ :=
  (percolation d p).real (connectionToSetEvent e.T e.a {e.b})

/-- The overlap of a new edge `f` with an earlier edge `x`. -/
def TEdge.overlap (p : unitInterval) (f x : TEdge d U) : ℝ :=
  ∑ w ∈ U, (percolation d p).real (x.loc.withTarget w).ev *
    (percolation d p).real {ω | DisjointOccurrence (connectionToSetEvent f.T f.a {w})
      (connectionToSetEvent f.T w {f.b}) ω}

lemma TEdge.loc_stable (e : TEdge d U) (ω ω' : Configuration d)
    (h : ∀ b ∈ clusterRevealBonds U (finiteBoxCluster ω U e.loc.root), ω' b = ω b)
    (hω : ω ∈ e.loc.ev) : ω' ∈ e.loc.ev :=
  conn_stable e.hT h hω

/-- Position sum of the overlaps of `f` with a list of earlier edges:
`Σ_i overlap f x_i · ∏_{j ≠ i} τ_j`. -/
def posSum (p : unitInterval) (f : TEdge d U) : List (TEdge d U) → ℝ
  | [] => 0
  | x :: t => f.overlap p x * (t.map (fun y => y.tau p)).prod + x.tau p * posSum p f t

/-- The step error is exactly the position sum of overlaps. -/
theorem sum_hitSum_eq (p : unitInterval) (f : TEdge d U) :
    ∀ L : List (TEdge d U),
      ∑ w ∈ U, hitSum p w (L.map TEdge.loc) *
          (percolation d p).real {ω | DisjointOccurrence (connectionToSetEvent f.T f.a {w})
            (connectionToSetEvent f.T w {f.b}) ω} = posSum p f L
  | [] => by
    show ∑ w ∈ U, (0 : ℝ) * _ = 0
    simp
  | x :: t => by
    have ih := sum_hitSum_eq p f t
    have hmapτ : (t.map TEdge.loc).map (fun y => (percolation d p).real y.ev) =
        t.map (fun y => y.tau p) := by
      rw [List.map_map]
      rfl
    show _ = f.overlap p x * (t.map (fun y => y.tau p)).prod + x.tau p * posSum p f t
    rw [← ih]
    unfold TEdge.overlap
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    show ((percolation d p).real (x.loc.withTarget w).ev *
        ((t.map TEdge.loc).map (fun y => (percolation d p).real y.ev)).prod +
      (percolation d p).real x.loc.ev * hitSum p w (t.map TEdge.loc)) * _ = _
    rw [hmapτ]
    show _ = _ + x.tau p * _
    unfold TEdge.tau TEdge.loc connLoc
    ring

/-- Total error: sum over ordered pairs of the overlap times the other `τ`. -/
def errTotal (p : unitInterval) : List (TEdge d U) → ℝ
  | [] => 0
  | f :: L => errTotal p L * f.tau p + posSum p f L

set_option maxHeartbeats 800000 in
/-- **Distinct-cluster lower bound, additive form.** -/
theorem distinct_edges_lower (p : unitInterval) :
    ∀ es : List (TEdge d U),
      (es.map (fun x => x.tau p)).prod - errTotal p es ≤
        (percolation d p).real (distinctLoc U (es.map TEdge.loc))
  | [] => by
    have huniv : distinctLoc U (([] : List (TEdge d U)).map TEdge.loc) = Set.univ := by
      ext ω
      simp [distinctLoc]
    rw [huniv]
    show (1 : ℝ) - 0 ≤ _
    simp
  | f :: L => by
    have ih := distinct_edges_lower p L
    have hstep := distinct_step p (L.map TEdge.loc)
      (fun x hx => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
        exact e.ha)
      (fun x hx => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
        exact e.loc_stable)
      f.T f.hT f.a f.b
    have hhit : ∀ w ∈ U, (percolation d p).real (distinctLoc U (L.map TEdge.loc) ∩
        {ω | ∃ x ∈ L.map TEdge.loc, w ∈ finiteBoxCluster ω U x.root}) ≤
        hitSum p w (L.map TEdge.loc) := by
      intro w _
      have h := distinctLoc_hit_le p w (L.map TEdge.loc) []
        (fun x hx => by
          obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
          exact e.ha)
      simpa using h
    have herr : ∑ w ∈ U, (percolation d p).real (distinctLoc U (L.map TEdge.loc) ∩
          {ω | ∃ x ∈ L.map TEdge.loc, w ∈ finiteBoxCluster ω U x.root}) *
        (percolation d p).real {ω | DisjointOccurrence (connectionToSetEvent f.T f.a {w})
          (connectionToSetEvent f.T w {f.b}) ω} ≤ posSum p f L :=
      (Finset.sum_le_sum (fun w hw =>
        mul_le_mul_of_nonneg_right (hhit w hw) measureReal_nonneg)).trans_eq
        (sum_hitSum_eq p f L)
    have hτf : 0 ≤ f.tau p := measureReal_nonneg
    have hs : (percolation d p).real (distinctLoc U (L.map TEdge.loc)) * f.tau p ≤
        (percolation d p).real (distinctLoc U (connLoc U f.T f.hT f.a f.b :: L.map TEdge.loc)) +
        posSum p f L := hstep.trans (add_le_add le_rfl herr)
    have hcons : (f :: L).map TEdge.loc = connLoc U f.T f.hT f.a f.b :: L.map TEdge.loc := rfl
    rw [hcons, List.map_cons, List.prod_cons]
    show f.tau p * (L.map (fun x => x.tau p)).prod - (errTotal p L * f.tau p + posSum p f L) ≤ _
    have hih := mul_le_mul_of_nonneg_right ih hτf
    linarith

end NearCritical.SplitCrossDirect
end
