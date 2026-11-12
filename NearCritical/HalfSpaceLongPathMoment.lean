module

public import NearCritical.FarFaceTailFromHalfSpace
public import NearCritical.Events

/-! The Markov step behind the far-face tail: from the moment bound CHS23 (105)
to `HalfSpaceLongPathTail`.

* `pathListEvent i b s x l`: the vertex list `l` is a self-avoiding open path in
  the axis half-space from `x` to a point of the boundary hyperplane.
* `longestPath i b s x ω`: the supremum of the lengths (numbers of edges) of
  such paths, `0` if there is none. This is `L(x) 1{x <-> boundary}` of
  main.tex 1514--1517; it is measurable (`measurable_longestPath`).
* `HalfSpaceLongPathMoment d K`: `E_{p_c}[L(x) 1{x <-> boundary}] <= K` for every
  axis half-space and every `x` — the cited statement (105), for all axis
  half-spaces (lattice symmetry).
* `halfSpaceLongPathTail_of_moment`: Markov's inequality gives
  `HalfSpaceLongPathTail d K`.

So the far-face tail of the time-constant and slab theorems rests on the cited
moment bound itself, with the Markov step proved.
-/

@[expose] public section
noncomputable section

namespace NearCritical.Section7

open MeasureTheory Set
open scoped Classical ENNReal

variable {d : ℕ}

lemma measurableSet_isChain_restricted (S : Set (Vertex d)) :
    ∀ l : List (Vertex d),
      MeasurableSet {ω : Configuration d | l.IsChain (restrictedGraph ω S).Adj}
  | [] => by simp
  | [_] => by simp
  | a :: b :: l => by
    have h := measurableSet_isChain_restricted S (b :: l)
    have hEq : {ω : Configuration d | (a :: b :: l).IsChain (restrictedGraph ω S).Adj} =
        ({ω : Configuration d | (openGraph ω).Adj a b} ∩ {_ω : Configuration d | a ∈ S ∧ b ∈ S}) ∩
          {ω : Configuration d | (b :: l).IsChain (restrictedGraph ω S).Adj} := by
      ext ω
      simp only [List.isChain_cons_cons, mem_setOf_eq, mem_inter_iff]
      exact ⟨fun h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩⟩
    rw [hEq]
    exact ((measurableSet_open_adj a b).inter (MeasurableSet.const _)).inter h

/-- The list `l` is a self-avoiding open path in the half-space from `x` to the
boundary hyperplane. -/
def pathListEvent (i : Fin d) (b : ℤ) (s : Bool) (x : Vertex d) (l : List (Vertex d)) :
    Set (Configuration d) :=
  {_ω : Configuration d | (∃ h : l ≠ [], l.head h = x ∧ (l.getLast h) i = b) ∧ l.Nodup} ∩
    {ω : Configuration d | l.IsChain (restrictedGraph ω (axisHalfSpace i b s)).Adj}

lemma measurableSet_pathListEvent (i : Fin d) (b : ℤ) (s : Bool) (x : Vertex d)
    (l : List (Vertex d)) : MeasurableSet (pathListEvent i b s x l) :=
  (MeasurableSet.const _).inter (measurableSet_isChain_restricted _ l)

/-- Length of the longest self-avoiding open path from `x` to the boundary
hyperplane inside the half-space (`0` if there is none). -/
def longestPath (i : Fin d) (b : ℤ) (s : Bool) (x : Vertex d) (ω : Configuration d) : ℝ≥0∞ :=
  ⨆ l : List (Vertex d),
    (pathListEvent i b s x l).indicator (fun _ => ((l.length - 1 : ℕ) : ℝ≥0∞)) ω

lemma measurable_longestPath (i : Fin d) (b : ℤ) (s : Bool) (x : Vertex d) :
    Measurable (longestPath i b s x) :=
  Measurable.iSup (fun l => measurable_const.indicator (measurableSet_pathListEvent i b s x l))

/-- Cited moment bound CHS23 (105), main.tex 1514--1517, for every axis
half-space. -/
def HalfSpaceLongPathMoment (d : ℕ) (K : ℝ) : Prop :=
  ∀ (i : Fin d) (b : ℤ) (s : Bool) (x : Vertex d),
    (∫⁻ ω, longestPath i b s x ω ∂percolation d (criticalPoint d)) ≤ ENNReal.ofReal K

lemma halfSpaceLongPathEvent_subset (i : Fin d) (b : ℤ) (s : Bool) (x : Vertex d) (T : ℝ) :
    halfSpaceLongPathEvent i b s x T ⊆ {ω | ENNReal.ofReal T ≤ longestPath i b s x ω} := by
  rintro ω ⟨u, hu, p, hp, hlen⟩
  have hmem : ω ∈ pathListEvent i b s x p.support :=
    ⟨⟨⟨p.support_ne_nil, p.head_support, by rw [p.getLast_support]; exact hu⟩,
      hp.support_nodup⟩, p.isChain_adj_support⟩
  refine le_trans ?_ (le_iSup (fun l : List (Vertex d) =>
    (pathListEvent i b s x l).indicator (fun _ => ((l.length - 1 : ℕ) : ℝ≥0∞)) ω) p.support)
  show ENNReal.ofReal T ≤ (pathListEvent i b s x p.support).indicator
    (fun _ => ((p.support.length - 1 : ℕ) : ℝ≥0∞)) ω
  rw [Set.indicator_of_mem hmem, SimpleGraph.Walk.length_support, Nat.add_sub_cancel,
    ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hlen

/-- **Markov step**: the cited moment bound gives the long-path tail. -/
theorem halfSpaceLongPathTail_of_moment {K : ℝ} (hK : 0 ≤ K)
    (h : HalfSpaceLongPathMoment d K) : HalfSpaceLongPathTail d K := by
  intro i b s x T hT
  have hT0 : ENNReal.ofReal T ≠ 0 := (ENNReal.ofReal_pos.mpr hT).ne'
  have hmarkov := meas_ge_le_lintegral_div (μ := percolation d (criticalPoint d))
    (measurable_longestPath i b s x).aemeasurable hT0 ENNReal.ofReal_ne_top
  have hle : percolation d (criticalPoint d) (halfSpaceLongPathEvent i b s x T) ≤
      ENNReal.ofReal K / ENNReal.ofReal T :=
    (measure_mono (halfSpaceLongPathEvent_subset i b s x T)).trans
      (hmarkov.trans (ENNReal.div_le_div_right (h i b s x) _))
  have hfin : ENNReal.ofReal K / ENNReal.ofReal T ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.ofReal_ne_top hT0
  calc (percolation d (criticalPoint d)).real (halfSpaceLongPathEvent i b s x T)
      ≤ (ENNReal.ofReal K / ENNReal.ofReal T).toReal := ENNReal.toReal_mono hfin hle
    _ = K / T := by
        rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hK, ENNReal.toReal_ofReal hT.le]

end NearCritical.Section7
