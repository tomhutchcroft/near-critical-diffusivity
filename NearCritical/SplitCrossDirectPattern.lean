module

public import NearCritical.SplitCrossDirectIndep
public import NearCritical.SplitCrossDirectPunctured
public import NearCritical.FiniteSurgeryProbability

/-! The local pattern at the nodes (item C of the direct proof of
`SplitCrossInput`).

For a finite set `Rm` of removed vertices and a finite set `St` of star bonds:

* `touchBonds Rm`: the bonds with an endpoint in `Rm`;
* `patEv Rm St`: on `touchBonds Rm` the configuration is exactly "open on
  `St`, closed elsewhere";
* `patEv_prob_ge`: `min(p, 1-p)^|touchBonds Rm| ≤ P[patEv Rm St]`;
* `pattern_indep`: `patEv Rm St` is independent of every event determined by
  the internal bonds of `Λ \ Rm` (the outside domain);
* `arm b i R`, `armBonds b i R` and `arm_reachable`: an open arm joins `b` to
  its tip `rayPt b i R`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ}

/-- The vertex below `v` in direction `i`. -/
def backPt (v : Vertex d) (i : Fin d) : Vertex d := Function.update v i (v i - 1)

lemma bondTip_backPt (v : Vertex d) (i : Fin d) : bondTip (backPt v i, i) = v := by
  unfold bondTip backPt
  simp

lemma backPt_bondTip (e : Bond d) : backPt (bondTip e) e.2 = e.1 := by
  unfold bondTip backPt
  simp

/-- Bonds with an endpoint in `Rm`. -/
def touchBonds (Rm : Finset (Vertex d)) : Finset (Bond d) :=
  Rm.biUnion fun v =>
    (Finset.univ.image fun i : Fin d => ((v, i) : Bond d)) ∪
      (Finset.univ.image fun i : Fin d => ((backPt v i, i) : Bond d))

lemma mem_touchBonds (Rm : Finset (Vertex d)) (e : Bond d) :
    e ∈ touchBonds Rm ↔ e.1 ∈ Rm ∨ bondTip e ∈ Rm := by
  unfold touchBonds
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp h
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      exact Or.inl hv
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      exact Or.inr (by rw [bondTip_backPt]; exact hv)
  · rintro (h | h)
    · exact Finset.mem_biUnion.mpr ⟨e.1, h, Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨e.2, Finset.mem_univ _, rfl⟩)⟩
    · refine Finset.mem_biUnion.mpr ⟨bondTip e, h, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e.2, Finset.mem_univ _, ?_⟩)⟩
      rw [backPt_bondTip]

/-- The prescribed configuration on the bonds touching `Rm`. -/
def patEv (Rm : Finset (Vertex d)) (St : Finset (Bond d)) : Set (Configuration d) :=
  {ω | ∀ e ∈ touchBonds Rm, ω e = decide (e ∈ St)}

lemma patEv_dependsOn (Rm : Finset (Vertex d)) (St : Finset (Bond d)) :
    DependsOn (patEv Rm St) (touchBonds Rm) :=
  fun ω ω' h hω e he => (h e he).symm.trans (hω e he)

theorem patEv_prob_ge (p : unitInterval) (Rm : Finset (Vertex d)) (St : Finset (Bond d)) :
    (min (p : ℝ) (1 - (p : ℝ))) ^ (touchBonds Rm).card ≤
      (percolation d p).real (patEv Rm St) := by
  have h := percolation_finite_surgery_probability p (touchBonds Rm) (touchBonds Rm)
    {ξ | ∀ e : touchBonds Rm, ξ e = decide (e.1 ∈ St)} Set.univ
    (fun ω _ => ⟨fun b => if b ∈ touchBonds Rm then decide (b ∈ St) else ω b,
      fun b hb => if_neg hb, fun e => by
        show (if e.1 ∈ touchBonds Rm then decide (e.1 ∈ St) else ω e.1) = _
        rw [if_pos e.2]⟩)
  have hA : (touchBonds Rm).restrict ⁻¹' {ξ | ∀ e : touchBonds Rm, ξ e = decide (e.1 ∈ St)} =
      patEv Rm St := by
    ext ω
    constructor
    · intro hω e he
      exact hω ⟨e, he⟩
    · intro hω e
      exact hω e.1 e.2
  rw [hA, Set.preimage_univ] at h
  simpa using h

lemma touch_disjoint_internal (Λ Rm : Finset (Vertex d)) :
    Disjoint (touchBonds Rm) (internalBondSet (Λ \ Rm)) := by
  refine Finset.disjoint_left.mpr (fun e he hint => ?_)
  obtain ⟨h1, h2⟩ := (mem_internalBondSet _ e).mp hint
  rcases (mem_touchBonds Rm e).mp he with h | h
  · exact (Finset.mem_sdiff.mp h1).2 h
  · exact (Finset.mem_sdiff.mp h2).2 h

/-- **Pattern and outside events are independent.** -/
theorem pattern_indep (p : unitInterval) (Λ Rm : Finset (Vertex d)) (St : Finset (Bond d))
    {E : Set (Configuration d)} (hE : DependsOn E (internalBondSet (Λ \ Rm))) :
    (percolation d p).real (patEv Rm St ∩ E) =
      (percolation d p).real (patEv Rm St) * (percolation d p).real E :=
  indep_of_dependsOn p (touch_disjoint_internal Λ Rm) (patEv_dependsOn Rm St) hE

/-- The arm from `b` in direction `i`: the points `b + k e_i`, `k < R`. -/
def arm (b : Vertex d) (i : Fin d) (R : ℕ) : Finset (Vertex d) :=
  (Finset.range R).image (rayPt b i)

/-- The bonds of the arm, the last one ending at the tip `rayPt b i R`. -/
def armBonds (b : Vertex d) (i : Fin d) (R : ℕ) : Finset (Bond d) :=
  (Finset.range R).image fun k => ((rayPt b i k, i) : Bond d)

/-- An open arm joins `b` to its tip. -/
theorem arm_reachable {ω : Configuration d} {S : Set (Vertex d)} (b : Vertex d) (i : Fin d) :
    ∀ R : ℕ, (∀ k < R, ω (rayPt b i k, i) = true) → (∀ k ≤ R, rayPt b i k ∈ S) →
      (restrictedGraph ω S).Reachable b (rayPt b i R)
  | 0, _, _ => Reachable.refl _
  | R+1, hopen, hS => by
    have ih := arm_reachable b i R (fun k hk => hopen k (Nat.lt_succ_of_lt hk))
      (fun k hk => hS k (Nat.le_succ_of_le hk))
    have hadj : (restrictedGraph ω S).Adj (rayPt b i R) (rayPt b i (R + 1)) :=
      ⟨⟨(rayPt b i R, i), hopen R (Nat.lt_succ_self R), Or.inl ⟨rfl, rfl⟩⟩,
        hS R (Nat.le_succ R), hS (R + 1) le_rfl⟩
    exact ih.trans hadj.reachable

end NearCritical.SplitCrossDirect
end
