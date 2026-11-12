module

public import NearCritical.SplitCrossDirectOffReveal
public import NearCritical.OpenEventHarris

/-! Connections in punctured domains (item C of the direct proof of
`SplitCrossInput`, generic lemmas).

* `conn_harris_concat`: `P[a ↔ b in S] · P[b ↔ c in S] ≤ P[a ↔ c in S]` (Harris).
* `rayPt x i k`: the point `x + k e_i`; `conn_ray_ge`: if the ray segment lies
  in `S` then `p^k ≤ P[x ↔ x + k e_i in S]`.
* `conn_avoid_lower`: for a finite removed set `Rm`,
  `P[a ↔ b in S] ≤ P[a ↔ b in S \ Rm] + Σ_{w ∈ Rm} P[a ↔ w in S] · P[w ↔ b in S]`
  (a path meeting `Rm` at `w` has edge-disjoint halves; BK).
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory SimpleGraph
open scoped Classical BigOperators ENNReal

variable {d : ℕ}

lemma conn_finite_witnesses (S A : Set (Vertex d)) (x : Vertex d) :
    connectionToSetEvent S x A =
      ⋃ F : Finset (Bond d), BK.truncation (connectionToSetEvent S x A) F := by
  ext ω
  constructor
  · rintro ⟨hx, y, hy, hyS, ⟨w⟩⟩
    have hle : restrictedGraph ω S ≤ openGraph ω := fun _ _ h => h.1
    have hv : ∀ z ∈ (w.mapLe hle).support, z ∈ S := by
      intro z hz
      rw [Walk.support_mapLe_eq_support] at hz
      exact restrictedWalk_support w hx z hz
    obtain ⟨F, hopen, _, hforce⟩ := openWalk_certificate (w.mapLe hle) S hv
    apply Set.mem_iUnion.mpr
    refine ⟨F, ?_⟩
    change connectionToSetEvent S x A (Network.certificateConfiguration ω (F : Set (Bond d)))
    obtain ⟨hx', z, hz, hzS, hp⟩ :=
      hforce (Network.certificateConfiguration ω (F : Set (Bond d))) (fun e he => by
        simpa [Network.certificateConfiguration, he] using hopen e he)
    have hzy : z = y := hz
    subst z
    exact ⟨hx', y, hy, hzS, hp⟩
  · intro h
    obtain ⟨F, hF⟩ := Set.mem_iUnion.mp h
    exact BK.truncation_subset (connectionToSetEvent_increasing S x A) F hF

/-- **Harris concatenation of restricted connections.** -/
theorem conn_harris_concat (p : unitInterval) (S : Set (Vertex d)) (a b c : Vertex d) :
    (percolation d p).real (connectionToSetEvent S a {b}) *
        (percolation d p).real (connectionToSetEvent S b {c}) ≤
      (percolation d p).real (connectionToSetEvent S a {c}) := by
  have hH := percolation_harris_of_finite_witnesses d p
    (connectionToSetEvent_increasing S a {b}) (connectionToSetEvent_increasing S b {c})
    (conn_finite_witnesses S {b} a) (conn_finite_witnesses S {c} b)
  have hsub : connectionToSetEvent S a {b} ∩ connectionToSetEvent S b {c} ⊆
      connectionToSetEvent S a {c} := by
    rintro ω ⟨⟨ha, y, hy, _, h1⟩, ⟨_, z, hz, hzS, h2⟩⟩
    rw [Set.mem_singleton_iff] at hy hz
    subst hy
    exact ⟨ha, z, hz, hzS, h1.trans h2⟩
  have hE := hH.trans (measure_mono hsub)
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hE
  rw [ENNReal.toReal_mul] at hreal
  exact hreal

/-- The point `x + k e_i`. -/
def rayPt (x : Vertex d) (i : Fin d) : ℕ → Vertex d
  | 0 => x
  | k+1 => bondTip (rayPt x i k, i)

lemma rayPt_apply (x : Vertex d) (i : Fin d) : ∀ (k : ℕ) (j : Fin d),
    rayPt x i k j = x j + (if j = i then (k : ℤ) else 0)
  | 0, j => by simp [rayPt]
  | k+1, j => by
    show bondTip (rayPt x i k, i) j = _
    unfold bondTip
    by_cases h : j = i
    · subst h
      rw [Function.update_self]
      show rayPt x j k j + 1 = _
      rw [rayPt_apply x j k j]
      simp
      ring
    · rw [Function.update_of_ne h]
      show rayPt x i k j = _
      rw [rayPt_apply x i k j]
      simp [h]

/-- One open bond gives a connection. -/
lemma conn_step_ge (p : unitInterval) (S : Set (Vertex d)) (x : Vertex d) (i : Fin d)
    (hx : x ∈ S) (hy : bondTip (x, i) ∈ S) :
    (p : ℝ) ≤ (percolation d p).real (connectionToSetEvent S x {bondTip (x, i)}) := by
  have hsub : {ω : Configuration d | ω (x, i) = true} ⊆
      connectionToSetEvent S x {bondTip (x, i)} := by
    intro ω hω
    refine ⟨hx, _, rfl, hy, Adj.reachable ?_⟩
    exact ⟨⟨(x, i), hω, Or.inl ⟨rfl, rfl⟩⟩, hx, hy⟩
  have h := measureReal_mono (μ := percolation d p) hsub (measure_ne_top _ _)
  rw [measureReal_def, percolation_open_bond, ENNReal.toReal_ofReal p.2.1] at h
  exact h

/-- A straight open segment. -/
theorem conn_ray_ge (p : unitInterval) (S : Set (Vertex d)) (x : Vertex d) (i : Fin d) :
    ∀ k : ℕ, (∀ j ≤ k, rayPt x i j ∈ S) →
      (p : ℝ) ^ k ≤ (percolation d p).real (connectionToSetEvent S x {rayPt x i k})
  | 0, h => by
    have hx : x ∈ S := h 0 le_rfl
    have huniv : connectionToSetEvent S x {rayPt x i 0} = Set.univ := by
      ext ω
      simp only [Set.mem_univ, iff_true]
      exact ⟨hx, x, rfl, hx, Reachable.refl _⟩
    rw [huniv, pow_zero]
    simp
  | k+1, h => by
    have ih := conn_ray_ge p S x i k (fun j hj => h j (Nat.le_succ_of_le hj))
    have hstep := conn_step_ge p S (rayPt x i k) i (h k (Nat.le_succ k)) (h (k + 1) le_rfl)
    have hcat := conn_harris_concat p S x (rayPt x i k) (bondTip (rayPt x i k, i))
    have hp0 : (0 : ℝ) ≤ p := p.2.1
    calc (p : ℝ) ^ (k + 1) = (p : ℝ) ^ k * p := pow_succ _ _
      _ ≤ (percolation d p).real (connectionToSetEvent S x {rayPt x i k}) *
          (percolation d p).real
            (connectionToSetEvent S (rayPt x i k) {bondTip (rayPt x i k, i)}) :=
          mul_le_mul ih hstep hp0 measureReal_nonneg
      _ ≤ _ := hcat

/-- A walk that stays in a smaller set is a walk of the smaller restricted graph. -/
lemma reachable_of_walk_in {ω : Configuration d} {S S' : Set (Vertex d)} :
    ∀ {x y : Vertex d} (π : (restrictedGraph ω S).Walk x y), (∀ z ∈ π.support, z ∈ S') →
      (restrictedGraph ω S').Reachable x y := by
  intro x y π
  induction π with
  | nil => exact fun _ => Reachable.refl _
  | @cons x z y hxz π ih =>
    intro h
    have hx : x ∈ S' := h x (by simp)
    have hz : z ∈ S' := h z (by simp)
    have hadj : (restrictedGraph ω S').Adj x z := ⟨hxz.1, hx, hz⟩
    exact hadj.reachable.trans (ih (fun t ht => h t (by simp [ht])))

/-- **Avoiding a finite removed set costs a BK sum.** -/
theorem conn_avoid_lower (p : unitInterval) (S : Set (Vertex d)) (Rm : Finset (Vertex d))
    (a b : Vertex d) :
    (percolation d p).real (connectionToSetEvent S a {b}) ≤
      (percolation d p).real (connectionToSetEvent (S \ (Rm : Set (Vertex d))) a {b}) +
      ∑ w ∈ Rm, (percolation d p).real (connectionToSetEvent S a {w}) *
        (percolation d p).real (connectionToSetEvent S w {b}) := by
  have hsub : connectionToSetEvent S a {b} ⊆
      connectionToSetEvent (S \ (Rm : Set (Vertex d))) a {b} ∪
      ⋃ w ∈ Rm, {ω | DisjointOccurrence (connectionToSetEvent S a {w})
        (connectionToSetEvent S w {b}) ω} := by
    rintro ω ⟨haS, y, hy, hbS, hreach⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨π, hπ⟩ := hreach.exists_isPath
    by_cases hhit : ∃ w ∈ π.support, w ∈ Rm
    · obtain ⟨w, hw, hwR⟩ := hhit
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨w, hwR, disjointOccurrence_of_path_through haS π hπ hw⟩)
    · left
      have hsupp := restrictedWalk_support π haS
      have hgood : ∀ z ∈ π.support, z ∈ S \ (Rm : Set (Vertex d)) :=
        fun z hz => ⟨hsupp z hz, fun hzR => hhit ⟨z, hz, Finset.mem_coe.mp hzR⟩⟩
      exact ⟨hgood a π.start_mem_support, y, rfl, hgood y π.end_mem_support,
        reachable_of_walk_in π hgood⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl ?_))
  refine (measureReal_biUnion_finset_le Rm _).trans (Finset.sum_le_sum (fun w _ => ?_))
  exact percolation_bk d p _ _ (connectionToSetEvent_increasing _ _ _)
    (connectionToSetEvent_increasing _ _ _)

end NearCritical.SplitCrossDirect
end
