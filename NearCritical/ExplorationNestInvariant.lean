module

public import NearCritical.ExplorationNestRule
public import NearCritical.SlabUpperMemoryCoupled

/-! Semantic invariant of the history-based nest rule, and the resulting
far-reach bound.

`nestRun_invariant`: fix a sample `x` and a predicate `Q v ℓ` on (site, nest)
that holds for the root nest and is propagated by `childNest` from the parent's
nest. Then along the run of the exploration with memory every explored site `v`
carries a recomputed nest `ℓ` with `Q v ℓ`. (Source 6097-6099: every nest of the
exploration has a cluster joined to the root nest.)

`reachFar_ge_of_nestRule`: for a coupled block sample, a `NestRule` whose rule
`nestSucc` satisfies the per-step bound, and a `Q` as above that forces the
far-reach event at target sites, `θ <= P_p[reach far]`. Locality, measurability
and the history invariant are discharged by `ExplorationNestRule`; the ONLY
probabilistic hypotheses left are the three per-step bounds (root, site, and edge
for every parent nest), assembled by `nestSucc_prob_of_parts`.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Function
open scoped ENNReal Classical

section
variable {Vx Ed : Type} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
variable (ends : Ed → Vx × Vx) (o : Vx)
variable {Ω : Vx ⊕ Ed → Type} {L : Type}

lemma otherEnd_mem {σ : ExploreState Vx Ed} {e : Ed} {z : Vx}
    (hm : exploreMove ends o σ = some (.edge e z)) : otherEnd ends e z ∈ σ.A := by
  obtain ⟨-, -, hc, hfar⟩ := exploreMove_edge ends o hm
  obtain ⟨-, -, hor, hfA, -⟩ := hc
  unfold exploreFar at hfar hfA
  unfold otherEnd
  by_cases h1 : (ends e).1 ∈ σ.A
  · rw [if_pos h1] at hfar hfA
    have hne : (ends e).1 ≠ z := fun h => hfA (by rw [hfar, ← h]; exact h1)
    rw [if_neg hne]
    exact h1
  · rw [if_neg h1] at hfar hfA
    rw [if_pos hfar]
    exact hor.resolve_left h1

/-- The target of an actual edge move is an endpoint of that edge. -/
lemma exploreMove_edge_target {σ : ExploreState Vx Ed} {e : Ed} {z : Vx}
    (hm : exploreMove ends o σ = some (.edge e z)) : z = (ends e).1 ∨ z = (ends e).2 := by
  obtain ⟨_, _, _, hfar⟩ := exploreMove_edge ends o hm
  rw [← hfar]
  unfold exploreFar
  split <;> simp

theorem nestRun_invariant [∀ i, MeasurableSpace (Ω i)] (Ru : NestRule Vx Ed o Ω L)
    (x : ∀ i, Ω i) (Q : Vx → L → Prop)
    (hrootQ : ∀ ℓ, Ru.rootNest x = some ℓ → Q o ℓ)
    (hrootsite : ∀ ℓ, Ru.rootNest x = some ℓ → Ru.siteOK o x = true)
    (hedgeQ : ∀ e z ℓ ℓ', (z = (ends e).1 ∨ z = (ends e).2) →
      Ru.siteOK z x = true → Q (otherEnd ends e z) ℓ →
      Ru.childNest e z ℓ x = some ℓ' → Q z ℓ') :
    ∀ (n : ℕ) (s : ExploreState Vx Ed × Hist Vx Ed),
      ((∀ v ∈ s.1.A, ∃ ℓ, nestsOf ends o Ru s.2 x v = some ℓ ∧ Q v ℓ) ∧
        ∀ z ∈ s.1.Reg, Ru.siteOK z x = true) →
      ∀ v ∈ (adaptiveRun (fun s : ExploreState Vx Ed × Hist Vx Ed => exploreQuery ends o s.1)
          (fun s b => (exploreNext ends o s.1 b, nextHist ends o s.1 s.2 b))
          (nestSucc ends o Ru) n s x).1.A,
        ∃ ℓ, nestsOf ends o Ru
          (adaptiveRun (fun s : ExploreState Vx Ed × Hist Vx Ed => exploreQuery ends o s.1)
            (fun s b => (exploreNext ends o s.1 b, nextHist ends o s.1 s.2 b))
            (nestSucc ends o Ru) n s x).2 x v = some ℓ ∧ Q v ℓ := by
  intro n
  induction n with
  | zero =>
    intro s hK
    exact hK.1
  | succ n ih =>
    intro s hK
    cases hq : exploreQuery ends o s.1 with
    | none =>
      rw [adaptiveRun_succ_of_none
        (query := fun s : ExploreState Vx Ed × Hist Vx Ed => exploreQuery ends o s.1) (σ := s) hq]
      exact hK.1
    | some i =>
      rw [adaptiveRun_succ_of_some
        (query := fun s : ExploreState Vx Ed × Hist Vx Ed => exploreQuery ends o s.1) (σ := s) hq]
      apply ih
      obtain ⟨m, hm, -⟩ := exploreQuery_eq_some ends o hq
      have hH : ∀ b, nextHist ends o s.1 s.2 b = (m, b) :: s.2 := fun b => by
        unfold nextHist
        rw [hm]
      refine ⟨?_, ?_⟩
      · intro v hv
        change v ∈ (exploreNext ends o s.1 (nestSucc ends o Ru s x)).A at hv
        change ∃ ℓ, nestsOf ends o Ru (nextHist ends o s.1 s.2 (nestSucc ends o Ru s x)) x v =
          some ℓ ∧ Q v ℓ
        rw [hH]
        change ∃ ℓ, nestStep ends o Ru x (nestsOf ends o Ru s.2 x)
          (m, nestSucc ends o Ru s x) v = some ℓ ∧ Q v ℓ
        cases hb : nestSucc ends o Ru s x
        · rw [hb] at hv
          have hvA : v ∈ s.1.A := by
            cases m <;> simpa [exploreNext, hm] using hv
          have hstep : nestStep ends o Ru x (nestsOf ends o Ru s.2 x) (m, false) =
              nestsOf ends o Ru s.2 x := by
            cases m <;> rfl
          rw [hstep]
          exact hK.1 v hvA
        · rw [hb] at hv
          cases m with
          | root =>
            have hv' : v = o ∨ v ∈ s.1.A := by simpa [exploreNext, hm] using hv
            have hsome : (Ru.rootNest x).isSome = true := by
              have h := hb
              unfold nestSucc at h
              simpa [hm] using h
            obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp hsome
            change ∃ ℓ, Function.update (nestsOf ends o Ru s.2 x) o (Ru.rootNest x) v = some ℓ ∧
              Q v ℓ
            by_cases hvo : v = o
            · rw [hvo, Function.update_self]
              exact ⟨ℓ, hℓ, hrootQ ℓ hℓ⟩
            · rw [Function.update_of_ne hvo]
              exact hK.1 v (hv'.resolve_left hvo)
          | site z =>
            have hvA : v ∈ s.1.A := by simpa [exploreNext, hm] using hv
            exact hK.1 v hvA
          | edge e z =>
            have hv' : v = z ∨ v ∈ s.1.A := by simpa [exploreNext, hm] using hv
            obtain ⟨ℓ, hℓ, hQ⟩ := hK.1 _ (otherEnd_mem ends o hm)
            have hzsite := hK.2 z (exploreMove_edge ends o hm).2.1
            have hsome : (Ru.childNest e z ℓ x).isSome = true := by
              have h := hb
              unfold nestSucc at h
              simpa [hm, hℓ] using h
            obtain ⟨ℓ', hℓ'⟩ := Option.isSome_iff_exists.mp hsome
            change ∃ ℓ'', Function.update (nestsOf ends o Ru s.2 x) z
              ((nestsOf ends o Ru s.2 x (otherEnd ends e z)).bind
                fun ℓ => Ru.childNest e z ℓ x) v = some ℓ'' ∧ Q v ℓ''
            by_cases hvz : v = z
            · rw [hvz, Function.update_self, hℓ]
              exact ⟨ℓ', hℓ', hedgeQ e z ℓ ℓ' (exploreMove_edge_target ends o hm) hzsite hQ hℓ'⟩
            · rw [Function.update_of_ne hvz]
              exact hK.1 v (hv'.resolve_left hvz)
      · intro w hw
        change w ∈ (exploreNext ends o s.1 (nestSucc ends o Ru s x)).Reg at hw
        cases hb : nestSucc ends o Ru s x
        · rw [hb] at hw
          have hwR : w ∈ s.1.Reg := by
            cases m <;> simpa [exploreNext, hm] using hw
          exact hK.2 w hwR
        · rw [hb] at hw
          cases m with
          | root =>
            have hw' : w = o ∨ w ∈ s.1.Reg := by simpa [exploreNext, hm] using hw
            rcases hw' with rfl | hwR
            · have hsome : (Ru.rootNest x).isSome = true := by
                have h := hb
                unfold nestSucc at h
                simpa [hm] using h
              obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp hsome
              exact hrootsite ℓ hℓ
            · exact hK.2 w hwR
          | site z =>
            have hw' : w = z ∨ w ∈ s.1.Reg := by simpa [exploreNext, hm] using hw
            rcases hw' with rfl | hwR
            · have h := hb
              unfold nestSucc at h
              simpa [hm] using h
            · exact hK.2 w hwR
          | edge e z =>
            have hwR : w ∈ s.1.Reg := by simpa [exploreNext, hm] using hw
            exact hK.2 w hwR

/-- The per-step bound of `nestSucc` from separate root, site and edge bounds.
The edge bound is required for every parent nest `ℓ` and every sample. -/
theorem nestSucc_prob_of_parts [∀ i, MeasurableSpace (Ω i)] (Ru : NestRule Vx Ed o Ω L)
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)] (κ : Measure Bool)
    [IsProbabilityMeasure κ]
    (proot : ∀ x : ∀ j, Ω j,
      κ {true} ≤ ν (Sum.inl o) {y | (Ru.rootNest (update x (Sum.inl o) y)).isSome = true})
    (psite : ∀ z (x : ∀ j, Ω j),
      κ {true} ≤ ν (Sum.inl z) {y | Ru.siteOK z (update x (Sum.inl z) y) = true})
    (pedge : ∀ e z ℓ (x : ∀ j, Ω j),
      κ {true} ≤ ν (Sum.inr e) {y | (Ru.childNest e z ℓ (update x (Sum.inr e) y)).isSome = true})
    (σ : ExploreState Vx Ed) (h : Hist Vx Ed) (i : Vx ⊕ Ed) (x : ∀ j, Ω j)
    (hI : histOK o (σ, h)) (hq : exploreQuery ends o σ = some i) :
    κ {true} ≤ ν i {y | nestSucc ends o Ru (σ, h) (update x i y) = true} := by
  have hnot := exploreQuery_notMem ends o hq
  obtain ⟨m, hm, rfl⟩ := exploreQuery_eq_some ends o hq
  cases m with
  | root =>
    change κ {true} ≤ ν (Sum.inl o) {y | nestSucc ends o Ru (σ, h) (update x (Sum.inl o) y) = true}
    have hset : {y | nestSucc ends o Ru (σ, h) (update x (Sum.inl o) y) = true} =
        {y | (Ru.rootNest (update x (Sum.inl o) y)).isSome = true} := by
      ext y
      unfold nestSucc
      simp [hm]
    rw [hset]
    exact proot x
  | site z =>
    change κ {true} ≤ ν (Sum.inl z) {y | nestSucc ends o Ru (σ, h) (update x (Sum.inl z) y) = true}
    have hset : {y | nestSucc ends o Ru (σ, h) (update x (Sum.inl z) y) = true} =
        {y | Ru.siteOK z (update x (Sum.inl z) y) = true} := by
      ext y
      unfold nestSucc
      simp [hm]
    rw [hset]
    exact psite z x
  | edge e z =>
    change κ {true} ≤ ν (Sum.inr e) {y | nestSucc ends o Ru (σ, h) (update x (Sum.inr e) y) = true}
    have hN : ∀ y, nestsOf ends o Ru h (update x (Sum.inr e) y) = nestsOf ends o Ru h x :=
      fun y => nestsOf_congr ends o Ru σ _ _
        (fun j hj => Function.update_of_ne
          (fun hje : j = Sum.inr e => hnot (by rw [hje] at hj; exact hj)) _ _) h hI
    cases hpar : nestsOf ends o Ru h x (otherEnd ends e z) with
    | none =>
      have hset : {y | nestSucc ends o Ru (σ, h) (update x (Sum.inr e) y) = true} = Set.univ := by
        ext y
        unfold nestSucc
        simp [hm, hN y, hpar]
      rw [hset, measure_univ]
      exact prob_le_one
    | some ℓ =>
      have hset : {y | nestSucc ends o Ru (σ, h) (update x (Sum.inr e) y) = true} =
          {y | (Ru.childNest e z ℓ (update x (Sum.inr e) y)).isSome = true} := by
        ext y
        unfold nestSucc
        simp [hm, hN y, hpar]
      rw [hset]
      exact pedge e z ℓ x

end

theorem reachFar_ge_of_nestRule {d : ℕ} {p : unitInterval}
    {S : Set (Vertex d)} {F : Finset (Vertex d)} {N : ℕ} {θ : ℝ≥0∞}
    {Vx Ed : Type} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
    (ends : Ed → Vx × Vx) (root : Vx) (target : Finset Vx)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (P : Measure Ω₀) [IsProbabilityMeasure P]
    (cfg : Ω₀ → Configuration d) (measurable_cfg : Measurable cfg)
    (map_cfg : Measure.map cfg P = percolation d p)
    {Ω : Vx ⊕ Ed → Type} [∀ i, MeasurableSpace (Ω i)] [∀ i, Countable (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)] [∀ i, Nonempty (Ω i)]
    (κ : Measure Bool) [IsProbabilityMeasure κ]
    (Φ : Ω₀ → ∀ i, Ω i) (measurable_Φ : Measurable Φ)
    (map_Φ : Measure.map Φ P = Measure.pi ν)
    {L : Type} (Ru : NestRule Vx Ed root Ω L)
    (proot : ∀ x : ∀ j, Ω j,
      κ {true} ≤ ν (Sum.inl root) {y | (Ru.rootNest (update x (Sum.inl root) y)).isSome = true})
    (psite : ∀ z (x : ∀ j, Ω j),
      κ {true} ≤ ν (Sum.inl z) {y | Ru.siteOK z (update x (Sum.inl z) y) = true})
    (pedge : ∀ e z ℓ (x : ∀ j, Ω j),
      κ {true} ≤ ν (Sum.inr e) {y | (Ru.childNest e z ℓ (update x (Sum.inr e) y)).isSome = true})
    (Q : Ω₀ → Vx → L → Prop)
    (hrootQ : ∀ ω₀ ℓ, Ru.rootNest (Φ ω₀) = some ℓ → Q ω₀ root ℓ)
    (hrootsite : ∀ ω₀ ℓ, Ru.rootNest (Φ ω₀) = some ℓ → Ru.siteOK root (Φ ω₀) = true)
    (hedgeQ : ∀ ω₀ e z ℓ ℓ', (z = (ends e).1 ∨ z = (ends e).2) →
      Ru.siteOK z (Φ ω₀) = true → Q ω₀ (otherEnd ends e z) ℓ →
      Ru.childNest e z ℓ (Φ ω₀) = some ℓ' → Q ω₀ z ℓ')
    (hfar : ∀ ω₀ v ℓ, v ∈ target → Q ω₀ v ℓ → cfg ω₀ ∈ restrictedReachFarEvent S F N)
    (mixed_ge : θ ≤ mixedValue ends root target κ ⟨∅, ∅, ∅, ∅, ∅⟩) :
    θ ≤ percolation d p (restrictedReachFarEvent S F N) := by
  refine reachFar_ge_of_memory_exploration ends root target P cfg measurable_cfg map_cfg ν κ Φ
    measurable_Φ map_Φ (nextHist ends root) ([] : Hist Vx Ed) (histOK root) (histOK_nil root)
    (fun σ h i b _ hI hq => histOK_next ends root σ h i b hI hq)
    (nestSucc ends root Ru)
    (fun σ h i x x' _ hI hq hx => nestSucc_local ends root Ru σ h i x x' hI hq hx)
    (nestSucc_measurable ends root Ru)
    (fun σ h i x _ hI hq => nestSucc_prob_of_parts ends root Ru ν κ proot psite pedge σ h i x hI hq)
    ?_ mixed_ge
  intro ω₀ hpay
  have hall := nestRun_invariant ends root Ru (Φ ω₀) (Q ω₀) (hrootQ ω₀) (hrootsite ω₀) (hedgeQ ω₀)
    (Fintype.card (Vx ⊕ Ed)) ((⟨∅, ∅, ∅, ∅, ∅⟩ : ExploreState Vx Ed), ([] : Hist Vx Ed))
    (by simp)
  unfold explorePayoff at hpay
  split_ifs at hpay with hne
  · obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_inter] at hv
    obtain ⟨ℓ, -, hQ⟩ := hall v hv.1
    exact hfar ω₀ v ℓ hv.2 hQ
  · exact absurd rfl hpay

end NearCritical
