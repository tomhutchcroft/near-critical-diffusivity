module

public import NearCritical.SlabUpperGeometry
public import NearCritical.ExplorationDomination

/-! Assembly of source prop.slab.upper (source 6069–6106) from the verified
threshold bridge, slab geometry and exploration domination.

1. Finite-box limit. If for every `N`, with probability at least `θ > 0`, some
   vertex of a fixed finite set `F` is joined inside `S` to a vertex of size `≥ N`,
   then an infinite `S`-cluster exists with probability at least `θ`
   (antitone continuity + pigeonhole on `F`).
2. Bridge. For each `N`, a `RenormalizedExploration` packages the per-box
   renormalisation: the cube/tube blocks `Φ` of the actual percolation
   configuration with product law, the actual tube success rule with the source's
   conditional bound, the deterministic fact that a successful exploration yields a
   slab connection from `F` to size `≥ N`, and the planar mixed site–bond lower
   bound `θ ≤ mixedValue` (where grimmett1999 enters). `exploration_dominates_mixed`
   then gives the `θ` bound of step 1.
3. Source form: `pc(ℤ²×{0..n}^{d-2}) - pc ≤ C n⁻²` for all `n ≥ 1`, from
   renormalised explorations at `p = pc + c n⁻²` for large `n`.

The fields of `RenormalizedExploration` are exactly the inputs still owed by
prop.regular_cube / prop.sprinkling.AB.disjoint and grimmett1999;
nothing about the slab threshold is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set Function
open scoped ENNReal Classical

/-- `ℓ¹` size of a lattice vertex. -/
def vertexSize {d : ℕ} (y : Vertex d) : ℕ := ∑ i, (y i).natAbs

lemma infinite_of_unbounded_vertexSize {d : ℕ} {C : Set (Vertex d)}
    (h : ∀ B : ℕ, ∃ z ∈ C, B ≤ vertexSize z) : C.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image vertexSize).bddAbove
  obtain ⟨z, hz, hBz⟩ := h (B + 1)
  have := hB (Set.mem_image_of_mem vertexSize hz)
  omega

/-- Some vertex of `F` is joined inside `S` to a vertex of size at least `N`. -/
def restrictedReachFarEvent {d : ℕ} (S : Set (Vertex d)) (F : Finset (Vertex d)) (N : ℕ) :
    Set (Configuration d) :=
  {ω | ∃ x ∈ F, ∃ y, N ≤ vertexSize y ∧ (restrictedGraph ω S).Reachable x y}

lemma restrictedReachFarEvent_antitone {d : ℕ} (S : Set (Vertex d)) (F : Finset (Vertex d)) :
    Antitone (restrictedReachFarEvent S F) := by
  rintro N M hNM ω ⟨x, hx, y, hy, hr⟩
  exact ⟨x, hx, y, hNM.trans hy, hr⟩

lemma measurableSet_restrictedReachFarEvent {d : ℕ} (S : Set (Vertex d))
    (F : Finset (Vertex d)) (N : ℕ) : MeasurableSet (restrictedReachFarEvent S F N) := by
  have heq : restrictedReachFarEvent S F N = ⋃ x : Vertex d, ⋃ (_ : x ∈ F), ⋃ y : Vertex d,
      ⋃ (_ : N ≤ vertexSize y), {ω : Configuration d | (restrictedGraph ω S).Reachable x y} := by
    ext ω
    simp [restrictedReachFarEvent]
  rw [heq]
  exact MeasurableSet.iUnion fun x ↦ MeasurableSet.iUnion fun _ ↦
    MeasurableSet.iUnion fun y ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_graphReachable (fun ω ↦ restrictedGraph ω S)
        (measurableSet_restricted_adj S) x y

lemma iInter_restrictedReachFarEvent_subset {d : ℕ} (S : Set (Vertex d))
    (F : Finset (Vertex d)) :
    (⋂ N, restrictedReachFarEvent S F N) ⊆ restrictedSomeInfiniteEvent S := by
  intro ω hω
  have h : ∀ N : ℕ, ∃ x, x ∈ F ∧ ∃ y, N ≤ vertexSize y ∧ (restrictedGraph ω S).Reachable x y := by
    intro N
    obtain ⟨x, hx, y, hy, hr⟩ := mem_iInter.mp hω N
    exact ⟨x, hx, y, hy, hr⟩
  choose x hx y hy hr using h
  obtain ⟨x₀, hfib⟩ := Finite.exists_infinite_fiber (fun N ↦ (⟨x N, hx N⟩ : F))
  have hinf : ((fun N ↦ (⟨x N, hx N⟩ : F)) ⁻¹' {x₀}).Infinite :=
    Set.infinite_coe_iff.mp hfib
  refine ⟨(x₀ : Vertex d), infinite_of_unbounded_vertexSize fun B ↦ ?_⟩
  obtain ⟨N, hN, hBN⟩ := hinf.exists_gt B
  have hN' : (⟨x N, hx N⟩ : F) = x₀ := hN
  have hxN : x N = (x₀ : Vertex d) := congrArg Subtype.val hN'
  refine ⟨y N, ?_, hBN.le.trans (hy N)⟩
  show (restrictedGraph ω S).Reachable (x₀ : Vertex d) (y N)
  rw [← hxN]
  exact hr N

/-- Finite-box limit: uniform-in-`N` far-reach probability forces an infinite
restricted cluster with positive probability. -/
theorem restrictedSomeInfinite_ne_zero_of_reachFar {d : ℕ} (p : unitInterval)
    (S : Set (Vertex d)) (F : Finset (Vertex d)) {θ : ℝ≥0∞} (hθ : θ ≠ 0)
    (h : ∀ N, θ ≤ percolation d p (restrictedReachFarEvent S F N)) :
    percolation d p (restrictedSomeInfiniteEvent S) ≠ 0 := by
  have hInter : percolation d p (⋂ N, restrictedReachFarEvent S F N) =
      ⨅ N, percolation d p (restrictedReachFarEvent S F N) :=
    (restrictedReachFarEvent_antitone S F).measure_iInter
      (fun N ↦ (measurableSet_restrictedReachFarEvent S F N).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have hle : θ ≤ percolation d p (restrictedSomeInfiniteEvent S) := by
    calc θ ≤ ⨅ N, percolation d p (restrictedReachFarEvent S F N) := le_iInf h
      _ = percolation d p (⋂ N, restrictedReachFarEvent S F N) := hInter.symm
      _ ≤ _ := measure_mono (iInter_restrictedReachFarEvent_subset S F)
  intro h0
  rw [h0] at hle
  exact hθ (nonpos_iff_eq_zero.mp hle)

/-- Bridge: a renormalised exploration whose success yields far reach gives the
mixed site–bond lower bound for the far-reach probability. -/
theorem reachFar_ge_of_exploration {d : ℕ} (S : Set (Vertex d)) (F : Finset (Vertex d))
    (N : ℕ) (p : unitInterval)
    {Vx Ed : Type*} [Fintype Vx] [DecidableEq Vx] [Fintype Ed] [DecidableEq Ed]
    (ends : Ed → Vx × Vx) (o : Vx) (D : Finset Vx)
    {Ω : Vx ⊕ Ed → Type*} [∀ i, MeasurableSpace (Ω i)] (ν : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (ν i)] [∀ i, Nonempty (Ω i)]
    (κ : Measure Bool) [IsProbabilityMeasure κ]
    (Φ : Configuration d → ∀ i, Ω i) (hΦ : Measurable Φ)
    (hmap : Measure.map Φ (percolation d p) = Measure.pi ν)
    (succ : ExploreState Vx Ed → (∀ i, Ω i) → Bool)
    (hlocal : ∀ σ i (x x' : ∀ j, Ω j), ExploreInv ends o σ → exploreQuery ends o σ = some i →
      (∀ j ∈ insert i (exploreRevealed σ), x j = x' j) → succ σ x = succ σ x')
    (hmeas : ∀ σ, Measurable (succ σ))
    (hprob : ∀ σ i (x : ∀ j, Ω j), ExploreInv ends o σ → exploreQuery ends o σ = some i →
      κ {true} ≤ ν i {y | succ σ (update x i y) = true})
    (hgood : ∀ ω, explorePayoff D (adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ
      (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ (Φ ω)) ≠ 0 →
        ω ∈ restrictedReachFarEvent S F N) :
    mixedValue ends o D κ ⟨∅, ∅, ∅, ∅, ∅⟩ ≤ percolation d p (restrictedReachFarEvent S F N) := by
  have hf := measurable_payoff_adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ
    (explorePayoff D) hmeas (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩
  calc mixedValue ends o D κ ⟨∅, ∅, ∅, ∅, ∅⟩
      ≤ ∫⁻ x, explorePayoff D (adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ
          (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ x) ∂Measure.pi ν :=
        exploration_dominates_mixed ends o D ν κ succ hlocal hmeas hprob
    _ = ∫⁻ ω, explorePayoff D (adaptiveRun (exploreQuery ends o) (exploreNext ends o) succ
          (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ (Φ ω)) ∂percolation d p := by
        rw [← hmap, lintegral_map hf hΦ]
    _ ≤ ∫⁻ ω, (restrictedReachFarEvent S F N).indicator 1 ω ∂percolation d p := by
        refine lintegral_mono fun ω ↦ ?_
        try dsimp only
        by_cases h0 : explorePayoff D (adaptiveRun (exploreQuery ends o) (exploreNext ends o)
            succ (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ (Φ ω)) = 0
        · rw [h0]
          exact zero_le
        · rw [Set.indicator_of_mem (hgood ω h0), Pi.one_apply]
          unfold explorePayoff
          split_ifs <;> simp
    _ = _ := lintegral_indicator_one (measurableSet_restrictedReachFarEvent S F N)

/-- Per-box renormalisation data for prop.slab.upper at parameter `p`: the inputs
owed by prop.regular_cube / prop.sprinkling.AB.disjoint (block law, tube success
rule with the source's conditional bound, nest-chain semantics) and grimmett1999
(`mixed_ge`). -/
structure RenormalizedExploration (d : ℕ) (p : unitInterval) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (N : ℕ) (θ : ℝ≥0∞) where
  Vx : Type
  Ed : Type
  [fintypeVx : Fintype Vx]
  [decEqVx : DecidableEq Vx]
  [fintypeEd : Fintype Ed]
  [decEqEd : DecidableEq Ed]
  ends : Ed → Vx × Vx
  root : Vx
  target : Finset Vx
  Ω : Vx ⊕ Ed → Type
  [measΩ : ∀ i, MeasurableSpace (Ω i)]
  ν : ∀ i, Measure (Ω i)
  [probν : ∀ i, IsProbabilityMeasure (ν i)]
  [nonemptyΩ : ∀ i, Nonempty (Ω i)]
  κ : Measure Bool
  [probκ : IsProbabilityMeasure κ]
  Φ : Configuration d → ∀ i, Ω i
  measurable_Φ : Measurable Φ
  map_Φ : Measure.map Φ (percolation d p) = Measure.pi ν
  succ : ExploreState Vx Ed → (∀ i, Ω i) → Bool
  local_succ : ∀ σ i (x x' : ∀ j, Ω j), ExploreInv ends root σ →
    exploreQuery ends root σ = some i →
      (∀ j ∈ insert i (exploreRevealed σ), x j = x' j) → succ σ x = succ σ x'
  measurable_succ : ∀ σ, Measurable (succ σ)
  prob_succ : ∀ σ i (x : ∀ j, Ω j), ExploreInv ends root σ →
    exploreQuery ends root σ = some i → κ {true} ≤ ν i {y | succ σ (update x i y) = true}
  good : ∀ ω, explorePayoff target (adaptiveRun (exploreQuery ends root)
    (exploreNext ends root) succ (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ (Φ ω)) ≠ 0 →
      ω ∈ restrictedReachFarEvent S F N
  mixed_ge : θ ≤ mixedValue ends root target κ ⟨∅, ∅, ∅, ∅, ∅⟩

theorem RenormalizedExploration.reachFar_ge {d : ℕ} {p : unitInterval} {S : Set (Vertex d)}
    {F : Finset (Vertex d)} {N : ℕ} {θ : ℝ≥0∞} (M : RenormalizedExploration d p S F N θ) :
    θ ≤ percolation d p (restrictedReachFarEvent S F N) := by
  letI := M.fintypeVx
  letI := M.decEqVx
  letI := M.fintypeEd
  letI := M.decEqEd
  letI := M.measΩ
  letI := M.probν
  letI := M.nonemptyΩ
  letI := M.probκ
  exact M.mixed_ge.trans (reachFar_ge_of_exploration S F N p M.ends M.root M.target M.ν M.κ
    M.Φ M.measurable_Φ M.map_Φ M.succ M.local_succ M.measurable_succ M.prob_succ M.good)

/-- prop.slab.upper at one parameter: renormalised explorations for every box size
place the actual slab critical point at or below `p`. -/
theorem slab_critical_le_of_renormalized_exploration (d k n : ℕ) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (F : Finset (Vertex d)) {θ : ℝ≥0∞} (hθ : θ ≠ 0)
    (M : ∀ N, RenormalizedExploration d p (slabVertices d k n) F N θ) :
    restrictedCriticalPoint d (slabVertices d k n) ≤ p :=
  slab_restrictedCriticalPoint_le_of_someInfinite d k n p hp
    (restrictedSomeInfinite_ne_zero_of_reachFar p _ F hθ fun N ↦ (M N).reachFar_ge)

/-- Source prop.slab.upper: if renormalised explorations exist at
`p = pc + c n⁻²` for all large `n`, then
`pc(ℤ² × {0,…,n}^{d-2}) - pc ≤ C n⁻²` for every `n ≥ 1`. -/
theorem slab_upper_inverse_square {d : ℕ} {c : ℝ} (hc : 0 < c) (n₀ : ℕ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : unitInterval,
      (p : ℝ) = (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 →
        ∃ (F : Finset (Vertex d)) (θ : ℝ≥0∞), θ ≠ 0 ∧
          ∀ N, Nonempty (RenormalizedExploration d p (slabVertices d 2 n) F N θ)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        C / (n : ℝ) ^ 2 := by
  refine ⟨max c ((n₀ : ℝ) ^ 2), fun n hn ↦ ?_⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn' 2
  have hpc0 : (0 : ℝ) ≤ criticalPoint d := (criticalPoint d).2.1
  have hs1 : (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) ≤ 1 :=
    (restrictedCriticalPoint d (slabVertices d 2 n)).2.2
  have hcC : c / (n : ℝ) ^ 2 ≤ max c ((n₀ : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
    gcongr
    exact le_max_left _ _
  by_cases hn0 : n₀ ≤ n
  · by_cases hle : (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 ≤ 1
    · have hv0 : 0 ≤ (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 :=
        add_nonneg hpc0 (div_nonneg hc.le hnpos.le)
      let p : unitInterval := ⟨(criticalPoint d : ℝ) + c / (n : ℝ) ^ 2, hv0, hle⟩
      obtain ⟨F, θ, hθ, hM⟩ := hmodel n hn0 hn p rfl
      have hp : 0 < (p : ℝ) := add_pos_of_nonneg_of_pos hpc0 (div_pos hc hnpos)
      have hcrit := slab_critical_le_of_renormalized_exploration d 2 n p hp F hθ
        (fun N ↦ (hM N).some)
      have hv : (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) ≤
          (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 := Subtype.coe_le_coe.mpr hcrit
      linarith
    · push_neg at hle
      linarith
  · have hnn : (n : ℝ) ≤ n₀ := by exact_mod_cast (Nat.le_of_lt (not_le.mp hn0))
    have hsq : (n : ℝ) ^ 2 ≤ (n₀ : ℝ) ^ 2 := by gcongr
    have h1 : (1 : ℝ) ≤ (n₀ : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
      rw [le_div_iff₀ hnpos]
      linarith
    have hC : (n₀ : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ max c ((n₀ : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
      gcongr
      exact le_max_right _ _
    linarith

end NearCritical
