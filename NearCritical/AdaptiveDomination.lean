module

public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Adaptive query domination, the probabilistic core of the stochastic
domination step in source prop.slab.upper (source 6094–6097: "an attempt ...
succeeds with conditional probability at least `1-ε`, whatever has been revealed
before ... hence the set of explored sites stochastically dominates ...").

Abstract setting. Independent coordinates `x i ∈ Ω i` with law `Measure.pi ν`.
An adaptive rule, in combinatorial state `σ`, either stops (`query σ = none`) or
queries a not-yet-revealed coordinate `i`; the outcome is a success bit
`succ σ x`, which may depend on the revealed coordinates and on `x i` only, and
has conditional success probability at least `q` given ANY values of the
revealed coordinates. The state then moves to `next σ bit`.

Comparison. Any value function `V` on states with
* `V σ ≤ q·V(next σ true) + (1-q)·V(next σ false)` (one fresh `q`-coin step),
* `V(next σ false) ≤ V(next σ true)` (monotonicity),
* `V σ ≤ payoff σ` at stopping states,
is dominated by the expected payoff of the adaptive run. Instantiated with
`V = ` mixed site–bond percolation probabilities, this is the domination.

The proof conditions on the revealed coordinates through `lmarginal` and peels
off the queried coordinate with `lmarginal_insert`; no filtration, conditional
expectation or extra randomisation is used. Pure Mathlib. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Function Finset
open scoped ENNReal Classical

section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)] {S : Type*}

/-- Run an adaptive query rule for at most `n` steps. -/
def adaptiveRun (query : S → Option ι) (next : S → Bool → S)
    (succ : S → (∀ i, Ω i) → Bool) : ℕ → S → (∀ i, Ω i) → S
  | 0, σ, _ => σ
  | n + 1, σ, x =>
    match query σ with
    | none => σ
    | some _ => adaptiveRun query next succ n (next σ (succ σ x)) x

@[simp] lemma adaptiveRun_zero {query : S → Option ι} {next : S → Bool → S}
    {succ : S → (∀ i, Ω i) → Bool} {σ : S} {x : ∀ i, Ω i} :
    adaptiveRun query next succ 0 σ x = σ := by
  simp [adaptiveRun]

lemma adaptiveRun_succ_of_none {query : S → Option ι} {next : S → Bool → S}
    {succ : S → (∀ i, Ω i) → Bool} {n : ℕ} {σ : S} {x : ∀ i, Ω i}
    (h : query σ = none) : adaptiveRun query next succ (n + 1) σ x = σ := by
  simp [adaptiveRun, h]

lemma adaptiveRun_succ_of_some {query : S → Option ι} {next : S → Bool → S}
    {succ : S → (∀ i, Ω i) → Bool} {n : ℕ} {σ : S} {i : ι} {x : ∀ i, Ω i}
    (h : query σ = some i) :
    adaptiveRun query next succ (n + 1) σ x =
      adaptiveRun query next succ n (next σ (succ σ x)) x := by
  simp [adaptiveRun, h]

lemma measurable_payoff_adaptiveRun (query : S → Option ι) (next : S → Bool → S)
    (succ : S → (∀ i, Ω i) → Bool) (payoff : S → ℝ≥0∞)
    (hmeas : ∀ σ, Measurable (succ σ)) (n : ℕ) (σ : S) :
    Measurable (fun x ↦ payoff (adaptiveRun query next succ n σ x)) := by
  induction n generalizing σ with
  | zero =>
    simp only [adaptiveRun_zero]
    exact measurable_const
  | succ n ih =>
    cases hq : query σ with
    | none =>
      have hc : (fun x ↦ payoff (adaptiveRun query next succ (n + 1) σ x)) =
          fun _ ↦ payoff σ := by
        funext x
        rw [adaptiveRun_succ_of_none hq]
      rw [hc]
      exact measurable_const
    | some i =>
      have hs : MeasurableSet {x : ∀ i, Ω i | succ σ x = true} :=
        hmeas σ (measurableSet_singleton true)
      have heq : (fun x ↦ payoff (adaptiveRun query next succ (n + 1) σ x)) =
          Set.piecewise {x : ∀ i, Ω i | succ σ x = true}
            (fun x ↦ payoff (adaptiveRun query next succ n (next σ true) x))
            (fun x ↦ payoff (adaptiveRun query next succ n (next σ false) x)) := by
        funext x
        rw [adaptiveRun_succ_of_some hq]
        by_cases hx : succ σ x = true
        · simp [Set.piecewise, hx]
        · simp [Set.piecewise, hx]
      rw [heq]
      exact Measurable.piecewise hs (ih _) (ih _)

lemma lmarginal_const_of_prob (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (s : Finset ι) (c : ℝ≥0∞) (x : ∀ i, Ω i) :
    lmarginal ν s (fun _ ↦ c) x = c := by
  simp [lmarginal, lintegral_const, measure_univ]

/-- `lmarginal` only sees the integrand at points agreeing with `x` off `s`. -/
lemma lmarginal_congr_on (ν : ∀ i, Measure (Ω i)) {s : Finset ι}
    {f g : (∀ i, Ω i) → ℝ≥0∞} {x : ∀ i, Ω i}
    (h : ∀ z : ∀ i, Ω i, (∀ j ∉ s, z j = x j) → f z = g z) :
    lmarginal ν s f x = lmarginal ν s g x := by
  unfold lmarginal
  refine lintegral_congr fun w ↦ h _ fun j hj ↦ ?_
  simp [updateFinset_def, hj]

/-- One fresh `q`-coin step against an actual success set of conditional mass at
least `q`, for a monotone two-valued continuation. -/
lemma step_value_le_lintegral {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) {q VT VF : ℝ≥0∞} (hq : q ≤ 1)
    (hm : VF ≤ VT) (hp : q ≤ ν A) :
    q * VT + (1 - q) * VF ≤ ∫⁻ y, A.indicator (fun _ ↦ VT) y + Aᶜ.indicator (fun _ ↦ VF) y ∂ν := by
  have hfun : (fun y ↦ A.indicator (fun _ ↦ VT) y + Aᶜ.indicator (fun _ ↦ VF) y) =
      fun y ↦ VF + A.indicator (fun _ ↦ VT - VF) y := by
    funext y
    by_cases hy : y ∈ A
    · simp [Set.indicator, hy, add_tsub_cancel_of_le hm]
    · simp [Set.indicator, hy]
  rw [hfun, lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_indicator_const hA]
  calc q * VT + (1 - q) * VF = q * (VF + (VT - VF)) + (1 - q) * VF := by
        rw [add_tsub_cancel_of_le hm]
    _ = (q + (1 - q)) * VF + q * (VT - VF) := by ring
    _ = VF + q * (VT - VF) := by rw [add_tsub_cancel_of_le hq, one_mul]
    _ ≤ VF + (VT - VF) * ν A := by
        rw [mul_comm q]
        gcongr

/-- Conditional form: for every state and every value of the revealed coordinates,
the conditional expected payoff of the adaptive run dominates `V`. -/
theorem adaptive_domination_lmarginal
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (revealed : S → Finset ι) (query : S → Option ι) (next : S → Bool → S)
    (succ : S → (∀ i, Ω i) → Bool) (Inv : S → Prop) (V payoff : S → ℝ≥0∞)
    {q : ℝ≥0∞} (hq : q ≤ 1)
    (hquery : ∀ σ i, Inv σ → query σ = some i → i ∉ revealed σ)
    (hrev : ∀ σ i b, Inv σ → query σ = some i →
      revealed (next σ b) = insert i (revealed σ))
    (hinv : ∀ σ i b, Inv σ → query σ = some i → Inv (next σ b))
    (hlocal : ∀ σ i (x x' : ∀ j, Ω j), Inv σ → query σ = some i →
      (∀ j ∈ insert i (revealed σ), x j = x' j) → succ σ x = succ σ x')
    (hmeas : ∀ σ, Measurable (succ σ))
    (hprob : ∀ σ i (x : ∀ j, Ω j), Inv σ → query σ = some i →
      q ≤ ν i {y | succ σ (update x i y) = true})
    (hstep : ∀ σ i, Inv σ → query σ = some i →
      V σ ≤ q * V (next σ true) + (1 - q) * V (next σ false))
    (hmono : ∀ σ i, Inv σ → query σ = some i → V (next σ false) ≤ V (next σ true))
    (hterm : ∀ σ, Inv σ → query σ = none → V σ ≤ payoff σ) :
    ∀ (n : ℕ) (σ : S), Inv σ → Fintype.card ι ≤ n + (revealed σ).card →
      ∀ x : ∀ i, Ω i, V σ ≤ lmarginal ν (univ \ revealed σ)
        (fun z ↦ payoff (adaptiveRun query next succ n σ z)) x := by
  intro n
  induction n with
  | zero =>
    intro σ hσ hcard x
    have hfull : revealed σ = univ := by
      apply Finset.eq_univ_of_card
      exact le_antisymm (Finset.card_le_univ _) (by simpa using hcard)
    have hnone : query σ = none := by
      cases h : query σ with
      | none => rfl
      | some i =>
        exact (hquery σ i hσ h (by rw [hfull]; exact mem_univ i)).elim
    rw [hfull]
    simp only [sdiff_self, Finset.bot_eq_empty, lmarginal_empty, adaptiveRun_zero]
    exact hterm σ hσ hnone
  | succ n ih =>
    intro σ hσ hcard x
    cases hqσ : query σ with
    | none =>
      have hc : (fun z ↦ payoff (adaptiveRun query next succ (n + 1) σ z)) =
          fun _ ↦ payoff σ := by
        funext z
        rw [adaptiveRun_succ_of_none hqσ]
      rw [hc, lmarginal_const_of_prob]
      exact hterm σ hσ hqσ
    | some i =>
      have hiR : i ∉ revealed σ := hquery σ i hσ hqσ
      have hU : univ \ revealed σ = insert i (univ \ insert i (revealed σ)) := by
        ext j
        by_cases hj : j = i
        · simp [hj, hiR]
        · simp [hj]
      have hiU : i ∉ univ \ insert i (revealed σ) := by simp
      have hmf := measurable_payoff_adaptiveRun query next succ payoff hmeas (n + 1) σ
      rw [hU, lmarginal_insert _ hmf hiU]
      have hinner : ∀ y : Ω i, V (next σ (succ σ (update x i y))) ≤
          lmarginal ν (univ \ insert i (revealed σ))
            (fun z ↦ payoff (adaptiveRun query next succ (n + 1) σ z)) (update x i y) := by
        intro y
        have hcongr : lmarginal ν (univ \ insert i (revealed σ))
              (fun z ↦ payoff (adaptiveRun query next succ (n + 1) σ z)) (update x i y) =
            lmarginal ν (univ \ insert i (revealed σ))
              (fun z ↦ payoff (adaptiveRun query next succ n
                (next σ (succ σ (update x i y))) z)) (update x i y) := by
          apply lmarginal_congr_on
          intro z hz
          have hsz : succ σ z = succ σ (update x i y) :=
            hlocal σ i z (update x i y) hσ hqσ (fun j hj ↦ hz j (by simp [hj]))
          try dsimp only
          rw [adaptiveRun_succ_of_some hqσ, hsz]
        have hb := hrev σ i (succ σ (update x i y)) hσ hqσ
        have hih := ih (next σ (succ σ (update x i y)))
          (hinv σ i _ hσ hqσ)
          (by rw [hb, Finset.card_insert_of_notMem hiR]; omega) (update x i y)
        rw [hb] at hih
        rw [hcongr]
        exact hih
      have hA : MeasurableSet {y : Ω i | succ σ (update x i y) = true} :=
        ((hmeas σ).comp (measurable_update (a := i) x)) (measurableSet_singleton true)
      have hvals : (fun y : Ω i ↦ V (next σ (succ σ (update x i y)))) =
          fun y ↦ {y : Ω i | succ σ (update x i y) = true}.indicator
              (fun _ ↦ V (next σ true)) y +
            {y : Ω i | succ σ (update x i y) = true}ᶜ.indicator
              (fun _ ↦ V (next σ false)) y := by
        funext y
        by_cases hy : succ σ (update x i y) = true
        · simp [Set.indicator, hy]
        · simp [Set.indicator, hy]
      calc V σ ≤ q * V (next σ true) + (1 - q) * V (next σ false) := hstep σ i hσ hqσ
        _ ≤ ∫⁻ y, V (next σ (succ σ (update x i y))) ∂ν i := by
          rw [hvals]
          exact step_value_le_lintegral (ν i) hA hq (hmono σ i hσ hqσ)
            (hprob σ i x hσ hqσ)
        _ ≤ _ := lintegral_mono hinner

/-- Adaptive domination: starting with nothing revealed, the expected payoff of the
adaptive run (with enough steps to reveal every coordinate) dominates `V`. -/
theorem adaptive_domination
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)] [∀ i, Nonempty (Ω i)]
    (revealed : S → Finset ι) (query : S → Option ι) (next : S → Bool → S)
    (succ : S → (∀ i, Ω i) → Bool) (Inv : S → Prop) (V payoff : S → ℝ≥0∞)
    {q : ℝ≥0∞} (hq : q ≤ 1)
    (hquery : ∀ σ i, Inv σ → query σ = some i → i ∉ revealed σ)
    (hrev : ∀ σ i b, Inv σ → query σ = some i →
      revealed (next σ b) = insert i (revealed σ))
    (hinv : ∀ σ i b, Inv σ → query σ = some i → Inv (next σ b))
    (hlocal : ∀ σ i (x x' : ∀ j, Ω j), Inv σ → query σ = some i →
      (∀ j ∈ insert i (revealed σ), x j = x' j) → succ σ x = succ σ x')
    (hmeas : ∀ σ, Measurable (succ σ))
    (hprob : ∀ σ i (x : ∀ j, Ω j), Inv σ → query σ = some i →
      q ≤ ν i {y | succ σ (update x i y) = true})
    (hstep : ∀ σ i, Inv σ → query σ = some i →
      V σ ≤ q * V (next σ true) + (1 - q) * V (next σ false))
    (hmono : ∀ σ i, Inv σ → query σ = some i → V (next σ false) ≤ V (next σ true))
    (hterm : ∀ σ, Inv σ → query σ = none → V σ ≤ payoff σ)
    (σ₀ : S) (h₀ : Inv σ₀) (hr₀ : revealed σ₀ = ∅) :
    V σ₀ ≤ ∫⁻ x, payoff (adaptiveRun query next succ (Fintype.card ι) σ₀ x)
      ∂Measure.pi ν := by
  have x : ∀ i, Ω i := fun i ↦ Classical.arbitrary (Ω i)
  have h := adaptive_domination_lmarginal ν revealed query next succ Inv V payoff hq
    hquery hrev hinv hlocal hmeas hprob hstep hmono hterm (Fintype.card ι) σ₀ h₀
    (by omega) x
  rw [hr₀, Finset.sdiff_empty, lmarginal_univ] at h
  exact h

end Adaptive

end NearCritical
