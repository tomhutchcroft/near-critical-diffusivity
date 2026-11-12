module

public import NearCritical.Section10LatticeRuleBuild
public import NearCritical.Section9ConditionalLaw
public import NearCritical.Section9RevealSupport

/-! Positivity of realised reveals.

* `cylinder_ne_zero`: for `0 < p < 1` every finite bond pattern has positive
  `P_p`-probability.
* `revealEvent_ne_zero_of_realised`: the two-cube reveal event of Section 9 for
  the revealed sets of an actual configuration has positive probability (it
  contains the cylinder of that configuration on the explored bonds).
* `NestLayout.Fat_realised`: for the base reveal of a configuration, the
  revealed set in the cube of a site is the heart-cluster union of that cube.

These give the hypothesis `hpos` of the Section 9 theorems for the reveal of a
moving step.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical

theorem cylinder_ne_zero {d : ℕ} (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (T : Finset (Bond d)) (ζ : Configuration d) :
    percolation d p {ω : Configuration d | ∀ b ∈ T, ω b = ζ b} ≠ 0 := by
  have hT : (percolation d p).map T.restrict =
      Measure.pi (fun _ : T => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  have hset : {ω : Configuration d | ∀ b ∈ T, ω b = ζ b} =
      (T.restrict : Configuration d → (T → Bool)) ⁻¹' {T.restrict ζ} := by
    ext ω
    constructor
    · intro h
      show T.restrict ω = T.restrict ζ
      funext e
      exact h e.1 e.2
    · intro h b hb
      have h' : T.restrict ω = T.restrict ζ := h
      exact congrFun h' ⟨b, hb⟩
  rw [hset, ← Measure.map_apply (Finset.measurable_restrict T) (measurableSet_singleton _), hT,
    Measure.pi_singleton]
  refine Finset.prod_ne_zero_iff.mpr (fun e _ => ?_)
  have hreal : (bernoulliMeasure true false p).real {T.restrict ζ e} ≠ 0 := by
    cases hv : T.restrict ζ e with
    | true =>
      have : (bernoulliMeasure true false p).real {true} = (p : ℝ) := by simp
      rw [this]
      exact hp0.ne'
    | false =>
      have : (bernoulliMeasure true false p).real {false} = 1 - (p : ℝ) := by simp
      rw [this]
      linarith
  intro h0
  apply hreal
  unfold Measure.real
  rw [h0]
  rfl

theorem revealEvent_ne_zero_of_realised {d : ℕ} (p : unitInterval) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (Q₁ H₁ Q₃ H₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (ω₀ : Configuration d) :
    percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃
      (heartClusterUnion ω₀ Q₁ H₁) (heartClusterUnion ω₀ Q₃ H₃)) ≠ 0 := by
  have hcyl := cylinder_ne_zero p hp0 hp1
    (clusterRevealBonds Q₁ (heartClusterUnion ω₀ Q₁ H₁) ∪
      clusterRevealBonds Q₃ (heartClusterUnion ω₀ Q₃ H₃)) ω₀
  have hsub : {ω : Configuration d | ∀ b ∈ clusterRevealBonds Q₁ (heartClusterUnion ω₀ Q₁ H₁) ∪
      clusterRevealBonds Q₃ (heartClusterUnion ω₀ Q₃ H₃), ω b = ω₀ b} ⊆
      section9RevealEvent Q₁ H₁ Q₃ H₃ (heartClusterUnion ω₀ Q₁ H₁)
        (heartClusterUnion ω₀ Q₃ H₃) := by
    intro ω hω
    exact ⟨heartClusterUnion_eq_of_reveal_agree Q₁ H₁ _ hH₁ rfl
        (fun e he => (hω e (Finset.mem_union_left _ he)).symm),
      heartClusterUnion_eq_of_reveal_agree Q₃ H₃ _ hH₃ rfl
        (fun e he => (hω e (Finset.mem_union_right _ he)).symm)⟩
  intro h0
  exact hcyl (measure_mono_null hsub h0)

variable {D d : ℕ} (Λ : NestLayout D d)

theorem NestLayout.Fat_realised (z : Configuration d × Configuration d) {s : RSite D}
    (hs : s ∈ Λ.siteBox) :
    Λ.Fat (Λ.ρ₀ z) s = heartClusterUnion z.1 (Λ.Q s) (Λ.Hh s) :=
  clusterFamilyUnion_inter_cube z.1 Λ.siteBox Λ.Q Λ.Hh Λ.hdisj s hs

/-- The reveal event of a moving step of a realised reveal has positive
probability. -/
theorem NestLayout.stepReveal_ne_zero (p : unitInterval) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (z : Configuration d × Configuration d) {s s' : RSite D}
    (hs : s ∈ Λ.siteBox) (hs' : s' ∈ Λ.siteBox) :
    percolation d p (section9RevealEvent (Λ.Q s) (Λ.Hh s) (Λ.Q s') (Λ.Hh s')
      (Λ.Fat (Λ.ρ₀ z) s) (Λ.Fat (Λ.ρ₀ z) s')) ≠ 0 := by
  rw [Λ.Fat_realised z hs, Λ.Fat_realised z hs']
  exact revealEvent_ne_zero_of_realised p hp0 hp1 _ _ _ _ (Λ.hH s) (Λ.hH s') z.1

end NearCritical.Section10
