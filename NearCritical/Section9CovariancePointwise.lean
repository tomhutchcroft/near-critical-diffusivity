module
public import NearCritical.Section9CollisionDecomposition
public import NearCritical.Section9TwoClusterReveal

/-! Pointwise pivotal covariance decoupling with retained connection witnesses. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

/-- For any revealed vertex set C inside a fixed cutoff W, the original
pivotal product is bounded by its intersection part, its resampled product,
and the marked retained-witness sum. -/
theorem section9_pivotal_product_resampling_le {d : ℕ}
    (S : Finset (Bond d)) (C W L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hCW : C ⊆ W) (htouch : ∀ b ∈ S, b.1 ∈ C ∨ bondTip b ∈ C)
    (ω ζ : Configuration d) (e f : Vertex d × Vertex d) :
    section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω *
      section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f ω ≤
    (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f ∧
        ¬ (Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) C ∧
           Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) C) then (1 : ℝ) else 0) +
    section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω *
      section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f (resampleBonds S ω ζ) +
    ∑ w ∈ W, (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧ w ∈ C
      then (1 : ℝ) else 0) *
      ((if resampleBonds S ω ζ ∈ section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w
          then (1 : ℝ) else 0) +
       (if resampleBonds S ω ζ ∈ section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w
          then (1 : ℝ) else 0)) := by
  let η := resampleBonds S ω ζ
  let J := fun w => (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧ w ∈ C
      then (1 : ℝ) else 0) *
      ((if η ∈ section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w then (1 : ℝ) else 0) +
       (if η ∈ section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A f.swap w then (1 : ℝ) else 0))
  have hJ (w : Vertex d) : 0 ≤ J w := by dsimp [J]; positivity
  have hsum : 0 ≤ ∑ w ∈ W, J w := Finset.sum_nonneg fun w _ => hJ w
  by_cases he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e
  · by_cases hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f
    · by_cases havoid : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) C ∧
          Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) C
      · have hc := section9_pivotal_resampling_or_retained_witness S C L R Q₁ F₁ Q₃ F₃ A B
          htouch ω ζ f hf havoid.1 havoid.2
        have hbound : (1 : ℝ) ≤ section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f η + ∑ w ∈ W, J w := by
          rcases hc with hp | ⟨w,hw,hwitness⟩ | ⟨w,hw,hwitness⟩
          · simpa [section9PivotalIndicator,η,hp] using (le_add_of_nonneg_right hsum :
              (1 : ℝ) ≤ 1 + ∑ w ∈ W, J w)
          all_goals
            have hsingle := Finset.single_le_sum (fun v _ => hJ v) (hCW hw)
            have hwone : (1 : ℝ) ≤ J w := by dsimp [J,η]; split_ifs <;> simp_all <;> norm_num
            have hprob : 0 ≤ section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f η := by
              unfold section9PivotalIndicator; positivity
            exact hwone.trans (hsingle.trans (le_add_of_nonneg_left hprob))
        simpa only [section9PivotalIndicator,he,hf,havoid,not_true_eq_false,and_false,
          ite_false,ite_true,one_mul,zero_add,and_self,true_and,J,η] using hbound
      · have hrest : 0 ≤ section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f η := by
          unfold section9PivotalIndicator; positivity
        simpa only [section9PivotalIndicator,he,hf,havoid,not_false_eq_true,and_self,
          ite_true,one_mul,J,η] using
          (show (1 : ℝ) ≤ 1 + section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f η + ∑ w ∈ W, J w by linarith)
    · simp only [section9PivotalIndicator,he,hf,ite_false,ite_true,mul_zero]
      positivity
  · simp only [section9PivotalIndicator,he,ite_false,zero_mul]
    positivity

end NearCritical
