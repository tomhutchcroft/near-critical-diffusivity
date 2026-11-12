module

public import NearCritical.Section9PivotalMoments
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

/-- Target clusters with at least one actual critical pivotal pair. -/
def section9PivotalTargets {d : ℕ} {ι : Type*} (I : Finset ι)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d))
    (target : ι → Finset (Vertex d)) (ω : Configuration d) : Finset ι :=
  I.filter fun i => section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (target i) ω ≠ 0

/-- Source eq.sprinkling.AB.disjoint.CS for the literal pivotal counts
of the indexed target clusters. -/
theorem section9_distinct_targets_moment_bound {d : ℕ} {ι : Type*}
    (I : Finset ι) (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d))
    (target : ι → Finset (Vertex d)) (ω : Configuration d) :
    (∑ i ∈ I, section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (target i) ω)^2 ≤
      ((section9PivotalTargets I E L R Q₁ F₁ Q₃ F₃ A target ω).card : ℝ) *
        ∑ i ∈ I, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (target i) ω)^2 := by
  let c := fun i => section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (target i) ω
  let J := section9PivotalTargets I E L R Q₁ F₁ Q₃ F₃ A target ω
  have hsum : ∑ i ∈ J, c i = ∑ i ∈ I, c i := by
    dsimp only [J, section9PivotalTargets]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : c i = 0 <;> simp [c, hi] at *
  have hsq : ∑ i ∈ J, (c i)^2 = ∑ i ∈ I, (c i)^2 := by
    dsimp only [J, section9PivotalTargets]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : c i = 0 <;> simp [c, hi] at *
  have h := Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) c
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, hsq]
    using h

end NearCritical
