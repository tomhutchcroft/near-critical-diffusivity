module
public import NearCritical.Section9CrossOverlapCertificates
public import NearCritical.Section9FiniteTripodDecay

/-! Source Case IV's uniform four-terminal upper factor, from finite BK. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Dropping the second fixed terminal bounds a cross-joint event by the
separated tripod estimate, summed over both actual target families. -/
theorem section9_cross_joint_uniform_tripod_bound {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (D A B : Finset (Vertex d)) (a b : Vertex d),
      a ∈ section9FiniteMiddle i n →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      (percolation d (criticalPoint d)).real (section9CrossJointEvent D a b A B) ≤
        (A.card : ℝ)*(B.card : ℝ)*(C*((n:ℝ)/8)^(6-2*(d : ℝ))) := by
  obtain ⟨C,hC,hJoint⟩ := section9_cross_finite_joint_arm_le hd asymptotics
  refine ⟨C,hC,?_⟩
  intro i n hn D A B a b ha hA hB
  let E := fun x => connectionToSetEvent (D : Set (Vertex d)) a {x} ∩
    connectionToSetEvent (D : Set (Vertex d)) a (B : Set (Vertex d))
  have hsub : section9CrossJointEvent D a b A B ⊆ ⋃ x ∈ A, E x := by
    rintro ω ⟨_,⟨haD,x,hxA,hxD,hax⟩,hBω⟩
    exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hxA,⟨haD,x,rfl,hxD,hax⟩,hBω⟩⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le A E).trans ?_)
  calc
    _ ≤ ∑ _x ∈ A, (B.card : ℝ)*(C*((n:ℝ)/8)^(6-2*(d : ℝ))) :=
      Finset.sum_le_sum fun x hx => hJoint i n hn D B a x ha (hA hx) hB
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]

end NearCritical
