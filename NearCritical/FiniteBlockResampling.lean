module

public import NearCritical.ClusterRevealSupport

/-! Finite-coordinate reassembly for the ACTUAL replacement sampler in source
prop.num_spanning_new. The product-law average is proved, not assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Replace S by the second configuration; preserve the first everywhere else. -/
def resampleBonds {d : ℕ} (S : Finset (Bond d)) (ω ζ : Configuration d) : Configuration d :=
  extendConfiguration S ω (S.restrict ζ)

/-- Reassemble finite observed coordinates G from fresh S bits and retained
G\S bits. S may contain additional unobserved coordinates. -/
def mergeResampledBits {d : ℕ} (G S : Finset (Bond d))
    (η : S → Bool) (ξ : (G \ S : Finset (Bond d)) → Bool) : G → Bool :=
  fun e => if h : e.val ∈ S then η ⟨e.val,h⟩
    else ξ ⟨e.val, Finset.mem_sdiff.mpr ⟨e.property,h⟩⟩

lemma mergeResampledBits_restrict {d : ℕ} (G S : Finset (Bond d)) (ω : Configuration d) :
    mergeResampledBits G S (S.restrict ω) ((G \ S : Finset (Bond d)).restrict ω) = G.restrict ω := by
  funext e
  simp [mergeResampledBits, Finset.restrict]

lemma resampleBonds_restrict {d : ℕ} (G S : Finset (Bond d)) (ω ζ : Configuration d) :
    G.restrict (resampleBonds S ω ζ) =
      mergeResampledBits G S (S.restrict ζ) ((G \ S : Finset (Bond d)).restrict ω) := by
  funext e
  simp only [Finset.restrict, resampleBonds, extendConfiguration, mergeResampledBits]
  split_ifs <;> rfl

def resampleAverage {d : ℕ} (p : unitInterval) (G S : Finset (Bond d))
    (H : (G → Bool) → ℝ) (ξ : (G \ S : Finset (Bond d)) → Bool) : ℝ :=
  ∫ η, H (mergeResampledBits G S η ξ)
    ∂(Measure.pi (fun _ : S => bernoulliMeasure true false p))

lemma integral_resampleBonds {d : ℕ} (p : unitInterval) (G S : Finset (Bond d))
    (H : (G → Bool) → ℝ) (ω : Configuration d) :
    (∫ ζ, H (G.restrict (resampleBonds S ω ζ)) ∂percolation d p) =
      resampleAverage p G S H ((G \ S : Finset (Bond d)).restrict ω) := by
  simp_rw [resampleBonds_restrict]
  calc
    _ = finiteExpectation p (fun η => H (mergeResampledBits G S η ((G \ S : Finset (Bond d)).restrict ω))) :=
      percolation_cylinder_expectation d p S _
    _ = _ := (integral_finite_bernoulli p _).symm

/-- Actual fixed-mask resampling preserves every finite-coordinate expectation.
No product law for the reassembled field is inserted as an input. -/
theorem integral_resampleAverage {d : ℕ} (p : unitInterval) (G S : Finset (Bond d))
    (H : (G → Bool) → ℝ) :
    (∫ ω, resampleAverage p G S H ((G \ S : Finset (Bond d)).restrict ω) ∂percolation d p) =
      ∫ ω, H (G.restrict ω) ∂percolation d p := by
  have hd : Disjoint S (G \ S : Finset (Bond d)) := by
    apply Finset.disjoint_left.mpr
    intro e he hdiff
    exact (Finset.mem_sdiff.mp hdiff).2 he
  have hbase := percolation_disjoint_block_integral p S (G \ S : Finset (Bond d)) hd
    (fun z => H (mergeResampledBits G S z.1 z.2))
  simp_rw [mergeResampledBits_restrict] at hbase
  rw [percolation_cylinder_expectation, ← integral_finite_bernoulli]
  change (∫ ξ, ∫ η, H (mergeResampledBits G S η ξ)
    ∂(Measure.pi (fun _ : S => bernoulliMeasure true false p))
    ∂(Measure.pi (fun _ : (G \ S : Finset (Bond d)) => bernoulliMeasure true false p))) = _
  rw [integral_integral_swap (Integrable.of_finite : Integrable
    (fun z : ((G \ S : Finset (Bond d)) → Bool) × (S → Bool) => H (mergeResampledBits G S z.2 z.1)) _)]
  exact hbase.symm

/-- Joint observables of two finite restriction blocks are integrable. This
small helper supplies the finite-sum interchange in the adaptive source proof. -/
lemma integrable_two_block_product {d : ℕ} (p : unitInterval) (S T : Finset (Bond d))
    (f : (S → Bool) → ℝ) (g : (T → Bool) → ℝ) :
    Integrable (fun ω : Configuration d => f (S.restrict ω) * g (T.restrict ω)) (percolation d p) := by
  let E : Bool → Finset (Bond d) := fun b => if b then T else S
  let h : ∀ b, (E b → Bool) → ℝ := fun b => match b with
    | false => f
    | true => g
  have hi := integrable_finite_block_product p (Finset.univ : Finset Bool) E h
  simpa [E,h,Fintype.prod_bool,mul_comm] using hi

end NearCritical
