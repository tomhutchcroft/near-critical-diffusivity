module

public import NearCritical.LatticeFullConductivity
public import NearCritical.NestChainLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration

/-! Actual percolation cube-weight factorization for source lem.nw.mean.
The source pre-good events must still be identified with disjoint bond blocks. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory ProbabilityTheory

/-- Any finite product of local observables is still a finite cylinder. -/
lemma finite_block_product_cylinder {d : ℕ} {I : Type*} (s : Finset I)
    (E : I → Finset (Bond d)) (f : ∀ i, (E i → Bool) → ℝ) :
    ∃ g : ((s.biUnion E) → Bool) → ℝ, ∀ ω : Configuration d,
      g ((s.biUnion E).restrict ω) = ∏ i ∈ s, f i ((E i).restrict ω) := by
  classical
  let T := s.biUnion E
  let g : (T → Bool) → ℝ := fun η => ∏ i ∈ s,
    f i (fun e => if h : e.val ∈ T then η ⟨e.val,h⟩ else false)
  refine ⟨g,?_⟩
  intro ω
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext e
  have he : e.val ∈ T := Finset.mem_biUnion.mpr ⟨i,hi,e.property⟩
  simp [he,Finset.restrict]

lemma integrable_finite_block_product {d : ℕ} {I : Type*} (p : unitInterval)
    (s : Finset I) (E : I → Finset (Bond d)) (f : ∀ i, (E i → Bool) → ℝ) :
    Integrable (fun ω : Configuration d => ∏ i ∈ s, f i ((E i).restrict ω)) (percolation d p) := by
  obtain ⟨g,hg⟩ := finite_block_product_cylinder s E f
  have hf := percolation_cylinder_integrable d p (s.biUnion E) g
  simpa only [hg] using hf

/-- Product expectations for genuinely disjoint local edge blocks, derived from
independent coordinates of the actual infinite Bernoulli law. -/
theorem percolation_disjoint_block_product {d : ℕ} {I : Type*} (p : unitInterval)
    (s : Finset I) (E : I → Finset (Bond d))
    (hd : (s:Set I).PairwiseDisjoint E) (f : ∀ i, (E i → Bool) → ℝ) :
    (∫ ω : Configuration d, ∏ i ∈ s, f i ((E i).restrict ω) ∂percolation d p) =
      ∏ i ∈ s, ∫ ω : Configuration d, f i ((E i).restrict ω) ∂percolation d p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    let T := s.biUnion E
    have hdis : Disjoint (E a) T := by
      apply Finset.disjoint_left.mpr
      intro e hea heT
      obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp heT
      exact Finset.disjoint_left.mp
        (hd (by simp) (by simp [hj]) (by intro heq; subst j; exact ha hj)) hea hej
    obtain ⟨g,hg⟩ := finite_block_product_cylinder s E f
    have hind : IndepFun ((E a).restrict : Configuration d → (E a → Bool))
        (T.restrict : Configuration d → (T → Bool)) (percolation d p) := by
      exact iIndepFun.indepFun_finset (E a) T hdis
        (iIndepFun_infinitePi (fun _ : Bond d => (measurable_id : Measurable (id : Bool → Bool))))
        (fun e => measurable_pi_apply e)
    have hc := hind.comp (measurable_of_finite (f a)) (measurable_of_finite g)
    have hmul := hc.integral_mul_eq_mul_integral
      (percolation_cylinder_integrable d p (E a) (f a)).aestronglyMeasurable
      (percolation_cylinder_integrable d p T g).aestronglyMeasurable
    have he : (∫ ω : Configuration d, f a ((E a).restrict ω) *
          (∏ j ∈ s, f j ((E j).restrict ω)) ∂percolation d p) =
        (∫ ω : Configuration d, f a ((E a).restrict ω) ∂percolation d p) *
          (∫ ω : Configuration d, ∏ j ∈ s, f j ((E j).restrict ω) ∂percolation d p) := by
      simpa only [Function.comp_apply,Pi.mul_apply,T,hg] using hmul
    simp only [Finset.prod_insert ha]
    rw [he,ih (fun i hi j hj hij => hd (by simp [hi]) (by simp [hj]) hij)]

def nestCubeProbability {d : ℕ} (p : unitInterval) (E : Finset (Bond d))
    (A : Set (E → Bool)) : ℝ :=
  (percolation d p).real {ω | E.restrict ω ∈ A}

def nestCubeWeight {d : ℕ} (p : unitInterval) (E : Finset (Bond d))
    (A : Set (E → Bool)) (ω : Configuration d) : ℝ := by
  classical
  exact if E.restrict ω ∈ A then (nestCubeProbability p E A)⁻¹ else 0

lemma integrable_nestCubeWeight {d : ℕ} (p : unitInterval) (E : Finset (Bond d))
    (A : Set (E → Bool)) : Integrable (nestCubeWeight p E A) (percolation d p) := by
  classical
  exact percolation_cylinder_integrable d p E
    (fun η => if η∈A then (nestCubeProbability p E A)⁻¹ else 0)

lemma nestCubeWeight_integral {d : ℕ} (p : unitInterval) (E : Finset (Bond d))
    (A : Set (E → Bool)) (hq : 0<nestCubeProbability p E A) :
    ∫ ω, nestCubeWeight p E A ω ∂percolation d p = 1 := by
  classical
  have hm : MeasurableSet {ω : Configuration d | E.restrict ω∈A} :=
    (Finset.measurable_restrict E) (Set.toFinite A).measurableSet
  have he : nestCubeWeight p E A =
      ({ω : Configuration d | E.restrict ω∈A} : Set (Configuration d)).indicator
        (fun _ => (nestCubeProbability p E A)⁻¹) := by
    funext ω
    simp [nestCubeWeight,Set.indicator]
  rw [he,integral_indicator_const _ hm]
  exact mul_inv_cancel₀ hq.ne'

/-- Source omega_Gamma has mean one for actual disjoint local cube events.
Neither independence of these observables nor the product-mean conclusion is
assumed: both follow from the actual disjoint bond coordinates. -/
theorem percolation_nestCubeWeight_product_mean {d : ℕ} {I : Type*}
    (p : unitInterval) (s : Finset I) (E : I → Finset (Bond d))
    (A : ∀ i, Set (E i → Bool)) (hd : (s:Set I).PairwiseDisjoint E)
    (hq : ∀ i∈s, 0<nestCubeProbability p (E i) (A i)) :
    (∫ ω : Configuration d, ∏ i∈s, nestCubeWeight p (E i) (A i) ω ∂percolation d p)=1 := by
  classical
  let f : ∀ i, (E i → Bool) → ℝ := fun i η =>
    if η∈A i then (nestCubeProbability p (E i) (A i))⁻¹ else 0
  have he := percolation_disjoint_block_product p s E hd f
  change (∫ ω : Configuration d, ∏ i∈s, f i ((E i).restrict ω) ∂percolation d p)=1
  rw [he]
  apply Finset.prod_eq_one
  intro i hi
  exact nestCubeWeight_integral p (E i) (A i) (hq i hi)

/-- Mixed actual percolation/finite-trace mean-one identity, before the source
exploration and W conditional-projection identifications. The conditional chain
law may depend on the entire base configuration; no independence from it is used. -/
theorem percolation_cube_chain_weight_mean {d : ℕ} {I X : Type*} [Fintype X]
    (p : unitInterval) (s : Finset I) (E : I → Finset (Bond d))
    (A : ∀ i, Set (E i → Bool)) (hd : (s:Set I).PairwiseDisjoint E)
    (hq : ∀ i∈s, 0<nestCubeProbability p (E i) (A i))
    (P : Configuration d → ℕ → X → X → ℝ)
    (success : Configuration d → ℕ → X → X → Prop) (N : ℕ)
    (hP : ∀ ω n, n<N → ∀ x y, 0≤P ω n x y)
    (hrow : ∀ ω n, n<N → ∀ x, ∑ y, P ω n x y=1)
    (hs : ∀ ω n, n<N → ∀ x, 0<nestSuccessProbability (P ω n) (success ω n) x)
    (start : Configuration d → X) :
    (∫ ω : Configuration d, (∏ i∈s, nestCubeWeight p (E i) (A i) ω) *
      (∫ z, nestTraceWeight (P ω) (success ω) N (start ω) z
        ∂(nestTraceLaw (P ω) N (hP ω) (hrow ω) (start ω)).toMeasure) ∂percolation d p)=1 := by
  have he (ω : Configuration d) := nestTraceLaw_integral_weight
    (P ω) (success ω) N (hP ω) (hrow ω) (hs ω) (start ω)
  simp only [he,mul_one]
  exact percolation_nestCubeWeight_product_mean p s E A hd hq

end NearCritical
