module

public import NearCritical.SlabUpperLabelCoupling

/-! Two-layer sprinkling coupling for prop.slab.upper (faithful to the source).

The source tube `T₁₂₃` reaches into the two cubes it joins, so cube and tube bond
sets are NOT disjoint; independence comes from sprinkling. Each bond carries a
base bit (law `Ber(a)`, `a = p_c`) and an independent sprinkle bit (`Ber(s)`); the
`p`-configuration is their OR, `p = 1 - (1-a)(1-s)`. Cube blocks read base bits of
cube bonds; tube blocks read sprinkle bits (and base bits outside cubes). Blocks
are then disjoint in the coordinate set `Bond d × Bool`.

* `infinitePi_map_blockFamily`: generic block law for a NON-identical product.
* `map_sprinkleConfiguration`: the OR configuration has law
  `percolation d (σ (σ a * σ s))`.
* `sprinkleConfiguration_base`: base-open ⇒ open (monotone coupling).
* `coupledRenormalizedExploration_of_sprinkleBlocks`: constructor. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory ProbabilityTheory Finset unitInterval
open scoped ENNReal

variable {d : ℕ}

/-! Generic block law. -/

def blockFamily {J ι : Type*} {X : J → Type*} (B : ι → Finset J) (ω : ∀ j, X j) :
    ∀ i, ∀ e : B i, X e :=
  fun _ e => ω e

lemma measurable_blockFamily {J ι : Type*} {X : J → Type*} [∀ j, MeasurableSpace (X j)]
    (B : ι → Finset J) : Measurable (blockFamily (X := X) B) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem infinitePi_map_blockFamily {J ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : J → Type*} [∀ j, MeasurableSpace (X j)] (μ : ∀ j, Measure (X j))
    [∀ j, IsProbabilityMeasure (μ j)]
    (B : ι → Finset J) (hB : Pairwise fun i j => Disjoint (B i) (B j)) :
    Measure.map (blockFamily B) (Measure.infinitePi μ) =
      Measure.pi (fun i => Measure.pi (fun e : B i => μ e)) := by
  have hf : Function.Injective (fun s : (Σ i, B i) => (s.2 : J)) := by
    rintro ⟨i, e, he⟩ ⟨j, e', he'⟩ h
    change e = e' at h
    subst h
    by_cases hij : i = j
    · subst hij; rfl
    · exact absurd he' (Finset.disjoint_left.1 (hB hij) he)
  have h1 : Measure.map (fun (ω : ∀ j, X j) (s : Σ i, B i) => ω s.2)
      (Measure.infinitePi μ) = Measure.infinitePi (fun s : (Σ i, B i) => μ s.2) :=
    Measure.map_infinitePi_infinitePi_of_inj hf
  have h2 : Measure.map (MeasurableEquiv.piCurry (fun (i : ι) (e : B i) => X e))
      (Measure.infinitePi (fun s : (Σ i, B i) => μ s.2)) =
      Measure.infinitePi (fun i : ι => Measure.infinitePi (fun e : B i => μ e)) :=
    Measure.infinitePi_map_piCurry (fun (i : ι) (e : B i) => μ e)
  have hg : Measurable (fun (ω : ∀ j, X j) (s : Σ i, B i) => ω s.2) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hcomp : blockFamily (X := X) B =
      (MeasurableEquiv.piCurry (fun (i : ι) (e : B i) => X e)) ∘
        (fun (ω : ∀ j, X j) (s : Σ i, B i) => ω s.2) := rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) hg, h1, h2]
  simp_rw [Measure.infinitePi_eq_pi]

/-! Bernoulli OR. -/

lemma bool_measure_ext (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ {false} = ν {false}) : μ = ν := by
  apply Measure.ext_of_singleton
  intro b
  cases b
  · exact h
  · have hc : ({true} : Set Bool) = ({false} : Set Bool)ᶜ := by
      ext b; cases b <;> simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_singleton _),
      prob_compl_eq_one_sub (measurableSet_singleton _), h]

lemma bernoulli_false (a : I) :
    bernoulliMeasure true false a {false} = ((toNNReal (σ a) : NNReal) : ℝ≥0∞) := by
  classical
  rw [bernoulliMeasure_apply a (measurableSet_singleton false)]
  simp

lemma toNNReal_mul (x y : I) : toNNReal (x * y) = toNNReal x * toNNReal y := by
  apply NNReal.eq
  rw [NNReal.coe_mul, coe_toNNReal, coe_toNNReal, coe_toNNReal, Set.Icc.coe_mul]

/-- Single-bond two-layer law. -/
def sprinkleLaw (a s : I) (j : Bond d × Bool) : Measure Bool :=
  if j.2 then bernoulliMeasure true false a else bernoulliMeasure true false s

instance (a s : I) (j : Bond d × Bool) : IsProbabilityMeasure (sprinkleLaw a s j) := by
  unfold sprinkleLaw
  split <;> infer_instance

def boolOr (f : Bool → Bool) : Bool := f true || f false

lemma measurable_boolOr : Measurable boolOr := fun _ _ => (Set.toFinite _).measurableSet

lemma map_boolOr (a s : I) (e : Bond d) :
    (Measure.pi (fun b : Bool => sprinkleLaw a s (e, b))).map boolOr =
      bernoulliMeasure true false (σ (σ a * σ s)) := by
  have hm : Measurable boolOr := measurable_boolOr
  apply bool_measure_ext
  rw [Measure.map_apply hm (measurableSet_singleton false)]
  have hpre : boolOr ⁻¹' {false} = ({fun _ => false} : Set (Bool → Bool)) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, boolOr, Bool.or_eq_false_iff]
    constructor
    · rintro ⟨h1, h2⟩
      funext b
      cases b <;> assumption
    · rintro rfl
      exact ⟨rfl, rfl⟩
  rw [hpre, Measure.pi_singleton, Fintype.prod_bool]
  simp only [sprinkleLaw, ↓reduceIte, Bool.false_eq_true]
  rw [bernoulli_false, bernoulli_false, bernoulli_false, symm_symm, toNNReal_mul,
    ENNReal.coe_mul]

/-- The `p`-configuration of the two-layer coupling. -/
def sprinkleConfiguration (ω : Bond d × Bool → Bool) : Configuration d :=
  fun e => ω (e, true) || ω (e, false)

lemma measurable_sprinkleConfiguration :
    Measurable (sprinkleConfiguration (d := d)) :=
  measurable_pi_iff.2 fun e => measurable_boolOr.comp
    (f := fun ω : Bond d × Bool → Bool => fun b => ω (e, b))
    (measurable_pi_iff.2 fun b => measurable_pi_apply (e, b))

theorem map_sprinkleConfiguration (a s : I) :
    Measure.map sprinkleConfiguration (Measure.infinitePi (sprinkleLaw (d := d) a s)) =
      percolation d (σ (σ a * σ s)) := by
  have hc : Measure.map (MeasurableEquiv.curry (Bond d) Bool Bool)
      (Measure.infinitePi (sprinkleLaw (d := d) a s)) =
      Measure.infinitePi (fun e : Bond d => Measure.infinitePi (fun b : Bool => sprinkleLaw a s (e, b))) :=
    Measure.infinitePi_map_curry (fun (e : Bond d) (b : Bool) => sprinkleLaw a s (e, b))
  have hcomp : sprinkleConfiguration (d := d) =
      (fun (g : Bond d → Bool → Bool) e => boolOr (g e)) ∘ (MeasurableEquiv.curry (Bond d) Bool Bool) :=
    rfl
  have hg : Measurable (fun (g : Bond d → Bool → Bool) e => boolOr (g e)) :=
    measurable_pi_iff.2 fun e => measurable_boolOr.comp (measurable_pi_apply e)
  rw [hcomp, ← Measure.map_map hg (MeasurableEquiv.measurable _), hc]
  simp_rw [Measure.infinitePi_eq_pi]
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_boolOr)]
  simp_rw [map_boolOr]
  try rfl

lemma sprinkleConfiguration_base (ω : Bond d × Bool → Bool) (e : Bond d)
    (h : ω (e, true) = true) : sprinkleConfiguration ω e = true := by
  simp [sprinkleConfiguration, h]

/-! Constructor. -/

theorem coupledRenormalizedExploration_of_sprinkleBlocks (a s p : I)
    (hp : p = σ (σ a * σ s)) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (N : ℕ) (Bx : Finset (Vertex 2)) (h0 : (0 : Vertex 2) ∈ Bx)
    (B : Bx ⊕ boxBonds Bx → Finset (Bond d × Bool))
    (hB : Pairwise fun i j => Disjoint (B i) (B j))
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞}
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (succ : ExploreState Bx (boxBonds Bx) → (∀ i, B i → Bool) → Bool)
    (local_succ : ∀ st i (x x' : ∀ j, B j → Bool),
      ExploreInv (boxEnds Bx) (⟨0, h0⟩ : Bx) st →
      exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx) st = some i →
      (∀ j ∈ insert i (exploreRevealed st), x j = x' j) → succ st x = succ st x')
    (measurable_succ : ∀ st, Measurable (succ st))
    (prob_succ : ∀ st i (x : ∀ j, B j → Bool),
      ExploreInv (boxEnds Bx) (⟨0, h0⟩ : Bx) st →
      exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx) st = some i →
      κ {true} ≤ Measure.pi (fun e : B i => sprinkleLaw a s (e : Bond d × Bool))
        {y | succ st (Function.update x i y) = true})
    (good : ∀ ω : Bond d × Bool → Bool, explorePayoff (boxInnerBoundary Bx)
      (adaptiveRun (exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx))
        (exploreNext (boxEnds Bx) (⟨0, h0⟩ : Bx)) succ
        (Fintype.card (Bx ⊕ boxBonds Bx)) ⟨∅, ∅, ∅, ∅, ∅⟩ (blockFamily B ω)) ≠ 0 →
      sprinkleConfiguration ω ∈ restrictedReachFarEvent S F N) :
    Nonempty (CoupledRenormalizedExploration d p S F N θ) :=
  ⟨{ Vx := Bx
     Ed := boxBonds Bx
     ends := boxEnds Bx
     root := ⟨0, h0⟩
     target := boxInnerBoundary Bx
     Ω₀ := Bond d × Bool → Bool
     P := Measure.infinitePi (sprinkleLaw a s)
     cfg := sprinkleConfiguration
     measurable_cfg := measurable_sprinkleConfiguration
     map_cfg := by rw [hp]; exact map_sprinkleConfiguration a s
     Ω := fun i => B i → Bool
     ν := fun i => Measure.pi (fun e : B i => sprinkleLaw a s (e : Bond d × Bool))
     κ := κ
     Φ := blockFamily B
     measurable_Φ := measurable_blockFamily B
     map_Φ := infinitePi_map_blockFamily (sprinkleLaw a s) B hB
     succ := succ
     local_succ := local_succ
     measurable_succ := measurable_succ
     prob_succ := prob_succ
     good := good
     mixed_ge := mixedValue_box_ge Bx h0 κ hθ }⟩

end NearCritical
