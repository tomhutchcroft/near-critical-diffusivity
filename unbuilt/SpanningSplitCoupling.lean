module

public import NearCritical.SpanningSplitWalk
public import NearCritical.SpanningSplitProbability

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory Filter Set
open scoped Topology ENNReal Classical

/-- A limit tree with the robust embedded branches needed for the split
crossings. Projection records the usual real-tree tripod identity. -/
structure SplitSpanningTree (d : ℕ) where
  Tree : Type
  metric : PseudoMetricSpace Tree
  root : Tree
  embed : Tree → (Fin d → ℝ)
  continuous : letI := metric; UniformContinuous embed
  projection : letI := metric; ∀ r y b : Tree, ∃ a : Tree,
    dist r a + dist a y = dist r y ∧ 2*dist b a = dist r b + dist b y - dist r y
  branches : letI := metric; ∀ (f : Fin d × Bool) (pl : Bool), ∃ y : Tree,
    (7/4:ℝ) ≤ realSpanningHeight f (embed y) ∧
    ∀ a : Tree, dist root a + dist a y = dist root y →
      (-(1/3:ℝ) ≤ realSpanningHeight f (embed a)) ∧
      (∀ j, j ≠ f.1 → |embed a j| ≤ (1/3:ℝ)) ∧
      ((3/8:ℝ) ≤ realSpanningHeight f (embed a) → ∀ j, j ≠ f.1 →
        (9/64:ℝ) ≤ (if pl then embed a j else -embed a j) ∧
        (if pl then embed a j else -embed a j) ≤ 15/64)

/-- Pointed chemical-metric and embedding approximation to a limit tree.
The relation covers exactly the root cluster on the lattice side and
covers the whole tree on the limit side. -/
def SplitSpanningTree.approximatedBy {d : ℕ} (L : SplitSpanningTree d)
    (t : ℕ) (o : Vertex d) (ω : Configuration d) (ε : ℝ) : Prop :=
  letI := L.metric
  ∃ (c : ℝ) (R : Vertex d → L.Tree → Prop), 0 ≤ c ∧ R o L.root ∧
    (∀ x a, R x a → (openGraph ω).Reachable o x) ∧
    (∀ x, (openGraph ω).Reachable o x → ∃ a, R x a) ∧
    (∀ a, ∃ x, R x a) ∧
    (∀ x a x' a', R x a → R x' a' → |c*((openGraph ω).dist x x':ℝ)-dist a a'| ≤ ε) ∧
    (∀ x a, R x a → dist (scaledSpanningVertex t x) (L.embed a) ≤ ε)

/-- Vanishing distortion in a sample of the coupling gives all the
simultaneous split crossings at large enough indices in that sample. -/
theorem SplitSpanningTree.crossAll_eventually {d : ℕ} (L : SplitSpanningTree d)
    (t : ℕ → ℕ) (o : ℕ → Vertex d) (ω : ℕ → Configuration d) (ε : ℕ → ℝ)
    (ht : Tendsto t atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (ho : ∀ n, o n ∈ centeredBox d ((t n - 1) / 32))
    (happrox : ∀ᶠ n in atTop, L.approximatedBy (t n) (o n) (ω n) (ε n)) :
    ∀ᶠ n in atTop, ω n ∈ crossAll (t n) (t n) (o n) := by
  letI := L.metric
  obtain ⟨ε₀,hε₀,hmod⟩ := uniformContinuous_geodesic_modulus L.embed L.continuous
    (show (0:ℝ) < 1/256 by norm_num)
  filter_upwards [(tendsto_atTop.1 ht) 1,
    hε.eventually_le_const hε₀, hε.eventually_le_const (show (0:ℝ) < 1/256 by norm_num), happrox]
    with n htn hsmall hsmall' hn
  obtain ⟨c,R,hc,hroot,hR,hcover,hsurj,hdist,hembed⟩ := hn
  have hrootCube : o n ∈ typicalCube (t n) (0 : Vertex d) := by
    apply (mem_typicalCube_iff_int htn 0 (o n)).mpr
    intro j
    have hcoord := mem_centeredBox.mp (ho n) j
    have hN : (((t n - 1)/32:ℕ):ℤ) ≤ (((t n - 1)/2:ℕ):ℤ) := by
      exact_mod_cast (show (t n - 1)/32 ≤ (t n - 1)/2 by omega)
    simp only [Pi.zero_apply,sub_zero]
    exact ⟨(neg_le_neg hN).trans hcoord.1, hcoord.2.trans hN⟩
  intro i
  obtain ⟨y,hy,hbranch⟩ := L.branches i.1 i.2
  obtain ⟨v,hvy⟩ := hsurj y
  exact chemical_correspondence_crossSplit htn i.1 i.2 (ω n) hrootCube c hc R (ε n) (1/256)
    (by norm_num) (by linarith) hR hcover hdist L.projection L.embed hembed
    (hmod (ε n) hsmall) hroot hvy hbranch hy

/-- A common probability space carrying the configurations of a
sequence under their specified conditional critical laws. -/
structure ConditionalClusterSample (d : ℕ) (condition : ℕ → Set (Configuration d)) where
  Sample : Type
  measurableSpace : MeasurableSpace Sample
  μ : @Measure Sample measurableSpace
  probability : IsProbabilityMeasure μ
  config : ℕ → Sample → Configuration d
  measurable_config : letI := measurableSpace; ∀ n, Measurable (config n)
  law : letI := measurableSpace; ∀ n, Measure.map (config n) μ =
    ProbabilityTheory.cond (percolation d (criticalPoint d)) (condition n)

/-- A conditional scaling-limit coupling with a favorable event
described by limit-tree branches and vanishing correspondence errors. -/
structure SplitCrossingCoupling (d : ℕ) (t : ℕ → ℕ) (o : ℕ → Vertex d)
    (condition : ℕ → Set (Configuration d)) extends ConditionalClusterSample d condition where
  favorable : Set Sample
  converges : ∀ s ∈ favorable, ∃ (L : SplitSpanningTree d) (ε : ℕ → ℝ),
    Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, L.approximatedBy (t n) (o n) (config n s) (ε n)

/-- If the coupling has a positive mass of favorable limit samples,
its conditional marginal crossing probabilities are eventually bounded below. -/
theorem SplitCrossingCoupling.eventually_cond_crossAll {d : ℕ}
    {t : ℕ → ℕ} {o : ℕ → Vertex d} {condition : ℕ → Set (Configuration d)}
    (B : SplitCrossingCoupling d t o condition)
    (ht : Tendsto t atTop atTop) (ho : ∀ n, o n ∈ centeredBox d ((t n - 1) / 32))
    {a : ℝ} (ha : 0 ≤ a) (hpos : ENNReal.ofReal a < B.μ B.favorable) :
    ∀ᶠ n in atTop, a ≤ (ProbabilityTheory.cond (percolation d (criticalPoint d))
      (condition n)).real (crossAll (t n) (t n) (o n)) := by
  letI := B.measurableSpace
  letI := B.probability
  let A (n : ℕ) := B.config n ⁻¹' crossAll (t n) (t n) (o n)
  have hE (s : B.Sample) (hs : s ∈ B.favorable) : ∃ n, ∀ m ≥ n, s ∈ A m := by
    obtain ⟨L,ε,hε,happrox⟩ := B.converges s hs
    exact eventually_atTop.1 (L.crossAll_eventually t o (fun n => B.config n s) ε ht hε ho happrox)
  obtain ⟨N,hN⟩ := eventually_measure_ge_of_eventually_mem B.μ B.favorable A hpos hE
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hm := Measure.map_apply (B.measurable_config n) (measurableSet_crossAll (t n) (t n) (o n))
  rw [B.law n] at hm
  have hreal := ENNReal.toReal_mono (measure_ne_top B.μ (A n)) (hN n hn)
  rw [ENNReal.toReal_ofReal ha] at hreal
  exact hreal.trans_eq (congrArg ENNReal.toReal hm).symm

/-- Sequence-wise conditional convergence gives a common threshold over
the allowed lattice roots for a specified cluster-mass condition. -/
theorem eventually_cond_crossAll_of_couplings {d : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (condition : ℕ → Vertex d → Set (Configuration d))
    (hCouple : ∀ (t : ℕ → ℕ) (o : ℕ → Vertex d), (∀ n, n ≤ t n) →
      (∀ n, o n ∈ centeredBox d ((t n - 1) / 32)) →
      ∃ sub : ℕ → ℕ, (∀ n, n ≤ sub n) ∧
        ∃ B : SplitCrossingCoupling d (t ∘ sub) (o ∘ sub)
            (fun n => condition (t (sub n)) (o (sub n))),
          ENNReal.ofReal a < B.μ B.favorable) :
    ∃ T, ∀ t ≥ T, ∀ x ∈ centeredBox d ((t - 1) / 32),
      a ≤ (ProbabilityTheory.cond (percolation d (criticalPoint d))
        (condition t x)).real (crossAll t t x) := by
  by_contra! h
  choose t ht o ho hbad using h
  obtain ⟨sub,hsub,B,hB⟩ := hCouple t o ht ho
  have ht' : Tendsto (t ∘ sub) atTop atTop :=
    tendsto_atTop_mono (fun n => (hsub n).trans (ht (sub n))) tendsto_id
  obtain ⟨N,hN⟩ := eventually_atTop.1 (B.eventually_cond_crossAll ht' (fun n => ho (sub n)) ha hB)
  exact (not_lt_of_ge (hN N le_rfl)) (hbad (sub N))

/-- The only probabilistic inputs to the eventual split-crossing
bound are the critical mass tail and conditional cluster couplings
with positive mass of robust limiting branches. -/
theorem splitCrossInput_of_volume_tail_and_couplings {d : ℕ} {c C : ℝ}
    (hc : 0 < c) (hvol : SpanningVolumeTail d c C)
    (hCouple : ∀ J : ℕ, ∃ a : ℝ, 0 < a ∧
      ∀ j < J, ∀ (t : ℕ → ℕ) (o : ℕ → Vertex d), (∀ n, n ≤ t n) →
      (∀ n, o n ∈ centeredBox d ((t n - 1) / 32)) →
      ∃ sub : ℕ → ℕ, (∀ n, n ≤ sub n) ∧
        ∃ B : SplitCrossingCoupling d (t ∘ sub) (o ∘ sub)
            (fun n => spanningMassBin (o (sub n)) (t (sub n)) j),
          ENNReal.ofReal a < B.μ B.favorable) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ SplitCrossInput d c₀ := by
  obtain ⟨J,b,hb,hbin⟩ := spanningMassBin_lower_of_volume_tail hc hvol
  obtain ⟨a,ha,hC⟩ := hCouple J
  have hlocal (j : Fin J) := eventually_cond_crossAll_of_couplings ha.le
    (fun t x => spanningMassBin x t j) (hC j j.isLt)
  choose T hT using hlocal
  refine ⟨a*b,mul_pos ha hb,splitCrossInput_of_size_bins ha.le hb.le 1
    (Finset.univ.sup T) (fun t ht x _ => hbin t ht x) ?_⟩
  intro t ht x hx j hj
  let i : Fin J := ⟨j,hj⟩
  have hle : T i ≤ Finset.univ.sup T := Finset.le_sup (Finset.mem_univ i)
  exact hT i t (hle.trans ht) x hx

/-- With a tail-conditioned coupling, the lower half of the critical
volume-tail estimate suffices for the split crossings. -/
theorem splitCrossInput_of_tail_couplings {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (T₀ : ℕ)
    (hTail : ∀ t ≥ T₀,
      b/(t:ℝ)^2 ≤ (percolation d (criticalPoint d)).real (spanningMassTail t 0))
    (hCouple : ∀ (t : ℕ → ℕ) (o : ℕ → Vertex d), (∀ n, n ≤ t n) →
      (∀ n, o n ∈ centeredBox d ((t n - 1) / 32)) →
      ∃ sub : ℕ → ℕ, (∀ n, n ≤ sub n) ∧
        ∃ B : SplitCrossingCoupling d (t ∘ sub) (o ∘ sub)
            (fun n => spanningMassTail (t (sub n)) (o (sub n))),
          ENNReal.ofReal a < B.μ B.favorable) :
    SplitCrossInput d (a*b) := by
  obtain ⟨T,hT⟩ := eventually_cond_crossAll_of_couplings ha.le spanningMassTail hCouple
  refine ⟨max T₀ T,?_⟩
  intro t ht x hx
  have htail : b/(t:ℝ)^2 ≤
      (percolation d (criticalPoint d)).real (spanningMassTail t x) := by
    change b/(t:ℝ)^2 ≤ (percolation d (criticalPoint d) (spanningMassTail t x)).toReal
    rw [spanningMassTail_measure_eq_origin]
    exact hTail t ((le_max_left _ _).trans ht)
  have h := measureReal_ge_of_cond_and_mass (percolation d (criticalPoint d))
    (measurableSet_spanningMassTail t x) ha.le (div_nonneg hb.le (sq_nonneg _))
    (hT t ((le_max_right _ _).trans ht) x hx) htail
  simpa only [mul_div_assoc] using h

end NearCritical.Section10
