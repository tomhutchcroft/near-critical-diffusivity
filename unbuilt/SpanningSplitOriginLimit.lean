module

public import NearCritical.SpanningSplitReducedTree

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open Filter MeasureTheory Set
open scoped Classical Topology ENNReal

/-- The rooted metric and embedding of the centered scaling limit. -/
structure CenteredEmbeddedTree (d : ℕ) where
  Tree : Type
  metric : PseudoMetricSpace Tree
  root : Tree
  embed : Tree → (Fin d → ℝ)
  continuous : letI := metric; UniformContinuous embed
  projection : letI := metric; ∀ r y b : Tree, ∃ a : Tree,
    dist r a+dist a y = dist r y ∧ 2*dist b a = dist r b+dist b y-dist r y
/-- A centered embedded limit with the guide paths obtained by
concatenating the edges of a sampled reduced tree. -/
structure CenteredGuideTree (d : ℕ) extends CenteredEmbeddedTree d where
  guides : letI := metric; ∀ (f : Fin d × Bool) (pl : Bool), ∃ y : Tree,
    dist (embed y) (splitBranchGuide f pl 1) ≤ (1/128:ℝ) ∧
    ∀ a : Tree, dist root a+dist a y = dist root y →
      ∃ u : ℝ, 0 ≤ u ∧ dist (embed a) (splitBranchGuide f pl u) ≤ (1/128:ℝ)

/-- Pointed chemical and spatial approximation at the origin. -/
def CenteredEmbeddedTree.approximatedBy {d : ℕ} (L : CenteredEmbeddedTree d)
    (t : ℕ) (ω : Configuration d) (ε : ℝ) : Prop :=
  letI := L.metric
  ∃ (c : ℝ) (R : Vertex d → L.Tree → Prop), 0 ≤ c ∧ R 0 L.root ∧
    (∀ x a, R x a → (openGraph ω).Reachable 0 x) ∧
    (∀ x, (openGraph ω).Reachable 0 x → ∃ a, R x a) ∧
    (∀ a, ∃ x, R x a) ∧
    (∀ x a x' a', R x a → R x' a' →
      |c*((openGraph ω).dist x x':ℝ)-dist a a'| ≤ ε) ∧
    (∀ x a, R x a → dist (scaledSpanningVertex t x) (L.embed a) ≤ ε)

abbrev CenteredGuideTree.approximatedBy {d : ℕ} (L : CenteredGuideTree d)
    (t : ℕ) (ω : Configuration d) (ε : ℝ) : Prop :=
  L.toCenteredEmbeddedTree.approximatedBy t ω ε

/-- A sampled reduced tree with the edge paths in their guide tubes.
The geodesic decomposition lists the completed internal edges and the
current stem or leaf edge for every point of a root-to-leaf branch. -/
structure ReducedTreeGuideWitness {d : ℕ} (L : CenteredEmbeddedTree d)
    (E : Type*) [Fintype E] where
  paths : E → SplitEdgePath d
  labels : E → Option ((Fin d × Bool) × Bool)
  leaf : (Fin d × Bool) → Bool → E
  leaf_label : ∀ f pl, labels (leaf f pl) = some (f,pl)
  tubes : ∀ e, dist (paths e) (match labels e with
    | none => 0
    | some i => splitGuidePath i.1 i.2) ≤
      (match labels e with
      | none => 1/(256*((Fintype.card E:ℝ)+1))
      | some _ => 1/256)
  branches : letI := L.metric; ∀ (f : Fin d × Bool) (pl : Bool),
    ∃ (y : L.Tree) (P : Finset E), (∀ e ∈ P, labels e = none) ∧
      L.embed y = (∑ e ∈ P, paths e splitEdgePathEnd) + paths (leaf f pl) splitEdgePathEnd ∧
      ∀ a : L.Tree, dist L.root a + dist a y = dist L.root y →
        (∃ (Q : Finset E) (e : E) (u : Set.Icc (0:ℝ) 1),
          (∀ e' ∈ Q, labels e' = none) ∧ labels e = none ∧
          L.embed a = (∑ e' ∈ Q, paths e' splitEdgePathEnd) + paths e u) ∨
        (∃ u : Set.Icc (0:ℝ) 1,
          L.embed a = (∑ e ∈ P, paths e splitEdgePathEnd) + paths (leaf f pl) u)

def ReducedTreeGuideWitness.toGuideTree {d : ℕ} {L : CenteredEmbeddedTree d}
    {E : Type*} [Fintype E] (W : ReducedTreeGuideWitness L E) : CenteredGuideTree d where
  toCenteredEmbeddedTree := L
  guides := by
    letI := L.metric
    exact reducedTreeGuides_of_edgeTubes L.root L.embed W.paths W.labels W.leaf
      W.leaf_label W.tubes W.branches

/-- The favorable origin coupling transfers to a sequence of roots
whose normalized offsets converge. -/
theorem CenteredGuideTree.approximations_translate {d : ℕ} (L : CenteredGuideTree d)
    (t : ℕ → ℕ) (o : ℕ → Vertex d) (ω : ℕ → Configuration d) (ε : ℕ → ℝ)
    (s : Fin d → ℝ) (hs : ∀ j, |s j| ≤ (1/32:ℝ))
    (hshift : Tendsto (fun n => scaledSpanningVertex (t n) (o n)) atTop (𝓝 s))
    (hε : Tendsto ε atTop (𝓝 0))
    (happrox : ∀ᶠ n in atTop, L.approximatedBy (t n) (ω n) (ε n)) :
    ∃ (L' : SplitSpanningTree d) (ε' : ℕ → ℝ), Tendsto ε' atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, L'.approximatedBy (t n) (o n)
        (translateConfiguration (-o n) (ω n)) (ε' n) := by
  letI := L.metric
  let L' := splitSpanningTree_of_branchGuides L.root L.embed L.continuous L.projection s hs L.guides
  refine ⟨L', L'.eventually_approximatedBy_of_centered s t o
    (fun n => translateConfiguration (-o n) (ω n)) ε hε hshift ?_⟩
  filter_upwards [happrox] with n hn
  obtain ⟨c,R,hc,hroot,hR,hcover,hsurj,hdist,hembed⟩ := hn
  let I := translationGraphIso (-o n) (ω n)
  have hr (x : Vertex d) :
      (openGraph (translateConfiguration (-o n) (ω n))).Reachable (o n) x ↔
        (openGraph (ω n)).Reachable 0 (x-o n) := by
    have h := (SimpleGraph.Iso.reachable_iff (φ := I) (u := o n) (v := x)).symm
    change (openGraph (translateConfiguration (-o n) (ω n))).Reachable (o n) x ↔
      (openGraph (ω n)).Reachable (-o n+o n) (-o n+x) at h
    simpa only [neg_add_cancel,add_comm (-o n) x,← sub_eq_add_neg] using h
  refine ⟨c,fun x a => R (x-o n) a,hc,?_,?_,?_,?_,?_,?_⟩
  · simpa only [sub_self] using hroot
  · intro x a hx
    exact (hr x).mpr (hR _ _ hx)
  · intro x hx
    exact hcover _ ((hr x).mp hx)
  · intro a
    obtain ⟨x,hx⟩ := hsurj a
    exact ⟨x+o n,by simpa only [add_sub_cancel_right] using hx⟩
  · intro x a x' a' hx hx'
    rw [chemicalDist_translate]
    simpa only [add_comm (-o n) x,add_comm (-o n) x',← sub_eq_add_neg] using
      hdist (x-o n) a (x'-o n) a' hx hx'
  · intro x a hx
    have he : L'.embed a-s = L.embed a := by
      change (L.embed a+s)-s = _
      exact add_sub_cancel_right _ _
    rw [he]
    exact hembed _ _ hx

/-- The cited rooted scaling coupling at the origin suffices for the
split-crossing bound at all allowed roots. The favorable event uses
the Brownian guide tubes in the centered continuum-tree embedding. -/
theorem splitCrossInput_of_origin_tail_limit {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (T₀ : ℕ)
    (hTail : ∀ t ≥ T₀,
      b/(t:ℝ)^2 ≤ (percolation d (criticalPoint d)).real (spanningMassTail t 0))
    (hLimit : ∀ t : ℕ → ℕ, Tendsto t atTop atTop →
      ∃ B : ConditionalClusterSample d (fun n => spanningMassTail (t n) 0),
        ∃ E : Set B.Sample, ENNReal.ofReal a < B.μ E ∧
          ∀ z ∈ E, ∃ (L : CenteredGuideTree d) (ε : ℕ → ℝ),
            Tendsto ε atTop (𝓝 0) ∧
            ∀ᶠ n in atTop, L.approximatedBy (t n) (B.config n z) (ε n)) :
    SplitCrossInput d (a*b) := by
  apply splitCrossInput_of_tail_couplings ha hb T₀ hTail
  intro t o ht ho
  obtain ⟨s,hs,sub,hsub,hshift⟩ := split_root_offsets_tendsto_subseq t o ho
  have hts : Tendsto (t ∘ sub) atTop atTop :=
    tendsto_atTop_mono (fun n => (hsub.id_le n).trans (ht (sub n))) tendsto_id
  obtain ⟨B,E,hE,happrox⟩ := hLimit (t ∘ sub) hts
  letI := B.measurableSpace
  let B' : SplitCrossingCoupling d (t ∘ sub) (o ∘ sub)
      (fun n => spanningMassTail (t (sub n)) (o (sub n))) := {
    Sample := B.Sample
    measurableSpace := B.measurableSpace
    μ := B.μ
    probability := B.probability
    config := fun n z => translateConfiguration (-o (sub n)) (B.config n z)
    measurable_config := fun n => (measurable_translateConfiguration _).comp (B.measurable_config n)
    law := by
      intro n
      change Measure.map (translateConfiguration (-o (sub n)) ∘ B.config n) B.μ = _
      rw [← Measure.map_map (measurable_translateConfiguration _) (B.measurable_config n), B.law n]
      exact translate_cond_spanningMassTail (criticalPoint d) (t (sub n)) (o (sub n))
    favorable := E
    converges := by
      intro z hz
      obtain ⟨L,ε,hε,hL⟩ := happrox z hz
      exact L.approximations_translate (t ∘ sub) (o ∘ sub) (fun n => B.config n z)
        ε s hs hshift hε hL }
  exact ⟨sub, hsub.id_le, B', hE⟩

/-- A common reduced-tree law in the origin scaling couplings gives
a single positive split-crossing constant. The law supplies the same
mixture of guide-tube masses for every scale sequence. -/
theorem splitCrossInput_of_reducedTree_limit {d : ℕ} {E Z : Type*} [Fintype E]
    [MeasurableSpace Z] [MeasurableSpace (SplitEdgePath d)]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (law : Z → E → Measure (SplitEdgePath d)) [∀ z e, IsProbabilityMeasure (law z e)]
    (lab : Z → E → Option ((Fin d × Bool) × Bool)) (δ : Z → E → ℝ)
    (hδ : ∀ᵐ z ∂ν, ∀ e, 0 < δ z e)
    (hsupport : ∀ᵐ z ∂ν, ∀ e (g : SplitEdgePath d), g splitEdgePathStart = 0 →
      ∀ r : ℝ, 0 < r → 0 < law z e (Metric.ball g r))
    (hmeas : AEMeasurable (fun z => Measure.pi (law z) (splitReducedTreeTubeEvent (lab z) (δ z))) ν)
    {b : ℝ} (hb : 0 < b) (T₀ : ℕ)
    (hTail : ∀ t ≥ T₀,
      b/(t:ℝ)^2 ≤ (percolation d (criticalPoint d)).real (spanningMassTail t 0))
    (hLimit : ∀ t : ℕ → ℕ, Tendsto t atTop atTop →
      ∃ B : ConditionalClusterSample d (fun n => spanningMassTail (t n) 0),
        ∃ A : Set B.Sample,
          (∫⁻ z, Measure.pi (law z) (splitReducedTreeTubeEvent (lab z) (δ z)) ∂ν) ≤ B.μ A ∧
          ∀ w ∈ A, ∃ (L : CenteredEmbeddedTree d) (_ : ReducedTreeGuideWitness L E) (ε : ℕ → ℝ),
            Tendsto ε atTop (𝓝 0) ∧
            ∀ᶠ n in atTop, L.approximatedBy (t n) (B.config n w) (ε n)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ SplitCrossInput d c₀ := by
  let m := ∫⁻ z, Measure.pi (law z) (splitReducedTreeTubeEvent (lab z) (δ z)) ∂ν
  have hm : 0 < m := split_reduced_tree_tube_mixture_positive ν law lab δ hδ hsupport hmeas
  have hm₁ : m ≤ 1 := by
    calc
      m ≤ ∫⁻ _ : Z, (1:ℝ≥0∞) ∂ν := lintegral_mono (fun _ => prob_le_one)
      _ = 1 := by simp
  have hmfin : m ≠ ∞ := (hm₁.trans_lt ENNReal.one_lt_top).ne
  have hmpos := ENNReal.toReal_pos hm.ne' hmfin
  let a := m.toReal / 2
  have ha : 0 < a := half_pos hmpos
  have hsmall : ENNReal.ofReal a < m := by
    rw [← ENNReal.ofReal_toReal hmfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hmpos).mpr (half_lt_self hmpos)
  refine ⟨a*b,mul_pos ha hb,splitCrossInput_of_origin_tail_limit ha hb T₀ hTail ?_⟩
  intro t ht
  obtain ⟨B,A,hA,hconv⟩ := hLimit t ht
  refine ⟨B,A,hsmall.trans_le hA,?_⟩
  intro w hw
  obtain ⟨L,W,ε,hε,hL⟩ := hconv w hw
  exact ⟨W.toGuideTree,ε,hε,hL⟩

end NearCritical.Section10
