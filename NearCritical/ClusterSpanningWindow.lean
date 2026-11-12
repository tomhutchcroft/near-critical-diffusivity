module

public import NearCritical.CriticalClusterVolume
public import NearCritical.ClusterDecoupling
public import NearCritical.PreGoodUpperCount

/-! Source prop.num_spanning_new Step1, eq.bound.delta2. The actual strict
size window is combined with component graph property and all labelled faces.
The large-volume input is derived from (A). Small-volume control and actual
spanning probability remain explicit standard-input instantiations. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical

/-- Actual source X event with strict lower and upper volume cutoffs. -/
def spanningPropertyWindowEvent {d : ℕ} {φ : Type*}
    (Q : Finset (Vertex d)) (faces : φ → Finset (Vertex d)) (x : Vertex d)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a b : ℝ) :
    Set (Configuration d) :=
  {ω | rootedClusterProperty Q x P ω ∧ ω ∈ finiteRootSpanningEvent Q faces x ∧
    a < ((finiteBoxCluster ω Q x).card : ℝ) ∧
      ((finiteBoxCluster ω Q x).card : ℝ) < b}

/-- The literal window event is a property of the component and its induced
open graph, so it fits the existing nonmonotone count-decoupling interface. -/
lemma spanningPropertyWindowEvent_eq_rooted {d : ℕ} {φ : Type*}
    (Q : Finset (Vertex d)) (faces : φ → Finset (Vertex d)) (x : Vertex d)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a b : ℝ) :
    spanningPropertyWindowEvent Q faces x P a b =
      {ω | rootedClusterProperty Q x
        (fun G C => P G C ∧ (∀ i, (C ∩ faces i).Nonempty) ∧
          a < (C.card:ℝ) ∧ (C.card:ℝ) < b) ω} := by
  rfl

lemma measurableSet_spanningPropertyWindowEvent {d : ℕ} {φ : Type*}
    (Q : Finset (Vertex d)) (faces : φ → Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a b : ℝ) :
    MeasurableSet (spanningPropertyWindowEvent Q faces x P a b) := by
  rw [spanningPropertyWindowEvent_eq_rooted]
  exact measurableSet_rootedClusterProperty Q x hx _

/-- Pure actual-event subtraction step; no conditional-probability identity
or monotonicity of the component property is required. -/
theorem spanningPropertyWindow_probability_lower {d : ℕ} {φ : Type*}
    (p : unitInterval) (Q : Finset (Vertex d)) (faces : φ → Finset (Vertex d))
    (x : Vertex d) (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (a b δ : ℝ)
    (hproperty : δ*(percolation d p).real (finiteRootSpanningEvent Q faces x) ≤
      (percolation d p).real
        ({ω | rootedClusterProperty Q x P ω} ∩ finiteRootSpanningEvent Q faces x))
    (hlow : (percolation d p).real
      ({ω | ((finiteBoxCluster ω Q x).card : ℝ) ≤ a} ∩ finiteRootSpanningEvent Q faces x) ≤
        (δ/4)*(percolation d p).real (finiteRootSpanningEvent Q faces x))
    (hhigh : (percolation d p).real
      ({ω | b ≤ ((finiteBoxCluster ω Q x).card : ℝ)} ∩ finiteRootSpanningEvent Q faces x) ≤
        (δ/4)*(percolation d p).real (finiteRootSpanningEvent Q faces x)) :
    (δ/2)*(percolation d p).real (finiteRootSpanningEvent Q faces x) ≤
      (percolation d p).real (spanningPropertyWindowEvent Q faces x P a b) := by
  let S := finiteRootSpanningEvent Q faces x
  let G := spanningPropertyWindowEvent Q faces x P a b
  let L := {ω : Configuration d | ((finiteBoxCluster ω Q x).card : ℝ) ≤ a} ∩ S
  let H := {ω : Configuration d | b ≤ ((finiteBoxCluster ω Q x).card : ℝ)} ∩ S
  have hcover : ({ω | rootedClusterProperty Q x P ω} ∩ S) ⊆ (G ∪ L) ∪ H := by
    rintro ω ⟨hp,hs⟩
    by_cases hl : ((finiteBoxCluster ω Q x).card : ℝ) ≤ a
    · exact Or.inl (Or.inr ⟨hl,hs⟩)
    · by_cases hh : b ≤ ((finiteBoxCluster ω Q x).card : ℝ)
      · exact Or.inr ⟨hh,hs⟩
      · exact Or.inl (Or.inl ⟨hp,hs,lt_of_not_ge hl,lt_of_not_ge hh⟩)
  have hb : (percolation d p).real ({ω | rootedClusterProperty Q x P ω} ∩ S) ≤
      (percolation d p).real G + (percolation d p).real L + (percolation d p).real H := by
    calc
      _ ≤ (percolation d p).real ((G ∪ L) ∪ H) := measureReal_mono hcover
      _ ≤ (percolation d p).real (G ∪ L) + (percolation d p).real H := measureReal_union_le _ _
      _ ≤ _ := add_le_add (measureReal_union_le G L) (le_refl ((percolation d p).real H))
  change (δ/2)*(percolation d p).real S ≤ (percolation d p).real G
  change δ*(percolation d p).real S ≤ _ at hproperty
  change (percolation d p).real L ≤ (δ/4)*(percolation d p).real S at hlow
  change (percolation d p).real H ≤ (δ/4)*(percolation d p).real S at hhigh
  linarith

/-- ONE upper-volume cutoff before all radii, domains, roots, labelled face
families and graph properties. Only the small-volume estimate remains a tail
hypothesis; the large-volume estimate is derived from actual assumption(A). -/
theorem critical_spanningPropertyWindow_lower {d : ℕ} (hd : 2 ≤ d)
    (hA : TwoPointAsymptotics d) (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Q : Finset (Vertex d)), Q ⊆ centeredBox d N →
      ∀ x ∈ Q, ∀ (φ : Type*) (faces : φ → Finset (Vertex d))
        (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (a : ℝ),
        c/(N+1:ℝ)^2 ≤ (percolation d (criticalPoint d)).real (finiteRootSpanningEvent Q faces x) →
        δ*(percolation d (criticalPoint d)).real (finiteRootSpanningEvent Q faces x) ≤
          (percolation d (criticalPoint d)).real
            ({ω | rootedClusterProperty Q x P ω} ∩ finiteRootSpanningEvent Q faces x) →
        (percolation d (criticalPoint d)).real
          ({ω | ((finiteBoxCluster ω Q x).card : ℝ) ≤ a} ∩ finiteRootSpanningEvent Q faces x) ≤
            (δ/4)*(percolation d (criticalPoint d)).real (finiteRootSpanningEvent Q faces x) →
        (δ/2)*(percolation d (criticalPoint d)).real (finiteRootSpanningEvent Q faces x) ≤
          (percolation d (criticalPoint d)).real
            (spanningPropertyWindowEvent Q faces x P a (C*(N+1:ℝ)^4)) := by
  obtain ⟨K,hK,hjoint⟩ := critical_finiteBoxCluster_volume_joint_ratio hd hA
  let C := 1+4*K/(δ*c)
  have hC : 0 < C := by dsimp [C]; positivity
  have hscalar : K/(C*c) ≤ δ/4 := by
    apply (div_le_iff₀ (mul_pos hC hc)).mpr
    have he : (4*K/(δ*c))*(δ*c) = 4*K := by
      field_simp [ne_of_gt hδ, ne_of_gt hc]
    have hprod : 0 < δ*c := mul_pos hδ hc
    dsimp [C]
    nlinarith
  refine ⟨C,hC,?_⟩
  intro N Q hQ x hx φ faces P a hspan hproperty hlow
  let μ := percolation d (criticalPoint d)
  let S := finiteRootSpanningEvent Q faces x
  have hSpos : 0 < μ.real S := lt_of_lt_of_le (by positivity : 0 < c/(N+1:ℝ)^2) hspan
  have hratio := (hjoint N Q hQ x hx C c hC hc S hspan).trans hscalar
  have hhigh : μ.real
      ({ω | C*(N+1:ℝ)^4 ≤ ((finiteBoxCluster ω Q x).card : ℝ)} ∩ S) ≤
        (δ/4)*μ.real S := (div_le_iff₀ hSpos).mp hratio
  exact spanningPropertyWindow_probability_lower (criticalPoint d) Q faces x P
    a (C*(N+1:ℝ)^4) δ hproperty hlow hhigh

end NearCritical
