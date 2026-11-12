module

public import NearCritical.MaskedBulkReflectionLaw
public import NearCritical.MaskedArmNegativePath
public import NearCritical.TwoPhaseSlabMaskGeometry
public import Mathlib.Tactic.Abel

@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

theorem waterCube_reflect_base {d : ℕ} (i : Fin d) (r R : ℕ)
    {x : Vertex d} (hx : x ∈ waterCube d i r R) (hlo : -(r : ℤ) < x i) :
    Pi.single i (1 : ℤ) - x ∈ waterCube d i r R := by
  apply mem_rectangularBox.mpr
  intro j
  have hb := (mem_rectangularBox.mp hx) j
  by_cases hji : j = i
  · subst j
    simp only [ite_true, Pi.sub_apply, Pi.single_eq_same] at hb ⊢
    omega
  · simp only [hji, ite_false, Pi.sub_apply, Pi.single_eq_of_ne hji, zero_sub] at hb ⊢
    omega

private theorem waterCube_reflect_bottom_sitesPlus {d : ℕ} (i : Fin d) (r R : ℕ)
    {y : Vertex d} (hy : y ∈ waterCube d i r R) (hy0 : y i = -(r : ℤ)) :
    Pi.single i (1 : ℤ) - y ∈ sitesPlus (waterCube d i r R) := by
  let z : Vertex d := Pi.single i (1 : ℤ) - y
  let base : Vertex d := Function.update z i (r : ℤ)
  have hb : base ∈ waterCube d i r R := by
    apply mem_rectangularBox.mpr
    intro j
    by_cases hji : j = i
    · subst j
      simp [base] <;> omega
    · have h := (mem_rectangularBox.mp hy) j
      simp only [hji, ite_false, base, Function.update_of_ne hji, z,
        Pi.sub_apply, Pi.single_eq_of_ne hji, zero_sub] at h ⊢
      omega
  have ht : bondTip (base, i) = z := by
    ext j
    by_cases hji : j = i
    · subst j
      simp only [bondTip, Function.update_self, base, z, Pi.sub_apply, Pi.single_eq_same, hy0]
      omega
    · simp [bondTip, base, Function.update_of_ne hji]
  rw [show Pi.single i (1 : ℤ) - y = z from rfl, ← ht]
  exact tip_mem_sitesPlus hb i

private theorem waterCube_reflection_step_issued {d : ℕ} (i : Fin d) (r R : ℕ)
    (ω : Configuration d) {u v : DomainVertex (waterCube d i r R)}
    (h : (openGraph ω).Adj u.val v.val) (hu : u.val ∈ waterCube d i r R)
    (hv : v.val ∈ waterCube d i r R ∨ v.val i = (r : ℤ)+1) :
    ((issuedNetwork (waterCube d i r R)).positiveGraph
      (Network.binaryWeights ((issuedBondSet (waterCube d i r R)).restrict ω)) Set.univ).Adj u v := by
  obtain ⟨e, he, heuv⟩ := h
  have hbase : e.1 ∈ waterCube d i r R := by
    rcases heuv with ⟨he₁,_⟩ | ⟨he₁,he₂⟩
    · exact he₁ ▸ hu
    · rcases hv with hv | hv
      · exact he₁ ▸ hv
      · have hstep := (twoPhase_bond_height_step e i).1
        have hub := (mem_rectangularBox.mp hu) i
        simp only [ite_true] at hub
        rw [← he₁, ← he₂, hv] at hstep
        omega
  let f : IssuedBond (waterCube d i r R) :=
    ⟨e, Finset.mem_product.mpr ⟨hbase, Finset.mem_univ _⟩⟩
  have hne : u ≠ v := by
    intro huv
    have he' : e.1 = bondTip e := by
      rcases heuv with ⟨he₁,he₂⟩ | ⟨he₁,he₂⟩
      · exact he₁.symm.trans ((congrArg Subtype.val huv).trans he₂)
      · exact he₁.symm.trans ((congrArg Subtype.val huv.symm).trans he₂)
    exact bondTip_ne_base e he'.symm
  refine ⟨hne, Set.mem_univ _, Set.mem_univ _, f, ?_, ?_⟩
  · change 0 < Network.binaryWeights ((issuedBondSet (waterCube d i r R)).restrict ω) f
    simp [Network.binaryWeights, Finset.restrict, f, he]
  · rcases heuv with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨Subtype.ext h₁.symm, Subtype.ext h₂.symm⟩
    · exact Or.inr ⟨Subtype.ext h₁.symm, Subtype.ext h₂.symm⟩

private theorem walk_to_waterCube_issued_top {d : ℕ} (i : Fin d) (r R : ℕ)
    (ω : Configuration d) {x y : Vertex d} (w : (openGraph ω).Walk x y)
    (hx : x ∈ sitesPlus (waterCube d i r R)) (hy : y ∈ sitesPlus (waterCube d i r R))
    (hytop : y i = (r : ℤ)+1)
    (hs : ∀ z ∈ w.support, z ∈ waterCube d i r R ∨ z=y) :
    ((issuedNetwork (waterCube d i r R)).positiveGraph
      (Network.binaryWeights ((issuedBondSet (waterCube d i r R)).restrict ω))
      Set.univ).Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x v y hxv w ih =>
    by_cases hxy : x=y
    · subst x
      exact SimpleGraph.Reachable.refl _
    · have hxU := (hs x (by simp)).resolve_right hxy
      have hs' (z) (hz : z ∈ w.support) := hs z (by simp [hz])
      have hv := hs' v w.start_mem_support
      have hvPlus : v ∈ sitesPlus (waterCube d i r R) :=
        by
          rcases hv with hvU | hvy
          · exact base_mem_sitesPlus hvU
          · exact hvy.symm ▸ hy
      have hAdj := waterCube_reflection_step_issued i r R ω
        (u := ⟨x,hx⟩) (v := ⟨v,hvPlus⟩) hxv hxU
        (hv.imp id (fun (h : v = y) => h.symm ▸ hytop))
      exact hAdj.reachable.trans (by apply ih <;> assumption)

/-- Reflect the first-bottom-hit prefix, including its terminal vertical
edge. All reflected preterminal vertices remain base vertices. -/
theorem waterCube_negativeFace_reflected_event {d : ℕ}
    (i : Fin d) (r R : ℕ) (x : DomainVertex (waterCube d i r R))
    (hx : x.val ∈ waterCube d i r R) (hxlo : -(r : ℤ) < x.val i) :
    let a : Vertex d := Pi.single i (1 : ℤ)
    let x' : DomainVertex (waterCube d i r R) :=
      ⟨a-x.val, base_mem_sitesPlus (waterCube_reflect_base i r R hx hxlo)⟩
    latticeBoundaryConnectionEvent (waterCube d i r R) x (negativeFace _ i) ⊆
      translateConfiguration a ⁻¹' (invertConfiguration ⁻¹'
        latticeBoundaryConnectionEvent (waterCube d i r R) x' (positiveFace _ i)) := by
  dsimp only
  intro ω hω
  obtain ⟨y,hy,w,_,hU,hlo⟩ := waterCube_negativeFace_simple_open_prefix i r R ω x hx hxlo hω
  let a : Vertex d := Pi.single i (1 : ℤ)
  let θ := invertConfiguration (translateConfiguration a ω)
  have hcancel (z : Vertex d) : a + -(a-z) = z := by abel
  let f : openGraph ω →g openGraph θ :=
    ⟨fun z => a-z, fun {u v} huv => by
      apply (openGraph_invert_adj _ _ _).2
      apply (openGraph_translate_adj a ω _ _).2
      simpa only [hcancel] using huv⟩
  have htop : (a-y.val) i = (r : ℤ)+1 := by simp [a,hy] <;> omega
  have hyPlus : a-y.val ∈ sitesPlus (waterCube d i r R) :=
    waterCube_reflect_bottom_sitesPlus i r R (hU y.val w.end_mem_support) hy
  let y' : DomainVertex (waterCube d i r R) := ⟨a-y.val,hyPlus⟩
  have hmax : ∀ z ∈ sitesPlus (waterCube d i r R), z i ≤ y'.val i := by
    intro z hz
    have hbound := sitesPlus_coordinate_bounds (waterCube d i r R) i
      (fun v hv => by simpa only [ite_true] using (mem_rectangularBox.mp hv) i) z hz
    exact hbound.2.trans (le_of_eq htop.symm)
  have hface : y' ∈ positiveFace (waterCube d i r R) i :=
    ⟨mem_boundarySites_of_max i hyPlus hmax,hmax⟩
  have hs : ∀ z ∈ (w.map f).support, z ∈ waterCube d i r R ∨ z=a-y.val := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    by_cases hvy : v=y.val
    · exact Or.inr (congrArg f hvy)
    · exact Or.inl (waterCube_reflect_base i r R (hU v hv) (hlo v hv hvy))
  exact ⟨y', hface, walk_to_waterCube_issued_top i r R θ (w.map f)
    (base_mem_sitesPlus (waterCube_reflect_base i r R hx hxlo)) hyPlus htop hs⟩

/-- Under the actual bulk law the negative arm is dominated by the reflected
positive arm. The comparison uses path inclusion and measure invariance. -/
theorem maskedWaterCube_negativeFace_probability_le_reflected {d : ℕ}
    (i : Fin d) (r R : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (p q : unitInterval)
    (x : DomainVertex (waterCube d i r R))
    (hx : x.val ∈ waterCube d i r R) (hxlo : -(r : ℤ) < x.val i) :
    let a : Vertex d := Pi.single i (1 : ℤ)
    let x' : DomainVertex (waterCube d i r R) :=
      ⟨a-x.val, base_mem_sitesPlus (waterCube_reflect_base i r R hx hxlo)⟩
    let U := waterCube d i r R
    let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
    μ.real (latticeBoundaryConnectionEvent U x (negativeFace U i)) ≤
      μ.real (latticeBoundaryConnectionEvent U x' (positiveFace U i)) := by
  dsimp only
  let U := waterCube d i r R
  let μ := bulkPercolation U i (2*(r : ℝ)+1) δ p q
  let a : Vertex d := Pi.single i (1 : ℤ)
  let x' : DomainVertex U :=
    ⟨a-x.val,base_mem_sitesPlus (waterCube_reflect_base i r R hx hxlo)⟩
  let E := latticeBoundaryConnectionEvent U x' (positiveFace U i)
  have hE : MeasurableSet E := by
    change MeasurableSet (((issuedBondSet U).restrict : Configuration d → IssuedBond U → Bool) ⁻¹'
      (issuedNetwork U).boundaryConnectionEvent x' (positiveFace U i))
    exact (Set.toFinite _).measurableSet.preimage (Finset.measurable_restrict _)
  have hmap : μ (translateConfiguration a ⁻¹' (invertConfiguration ⁻¹' E)) = μ E := by
    rw [← Measure.map_apply (measurable_translateConfiguration a)
      (hE.preimage measurable_invertConfiguration),
      ← Measure.map_apply measurable_invertConfiguration hE]
    rw [bulkPercolation_waterCube_map_reflection i r R δ hδ p q]
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (percolationProfile d _)
    infer_instance
  apply ENNReal.toReal_mono (measure_ne_top μ E)
  exact (measure_mono (waterCube_negativeFace_reflected_event i r R x hx hxlo)).trans_eq hmap

end NearCritical
