module

public import NearCritical.ChemicalUpperReduction
public import NearCritical.ConductivityTranslation
public import NearCritical.Slab

/-! Literal odd box and the extra exit layer of source lem.nw.path and
lem.chem.crossing. The path construction/probability lower bound remain open. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory

/-- F- is the bottom layer of the odd box of side 2r+1. -/
def chemicalBottomFace (d r : ℕ) (i : Fin d) : Finset (Vertex d) :=
  (centeredBox d r).filter (fun x => x i = -(r:ℤ))

/-- F+ is one layer ABOVE the top, preserving the source exit-edge convention. -/
def chemicalExitFace (d r : ℕ) (i : Fin d) : Finset (Vertex d) :=
  ((centeredBox d r).filter (fun x => x i = (r:ℤ))).image (fun x => bondTip (x,i))

def chemicalCrossingSupport (d r : ℕ) (i : Fin d) : Finset (Vertex d) :=
  centeredBox d r ∪ chemicalExitFace d r i

lemma chemicalExitFace_coordinate {d r : ℕ} (i : Fin d) {y : Vertex d}
    (hy : y ∈ chemicalExitFace d r i) : y i = (r:ℤ)+1 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  simp only [bondTip,Function.update_self]
  rw [(Finset.mem_filter.mp hx).2]

lemma chemicalCrossingSupport_subset_sitesPlus (d r : ℕ) (i : Fin d) :
    chemicalCrossingSupport d r i ⊆ sitesPlus (centeredBox d r) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact base_mem_sitesPlus hx
  · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact tip_mem_sitesPlus (Finset.mem_filter.mp hy).1 i

/-- The box plus exit layer embeds in the literal open cube Lambda_(2L).
The restriction r>=1 is harmless at large source scales; r=0 would fail at F+. -/
lemma chemicalCrossingSupport_subset_pairBox {d r : ℕ} (i : Fin d) (hr : 1≤r) :
    chemicalCrossingSupport d r i ⊆ chemicalPairBox d (2*r+1) := by
  intro x hx
  have hxS := chemicalCrossingSupport_subset_sitesPlus d r i hx
  change x ∈ Fintype.piFinset _
  rw [Fintype.mem_piFinset]
  intro j
  have h := sitesPlus_coordinate_bounds (centeredBox d r) j
    (fun y hy => (mem_centeredBox.mp hy) j) x hxS
  simp only [Finset.mem_Ioo]
  push_cast
  omega

lemma chemicalCrossing_face_gap {d r : ℕ} (i : Fin d) {x y : Vertex d}
    (hx : x ∈ chemicalBottomFace d r i) (hy : y ∈ chemicalExitFace d r i) :
    (y i:ℝ)-(x i:ℝ) = (2*r+1:ℕ) := by
  rw [(Finset.mem_filter.mp hx).2,chemicalExitFace_coordinate i hy]
  push_cast
  ring

lemma graphNStep_center_translation {d : ℕ} (a : Vertex d) (ω : Configuration d)
    {n : ℕ} {x y : Vertex d} (h : graphNStep (openGraph ω) n (a+x) (a+y)) :
    graphNStep (openGraph (translateConfiguration a ω)) n x y := by
  induction n generalizing y with
  | zero => exact add_left_cancel h
  | succ n ih =>
    obtain ⟨z,hz,hzy⟩ := h
    refine ⟨-a+z,ih (by simpa using hz),?_⟩
    apply (openGraph_translate_adj a ω (-a+z) y).2
    simpa using hzy

/-- Source confined crossing event for B_L=a+Lambda_L, L=2r+1. Endpoints are
parametrized before translation; confinement includes exactly the exit layer. -/
def chemicalBoxCrossingEvent {d : ℕ} (a : Vertex d) (r : ℕ) (i : Fin d)
    (K : ℝ) : Set (Configuration d) :=
  {ω | ∃ x y : Vertex d, x ∈ chemicalBottomFace d r i ∧ y ∈ chemicalExitFace d r i ∧
    ∃ n : ℕ, (n:ℝ) ≤ K*(2*r+1:ℕ) ∧
      graphNStep (restrictedGraph ω (translateSites a (chemicalCrossingSupport d r i) : Set (Vertex d)))
        n (a+x) (a+y)}

lemma measurableSet_chemicalBoxCrossingEvent {d : ℕ} (a : Vertex d) (r : ℕ)
    (i : Fin d) (K : ℝ) : MeasurableSet (chemicalBoxCrossingEvent a r i K) := by
  unfold chemicalBoxCrossingEvent
  simp only [Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro y
  apply MeasurableSet.inter (MeasurableSet.const _)
  apply MeasurableSet.inter (MeasurableSet.const _)
  apply MeasurableSet.iUnion
  intro n
  exact (MeasurableSet.const _).inter (measurableSet_graphNStep _
    (measurableSet_restricted_adj _) n (a+x) (a+y))

/-- Centering a genuine confined crossing gives the actual span event. -/
theorem chemicalBoxCrossing_subset_span {d r : ℕ} (a : Vertex d) (i : Fin d)
    (K : ℝ) (hr : 1≤r) :
    chemicalBoxCrossingEvent a r i K ⊆
      translateConfiguration a ⁻¹' chemicalSpanEvent i (2*r+1) K := by
  rintro ω ⟨x,y,hx,hy,n,hlen,hw⟩
  have hstep : graphNStep (openGraph ω) n (a+x) (a+y) :=
    graphNStep_mono (show restrictedGraph ω
      (translateSites a (chemicalCrossingSupport d r i) : Set (Vertex d)) ≤ openGraph ω
      from fun _ _ h => h.1) hw
  have hc := graphNStep_center_translation a ω hstep
  obtain ⟨w,hwlen⟩ := (graphNStep_iff_exists_walk _ _ _ _).1 hc
  apply chemicalSpanEvent_of_walk i (2*r+1)
    (chemicalCrossingSupport_subset_pairBox i hr (Finset.mem_union_left _ (Finset.mem_filter.mp hx).1))
    (chemicalCrossingSupport_subset_pairBox i hr (Finset.mem_union_right _ hy))
    (by rw [chemicalCrossing_face_gap i hx hy]
        have hL : (0:ℝ) ≤ (2*r+1:ℕ) := Nat.cast_nonneg _
        linarith) w
  simpa [hwlen] using hlen

/-- Actual percolation probability domination, with translation law discharged. -/
theorem chemicalBoxCrossing_probability_le_span {d r : ℕ} (p : unitInterval)
    (a : Vertex d) (i : Fin d) (K : ℝ) (hr : 1≤r) :
    (percolation d p).real (chemicalBoxCrossingEvent a r i K) ≤
      (percolation d p).real (chemicalSpanEvent i (2*r+1) K) := by
  have h := measureReal_mono (μ := percolation d p)
    (chemicalBoxCrossing_subset_span a i K hr)
  have he := map_measureReal_apply (μ := percolation d p)
    (measurable_translateConfiguration a) (measurableSet_chemicalSpanEvent i (2*r+1) K)
  rw [percolation_map_translation] at he
  exact h.trans_eq he.symm

/-- The centered lattice box is literally the source open real cube of odd side. -/
lemma mem_centeredBox_source_open {d r : ℕ} (x : Vertex d) :
    x ∈ centeredBox d r ↔ ∀ j, -((2*(r:ℝ)+1)/2) < (x j:ℝ) ∧
      (x j:ℝ) < (2*(r:ℝ)+1)/2 := by
  rw [mem_centeredBox]
  exact forall_congr' (fun j => int_mem_odd_open_interval r (x j))

/-- The coarse path-length bound in lem.chem.crossing. For M>=2 and
L=(M-1)ell0+s, no limiting comparison or hidden asymptotic constant is used. -/
lemma chemical_crossing_coarse_length_bound {M ell0 s n0 ellStar : ℕ}
    (hM : 2≤M) (hscale : ell0=n0*ellStar) {A : ℝ} (hA : 0≤A) :
    2*(M:ℝ)*A*(ell0:ℝ)^2 ≤
      (4*A*(n0:ℝ))*(ellStar:ℝ)*(((M-1)*ell0+s:ℕ):ℝ) := by
  have hnat : M*ell0 ≤ 2*((M-1)*ell0+s) := by
    have hsub : M-1+1=M := Nat.sub_add_cancel (by omega)
    have hm : M ≤ 2*(M-1) := by omega
    have hm' := Nat.mul_le_mul_right ell0 hm
    nlinarith
  have hreal : (M:ℝ)*(ell0:ℝ) ≤ 2*(((M-1)*ell0+s:ℕ):ℝ) := by
    exact_mod_cast hnat
  have hm := mul_le_mul_of_nonneg_left hreal
    (show 0≤2*A*(ell0:ℝ) by positivity)
  have hs : (ell0:ℝ)=(n0:ℝ)*(ellStar:ℝ) := by exact_mod_cast hscale
  calc
    _ ≤ 4*A*(ell0:ℝ)*(((M-1)*ell0+s:ℕ):ℝ) := by nlinarith [hm]
    _ = _ := by rw [hs]; ring

lemma chemicalBoxCrossingEvent_of_walk {d r : ℕ} (a : Vertex d) (i : Fin d)
    {ω : Configuration d} {K : ℝ} {x y : Vertex d}
    (hx : x ∈ chemicalBottomFace d r i) (hy : y ∈ chemicalExitFace d r i)
    (w : (restrictedGraph ω (translateSites a (chemicalCrossingSupport d r i) :
      Set (Vertex d))).Walk (a+x) (a+y))
    (hlen : (w.length:ℝ)≤K*(2*r+1:ℕ)) : ω ∈ chemicalBoxCrossingEvent a r i K := by
  refine ⟨x,y,hx,hy,w.length,hlen,?_⟩
  exact (graphNStep_iff_exists_walk _ _ _ _).2 ⟨w,rfl⟩

end NearCritical
