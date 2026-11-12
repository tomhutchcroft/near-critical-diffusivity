module

public import NearCritical.ChemicalCrossingGeometry
public import NearCritical.RectangleBoundary

/-! Literal coarse box B_L of source subsec.nw.strategy. The even mesh is 2t
and each microscopic cube has odd side 2r+1. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Filter

def chemicalCoarseIndices (d M : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range M)

def chemicalCoarseCenter {d : ℕ} (t : ℕ) (a : Fin d → ℕ) : Vertex d :=
  fun j => (2*t*a j : ℕ)

def chemicalCoarseCubeUnion (d M t r : ℕ) : Finset (Vertex d) :=
  (chemicalCoarseIndices d M).biUnion
    (fun a => translateSites (chemicalCoarseCenter t a) (centeredBox d r))

def chemicalCoarseBox (d M t r : ℕ) : Finset (Vertex d) :=
  latticeRectangle (fun _ => -(r:ℤ)) (fun _ => (2*(M-1)*t+r:ℕ))

def chemicalCoarseRadius (M t r : ℕ) : ℕ := (M-1)*t+r

def chemicalCoarseSide (M t r : ℕ) : ℕ := (M-1)*(2*t)+(2*r+1)

lemma chemicalCoarseSide_eq (M t r : ℕ) :
    chemicalCoarseSide M t r = 2*chemicalCoarseRadius M t r+1 := by
  unfold chemicalCoarseSide chemicalCoarseRadius
  ring

lemma chemicalCoarseBox_centered (d M t r : ℕ) :
    chemicalCoarseBox d M t r =
      translateSites (fun _ => ((M-1)*t:ℕ)) (centeredBox d (chemicalCoarseRadius M t r)) := by
  classical
  ext x
  rw [translateSites,Finset.mem_image]
  constructor
  · intro hx
    refine ⟨fun j => x j-((M-1)*t:ℕ),mem_centeredBox.mpr ?_,?_⟩
    · intro j
      have h := mem_latticeRectangle.mp hx j
      dsimp [chemicalCoarseRadius]
      push_cast at *
      constructor <;> nlinarith
    · ext j
      simp
  · rintro ⟨y,hy,rfl⟩
    apply mem_latticeRectangle.mpr
    intro j
    have h := mem_centeredBox.mp hy j
    dsimp only [Pi.add_apply]
    dsimp [chemicalCoarseRadius] at h
    push_cast at *
    constructor <;> nlinarith

lemma chemicalCoarseCubeUnion_subset (d M t r : ℕ) :
    chemicalCoarseCubeUnion d M t r ⊆ chemicalCoarseBox d M t r := by
  intro x hx
  obtain ⟨a,ha,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  have ha' : ∀ j, a j<M := by simpa [chemicalCoarseIndices,Fintype.mem_piFinset] using ha
  apply mem_latticeRectangle.mpr
  intro j
  have hvj := mem_centeredBox.mp hv j
  have haj : a j ≤ M-1 := by have := ha' j; omega
  have hc : 2*t*a j ≤ 2*(M-1)*t := by nlinarith [Nat.mul_le_mul_left (2*t) haj]
  have hc' : (2*t*a j:ℕ) ≤ (2*(M-1)*t:ℕ) := hc
  have hr : (0:ℤ) ≤ (2*t*a j:ℕ) := by positivity
  have hcZ : ((2*t*a j:ℕ):ℤ) ≤ (2*(M-1)*t:ℕ) := by exact_mod_cast hc'
  change -(r:ℤ) ≤ ((2*t*a j:ℕ):ℤ)+v j ∧
    ((2*t*a j:ℕ):ℤ)+v j ≤ (2*(M-1)*t+r:ℕ)
  push_cast at hcZ hr ⊢
  omega

lemma chemicalCoarseCubeUnion_lower_corner (d t r : ℕ) {M : ℕ} (hM : 1≤M) :
    (fun _ : Fin d => -(r:ℤ)) ∈ chemicalCoarseCubeUnion d M t r := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(fun _ => 0),?_,?_⟩
  · simp [chemicalCoarseIndices,Fintype.mem_piFinset,show 0<M by omega]
  · have hv : (fun _ : Fin d => -(r:ℤ)) ∈ centeredBox d r :=
      mem_centeredBox.mpr (fun _ => by constructor <;> omega)
    apply Finset.mem_image.mpr
    refine ⟨(fun _ => -(r:ℤ)),hv,?_⟩
    ext j
    simp [chemicalCoarseCenter]

lemma chemicalCoarseCubeUnion_upper_corner (d t r : ℕ) {M : ℕ} (hM : 1≤M) :
    (fun _ : Fin d => ((2*(M-1)*t+r:ℕ):ℤ)) ∈ chemicalCoarseCubeUnion d M t r := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(fun _ => M-1),?_,?_⟩
  · simp [chemicalCoarseIndices,Fintype.mem_piFinset,show M-1<M by omega]
  · apply Finset.mem_image.mpr
    refine ⟨(fun _ => (r:ℤ)),mem_centeredBox.mpr (fun _ => by constructor <;> omega),?_⟩
    ext j
    simp [chemicalCoarseCenter]
    ring

/-- B_L really is the smallest coordinate rectangle containing all coarse cubes. -/
theorem chemicalCoarseBox_least {d M t r : ℕ} (hM : 1≤M) {lo hi : Vertex d}
    (h : chemicalCoarseCubeUnion d M t r ⊆ latticeRectangle lo hi) :
    chemicalCoarseBox d M t r ⊆ latticeRectangle lo hi := by
  intro x hx
  have hl := mem_latticeRectangle.mp (h (chemicalCoarseCubeUnion_lower_corner d t r hM))
  have hh := mem_latticeRectangle.mp (h (chemicalCoarseCubeUnion_upper_corner d t r hM))
  apply mem_latticeRectangle.mpr
  intro j
  have hj := mem_latticeRectangle.mp hx j
  exact ⟨(hl j).1.trans hj.1,hj.2.trans (hh j).2⟩

lemma chemicalCoarseSide_tendsto {t r : ℕ} (ht : 1≤t) :
    Tendsto (fun M => chemicalCoarseSide M t r) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b+1)] with M hM
  have hmul : M-1 ≤ (M-1)*t := Nat.le_mul_of_pos_right _ ht
  rw [chemicalCoarseSide_eq]
  unfold chemicalCoarseRadius
  omega

lemma chemicalCoarseRadius_eventually_pos {t r : ℕ} (ht : 1≤t) :
    ∀ᶠ M : ℕ in atTop, 1≤chemicalCoarseRadius M t r := by
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hmul : M-1 ≤ (M-1)*t := Nat.le_mul_of_pos_right _ ht
  unfold chemicalCoarseRadius
  omega

/-- The source M-dependent confined crossing feeds the span-event probability
at exactly L=(M-1)ell0+s. No cofinality/centering premise is left here. -/
theorem chemicalCoarseCrossing_probability_le_span {d M t r : ℕ}
    (p : unitInterval) (i : Fin d) (K : ℝ) (hM : 2≤M) (ht : 1≤t) :
    (percolation d p).real (chemicalBoxCrossingEvent
      (fun _ => ((M-1)*t:ℕ)) (chemicalCoarseRadius M t r) i K) ≤
    (percolation d p).real (chemicalSpanEvent i (chemicalCoarseSide M t r) K) := by
  rw [chemicalCoarseSide_eq]
  apply chemicalBoxCrossing_probability_le_span
  have hmul : M-1 ≤ (M-1)*t := Nat.le_mul_of_pos_right _ ht
  unfold chemicalCoarseRadius
  omega

end NearCritical
