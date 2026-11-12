module

public import NearCritical.LatticeCanonicalMinimizer
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators

/-! Odd-side water cubes with exact volume and source-minimizer gradient bound.
Radius r in the distinguished direction means height 2r+1; transverse radius R
means width 2R+1. These are the source's open real-coordinate boxes at odd sides. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set

/-- Axis-aligned odd-side rectangles centered at the origin. -/
def rectangularBox {d : ℕ} (radii : Fin d → ℕ) : Finset (Vertex d) := by
  classical
  exact Fintype.piFinset (fun j ↦ Finset.Icc (-(radii j : ℤ)) (radii j : ℤ))

lemma mem_rectangularBox {d : ℕ} {radii : Fin d → ℕ} {x : Vertex d} :
    x ∈ rectangularBox radii ↔ ∀ j, -(radii j : ℤ) ≤ x j ∧ x j ≤ (radii j : ℤ) := by
  classical
  simp [rectangularBox, Fintype.mem_piFinset]

lemma rectangularBox_nonempty {d : ℕ} (radii : Fin d → ℕ) : (rectangularBox radii).Nonempty := by
  refine ⟨0, mem_rectangularBox.mpr ?_⟩
  intro j
  change -(radii j : ℤ) ≤ 0 ∧ 0 ≤ (radii j : ℤ)
  omega

lemma card_rectangularBox {d : ℕ} (radii : Fin d → ℕ) :
    (rectangularBox radii).card = ∏ j, (2 * radii j + 1) := by
  classical
  rw [rectangularBox, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j _
  rw [Int.card_Icc]
  omega

/-- Integer coordinates in the source's open odd-side interval are exactly
those in the inclusive radius-r integer interval. -/
lemma int_mem_odd_open_interval (r : ℕ) (z : ℤ) :
    (-(r : ℤ) ≤ z ∧ z ≤ (r : ℤ)) ↔
      -((2 * (r : ℝ) + 1) / 2) < (z : ℝ) ∧ (z : ℝ) < (2 * (r : ℝ) + 1) / 2 := by
  constructor
  · rintro ⟨hl, hh⟩
    have hl' : -(r : ℝ) ≤ (z : ℝ) := by exact_mod_cast hl
    have hh' : (z : ℝ) ≤ (r : ℝ) := by exact_mod_cast hh
    constructor <;> linarith
  · rintro ⟨hl, hh⟩
    have hl' : ((-(r : ℤ) - 1 : ℤ) : ℝ) < (z : ℝ) := by
      push_cast
      linarith
    have hh' : (z : ℝ) < (((r : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    have hli : -(r : ℤ) - 1 < z := by exact_mod_cast hl'
    have hhi : z < (r : ℤ) + 1 := by exact_mod_cast hh'
    omega

lemma mem_rectangularBox_iff_real_open {d : ℕ} (radii : Fin d → ℕ) (x : Vertex d) :
    x ∈ rectangularBox radii ↔ ∀ j,
      -((2 * (radii j : ℝ) + 1) / 2) < (x j : ℝ) ∧
        (x j : ℝ) < (2 * (radii j : ℝ) + 1) / 2 := by
  rw [mem_rectangularBox]
  exact forall_congr' (fun j ↦ int_mem_odd_open_interval (radii j) (x j))

/-- The source Λ_(h,L), with odd h=2r+1 and L=2R+1. -/
def waterCube (d : ℕ) (i : Fin d) (r R : ℕ) : Finset (Vertex d) :=
  rectangularBox (fun j ↦ if j = i then r else R)

lemma waterCube_nonempty (d : ℕ) (i : Fin d) (r R : ℕ) : (waterCube d i r R).Nonempty :=
  rectangularBox_nonempty _

lemma card_waterCube (d : ℕ) (i : Fin d) (r R : ℕ) :
    (waterCube d i r R).card = (2 * r + 1) * (2 * R + 1) ^ (d - 1) := by
  classical
  rw [waterCube, card_rectangularBox]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j : Fin d ↦ 2 * (if j = i then r else R) + 1) (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  have hp : (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
      (2 * (if j = i then r else R) + 1)) =
      ∏ _j ∈ (Finset.univ : Finset (Fin d)).erase i, (2 * R + 1) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [hp, Finset.prod_const]
  simp

lemma rectangularBox_sitesPlus_range {d : ℕ} (radii : Fin d → ℕ) (i : Fin d)
    (x : DomainVertex (rectangularBox radii)) :
    coordinateData i x ∈ Icc (-(radii i : ℝ)) ((radii i : ℝ) + 1) := by
  have hx := sitesPlus_coordinate_bounds (rectangularBox radii) i
    (fun y hy ↦ (mem_rectangularBox.mp hy) i) x.val x.property
  constructor <;> dsimp only [coordinateData]
  · exact_mod_cast hx.1
  · exact_mod_cast hx.2

lemma rectangularBox_negativeFace_coordinate {d : ℕ} (radii : Fin d → ℕ) (i : Fin d)
    {x : DomainVertex (rectangularBox radii)} (hx : x ∈ negativeFace (rectangularBox radii) i) :
    x.val i = -(radii i : ℤ) := by
  classical
  let q : Vertex d := Function.update 0 i (-(radii i : ℤ))
  have hq : q ∈ rectangularBox radii := by
    apply mem_rectangularBox.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simp only [q, Function.update_self]
      omega
    · simp only [q, Function.update_of_ne hj, Pi.zero_apply]
      omega
  have hmin := hx.2 q (base_mem_sitesPlus hq)
  simp only [q, Function.update_self] at hmin
  have hr := sitesPlus_coordinate_bounds (rectangularBox radii) i
    (fun y hy ↦ (mem_rectangularBox.mp hy) i) x.val x.property
  omega

lemma rectangularBox_positiveFace_coordinate {d : ℕ} (radii : Fin d → ℕ) (i : Fin d)
    {x : DomainVertex (rectangularBox radii)} (hx : x ∈ positiveFace (rectangularBox radii) i) :
    x.val i = (radii i : ℤ) + 1 := by
  classical
  let q : Vertex d := Function.update 0 i (radii i : ℤ)
  have hq : q ∈ rectangularBox radii := by
    apply mem_rectangularBox.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simp only [q, Function.update_self]
      omega
    · simp only [q, Function.update_of_ne hj, Pi.zero_apply]
      omega
  have hmax := hx.2 (bondTip (q, i)) (tip_mem_sitesPlus hq i)
  simp only [bondTip, Function.update_self, q] at hmax
  have hr := sitesPlus_coordinate_bounds (rectangularBox radii) i
    (fun y hy ↦ (mem_rectangularBox.mp hy) i) x.val x.property
  omega

lemma rectangularBox_face_height {d : ℕ} (radii : Fin d → ℕ) (i : Fin d)
    {l h : DomainVertex (rectangularBox radii)}
    (hl : l ∈ negativeFace (rectangularBox radii) i) (hh : h ∈ positiveFace (rectangularBox radii) i) :
    coordinateData i h - coordinateData i l = 2 * (radii i : ℝ) + 1 := by
  dsimp only [coordinateData]
  rw [rectangularBox_positiveFace_coordinate radii i hh,
    rectangularBox_negativeFace_coordinate radii i hl]
  push_cast
  ring

lemma waterCube_face_height (d : ℕ) (i : Fin d) (r R : ℕ)
    {l h : DomainVertex (waterCube d i r R)}
    (hl : l ∈ negativeFace (waterCube d i r R) i) (hh : h ∈ positiveFace (waterCube d i r R) i) :
    coordinateData i h - coordinateData i l = 2 * (r : ℝ) + 1 := by
  convert! rectangularBox_face_height (fun j ↦ if j = i then r else R) i hl hh using 1
  simp

/-- The literal source selector satisfies |∇u| <= h on water cubes. -/
theorem sourceMinimizer_waterCube_gradient (d : ℕ) (i : Fin d) (r R : ℕ)
    (η : IssuedBond (waterCube d i r R) → Bool) (e : IssuedBond (waterCube d i r R)) :
    |(issuedNetwork (waterCube d i r R)).gradient (sourceMinimizer (waterCube d i r R) i η) e| ≤
      2 * (r : ℝ) + 1 := by
  have hne : (twoFaceBoundary (waterCube d i r R) i).Nonempty := by
    obtain ⟨l, hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
    exact ⟨l, by rw [twoFaceBoundary_eq_union]; exact Or.inl hl⟩
  have hdata : ∀ x ∈ twoFaceBoundary (waterCube d i r R) i,
      coordinateData i x ∈ Icc (-(r : ℝ)) ((r : ℝ) + 1) := by
    intro x _
    convert! rectangularBox_sitesPlus_range (fun j ↦ if j = i then r else R) i x using 1; simp
  have h := (issuedNetwork (waterCube d i r R)).boundaryAverageMinimizer_gradient_abs_le
    (Network.binaryWeights_nonneg η) (twoFaceBoundary (waterCube d i r R) i)
    (coordinateData i) hne hdata e
  change |(issuedNetwork (waterCube d i r R)).gradient (sourceMinimizer (waterCube d i r R) i η) e| ≤
    (r : ℝ) + 1 - (-(r : ℝ)) at h
  linarith

end NearCritical
