module

public import NearCritical.LatticeFullConductivity
public import NearCritical.LatticeFaces
public import NearCritical.Mecke
public import NearCritical.DifferentialInequality

/-! Source `lem.boundary` (main.tex 1627): the boundary-layer lower bound for
the full-Dirichlet annealed conductivity of a cube,
`A_11(Lambda_L, p) >= p/(2L)`.

For the odd cube `centeredBox d r` (side `n = 2r+1`) and any second direction
`j != i`, every issued bond `(x, i)` with `x` on the face `x_j = -r` has both
endpoints on the boundary of the enlarged vertex set, so every admissible
potential has gradient exactly `1` across it. There are at least `|Lambda|/n`
such bonds, each open with probability `p`. This gives the slightly sharper
`p/n <= A_11(Lambda_n, p)`; the source's `(L-1)L^(d-2)` count omits the bonds
leaving the cube, which belong to the issued set `E^+`.

Unconditional. -/
@[expose] public section
noncomputable section
namespace NearCritical.BoundaryLayer
open MeasureTheory
open scoped Classical

section Expectation
variable {E : Type*} [Fintype E]

lemma finiteExpectation_const_one (p : unitInterval) :
    finiteExpectation (p:ℝ) (fun _ : E → Bool => (1:ℝ)) = 1 := by
  rw [← integral_finite_bernoulli p (fun _ : E → Bool => (1:ℝ))]
  simp

lemma finiteExpectation_zero (p : ℝ) :
    finiteExpectation p (fun _ : E → Bool => (0:ℝ)) = 0 := by
  simp [finiteExpectation]

/-- Each coordinate is open with probability `p`. -/
lemma finiteExpectation_open_indicator (p : unitInterval) (e : E) :
    finiteExpectation (p:ℝ) (fun η : E → Bool => if η e then (1:ℝ) else 0) = (p:ℝ) := by
  have h := BernoulliCalculus.finiteExpectation_mecke (p:ℝ) e (fun _ : E → Bool => (1:ℝ))
  simp only [one_mul] at h
  rw [h, finiteExpectation_const_one, mul_one]

end Expectation

/-- Quenched bound: the full conductivity dominates the normalized number of
open issued bonds in direction `i` based on the face `x_j = -r`. -/
theorem localFull_ge_face_bonds {d r : ℕ} (i j : Fin d) (hij : i ≠ j)
    (η : IssuedBond (centeredBox d r) → Bool) :
    (1/((centeredBox d r).card:ℝ)) *
        (∑ e : IssuedBond (centeredBox d r),
          if e.val.1 j = -(r:ℤ) ∧ e.val.2 = i then (if η e then (1:ℝ) else 0) else 0) ≤
      localFullConductivity (centeredBox d r) i η := by
  have hbounds := sitesPlus_coordinate_bounds (centeredBox d r) j
    (fun y hy => (mem_centeredBox.mp hy) j)
  have hmain : (∑ e : IssuedBond (centeredBox d r),
      if e.val.1 j = -(r:ℤ) ∧ e.val.2 = i then (if η e then (1:ℝ) else 0) else 0) /
        ((centeredBox d r).card:ℝ) ≤ localFullConductivity (centeredBox d r) i η := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply le_csInf ((issuedNetwork (centeredBox d r)).energyValues_nonempty _ _ _)
    rintro t ⟨u, hu, rfl⟩
    apply Finset.sum_le_sum
    intro e _
    have ha0 : (0:ℝ) ≤ if η e then (1:ℝ) else 0 := by split_ifs <;> norm_num
    by_cases he : e.val.1 j = -(r:ℤ) ∧ e.val.2 = i
    · rw [if_pos he]
      have heU : e.val.1 ∈ centeredBox d r := (Finset.mem_product.mp e.property).1
      have hj2 : j ≠ e.val.2 := by
        rw [he.2]
        exact hij.symm
      have htipj : bondTip e.val j = e.val.1 j := by
        simp only [bondTip]
        exact Function.update_of_ne hj2 _ _
      have htipi : bondTip e.val i = e.val.1 i + 1 := by
        simp only [bondTip]
        rw [← he.2]
        exact Function.update_self _ _ _
      have hmin1 : ∀ y ∈ sitesPlus (centeredBox d r), e.val.1 j ≤ y j := by
        intro y hy
        rw [he.1]
        exact (hbounds y hy).1
      have hmin2 : ∀ y ∈ sitesPlus (centeredBox d r), bondTip e.val j ≤ y j := by
        intro y hy
        rw [htipj, he.1]
        exact (hbounds y hy).1
      have htail : (issuedNetwork (centeredBox d r)).tail e ∈ fullBoundary (centeredBox d r) :=
        mem_boundarySites_of_min j (base_mem_sitesPlus heU) hmin1
      have hhead : (issuedNetwork (centeredBox d r)).head e ∈ fullBoundary (centeredBox d r) :=
        mem_boundarySites_of_min j (tip_mem_sitesPlus heU e.val.2) hmin2
      have hg : (issuedNetwork (centeredBox d r)).gradient u e = 1 := by
        change u ((issuedNetwork (centeredBox d r)).head e) -
          u ((issuedNetwork (centeredBox d r)).tail e) = 1
        rw [hu _ hhead, hu _ htail]
        change ((bondTip e.val i : ℤ) : ℝ) - ((e.val.1 i : ℤ) : ℝ) = 1
        rw [htipi]
        push_cast
        ring
      rw [hg]
      simp
    · rw [if_neg he]
      exact mul_nonneg ha0 (sq_nonneg _)
  calc (1/((centeredBox d r).card:ℝ)) *
        (∑ e : IssuedBond (centeredBox d r),
          if e.val.1 j = -(r:ℤ) ∧ e.val.2 = i then (if η e then (1:ℝ) else 0) else 0)
      = (∑ e : IssuedBond (centeredBox d r),
          if e.val.1 j = -(r:ℤ) ∧ e.val.2 = i then (if η e then (1:ℝ) else 0) else 0) /
        ((centeredBox d r).card:ℝ) := by rw [one_div, mul_comm, div_eq_mul_inv]
    _ ≤ _ := hmain

/-- The face `x_j = -r` carries at least `|Lambda|/n` issued bonds in direction `i`. -/
theorem card_box_le_face_bonds {d : ℕ} (r : ℕ) (i j : Fin d) :
    (centeredBox d r).card ≤ (2*r+1) *
      (Finset.univ.filter (fun e : IssuedBond (centeredBox d r) =>
        e.val.1 j = -(r:ℤ) ∧ e.val.2 = i)).card := by
  have hproj : ∀ x ∈ centeredBox d r, Function.update x j (-(r:ℤ)) ∈ centeredBox d r := by
    intro x hx
    apply mem_centeredBox.mpr
    intro k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      omega
    · rw [Function.update_of_ne hk]
      exact (mem_centeredBox.mp hx) k
  have hIcc : (Finset.Icc (-(r:ℤ)) (r:ℤ)).card = 2*r+1 := by
    rw [Int.card_Icc]
    omega
  have h1 : (centeredBox d r).card ≤ (2*r+1) *
      ((centeredBox d r).image (fun x => Function.update x j (-(r:ℤ)))).card := by
    apply Finset.card_le_mul_card_image
    intro a _
    rw [← hIcc]
    apply Finset.card_le_card_of_injOn (fun x : Vertex d => x j)
    · intro x hx
      have hxU := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
      exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ((mem_centeredBox.mp hxU) j))
    · intro x hx y hy hxy
      have hxa := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have hya := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
      funext k
      by_cases hk : k = j
      · subst hk
        exact hxy
      · have h := congrFun (hxa.trans hya.symm) k
        rwa [Function.update_of_ne hk, Function.update_of_ne hk] at h
  have h2 : ((centeredBox d r).image (fun x => Function.update x j (-(r:ℤ)))).card ≤
      (Finset.univ.filter (fun e : IssuedBond (centeredBox d r) =>
        e.val.1 j = -(r:ℤ) ∧ e.val.2 = i)).card := by
    refine le_trans (Finset.card_le_card ?_)
      (Finset.card_image_le (s := Finset.univ.filter (fun e : IssuedBond (centeredBox d r) =>
        e.val.1 j = -(r:ℤ) ∧ e.val.2 = i)) (f := fun e => e.val.1))
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨⟨(Function.update x j (-(r:ℤ)), i),
      Finset.mem_product.mpr ⟨hproj x hx, Finset.mem_univ _⟩⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.update_self _ _ _, rfl⟩
  exact le_trans h1 (Nat.mul_le_mul_left _ h2)

/-- **Source `lem.boundary`** for the odd cube of side `n = 2r+1`:
`p/n <= A_11(Lambda_n, p)` for every parameter, whenever a second coordinate
direction exists. -/
theorem annealedFull_boundary_layer {d : ℕ} (r : ℕ) (i j : Fin d) (hij : i ≠ j)
    (p : unitInterval) :
    (p:ℝ)/(2*(r:ℝ)+1) ≤ annealedFull (centeredBox d r) i (p:ℝ) := by
  have hmono := finiteExpectation_mono p.2.1 p.2.2
    (fun η => localFull_ge_face_bonds (r := r) i j hij η)
  have hterm : ∀ e : IssuedBond (centeredBox d r),
      finiteExpectation (p:ℝ) (fun η : IssuedBond (centeredBox d r) → Bool =>
        if e.val.1 j = -(r:ℤ) ∧ e.val.2 = i then (if η e then (1:ℝ) else 0) else 0) =
      if e.val.1 j = -(r:ℤ) ∧ e.val.2 = i then (p:ℝ) else 0 := by
    intro e
    by_cases he : e.val.1 j = -(r:ℤ) ∧ e.val.2 = i
    · simp only [if_pos he]
      exact finiteExpectation_open_indicator p e
    · simp only [if_neg he]
      exact finiteExpectation_zero (p:ℝ)
  have hsum : (∑ e : IssuedBond (centeredBox d r),
      if e.val.1 j = -(r:ℤ) ∧ e.val.2 = i then (p:ℝ) else 0) =
      ((Finset.univ.filter (fun e : IssuedBond (centeredBox d r) =>
        e.val.1 j = -(r:ℤ) ∧ e.val.2 = i)).card : ℝ) * (p:ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [finiteExpectation_const_mul, finiteExpectation_sum,
    Finset.sum_congr rfl (fun e _ => hterm e), hsum] at hmono
  refine le_trans ?_ hmono
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ((Finset.univ.filter
      (fun e : IssuedBond (centeredBox d r) =>
        e.val.1 j = -(r:ℤ) ∧ e.val.2 = i)).card : ℝ) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ((centeredBox d r).card : ℝ) := ⟨_, rfl⟩
  have hcount : c ≤ (2*(r:ℝ)+1) * S := by
    rw [hcdef, hSdef]
    exact_mod_cast card_box_le_face_bonds r i j
  rw [← hSdef, ← hcdef]
  have hc : 0 < c := by
    rw [hcdef]
    refine Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨0, mem_centeredBox.mpr ?_⟩)
    intro k
    change -(r:ℤ) ≤ 0 ∧ 0 ≤ (r:ℤ)
    omega
  have hn : (0:ℝ) < 2*(r:ℝ)+1 := by positivity
  have hp0 : (0:ℝ) ≤ (p:ℝ) := p.2.1
  have h1 : (p:ℝ) * c ≤ (p:ℝ) * ((2*(r:ℝ)+1) * S) := mul_le_mul_of_nonneg_left hcount hp0
  have e1 : (1/c) * ((p:ℝ) * c) = (p:ℝ) := by
    rw [one_div, mul_comm (p:ℝ) c, inv_mul_cancel_left₀ hc.ne']
  rw [div_le_iff₀ hn]
  calc (p:ℝ) = (1/c) * ((p:ℝ) * c) := e1.symm
    _ ≤ (1/c) * ((p:ℝ) * ((2*(r:ℝ)+1) * S)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1/c * (S * (p:ℝ)) * (2*(r:ℝ)+1) := by ring

/-- **Source `lem.boundary`, literal form** `A_11(Lambda_L, p) >= p/(2L)` with
`L = 2r+1`. -/
theorem annealedFull_boundary_layer_half {d : ℕ} (r : ℕ) (i j : Fin d) (hij : i ≠ j)
    (p : unitInterval) :
    (p:ℝ)/(2*(2*(r:ℝ)+1)) ≤ annealedFull (centeredBox d r) i (p:ℝ) := by
  refine le_trans ?_ (annealedFull_boundary_layer r i j hij p)
  have hn : (0:ℝ) < 2*(r:ℝ)+1 := by positivity
  exact div_le_div_of_nonneg_left p.2.1 hn (by linarith)

end NearCritical.BoundaryLayer
