module

public import NearCritical.SplitCrossBranchMargins

/-! Quantitative separation of the endpoint boxes used by the direct
split-crossing tree. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10
open scoped Classical

private theorem coordinate_gap_le_dist {d R : ℕ} {x y : Vertex d} (j : Fin d)
    (h : (R : ℤ) ≤ |x j - y j|) : (R : ℝ) ≤ dist x y := by
  refine le_trans ?_ (dist_le_pi_dist x y j)
  rw [Int.dist_eq]
  simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub] using
    (Int.cast_le.mpr h : ((R : ℤ) : ℝ) ≤ ((|x j - y j| : ℤ) : ℝ))

private theorem translatedBoxes_separated {d r s R : ℕ} {a b x y : Vertex d}
    (j : Fin d) (hgap : (R : ℤ) + (r : ℤ) + (s : ℤ) ≤ |a j - b j|)
    (hx : x ∈ translateSites a (centeredBox d r))
    (hy : y ∈ translateSites b (centeredBox d s)) : (R : ℝ) ≤ dist x y := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  have hu' := mem_centeredBox.mp hu j
  have hv' := mem_centeredBox.mp hv j
  apply coordinate_gap_le_dist j
  simp only [Pi.add_apply]
  have h₁ := le_abs_self (a j + u j - (b j + v j))
  have h₂ := neg_le_abs (a j + u j - (b j + v j))
  rcases le_total (b j) (a j) with h | h
  · rw [abs_of_nonneg (by omega : 0 ≤ a j - b j)] at hgap
    omega
  · rw [abs_of_nonpos (by omega : a j - b j ≤ 0)] at hgap
    omega

/-- The entry branch and cube-side dummy boxes are all macroscopically
separated, both within a leg and between distinct legs. -/
theorem entryLegBoxes_separated {d t : ℕ} (hd : 2 ≤ d) (ht : 128 ≤ t)
    {f g : Fin d × Bool} {pl ql b c : Bool} {x y : Vertex d}
    (h : (f, pl, b) ≠ (g, ql, c))
    (hx : x ∈ entryLegBox t f pl b) (hy : y ∈ entryLegBox t g ql c) :
    ((t / 64 : ℕ) : ℝ) ≤ dist x y := by
  let a := legBoxCenter t f pl (entryBoxHeight t b)
  let a' := legBoxCenter t g ql (entryBoxHeight t c)
  have hdist (j : Fin d) (hj : ((t / 64 : ℕ) : ℤ) + (legBoxRadius t : ℤ) +
      (legBoxRadius t : ℤ) ≤ |a j - a' j|) : ((t / 64 : ℕ) : ℝ) ≤ dist x y :=
    translatedBoxes_separated j hj hx hy
  obtain ⟨i, s⟩ := f
  obtain ⟨j, u⟩ := g
  by_cases hij : i = j
  · subst j
    by_cases hsu : s = u
    · subst u
      by_cases hp : pl = ql
      · subst ql
        have hbc : b ≠ c := fun e => h (by rw [e])
        apply hdist i
        cases s <;> cases b <;> cases c <;>
          simp [a, a', legBoxCenter, entryBoxHeight, legBoxRadius, abs_eq_max_neg, le_max_iff] at hbc ⊢ <;>
          omega
      · letI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
        obtain ⟨k, hk⟩ := exists_ne i
        apply hdist k
        cases pl <;> cases ql <;>
          simp [a, a', legBoxCenter, hk, legBoxRadius, abs_eq_max_neg, le_max_iff] at hp ⊢ <;> omega
    · apply hdist i
      cases s <;> cases u <;> cases b <;> cases c <;>
        simp [a, a', legBoxCenter, entryBoxHeight, legBoxRadius, abs_eq_max_neg, le_max_iff] at hsu ⊢ <;> omega
  · apply hdist i
    cases s <;> cases b <;> cases ql <;>
      simp [a, a', legBoxCenter, entryBoxHeight, hij, legBoxRadius, abs_eq_max_neg, le_max_iff] <;> omega

/-- Any point of the inner cube is separated from every beyond-cube leg.
This applies to the root, the spine and the two entry boxes. -/
theorem innerCube_splitBeyond_separated {d t : ℕ} (ht : 64 ≤ t)
    {f : Fin d × Bool} {pl : Bool} {x y : Vertex d}
    (hx : x ∈ centeredBox d (7 * t / 16)) (hy : y ∈ splitBeyond t f pl t) :
    ((t / 32 : ℕ) : ℝ) ≤ dist x y := by
  have hax := (Finset.mem_filter.mp hy).2.1
  obtain ⟨i, s⟩ := f
  have hx' := mem_centeredBox.mp hx i
  have h₁ := le_abs_self (x i - y i)
  have h₂ := neg_le_abs (x i - y i)
  apply coordinate_gap_le_dist i
  cases s <;> simp [faceHeight] at hax <;> omega

/-- A signed axial gap is a lower bound for the sup distance. -/
theorem faceHeight_sub_le_dist {d : ℕ} (f : Fin d × Bool) (x y : Vertex d) :
    ((faceHeight f y : ℤ) : ℝ) - ((faceHeight f x : ℤ) : ℝ) ≤ dist x y := by
  obtain ⟨i, s⟩ := f
  refine le_trans ?_ (dist_le_pi_dist x y i)
  rw [Int.dist_eq]
  cases s
  · simp only [faceHeight, Prod.snd, Bool.false_eq_true, if_false, Prod.fst, Int.cast_neg]
    linarith [le_abs_self ((x i : ℝ) - (y i : ℝ))]
  · simpa [faceHeight, neg_sub] using neg_le_abs ((x i : ℝ) - (y i : ℝ))

theorem exteriorBranch_dist_target {d t : ℕ} (ht : 4096 ≤ t)
    {f : Fin d × Bool} {pl : Bool} {x y : Vertex d}
    (hx : x ∈ legBranchBox t f pl false) (hy : y ∈ splitTarget t f pl t) :
    (t : ℝ) / 128 ≤ dist x y := by
  have hN := cast_nat_halfSide_lower t (by omega)
  have hax := (legBranchBox_axial ht hx).2
  change (faceHeight f x : ℝ) ≤ 95 / 64 * (t : ℝ) + (t : ℝ) / 512 at hax
  have hy' : (faceHeight f y : ℝ) = (((t - 1) / 2 : ℕ) : ℝ) + (t : ℝ) := by
    have he := (Finset.mem_filter.mp hy).2
    simpa only [Int.cast_add, Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℝ)) he
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  refine le_trans ?_ (faceHeight_sub_le_dist f x y)
  linarith

theorem exteriorBoxes_dist {d t : ℕ} (ht : 64 ≤ t)
    {f : Fin d × Bool} {pl : Bool} {x y : Vertex d}
    (hx : x ∈ translateSites (interiorLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)))
    (hy : y ∈ translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t))) :
    ((t / 4 : ℕ) : ℝ) ≤ dist x y := by
  have ha := (legBox_height_bounds f pl _ hx).2
  have hb := (legBox_height_bounds f pl _ hy).1
  change faceHeight f x ≤ (((t - 1) / 2 : ℕ) : ℤ) + ((t / 2 : ℕ) : ℤ) +
    (legBoxRadius t : ℤ) at ha
  change (((t - 1) / 2 : ℕ) : ℤ) + (t : ℤ) - (legBoxRadius t : ℤ) -
    (legBoxRadius t : ℤ) ≤ faceHeight f y at hb
  have hgap : ((t / 4 : ℕ) : ℤ) ≤ faceHeight f y - faceHeight f x := by
    unfold legBoxRadius at ha hb
    omega
  refine le_trans ?_ (faceHeight_sub_le_dist f x y)
  simpa only [Int.cast_natCast, Int.cast_sub] using
    (Int.cast_le.mpr hgap : (((t / 4 : ℕ) : ℤ) : ℝ) ≤
      ((faceHeight f y - faceHeight f x : ℤ) : ℝ))

end NearCritical.SplitCrossDirect
