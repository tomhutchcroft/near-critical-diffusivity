module

public import NearCritical.Section10SplitCrossing
public import NearCritical.ConductivityTranslation
public import NearCritical.PreGoodUpperCount
public import NearCritical.SpanningBoundaryDiameter

/-! Two finite terminal sets for each leg of the direct split-crossing proof.
The far cube has a full face in the split target. The interior cube is
strictly separated from it along the same split corridor. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10
open scoped Classical

/-- The centre of a box in a split leg, at signed axial height `h`. -/
def legBoxCenter {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) (h : ℤ) : Vertex d :=
  fun j => if j = f.1 then (if f.2 then h else -h)
    else if pl then 3 * (t : ℤ) / 16 else -(3 * (t : ℤ) / 16)

/-- Radius of both terminal boxes. -/
def legBoxRadius (t : ℕ) : ℕ := t / 64

/-- Box with its outer face at the far end of the corridor. -/
def farLegBoxCenter {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) : Vertex d :=
  legBoxCenter t f pl ((((t - 1) / 2 : ℕ) : ℤ) + (t : ℤ) - (legBoxRadius t : ℤ))

/-- Box strictly inside the corridor and separated from the far face. -/
def interiorLegBoxCenter {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) : Vertex d :=
  legBoxCenter t f pl ((((t - 1) / 2 : ℕ) : ℤ) + ((t / 2 : ℕ) : ℤ))

theorem legBox_height_bounds {d t : ℕ} (f : Fin d × Bool) (pl : Bool) (h : ℤ)
    {y : Vertex d} (hy : y ∈ translateSites (legBoxCenter t f pl h)
      (centeredBox d (legBoxRadius t))) :
    h - (legBoxRadius t : ℤ) ≤ faceHeight f y ∧ faceHeight f y ≤ h + (legBoxRadius t : ℤ) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨i, s⟩ := f
  have hz' := mem_centeredBox.mp hz i
  cases s <;> simp [faceHeight, legBoxCenter, Pi.add_apply] <;> omega

theorem legBox_subset_beyond {d t : ℕ} (ht : 64 ≤ t) (f : Fin d × Bool) (pl : Bool)
    (h : ℤ)
    (hlo : (((t - 1) / 2 : ℕ) : ℤ) < h - (legBoxRadius t : ℤ))
    (hhi : h + (legBoxRadius t : ℤ) ≤ (((t - 1) / 2 : ℕ) : ℤ) + (t : ℤ)) :
    translateSites (legBoxCenter t f pl h) (centeredBox d (legBoxRadius t)) ⊆
      splitBeyond t f pl t := by
  intro y hy
  have hh := legBox_height_bounds f pl h hy
  have hpos := hlo.trans_le hh.1
  have hup := hh.2.trans hhi
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have htrans (j : Fin d) (hj : j ≠ f.1) :
      splitRange t pl ((legBoxCenter t f pl h + z) j) := by
    have hz' := mem_centeredBox.mp hz j
    change -((t / 64 : ℕ) : ℤ) ≤ z j ∧ z j ≤ ((t / 64 : ℕ) : ℤ) at hz'
    cases pl
    · simp only [legBoxCenter, Pi.add_apply, if_neg hj, Bool.false_eq_true,
        if_false, splitRange]
      constructor
      · exact_mod_cast (show -(t : ℤ) < 4 * (-(3 * (t : ℤ) / 16) + z j) by omega)
      · exact_mod_cast (show 8 * (-(3 * (t : ℤ) / 16) + z j) < -(t : ℤ) by omega)
    · simp only [legBoxCenter, Pi.add_apply, if_neg hj, if_true, splitRange]
      constructor
      · exact_mod_cast (show (t : ℤ) < 8 * (3 * (t : ℤ) / 16 + z j) by omega)
      · exact_mod_cast (show 4 * (3 * (t : ℤ) / 16 + z j) < (t : ℤ) by omega)
  refine Finset.mem_filter.mpr ⟨mem_centeredBox.mpr ?_, hpos, htrans⟩
  intro j
  by_cases hj : j = f.1
  · subst j
    obtain ⟨i, s⟩ := f
    cases s <;> simp [faceHeight] at hpos hup ⊢ <;> omega
  · have hz' := mem_centeredBox.mp hz j
    change -((t / 64 : ℕ) : ℤ) ≤ z j ∧ z j ≤ ((t / 64 : ℕ) : ℤ) at hz'
    cases pl <;> simp [legBoxCenter, Pi.add_apply, hj] <;> omega

theorem farLegBox_subset_beyond {d t : ℕ} (ht : 64 ≤ t) (f : Fin d × Bool) (pl : Bool) :
    translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)) ⊆
      splitBeyond t f pl t := by
  unfold farLegBoxCenter
  apply legBox_subset_beyond ht
  · unfold legBoxRadius
    omega
  · omega

theorem interiorLegBox_subset_beyond {d t : ℕ} (ht : 64 ≤ t) (f : Fin d × Bool) (pl : Bool) :
    translateSites (interiorLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)) ⊆
      splitBeyond t f pl t := by
  unfold interiorLegBoxCenter
  apply legBox_subset_beyond ht <;> unfold legBoxRadius <;> omega

theorem farLegBox_face_subset_target {d t : ℕ} (ht : 64 ≤ t) (f : Fin d × Bool)
    (pl : Bool) :
    translateSites (farLegBoxCenter t f pl) (signedCubeFace d (legBoxRadius t) f) ⊆
      splitTarget t f pl t := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hzBox, hzFace⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨farLegBox_subset_beyond ht f pl
    ((mem_translateSites _ _ _).mpr hzBox), ?_⟩
  obtain ⟨i, s⟩ := f
  cases s <;> simp [farLegBoxCenter, legBoxCenter, faceHeight, Pi.add_apply] at hzFace ⊢ <;> omega

theorem legBoxes_disjoint {d t : ℕ} (ht : 64 ≤ t) (f : Fin d × Bool) (pl : Bool) :
    Disjoint (translateSites (interiorLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)))
      (translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t))) := by
  rw [Finset.disjoint_left]
  intro y hy hz
  have h₁ := (legBox_height_bounds f pl _ hy).2
  have h₂ := (legBox_height_bounds f pl _ hz).1
  change faceHeight f y ≤ (((t - 1) / 2 : ℕ) : ℤ) + ((t / 2 : ℕ) : ℤ) +
    (legBoxRadius t : ℤ) at h₁
  change (((t - 1) / 2 : ℕ) : ℤ) + (t : ℤ) - (legBoxRadius t : ℤ) -
    (legBoxRadius t : ℤ) ≤ faceHeight f y at h₂
  unfold legBoxRadius at h₁ h₂
  omega

/-- A full signed face has one free coordinate for each transverse axis. -/
theorem signedCubeFace_card_lower (d r : ℕ) (f : Fin d × Bool) :
    (2 * r + 1) ^ (d - 1) ≤ (signedCubeFace d r f).card := by
  let V := {j : Fin d // j ≠ f.1}
  let T := Fintype.piFinset (fun _ : V => Finset.Icc (-(r : ℤ)) (r : ℤ))
  have hT : T.card = (2 * r + 1) ^ (d - 1) := by
    dsimp only [T]
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    have h₁ : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
    have h₂ : Fintype.card V = d - 1 := by
      dsimp only [V]
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      simp
    rw [h₁, h₂]
  rw [← hT]
  let extend (x : V → ℤ) (i : Fin d) : ℤ :=
    if hi : i = f.1 then (if f.2 then (r : ℤ) else -(r : ℤ)) else x ⟨i, hi⟩
  refine Finset.card_le_card_of_injOn extend ?_ ?_
  · intro x hx
    have hx' := Fintype.mem_piFinset.mp hx
    refine Finset.mem_filter.mpr ⟨mem_centeredBox.mpr ?_, by simp [extend]⟩
    intro i
    by_cases hi : i = f.1
    · cases hsign : f.2 <;> simp [extend, hi, hsign] <;> omega
    · simpa [extend, hi] using Finset.mem_Icc.mp (hx' ⟨i, hi⟩)
  · intro x _ y _ hxy
    funext j
    simpa [extend, j.property] using congrFun hxy j.val

theorem farLegBox_face_card_lower {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) :
    (2 * legBoxRadius t + 1) ^ (d - 1) ≤
      (translateSites (farLegBoxCenter t f pl) (signedCubeFace d (legBoxRadius t) f)).card := by
  rw [card_translateSites]
  exact signedCubeFace_card_lower d _ f

theorem interiorLegBox_card {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) :
    (translateSites (interiorLegBoxCenter t f pl) (centeredBox d (legBoxRadius t))).card =
      (2 * legBoxRadius t + 1) ^ d := by
  rw [card_translateSites, card_centeredBox_exact]

theorem legBox_side_ge {t : ℕ} (ht : 64 ≤ t) : t ≤ 64 * (2 * legBoxRadius t + 1) := by
  unfold legBoxRadius
  omega

private theorem splitRange_int (t : ℕ) (pl : Bool) (a : ℤ)
    (ha : splitRange t pl a) :
    if pl then (t : ℤ) < 8 * a ∧ 4 * a < (t : ℤ)
    else -(t : ℤ) < 4 * a ∧ 8 * a < -(t : ℤ) := by
  cases pl <;> simp [splitRange] at ha ⊢ <;>
    exact ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩

/-- Distinct legs have macroscopically separated beyond-cube regions. -/
theorem splitBeyond_separated {d t : ℕ} (hd : 2 ≤ d) (ht : 64 ≤ t)
    {f g : Fin d × Bool} {pl ql : Bool} (hleg : (f, pl) ≠ (g, ql))
    {x y : Vertex d} (hx : x ∈ splitBeyond t f pl t) (hy : y ∈ splitBeyond t g ql t) :
    ((t / 8 : ℕ) : ℝ) ≤ dist x y := by
  obtain ⟨_, hxHeight, hxRange⟩ := Finset.mem_filter.mp hx
  obtain ⟨_, hyHeight, hyRange⟩ := Finset.mem_filter.mp hy
  have hcoord (j : Fin d) (hj : ((t / 8 : ℕ) : ℤ) ≤ |x j - y j|) :
      ((t / 8 : ℕ) : ℝ) ≤ dist x y := by
    refine le_trans ?_ (dist_le_pi_dist x y j)
    rw [Int.dist_eq]
    simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub] using
      (Int.cast_le.mpr hj : (((t / 8 : ℕ) : ℤ) : ℝ) ≤ ((|x j - y j| : ℤ) : ℝ))
  obtain ⟨i, s⟩ := f
  obtain ⟨j, u⟩ := g
  by_cases hij : i = j
  · subst j
    by_cases hsu : s = u
    · subst u
      haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
      obtain ⟨k, hk⟩ := exists_ne i
      have hp : pl ≠ ql := fun h => hleg (by rw [h])
      have hxk := splitRange_int t pl (x k) (hxRange k hk)
      have hyk := splitRange_int t ql (y k) (hyRange k hk)
      apply hcoord k
      have h₁ := le_abs_self (x k - y k)
      have h₂ := neg_le_abs (x k - y k)
      cases pl <;> cases ql <;> simp at hp hxk hyk <;> omega
    · apply hcoord i
      have h₁ := le_abs_self (x i - y i)
      have h₂ := neg_le_abs (x i - y i)
      cases s <;> cases u <;> simp [faceHeight] at hsu hxHeight hyHeight <;> omega
  · have hyi := splitRange_int t ql (y i) (hyRange i hij)
    apply hcoord i
    have h₁ := le_abs_self (x i - y i)
    have h₂ := neg_le_abs (x i - y i)
    cases s <;> cases ql <;> simp [faceHeight] at hxHeight hyi <;> omega

end NearCritical.SplitCrossDirect
