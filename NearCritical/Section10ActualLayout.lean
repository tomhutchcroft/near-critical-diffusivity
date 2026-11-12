module

public import NearCritical.Section10LatticeRule
public import NearCritical.Section10BoxFaces

/-! The actual layout of the Section 10 construction in dimension `D + 1`.

Coarse site `(j, y)` (level `j`, transverse position `y`) sits at the lattice
point `vecSite (j, y) = (j, y_1, ..., y_D)`, with cube centre `2t * vecSite`.
The vertical direction is coordinate `0`. A step label has a tube when its
target is a lattice neighbour of its site in a positive direction and the
target level is below `M`; its two half tubes are the translated Section 9
tubes. Exit bonds are reserved at the top level `M - 1` only.

`actualLayout` is the `NestLayout`; all its structural fields (disjoint cubes,
disjoint regions, containments) are proved here, for `t >= 9`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Lattice point of a coarse site. -/
def vecSite {D : ℕ} (s : RSite D) : Vertex (D + 1) := Fin.cons (s.1 : ℤ) s.2

lemma vecSite_zero {D : ℕ} (s : RSite D) : vecSite s 0 = (s.1 : ℤ) := rfl

lemma vecSite_succ {D : ℕ} (s : RSite D) (j : Fin D) : vecSite s j.succ = s.2 j := rfl

lemma vecSite_injective {D : ℕ} : Function.Injective (vecSite (D := D)) := by
  intro s s' h
  have h0 := congrFun h 0
  rw [vecSite_zero, vecSite_zero] at h0
  have h1 : s.2 = s'.2 := funext fun j => by
    have := congrFun h j.succ
    rwa [vecSite_succ, vecSite_succ] at this
  exact Prod.ext (by exact_mod_cast h0) h1

/-- Cube centre of a coarse site. -/
def siteCenter {D : ℕ} (t : ℕ) (s : RSite D) : Vertex (D + 1) := coarseCenter t (vecSite s)

/-- The coarse box. -/
def siteBoxOf (D M : ℕ) : Finset (RSite D) :=
  (Finset.range M) ×ˢ (Fintype.piFinset fun _ : Fin D => Finset.Ico (0:ℤ) (M:ℤ))

lemma mem_siteBoxOf {D M : ℕ} {s : RSite D} :
    s ∈ siteBoxOf D M ↔ s.1 < M ∧ ∀ j, 0 ≤ s.2 j ∧ s.2 j < (M:ℤ) := by
  unfold siteBoxOf
  simp [Finset.mem_product, Fintype.mem_piFinset]

/-- The label has a tube: its target is a positive lattice neighbour of its site,
at a level below `M`. -/
def HasTube {D : ℕ} (M : ℕ) (ℓ : RouteLabel D) : Prop :=
  (∃ i : Fin (D + 1), vecSite ℓ.target = vecSite ℓ.site + Pi.single i 1) ∧ ℓ.target.1 < M

/-- Direction of the tube of a label. -/
def dirOf {D : ℕ} (ℓ : RouteLabel D) : Fin (D + 1) :=
  if h : ∃ i : Fin (D + 1), vecSite ℓ.target = vecSite ℓ.site + Pi.single i 1
  then Classical.choose h else 0

lemma dirOf_spec {D M : ℕ} {ℓ : RouteLabel D} (h : HasTube M ℓ) :
    vecSite ℓ.target = vecSite ℓ.site + Pi.single (dirOf ℓ) 1 := by
  unfold dirOf
  rw [dif_pos h.1]
  exact Classical.choose_spec h.1

/-- Left half tube of a label. -/
def LOf {D : ℕ} (t M : ℕ) (ℓ : RouteLabel D) : Finset (Vertex (D + 1)) :=
  if HasTube M ℓ then stepL t (siteCenter t ℓ.site) (dirOf ℓ) else ∅

/-- Right half tube of a label. -/
def ROf {D : ℕ} (t M : ℕ) (ℓ : RouteLabel D) : Finset (Vertex (D + 1)) :=
  if HasTube M ℓ then stepR t (siteCenter t ℓ.site) (dirOf ℓ) else ∅

/-- Middle region of a label. -/
def MidOf {D : ℕ} (t M : ℕ) (ℓ : RouteLabel D) : Finset (Vertex (D + 1)) :=
  if HasTube M ℓ then stepMid t (siteCenter t ℓ.site) (dirOf ℓ) else ∅

/-- Exit bonds of a label. -/
def exitBondsOf {D : ℕ} (t M : ℕ) (ℓ : RouteLabel D) : Finset (Bond (D + 1)) :=
  if ℓ.isExit ∧ ℓ.site.1 = M - 1 then
    (typicalFace t (siteCenter t ℓ.site) ((0 : Fin (D + 1)), true)).image
      (fun y => ((y, (0 : Fin (D + 1))) : Bond (D + 1)))
  else ∅

/-- Bonds reserved for a label. -/
def regionOf {D : ℕ} (t M : ℕ) (ℓ : RouteLabel D) : Finset (Bond (D + 1)) :=
  internalBondSet (LOf t M ℓ ∪ ROf t M ℓ) ∪ exitBondsOf t M ℓ

lemma internalBondSet_mono' {d : ℕ} {U V : Finset (Vertex d)} (h : U ⊆ V) :
    internalBondSet U ⊆ internalBondSet V := by
  intro e he
  rw [mem_internalBondSet] at he ⊢
  exact ⟨h he.1, h he.2⟩

lemma label_eq_of_site_target {D : ℕ} {a b : RouteLabel D} (ha : a.target ≠ a.site)
    (hb : b.target ≠ b.site) (hs : a.site = b.site) (ht : a.target = b.target) : a = b := by
  cases a <;> cases b <;>
    simp_all [RouteLabel.site, RouteLabel.target, Prod.ext_iff]

lemma hasTube_target_ne {D M : ℕ} {ℓ : RouteLabel D} (h : HasTube M ℓ) :
    ℓ.target ≠ ℓ.site := by
  intro heq
  obtain ⟨i, hi⟩ := h.1
  rw [heq] at hi
  have := congrFun hi i
  simp at this

lemma tube_key_ne {D M : ℕ} {a b : RouteLabel D} (ha : HasTube M a) (hb : HasTube M b)
    (hab : a ≠ b) : (vecSite a.site, dirOf a) ≠ (vecSite b.site, dirOf b) := by
  intro h
  have hs : a.site = b.site := vecSite_injective (Prod.mk.inj h).1
  have hd : dirOf a = dirOf b := (Prod.mk.inj h).2
  have ht : a.target = b.target := by
    apply vecSite_injective
    rw [dirOf_spec ha, dirOf_spec hb, hs, hd]
  exact hab (label_eq_of_site_target (hasTube_target_ne ha) (hasTube_target_ne hb) hs ht)

lemma mem_LROf {D t M : ℕ} {ℓ : RouteLabel D} {x : Vertex (D + 1)}
    (hx : x ∈ LOf t M ℓ ∪ ROf t M ℓ) :
    HasTube M ℓ ∧ x ∈ stepL t (siteCenter t ℓ.site) (dirOf ℓ) ∪
      stepR t (siteCenter t ℓ.site) (dirOf ℓ) := by
  unfold LOf ROf at hx
  by_cases h : HasTube M ℓ
  · rw [if_pos h, if_pos h] at hx
    exact ⟨h, hx⟩
  · rw [if_neg h, if_neg h] at hx
    simp at hx

theorem tubeBonds_disjoint {D t M : ℕ} (ht : 0 < t) {a b : RouteLabel D} (hab : a ≠ b) :
    Disjoint (LOf t M a ∪ ROf t M a) (LOf t M b ∪ ROf t M b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨ha, hxa'⟩ := mem_LROf hxa
  obtain ⟨hb, hxb'⟩ := mem_LROf hxb
  have hd := stepTubes_disjoint ht (vecSite a.site) (vecSite b.site) (dirOf a) (dirOf b)
    (tube_key_ne ha hb hab)
  exact Finset.disjoint_left.mp hd hxa' hxb'

lemma siteCenter_zero {D : ℕ} (t : ℕ) (s : RSite D) :
    siteCenter t s 0 = 2 * (t : ℤ) * (s.1 : ℤ) := rfl

theorem regionOf_disjoint {D t M : ℕ} (ht : 9 ≤ t) {a b : RouteLabel D} (hab : a ≠ b) :
    Disjoint (regionOf (D := D) t M a) (regionOf t M b) := by
  have ht0 : 0 < t := by omega
  -- an exit bond of `e` is not a tube bond of `u`
  have hTE : ∀ u e : RouteLabel D, ∀ bd : Bond (D + 1),
      bd ∈ internalBondSet (LOf t M u ∪ ROf t M u) → bd ∈ exitBondsOf t M e → False := by
    intro u e bd hbu hbe
    unfold exitBondsOf at hbe
    by_cases hex : e.isExit ∧ e.site.1 = M - 1
    · rw [if_pos hex] at hbe
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hbe
      obtain ⟨h1, h2⟩ := (mem_internalBondSet _ _).mp hbu
      obtain ⟨hu, h1'⟩ := mem_LROf h1
      obtain ⟨_, h2'⟩ := mem_LROf h2
      refine exitBond_not_in_tube (M := M) ht (0 : Fin (D + 1)) (dirOf u)
        (siteCenter t u.site) (siteCenter t e.site) (u.site.1 : ℤ) (siteCenter_zero t u.site)
        (by rw [siteCenter_zero, hex.2]) ?_ hy h1' h2'
      intro hdir
      have hspec := dirOf_spec hu
      rw [hdir] at hspec
      have h0 := congrFun hspec 0
      rw [vecSite_zero] at h0
      simp only [Pi.add_apply, vecSite_zero, Pi.single_eq_same] at h0
      have hlt := hu.2
      have : (u.target.1 : ℤ) ≤ ((M - 1 : ℕ) : ℤ) := by
        have : u.target.1 ≤ M - 1 := by omega
        exact_mod_cast this
      linarith
    · rw [if_neg hex] at hbe
      simp at hbe
  unfold regionOf
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro e hea heb
    have h1 := ((mem_internalBondSet _ _).mp hea).1
    have h2 := ((mem_internalBondSet _ _).mp heb).1
    exact Finset.disjoint_left.mp (tubeBonds_disjoint ht0 hab) h1 h2
  · rw [Finset.disjoint_left]
    intro e hea heb
    exact hTE a b e hea heb
  · rw [Finset.disjoint_left]
    intro e hea heb
    exact hTE b a e heb hea
  · rw [Finset.disjoint_left]
    intro e hea heb
    unfold exitBondsOf at hea heb
    by_cases hexa : a.isExit ∧ a.site.1 = M - 1
    · by_cases hexb : b.isExit ∧ b.site.1 = M - 1
      · rw [if_pos hexa] at hea
        rw [if_pos hexb] at heb
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hea
        obtain ⟨y', hy', hyy⟩ := Finset.mem_image.mp heb
        have hy'y : y' = y := (Prod.mk.inj hyy).1
        rw [hy'y] at hy'
        have hsite : a.site ≠ b.site := by
          intro hs
          apply hab
          cases a <;> cases b <;> simp_all [RouteLabel.isExit, RouteLabel.site]
        have hd := typicalCube_disjoint_of_ne (t := t) ht0
          (fun h => hsite (vecSite_injective h))
        have hya : y ∈ typicalCube t (coarseCenter t (vecSite a.site)) := by
          unfold typicalFace at hy
          exact (Finset.mem_filter.mp hy).1
        have hyb : y ∈ typicalCube t (coarseCenter t (vecSite b.site)) := by
          unfold typicalFace at hy'
          exact (Finset.mem_filter.mp hy').1
        exact Finset.disjoint_left.mp hd hya hyb
      · rw [if_neg hexb] at heb
        simp at heb
    · rw [if_neg hexa] at hea
      simp at hea

/-- **The actual layout.** -/
def actualLayout (D : ℕ) (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
    (MOff Mcoal Kdiam M : ℕ) : NestLayout D (D + 1) where
  typ := typ
  t := t
  k := k
  hk := hk
  MOff := MOff
  Mcoal := Mcoal
  Kdiam := Kdiam
  siteBox := siteBoxOf D M
  center := siteCenter t
  hdisj := by
    intro a _ b _ hab
    exact typicalCube_disjoint_of_ne (by omega) (fun h => hab (vecSite_injective h))
  i₀ := 0
  dir := dirOf
  Mid := MidOf t M
  L := LOf t M
  R := ROf t M
  region := regionOf t M
  hregion := fun a b hab => regionOf_disjoint ht hab
  hL := fun ℓ => (internalBondSet_mono' Finset.subset_union_left).trans Finset.subset_union_left
  hR := fun ℓ => (internalBondSet_mono' Finset.subset_union_right).trans Finset.subset_union_left
  hMid := fun ℓ => by
    refine (internalBondSet_mono' ?_).trans Finset.subset_union_left
    unfold MidOf LOf
    by_cases h : HasTube M ℓ
    · rw [if_pos h, if_pos h]
      exact (stepMid_subset_stepL _ _ _).trans Finset.subset_union_left
    · rw [if_neg h]
      exact Finset.empty_subset _
  top := M - 1
  hexit := fun z hz => by
    unfold regionOf exitBondsOf
    have h : (RouteLabel.exit z : RouteLabel D).isExit ∧
        (RouteLabel.exit z : RouteLabel D).site.1 = M - 1 := ⟨trivial, hz⟩
    rw [if_pos h]
    exact Finset.subset_union_right

end NearCritical.Section10
