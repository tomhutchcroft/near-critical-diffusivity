module

public import NearCritical.BulkDomain
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Exact water-cube bulk geometry on the ACTUAL issued support and graph.
No induced graph on U+ is substituted for the issued network. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset
open scoped Classical

private lemma rectangularBox_nearest_face_witnesses {d : ℕ} (ρ : Fin d → ℕ)
    (i : Fin d) (x : Vertex d) (hx : x ∈ rectangularBox ρ) :
    (∃ y : DomainVertex (rectangularBox ρ), y ∈ negativeFace _ i ∧
      dist x y.val ≤ (x i : ℝ)+(ρ i : ℝ)) ∧
    (∃ y : DomainVertex (rectangularBox ρ), y ∈ positiveFace _ i ∧
      dist x y.val ≤ (ρ i : ℝ)+1-(x i : ℝ)) := by
  have hxρ := mem_rectangularBox.mp hx
  let l := Function.update x i (-(ρ i : ℤ))
  let b := Function.update x i (ρ i : ℤ)
  have hl : l ∈ rectangularBox ρ := by
    apply mem_rectangularBox.mpr
    intro j
    by_cases hj : j=i
    · subst j; simp [l]
    · simpa [l,Function.update_of_ne hj] using hxρ j
  have hb : b ∈ rectangularBox ρ := by
    apply mem_rectangularBox.mpr
    intro j
    by_cases hj : j=i
    · subst j; simp [b]
    · simpa [b,Function.update_of_ne hj] using hxρ j
  have hlo : ∀ y ∈ sitesPlus (rectangularBox ρ), l i ≤ y i := by
    intro y hy
    have hyb := sitesPlus_coordinate_bounds (rectangularBox ρ) i
      (fun z hz => (mem_rectangularBox.mp hz) i) y hy
    simpa [l] using hyb.1
  have hhi : ∀ y ∈ sitesPlus (rectangularBox ρ), y i ≤ bondTip (b,i) i := by
    intro y hy
    have hyb := sitesPlus_coordinate_bounds (rectangularBox ρ) i
      (fun z hz => (mem_rectangularBox.mp hz) i) y hy
    simpa [b,bondTip] using hyb.2
  have hln : 0 ≤ (x i : ℝ)+(ρ i : ℝ) := by exact_mod_cast (show 0 ≤ x i+(ρ i : ℤ) by have := hxρ i; omega)
  have hhn : 0 ≤ (ρ i : ℝ)+1-(x i : ℝ) := by exact_mod_cast (show 0 ≤ (ρ i : ℤ)+1-x i by have := hxρ i; omega)
  constructor
  · refine ⟨⟨l,base_mem_sitesPlus hl⟩, ⟨mem_boundarySites_of_min i (base_mem_sitesPlus hl) hlo,hlo⟩, ?_⟩
    apply (dist_pi_le_iff hln).mpr
    intro j
    by_cases hj : j=i
    · subst j
      simp only [l,Function.update_self,Int.dist_eq,Int.cast_neg,Int.cast_natCast,sub_neg_eq_add]
      rw [abs_of_nonneg hln]
    · simp [l,Function.update_of_ne hj, hln]
  · refine ⟨⟨bondTip (b,i),tip_mem_sitesPlus hb i⟩,
      ⟨mem_boundarySites_of_max i (tip_mem_sitesPlus hb i) hhi,hhi⟩, ?_⟩
    apply (dist_pi_le_iff hhn).mpr
    intro j
    by_cases hj : j=i
    · subst j
      simp only [bondTip,Function.update_self,b,Int.dist_eq,Int.cast_add,Int.cast_natCast,Int.cast_one]
      rw [abs_of_nonpos (by linarith : (x i : ℝ)-((ρ i : ℝ)+1) ≤ 0)]
      linarith
    · simp [bondTip,b,Function.update_of_ne hj,hhn]

/-- Literal sup-distance to the source's U+ faces, for a base-box vertex.
The asymmetry H=2r+1 is retained. -/
theorem waterCube_twoFaceDistance_eq_min {d : ℕ} (i : Fin d) (r R : ℕ)
    (x : Vertex d) (hx : x ∈ waterCube d i r R) :
    twoFaceDistance (waterCube d i r R) i x =
      min ((x i : ℝ)+(r : ℝ)) ((r : ℝ)+1-(x i : ℝ)) := by
  let U := waterCube d i r R
  let A : Set (Vertex d) := Subtype.val '' twoFaceBoundary U i
  have hA : A.Nonempty := by
    obtain ⟨y,hy⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
    exact ⟨y.val,y,by rw [twoFaceBoundary_eq_union]; exact Or.inl hy,rfl⟩
  have hlower : min ((x i : ℝ)+(r : ℝ)) ((r : ℝ)+1-(x i : ℝ)) ≤ Metric.infDist x A := by
    apply (Metric.le_infDist hA).mpr
    rintro y ⟨z,hz,rfl⟩
    have hd := dist_le_pi_dist x z.val i
    rw [Int.dist_eq] at hd
    rw [twoFaceBoundary_eq_union] at hz
    rcases hz with hz | hz
    · have hzcoord := rectangularBox_negativeFace_coordinate
        (fun j => if j=i then r else R) i hz
      simp only [ite_true] at hzcoord
      rw [hzcoord,Int.cast_neg,Int.cast_natCast,sub_neg_eq_add] at hd
      have hnon : 0 ≤ (x i : ℝ)+(r : ℝ) := by
        have hh := (mem_rectangularBox.mp hx) i
        simp only [ite_true] at hh
        exact_mod_cast (show 0 ≤ x i+(r : ℤ) by omega)
      rw [abs_of_nonneg hnon] at hd
      exact (min_le_left _ _).trans hd
    · have hzcoord := rectangularBox_positiveFace_coordinate
        (fun j => if j=i then r else R) i hz
      simp only [ite_true] at hzcoord
      rw [hzcoord,Int.cast_add,Int.cast_natCast,Int.cast_one] at hd
      have hnon : (x i : ℝ)-((r : ℝ)+1) ≤ 0 := by
        have hh := (mem_rectangularBox.mp hx) i
        simp only [ite_true] at hh
        have hhR : (x i : ℝ) ≤ (r : ℝ) := by exact_mod_cast hh.2
        linarith
      rw [abs_of_nonpos hnon] at hd
      exact (min_le_right _ _).trans (by linarith)
  obtain ⟨⟨l,hl,hld⟩,⟨u,hu,hud⟩⟩ := rectangularBox_nearest_face_witnesses
    (fun j => if j=i then r else R) i x hx
  simp only [ite_true] at hld hud
  have hlA : l.val ∈ A := ⟨l,by rw [twoFaceBoundary_eq_union]; exact Or.inl hl,rfl⟩
  have huA : u.val ∈ A := ⟨u,by rw [twoFaceBoundary_eq_union]; exact Or.inr hu,rfl⟩
  exact le_antisymm (le_min
    ((Metric.infDist_le_dist_of_mem hlA).trans hld)
    ((Metric.infDist_le_dist_of_mem huA).trans hud)) hlower

/-- Exact strict integer bulk band. No nonintegrality assumption on δH/2,
no δ perturbation and no edge-endpoint convention is hidden. -/
theorem mem_bulkVertices_waterCube_iff_band {d : ℕ} (i : Fin d) (r R : ℕ)
    (δ : ℝ) (x : Vertex d) :
    x ∈ bulkVertices (waterCube d i r R) i (2*(r : ℝ)+1) δ ↔
      x ∈ waterCube d i r R ∧
      let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
      m < x i+(r : ℤ) ∧ x i+(r : ℤ) ≤ (2*r+1 : ℤ)-m-1 := by
  rw [mem_bulkVertices]
  by_cases hx : x ∈ waterCube d i r R
  · simp only [hx,true_and]
    rw [waterCube_twoFaceDistance_eq_min i r R x hx,lt_min_iff]
    have ht : ((x i+(r : ℤ) : ℤ) : ℝ) = (x i : ℝ)+(r : ℝ) := by push_cast; ring
    have hu : ((2*r+1-(x i+(r : ℤ)) : ℤ) : ℝ) = (r : ℝ)+1-(x i : ℝ) := by push_cast; ring
    rw [← ht,← hu,← Int.floor_lt,← Int.floor_lt]
    omega
  · simp [hx]

/-- Any issued tip outside a rectangle has a UNIQUE issued bond into it.
This is the actual issued-edge geometry, not adjacency in induced U+. -/
theorem rectangularBox_issued_tip_outside_unique {d : ℕ} (ρ : Fin d → ℕ)
    (e f : IssuedBond (rectangularBox ρ))
    (he : bondTip e.val ∉ rectangularBox ρ) (h : bondTip e.val = bondTip f.val) : e=f := by
  have heU := mem_rectangularBox.mp (Finset.mem_product.mp e.property).1
  have hfU := mem_rectangularBox.mp (Finset.mem_product.mp f.property).1
  have heaxis : e.val.1 e.val.2 = (ρ e.val.2 : ℤ) := by
    by_contra hh
    apply he
    apply mem_rectangularBox.mpr
    intro j
    by_cases hj : j=e.val.2
    · subst j
      simp only [bondTip,Function.update_self]
      have := heU e.val.2
      omega
    · simpa [bondTip,Function.update_of_ne hj] using heU j
  have haxis : e.val.2=f.val.2 := by
    by_contra hh
    have hhcoord := congrFun h e.val.2
    simp only [bondTip,Function.update_self,Function.update_of_ne hh] at hhcoord
    have := hfU e.val.2
    omega
  apply Subtype.ext
  apply Prod.ext
  · funext j
    by_cases hj : j=e.val.2
    · subst j
      have hhcoord := congrFun h e.val.2
      simpa [bondTip,haxis] using hhcoord
    · have hhcoord := congrFun h j
      simpa [bondTip,Function.update_of_ne hj,← haxis] using hhcoord
  · exact haxis

/-- In the actual issued network, an exterior rectangle vertex has at most
one neighbor, for arbitrary weights and vertex restriction. -/
theorem rectangularBox_issued_neighbors_unique {d : ℕ} (ρ : Fin d → ℕ)
    (a : IssuedBond (rectangularBox ρ) → ℝ)
    (S : Set (DomainVertex (rectangularBox ρ)))
    (x y z : DomainVertex (rectangularBox ρ)) (hx : x.val ∉ rectangularBox ρ)
    (hxy : ((issuedNetwork (rectangularBox ρ)).positiveGraph a S).Adj x y)
    (hxz : ((issuedNetwork (rectangularBox ρ)).positiveGraph a S).Adj x z) : y=z := by
  have hrepr (v : DomainVertex (rectangularBox ρ))
      (hv : ((issuedNetwork (rectangularBox ρ)).positiveGraph a S).Adj x v) :
      ∃ e : IssuedBond (rectangularBox ρ),
        (issuedNetwork (rectangularBox ρ)).head e=x ∧
        (issuedNetwork (rectangularBox ρ)).tail e=v := by
    obtain ⟨_,_,_,e,_,he⟩ := hv
    rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · have hb : ((issuedNetwork (rectangularBox ρ)).tail e).val ∈ rectangularBox ρ :=
        (Finset.mem_product.mp e.property).1
      exact (hx ((congrArg Subtype.val ht) ▸ hb)).elim
    · exact ⟨e,hh,ht⟩
  obtain ⟨e,hex,hey⟩ := hrepr y hxy
  obtain ⟨f,hfx,hfz⟩ := hrepr z hxz
  have hef : e=f := rectangularBox_issued_tip_outside_unique ρ e f
    (by
      have htip : bondTip e.val = x.val := by simpa [issuedNetwork,issuedBond] using congrArg Subtype.val hex
      rw [htip]
      exact hx)
    (congrArg Subtype.val (hex.trans hfx.symm))
  subst f
  exact hey.symm.trans hfz

private lemma path_support_of_outside_neighbors_unique {V : Type*} {G : SimpleGraph V}
    (S : Set V) (hleaf : ∀ x ∉ S, ∀ y z, G.Adj x y → G.Adj x z → y=z)
    {x y : V} (w : G.Walk x y) :
    w.IsPath → x ∈ S → y ∈ S → ∀ z ∈ w.support, z ∈ S := by
  induction w with
  | @nil u =>
      intro _ hx _ z hz
      have hzx : z=u := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
      simpa only [hzx] using hx
  | @cons x v y hxv w ih =>
      intro hw hx hy
      have hw' := (SimpleGraph.Walk.cons_isPath_iff hxv w).mp hw
      have hv : v ∈ S := by
        by_contra hv
        cases w with
        | nil => exact hv hy
        | @cons v u y hvu q =>
            have hux : u=x := (hleaf v hv x u hxv.symm hvu).symm
            apply hw'.2
            simp only [SimpleGraph.Walk.support_cons,List.mem_cons]
            exact Or.inr (hux ▸ q.start_mem_support)
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact ih hw'.1 hv hy z hz

/-- A simple ACTUAL issued path from a base vertex visits no exterior
protrusion internally. The endpoint may itself be the upper-face leaf.
Zero-length paths are included, without an assumed positive height. -/
theorem rectangularBox_issued_simplePath_support {d : ℕ} (ρ : Fin d → ℕ)
    (a : IssuedBond (rectangularBox ρ) → ℝ)
    (S : Set (DomainVertex (rectangularBox ρ)))
    {x y : DomainVertex (rectangularBox ρ)}
    (w : ((issuedNetwork (rectangularBox ρ)).positiveGraph a S).Walk x y)
    (hw : w.IsPath) (hx : x.val ∈ rectangularBox ρ) :
    ∀ z ∈ w.support, z.val ∈ rectangularBox ρ ∨ z=y := by
  let T : Set (DomainVertex (rectangularBox ρ)) :=
    {z | z.val ∈ rectangularBox ρ ∨ z=y}
  apply path_support_of_outside_neighbors_unique T _ w hw (Or.inl hx) (Or.inr rfl)
  intro z hz u v hzu hzv
  exact rectangularBox_issued_neighbors_unique ρ a S z u v
    (fun h => hz (Or.inl h)) hzu hzv

/-- Positive-face specialization. Every vertex of a simple issued path
strictly below its terminal face belongs to U itself, not merely U+.
This is the local-law prerequisite for a middle cut n<H. -/
theorem waterCube_issued_simplePath_below_positiveFace {d : ℕ} (i : Fin d) (r R : ℕ)
    (a : IssuedBond (waterCube d i r R) → ℝ)
    (S : Set (DomainVertex (waterCube d i r R)))
    {x y : DomainVertex (waterCube d i r R)}
    (w : ((issuedNetwork (waterCube d i r R)).positiveGraph a S).Walk x y)
    (hw : w.IsPath) (hx : x.val ∈ waterCube d i r R)
    (hy : y ∈ positiveFace (waterCube d i r R) i) :
    ∀ z ∈ w.support, z.val i < (r : ℤ)+1 → z.val ∈ waterCube d i r R := by
  intro z hz hzi
  obtain hU | rfl := rectangularBox_issued_simplePath_support
    (fun j => if j=i then r else R) a S w hw hx z hz
  · exact hU
  · have hyi := rectangularBox_positiveFace_coordinate
      (fun j => if j=i then r else R) i hy
    simp only [ite_true] at hyi
    omega

end NearCritical
