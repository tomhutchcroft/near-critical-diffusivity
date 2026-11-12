module

public import NearCritical.WaterCubeBulkBandGeometry
public import NearCritical.WalkFirstHeight
public import NearCritical.SlabPioneerConvolution
public import NearCritical.HalfSpaceLastVisit

/-! Actual issued first-hit certificates for the masked water cube.
All domains are PHYSICAL coordinates; normalized height is z_i+r. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset
open scoped Classical

private theorem waterCube_positiveFace_simple_open_path {d : ℕ}
    (i : Fin d) (r R : ℕ) (ω : Configuration d)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (hω : ω ∈ latticeBoundaryConnectionEvent (waterCube d i r R) x
      (positiveFace (waterCube d i r R) i)) :
    ∃ (y : DomainVertex (waterCube d i r R)), y ∈ positiveFace _ i ∧
      ∃ w : (openGraph ω).Walk x.val y.val, w.IsPath ∧
        (∀ z ∈ w.support, z ∈ waterCube d i r R ∨ z=y.val) ∧
        (∀ z ∈ w.support, -(r : ℤ) ≤ z i ∧ z i ≤ (r : ℤ)+1) := by
  obtain ⟨y,hy,⟨q⟩⟩ := hω
  let p := q.toPath.val
  let f := issuedGraphToRestricted (waterCube d i r R) ω
  have hle : restrictedGraph ω (sitesPlus (waterCube d i r R) : Set (Vertex d)) ≤ openGraph ω :=
    fun _ _ h => h.1
  let w := (p.map f).mapLe hle
  have hp : p.IsPath := q.toPath.property
  have hw : w.IsPath := (hp.map (show Function.Injective f from Subtype.val_injective)).mapLe hle
  have hconf := rectangularBox_issued_simplePath_support
    (fun j => if j=i then r else R)
    (Network.binaryWeights ((issuedBondSet (waterCube d i r R)).restrict ω)) Set.univ p hp hx
  refine ⟨y,hy,w,hw,?_,?_⟩
  · intro z hz
    have hz' : z ∈ p.support.map Subtype.val := by
      change z ∈ ((p.map f).mapLe hle).support at hz
      rw [SimpleGraph.Walk.support_mapLe_eq_support, SimpleGraph.Walk.support_map] at hz
      exact hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz'
    rcases hconf v hv with hU | rfl
    · exact Or.inl hU
    · exact Or.inr rfl
  · intro z hz
    have hz' : z ∈ p.support.map Subtype.val := by
      change z ∈ ((p.map f).mapLe hle).support at hz
      rw [SimpleGraph.Walk.support_mapLe_eq_support, SimpleGraph.Walk.support_map] at hz
      exact hz
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz'
    have hv := sitesPlus_coordinate_bounds (waterCube d i r R) i
      (fun z hz => by
        have hh := (mem_rectangularBox.mp hz) i
        simpa only [ite_true] using hh) v.val v.property
    exact hv

private lemma three_openWalk_certificates {d : ℕ} {ω : Configuration d}
    {x u v y : Vertex d} (p : (openGraph ω).Walk x u)
    (q : (openGraph ω).Walk u v) (r : (openGraph ω).Walk v y)
    (htrail : (p.append (q.append r)).IsTrail)
    (S T V A : Set (Vertex d))
    (hp : ∀ z ∈ p.support, z ∈ S) (hq : ∀ z ∈ q.support, z ∈ T)
    (hr : ∀ z ∈ r.support, z ∈ V) (hy : y ∈ A) :
    ∃ F G H : Finset (Bond d), Disjoint F G ∧ Disjoint F H ∧ Disjoint G H ∧
      (∀ e ∈ F, ω e=true) ∧ (∀ e ∈ G, ω e=true) ∧ (∀ e ∈ H, ω e=true) ∧
      (∀ θ : Configuration d, (∀ e ∈ F, θ e=true) → θ ∈ connectionToSetEvent S x {u}) ∧
      (∀ θ : Configuration d, (∀ e ∈ G, θ e=true) → θ ∈ connectionToSetEvent T u {v}) ∧
      (∀ θ : Configuration d, (∀ e ∈ H, θ e=true) → θ ∈ connectionToSetEvent V v A) := by
  obtain ⟨F,hFo,hFe,hF⟩ := openWalk_certificate p S hp
  obtain ⟨G,hGo,hGe,hG⟩ := openWalk_certificate q T hq
  obtain ⟨H,hHo,hHe,hH⟩ := openWalk_certificate r V hr
  have hsplit := (SimpleGraph.Walk.isTrail_append p (q.append r)).mp htrail
  have hsplit' := (SimpleGraph.Walk.isTrail_append q r).mp hsplit.2.1
  have hFG : Disjoint F G := by
    apply Finset.disjoint_left.mpr
    intro e heF heG
    apply List.disjoint_left.mp hsplit.2.2 (hFe e heF)
    rw [SimpleGraph.Walk.edges_append]
    exact List.mem_append.mpr (Or.inl (hGe e heG))
  have hFH : Disjoint F H := by
    apply Finset.disjoint_left.mpr
    intro e heF heH
    apply List.disjoint_left.mp hsplit.2.2 (hFe e heF)
    rw [SimpleGraph.Walk.edges_append]
    exact List.mem_append.mpr (Or.inr (hHe e heH))
  have hGH : Disjoint G H := Finset.disjoint_left.mpr
    (fun e heG heH => List.disjoint_left.mp hsplit'.2.2 (hGe e heG) (hHe e heH))
  refine ⟨F,G,H,hFG,hFH,hGH,hFo,hGo,hHo,hF,hG,?_⟩
  intro θ hθ
  exact connectionToSetEvent_mono subset_rfl (Set.singleton_subset_iff.mpr hy) v (hH θ hθ)

/-- Three OLD-open disjoint certificates from the actual issued path.
The physical prefixes lie in U∩[-r,m-r] and U∩[-r,n-r].
Cuts may coincide; a first piece may be nil. -/
theorem maskedWaterCube_two_first_heights_open_forcing {d : ℕ}
    (i : Fin d) (r R : ℕ) (ω : Configuration d)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (m n : ℤ) (hm : 0 ≤ m) (hxm : x.val i+(r : ℤ) ≤ m)
    (hmn : m ≤ n) (hnH : n < 2*(r : ℤ)+1)
    (hω : ω ∈ latticeBoundaryConnectionEvent (waterCube d i r R) x
      (positiveFace (waterCube d i r R) i)) :
    ∃ u v : Vertex d, u ∈ waterCube d i r R ∧ v ∈ waterCube d i r R ∧
      u i+(r : ℤ)=m ∧ v i+(r : ℤ)=n ∧
      ∃ F G H : Finset (Bond d), Disjoint F G ∧ Disjoint F H ∧ Disjoint G H ∧
      (∀ e ∈ F, ω e=true) ∧ (∀ e ∈ G, ω e=true) ∧ (∀ e ∈ H, ω e=true) ∧
      (∀ θ : Configuration d, (∀ e ∈ F, θ e=true) → θ ∈ connectionToSetEvent
        ((waterCube d i r R : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (m-r)) x.val {u}) ∧
      (∀ θ : Configuration d, (∀ e ∈ G, θ e=true) → θ ∈ connectionToSetEvent
        ((waterCube d i r R : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) u {v}) ∧
      (∀ θ : Configuration d, (∀ e ∈ H, θ e=true) → θ ∈ connectionToSetEvent
        (finiteHeightSlab i (-(r : ℤ)) ((r : ℤ)+1)) v
        (Subtype.val '' positiveFace (waterCube d i r R) i)) := by
  obtain ⟨y,hy,w,hw,hconf,hbounds⟩ := waterCube_positiveFace_simple_open_path i r R ω x hx hω
  have hyi := rectangularBox_positiveFace_coordinate (fun j => if j=i then r else R) i hy
  simp only [ite_true] at hyi
  have hstep : ∀ {a b : Vertex d}, (openGraph ω).Adj a b → b i+(r : ℤ) ≤ a i+(r : ℤ)+1 := by
    intro a b hab
    have := (openGraph_adj_height_bounds hab i).2
    omega
  obtain ⟨u,v,p,q,s,hdecomp,hu,hv,hp,hq⟩ := walk_two_height_prefixes
    (fun z : Vertex d => z i+(r : ℤ)) hstep w m n hxm hmn (by omega)
  have hpall : p.support ⊆ w.support := by
    rw [← hdecomp]
    exact SimpleGraph.Walk.support_subset_support_append_left _ _
  have hqall : q.support ⊆ w.support := by
    rw [← hdecomp]
    intro z hz
    exact SimpleGraph.Walk.support_subset_support_append_right p (q.append s)
      (SimpleGraph.Walk.support_subset_support_append_left q s hz)
  have hsall : s.support ⊆ w.support := by
    rw [← hdecomp]
    intro z hz
    exact SimpleGraph.Walk.support_subset_support_append_right p (q.append s)
      (SimpleGraph.Walk.support_subset_support_append_right q s hz)
  have hbase (z : Vertex d) (hz : z ∈ w.support) (hzn : z i+(r : ℤ) ≤ n) :
      z ∈ waterCube d i r R := by
    rcases hconf z hz with hU | rfl
    · exact hU
    · omega
  have hpS : ∀ z ∈ p.support, z ∈ (waterCube d i r R : Set (Vertex d)) ∩
      finiteHeightSlab i (-(r : ℤ)) (m-r) := by
    intro z hz
    refine ⟨hbase z (hpall hz) ((hp z hz).trans hmn),?_⟩
    have hl := (hbounds z (hpall hz)).1
    have hupper := hp z hz
    change -(r : ℤ) ≤ z i ∧ z i ≤ m-(r : ℤ)
    constructor <;> omega
  have hqS : ∀ z ∈ q.support, z ∈ (waterCube d i r R : Set (Vertex d)) ∩
      finiteHeightSlab i (-(r : ℤ)) (n-r) := by
    intro z hz
    refine ⟨hbase z (hqall hz) (hq z hz),?_⟩
    have hl := (hbounds z (hqall hz)).1
    have hupper := hq z hz
    change -(r : ℤ) ≤ z i ∧ z i ≤ n-(r : ℤ)
    constructor <;> omega
  have hsS : ∀ z ∈ s.support, z ∈ finiteHeightSlab i (-(r : ℤ)) ((r : ℤ)+1) := by
    intro z hz
    exact hbounds z (hsall hz)
  refine ⟨u,v,(hpS u p.end_mem_support).1,(hqS v q.end_mem_support).1,hu,hv,?_⟩
  apply three_openWalk_certificates p q s
    (by rw [hdecomp]; exact hw.isTrail) _ _ _ _ hpS hqS hsS
  exact ⟨y,hy,rfl⟩

/-- Two OLD-open disjoint certificates at a single first-height cut.
A zero-length prefix at x_i+r=n is allowed; no strict crossing premise. -/
theorem maskedWaterCube_first_height_open_forcing {d : ℕ}
    (i : Fin d) (r R : ℕ) (ω : Configuration d)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (n : ℤ) (hn : 0 ≤ n) (hxn : x.val i+(r : ℤ) ≤ n)
    (hnH : n < 2*(r : ℤ)+1)
    (hω : ω ∈ latticeBoundaryConnectionEvent (waterCube d i r R) x
      (positiveFace (waterCube d i r R) i)) :
    ∃ v : Vertex d, v ∈ waterCube d i r R ∧ v i+(r : ℤ)=n ∧
      ∃ F H : Finset (Bond d), Disjoint F H ∧
      (∀ e ∈ F, ω e=true) ∧ (∀ e ∈ H, ω e=true) ∧
      (∀ θ : Configuration d, (∀ e ∈ F, θ e=true) → θ ∈ connectionToSetEvent
        ((waterCube d i r R : Set (Vertex d)) ∩ finiteHeightSlab i (-(r : ℤ)) (n-r)) x.val {v}) ∧
      (∀ θ : Configuration d, (∀ e ∈ H, θ e=true) → θ ∈ connectionToSetEvent
        (finiteHeightSlab i (-(r : ℤ)) ((r : ℤ)+1)) v
        (Subtype.val '' positiveFace (waterCube d i r R) i)) := by
  obtain ⟨u,v,_,hv,_,hvn,F,G,H,_,hFH,hGH,hFo,hGo,hHo,hF,hG,hH⟩ :=
    maskedWaterCube_two_first_heights_open_forcing i r R ω x hx n n hn hxn le_rfl hnH hω
  have hdis : Disjoint (F∪G) H := Finset.disjoint_left.mpr (by
    intro e he heH
    rcases Finset.mem_union.mp he with heF | heG
    · exact Finset.disjoint_left.mp hFH heF heH
    · exact Finset.disjoint_left.mp hGH heG heH)
  refine ⟨v,hv,hvn,F∪G,H,hdis,?_,hHo,?_,hH⟩
  · intro e he
    rcases Finset.mem_union.mp he with heF | heG
    · exact hFo e heF
    · exact hGo e heG
  · intro θ hθ
    obtain ⟨hxD,t,ht,htD,hxt⟩ := hF θ (fun e he => hθ e (Finset.mem_union_left G he))
    have htu : t=u := ht
    subst t
    obtain ⟨_,z,hz,hzD,huz⟩ := hG θ (fun e he => hθ e (Finset.mem_union_right F he))
    have hzv : z=v := hz
    subst z
    exact ⟨hxD,v,rfl,hzD,hxt.trans huz⟩

end NearCritical
