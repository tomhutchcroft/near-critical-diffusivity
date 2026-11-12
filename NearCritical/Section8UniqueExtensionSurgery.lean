module
public import NearCritical.Section9AvoidanceLastExit
public import NearCritical.Section9RevealFiber

/-! Deterministic finite surgery for the unique extension property. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

private theorem extension_available_adj {d : ℕ} {ω : Configuration d}
    (T Q F : Finset (Vertex d)) (b : Bond d)
    (hb : b ∈ sprinklingAvailableBonds T Q F) (hopen : ω b = true) :
    (sprinklingUnexploredGraph ω T Q F).Adj b.1 (bondTip b) := by
  obtain ⟨hbT,hbNot⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨hbase,htip⟩ := (mem_internalBondSet T b).mp hbT
  refine ⟨⟨b,hopen,Or.inl ⟨rfl,rfl⟩⟩,hbase,htip,?_⟩
  intro he
  exact hbNot ((mem_clusterRevealBonds Q F b).mpr
    ((pair_mem_exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)) b.1 (bondTip b)).mp he))

private theorem extension_available_mono {d : ℕ} (S T Q F : Finset (Vertex d))
    (hST : S ⊆ T) : sprinklingAvailableBonds S Q F ⊆ sprinklingAvailableBonds T Q F := by
  intro b hb
  obtain ⟨hbS,hbNot⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨hbase,htip⟩ := (mem_internalBondSet S b).mp hbS
  exact Finset.mem_sdiff.mpr ⟨(mem_internalBondSet T b).mpr ⟨hST hbase,hST htip⟩,hbNot⟩

private theorem extension_walk_preserves {X : Type*} {G : SimpleGraph X} (K : Set X)
    (hstep : ∀ a c, a ∈ K → G.Adj a c → c ∈ K)
    {a c : X} (w : G.Walk a c) (ha : a ∈ K) : c ∈ K := by
  induction w with
  | nil => exact ha
  | cons h w ih => exact ih (hstep _ _ ha h)

/-- A connected static segment allows unique-extension surgery on its finite
available incident-bond mask. Exactly one old exit is retained; all other
exits are closed. Static connectivity is structural, rather than a random
connection or a probability estimate. -/
theorem section8_unique_extension_surgery {d : ℕ} (ω : Configuration d)
    (T Q F I W : Finset (Vertex d)) (x x' z : Vertex d)
    (hIT : I ⊆ T) (hx : x ∈ I) (hx' : x' ∈ I) (hz : z ∉ I)
    (hIW : ∀ y ∈ I, y ∈ W → y = x)
    (hconnected : ∀ u ∈ I,
      (sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F).Reachable x u)
    (hshift : ω ∈ section9AvoidanceEvent T T Q F {z} W x') :
    ∃ θ : Configuration d,
      (∀ b ∉ sprinklingClusterFiberMask T Q F I, θ b = ω b) ∧
      θ ∈ section9AvoidanceEvent T T Q F {z} (W \ {x}) x ∧
      sprinklingUnexploredCluster θ T Q F x ⊆
        I ∪ sprinklingUnexploredCluster ω T Q F x' := by
  have htarget : Disjoint ({z} : Finset (Vertex d)) I := by
    apply Finset.disjoint_left.mpr
    intro y hy hyI
    have hyz : y = z := Finset.mem_singleton.mp hy
    subst y
    exact hz hyI
  obtain ⟨u,v,b,huT,huI,hvTI,hbAvailable,hbOpen,hbEnds,
      P,N,hP,hN,hPBridge,hPSuffix,hBridgeSuffix,hNClosed,hPrefix,hBridge,hSuffix⟩ :=
    section9_avoidance_last_exit_certificates ω T T I Q F {z} W
      (hIT hx') hx' (Finset.Subset.refl T) htarget hshift
  have hvT : v ∈ T := (Finset.mem_sdiff.mp hvTI).1
  have hvI : v ∉ I := (Finset.mem_sdiff.mp hvTI).2
  let U := sprinklingClusterFiberMask T Q F I
  let θ : Configuration d := fun e =>
    if e ∈ U then
      if e = b ∨ (e.1 ∈ I ∧ bondTip e ∈ I) then true else false
    else ω e
  have hθoff (e : Bond d) (he : e ∉ U) : θ e = ω e := by simp only [θ,if_neg he]
  have hθon (e : Bond d) (he : e ∈ U) :
      θ e = true ↔ e = b ∨ (e.1 ∈ I ∧ bondTip e ∈ I) := by
    simp [θ,he]
  have hbU : b ∈ U := by
    apply Finset.mem_filter.mpr
    refine ⟨hbAvailable,?_⟩
    rcases hbEnds with ⟨huBase,hvTip⟩ | ⟨hvBase,huTip⟩
    · exact Or.inl (huBase ▸ huI)
    · exact Or.inr (huTip ▸ huI)
  have hbθ : θ b = true := (hθon b hbU).mpr (Or.inl rfl)
  have hbPhys : s(b.1,bondTip b) = s(u,v) := by
    rcases hbEnds with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Sym2.eq_swap
  have hbridgeω : (sprinklingUnexploredGraph ω T Q F).Adj u v := by
    have h := extension_available_adj T Q F b hbAvailable hbOpen
    rcases hbEnds with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · exact h.symm
  have hbridgeθ : (sprinklingUnexploredGraph θ T Q F).Adj u v := by
    have h := extension_available_adj T Q F b hbAvailable hbθ
    rcases hbEnds with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact h
    · exact h.symm
  have huOld : u ∈ sprinklingUnexploredCluster ω T Q F x' :=
    hPrefix ω (fun _ _ => rfl)
  have hvOld : v ∈ sprinklingUnexploredCluster ω T Q F x' := by
    apply (mem_sprinklingUnexploredCluster ω T Q F x' v).mpr
    exact ⟨hvT,((mem_sprinklingUnexploredCluster ω T Q F x' u).mp huOld).2.trans hbridgeω.reachable⟩
  have hstatic : sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F ≤
      sprinklingUnexploredGraph θ T Q F := by
    intro a c hac
    obtain ⟨e,heI,_,hends⟩ := sprinklingUnexplored_adj_available_bond I Q F hac
    have heT := extension_available_mono I T Q F hIT heI
    have heInternal := (mem_internalBondSet I e).mp (Finset.mem_sdiff.mp heI).1
    have heU : e ∈ U := Finset.mem_filter.mpr ⟨heT,Or.inl heInternal.1⟩
    have heθ := (hθon e heU).mpr (Or.inr heInternal)
    exact ⟨⟨e,heθ,hends⟩,hIT hac.2.1,hIT hac.2.2.1,hac.2.2.2⟩
  have hOutside : sprinklingUnexploredGraph ω (T \ I) Q F ≤
      sprinklingUnexploredGraph θ T Q F := by
    intro a c hac
    obtain ⟨e,heTI,heOpen,hends⟩ := sprinklingUnexplored_adj_available_bond (T \ I) Q F hac
    have heT := extension_available_mono (T \ I) T Q F Finset.sdiff_subset heTI
    have heInternal := (mem_internalBondSet (T \ I) e).mp (Finset.mem_sdiff.mp heTI).1
    have heNot : e ∉ U := by
      intro heU
      rcases (Finset.mem_filter.mp heU).2 with hbaseI | htipI
      · exact (Finset.mem_sdiff.mp heInternal.1).2 hbaseI
      · exact (Finset.mem_sdiff.mp heInternal.2).2 htipI
    have heθ : θ e = true := (hθoff e heNot).trans heOpen
    exact ⟨⟨e,heθ,hends⟩,(Finset.mem_sdiff.mp hac.2.1).1,
      (Finset.mem_sdiff.mp hac.2.2.1).1,hac.2.2.2⟩
  have hSuffixω := hSuffix ω (fun _ _ => rfl)
  obtain ⟨hySuffix,_⟩ := hSuffixω
  obtain ⟨y,hy⟩ := hySuffix
  obtain ⟨hyCluster,hyTarget⟩ := Finset.mem_inter.mp hy
  have hyz : y = z := Finset.mem_singleton.mp hyTarget
  subst y
  have hzTI : z ∈ T \ I := ((mem_sprinklingUnexploredCluster ω (T \ I) Q F v z).mp hyCluster).1
  have hvz := ((mem_sprinklingUnexploredCluster ω (T \ I) Q F v z).mp hyCluster).2
  have hxz : (sprinklingUnexploredGraph θ T Q F).Reachable x z :=
    ((hconnected u huI).mono hstatic).trans (hbridgeθ.reachable.trans (hvz.mono hOutside))
  have hstep (a c : Vertex d)
      (ha : a ∈ I ∪ sprinklingUnexploredCluster ω T Q F x')
      (hac : (sprinklingUnexploredGraph θ T Q F).Adj a c) :
      c ∈ I ∪ sprinklingUnexploredCluster ω T Q F x' := by
    by_cases hcI : c ∈ I
    · exact Finset.mem_union.mpr (Or.inl hcI)
    obtain ⟨e,heT,heOpen,hends⟩ := sprinklingUnexplored_adj_available_bond T Q F hac
    have hePhys : s(e.1,bondTip e) = s(a,c) := by
      rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rfl
      · exact Sym2.eq_swap
    by_cases haI : a ∈ I
    · have heU : e ∈ U := by
        apply Finset.mem_filter.mpr
        refine ⟨heT,?_⟩
        rcases hends with ⟨haBase,hcTip⟩ | ⟨hcBase,haTip⟩
        · exact Or.inl (haBase ▸ haI)
        · exact Or.inr (haTip ▸ haI)
      have heAllowed := (hθon e heU).mp heOpen
      have heb : e = b := by
        rcases heAllowed with heb | ⟨hbaseI,htipI⟩
        · exact heb
        · have hcIn : c ∈ I := by
            rcases hends with ⟨_,hcTip⟩ | ⟨hcBase,_⟩
            · exact hcTip.symm ▸ htipI
            · exact hcBase.symm ▸ hbaseI
          exact (hcI hcIn).elim
      have hpair : s(a,c) = s(u,v) := by
        rw [← hePhys,heb]
        exact hbPhys
      have hcv : c = v := by
        rcases Sym2.eq_iff.mp hpair with ⟨_,hcv⟩ | ⟨hav,_⟩
        · exact hcv
        · exact (hvI (hav ▸ haI)).elim
      exact Finset.mem_union.mpr (Or.inr (hcv.symm ▸ hvOld))
    · have haOld : a ∈ sprinklingUnexploredCluster ω T Q F x' :=
        (Finset.mem_union.mp ha).resolve_left haI
      have heNot : e ∉ U := by
        intro heU
        have htouch := (Finset.mem_filter.mp heU).2
        rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact htouch.elim haI hcI
        · exact htouch.elim hcI haI
      have heω : ω e = true := (hθoff e heNot).symm.trans heOpen
      have hacω : (sprinklingUnexploredGraph ω T Q F).Adj a c := ⟨⟨e,heω,hends⟩,hac.2⟩
      have hcOld := (mem_sprinklingUnexploredCluster ω T Q F x' c).mpr
        ⟨hac.2.2.1,((mem_sprinklingUnexploredCluster ω T Q F x' a).mp haOld).2.trans hacω.reachable⟩
      exact Finset.mem_union.mpr (Or.inr hcOld)
  have hcontain : sprinklingUnexploredCluster θ T Q F x ⊆
      I ∪ sprinklingUnexploredCluster ω T Q F x' := by
    intro y hy
    obtain ⟨_,hyReach⟩ := (mem_sprinklingUnexploredCluster θ T Q F x y).mp hy
    obtain ⟨w⟩ := hyReach
    exact extension_walk_preserves (G := sprinklingUnexploredGraph θ T Q F)
      ((I ∪ sprinklingUnexploredCluster ω T Q F x' : Finset (Vertex d)) : Set (Vertex d))
      hstep w (Finset.mem_union.mpr (Or.inl hx))
  refine ⟨θ,hθoff,?_,hcontain⟩
  constructor
  · exact ⟨z,Finset.mem_inter.mpr
      ⟨(mem_sprinklingUnexploredCluster θ T Q F x z).mpr
        ⟨(Finset.mem_sdiff.mp hzTI).1,hxz⟩,Finset.mem_singleton_self z⟩⟩
  · rintro ⟨y,hy⟩
    obtain ⟨hyCluster,hyForbidden⟩ := Finset.mem_inter.mp hy
    obtain ⟨hyW,hyNotX⟩ := Finset.mem_sdiff.mp hyForbidden
    rcases Finset.mem_union.mp (hcontain hyCluster) with hyI | hyOld
    · exact hyNotX (Finset.mem_singleton.mpr (hIW y hyI hyW))
    · exact hshift.2 ⟨y,Finset.mem_inter.mpr ⟨hyOld,hyW⟩⟩

end NearCritical
