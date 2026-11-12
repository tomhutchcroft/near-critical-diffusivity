module
public import NearCritical.Section8DiagramCaseTwo
public import NearCritical.Section8TripodAttachment
public import NearCritical.Section8DiagramWalkCertificates

/-! Section 8, lem.Ay1y2_diagrams. Actual annulus paths and finite-forcing
diagram occurrences; nil legs and coincident branch vertices are allowed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

def annulusLink {d : ℕ} (Q H : Finset (Vertex d)) (x y : Vertex d) : Set (Configuration d) :=
  connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) x {y}

def annulusHit {d : ℕ} (Q H : Finset (Vertex d)) (x : Vertex d) : Set (Configuration d) :=
  connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) x (boundarySites H : Set (Vertex d))

def annulusDiagramOne {d : ℕ} (Q H : Finset (Vertex d)) (x y z u w : Vertex d) :
    Set (Configuration d) :=
  diagramOccurrence5 (annulusHit Q H w) (annulusLink Q H w u) (annulusLink Q H w y)
    (annulusLink Q H u x) (annulusLink Q H u z)

def annulusDiagramTwo {d : ℕ} (Q H : Finset (Vertex d)) (x y z u w : Vertex d) :
    Set (Configuration d) :=
  diagramOccurrence5 (annulusHit Q H u) (annulusLink Q H u w) (annulusLink Q H u z)
    (annulusLink Q H w x) (annulusLink Q H w y)

def annulusDiagramThree {d : ℕ} (Q H : Finset (Vertex d)) (x y z u w : Vertex d) :
    Set (Configuration d) :=
  diagramOccurrence5 (annulusHit Q H u) (annulusLink Q H u w) (annulusLink Q H u x)
    (annulusLink Q H w z) (annulusLink Q H w y)

def annulusDiagramFour {d : ℕ} (Q H : Finset (Vertex d)) (x y z u : Vertex d) :
    Set (Configuration d) :=
  diagramOccurrence4 (annulusHit Q H y) (annulusHit Q H u)
    (annulusLink Q H u x) (annulusLink Q H u z)

def annulusDiagramFive {d : ℕ} (Q H : Finset (Vertex d)) (x y z w : Vertex d) :
    Set (Configuration d) :=
  diagramOccurrence4 (annulusHit Q H x) (annulusHit Q H w)
    (annulusLink Q H w y) (annulusLink Q H w z)

private structure Leg {d : ℕ} (ω : Configuration d) (D : Finset (Vertex d)) (x y : Vertex d) where
  walk : (openGraph ω).Walk x y
  domain : ∀ v ∈ walk.support, v ∈ D

private def revLeg {d : ℕ} {ω : Configuration d} {D : Finset (Vertex d)} {x y : Vertex d}
    (p : Leg ω D x y) : Leg ω D y x :=
  ⟨p.walk.reverse,fun v hv => p.domain v (by
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv)⟩

private def prefixLeg {d : ℕ} {ω : Configuration d} {D : Finset (Vertex d)} {x y z : Vertex d}
    (r : Leg ω D x z) (p : (openGraph ω).Walk x y) (q : (openGraph ω).Walk y z)
    (hpq : p.append q = r.walk) : Leg ω D x y :=
  ⟨p,fun v hv => r.domain v (by rw [← hpq]; exact p.support_subset_support_append_left q hv)⟩

private def suffixLeg {d : ℕ} {ω : Configuration d} {D : Finset (Vertex d)} {x y z : Vertex d}
    (r : Leg ω D x z) (p : (openGraph ω).Walk x y) (q : (openGraph ω).Walk y z)
    (hpq : p.append q = r.walk) : Leg ω D y z :=
  ⟨q,fun v hv => r.domain v (by rw [← hpq]; exact p.support_subset_support_append_right q hv)⟩

private lemma rev_disjoint_left {d : ℕ} {ω : Configuration d} {x a y b : Vertex d}
    {p : (openGraph ω).Walk x a} {q : (openGraph ω).Walk y b}
    (h : p.edges.Disjoint q.edges) : p.reverse.edges.Disjoint q.edges := by
  apply List.disjoint_left.mpr
  intro e he hq
  exact List.disjoint_left.mp h
    (by simpa only [SimpleGraph.Walk.edges_reverse,List.mem_reverse] using he) hq

private lemma rev_disjoint_right {d : ℕ} {ω : Configuration d} {x a y b : Vertex d}
    {p : (openGraph ω).Walk x a} {q : (openGraph ω).Walk y b}
    (h : p.edges.Disjoint q.edges) : p.edges.Disjoint q.reverse.edges :=
  (rev_disjoint_left h.symm).symm

private lemma five_pairs {E : Type*} {A B C D F : List E}
    (h : List.Pairwise List.Disjoint [A,B,C,D,F]) :
    A.Disjoint B ∧ A.Disjoint C ∧ A.Disjoint D ∧ A.Disjoint F ∧
    B.Disjoint C ∧ B.Disjoint D ∧ B.Disjoint F ∧ C.Disjoint D ∧ C.Disjoint F ∧ D.Disjoint F := by
  simpa [List.pairwise_cons,and_assoc] using h

private lemma heart_arm {d : ℕ} {ω : Configuration d} (Q H : Finset (Vertex d))
    (x : Vertex d) (hx : x ∈ heartAnnulus Q H) (he : ω ∈ heartEvent Q H x) :
    ∃ a ∈ boundarySites H, ∃ p : Leg ω (heartAnnulus Q H) x a, p.walk.IsPath := by
  rw [heartEvent_eq_annulus Q H x hx] at he
  obtain ⟨hxD,a,haR,_haD,⟨w⟩⟩ := he
  have hle : restrictedGraph ω (heartAnnulus Q H : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
  let r : (openGraph ω).Walk x a :=
    (w.toPath : (restrictedGraph ω (heartAnnulus Q H : Set (Vertex d))).Walk x a).mapLe hle
  have hrD : ∀ v ∈ r.support, v ∈ heartAnnulus Q H := by
    intro v hv
    exact restrictedWalk_support
      (w.toPath : (restrictedGraph ω (heartAnnulus Q H : Set (Vertex d))).Walk x a) hxD v
      (by simpa only [r,SimpleGraph.Walk.support_mapLe_eq_support] using hv)
  exact ⟨a,haR,⟨r,hrD⟩,w.toPath.property.mapLe hle⟩

private lemma root_attachment {d : ℕ} {ω : Configuration d} (D : Finset (Vertex d))
    (R : Set (Vertex d)) {u x z a y w : Vertex d}
    (pa : Leg ω D u x) (pb : Leg ω D u z) (pc : Leg ω D u a) (py : Leg ω D y w)
    (hc : pc.walk.IsPath) (hw : w ∈ pc.walk.support) (ha : a ∈ R)
    (hab : pa.walk.edges.Disjoint pb.walk.edges) (hac : pa.walk.edges.Disjoint pc.walk.edges)
    (hbc : pb.walk.edges.Disjoint pc.walk.edges)
    (hfirst : ∀ v ∈ py.walk.support,
      v ∈ pa.walk.support ∨ v ∈ pb.walk.support ∨ v ∈ pc.walk.support → v = w) :
    ω ∈ diagramOccurrence5 (connectionToSetEvent (D : Set (Vertex d)) w R)
      (connectionToSetEvent (D : Set (Vertex d)) w {u})
      (connectionToSetEvent (D : Set (Vertex d)) w {y})
      (connectionToSetEvent (D : Set (Vertex d)) u {x})
      (connectionToSetEvent (D : Set (Vertex d)) u {z}) := by
  obtain ⟨t,s,hts,hpairs⟩ := tripod_attach_on_leg pa.walk pb.walk pc.walk py.walk hc hw hab hac hbc hfirst
  obtain ⟨hab',hat,has,hapy,hbt,hbs,hbpy,hts',htpy,hspy⟩ := five_pairs hpairs
  exact fiveOpenWalks_diagramOccurrence s t.reverse py.walk.reverse pa.walk pb.walk
    (D : Set (Vertex d)) R {u} {y} {x} {z}
    (suffixLeg pc t s hts).domain ha (revLeg (prefixLeg pc t s hts)).domain rfl
    (revLeg py).domain rfl pa.domain rfl pb.domain rfl
    (rev_disjoint_right hts'.symm) (rev_disjoint_right hspy) has.symm hbs.symm
    (rev_disjoint_left (rev_disjoint_right htpy)) (rev_disjoint_left hat.symm)
    (rev_disjoint_left hbt.symm) (rev_disjoint_left hapy.symm) (rev_disjoint_left hbpy.symm) hab'

private lemma side_attachment {d : ℕ} {ω : Configuration d} (D : Finset (Vertex d))
    (R : Set (Vertex d)) {u a b c y w : Vertex d}
    (pa : Leg ω D u a) (pb : Leg ω D u b) (pc : Leg ω D u c) (py : Leg ω D y w)
    (hc : pc.walk.IsPath) (hw : w ∈ pc.walk.support) (hb : b ∈ R)
    (hab : pa.walk.edges.Disjoint pb.walk.edges) (hac : pa.walk.edges.Disjoint pc.walk.edges)
    (hbc : pb.walk.edges.Disjoint pc.walk.edges)
    (hfirst : ∀ v ∈ py.walk.support,
      v ∈ pa.walk.support ∨ v ∈ pb.walk.support ∨ v ∈ pc.walk.support → v = w) :
    ω ∈ diagramOccurrence5 (connectionToSetEvent (D : Set (Vertex d)) u R)
      (connectionToSetEvent (D : Set (Vertex d)) u {w})
      (connectionToSetEvent (D : Set (Vertex d)) u {a})
      (connectionToSetEvent (D : Set (Vertex d)) w {c})
      (connectionToSetEvent (D : Set (Vertex d)) w {y}) := by
  obtain ⟨t,s,hts,hpairs⟩ := tripod_attach_on_leg pa.walk pb.walk pc.walk py.walk hc hw hab hac hbc hfirst
  obtain ⟨hab',hat,has,hapy,hbt,hbs,hbpy,hts',htpy,hspy⟩ := five_pairs hpairs
  exact fiveOpenWalks_diagramOccurrence pb.walk t pa.walk s py.walk.reverse
    (D : Set (Vertex d)) R {w} {a} {c} {y}
    pb.domain hb (prefixLeg pc t s hts).domain rfl pa.domain rfl
    (suffixLeg pc t s hts).domain rfl (revLeg py).domain rfl hbt hab'.symm hbs (rev_disjoint_right hbpy)
    hat.symm hts' (rev_disjoint_right htpy) has (rev_disjoint_right hapy) (rev_disjoint_right hspy)

/-- Every literal branch configuration contains one of the five actual
finite-forcing diagrams, with its branch vertices inside the annulus. -/
theorem heartBranch_has_annulus_diagram {d : ℕ} (Q H : Finset (Vertex d)) (x y z : Vertex d)
    (hx : x ∈ heartAnnulus Q H) (hy : y ∈ heartAnnulus Q H) (hz : z ∈ heartAnnulus Q H)
    {ω : Configuration d} (hA : ω ∈ heartBranchEvent Q H x y z) :
    (∃ u ∈ heartAnnulus Q H, ∃ w ∈ heartAnnulus Q H,
      ω ∈ annulusDiagramOne Q H x y z u w ∨ ω ∈ annulusDiagramTwo Q H x y z u w ∨
        ω ∈ annulusDiagramThree Q H x y z u w) ∨
    (∃ u ∈ heartAnnulus Q H, ω ∈ annulusDiagramFour Q H x y z u) ∨
    (∃ w ∈ heartAnnulus Q H, ω ∈ annulusDiagramFive Q H x y z w) := by
  let D := heartAnnulus Q H
  let R : Set (Vertex d) := (boundarySites H : Set (Vertex d))
  obtain ⟨a,ha,wx,hwx⟩ := heart_arm Q H x hx hA.1.1.1
  obtain ⟨b,hb,wy,_hwy⟩ := heart_arm Q H y hy hA.1.1.2
  obtain ⟨c,hc,wz,hwz⟩ := heart_arm Q H z hz hA.1.2
  have hA' := hA
  rw [heartBranchEvent_eq_annulus Q H x y z hx hy hz] at hA'
  by_cases hex : ∃ v ∈ wz.walk.support, v ∈ wx.walk.support
  · obtain ⟨u,p,q,r,s,hpq,hrs,hpqdis,hrp,hrq,_hfirstX⟩ :=
      first_hit_tripod wx.walk hwx wz.walk hex
    let pa := revLeg (prefixLeg wx p q hpq)
    let pb := revLeg (prefixLeg wz r s hrs)
    let pc := suffixLeg wx p q hpq
    have hab : pa.walk.edges.Disjoint pb.walk.edges := rev_disjoint_left (rev_disjoint_right hrp.symm)
    have hac : pa.walk.edges.Disjoint pc.walk.edges := rev_disjoint_left hpqdis
    have hbc : pb.walk.edges.Disjoint pc.walk.edges := rev_disjoint_left hrq
    have hpa : pa.walk.IsPath := (SimpleGraph.Walk.IsPath.of_append_left (hpq.symm ▸ hwx)).reverse
    have hpb : pb.walk.IsPath := (SimpleGraph.Walk.IsPath.of_append_left (hrs.symm ▸ hwz)).reverse
    have hpc : pc.walk.IsPath := SimpleGraph.Walk.IsPath.of_append_right (hpq.symm ▸ hwx)
    have hu : u ∈ D := pa.domain u pa.walk.start_mem_support
    let T : Set (Vertex d) := {v | v ∈ pa.walk.support ∨ v ∈ pb.walk.support ∨ v ∈ pc.walk.support}
    by_cases hY : ∃ v ∈ wy.walk.support, v ∈ T
    · obtain ⟨w,py,qy,hpy,hwT,hfirst⟩ := walk_first_hit wy.walk T hY
      let ly := prefixLeg wy py qy hpy
      have hwD : w ∈ D := ly.domain w ly.walk.end_mem_support
      rcases hwT with hwa | hwb | hwc
      · have hf : ∀ v ∈ ly.walk.support,
            v ∈ pb.walk.support ∨ v ∈ pc.walk.support ∨ v ∈ pa.walk.support → v = w := by
          intro v hv hm
          apply hfirst v hv
          rcases hm with hm | hm | hm
          · exact Or.inr (Or.inl hm)
          · exact Or.inr (Or.inr hm)
          · exact Or.inl hm
        have hD2 : ω ∈ annulusDiagramTwo Q H x y z u w :=
          side_attachment D R pb pc pa ly hpa hwa ha hbc hab.symm hac.symm hf
        exact Or.inl ⟨u,hu,w,hwD,Or.inr (Or.inl hD2)⟩
      · have hf : ∀ v ∈ ly.walk.support,
            v ∈ pa.walk.support ∨ v ∈ pc.walk.support ∨ v ∈ pb.walk.support → v = w := by
          intro v hv hm
          apply hfirst v hv
          rcases hm with hm | hm | hm
          · exact Or.inl hm
          · exact Or.inr (Or.inr hm)
          · exact Or.inr (Or.inl hm)
        have hD3 : ω ∈ annulusDiagramThree Q H x y z u w :=
          side_attachment D R pa pc pb ly hpb hwb ha hac hab hbc.symm hf
        exact Or.inl ⟨u,hu,w,hwD,Or.inr (Or.inr hD3)⟩
      · have hD1 : ω ∈ annulusDiagramOne Q H x y z u w :=
          root_attachment D R pa pb pc ly hpc hwc ha hab hac hbc hfirst
        exact Or.inl ⟨u,hu,w,hwD,Or.inl hD1⟩
    · have hydis {v : Vertex d} (l : Leg ω D u v)
          (hl : ∀ t ∈ l.walk.support, t ∈ T) : wy.walk.edges.Disjoint l.walk.edges := by
        apply walk_edges_disjoint_of_one_common_vertex (u := u)
        intro t hty htl
        exact (hY ⟨t,hty,hl t htl⟩).elim
      have hya := hydis pa (fun _ ht => Or.inl ht)
      have hyb := hydis pb (fun _ ht => Or.inr (Or.inl ht))
      have hyc := hydis pc (fun _ ht => Or.inr (Or.inr ht))
      have hD4 : ω ∈ annulusDiagramFour Q H x y z u :=
        fourOpenWalks_diagramOccurrence wy.walk pc.walk pa.walk pb.walk
          (D : Set (Vertex d)) R R {x} {z} wy.domain pc.domain pa.domain pb.domain
          hb ha rfl rfl hyc hya hyb hac.symm hbc.symm hab
      exact Or.inr (Or.inl ⟨u,hu,hD4⟩)
  · have hsup : wx.walk.support.Disjoint wz.walk.support :=
      List.disjoint_left.mpr (fun v hvx hvz => hex ⟨v,hvz,hvx⟩)
    have hxde : wx.walk.edges.Disjoint wz.walk.edges := by
      apply walk_edges_disjoint_of_one_common_vertex (u := x)
      intro v hvx hvz
      exact (List.disjoint_left.mp hsup hvx hvz).elim
    have hyz : ∃ v ∈ wy.walk.support, v ∈ wz.walk.support := by
      by_contra hn
      have hyde : wy.walk.edges.Disjoint wz.walk.edges := by
        apply walk_edges_disjoint_of_one_common_vertex (u := y)
        intro v hvy hvz
        exact (hn ⟨v,hvy,hvz⟩).elim
      exact (heartBranch_walks_not_separated D (boundarySites H) hA' wx.walk wy.walk wz.walk
        wx.domain wy.domain wz.domain ha hb hc) ⟨hxde,hyde⟩
    obtain ⟨u,py,rz,sz,hu,_hrsz,hxp,hxr,hxs,hpr,hps,hrs,hpyD,hrzD,hszD⟩ :=
      branch_caseTwo_diagram_five D (boundarySites H) hA' wx.walk wy.walk wz.walk hwz
        wx.domain wy.domain wz.domain ha hc hsup hyz
    have hD5 : ω ∈ annulusDiagramFive Q H x y z u :=
      fourOpenWalks_diagramOccurrence wx.walk sz py.reverse rz.reverse
        (D : Set (Vertex d)) R R {y} {z} wx.domain hszD
        (revLeg (⟨py,hpyD⟩ : Leg ω D y u)).domain (revLeg (⟨rz,hrzD⟩ : Leg ω D z u)).domain
        ha hc rfl rfl hxs (rev_disjoint_right hxp) (rev_disjoint_right hxr)
        (rev_disjoint_right hps.symm) (rev_disjoint_right hrs.symm)
        (rev_disjoint_left (rev_disjoint_right hpr))
    exact Or.inr (Or.inr ⟨u,hu,hD5⟩)

def annulusG {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d)) (v : Vertex d) : ℝ :=
  (percolation d p).real (annulusHit Q H v)

def annulusTau {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d)) (v w : Vertex d) : ℝ :=
  (percolation d p).real (annulusLink Q H v w)

private lemma hit_increasing {d : ℕ} (Q H : Finset (Vertex d)) (v : Vertex d) :
    BK.Increasing (annulusHit Q H v) := connectionToSetEvent_increasing _ _ _

private lemma link_increasing {d : ℕ} (Q H : Finset (Vertex d)) (v w : Vertex d) :
    BK.Increasing (annulusLink Q H v w) := connectionToSetEvent_increasing _ _ _

private lemma diagram_one_bound {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x y z u w : Vertex d) :
    (percolation d p).real (annulusDiagramOne Q H x y z u w) ≤
      annulusG p Q H w*annulusTau p Q H w u*annulusTau p Q H w y*
        annulusTau p Q H u x*annulusTau p Q H u z :=
  diagramOccurrence5_probability_le p _ _ _ _ _ (hit_increasing Q H w)
    (link_increasing Q H w u) (link_increasing Q H w y)
    (link_increasing Q H u x) (link_increasing Q H u z)

private lemma diagram_two_bound {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x y z u w : Vertex d) :
    (percolation d p).real (annulusDiagramTwo Q H x y z u w) ≤
      annulusG p Q H u*annulusTau p Q H u w*annulusTau p Q H u z*
        annulusTau p Q H w x*annulusTau p Q H w y :=
  diagramOccurrence5_probability_le p _ _ _ _ _ (hit_increasing Q H u)
    (link_increasing Q H u w) (link_increasing Q H u z)
    (link_increasing Q H w x) (link_increasing Q H w y)

private lemma diagram_three_bound {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x y z u w : Vertex d) :
    (percolation d p).real (annulusDiagramThree Q H x y z u w) ≤
      annulusG p Q H u*annulusTau p Q H u w*annulusTau p Q H u x*
        annulusTau p Q H w z*annulusTau p Q H w y :=
  diagramOccurrence5_probability_le p _ _ _ _ _ (hit_increasing Q H u)
    (link_increasing Q H u w) (link_increasing Q H u x)
    (link_increasing Q H w z) (link_increasing Q H w y)

private lemma diagram_four_bound {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x y z u : Vertex d) :
    (percolation d p).real (annulusDiagramFour Q H x y z u) ≤
      annulusG p Q H y*annulusG p Q H u*annulusTau p Q H u x*annulusTau p Q H u z :=
  diagramOccurrence4_probability_le p _ _ _ _ (hit_increasing Q H y) (hit_increasing Q H u)
    (link_increasing Q H u x) (link_increasing Q H u z)

private lemma diagram_five_bound {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x y z w : Vertex d) :
    (percolation d p).real (annulusDiagramFive Q H x y z w) ≤
      annulusG p Q H x*annulusG p Q H w*annulusTau p Q H w y*annulusTau p Q H w z :=
  diagramOccurrence4_probability_le p _ _ _ _ (hit_increasing Q H x) (hit_increasing Q H w)
    (link_increasing Q H w y) (link_increasing Q H w z)

private lemma double_union_bound {d : ℕ} (p : unitInterval) (D : Finset (Vertex d))
    (E : Vertex d → Vertex d → Set (Configuration d)) :
    (percolation d p).real (⋃ u ∈ D, ⋃ w ∈ D, E u w) ≤
      ∑ u ∈ D, ∑ w ∈ D, (percolation d p).real (E u w) :=
  (measureReal_biUnion_finset_le D (fun u => ⋃ w ∈ D, E u w)).trans
    (Finset.sum_le_sum (fun u _hu => measureReal_biUnion_finset_le D (E u)))

/-- Source lem.Ay1y2_diagrams, for actual finite heart events. The five
products are in the source order. No diagram inclusion or probability bound
is supplied as a hypothesis. -/
theorem heartBranch_probability_le_five_diagrams {d : ℕ} (p : unitInterval)
    (Q H : Finset (Vertex d)) (x y z : Vertex d)
    (hx : x ∈ heartAnnulus Q H) (hy : y ∈ heartAnnulus Q H) (hz : z ∈ heartAnnulus Q H) :
    (percolation d p).real (heartBranchEvent Q H x y z) ≤
      (∑ u ∈ heartAnnulus Q H, ∑ w ∈ heartAnnulus Q H,
        annulusG p Q H w*annulusTau p Q H w u*annulusTau p Q H w y*
          annulusTau p Q H u x*annulusTau p Q H u z) +
      (∑ u ∈ heartAnnulus Q H, ∑ w ∈ heartAnnulus Q H,
        annulusG p Q H u*annulusTau p Q H u w*annulusTau p Q H u z*
          annulusTau p Q H w x*annulusTau p Q H w y) +
      (∑ u ∈ heartAnnulus Q H, ∑ w ∈ heartAnnulus Q H,
        annulusG p Q H u*annulusTau p Q H u w*annulusTau p Q H u x*
          annulusTau p Q H w z*annulusTau p Q H w y) +
      annulusG p Q H y*(∑ u ∈ heartAnnulus Q H,
        annulusG p Q H u*annulusTau p Q H u x*annulusTau p Q H u z) +
      annulusG p Q H x*(∑ w ∈ heartAnnulus Q H,
        annulusG p Q H w*annulusTau p Q H w y*annulusTau p Q H w z) := by
  let D := heartAnnulus Q H
  let B₁ : Set (Configuration d) := ⋃ u ∈ D, ⋃ w ∈ D, annulusDiagramOne Q H x y z u w
  let B₂ : Set (Configuration d) := ⋃ u ∈ D, ⋃ w ∈ D, annulusDiagramTwo Q H x y z u w
  let B₃ : Set (Configuration d) := ⋃ u ∈ D, ⋃ w ∈ D, annulusDiagramThree Q H x y z u w
  let B₄ : Set (Configuration d) := ⋃ u ∈ D, annulusDiagramFour Q H x y z u
  let B₅ : Set (Configuration d) := ⋃ w ∈ D, annulusDiagramFive Q H x y z w
  have hm {ω : Configuration d} (E : Vertex d → Vertex d → Set (Configuration d))
      {u w : Vertex d} (hu : u ∈ D) (hw : w ∈ D) (he : ω ∈ E u w) :
      ω ∈ ⋃ u ∈ D, ⋃ w ∈ D, E u w :=
    Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,
      Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨hw,he⟩⟩⟩⟩
  have hsub : heartBranchEvent Q H x y z ⊆ B₁ ∪ (B₂ ∪ (B₃ ∪ (B₄ ∪ B₅))) := by
    intro ω hω
    rcases heartBranch_has_annulus_diagram Q H x y z hx hy hz hω with h123 | h4 | h5
    · obtain ⟨u,hu,w,hw,hcases⟩ := h123
      rcases hcases with h1 | h2 | h3
      · exact Or.inl (hm (annulusDiagramOne Q H x y z) hu hw h1)
      · exact Or.inr (Or.inl (hm (annulusDiagramTwo Q H x y z) hu hw h2))
      · exact Or.inr (Or.inr (Or.inl (hm (annulusDiagramThree Q H x y z) hu hw h3)))
    · obtain ⟨u,hu,h4⟩ := h4
      exact Or.inr (Or.inr (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,h4⟩⟩))))
    · obtain ⟨w,hw,h5⟩ := h5
      exact Or.inr (Or.inr (Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨hw,h5⟩⟩))))
  have hsum : (percolation d p).real (heartBranchEvent Q H x y z) ≤
      (percolation d p).real B₁+(percolation d p).real B₂+(percolation d p).real B₃+
        (percolation d p).real B₄+(percolation d p).real B₅ := by
    have h0 := measureReal_mono (μ := percolation d p) hsub
    have h12 := measureReal_union_le (μ := percolation d p) B₁ (B₂ ∪ (B₃ ∪ (B₄ ∪ B₅)))
    have h23 := measureReal_union_le (μ := percolation d p) B₂ (B₃ ∪ (B₄ ∪ B₅))
    have h34 := measureReal_union_le (μ := percolation d p) B₃ (B₄ ∪ B₅)
    have h45 := measureReal_union_le (μ := percolation d p) B₄ B₅
    linarith
  have h1 : (percolation d p).real B₁ ≤
      ∑ u ∈ D, ∑ w ∈ D, annulusG p Q H w*annulusTau p Q H w u*annulusTau p Q H w y*
        annulusTau p Q H u x*annulusTau p Q H u z :=
    (double_union_bound p D (annulusDiagramOne Q H x y z)).trans
      (Finset.sum_le_sum (fun u _hu => Finset.sum_le_sum (fun w _hw => diagram_one_bound p Q H x y z u w)))
  have h2 : (percolation d p).real B₂ ≤
      ∑ u ∈ D, ∑ w ∈ D, annulusG p Q H u*annulusTau p Q H u w*annulusTau p Q H u z*
        annulusTau p Q H w x*annulusTau p Q H w y :=
    (double_union_bound p D (annulusDiagramTwo Q H x y z)).trans
      (Finset.sum_le_sum (fun u _hu => Finset.sum_le_sum (fun w _hw => diagram_two_bound p Q H x y z u w)))
  have h3 : (percolation d p).real B₃ ≤
      ∑ u ∈ D, ∑ w ∈ D, annulusG p Q H u*annulusTau p Q H u w*annulusTau p Q H u x*
        annulusTau p Q H w z*annulusTau p Q H w y :=
    (double_union_bound p D (annulusDiagramThree Q H x y z)).trans
      (Finset.sum_le_sum (fun u _hu => Finset.sum_le_sum (fun w _hw => diagram_three_bound p Q H x y z u w)))
  have h4 : (percolation d p).real B₄ ≤ annulusG p Q H y*
      (∑ u ∈ D, annulusG p Q H u*annulusTau p Q H u x*annulusTau p Q H u z) := by
    calc
      _ ≤ ∑ u ∈ D, (percolation d p).real (annulusDiagramFour Q H x y z u) :=
        measureReal_biUnion_finset_le D _
      _ ≤ ∑ u ∈ D, annulusG p Q H y*annulusG p Q H u*annulusTau p Q H u x*annulusTau p Q H u z :=
        Finset.sum_le_sum (fun u _hu => diagram_four_bound p Q H x y z u)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _hu
        ring
  have h5 : (percolation d p).real B₅ ≤ annulusG p Q H x*
      (∑ w ∈ D, annulusG p Q H w*annulusTau p Q H w y*annulusTau p Q H w z) := by
    calc
      _ ≤ ∑ w ∈ D, (percolation d p).real (annulusDiagramFive Q H x y z w) :=
        measureReal_biUnion_finset_le D _
      _ ≤ ∑ w ∈ D, annulusG p Q H x*annulusG p Q H w*annulusTau p Q H w y*annulusTau p Q H w z :=
        Finset.sum_le_sum (fun w _hw => diagram_five_bound p Q H x y z w)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _hw
        ring
  linarith

end NearCritical.Section8
