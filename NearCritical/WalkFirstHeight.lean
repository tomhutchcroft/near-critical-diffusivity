module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Lean.Elab.Tactic.Omega

/-! First-height cuts for actual finite walks. The height function and its
nearest-neighbor bound are explicit, so this also applies to issued networks. -/
@[expose] public section
namespace NearCritical

/-- Stop at the first crossing of an integer level. The selected prefix stays
below that level, including a nil prefix if the start is already on it. -/
theorem walk_first_height_prefix {V : Type*} {G : SimpleGraph V}
    (height : V → ℤ)
    (hstep : ∀ {u v}, G.Adj u v → height v ≤ height u+1)
    {x y : V} (w : G.Walk x y) (l : ℤ)
    (hx : height x ≤ l) (hy : l ≤ height y) :
    ∃ (u : V) (p : G.Walk x u) (q : G.Walk u y),
      p.append q = w ∧ height u = l ∧ ∀ z ∈ p.support, height z ≤ l := by
  induction w with
  | @nil u =>
      refine ⟨_,.nil,.nil,rfl,le_antisymm hx hy,?_⟩
      intro z hz
      have hzx : z=u := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
      simpa only [hzx] using hx
  | @cons x v y h w ih =>
      by_cases hxl : height x = l
      · refine ⟨x,.nil,w.cons h,rfl,hxl,?_⟩
        intro z hz
        have hzx : z=x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
        simpa only [hzx] using hx
      · have hv : height v ≤ l := by have hs := hstep h; omega
        obtain ⟨u,p,q,hpq,hu,hp⟩ := ih hv hy
        refine ⟨u,p.cons h,q,?_,hu,?_⟩
        · simp only [SimpleGraph.Walk.cons_append,hpq]
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hx
          · exact hp z hz

/-- Two successive first-height cuts retain the respective upper domains.
No simplicity or disjointness is assumed here; those are supplied separately
by the original simple path when making disjoint forcing certificates. -/
theorem walk_two_height_prefixes {V : Type*} {G : SimpleGraph V}
    (height : V → ℤ)
    (hstep : ∀ {u v}, G.Adj u v → height v ≤ height u+1)
    {x y : V} (w : G.Walk x y) (m n : ℤ)
    (hx : height x ≤ m) (hmn : m ≤ n) (hy : n ≤ height y) :
    ∃ (u v : V) (p : G.Walk x u) (q : G.Walk u v) (r : G.Walk v y),
      p.append (q.append r) = w ∧ height u = m ∧ height v = n ∧
        (∀ z ∈ p.support, height z ≤ m) ∧
        (∀ z ∈ q.support, height z ≤ n) := by
  obtain ⟨v,s,r,hsr,hv,hs⟩ := walk_first_height_prefix height hstep w n (hx.trans hmn) hy
  obtain ⟨u,p,q,hpq,hu,hp⟩ := walk_first_height_prefix height hstep s m hx (hmn.trans hv.ge)
  refine ⟨u,v,p,q,r,?_,hu,hv,hp,?_⟩
  · rw [SimpleGraph.Walk.append_assoc,hpq,hsr]
  · intro z hz
    apply hs z
    rw [← hpq,SimpleGraph.Walk.support_append_eq_support_dropLast_append]
    exact List.mem_append.mpr (Or.inr hz)

end NearCritical
