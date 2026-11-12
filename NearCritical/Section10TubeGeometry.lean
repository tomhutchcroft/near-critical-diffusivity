module

public import Mathlib.Tactic

/-! Exact tube separation in Section10 eq.def.SQH.ell0.T / lem.skl.independent.
Every unoriented nearest-neighbor coarse edge has a canonical positive-axis
representation (a,i). Coordinates below retain the source strict tube bounds. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Source tube from ell*a to ell*(a+e_i), intersected with lattice vertices.
Multiplication by sixteen removes all midpoint/width fractions exactly. -/
def coarseTubeVertices {d : ℕ} (ell : ℝ) (a : Fin d → ℤ) (i : Fin d) :
    Set (Fin d → ℤ) := {x | ∀ k,
      |16*(x k:ℝ)-16*ell*(a k:ℝ)-(if k=i then 8*ell else 0)| <
        if k=i then 5*ell else 3*ell}

private lemma perpendicular_tube_coordinate_impossible (ell x : ℝ) (hell : 0 < ell)
    (a b : ℤ) (ha : |16*x-16*ell*(a:ℝ)-8*ell| < 5*ell)
    (hb : |16*x-16*ell*(b:ℝ)| < 3*ell) : False := by
  obtain ⟨haL,haU⟩ := abs_lt.mp ha
  obtain ⟨hbL,hbU⟩ := abs_lt.mp hb
  by_cases hab : a < b
  · have habZ : a+1 ≤ b := by omega
    have habR : (a:ℝ)+1 ≤ (b:ℝ) := by exact_mod_cast habZ
    nlinarith [mul_nonneg hell.le (sub_nonneg.mpr habR)]
  · have habR : (b:ℝ) ≤ (a:ℝ) := by exact_mod_cast (le_of_not_gt hab)
    nlinarith [mul_nonneg hell.le (sub_nonneg.mpr habR)]

private lemma parallel_tube_coordinate_impossible (ell x offset : ℝ) (hell : 0 < ell)
    (a b : ℤ) (hab : a ≠ b)
    (ha : |16*x-16*ell*(a:ℝ)-offset| < 5*ell)
    (hb : |16*x-16*ell*(b:ℝ)-offset| < 5*ell) : False := by
  obtain ⟨haL,haU⟩ := abs_lt.mp ha
  obtain ⟨hbL,hbU⟩ := abs_lt.mp hb
  rcases lt_or_gt_of_ne hab with hab | hab
  · have habZ : a+1 ≤ b := by omega
    have habR : (a:ℝ)+1 ≤ (b:ℝ) := by exact_mod_cast habZ
    nlinarith [mul_nonneg hell.le (sub_nonneg.mpr habR)]
  · have habZ : b+1 ≤ a := by omega
    have habR : (b:ℝ)+1 ≤ (a:ℝ) := by exact_mod_cast habZ
    nlinarith [mul_nonneg hell.le (sub_nonneg.mpr habR)]

/-- The literal source tubes of distinct canonical coarse-neighbor pairs are
vertex-disjoint. No separation/disjointness conclusion is a premise. -/
theorem coarseTubeVertices_disjoint {d : ℕ} {ell : ℝ} (hell : 0 < ell)
    (a b : Fin d → ℤ) (i j : Fin d) (hne : (a,i) ≠ (b,j)) :
    Disjoint (coarseTubeVertices ell a i) (coarseTubeVertices ell b j) := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  by_cases hij : i = j
  · subst j
    have hab : a ≠ b := by
      intro heq
      exact hne (by rw [heq])
    have hcoord : ∃ k, a k ≠ b k := by
      by_contra h
      apply hab
      funext k
      by_contra hk
      exact h ⟨k,hk⟩
    obtain ⟨k,hk⟩ := hcoord
    have ha : |16*(x k:ℝ)-16*ell*(a k:ℝ)-(if k=i then 8*ell else 0)| < 5*ell := by
      have h := hxa k
      change |16*(x k:ℝ)-16*ell*(a k:ℝ)-(if k=i then 8*ell else 0)| <
        (if k=i then 5*ell else 3*ell) at h
      split_ifs at h ⊢ <;> linarith
    have hb : |16*(x k:ℝ)-16*ell*(b k:ℝ)-(if k=i then 8*ell else 0)| < 5*ell := by
      have h := hxb k
      change |16*(x k:ℝ)-16*ell*(b k:ℝ)-(if k=i then 8*ell else 0)| <
        (if k=i then 5*ell else 3*ell) at h
      split_ifs at h ⊢ <;> linarith
    exact parallel_tube_coordinate_impossible ell (x k:ℝ) _ hell (a k) (b k) hk ha hb
  · have ha : |16*(x i:ℝ)-16*ell*(a i:ℝ)-8*ell| < 5*ell := by
      have h := hxa i
      change |16*(x i:ℝ)-16*ell*(a i:ℝ)-(if i=i then 8*ell else 0)| <
        (if i=i then 5*ell else 3*ell) at h
      rw [if_pos (rfl : i=i),if_pos (rfl : i=i)] at h
      exact h
    have hb : |16*(x i:ℝ)-16*ell*(b i:ℝ)| < 3*ell := by
      simpa only [if_neg hij,sub_zero] using hxb i
    exact perpendicular_tube_coordinate_impossible ell (x i:ℝ) hell (a i) (b i) ha hb

/-- Pairwise form for finite collections of source tubes, suitable for the
product-law independence step once actual fresh bond masks are identified. -/
theorem coarseTubeVertices_pairwiseDisjoint {d : ℕ} {ell : ℝ} (hell : 0 < ell) :
    (Set.univ : Set ((Fin d → ℤ) × Fin d)).PairwiseDisjoint
      (fun e => coarseTubeVertices ell e.1 e.2) := by
  intro e _ f _ hef
  exact coarseTubeVertices_disjoint hell e.1 f.1 e.2 f.2 hef

end NearCritical.Section10
