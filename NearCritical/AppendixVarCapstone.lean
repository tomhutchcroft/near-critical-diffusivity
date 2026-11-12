module

public import NearCritical.AppendixVarTerm1Phi
public import NearCritical.AppendixVarTerm2Case2
public import NearCritical.AppendixVarTerm3Cases
public import NearCritical.AppendixVarTerm4AllDimensions
public import NearCritical.AppendixVarAssembly

/-! Appendix B end-to-end: the variance bound `Var ≲ r^{6-d}` (prop.VARf1/VARf2, the
Appendix-B part) assembled from the four var_terms on the LITERAL source geometry.

Dimension `d = E + 7` with `E ≥ 2` (so `d ≥ 9`). The geometry is:
* `Ann = Ann_{c₁n} = sourceAnnulus n c`;
* `outer = Λ_n \ Λ_h = {w ∈ Ann : |w| > h}`, so `Ann \ outer = Ann ∩ Λ_h = sourceAnnulus h c`
  (`h = n/2`, `2c ≤ h`, `2h ≤ n`);
* `x` on `∂Λ_n` (`|x|_∞ = n`).
The geometric facts used by the var_terms are proved here: `Ann ⊆ ball(x,2n) ∩ Λ_n`, and
`|x-w| ≥ 2q` on the inner region with `q = (n-h)/2`, `n ≤ 4(q+1)`.

`VARf_capstone` takes:
* `hdecomp` (lem.Ay1y2_diagrams: `Var ≤ T1+T2+T3+T4`);
* one shared list of pointwise inputs: eq.g_outer, eq.g_inner, eq.F_pointwise, lem.F_RD,
  lem.box_twopoint_onesided/twosided, the full-space two-point bound, lem.RD_bound, and
  `0 ≤ l_u ≤ |x-u|`;
* `ρ ≤ Cρ` (lem.rho_F_basic);
* `hbubble` (var_term_2's outer bubble/kernel input);
* the EXPLICIT regime hypothesis `(1+log n)/n^{d-6} ≤ K/r^{d-6}`, needed by var_term_3 and
  var_term_4's inner region. The source asserts it as "`n` sufficiently large", but it fails
  uniformly at `r ≍ n`.
It concludes `∃ C ≥ 0, Var ≤ C/r^{d-6}`. var_term_4's inner region reuses `var_term_3_source`
with `τ := F/n³` and `ρ := 1`. All inputs are explicit hypotheses; none is assumed silently.
 -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

theorem mem_cube_iff_dist {D m : ℕ} {w : Fin D → ℤ} :
    w ∈ (cube m : Finset (Fin D → ℤ)) ↔ linfDist (0 : Fin D → ℤ) w ≤ m := by
  rw [cube_eq_linfBall, mem_linfBall_iff_dist 0 w (by positivity)]
  simp

/-- `outer = Λ_n \ Λ_h` inside `Ann_{c₁n}`. -/
def capOuter {k : ℕ} (n h c : ℕ) : Finset (Fin (k + 1) → ℤ) :=
  (sourceAnnulus n c).filter (fun w => h < linfDist (0 : Fin (k + 1) → ℤ) w)

theorem capOuter_subset {k n h c : ℕ} :
    (capOuter n h c : Finset (Fin (k + 1) → ℤ)) ⊆ sourceAnnulus n c :=
  Finset.filter_subset _ _

theorem sourceAnnulus_sdiff_capOuter {k n h c : ℕ} (hhn : h ≤ n) :
    (sourceAnnulus n c : Finset (Fin (k + 1) → ℤ)) \ capOuter n h c = sourceAnnulus h c := by
  ext w
  simp only [capOuter, sourceAnnulus, Finset.mem_sdiff, Finset.mem_filter, mem_cube_iff_dist]
  omega

theorem sourceAnnulus_mono {k n h c : ℕ} (hhn : h ≤ n) :
    (sourceAnnulus h c : Finset (Fin (k + 1) → ℤ)) ⊆ sourceAnnulus n c := by
  intro w hw
  simp only [sourceAnnulus, Finset.mem_filter, mem_cube_iff_dist] at hw ⊢
  omega

theorem sourceAnnulus_subset_ball_x {k n c : ℕ} {x : Fin (k + 1) → ℤ}
    (hx : linfDist (0 : Fin (k + 1) → ℤ) x = n) :
    (sourceAnnulus n c : Finset (Fin (k + 1) → ℤ)) ⊆ linfBall x ((2 * n : ℕ) : ℤ) := by
  intro w hw
  simp only [sourceAnnulus, Finset.mem_filter, mem_cube_iff_dist] at hw
  rw [mem_linfBall_iff_dist x w (by positivity)]
  have htri := linfDist_triangle x 0 w
  rw [linfDist_comm x 0] at htri
  simp only [Int.toNat_natCast]
  omega

theorem sourceAnnulus_subset_ball_zero {k n c : ℕ} :
    (sourceAnnulus n c : Finset (Fin (k + 1) → ℤ)) ⊆
      linfBall (0 : Fin (k + 1) → ℤ) (n : ℤ) := by
  intro w hw
  simp only [sourceAnnulus, Finset.mem_filter, mem_cube_iff_dist] at hw
  rw [mem_linfBall_iff_dist 0 w (by positivity)]
  simp only [Int.toNat_natCast]
  omega

theorem inner_far_from_x {k n h c : ℕ} {x : Fin (k + 1) → ℤ}
    (hx : linfDist (0 : Fin (k + 1) → ℤ) x = n) :
    ∀ w ∈ (sourceAnnulus h c : Finset (Fin (k + 1) → ℤ)),
      2 * ((n - h) / 2) ≤ linfDist x w := by
  intro w hw
  simp only [sourceAnnulus, Finset.mem_filter, mem_cube_iff_dist] at hw
  have htri := linfDist_triangle (0 : Fin (k + 1) → ℤ) w x
  rw [linfDist_comm w x] at htri
  omega

theorem sourceR_cast_eq {k c : ℕ} {u : Fin (k + 1) → ℤ}
    (hu : c ≤ linfDist (0 : Fin (k + 1) → ℤ) u) :
    ((linfDist (0 : Fin (k + 1) → ℤ) u + 1 - c : ℕ) : ℝ) = (sourceR c u : ℝ) + 1 := by
  unfold sourceR
  rw [show linfDist (0 : Fin (k + 1) → ℤ) u + 1 - c = (linfDist 0 u - c) + 1 by omega]
  push_cast; ring

/-- The Appendix B coefficient depends only on dimension and the
uniform kernel and regime constants. -/
noncomputable def varCapstoneConstant (E : ℕ)
    (Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cbub Cρ Kreg : ℝ) : ℝ :=
  let Ct3 := max Ct Cc
  let CF3 := max CFr (CF * 4 ^ (E + 3))
  let C4 := 1 * (2 * (varTermThreeInnerConstant E Cg CF3 CF3 * Kreg))
  varTermOnePhiConstant E Cgo Ca Cb CF * varOuterRadialConstant (E + 7) +
    varTermOneInnerConstant E Cg Ca Cb Cc Cτ CF +
    (Cbub * varOuterRadialConstant (E + 7) + varTermTwoInnerConstant E Cg Cc Cτ (CF ^ 2)) +
    Cρ * (2 * (varTermThreeInnerConstant E Cg Ct3 CF3 * Kreg)) +
    (Cgo * CF ^ 2 * (3 * (2 * ((E + 7 : ℕ) : ℝ) * 3 ^ (E + 7 - 1) *
      ((((E + 7 - 8 : ℕ) : ℝ) + 1) / ((E + 7 - 8 : ℕ) : ℝ)))) + C4)

/-- Appendix B end-to-end variance bound on the literal geometry (`d = E+7 ≥ 9`). -/
theorem VARf_capstone_bound {E : ℕ} (hE : 2 ≤ E) (x : Fin (E + 7) → ℤ) {n r h c : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) (hc1 : 1 ≤ c) (h2c : 2 * c ≤ h) (h2h : 2 * h ≤ n)
    (hx : linfDist (0 : Fin (E + 7) → ℤ) x = n)
    (g F l : (Fin (E + 7) → ℤ) → ℝ) (tau : (Fin (E + 7) → ℤ) → (Fin (E + 7) → ℤ) → ℝ)
    (Var ρ : ℝ)
    {Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cbub Cρ Kreg : ℝ}
    (hCgo : 0 ≤ Cgo) (hCg : 0 ≤ Cg) (hCF : 0 ≤ CF) (hCFr : 0 ≤ CFr) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCt : 0 ≤ Ct) (hCbub : 0 ≤ Cbub)
    (hCρ : 0 ≤ Cρ) (hKreg : 0 ≤ Kreg) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
    -- lem.Ay1y2_diagrams
    (hdecomp : Var ≤
      (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
          ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
            g w * tau w u * tau u x * F w * F u +
        (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
          ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
            g u * tau u w * tau u x * F w ^ 2 +
        (n : ℝ) ^ 3 * (ρ * ∑ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
          g u * tau u x * F u) +
        ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), g w * F w ^ 2)
    -- nonnegativity
    (hg0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ g u)
    (hF0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ F u)
    (htau0 : ∀ a ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ b ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau a b)
    (htx0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau u x)
    (hl0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ l u)
    (hl : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), l u ≤ (linfDist x u : ℝ))
    -- eq.g_outer, eq.g_inner
    (hgo : ∀ w ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hgi : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    -- eq.F_pointwise, lem.F_RD
    (hF : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3))
    (hFRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)))
    -- two-point inputs
    (htwu : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 6))
    (htw_near : ∀ w ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), linfDist x u < (n - h) / 2 →
        tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (E + 6))
    (htw : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5))
    (htx : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (E + 7))
    (htx_far : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      (n - h) / 2 ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (E + 6))
    (htxRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 6) * (sParam c u : ℝ)))
    -- var_term_2 outer bubble input
    (hbubble : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        (n : ℝ) ^ 3 * ((∑ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
            g u * tau u w * tau u x) * F w ^ 2)
          ≤ Cbub * (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (E + 7 - 4)
              * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * (E + 7) - 8))))
    -- explicit regime hypothesis
    (hreg : (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (E + 1) ≤ Kreg / (r : ℝ) ^ (E + 1)) :
    let C := varCapstoneConstant E Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cbub Cρ Kreg
    0 ≤ C ∧ Var ≤ C / (r : ℝ) ^ (E + 7 - 6) := by
  -- geometry
  have hhn : h ≤ n := by omega
  have hsd := sourceAnnulus_sdiff_capOuter (k := E + 6) (n := n) (c := c) hhn
  have hosub := capOuter_subset (k := E + 6) (n := n) (h := h) (c := c)
  have hball := sourceAnnulus_subset_ball_x (k := E + 6) (c := c) hx
  have hball0 := sourceAnnulus_subset_ball_zero (k := E + 6) (n := n) (c := c)
  have hfar' := inner_far_from_x (k := E + 6) (h := h) (c := c) hx
  have hfar : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)) \ capOuter n h c,
      2 * ((n - h) / 2) ≤ linfDist x w := fun w hw => hfar' w (hsd ▸ hw)
  have hq : n ≤ 4 * ((n - h) / 2 + 1) := by omega
  have hmono := sourceAnnulus_mono (k := E + 6) (h := h) (n := n) (c := c) hhn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hinner_mem : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)) \ capOuter n h c,
      u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)) := fun u hu => hsd ▸ hu
  have hRD_sub : (sourceRD n c : Finset (Fin (E + 7) → ℤ)) ⊆ sourceAnnulus h c :=
    sourceRD_subset_sourceAnnulus h2c
  have hcompl_sub : (sourceAnnComplRD h c : Finset (Fin (E + 7) → ℤ)) ⊆ sourceAnnulus h c := by
    unfold sourceAnnComplRD; exact Finset.filter_subset _ _
  -- g in the `|u|+1-c` form on the inner region
  have hg_alt : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)) \ capOuter n h c,
      g u ≤ Cg / ((linfDist (0 : Fin (E + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2 := by
    intro u hu
    have hu' := hinner_mem u hu
    have hcu : c ≤ linfDist (0 : Fin (E + 7) → ℤ) u := by
      simp only [sourceAnnulus, Finset.mem_filter] at hu'; exact hu'.2
    rw [sourceR_cast_eq hcu]
    exact hgi u hu'
  -- flat F bound on the inner region
  have hFin : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF * 4 ^ (E + 3) / (n : ℝ) ^ (E + 3) := by
    intro u hu
    have hfu := hfar' u hu
    have hQpos : (0 : ℝ) < (((n - h) / 2 : ℕ) : ℝ) + 1 := by positivity
    have hnQ : (n : ℝ) ≤ 4 * ((((n - h) / 2 : ℕ) : ℝ) + 1) := by exact_mod_cast hq
    have hQM : (((n - h) / 2 : ℕ) : ℝ) + 1 ≤ max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ) :=
      le_max_of_le_right (by exact_mod_cast (show (n - h) / 2 + 1 ≤ linfDist x u + 1 by omega))
    calc F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3) := hF u (hmono hu)
      _ ≤ CF / ((((n - h) / 2 : ℕ) : ℝ) + 1) ^ (E + 3) :=
          div_le_div_of_nonneg_left hCF (by positivity) (pow_le_pow_left₀ hQpos.le hQM _)
      _ = CF * (1 / ((((n - h) / 2 : ℕ) : ℝ) + 1) ^ (E + 3)) := by ring
      _ ≤ CF * (4 ^ (E + 3) / (n : ℝ) ^ (E + 3)) :=
          mul_le_mul_of_nonneg_left (inv_pow_le_of_le_four_mul hn hQpos hnQ _) hCF
      _ = _ := by ring
  -- F² bound
  have hF2 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      F u ^ 2 ≤ CF ^ 2 / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (2 * E + 6) := by
    intro u hu
    calc F u ^ 2 ≤ (CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3)) ^ 2 :=
          pow_le_pow_left₀ (hF0 u hu) (hF u hu) 2
      _ = _ := by ring
  -- T1
  have h1 := var_term_1_full_bound x hn hr hrn hq (sourceAnnulus n c) (capOuter n h c) hosub hball
    hball0 hfar g F l tau hCg hCgo hCa hCb hCc hCτ hCF hg0 hF0 htau0 htx0 hl0 hl hgo hg_alt hF
    htwu (fun w hw u hu hk => htw_near w (hinner_mem w hw) u hu hk)
    (fun w hw u hu => htw w (Finset.mem_sdiff.mp hw).1 u hu) htx htx_far
  -- T2
  have h2 := var_term_2_source_bound x hn hr hrn hq (sourceAnnulus n c) (capOuter n h c) hosub hball
    hball0 hfar g F tau hCbub hCg hCc hCτ (sq_nonneg CF) hbubble
    (fun u hu => hg0 u (Finset.mem_sdiff.mp hu).1)
    (fun u hu => htx0 u (Finset.mem_sdiff.mp hu).1)
    (fun u hu w hw => htau0 u (Finset.mem_sdiff.mp hu).1 w hw) hg_alt
    (fun u hu => htx_far u (Finset.mem_sdiff.mp hu).1 (by have := hfar u hu; omega))
    (fun u hu w hw => htw u (Finset.mem_sdiff.mp hu).1 w hw) hF2
  -- shared constants for the inner-region (T3/T4) inputs
  set Ct3 : ℝ := max Ct Cc with hCt3
  set CF3 : ℝ := max CFr (CF * 4 ^ (E + 3)) with hCF3
  have hCt30 : 0 ≤ Ct3 := le_trans hCt (le_max_left _ _)
  have hCF30 : 0 ≤ CF3 := le_trans hCFr (le_max_left _ _)
  have htau1' : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Ct3 * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 6) * (sParam c u : ℝ)) :=
    fun u hu => (htxRD u hu).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity))
  have htau2' : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Ct3 / (n : ℝ) ^ (E + 6) :=
    fun u hu => (htx_far u (hmono (hcompl_sub hu))
      (by have := hfar' u (hcompl_sub hu); omega)).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  have hF1' : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF3 * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)) :=
    fun u hu => (hFRD u hu).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity))
  have hF2' : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF3 / (n : ℝ) ^ (E + 3) :=
    fun u hu => (hFin u (hcompl_sub hu)).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  -- T3
  have h3 := var_term_3_source_bound (e := E) hn hr hrn hc1 h2c hhn g (fun u => tau u x) F
    hCg hCt30 hCF30 hCρ hρ0 hρ hKreg
    (fun u hu => ⟨hg0 u (hmono hu), htx0 u (hmono hu), hF0 u (hmono hu)⟩) hgi htau1' hF1'
    htau2' hF2' hreg
  -- T4 inner region, via var_term_3_source with τ := F/n³ and ρ := 1
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  let C4 := 1 * (2 * (varTermThreeInnerConstant E Cg CF3 CF3 * Kreg))
  have hC4 := var_term_3_source_bound (e := E) hn hr hrn hc1 h2c hhn g
    (fun u => F u / (n : ℝ) ^ 3) F hCg hCF30 hCF30 zero_le_one zero_le_one le_rfl hKreg
    (fun u hu => ⟨hg0 u (hmono hu), div_nonneg (hF0 u (hmono hu)) hn3.le, hF0 u (hmono hu)⟩)
    hgi
    (fun u hu => by
      refine (div_le_div_of_nonneg_right (hF1' u hu) hn3.le).trans (le_of_eq ?_)
      rw [div_div]; congr 1; ring)
    hF1'
    (fun u hu => by
      refine (div_le_div_of_nonneg_right (hF2' u hu) hn3.le).trans (le_of_eq ?_)
      rw [div_div]; congr 1; ring)
    hF2' hreg
  have hinner4 : ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)) \ capOuter n h c,
      g w * F w ^ 2 ≤ C4 / (r : ℝ) ^ (E + 7 - 6) := by
    rw [hsd]
    refine le_trans (le_of_eq ?_) hC4
    rw [one_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    field_simp
  have hptwise : ∀ w ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      g w * F w ^ 2 ≤ Cgo * CF ^ 2 * ((n : ℝ) ^ 3)⁻¹ *
        (((linfDist x w + 1 : ℕ) : ℝ) /
          (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * (E + 7) - 8)) := by
    intro w hw
    rw [show 2 * (E + 7) - 8 = 2 * E + 6 by omega]
    have hgw : g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ) / (n : ℝ) ^ 3 := by
      rw [le_div_iff₀ hn3, mul_comm]; exact hgo w hw
    have hb : 0 ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ) / (n : ℝ) ^ 3 :=
      div_nonneg (mul_nonneg hCgo (by positivity)) hn3.le
    calc g w * F w ^ 2 ≤ (Cgo * ((linfDist x w + 1 : ℕ) : ℝ) / (n : ℝ) ^ 3) *
          (CF ^ 2 / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * E + 6)) :=
        mul_le_mul hgw (hF2 w (hosub hw)) (sq_nonneg _) hb
      _ = _ := by ring
  have h4bound := var_term_4_all_dimensions (d := E + 7) (by omega) x hr hrn
    (sourceAnnulus n c) (capOuter n h c) g F (Cgo * CF ^ 2) C4
    (mul_nonneg hCgo (sq_nonneg CF)) hosub (hosub.trans hball) hptwise hinner4
  have hRadial : 0 ≤ varOuterRadialConstant (E + 7) := by
    unfold varOuterRadialConstant
    positivity
  have hPhi : 0 ≤ varTermOnePhiConstant E Cgo Ca Cb CF := by
    unfold varTermOnePhiConstant
    positivity
  have hOne : 0 ≤ varTermOneInnerConstant E Cg Ca Cb Cc Cτ CF := by
    unfold varTermOneInnerConstant
    positivity
  have hTwo : 0 ≤ varTermTwoInnerConstant E Cg Cc Cτ (CF ^ 2) := by
    unfold varTermTwoInnerConstant
    positivity
  have hThree : 0 ≤ varTermThreeInnerConstant E Cg Ct3 CF3 := by
    unfold varTermThreeInnerConstant
    positivity
  have hFour : 0 ≤ varTermThreeInnerConstant E Cg CF3 CF3 := by
    unfold varTermThreeInnerConstant
    positivity
  change 0 ≤ varCapstoneConstant E Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cbub Cρ Kreg ∧ _
  constructor
  · unfold varCapstoneConstant
    change 0 ≤ varTermOnePhiConstant E Cgo Ca Cb CF * varOuterRadialConstant (E + 7) +
      varTermOneInnerConstant E Cg Ca Cb Cc Cτ CF +
      (Cbub * varOuterRadialConstant (E + 7) + varTermTwoInnerConstant E Cg Cc Cτ (CF ^ 2)) +
      Cρ * (2 * (varTermThreeInnerConstant E Cg Ct3 CF3 * Kreg)) +
      (Cgo * CF ^ 2 * (3 * (2 * ((E + 7 : ℕ) : ℝ) * 3 ^ (E + 7 - 1) *
        ((((E + 7 - 8 : ℕ) : ℝ) + 1) / ((E + 7 - 8 : ℕ) : ℝ)))) + C4)
    have hC40 : 0 ≤ C4 := by dsimp only [C4]; positivity
    positivity
  · refine hdecomp.trans ?_
    unfold varCapstoneConstant
    rw [add_div, add_div, add_div]
    exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4bound

/-- Existential form of the Appendix B capstone. -/
theorem VARf_capstone {E : ℕ} (hE : 2 ≤ E) (x : Fin (E + 7) → ℤ) {n r h c : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) (hc1 : 1 ≤ c) (h2c : 2 * c ≤ h) (h2h : 2 * h ≤ n)
    (hx : linfDist (0 : Fin (E + 7) → ℤ) x = n)
    (g F l : (Fin (E + 7) → ℤ) → ℝ) (tau : (Fin (E + 7) → ℤ) → (Fin (E + 7) → ℤ) → ℝ)
    (Var ρ : ℝ)
    {Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cbub Cρ Kreg : ℝ}
    (hCgo : 0 ≤ Cgo) (hCg : 0 ≤ Cg) (hCF : 0 ≤ CF) (hCFr : 0 ≤ CFr) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCt : 0 ≤ Ct) (hCbub : 0 ≤ Cbub)
    (hCρ : 0 ≤ Cρ) (hKreg : 0 ≤ Kreg) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
    -- lem.Ay1y2_diagrams
    (hdecomp : Var ≤
      (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
          ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
            g w * tau w u * tau u x * F w * F u +
        (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
          ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
            g u * tau u w * tau u x * F w ^ 2 +
        (n : ℝ) ^ 3 * (ρ * ∑ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
          g u * tau u x * F u) +
        ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), g w * F w ^ 2)
    -- nonnegativity
    (hg0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ g u)
    (hF0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ F u)
    (htau0 : ∀ a ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ b ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau a b)
    (htx0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau u x)
    (hl0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ l u)
    (hl : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), l u ≤ (linfDist x u : ℝ))
    -- eq.g_outer, eq.g_inner
    (hgo : ∀ w ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hgi : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    -- eq.F_pointwise, lem.F_RD
    (hF : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3))
    (hFRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)))
    -- two-point inputs
    (htwu : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 6))
    (htw_near : ∀ w ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), linfDist x u < (n - h) / 2 →
        tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (E + 6))
    (htw : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5))
    (htx : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (E + 7))
    (htx_far : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      (n - h) / 2 ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (E + 6))
    (htxRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 6) * (sParam c u : ℝ)))
    -- var_term_2 outer bubble input
    (hbubble : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        (n : ℝ) ^ 3 * ((∑ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
            g u * tau u w * tau u x) * F w ^ 2)
          ≤ Cbub * (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (E + 7 - 4)
              * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * (E + 7) - 8))))
    -- explicit regime hypothesis
    (hreg : (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (E + 1) ≤ Kreg / (r : ℝ) ^ (E + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ Var ≤ C / (r : ℝ) ^ (E + 7 - 6) := by
  obtain ⟨hC, hVar⟩ := VARf_capstone_bound hE x hn hr hrn hc1 h2c h2h hx g F l tau Var ρ
    hCgo hCg hCF hCFr hCa hCb hCc hCτ hCt hCbub hCρ hKreg hρ0 hρ hdecomp hg0 hF0
    htau0 htx0 hl0 hl hgo hgi hF hFRD htwu htw_near htw htx htx_far htxRD hbubble hreg
  exact ⟨_, hC, hVar⟩

end NearCritical.AppendixVariance
