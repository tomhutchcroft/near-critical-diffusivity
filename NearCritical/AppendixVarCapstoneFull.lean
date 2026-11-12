module

public import NearCritical.AppendixVarCapstone
public import NearCritical.AppendixSharpBubble

/-! Appendix B end-to-end, WITHOUT the `hbubble` hypothesis.

`capstone_hbubble` derives var_term_2's outer input (the source's Case 1 of prop.var_term_2) from
pointwise inputs `VARf_capstone` already takes:
* `n³g(u) ≤ C_go(|x-u|+1)` on `outer` [eq.g_outer];
* `τ(u,x) ≤ C_b(1+l_u)(|x-u|+1)^{-d}` with `l_u ≤ |x-u|` [lem.box_twopoint_twosided], giving
  `≤ C_b(|x-u|+1)^{1-d}`;
* `τ(u,w) ≤ C_τ(|u-w|+1)^{2-d}` [full-space two-point];
* `F(w)² ≤ C_F² max(r,|x-w|+1)^{8-2d}` [eq.F_pointwise].
It then applies the K-uniform `sharp_bubble` over `outer ⊆ ball(w,4n)`.

`VARf_capstone_full` is `VARf_capstone` with `hbubble` discharged. Its remaining explicit
hypotheses are `hdecomp`, the pointwise (A)/Appendix-A inputs, `ρ ≤ Cρ`, and the regime
hypothesis. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Uniform coefficient of the outer bubble estimate. -/
noncomputable def varBubbleConstant (E : ℕ) (Cgo CF Cb Cτ : ℝ) : ℝ :=
  Cgo * Cb * Cτ * (2 * ((E + 7 : ℕ) : ℝ) * 3 ^ (E + 6) *
    (2 * 2 ^ (E + 5) + 3 ^ (E + 5) * (((((E + 3 : ℕ) : ℝ) + 1) /
      ((E + 3 : ℕ) : ℝ)) * 2 ^ (E + 3)))) * CF ^ 2

theorem capstone_hbubble {E : ℕ} (x : Fin (E + 7) → ℤ) {n r h c : ℕ}
    (hx : linfDist (0 : Fin (E + 7) → ℤ) x = n)
    (g F l : (Fin (E + 7) → ℤ) → ℝ) (tau : (Fin (E + 7) → ℤ) → (Fin (E + 7) → ℤ) → ℝ)
    {Cgo CF Cb Cτ : ℝ} (hCgo : 0 ≤ Cgo) (hCF : 0 ≤ CF) (hCb : 0 ≤ Cb) (hCτ : 0 ≤ Cτ)
    (hn : 1 ≤ n)
    (hg0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ g u)
    (hF0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ F u)
    (htau0 : ∀ a ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ b ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau a b)
    (htx0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau u x)
    (hl0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ l u)
    (hl : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), l u ≤ (linfDist x u : ℝ))
    (hgo : ∀ w ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hF : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3))
    (htw : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5))
    (htx : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (E + 7)) :
    ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        (n : ℝ) ^ 3 * ((∑ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
            g u * tau u w * tau u x) * F w ^ 2)
          ≤ (Cgo * Cb * Cτ * (2 * ((E + 7 : ℕ) : ℝ) * 3 ^ (E + 6) *
              (2 * 2 ^ (E + 5) + 3 ^ (E + 5) * (((((E + 3 : ℕ) : ℝ) + 1) /
                ((E + 3 : ℕ) : ℝ)) * 2 ^ (E + 3)))) * CF ^ 2) *
            (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (E + 7 - 4)
              * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * (E + 7) - 8))) := by
  intro w hw
  rw [show E + 7 - 4 = E + 3 by omega, show 2 * (E + 7) - 8 = 2 * E + 6 by omega]
  have hosub := capOuter_subset (k := E + 6) (n := n) (h := h) (c := c)
  have hball := sourceAnnulus_subset_ball_x (k := E + 6) (c := c) hx
  set Cb0 : ℝ := 2 * ((E + 7 : ℕ) : ℝ) * 3 ^ (E + 6) *
    (2 * 2 ^ (E + 5) + 3 ^ (E + 5) * (((((E + 3 : ℕ) : ℝ) + 1) /
      ((E + 3 : ℕ) : ℝ)) * 2 ^ (E + 3))) with hCb0
  have hCb00 : 0 ≤ Cb0 := by rw [hCb0]; positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- per-u bound
  have hpt : ∀ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      (n : ℝ) ^ 3 * (g u * tau u w * tau u x) ≤ Cgo * Cb * Cτ *
        ((1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (E + 5)) *
          (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5))) := by
    intro u hu
    have huA := hosub hu
    set k1 : ℝ := ((linfDist x u + 1 : ℕ) : ℝ) with hk1
    have hk1pos : 0 < k1 := by rw [hk1]; positivity
    have hl1 : 0 ≤ 1 + l u := by linarith [hl0 u huA]
    have hlk : 1 + l u ≤ k1 := by rw [hk1]; push_cast; linarith [hl u huA]
    have htx' : tau u x ≤ Cb / k1 ^ (E + 6) := by
      refine (htx u huA).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc Cb * (1 + l u) * k1 ^ (E + 6) ≤ Cb * k1 * k1 ^ (E + 6) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlk hCb) (by positivity)
        _ = Cb * k1 ^ (E + 7) := by ring
    have htw' : tau u w ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5) := by
      rw [linfDist_comm w u]; exact htw u huA w hw
    have hg' : (n : ℝ) ^ 3 * g u ≤ Cgo * k1 := hgo u hu
    have hng0 : 0 ≤ (n : ℝ) ^ 3 * g u := mul_nonneg (by positivity) (hg0 u huA)
    calc (n : ℝ) ^ 3 * (g u * tau u w * tau u x)
        = ((n : ℝ) ^ 3 * g u) * tau u w * tau u x := by ring
      _ ≤ (Cgo * k1) * (Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5)) * (Cb / k1 ^ (E + 6)) :=
          mul_le_mul (mul_le_mul hg' htw' (htau0 u huA w hw)
              (mul_nonneg hCgo hk1pos.le)) htx' (htx0 u huA)
            (mul_nonneg (mul_nonneg hCgo hk1pos.le) (div_nonneg hCτ (by positivity)))
      _ = _ := by have := hk1pos.ne'; field_simp <;> ring
  have hsubw : (capOuter n h c : Finset (Fin (E + 7) → ℤ)) ⊆
      linfBall w ((4 * n : ℕ) : ℤ) := by
    intro u hu
    have hxu := (mem_linfBall_iff_dist x u (by positivity)).mp (hball (hosub hu))
    have hxw := (mem_linfBall_iff_dist x w (by positivity)).mp (hball hw)
    rw [mem_linfBall_iff_dist w u (by positivity)]
    have htri := linfDist_triangle w x u
    rw [linfDist_comm w x] at htri
    simp only [Int.toNat_natCast] at hxu hxw ⊢
    omega
  have hbub := sharp_bubble x w (4 * n) (capOuter n h c) hsubw
  rw [← hCb0] at hbub
  have hsum : (n : ℝ) ^ 3 * ∑ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      g u * tau u w * tau u x ≤ Cgo * Cb * Cτ * (Cb0 / ((linfDist x w + 1 : ℕ) : ℝ) ^ (E + 3)) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)), Cgo * Cb * Cτ *
          ((1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (E + 5)) *
            (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5))) := Finset.sum_le_sum hpt
      _ = Cgo * Cb * Cτ * ∑ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
          ((1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (E + 5)) *
            (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5))) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbub
          (mul_nonneg (mul_nonneg hCgo hCb) hCτ)
  have hF2 : F w ^ 2 ≤ CF ^ 2 / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * E + 6) := by
    calc F w ^ 2 ≤ (CF / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (E + 3)) ^ 2 :=
          pow_le_pow_left₀ (hF0 w hw) (hF w hw) 2
      _ = _ := by ring
  have hmpos : (0 : ℝ) < ((linfDist x w + 1 : ℕ) : ℝ) := by positivity
  have hMpos : (0 : ℝ) < max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le hmpos (le_max_right _ _)
  calc (n : ℝ) ^ 3 * ((∑ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
          g u * tau u w * tau u x) * F w ^ 2)
      = ((n : ℝ) ^ 3 * ∑ u ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
          g u * tau u w * tau u x) * F w ^ 2 := by ring
    _ ≤ (Cgo * Cb * Cτ * (Cb0 / ((linfDist x w + 1 : ℕ) : ℝ) ^ (E + 3))) *
          (CF ^ 2 / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * E + 6)) :=
        mul_le_mul hsum hF2 (sq_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg hCgo hCb) hCτ) (by positivity))
    _ = _ := by have := hmpos.ne'; have := hMpos.ne'; field_simp <;> ring

/-- Appendix B end-to-end variance bound, with var_term_2's bubble input discharged. -/
theorem VARf_capstone_full_bound {E : ℕ} (hE : 2 ≤ E) (x : Fin (E + 7) → ℤ) {n r h c : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) (hc1 : 1 ≤ c) (h2c : 2 * c ≤ h) (h2h : 2 * h ≤ n)
    (hx : linfDist (0 : Fin (E + 7) → ℤ) x = n)
    (g F l : (Fin (E + 7) → ℤ) → ℝ) (tau : (Fin (E + 7) → ℤ) → (Fin (E + 7) → ℤ) → ℝ)
    (Var ρ : ℝ)
    {Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cρ Kreg : ℝ}
    (hCgo : 0 ≤ Cgo) (hCg : 0 ≤ Cg) (hCF : 0 ≤ CF) (hCFr : 0 ≤ CFr) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCt : 0 ≤ Ct)
    (hCρ : 0 ≤ Cρ) (hKreg : 0 ≤ Kreg) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
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
    (hg0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ g u)
    (hF0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ F u)
    (htau0 : ∀ a ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ b ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau a b)
    (htx0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau u x)
    (hl0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ l u)
    (hl : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), l u ≤ (linfDist x u : ℝ))
    (hgo : ∀ w ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hgi : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    (hF : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3))
    (hFRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)))
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
    (hreg : (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (E + 1) ≤ Kreg / (r : ℝ) ^ (E + 1)) :
    let C := varCapstoneConstant E Cgo Cg CF CFr Ca Cb Cc Cτ Ct
      (varBubbleConstant E Cgo CF Cb Cτ) Cρ Kreg
    0 ≤ C ∧ Var ≤ C / (r : ℝ) ^ (E + 7 - 6) := by
  have hbub := capstone_hbubble x hx g F l tau hCgo hCF hCb hCτ hn hg0 hF0 htau0 htx0 hl0 hl
    hgo hF htw htx
  have hCbub : 0 ≤ varBubbleConstant E Cgo CF Cb Cτ := by
    unfold varBubbleConstant
    positivity
  exact VARf_capstone_bound hE x hn hr hrn hc1 h2c h2h hx g F l tau Var ρ hCgo hCg hCF hCFr hCa hCb
    hCc hCτ hCt hCbub hCρ hKreg hρ0 hρ hdecomp hg0 hF0 htau0 htx0 hl0 hl hgo hgi hF hFRD htwu
    htw_near htw htx htx_far htxRD hbub hreg

/-- Existential form with the outer bubble hypothesis discharged. -/
theorem VARf_capstone_full {E : ℕ} (hE : 2 ≤ E) (x : Fin (E + 7) → ℤ) {n r h c : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) (hc1 : 1 ≤ c) (h2c : 2 * c ≤ h) (h2h : 2 * h ≤ n)
    (hx : linfDist (0 : Fin (E + 7) → ℤ) x = n)
    (g F l : (Fin (E + 7) → ℤ) → ℝ) (tau : (Fin (E + 7) → ℤ) → (Fin (E + 7) → ℤ) → ℝ)
    (Var ρ : ℝ)
    {Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cρ Kreg : ℝ}
    (hCgo : 0 ≤ Cgo) (hCg : 0 ≤ Cg) (hCF : 0 ≤ CF) (hCFr : 0 ≤ CFr) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCt : 0 ≤ Ct)
    (hCρ : 0 ≤ Cρ) (hKreg : 0 ≤ Kreg) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
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
    (hg0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ g u)
    (hF0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ F u)
    (htau0 : ∀ a ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ b ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau a b)
    (htx0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau u x)
    (hl0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ l u)
    (hl : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), l u ≤ (linfDist x u : ℝ))
    (hgo : ∀ w ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hgi : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    (hF : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3))
    (hFRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)))
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
    (hreg : (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (E + 1) ≤ Kreg / (r : ℝ) ^ (E + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ Var ≤ C / (r : ℝ) ^ (E + 7 - 6) := by
  obtain ⟨hC, hVar⟩ := VARf_capstone_full_bound hE x hn hr hrn hc1 h2c h2h hx g F l tau Var ρ
    hCgo hCg hCF hCFr hCa hCb hCc hCτ hCt hCρ hKreg hρ0 hρ hdecomp hg0 hF0 htau0 htx0
    hl0 hl hgo hgi hF hFRD htwu htw_near htw htx htx_far htxRD hreg
  exact ⟨_, hC, hVar⟩

end NearCritical.AppendixVariance
