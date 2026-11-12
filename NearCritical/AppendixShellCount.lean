module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic
public import NearCritical.AppendixVarianceSum

/-! Appendix B lattice shell count.

Foundation: the ℓ∞ ball on `Fin d → ℤ` (= `Vertex d`), as a `piFinset` of coordinate
intervals, has cardinality `(2k+1)^d`. The shell `{u : |u - c|_∞ = k}` is then
contained in `ball k \ ball (k-1)`, giving `#shell ≤ (2k+1)^d - (2k-1)^d`.
 -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- The ℓ∞ ball of radius `k` about `c` on `Fin d → ℤ`, as a finite set. -/
def linfBall {d : ℕ} (c : Fin d → ℤ) (k : ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (c i - k) (c i + k))

/-- The ℓ∞ distance on `Fin d → ℤ`, as a natural number. -/
def linfDist {d : ℕ} (x u : Fin d → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (x i - u i).natAbs)

/-- Membership in the ℓ∞ ball is the coordinatewise `|u i - c i| ≤ k`. -/
theorem mem_linfBall {d : ℕ} (c : Fin d → ℤ) (k : ℤ) (u : Fin d → ℤ) :
    u ∈ linfBall c k ↔ ∀ i, |u i - c i| ≤ k := by
  simp only [linfBall, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor <;> intro h i <;>
    exact ⟨by linarith [(h i).1, (h i).2], by linarith [(h i).1, (h i).2]⟩

/-- The ℓ∞ ball is exactly the set of points within ℓ∞ distance `k.toNat`. -/
theorem mem_linfBall_iff_dist {d : ℕ} (x u : Fin d → ℤ) {k : ℤ} (hk : 0 ≤ k) :
    u ∈ linfBall x k ↔ linfDist x u ≤ k.toNat := by
  rw [linfBall, Fintype.mem_piFinset, linfDist, Finset.sup_le_iff]
  constructor
  · intro h i _
    have := h i; rw [Finset.mem_Icc] at this; omega
  · intro h i
    rw [Finset.mem_Icc]
    have := h i (Finset.mem_univ i); omega

/-- Cardinality of the ℓ∞ ball: `(2k+1)^d`. -/
theorem linfBall_card {d : ℕ} (c : Fin d → ℤ) (k : ℤ) :
    (linfBall c k).card = (2 * k + 1).toNat ^ d := by
  have hfac : ∀ i : Fin d, (Finset.Icc (c i - k) (c i + k)).card = (2 * k + 1).toNat := by
    intro i; rw [Int.card_Icc]; congr 1; ring
  rw [linfBall, Fintype.card_piFinset, Finset.prod_congr rfl (fun i _ => hfac i),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The ℓ∞ sphere `{u : |u - c|_∞ = k}` equals `ball k \ ball (k-1)`, so its
cardinality is `(2k+1)^d - (2k-1)^d`. -/
theorem linfSphere_card {d : ℕ} (c : Fin d → ℤ) {k : ℤ} (_hk : 1 ≤ k) :
    (linfBall c k \ linfBall c (k - 1)).card
      = (2 * k + 1).toNat ^ d - (2 * (k - 1) + 1).toNat ^ d := by
  have hsub : linfBall c (k - 1) ⊆ linfBall c k := by
    intro u hu
    rw [mem_linfBall] at hu ⊢
    exact fun i => le_trans (hu i) (by linarith)
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, linfBall_card, linfBall_card]

/-- Elementary power-difference bound `a^{d+1} - b^{d+1} ≤ (d+1)·a^d·(a-b)` for
`0 ≤ b ≤ a`, by induction on `d`. Turns the exact shell count into the
`≲ (1+k)^{d-1}` form used by the variance sums. -/
theorem pow_succ_sub_pow_succ_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (d : ℕ) :
    a ^ (d + 1) - b ^ (d + 1) ≤ ((d : ℝ) + 1) * a ^ d * (a - b) := by
  have ha : 0 ≤ a := hb.trans hab
  induction d with
  | zero => simp
  | succ d ih =>
    have hba : 0 ≤ a - b := by linarith
    have hbd : b ^ (d + 1) ≤ a ^ (d + 1) := pow_le_pow_left₀ hb hab (d + 1)
    calc a ^ (d + 2) - b ^ (d + 2)
        = a * (a ^ (d + 1) - b ^ (d + 1)) + (a - b) * b ^ (d + 1) := by ring
      _ ≤ a * (((d : ℝ) + 1) * a ^ d * (a - b)) + (a - b) * a ^ (d + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left ih ha) (mul_le_mul_of_nonneg_left hbd hba)
      _ = ((d : ℝ) + 1 + 1) * a ^ (d + 1) * (a - b) := by ring
      _ = (((d + 1 : ℕ) : ℝ) + 1) * a ^ (d + 1) * (a - b) := by push_cast; ring

/-- Radial grouping: a sum of a distance-only kernel over the ℓ∞ ball equals the
sum over distance-shells weighted by the shell cardinalities. The bridge from a
lattice sum to the one-dimensional `weighted_powerlaw_sum_le`. -/
theorem radial_sum_eq {d : ℕ} (x : Fin d → ℤ) (K : ℕ) (f : ℕ → ℝ) :
    ∑ u ∈ linfBall x (K : ℤ), f (linfDist x u)
      = ∑ j ∈ Finset.range (K + 1),
          (((linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)).card : ℝ) * f j := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun u => linfDist x u) (t := Finset.range (K + 1))
    (fun u hu => Finset.mem_range.mpr (by
      have h := (mem_linfBall_iff_dist x u (by positivity)).mp hu
      simp only [Int.toNat_natCast] at h; omega))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2]),
    Finset.sum_const, nsmul_eq_mul]

/-- For `1 ≤ j ≤ K`, the radius-`j` distance fiber inside the ball of radius `K` is
exactly the shell `ball j \ ball (j-1)`. This is the wiring that lets `radial_sum_eq`'s
fiber cardinalities be replaced by the exact `linfSphere_card`. -/
theorem linfShell_eq_filter {d : ℕ} (x : Fin d → ℤ) {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    (linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)
      = linfBall x (j : ℤ) \ linfBall x ((j : ℤ) - 1) := by
  ext u
  rw [Finset.mem_filter, Finset.mem_sdiff,
    mem_linfBall_iff_dist x u (show (0 : ℤ) ≤ (K : ℤ) by positivity),
    mem_linfBall_iff_dist x u (show (0 : ℤ) ≤ (j : ℤ) by positivity),
    mem_linfBall_iff_dist x u (show (0 : ℤ) ≤ (j : ℤ) - 1 by omega)]
  simp only [Int.toNat_natCast]
  omega

/-- The exact radius-`j` distance-fiber cardinality inside the ball of radius `K`
(for `1 ≤ j ≤ K`): the ℓ∞ shell count `(2j+1)^d - (2j-1)^d`. -/
theorem fiber_card_eq {d : ℕ} (x : Fin d → ℤ) {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    ((linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)).card
      = (2 * (j : ℤ) + 1).toNat ^ d - (2 * ((j : ℤ) - 1) + 1).toNat ^ d := by
  rw [linfShell_eq_filter x hj hjK,
    linfSphere_card x (show (1 : ℤ) ≤ (j : ℤ) by exact_mod_cast hj)]

/-- The exact ℓ∞ shell count is dominated by the polynomial `2d·(2j+1)^{d-1}` (for
`d ≥ 1`, `j ≥ 1`). This turns `fiber_card_eq` into the `≲ (1+k)^{d-1}` growth the
power-law variance sums consume. Final piece of component B. -/
theorem shell_count_real_le {d : ℕ} (hd : 1 ≤ d) {j : ℕ} (hj : 1 ≤ j) :
    (((2 * (j : ℤ) + 1).toNat ^ d - (2 * ((j : ℤ) - 1) + 1).toNat ^ d : ℕ) : ℝ)
      ≤ 2 * (d : ℝ) * (2 * (j : ℝ) + 1) ^ (d - 1) := by
  obtain ⟨D, rfl⟩ : ∃ D, d = D + 1 := ⟨d - 1, by omega⟩
  have hA : (2 * (j : ℤ) + 1).toNat = 2 * j + 1 := by omega
  have hB : (2 * ((j : ℤ) - 1) + 1).toNat = 2 * j - 1 := by omega
  have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  rw [hA, hB, Nat.cast_sub (Nat.pow_le_pow_left (by omega) (D + 1)),
    Nat.cast_pow, Nat.cast_pow,
    show ((2 * j + 1 : ℕ) : ℝ) = 2 * (j : ℝ) + 1 by push_cast; ring,
    show ((2 * j - 1 : ℕ) : ℝ) = 2 * (j : ℝ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]; push_cast; ring,
    Nat.add_sub_cancel]
  have key := pow_succ_sub_pow_succ_le (show (0 : ℝ) ≤ 2 * (j : ℝ) - 1 by linarith)
    (show 2 * (j : ℝ) - 1 ≤ 2 * (j : ℝ) + 1 by linarith) D
  rw [show (2 * (j : ℝ) + 1) - (2 * (j : ℝ) - 1) = 2 by ring] at key
  refine le_trans key (le_of_eq ?_)
  push_cast; ring

/-- Uniform (all `j ≤ K`, including the center `j = 0`) real bound on the
distance-fiber cardinality: `#{u ∈ ball K : linfDist x u = j} ≤ 2d·(2j+1)^{d-1}`. -/
theorem fiber_card_real_le {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℤ) {K j : ℕ} (hjK : j ≤ K) :
    (((linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)).card : ℝ)
      ≤ 2 * (d : ℝ) * (2 * (j : ℝ) + 1) ^ (d - 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have hcard : ((linfBall x (K : ℤ)).filter (fun u => linfDist x u = 0)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      have hax : a = x := by
        funext i
        have h : (x i - a i).natAbs ≤ Finset.univ.sup (fun i => (x i - a i).natAbs) :=
          Finset.le_sup (f := fun i => (x i - a i).natAbs) (Finset.mem_univ i)
        have hz : Finset.univ.sup (fun i => (x i - a i).natAbs) = 0 := ha.2
        rw [hz] at h; omega
      have hbx : b = x := by
        funext i
        have h : (x i - b i).natAbs ≤ Finset.univ.sup (fun i => (x i - b i).natAbs) :=
          Finset.le_sup (f := fun i => (x i - b i).natAbs) (Finset.mem_univ i)
        have hz : Finset.univ.sup (fun i => (x i - b i).natAbs) = 0 := hb.2
        rw [hz] at h; omega
      rw [hax, hbx]
    have h1 : (((linfBall x (K : ℤ)).filter (fun u => linfDist x u = 0)).card : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    refine le_trans h1 ?_
    have hone : (2 * ((0 : ℕ) : ℝ) + 1) ^ (d - 1) = 1 := by norm_num
    rw [hone, mul_one]
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  · rw [fiber_card_eq x hj1 hjK]
    exact shell_count_real_le hd hj1

/-- CAPSTONE (general Appendix-B radial kernel estimate): a lattice sum over the ℓ∞ ball
of the weighted radial power-law kernel
`(|x-u|_∞+1)^a · max(r, |x-u|_∞+1)^{-((a+(d-1))+(t+1))}` is bounded by
`2d·3^{d-1} · (t+1)/(t·r^t)`, i.e. it scales like `r^{-t}`. The extra numerator weight
`(|x-u|_∞+1)^a` is exactly what the `var_term` kernels pick up from the `g`-factor
`g(w) ≲ (1+l_w) n^{-3}` in the outer region. This assembles the full Appendix-B engine:
radial grouping (`radial_sum_eq`) + the shell-count bound (`fiber_card_real_le`) + the
one-dimensional weighted power-law sum (`weighted_powerlaw_sum_le`, with `c = a+(d-1)`).
It is the reusable abstract core each `prop.var_term_*` reduces to once its specific kernel
is bounded pointwise by this radial form. -/
theorem radial_weighted_power_sum_le {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℤ) (a : ℕ) {t r : ℕ}
    (ht : 1 ≤ t) (hr : 1 ≤ r) (K : ℕ) :
    ∑ u ∈ linfBall x (K : ℤ),
        ((linfDist x u + 1 : ℕ) : ℝ) ^ a
          / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1))
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t)) := by
  have hstep : ∑ j ∈ Finset.range (K + 1),
      (((linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)).card : ℝ)
        * (((j + 1 : ℕ) : ℝ) ^ a / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1)))
      ≤ ∑ j ∈ Finset.range (K + 1),
          2 * (d : ℝ) * 3 ^ (d - 1)
            * (((j + 1 : ℕ) : ℝ) ^ (a + (d - 1))
                / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1))) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjK : j ≤ K := by have := Finset.mem_range.mp hj; omega
    have hfib := fiber_card_real_le hd x hjK
    have hpow : (2 * (j : ℝ) + 1) ^ (d - 1) ≤ 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      push_cast; linarith
    have hchain : (((linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)).card : ℝ)
        ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) :=
      hfib.trans (by
        calc 2 * (d : ℝ) * (2 * (j : ℝ) + 1) ^ (d - 1)
            ≤ 2 * (d : ℝ) * (3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) := by ring)
    have hsplit : ((j + 1 : ℕ) : ℝ) ^ (a + (d - 1))
        = ((j + 1 : ℕ) : ℝ) ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ a := by
      rw [← pow_add, Nat.add_comm a (d - 1)]
    calc (((linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)).card : ℝ)
          * (((j + 1 : ℕ) : ℝ) ^ a / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1)))
        ≤ (2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1))
            * (((j + 1 : ℕ) : ℝ) ^ a / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1))) :=
          mul_le_mul_of_nonneg_right hchain (by positivity)
      _ = 2 * (d : ℝ) * 3 ^ (d - 1)
            * (((j + 1 : ℕ) : ℝ) ^ (a + (d - 1))
                / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1))) := by
          rw [hsplit]; ring
  calc ∑ u ∈ linfBall x (K : ℤ),
          ((linfDist x u + 1 : ℕ) : ℝ) ^ a
            / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1))
      = ∑ j ∈ Finset.range (K + 1),
          (((linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)).card : ℝ)
            * (((j + 1 : ℕ) : ℝ) ^ a / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1))) :=
        radial_sum_eq x K
          (fun j => ((j + 1 : ℕ) : ℝ) ^ a / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1)))
    _ ≤ ∑ j ∈ Finset.range (K + 1),
          2 * (d : ℝ) * 3 ^ (d - 1)
            * (((j + 1 : ℕ) : ℝ) ^ (a + (d - 1))
                / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1))) :=
        hstep
    _ = 2 * (d : ℝ) * 3 ^ (d - 1)
          * ∑ j ∈ Finset.range (K + 1),
              ((j + 1 : ℕ) : ℝ) ^ (a + (d - 1))
                / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ ((a + (d - 1)) + (t + 1)) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t)) :=
        mul_le_mul_of_nonneg_left (weighted_powerlaw_sum_le ht hr (K + 1)) (by positivity)

/-- The unweighted (`a = 0`) case of `radial_weighted_power_sum_le`: the pure radial
power-law kernel `max(r, |x-u|_∞+1)^{-((d-1)+(t+1))}` summed over the ℓ∞ ball scales as
`r^{-t}`. -/
theorem radial_power_sum_le {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℤ) {t r : ℕ}
    (ht : 1 ≤ t) (hr : 1 ≤ r) (K : ℕ) :
    ∑ u ∈ linfBall x (K : ℤ),
        (1 : ℝ) / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ ((d - 1) + (t + 1))
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t)) := by
  simpa using radial_weighted_power_sum_le hd x 0 ht hr K

/-- General radial shell bound: a lattice sum over the ℓ∞ ball of any nonnegative
distance-only kernel `f` is dominated by the one-dimensional sum weighted by the
polynomial shell bound `2d·3^{d-1}·(j+1)^{d-1}`. The un-specialized form of the radial
estimates — `radial_weighted_power_sum_le` is the special case `f j = (j+1)^a/max(r,j+1)^β`. -/
theorem radial_sum_shell_bound {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℤ) (K : ℕ)
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ u ∈ linfBall x (K : ℤ), f (linfDist x u)
      ≤ ∑ j ∈ Finset.range (K + 1),
          2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) * f j := by
  rw [radial_sum_eq x K f]
  apply Finset.sum_le_sum
  intro j hj
  have hjK : j ≤ K := by have := Finset.mem_range.mp hj; omega
  have h1 : (((linfBall x (K : ℤ)).filter (fun u => linfDist x u = j)).card : ℝ)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) := by
    refine (fiber_card_real_le hd x hjK).trans ?_
    have hpow : (2 * (j : ℝ) + 1) ^ (d - 1) ≤ 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) := by
      rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); push_cast; linarith
    calc 2 * (d : ℝ) * (2 * (j : ℝ) + 1) ^ (d - 1)
        ≤ 2 * (d : ℝ) * (3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) := by ring
  exact mul_le_mul_of_nonneg_right h1 (hf j)

/-- Radial estimate for kernels with a negative `(dist+1)` weight: for `p ≤ d-1`,
`∑_{w∈ball K} 1/((|x-w|_∞+1)^p · max(r,|x-w|_∞+1)^{((d-1)-p)+(t+1)}) ≤ 2d·3^{d-1}·(t+1)/(t·r^t)`.
The `(dist+1)^{-p}` partially cancels the shell count, so the effective grouped exponent is
`(d-1)-p`, which can be smaller than `d-1`. This is the form the `var_term_1`/`var_term_2`
outer-region contributions take (e.g. `p = d-4` gives the grouped `(1+m)^3` weight). -/
theorem radial_div_sum_le {d : ℕ} (hd : 1 ≤ d) (x : Fin d → ℤ) (p : ℕ) (hp : p ≤ d - 1)
    {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) (K : ℕ) :
    ∑ w ∈ linfBall x (K : ℤ),
        1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ p
              * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (((d - 1) - p) + (t + 1)))
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t)) := by
  refine le_trans (radial_sum_shell_bound hd x K
    (fun j => 1 / (((j + 1 : ℕ) : ℝ) ^ p
        * (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (((d - 1) - p) + (t + 1))))
    (fun j => by positivity)) ?_
  have hkey : ∀ j ∈ Finset.range (K + 1),
      2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (((j + 1 : ℕ) : ℝ) ^ p
              * (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (((d - 1) - p) + (t + 1))))
      = 2 * (d : ℝ) * 3 ^ (d - 1)
          * (((j + 1 : ℕ) : ℝ) ^ ((d - 1) - p)
              / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (((d - 1) - p) + (t + 1))) := by
    intro j _
    have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hmax : (0 : ℝ) < max (r : ℝ) ((j + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le (by exact_mod_cast hr) (le_max_left _ _)
    have hsplit : ((j + 1 : ℕ) : ℝ) ^ (d - 1)
        = ((j + 1 : ℕ) : ℝ) ^ ((d - 1) - p) * ((j + 1 : ℕ) : ℝ) ^ p := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    field_simp
  calc ∑ j ∈ Finset.range (K + 1),
        2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (((j + 1 : ℕ) : ℝ) ^ p
              * (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (((d - 1) - p) + (t + 1))))
      = ∑ j ∈ Finset.range (K + 1),
          2 * (d : ℝ) * 3 ^ (d - 1)
            * (((j + 1 : ℕ) : ℝ) ^ ((d - 1) - p)
                / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (((d - 1) - p) + (t + 1))) :=
        Finset.sum_congr rfl hkey
    _ = 2 * (d : ℝ) * 3 ^ (d - 1)
          * ∑ j ∈ Finset.range (K + 1),
              ((j + 1 : ℕ) : ℝ) ^ ((d - 1) - p)
                / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (((d - 1) - p) + (t + 1)) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t)) :=
        mul_le_mul_of_nonneg_left (weighted_powerlaw_sum_le ht hr (K + 1)) (by positivity)

/-- The `p = 2` series tail is bounded: `∑_{m<N} 1/(m+1)^2 ≤ 2` (reusing the verified
`powerlaw_tail_le` with `t = r = 1`, plus the `m = 0` term). The convergent-tail ingredient
behind the Appendix-B counting estimates `eq.inner_sum` / `eq.RD_count`. -/
theorem inv_sq_sum_le_two (N : ℕ) :
    ∑ m ∈ Finset.range N, (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
  cases N with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ']
    have htail : ∑ i ∈ Finset.range M, (1 : ℝ) / ((i + 1 + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
      have h := powerlaw_tail_le (t := 1) (le_refl 1) (r := 1) (le_refl 1) M
      have heq : ∀ k ∈ Finset.range M,
          (1 : ℝ) / ((1 + 1 + k : ℕ) : ℝ) ^ (1 + 1) = (1 : ℝ) / ((k + 1 + 1 : ℕ) : ℝ) ^ 2 := by
        intro k _; push_cast; ring
      rw [Finset.sum_congr rfl heq] at h
      simpa using h
    have h0 : (1 : ℝ) / (((0 : ℕ) + 1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    rw [h0]; linarith

/-- Appendix-B inner counting estimate (`eq.inner_sum`), ℓ∞ form: the radial sum of the
shifted inverse-square weight `1/(|w|_∞ + 1 - c)^2` over the cube of radius `N` is
`≲ N^{d-1}`. This is `eq.inner_sum` with `c = c₁n`, `|w|_∞ = ρ`, `r_w = ρ - c₁n`: it combines
the verified shell count (`radial_sum_shell_bound`) with the convergent tail
(`inv_sq_sum_le_two`), with NO probabilistic input — a genuine unconditional discharge of the
`eq.inner_sum` counting hypothesis used by `var_term_1`/`var_term_2`/`var_term_3`. -/
theorem inner_sum_count {d : ℕ} (hd : 1 ≤ d) (c N : ℕ) :
    ∑ w ∈ linfBall (0 : Fin d → ℤ) (N : ℤ),
        (1 : ℝ) / ((linfDist 0 w + 1 - c : ℕ) : ℝ) ^ 2
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((N : ℝ) + 1) ^ (d - 1) * 2 := by
  refine le_trans (radial_sum_shell_bound hd (0 : Fin d → ℤ) N
    (fun ρ => (1 : ℝ) / ((ρ + 1 - c : ℕ) : ℝ) ^ 2) (fun ρ => by positivity)) ?_
  have hb : ∀ ρ ∈ Finset.range (N + 1),
      2 * (d : ℝ) * 3 ^ (d - 1) * ((ρ + 1 : ℕ) : ℝ) ^ (d - 1) * (1 / ((ρ + 1 - c : ℕ) : ℝ) ^ 2)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((N : ℝ) + 1) ^ (d - 1) * (1 / ((ρ + 1 - c : ℕ) : ℝ) ^ 2) := by
    intro ρ hρ
    have hρN : ρ ≤ N := by have := Finset.mem_range.mp hρ; omega
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have hle : ((ρ : ℝ)) ≤ (N : ℝ) := by exact_mod_cast hρN
    push_cast; linarith
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  by_cases hcN : c ≤ N + 1
  · rw [← Finset.sum_range_add_sum_Ico _ hcN, Finset.sum_Ico_eq_sum_range]
    have hz : ∑ ρ ∈ Finset.range c, (1 : ℝ) / ((ρ + 1 - c : ℕ) : ℝ) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun ρ hρ => by
        have hρc : ρ + 1 - c = 0 := by have := Finset.mem_range.mp hρ; omega
        rw [hρc]; norm_num)
    rw [hz, zero_add]
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun k _ => ?_))) (inv_sq_sum_le_two (N + 1 - c))
    rw [show c + k + 1 - c = k + 1 by omega]
  · have hz : ∑ ρ ∈ Finset.range (N + 1), (1 : ℝ) / ((ρ + 1 - c : ℕ) : ℝ) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun ρ hρ => by
        have hρc : ρ + 1 - c = 0 := by have := Finset.mem_range.mp hρ; omega
        rw [hρc]; norm_num)
    rw [hz]; norm_num

/-- Near-region convolution bound (component of `eq.F_pointwise` / the bubble estimate, the
analytic — non-probabilistic — content given the two-point power-law `τ ≲ (1+|·|)^{2-d}`):
the kernel `(|u-y|_∞+1)^{2-d} = 1/(|u-y|_∞+1)^{d-2}` summed over the ℓ∞ ball of radius `K`
is `≲ (K+1)^2`. (This is the `∑_{|y-u|≤M/2}(1+|u-y|)^{2-d} ≲ M^2` step of the `F_1` estimate.)
Proof: radial grouping + `(j+1)^{d-1}/(j+1)^{d-2} = (j+1)` + `∑_{j≤K}(j+1) ≤ (K+1)^2`. -/
theorem ball_inv_pow_sum {d : ℕ} (hd : 2 ≤ d) (u : Fin d → ℤ) (K : ℕ) :
    ∑ y ∈ linfBall u (K : ℤ), (1 : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2 := by
  refine le_trans (radial_sum_shell_bound (by omega) u K
    (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (d - 2)) (fun j => by positivity)) ?_
  have hterm : ∀ j ∈ Finset.range (K + 1),
      2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) * (1 / ((j + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) := by
    intro j hj
    have hjK : ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) + 1 := by
      have h : j + 1 ≤ K + 1 := by have := Finset.mem_range.mp hj; omega
      exact_mod_cast h
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hsplit : ((j + 1 : ℕ) : ℝ) ^ (d - 1)
        = ((j + 1 : ℕ) : ℝ) ^ (d - 2) * ((j + 1 : ℕ) : ℝ) := by
      rw [← pow_succ]; congr 1; omega
    have heq : 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / ((j + 1 : ℕ) : ℝ) ^ (d - 2))
        = 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) := by
      rw [hsplit]; field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hjK (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- Far/convergent-region convolution bound (the second region of `eq.F_pointwise` / the bubble
estimate): for `d ≥ 5`, the kernel `(|u-y|_∞+1)^{4-2d} = 1/(|u-y|_∞+1)^{2d-4}` summed over the
ℓ∞ ball is `≲ 1` (bounded, uniformly in `K`). After radial grouping the exponent is
`(j+1)^{(d-1)-(2d-4)} = (j+1)^{3-d} ≤ (j+1)^{-2}`, and the `p=2` tail converges
(`inv_sq_sum_le_two`). This is the convergent piece of the `F_1` far-region estimate. -/
theorem ball_inv_pow_sum_conv {d : ℕ} (hd : 5 ≤ d) (u : Fin d → ℤ) (K : ℕ) :
    ∑ y ∈ linfBall u (K : ℤ), (1 : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (2 * d - 4)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * 2 := by
  refine le_trans (radial_sum_shell_bound (by omega) u K
    (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (2 * d - 4)) (fun j => by positivity)) ?_
  have hterm : ∀ j ∈ Finset.range (K + 1),
      2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1) * (1 / ((j + 1 : ℕ) : ℝ) ^ (2 * d - 4))
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (1 / ((j + 1 : ℕ) : ℝ) ^ 2) := by
    intro j _
    have hpos : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      have : 1 ≤ j + 1 := by omega
      exact_mod_cast this
    have hpos0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := lt_of_lt_of_le one_pos hpos
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsplit : ((j + 1 : ℕ) : ℝ) ^ (2 * d - 4)
        = ((j + 1 : ℕ) : ℝ) ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 3) := by
      rw [← pow_add]; congr 1; omega
    rw [mul_one_div, hsplit,
      show ((j + 1 : ℕ) : ℝ) ^ (d - 1) / (((j + 1 : ℕ) : ℝ) ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 3))
          = 1 / ((j + 1 : ℕ) : ℝ) ^ (d - 3) from by field_simp]
    exact one_div_le_one_div_of_le (pow_pos hpos0 2) (pow_le_pow_right₀ hpos (by omega))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (inv_sq_sum_le_two (K + 1)) (by positivity)

/-! ### `linfDist` is a metric: self / symmetry / triangle inequality

These are the foundational metric facts the two-center bubble estimate needs to relate
`|x-y|_∞`, `|y-u|_∞`, `|x-u|_∞` via the triangle inequality. -/

/-- `linfDist x x = 0`. -/
theorem linfDist_self {d : ℕ} (x : Fin d → ℤ) : linfDist x x = 0 := by
  rw [linfDist]; simp

/-- `linfDist` is symmetric. -/
theorem linfDist_comm {d : ℕ} (x u : Fin d → ℤ) : linfDist x u = linfDist u x := by
  rw [linfDist, linfDist]
  exact Finset.sup_congr rfl (fun i _ => by omega)

/-- Triangle inequality for the ℓ∞ distance: `|x-z|_∞ ≤ |x-u|_∞ + |u-z|_∞`. -/
theorem linfDist_triangle {d : ℕ} (x u z : Fin d → ℤ) :
    linfDist x z ≤ linfDist x u + linfDist u z := by
  rw [linfDist, Finset.sup_le_iff]
  intro i _
  have h1 : (x i - u i).natAbs ≤ linfDist x u := by
    rw [linfDist]; exact Finset.le_sup (f := fun i => (x i - u i).natAbs) (Finset.mem_univ i)
  have h2 : (u i - z i).natAbs ≤ linfDist u z := by
    rw [linfDist]; exact Finset.le_sup (f := fun i => (u i - z i).natAbs) (Finset.mem_univ i)
  have h3 : (x i - z i).natAbs ≤ (x i - u i).natAbs + (u i - z i).natAbs := by omega
  omega

/-- Bubble near-region bound: on a set `S ⊆ ball u K` where the distance to `x` is uniformly
`≥ c` (the region where `y` is near `u` and far from `x`), the two-center kernel product
`(|x-y|_∞+1)^{2-d}(|y-u|_∞+1)^{2-d}` sums to `≤ (c+1)^{2-d} · 2d·3^{d-1}(K+1)^2`: the far
`x`-factor is pulled out (uniformly bounded, since `t ↦ t^{2-d}` is decreasing) and the `u`-sum
is the near-region `ball_inv_pow_sum`. One region of the two-center bubble estimate, assembled
from `ball_inv_pow_sum` + power monotonicity. -/
theorem bubble_near_region {d : ℕ} (hd : 2 ≤ d) (x u : Fin d → ℤ) (c K : ℕ)
    (S : Finset (Fin d → ℤ)) (hS : S ⊆ linfBall u (K : ℤ))
    (hc : ∀ y ∈ S, c ≤ linfDist x y) :
    ∑ y ∈ S, (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2) := by
  calc ∑ y ∈ S, (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 2))
            * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ ∑ y ∈ S, (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2))
            * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)) := by
        apply Finset.sum_le_sum
        intro y hy
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply one_div_le_one_div_of_le (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        have h := hc y hy
        have : c + 1 ≤ linfDist x y + 1 := by omega
        exact_mod_cast this
    _ = (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2))
          * ∑ y ∈ S, (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)) := by rw [← Finset.mul_sum]
    _ ≤ (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_trans
          (Finset.sum_le_sum_of_subset_of_nonneg hS (fun y _ _ => by positivity))
          (ball_inv_pow_sum hd u K)

/-- Full two-center bubble bound: `∑_{y∈T} (|x-y|_∞+1)^{2-d}(|y-u|_∞+1)^{2-d}
≤ 2·(⌊|x-u|_∞/2⌋+1)^{2-d}·2d·3^{d-1}(K+1)^2` for `T ⊆ ball u K ∩ ball x K`. This is the lattice
convolution of two power laws (the analytic core of the bubble/`eq.F_pointwise` estimate, given
the two-point power law `τ ≲ (1+|·|)^{2-d}`). Proof: split `T` on whether `|x-y|_∞ ≥ ⌊|x-u|/2⌋`;
on that part `x` is far, on the complement the triangle inequality forces `u` far, so each part is
one application of `bubble_near_region`. (With `|x-u| ≥ r` the bound is `≲ |x-u|^{2-d}·M^2 ≲ M^{4-d}`.) -/
theorem bubble_bound {d : ℕ} (hd : 2 ≤ d) (x u : Fin d → ℤ) (K : ℕ)
    (T : Finset (Fin d → ℤ)) (hTu : T ⊆ linfBall u (K : ℤ)) (hTx : T ⊆ linfBall x (K : ℤ)) :
    ∑ y ∈ T, (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ 2 * ((1 / ((linfDist x u / 2 + 1 : ℕ) : ℝ) ^ (d - 2))
            * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2)) := by
  set c : ℕ := linfDist x u / 2 with hc_def
  set B : ℝ := (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2))
    * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2) with hB_def
  rw [← Finset.sum_filter_add_sum_filter_not T (fun y => c ≤ linfDist x y)]
  have hS1 : ∑ y ∈ T.filter (fun y => c ≤ linfDist x y),
      (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 2)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ B := by
    apply bubble_near_region hd x u c K
    · exact (Finset.filter_subset _ _).trans hTu
    · intro y hy; exact (Finset.mem_filter.mp hy).2
  have hS2 : ∑ y ∈ T.filter (fun y => ¬ c ≤ linfDist x y),
      (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 2)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ B := by
    rw [Finset.sum_congr rfl (fun y _ => mul_comm _ _)]
    apply bubble_near_region hd u x c K
    · exact (Finset.filter_subset _ _).trans hTx
    · intro y hy
      have hlt : linfDist x y < c := by have := (Finset.mem_filter.mp hy).2; omega
      have htri : linfDist x u ≤ linfDist x y + linfDist u y := by
        have h := linfDist_triangle x y u
        rw [linfDist_comm y u] at h
        exact h
      omega
  linarith [hS1, hS2]

end NearCritical.AppendixVariance
