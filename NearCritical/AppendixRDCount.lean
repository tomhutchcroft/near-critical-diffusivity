module

public import NearCritical.AppendixRDGeometry
public import NearCritical.HarmonicBound

/-! Sharp Appendix-B remote-distance count `eq.RD_count` (source §var_term_3 proof):
`#{w ∈ RD : s_w = s} ≲ s · n^{d-2}` and `∑_{w∈RD} s_w^{-2} ≲ n^{d-2} log n`.

Dimension is written `d = k + 1`, with coordinate `0` the half-space normal of
`AppendixRDGeometry`. The only regime hypotheses are `(c : ℤ) = a` (the half-space boundary
sits at `c₁n`) and `c ≤ m` (`c₁n ≤ n/2`). Coordinate-0 dominance `a₍₂₎(w) < |w 0|` is DERIVED
from membership in `RD`, not assumed. Proof: on `RD`, `r_w < s_w` pins `w 0` to `s_w` values,
and the remaining `k` coordinates have ℓ∞ norm exactly `c - s_w`, so they lie on a
`k`-dimensional ℓ∞ shell (`fiber_card_real_le`); `rd_count_template` then sums over `s`.
Non-probabilistic. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

variable {k : ℕ}

/-- The max absolute value over the non-pinned coordinates `1, …, k`. -/
def tailMax (w : Fin (k + 1) → ℤ) : ℕ :=
  Finset.univ.sup (fun i : Fin k => (w i.succ).natAbs)

theorem linfDist_zero_tail (w : Fin (k + 1) → ℤ) :
    linfDist (0 : Fin k → ℤ) (Fin.tail w) = tailMax w := by
  rw [linfDist_zero]; rfl

/-- Coordinate-0 dominance on `RD` (derived, not assumed): `a₍₂₎(w) < |w 0|`. -/
theorem RD_secondMax_lt {m c : ℕ} {a : ℤ} (hc : (c : ℤ) = a) {w : Fin (k + 1) → ℤ}
    (hw : w ∈ (RD m c a : Finset (Fin (k + 1) → ℤ))) :
    secondMax w < (w 0).natAbs := by
  rw [mem_RD, mem_annulus] at hw
  obtain ⟨⟨_, ha⟩, hrs⟩ := hw
  unfold rParam sParam at hrs
  omega

/-- Under coordinate-0 dominance, `a₍₂₎(w)` is the max over the other coordinates. -/
theorem secondMax_eq_tailMax {w : Fin (k + 1) → ℤ} (hdom : secondMax w < (w 0).natAbs) :
    secondMax w = tailMax w := by
  apply le_antisymm
  · rw [secondMax, Finset.sup_le_iff]
    intro p _
    by_cases hp : p.1 = p.2
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      by_cases h1 : p.1 = 0
      · have h2 : p.2 ≠ 0 := fun h => hp (h1.trans h.symm)
        refine le_trans (min_le_right _ _) ?_
        rw [← Fin.succ_pred p.2 h2]
        exact Finset.le_sup (f := fun i : Fin k => (w i.succ).natAbs) (Finset.mem_univ _)
      · refine le_trans (min_le_left _ _) ?_
        rw [← Fin.succ_pred p.1 h1]
        exact Finset.le_sup (f := fun i : Fin k => (w i.succ).natAbs) (Finset.mem_univ _)
  · rw [tailMax, Finset.sup_le_iff]
    intro j _
    have hne : (j.succ : Fin (k + 1)) ≠ 0 := Fin.succ_ne_zero j
    have hp : min (w j.succ).natAbs (w 0).natAbs ≤ secondMax w := by
      have h := Finset.le_sup
        (f := fun p : Fin (k + 1) × Fin (k + 1) =>
          if p.1 = p.2 then 0 else min (w p.1).natAbs (w p.2).natAbs)
        (Finset.mem_univ ((j.succ, 0) : Fin (k + 1) × Fin (k + 1)))
      simp only [hne, ↓reduceIte] at h
      exact h
    rcases le_total (w j.succ).natAbs (w 0).natAbs with h | h
    · rwa [min_eq_left h] at hp
    · rw [min_eq_right h] at hp; omega

/-- Each shortfall fiber of `RD` injects into (pinned coordinate 0) × (`k`-dim ℓ∞ shell). -/
theorem RD_fiber_subset {m c : ℕ} {a : ℤ} (hc : (c : ℤ) = a) (s : ℕ) :
    (RD m c a : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w = s) ⊆
      ((Finset.Ioc (a - s) a) ×ˢ ((linfBall (0 : Fin k → ℤ) (m : ℤ)).filter
          (fun u => linfDist 0 u = c - s))).image
        (fun x => (Fin.cons x.1 x.2 : Fin (k + 1) → ℤ)) := by
  intro w hw
  rw [Finset.mem_filter] at hw
  obtain ⟨hRD, hs⟩ := hw
  have htail := secondMax_eq_tailMax (RD_secondMax_lt hc hRD)
  rw [mem_RD, mem_annulus, mem_cube] at hRD
  obtain ⟨⟨hcube, ha⟩, hrs⟩ := hRD
  unfold rParam sParam at hrs
  unfold sParam at hs
  rw [Finset.mem_image]
  refine ⟨(w 0, Fin.tail w), ?_, Fin.cons_self_tail w⟩
  simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_filter, mem_linfBall,
    linfDist_zero_tail]
  refine ⟨⟨by omega, ha⟩, fun i => ?_, by omega⟩
  simpa [Fin.tail] using hcube i.succ

/-- Sharp per-shortfall count: `#{w ∈ RD : s_w = s} ≤ s · 2k(2m+1)^{k-1}`
(`≲ s · n^{d-2}` with `d = k+1`, `m ≍ n`). -/
theorem RD_fiber_card_le (hk : 1 ≤ k) {m c : ℕ} {a : ℤ} (hc : (c : ℤ) = a) (hcm : c ≤ m)
    (s : ℕ) :
    ((((RD m c a : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w = s)).card : ℕ) : ℝ)
      ≤ (s : ℝ) * (2 * (k : ℝ) * (2 * (m : ℝ) + 1) ^ (k - 1)) := by
  have h1 := Finset.card_le_card (RD_fiber_subset (k := k) (m := m) hc s)
  have h2 := Finset.card_image_le
    (s := (Finset.Ioc (a - s) a) ×ˢ ((linfBall (0 : Fin k → ℤ) (m : ℤ)).filter
          (fun u => linfDist 0 u = c - s)))
    (f := fun x => (Fin.cons x.1 x.2 : Fin (k + 1) → ℤ))
  rw [Finset.card_product, Int.card_Ioc, show (a - (a - (s : ℤ))).toNat = s by omega] at h2
  have h3 := fiber_card_real_le hk (0 : Fin k → ℤ) (K := m) (j := c - s) (by omega)
  have h4 : (2 * ((c - s : ℕ) : ℝ) + 1) ^ (k - 1) ≤ (2 * (m : ℝ) + 1) ^ (k - 1) := by
    have hle : ((c - s : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show c - s ≤ m by omega)
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have h5 : ((((RD m c a : Finset (Fin (k + 1) → ℤ)).filter
        (fun w => sParam c w = s)).card : ℕ) : ℝ)
      ≤ (s : ℝ) * ((((linfBall (0 : Fin k → ℤ) (m : ℤ)).filter
          (fun u => linfDist 0 u = c - s)).card : ℕ) : ℝ) := by
    exact_mod_cast h1.trans h2
  calc _ ≤ _ := h5
    _ ≤ (s : ℝ) * (2 * (k : ℝ) * (2 * ((c - s : ℕ) : ℝ) + 1) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity))
        (by positivity)

/-- `eq.RD_count`: `∑_{w∈RD} s_w^{-2} ≤ 2k(2m+1)^{k-1} (1 + log c)`
(`≲ n^{d-2} log n` with `d = k+1`, `c = c₁n ≤ m ≍ n`). -/
theorem RD_inv_sq_sum_le (hk : 1 ≤ k) {m c : ℕ} {a : ℤ} (hc : (c : ℤ) = a) (hcm : c ≤ m) :
    ∑ w ∈ (RD m c a : Finset (Fin (k + 1) → ℤ)), (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2
      ≤ 2 * (k : ℝ) * (2 * (m : ℝ) + 1) ^ (k - 1) * (1 + Real.log (c : ℝ)) := by
  have hmaps : ∀ w ∈ (RD m c a : Finset (Fin (k + 1) → ℤ)),
      sParam c w - 1 ∈ Finset.range c := by
    intro w hw
    rw [mem_RD] at hw
    have := sParam_le c w
    rw [Finset.mem_range]; omega
  have hinner : ∀ j ∈ Finset.range c,
      ∑ w ∈ (RD m c a : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w - 1 = j),
          (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2
        = ((((RD m c a : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w = j + 1)).card : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 := by
    intro j _
    have hf : (RD m c a : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w - 1 = j)
        = (RD m c a).filter (fun w => sParam c w = j + 1) := by
      apply Finset.filter_congr
      intro w hw
      rw [mem_RD] at hw
      constructor <;> intro h <;> omega
    rw [hf]
    calc ∑ w ∈ (RD m c a : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w = j + 1),
          (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2
        = ∑ w ∈ (RD m c a : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w = j + 1),
          (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2])
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc ∑ w ∈ (RD m c a : Finset (Fin (k + 1) → ℤ)), (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2
      = ∑ j ∈ Finset.range c,
          ∑ w ∈ (RD m c a : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w - 1 = j),
            (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ Finset.range c, ((((RD m c a : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w = j + 1)).card : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 :=
        Finset.sum_congr rfl hinner
    _ ≤ _ := rd_count_template (M := c) _ (by positivity)
        (fun s => ((((RD m c a : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w = s)).card : ℕ) : ℝ))
        (fun s _ => (RD_fiber_card_le hk hc hcm (s + 1)).trans_eq (mul_comm _ _))

end NearCritical.AppendixVariance
