module

public import NearCritical.AppendixRDGeometry
public import NearCritical.HarmonicBound

/-! Source-literal Appendix-B geometry and the first half of `eq.RD_count`.

Source (main.tex, §"Upper bound for the 2-point function in cubes and annulus" and the proof
of prop.var_term_3): `Ann_{c₁n} = Λ_n \ int Λ_{c₁n}`, `r_w = a₍₁₎(w) - c₁n = |w|_∞ - c₁n`,
`s_w = c₁n - a₍₂₎(w)`, `RD_{c₁n} = {w ∈ Ann : r_w < s_w}` (the union of `2d` OUTER pyramids).
These are formalized literally below as `sourceAnnulus`, `sourceR`, `sourceRD`, with `d = k+1`
and `c = c₁n`.

NOTE: `AppendixRDGeometry.annulus/RD` use a half-space convention, under which `RD m c c` is a
single INNER pyramid (a reflected face). `AppendixRDCount.RD_inv_sq_sum_le` is about that
set; THIS file proves the source statement itself.

Main result `sourceRD_inv_sq_sum_le`: `∑_{w∈RD} s_w^{-2} ≤ 4k(k+1)(2c+1)^{k-1}(1+log c)`
(`≲ n^{d-2} log n`). Proof: on `RD` the max coordinate `j` is unique (`a₍₂₎ < a₍₁₎`). With
`s_w = s`, `w j` takes `≤ 2s` values (`c ≤ |w j| < c+s`, either sign), and the other `k`
coordinates lie on the ℓ∞ shell of radius `c - s` (`fiber_card_real_le`). Deterministic;
only `1 ≤ k` and `c ≤ n` assumed. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

variable {k : ℕ}

/-- Source `Ann_{c₁n} = Λ_n \ int Λ_{c₁n}`. -/
def sourceAnnulus (n c : ℕ) : Finset (Fin (k + 1) → ℤ) :=
  (cube n : Finset (Fin (k + 1) → ℤ)).filter
    (fun w => c ≤ linfDist (0 : Fin (k + 1) → ℤ) w)

/-- Source `r_w = |w|_∞ - c₁n` (the ℓ∞ distance from `w ∈ Ann` to `∂Λ_{c₁n}`). -/
def sourceR (c : ℕ) (w : Fin (k + 1) → ℤ) : ℕ :=
  linfDist (0 : Fin (k + 1) → ℤ) w - c

/-- Source `RD_{c₁n} = {w ∈ Ann_{c₁n} : r_w < s_w}`. -/
def sourceRD (n c : ℕ) : Finset (Fin (k + 1) → ℤ) :=
  (sourceAnnulus n c).filter (fun w => sourceR c w < sParam c w)

theorem mem_sourceRD {n c : ℕ} {w : Fin (k + 1) → ℤ} :
    w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ)) ↔
      (w ∈ (cube n : Finset (Fin (k + 1) → ℤ)) ∧ c ≤ linfDist (0 : Fin (k + 1) → ℤ) w) ∧
        sourceR c w < sParam c w := by
  unfold sourceRD sourceAnnulus
  simp only [Finset.mem_filter]

/-- If coordinate `j` strictly exceeds `a₍₂₎(w)`, then `a₍₂₎(w)` is the max over the others. -/
theorem secondMax_eq_sup_succAbove {w : Fin (k + 1) → ℤ} {j : Fin (k + 1)}
    (hdom : secondMax w < (w j).natAbs) :
    secondMax w = Finset.univ.sup (fun i : Fin k => (w (j.succAbove i)).natAbs) := by
  apply le_antisymm
  · rw [secondMax, Finset.sup_le_iff]
    intro p _
    by_cases hp : p.1 = p.2
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      by_cases h1 : p.1 = j
      · have h2 : p.2 ≠ j := fun h => hp (h1.trans h.symm)
        obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq h2
        refine le_trans (min_le_right _ _) ?_
        rw [← hz]
        exact Finset.le_sup (f := fun i : Fin k => (w (j.succAbove i)).natAbs)
          (Finset.mem_univ z)
      · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq h1
        refine le_trans (min_le_left _ _) ?_
        rw [← hz]
        exact Finset.le_sup (f := fun i : Fin k => (w (j.succAbove i)).natAbs)
          (Finset.mem_univ z)
  · rw [Finset.sup_le_iff]
    intro i _
    have hne : j.succAbove i ≠ j := Fin.succAbove_ne j i
    have hp : min (w (j.succAbove i)).natAbs (w j).natAbs ≤ secondMax w := by
      have h := Finset.le_sup
        (f := fun p : Fin (k + 1) × Fin (k + 1) =>
          if p.1 = p.2 then 0 else min (w p.1).natAbs (w p.2).natAbs)
        (Finset.mem_univ ((j.succAbove i, j) : Fin (k + 1) × Fin (k + 1)))
      simp only [hne, ↓reduceIte] at h
      exact h
    rcases le_total (w (j.succAbove i)).natAbs (w j).natAbs with h | h
    · rwa [min_eq_left h] at hp
    · rw [min_eq_right h] at hp; omega

/-- On source `RD`, some coordinate realizes `|w|_∞` and strictly exceeds `a₍₂₎(w)`. -/
theorem sourceRD_exists_dominant {n c : ℕ} {w : Fin (k + 1) → ℤ}
    (hw : w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ))) :
    ∃ j : Fin (k + 1), (w j).natAbs = linfDist (0 : Fin (k + 1) → ℤ) w ∧
      secondMax w < (w j).natAbs := by
  rw [mem_sourceRD] at hw
  obtain ⟨⟨_, hcA⟩, hrs⟩ := hw
  unfold sourceR sParam at hrs
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (k + 1)))
    Finset.univ_nonempty (fun i => (w i).natAbs)
  have hA : linfDist (0 : Fin (k + 1) → ℤ) w = (w j).natAbs := by rw [linfDist_zero, hj]
  exact ⟨j, hA.symm, by omega⟩

/-- Values of the dominant coordinate with `c ≤ |t| < c + s`. -/
def sourceSignSet (c s : ℕ) : Finset ℤ :=
  Finset.Ico (c : ℤ) (c + s) ∪ Finset.Ioc (-((c : ℤ) + s)) (-(c : ℤ))

theorem sourceSignSet_card_le (c s : ℕ) : (sourceSignSet c s).card ≤ 2 * s := by
  unfold sourceSignSet
  refine (Finset.card_union_le _ _).trans ?_
  rw [Int.card_Ico, Int.card_Ioc]
  omega

/-- The `k`-dimensional ℓ∞ shell of radius `c - s` inside `Λ_n`. -/
def sourceTailShell (n c s : ℕ) : Finset (Fin k → ℤ) :=
  (linfBall (0 : Fin k → ℤ) (n : ℤ)).filter (fun u => linfDist 0 u = c - s)

/-- Each shortfall fiber of source `RD` injects into
(dominant index) × (dominant value) × (tail shell). -/
theorem sourceRD_fiber_subset {n c : ℕ} (s : ℕ) :
    (sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w = s) ⊆
      (Finset.univ ×ˢ sourceSignSet c s ×ˢ (sourceTailShell n c s : Finset (Fin k → ℤ))).image
        (fun x => (Fin.insertNth (α := fun _ => ℤ) x.1 x.2.1 x.2.2 : Fin (k + 1) → ℤ)) := by
  intro w hw
  rw [Finset.mem_filter] at hw
  obtain ⟨hRD, hs⟩ := hw
  obtain ⟨j, hjA, hdom⟩ := sourceRD_exists_dominant hRD
  have htail : linfDist (0 : Fin k → ℤ) (Fin.removeNth j w) = secondMax w := by
    rw [linfDist_zero, secondMax_eq_sup_succAbove hdom]; rfl
  rw [mem_sourceRD, mem_cube] at hRD
  obtain ⟨⟨hcube, hcA⟩, hrs⟩ := hRD
  unfold sourceR sParam at hrs
  unfold sParam at hs
  rw [Finset.mem_image]
  refine ⟨(j, w j, Fin.removeNth j w), ?_, Fin.insertNth_self_removeNth j w⟩
  simp only [Finset.mem_product, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · unfold sourceSignSet
    rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
    omega
  · unfold sourceTailShell
    rw [Finset.mem_filter, mem_linfBall, htail]
    refine ⟨fun i => ?_, by omega⟩
    simpa [Fin.removeNth] using hcube (j.succAbove i)

/-- Per-shortfall count on source `RD`: `#{w ∈ RD : s_w = s} ≤ s · 4k(k+1)(2c+1)^{k-1}`. -/
theorem sourceRD_fiber_card_le (hk : 1 ≤ k) {n c : ℕ} (hcn : c ≤ n) (s : ℕ) :
    ((((sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
        (fun w => sParam c w = s)).card : ℕ) : ℝ)
      ≤ (s : ℝ) * (4 * (k : ℝ) * ((k : ℝ) + 1) * (2 * (c : ℝ) + 1) ^ (k - 1)) := by
  have hnat : ((sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
      (fun w => sParam c w = s)).card ≤
      (k + 1) * (2 * s * (sourceTailShell n c s : Finset (Fin k → ℤ)).card) := by
    calc _ ≤ _ := Finset.card_le_card (sourceRD_fiber_subset (k := k) (n := n) s)
      _ ≤ (Finset.univ ×ˢ sourceSignSet c s ×ˢ
            (sourceTailShell n c s : Finset (Fin k → ℤ))).card := Finset.card_image_le
      _ = (k + 1) * ((sourceSignSet c s).card *
            (sourceTailShell n c s : Finset (Fin k → ℤ)).card) := by
          rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (sourceSignSet_card_le c s))
  have hR : ((((sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
        (fun w => sParam c w = s)).card : ℕ) : ℝ) ≤
      ((k : ℝ) + 1) * (2 * (s : ℝ) *
        (((sourceTailShell n c s : Finset (Fin k → ℤ)).card : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have h3 : (((sourceTailShell n c s : Finset (Fin k → ℤ)).card : ℕ) : ℝ) ≤
      2 * (k : ℝ) * (2 * ((c - s : ℕ) : ℝ) + 1) ^ (k - 1) :=
    fiber_card_real_le hk (0 : Fin k → ℤ) (K := n) (j := c - s) (by omega)
  have h4 : (2 * ((c - s : ℕ) : ℝ) + 1) ^ (k - 1) ≤ (2 * (c : ℝ) + 1) ^ (k - 1) := by
    have hle : ((c - s : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast Nat.sub_le c s
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc _ ≤ _ := hR
    _ ≤ ((k : ℝ) + 1) * (2 * (s : ℝ) *
          (2 * (k : ℝ) * (2 * ((c - s : ℕ) : ℝ) + 1) ^ (k - 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity))
          (by positivity)
    _ ≤ ((k : ℝ) + 1) * (2 * (s : ℝ) * (2 * (k : ℝ) * (2 * (c : ℝ) + 1) ^ (k - 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h4 (by positivity)) (by positivity)) (by positivity)
    _ = _ := by ring

/-- Source `eq.RD_count`, first estimate:
`∑_{w∈RD_{c₁n}} s_w^{-2} ≤ 4k(k+1)(2c+1)^{k-1}(1 + log c)` (`≲ n^{d-2} log n`, `d = k+1`). -/
theorem sourceRD_inv_sq_sum_le (hk : 1 ≤ k) {n c : ℕ} (hcn : c ≤ n) :
    ∑ w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ)), (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2
      ≤ 4 * (k : ℝ) * ((k : ℝ) + 1) * (2 * (c : ℝ) + 1) ^ (k - 1) *
        (1 + Real.log (c : ℝ)) := by
  have hmaps : ∀ w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ)),
      sParam c w - 1 ∈ Finset.range c := by
    intro w hw
    rw [mem_sourceRD] at hw
    have := sParam_le c w
    rw [Finset.mem_range]; omega
  have hinner : ∀ j ∈ Finset.range c,
      ∑ w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter (fun w => sParam c w - 1 = j),
          (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2
        = ((((sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w = j + 1)).card : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 := by
    intro j _
    have hf : (sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
        (fun w => sParam c w - 1 = j) = (sourceRD n c).filter (fun w => sParam c w = j + 1) := by
      apply Finset.filter_congr
      intro w hw
      rw [mem_sourceRD] at hw
      constructor <;> intro h <;> omega
    rw [hf]
    calc ∑ w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w = j + 1), (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2
        = ∑ w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w = j + 1), (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2])
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  calc ∑ w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ)), (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2
      = ∑ j ∈ Finset.range c,
          ∑ w ∈ (sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w - 1 = j), (1 : ℝ) / ((sParam c w : ℕ) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ Finset.range c, ((((sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w = j + 1)).card : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2 :=
        Finset.sum_congr rfl hinner
    _ ≤ _ := rd_count_template (M := c) _ (by positivity)
        (fun s => ((((sourceRD n c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sParam c w = s)).card : ℕ) : ℝ))
        (fun s _ => (sourceRD_fiber_card_le hk hcn (s + 1)).trans_eq (mul_comm _ _))

end NearCritical.AppendixVariance
