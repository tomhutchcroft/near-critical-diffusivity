module

public import NearCritical.AppendixSourceRD

/-! Source `eq.RD_count`, second estimate (proof of prop.var_term_3):
`∑_{w ∈ (Ann_{c₁n} ∩ Λ_{n/2}) \ RD_{c₁n}} (1+r_w)^{-2} ≲ n^{d-2} log n`.

Literal geometry from `AppendixSourceRD` (`d = k+1`, `c = c₁n`, `h = n/2`).
`Ann_{c₁n} ∩ Λ_h = sourceAnnulus h c`, and the complement of `RD` in it is
`sourceAnnComplRD h c` (identified with the set difference in `sourceAnnComplRD_eq`).

Proof: for `w` with `r_w = r`, a max coordinate `j` has `|w j| = c + r` (2 values), and the
other `k` coordinates lie in the ℓ∞ ball of radius `c+r` with norm `≥ a₍₂₎(w) ≥ c - r`
(`w ∉ RD` means `s_w ≤ r`). That tail set has `≤ 4k(2h+1)^{k-1}(1+r)` points: a shell
difference if `r < c`, the whole ball if `r ≥ c`. Summing `(1+r)·(1+r)^{-2}` gives the harmonic
bound via `rd_count_template`. Deterministic; only `1 ≤ k` and `c ≤ h` are assumed.
 -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

variable {k : ℕ}

/-- Source `(Ann_{c₁n} ∩ Λ_h) \ RD_{c₁n}`. -/
def sourceAnnComplRD (h c : ℕ) : Finset (Fin (k + 1) → ℤ) :=
  (sourceAnnulus h c).filter (fun w => ¬ sourceR c w < sParam c w)

/-- For `h ≤ n`, `sourceAnnComplRD h c` is literally `(Ann ∩ Λ_h) \ RD`. -/
theorem sourceAnnComplRD_eq {h n c : ℕ} (hhn : h ≤ n) :
    (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)) =
      (sourceAnnulus h c : Finset (Fin (k + 1) → ℤ)) \ sourceRD n c := by
  ext w
  simp only [sourceAnnComplRD, sourceAnnulus, Finset.mem_filter, Finset.mem_sdiff,
    mem_sourceRD]
  constructor
  · rintro ⟨⟨hcube, hc⟩, hnot⟩
    exact ⟨⟨hcube, hc⟩, fun h' => hnot h'.2⟩
  · rintro ⟨⟨hcube, hc⟩, hnot⟩
    refine ⟨⟨hcube, hc⟩, fun hlt => hnot ⟨⟨?_, hc⟩, hlt⟩⟩
    rw [mem_cube] at hcube ⊢
    exact fun i => (hcube i).trans (by exact_mod_cast hhn)

/-- `a₍₂₎(w)` is at most the max over the coordinates other than any fixed `j`. -/
theorem secondMax_le_sup_succAbove (w : Fin (k + 1) → ℤ) (j : Fin (k + 1)) :
    secondMax w ≤ Finset.univ.sup (fun i : Fin k => (w (j.succAbove i)).natAbs) := by
  rw [secondMax, Finset.sup_le_iff]
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

/-- Tail set: `k` coordinates in the ℓ∞ ball of radius `c+r` with norm `≥ c - r`. -/
def complTail (c r : ℕ) : Finset (Fin k → ℤ) :=
  (linfBall (0 : Fin k → ℤ) ((c + r : ℕ) : ℤ)).filter
    (fun u => c - r ≤ linfDist (0 : Fin k → ℤ) u)

/-- Each `r_w`-fiber of the complement injects into
(max index) × `{±(c+r)}` × (tail set). -/
theorem complRD_fiber_subset {h c : ℕ} (r : ℕ) :
    (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter (fun w => sourceR c w = r) ⊆
      (Finset.univ ×ˢ ({((c + r : ℕ) : ℤ), -((c + r : ℕ) : ℤ)} : Finset ℤ) ×ˢ
          (complTail c r : Finset (Fin k → ℤ))).image
        (fun x => (Fin.insertNth (α := fun _ => ℤ) x.1 x.2.1 x.2.2 : Fin (k + 1) → ℤ)) := by
  intro w hw
  simp only [sourceAnnComplRD, sourceAnnulus, Finset.mem_filter] at hw
  obtain ⟨⟨⟨_, hcA⟩, hnot⟩, hr⟩ := hw
  unfold sourceR sParam at hnot
  unfold sourceR at hr
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (k + 1)))
    Finset.univ_nonempty (fun i => (w i).natAbs)
  have hA : linfDist (0 : Fin (k + 1) → ℤ) w = (w j).natAbs := by rw [linfDist_zero, hj]
  have hmax : ∀ i, (w i).natAbs ≤ linfDist (0 : Fin (k + 1) → ℤ) w := by
    intro i; rw [linfDist_zero]
    exact Finset.le_sup (f := fun i => (w i).natAbs) (Finset.mem_univ i)
  have htail : secondMax w ≤ linfDist (0 : Fin k → ℤ) (Fin.removeNth j w) := by
    rw [linfDist_zero]; exact secondMax_le_sup_succAbove w j
  rw [Finset.mem_image]
  refine ⟨(j, w j, Fin.removeNth j w), ?_, Fin.insertNth_self_removeNth j w⟩
  simp only [Finset.mem_product, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_insert, Finset.mem_singleton]
    omega
  · unfold complTail
    rw [Finset.mem_filter, mem_linfBall]
    refine ⟨fun i => ?_, by omega⟩
    have hi := hmax (j.succAbove i)
    simp only [Fin.removeNth, Pi.zero_apply, sub_zero, Int.abs_eq_natAbs]
    omega

/-- Tail-set count: `#complTail c r ≤ 4k(2h+1)^{k-1}(1+r)` whenever `c + r ≤ h`. -/
theorem complTail_card_le (hk : 1 ≤ k) {h c r : ℕ} (hcrh : c + r ≤ h) :
    (((complTail c r : Finset (Fin k → ℤ)).card : ℕ) : ℝ) ≤
      4 * (k : ℝ) * (2 * (h : ℝ) + 1) ^ (k - 1) * ((r : ℝ) + 1) := by
  have hA : (linfBall (0 : Fin k → ℤ) ((c + r : ℕ) : ℤ)).card = (2 * (c + r) + 1) ^ k := by
    rw [linfBall_card]; congr 1 <;> omega
  have haN : ((2 * (c + r) + 1 : ℕ) : ℝ) ≤ 2 * (h : ℝ) + 1 := by
    have : 2 * (c + r) + 1 ≤ 2 * h + 1 := by omega
    exact_mod_cast this
  have hpow : ((2 * (c + r) + 1 : ℕ) : ℝ) ^ (k - 1) ≤ (2 * (h : ℝ) + 1) ^ (k - 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) haN _
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hkR : ((k - 1 : ℕ) : ℝ) + 1 = k := by rw [Nat.cast_sub hk, Nat.cast_one]; ring
  have hkpos : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rcases lt_or_ge r c with hrc | hrc
  · have hsub : linfBall (0 : Fin k → ℤ) (((c - r : ℕ) : ℤ) - 1) ⊆
        linfBall (0 : Fin k → ℤ) ((c + r : ℕ) : ℤ) := by
      intro u hu
      rw [mem_linfBall] at hu ⊢
      exact fun i => le_trans (hu i) (by omega)
    have hsd : (complTail c r : Finset (Fin k → ℤ)) ⊆
        linfBall (0 : Fin k → ℤ) ((c + r : ℕ) : ℤ) \
          linfBall (0 : Fin k → ℤ) (((c - r : ℕ) : ℤ) - 1) := by
      intro u hu
      unfold complTail at hu
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_sdiff]
      refine ⟨hu.1, fun hB => ?_⟩
      rw [mem_linfBall_iff_dist (0 : Fin k → ℤ) u
        (by omega : (0 : ℤ) ≤ ((c - r : ℕ) : ℤ) - 1)] at hB
      omega
    have hB : (linfBall (0 : Fin k → ℤ) (((c - r : ℕ) : ℤ) - 1)).card =
        (2 * (c - r) - 1) ^ k := by
      rw [linfBall_card]; congr 1 <;> omega
    have hle : (2 * (c - r) - 1) ^ k ≤ (2 * (c + r) + 1) ^ k :=
      Nat.pow_le_pow_left (by omega) k
    have hcard : (complTail c r : Finset (Fin k → ℤ)).card ≤
        (2 * (c + r) + 1) ^ k - (2 * (c - r) - 1) ^ k := by
      calc _ ≤ _ := Finset.card_le_card hsd
        _ = _ := by rw [Finset.card_sdiff_of_subset hsub, hA, hB]
    have hR : (((complTail c r : Finset (Fin k → ℤ)).card : ℕ) : ℝ) ≤
        ((2 * (c + r) + 1 : ℕ) : ℝ) ^ k - ((2 * (c - r) - 1 : ℕ) : ℝ) ^ k := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      rwa [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow] at this
    have hba : ((2 * (c - r) - 1 : ℕ) : ℝ) ≤ ((2 * (c + r) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (c - r) - 1 ≤ 2 * (c + r) + 1 by omega)
    have key := pow_succ_sub_pow_succ_le (Nat.cast_nonneg _) hba (k - 1)
    rw [hk', hkR] at key
    have hdiff : ((2 * (c + r) + 1 : ℕ) : ℝ) - ((2 * (c - r) - 1 : ℕ) : ℝ) =
        4 * (r : ℝ) + 2 := by
      have h' : 2 * (c + r) + 1 = (2 * (c - r) - 1) + (4 * r + 2) := by omega
      rw [h']; push_cast; ring
    calc _ ≤ _ := hR
      _ ≤ _ := key
      _ = (k : ℝ) * ((2 * (c + r) + 1 : ℕ) : ℝ) ^ (k - 1) * (4 * (r : ℝ) + 2) := by
          rw [hdiff]
      _ ≤ (k : ℝ) * (2 * (h : ℝ) + 1) ^ (k - 1) * (4 * ((r : ℝ) + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) (by linarith)
            (by positivity) (by positivity)
      _ = _ := by ring
  · have hcard : (complTail c r : Finset (Fin k → ℤ)).card ≤ (2 * (c + r) + 1) ^ k := by
      calc _ ≤ _ := Finset.card_le_card (Finset.filter_subset _ _)
        _ = _ := hA
    have hR : (((complTail c r : Finset (Fin k → ℤ)).card : ℕ) : ℝ) ≤
        ((2 * (c + r) + 1 : ℕ) : ℝ) ^ k := by exact_mod_cast hcard
    have hlin : ((2 * (c + r) + 1 : ℕ) : ℝ) ≤ 4 * ((r : ℝ) + 1) := by
      have : 2 * (c + r) + 1 ≤ 4 * (r + 1) := by omega
      exact_mod_cast this
    have hX : 0 ≤ (2 * (h : ℝ) + 1) ^ (k - 1) * ((r : ℝ) + 1) := by positivity
    calc _ ≤ _ := hR
      _ = ((2 * (c + r) + 1 : ℕ) : ℝ) ^ (k - 1) * ((2 * (c + r) + 1 : ℕ) : ℝ) := by
          rw [← pow_succ, hk']
      _ ≤ (2 * (h : ℝ) + 1) ^ (k - 1) * (4 * ((r : ℝ) + 1)) :=
          mul_le_mul hpow hlin (Nat.cast_nonneg _) (by positivity)
      _ = 4 * 1 * ((2 * (h : ℝ) + 1) ^ (k - 1) * ((r : ℝ) + 1)) := by ring
      _ ≤ 4 * (k : ℝ) * ((2 * (h : ℝ) + 1) ^ (k - 1) * ((r : ℝ) + 1)) := by gcongr
      _ = _ := by ring

/-- Per-`r` count on the complement: `≤ 8k(k+1)(2h+1)^{k-1}(1+r)` for `c + r ≤ h`. -/
theorem complRD_fiber_card_le (hk : 1 ≤ k) {h c : ℕ} (r : ℕ) (hcrh : c + r ≤ h) :
    ((((sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
        (fun w => sourceR c w = r)).card : ℕ) : ℝ)
      ≤ 8 * (k : ℝ) * ((k : ℝ) + 1) * (2 * (h : ℝ) + 1) ^ (k - 1) * ((r : ℝ) + 1) := by
  have hpm : (({((c + r : ℕ) : ℤ), -((c + r : ℕ) : ℤ)} : Finset ℤ)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have hnat : ((sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
      (fun w => sourceR c w = r)).card ≤
      (k + 1) * (2 * (complTail c r : Finset (Fin k → ℤ)).card) := by
    calc _ ≤ _ := Finset.card_le_card (complRD_fiber_subset (k := k) (h := h) r)
      _ ≤ (Finset.univ ×ˢ ({((c + r : ℕ) : ℤ), -((c + r : ℕ) : ℤ)} : Finset ℤ) ×ˢ
            (complTail c r : Finset (Fin k → ℤ))).card := Finset.card_image_le
      _ = (k + 1) * ((({((c + r : ℕ) : ℤ), -((c + r : ℕ) : ℤ)} : Finset ℤ)).card *
            (complTail c r : Finset (Fin k → ℤ)).card) := by
          rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpm)
  have hR : ((((sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
        (fun w => sourceR c w = r)).card : ℕ) : ℝ) ≤
      ((k : ℝ) + 1) * (2 * (((complTail c r : Finset (Fin k → ℤ)).card : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  calc _ ≤ _ := hR
    _ ≤ ((k : ℝ) + 1) * (2 * (4 * (k : ℝ) * (2 * (h : ℝ) + 1) ^ (k - 1) * ((r : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (complTail_card_le hk hcrh)
          (by norm_num)) (by positivity)
    _ = _ := by ring

/-- Source `eq.RD_count`, second estimate:
`∑_{w ∈ (Ann ∩ Λ_h) \ RD} (1+r_w)^{-2} ≤ 8k(k+1)(2h+1)^{k-1}(1 + log(h-c+1))`
(`≲ n^{d-2} log n` with `h = n/2`, `d = k+1`). -/
theorem sourceAnnComplRD_inv_sq_sum_le (hk : 1 ≤ k) {h c : ℕ} (hch : c ≤ h) :
    ∑ w ∈ (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)),
        (1 : ℝ) / ((sourceR c w + 1 : ℕ) : ℝ) ^ 2
      ≤ 8 * (k : ℝ) * ((k : ℝ) + 1) * (2 * (h : ℝ) + 1) ^ (k - 1) *
        (1 + Real.log ((h - c + 1 : ℕ) : ℝ)) := by
  have hmaps : ∀ w ∈ (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)),
      sourceR c w ∈ Finset.range (h - c + 1) := by
    intro w hw
    simp only [sourceAnnComplRD, sourceAnnulus, Finset.mem_filter] at hw
    obtain ⟨⟨hcube, _⟩, _⟩ := hw
    have hd := (mem_linfBall_iff_dist (0 : Fin (k + 1) → ℤ) w
      (by positivity : (0 : ℤ) ≤ (h : ℤ))).mp hcube
    unfold sourceR
    rw [Finset.mem_range]
    omega
  have hinner : ∀ s ∈ Finset.range (h - c + 1),
      ∑ w ∈ (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
          (fun w => sourceR c w = s), (1 : ℝ) / ((sourceR c w + 1 : ℕ) : ℝ) ^ 2
        = ((((sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sourceR c w + 1 = s + 1)).card : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ) ^ 2 := by
    intro s _
    have hf : (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
        (fun w => sourceR c w = s) =
        (sourceAnnComplRD h c).filter (fun w => sourceR c w + 1 = s + 1) :=
      Finset.filter_congr (fun w _ => by constructor <;> intro h <;> omega)
    calc ∑ w ∈ (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sourceR c w = s), (1 : ℝ) / ((sourceR c w + 1 : ℕ) : ℝ) ^ 2
        = ∑ w ∈ (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sourceR c w = s), (1 : ℝ) / ((s + 1 : ℕ) : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2])
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hf]; ring
  have hcnt : ∀ s ∈ Finset.range (h - c + 1),
      ((((sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
          (fun w => sourceR c w + 1 = s + 1)).card : ℕ) : ℝ) ≤
        (8 * (k : ℝ) * ((k : ℝ) + 1) * (2 * (h : ℝ) + 1) ^ (k - 1)) * ((s + 1 : ℕ) : ℝ) := by
    intro s hs
    rw [Finset.mem_range] at hs
    have hf : (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
        (fun w => sourceR c w + 1 = s + 1) =
        (sourceAnnComplRD h c).filter (fun w => sourceR c w = s) :=
      Finset.filter_congr (fun w _ => by constructor <;> intro h <;> omega)
    rw [hf]
    refine (complRD_fiber_card_le hk s (by omega)).trans_eq ?_
    push_cast; ring
  calc ∑ w ∈ (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)),
        (1 : ℝ) / ((sourceR c w + 1 : ℕ) : ℝ) ^ 2
      = ∑ s ∈ Finset.range (h - c + 1),
          ∑ w ∈ (sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sourceR c w = s), (1 : ℝ) / ((sourceR c w + 1 : ℕ) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ s ∈ Finset.range (h - c + 1), ((((sourceAnnComplRD h c :
            Finset (Fin (k + 1) → ℤ)).filter (fun w => sourceR c w + 1 = s + 1)).card : ℕ) :
            ℝ) / ((s + 1 : ℕ) : ℝ) ^ 2 :=
        Finset.sum_congr rfl hinner
    _ ≤ _ := rd_count_template (M := h - c + 1) _ (by positivity)
        (fun t => ((((sourceAnnComplRD h c : Finset (Fin (k + 1) → ℤ)).filter
            (fun w => sourceR c w + 1 = t)).card : ℕ) : ℝ)) hcnt

end NearCritical.AppendixVariance
