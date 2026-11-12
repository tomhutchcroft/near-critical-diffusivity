module

public import NearCritical.SplitCrossMoatLoss

/-! Choosing the outward length before the star length, and bounding
the remaining moats by their finite size and macroscopic separation. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open scoped Classical

/-- First fix an outward length, then take the star length large enough.
The own-moat Green mass is uniformly small for every larger star length. -/
theorem ownMoat_green_mass_small {d : ℕ} (hd : 4 ≤ d) (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℕ, 0 < ρ ∧ ∃ R₀ : ℕ, ∀ R ≥ R₀,
      ∀ (b : Vertex d) (axes : Finset (Fin d)) (i : Fin d), i ∈ axes →
        (∑ z ∈ branchMoatVertices b axes R r, moatGreen (starTip b i (R + r + ρ)) z) ≤ ε := by
  let M : ℝ := (((2 * (r - 1) + 1) ^ d : ℕ) : ℝ)
  have hM : 0 ≤ M := by positivity
  have hD : (0 : ℝ) ≤ d := by positivity
  obtain ⟨ρ, hρ⟩ := exists_nat_gt (2 * (1 + (d : ℝ) * M) / ε)
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (2 * (d : ℝ) / ε)
  have hρR : (0 : ℝ) < (ρ : ℝ) :=
    (by positivity : 0 ≤ 2 * (1 + (d : ℝ) * M) / ε).trans_lt hρ
  have hρpos : 0 < ρ := by exact_mod_cast hρR
  refine ⟨ρ, hρpos, R₀, ?_⟩
  intro R hR b axes i hi
  have hR' : (R₀ : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hden : 0 < (R : ℝ) + (r : ℝ) := by positivity
  have hcard : (axes.card : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (show axes.card ≤ d by simpa using Finset.card_le_univ axes)
  have hterm : (axes.card : ℝ) / ((R : ℝ) + (r : ℝ)) ≤ ε / 2 := by
    have hnum : (d : ℝ) ≤ (ε / 2) * ((R : ℝ) + (r : ℝ)) := by
      have hh := (div_lt_iff₀ hε).mp (hR₀.trans_le hR')
      nlinarith [mul_nonneg hε.le hrR.le]
    exact (div_le_iff₀ hden).mpr (hcard.trans hnum)
  have htail : (1 + (d : ℝ) * M) / (ρ : ℝ) ≤ ε / 2 := by
    have hh := (div_lt_iff₀ hε).mp hρ
    exact (div_le_iff₀ hρR).mpr (by nlinarith only [hh])
  have hball : (axes.card : ℝ) * M / ((ρ : ℝ) + 1)^2 ≤ (d : ℝ) * M / (ρ : ℝ) := by
    have hsquare : (ρ : ℝ) ≤ ((ρ : ℝ) + 1)^2 := by
      nlinarith [sq_nonneg (ρ : ℝ)]
    calc
      _ ≤ (d : ℝ) * M / ((ρ : ℝ) + 1)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hM) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hD hM) hρR hsquare
  have hbase := ownMoat_green_mass_le hd b axes i hi R r ρ hr hρpos
  change _ ≤ 1 / (ρ : ℝ) + (axes.card : ℝ) / ((R : ℝ) + (r : ℝ)) +
    (axes.card : ℝ) * M / ((ρ : ℝ) + 1)^2 at hbase
  rw [add_div] at htail
  linarith

private theorem branchMoatVertices_card_le_guard {d : ℕ} (b : Vertex d)
    (axes : Finset (Fin d)) (R r : ℕ) (i : Fin d) :
    (branchMoatVertices b axes R r).card ≤ (branchGuardBonds b axes R r).card := by
  refine Finset.card_le_card_of_injOn (fun x => (x, i)) ?_ ?_
  · intro x hx
    exact Finset.mem_biUnion.mpr ⟨x, hx, (External.mem_vertexIncidentBonds _ _).mpr (Or.inl rfl)⟩
  · intro x _ y _ h
    exact congrArg Prod.fst h

/-- All moats in a family remote from an endpoint have Green mass bounded
by their uniform size times the inverse square of their distance. -/
theorem remoteMoats_green_mass_le {d : ℕ} (hd : 4 ≤ d) {ι : Type*}
    (I : Finset ι) (b : ι → Vertex d) (axes : Finset (Fin d)) (R r : ℕ)
    (x : Vertex d) {s : ℝ} (hs : 1 ≤ s)
    (hsep : ∀ j ∈ I, s + ((R + r + 1 : ℕ) : ℝ) ≤ latticeDistance x (b j)) :
    (∑ z ∈ treeMoatVertices I b axes R r, moatGreen x z) ≤
      (I.card : ℝ) *
        ((((axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d) * (2 * d)) : ℕ) : ℝ) /
        s^2 := by
  let i : Fin d := ⟨0, by omega⟩
  let M := (axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d) * (2 * d)
  have hsum (j : ι) (hj : j ∈ I) :
      (∑ z ∈ branchMoatVertices (b j) axes R r, moatGreen x z) ≤ (M : ℝ) / s^2 := by
    have hcard := (branchMoatVertices_card_le_guard (b j) axes R r i).trans
      (branchGuardBonds_card_le (b j) axes R r)
    calc
      _ ≤ ∑ _z ∈ branchMoatVertices (b j) axes R r, 1 / s^2 := by
        apply Finset.sum_le_sum
        intro z hz
        have hdist := moatVertex_dist_center_le hz i
        have htri := latticeDistance_triangle x z (b j)
        rw [latticeDistance_eq_vertex_dist z (b j)] at htri
        exact moatGreen_le_invSq hd hs (by linarith [hsep j hj])
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg s)
  unfold treeMoatVertices
  calc
    _ ≤ ∑ j ∈ I, ∑ z ∈ branchMoatVertices (b j) axes R r, moatGreen x z :=
      sum_biUnion_le_of_nonneg _ (moatGreen_nonneg x) _ _
    _ ≤ ∑ _j ∈ I, (M : ℝ) / s^2 := Finset.sum_le_sum hsum
    _ = _ := by simp [M, div_eq_mul_inv, mul_assoc]

/-- At a branch's outward start, the mass of the union splits into its
own moat and a size bound for all other moats. -/
theorem treeMoat_green_mass_le_at_outward {d : ℕ} (hd : 4 ≤ d) {ι : Type*}
    (I : Finset ι) (b : ι → Vertex d) (axes : Finset (Fin d)) (R r ρ : ℕ)
    {v : ι} (hv : v ∈ I) (i : Fin d) {s : ℝ} (hs : 1 ≤ s)
    (hsep : ∀ j ∈ I.erase v, s + ((R + r + 1 : ℕ) : ℝ) ≤
      latticeDistance (starTip (b v) i (R + r + ρ)) (b j)) :
    let x := starTip (b v) i (R + r + ρ)
    (∑ z ∈ treeMoatVertices I b axes R r, moatGreen x z) ≤
      (∑ z ∈ branchMoatVertices (b v) axes R r, moatGreen x z) +
      ((I.erase v).card : ℝ) *
        ((((axes.card * (R + r) + axes.card * (2 * (r - 1) + 1) ^ d) * (2 * d)) : ℕ) : ℝ) /
        s^2 := by
  intro x
  have hsplit : treeMoatVertices I b axes R r =
      branchMoatVertices (b v) axes R r ∪ treeMoatVertices (I.erase v) b axes R r := by
    unfold treeMoatVertices
    nth_rw 1 [← Finset.insert_erase hv]
    rw [Finset.biUnion_insert]
  rw [hsplit]
  exact (sum_union_le_of_nonneg _ (moatGreen_nonneg x) _ _).trans
    (add_le_add le_rfl (remoteMoats_green_mass_le hd (I.erase v) b axes R r x hs hsep))

end NearCritical.SplitCrossDirect
