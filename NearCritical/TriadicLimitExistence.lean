module

public import NearCritical.TriadicDirichletLimit
public import NearCritical.Section10CubeRemainder

/-! Existence of the homogenized full-Dirichlet coefficient: discharge of the
CONVERGENCE content of `TriadicDirichletLimitInput`.

The actual annealed full-Dirichlet mean `f(M)` of the cube `[0, M-1]^d` satisfies
* exact tiling subadditivity `f(qL) ≤ f(L)` (`annealedFull_grid_subadditivity`);
* the remainder bound `f(M) ≤ f(qL) + |[0,M)^d \ [0,qL)^d| / M^d`
  (`Section10.annealedFull_rectangle_remainder_fraction`).
With `q = ⌊M/L⌋` this gives `f(M) ≤ f(L) + d L / M`, hence (multidimensional
Fekete) `f(M) → inf_L f(L)` as `M → ∞`. Every triadic sequence of odd cubes
has side tending to infinity, so all of them converge to the SAME limit
`fullCubeLimit d i p`, for every `p ∈ [0,1]` (in particular every `p > p_c`).

This removes the named convergence input; it does NOT identify the limit with a
random-walk diffusivity (Einstein relation / lem.basic identification remain). -/

@[expose] public section
noncomputable section

namespace NearCritical

open Filter Finset
open scoped Topology

/-- The cube `[0, M-1]^d`. -/
def zeroCube (d M : ℕ) : Finset (Vertex d) :=
  latticeRectangle 0 (fun _ => (M : ℤ) - 1)

lemma zeroCube_card (d M : ℕ) : (zeroCube d M).card = M ^ d := by
  classical
  unfold zeroCube latticeRectangle
  rw [Fintype.card_piFinset]
  simp [Int.card_Icc]

lemma gridCell_const_zero (d L : ℕ) :
    gridCell (fun _ : Fin d => (L : ℤ)) 0 = zeroCube d L := by
  unfold gridCell zeroCube
  congr 1 <;> funext k <;> simp

lemma zeroCube_mul_le {d : ℕ} (i : Fin d) {L q : ℕ} (hL : 0 < L) (hq : 0 < q)
    (p : unitInterval) :
    annealedFull (zeroCube d (q * L)) i (p : ℝ) ≤ annealedFull (zeroCube d L) i (p : ℝ) := by
  have H := annealedFull_grid_subadditivity i (fun _ : Fin d => (L : ℤ))
    (fun _ : Fin d => (q : ℤ)) (fun _ => by exact_mod_cast hL)
    (fun _ => by exact_mod_cast hq) p
  have e : zeroCube d (q * L) = latticeRectangle 0 (fun _ : Fin d => (q : ℤ) * (L : ℤ) - 1) := by
    unfold zeroCube
    congr 1
    all_goals (funext k; push_cast; try ring)
  rw [e, ← gridCell_const_zero]
  exact H

lemma zeroCube_subset {d a b : ℕ} (hab : a ≤ b) : zeroCube d a ⊆ zeroCube d b := by
  intro x hx
  unfold zeroCube at hx ⊢
  rw [mem_latticeRectangle] at hx ⊢
  intro j
  have := hx j
  simp only [Pi.zero_apply] at this ⊢
  have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
  constructor <;> omega

/-- Elementary volume bound: `1 - x^d ≤ d (1 - x)` for `0 ≤ x ≤ 1`. -/
lemma one_sub_pow_le {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : 1 - x ^ d ≤ d * (1 - x) := by
  have h := one_add_mul_le_pow (a := x - 1) (by linarith) d
  have : 1 + (x - 1) = x := by ring
  rw [this] at h
  linarith

/-- Quantitative subadditivity with remainder: `f(M) ≤ f(L) + d L / M`. -/
theorem annealedFull_zeroCube_le {d : ℕ} (i : Fin d) {L M : ℕ} (hL : 0 < L) (hLM : L ≤ M)
    (p : unitInterval) :
    annealedFull (zeroCube d M) i (p : ℝ) ≤
      annealedFull (zeroCube d L) i (p : ℝ) + (d : ℝ) * L / M := by
  have hM : 0 < M := lt_of_lt_of_le hL hLM
  set q := M / L with hqdef
  have hq : 0 < q := Nat.div_pos hLM hL
  have hqL : q * L ≤ M := Nat.div_mul_le_self M L
  have hrem : M < q * L + L := by
    have h1 := Nat.div_add_mod M L
    have h2 := Nat.mod_lt M hL
    rw [← hqdef] at h1
    linarith [Nat.mul_comm L q]
  have hsub := zeroCube_subset (d := d) hqL
  have hvalid : ∀ k : Fin d, (0 : Vertex d) k ≤ ((q * L : ℕ) : ℤ) - 1 := by
    intro k
    have h1 : 1 ≤ q * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hq.ne' hL.ne')
    have h1' : (1 : ℤ) ≤ ((q * L : ℕ) : ℤ) := by exact_mod_cast h1
    simp only [Pi.zero_apply]
    linarith
  have H := Section10.annealedFull_rectangle_remainder_fraction (zeroCube d M) 0
    (fun _ : Fin d => ((q * L : ℕ) : ℤ) - 1) hvalid hsub p i
  change annealedFull (zeroCube d M) i (p : ℝ) ≤ annealedFull (zeroCube d (q * L)) i (p : ℝ) +
      ((zeroCube d M \ zeroCube d (q * L)).card : ℝ) / ((zeroCube d M).card : ℝ) at H
  rw [card_sdiff_of_subset hsub, zeroCube_card, zeroCube_card] at H
  have hpow : (q * L) ^ d ≤ M ^ d := Nat.pow_le_pow_left hqL d
  rw [Nat.cast_sub hpow] at H
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hfrac : (((M ^ d : ℕ) : ℝ) - ((q * L) ^ d : ℕ)) / ((M ^ d : ℕ) : ℝ) ≤ (d : ℝ) * L / M := by
    push_cast
    have hMd : (0 : ℝ) < (M : ℝ) ^ d := pow_pos hMr d
    have hx0 : (0 : ℝ) ≤ (q : ℝ) * L / M := by positivity
    have key := one_sub_pow_le hx0 d
    rw [div_pow] at key
    rw [sub_div, div_self hMd.ne']
    refine key.trans ?_
    have hremr : (M : ℝ) < (q : ℝ) * L + L := by exact_mod_cast hrem
    rw [one_sub_div hMr.ne', mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    apply div_le_div_of_nonneg_right _ hMr.le
    linarith
  have hmul := zeroCube_mul_le i hL hq p
  linarith

/-- The homogenized full-Dirichlet coefficient: infimum of the actual cube means. -/
def fullCubeLimit (d : ℕ) (i : Fin d) (p : ℝ) : ℝ :=
  ⨅ L : ℕ, annealedFull (zeroCube d (L + 1)) i p

theorem tendsto_annealedFull_zeroCube {d : ℕ} (i : Fin d) (p : unitInterval) :
    Tendsto (fun M => annealedFull (zeroCube d M) i (p : ℝ)) atTop
      (𝓝 (fullCubeLimit d i (p : ℝ))) := by
  have hbdd : BddBelow (Set.range fun L : ℕ => annealedFull (zeroCube d (L + 1)) i (p : ℝ)) :=
    ⟨0, by rintro _ ⟨L, rfl⟩; exact annealedFull_nonneg _ i p.2.1 p.2.2⟩
  rw [tendsto_order]
  constructor
  · intro a ha
    rw [eventually_atTop]
    refine ⟨1, fun M hM => ?_⟩
    obtain ⟨L, rfl⟩ : ∃ L, M = L + 1 := ⟨M - 1, by omega⟩
    exact lt_of_lt_of_le ha (ciInf_le hbdd L)
  · intro b hb
    obtain ⟨L, hL⟩ := exists_lt_of_ciInf_lt hb
    set δ := b - annealedFull (zeroCube d (L + 1)) i (p : ℝ) with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((d : ℝ) * (L + 1 : ℕ) / δ)
    rw [eventually_atTop]
    refine ⟨max (L + 1) N, fun M hM => ?_⟩
    have hLM : L + 1 ≤ M := le_of_max_le_left hM
    have hNM : N ≤ M := le_of_max_le_right hM
    have h := annealedFull_zeroCube_le i (by omega : 0 < L + 1) hLM p
    have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hNMr : (N : ℝ) ≤ M := by exact_mod_cast hNM
    have h1 : (d : ℝ) * (L + 1 : ℕ) / δ < M := lt_of_lt_of_le hN hNMr
    have h2 : (d : ℝ) * (L + 1 : ℕ) < M * δ := by
      rw [div_lt_iff₀ hδpos] at h1
      linarith
    have h3 : (d : ℝ) * (L + 1 : ℕ) / M < δ := by
      rw [div_lt_iff₀ hMr]
      linarith
    linarith

lemma annealedFull_centeredBox_eq_zeroCube {d : ℕ} (i : Fin d) (p : unitInterval) (R : ℕ) :
    annealedFull (centeredBox d R) i (p : ℝ) = annealedFull (zeroCube d (2 * R + 1)) i (p : ℝ) := by
  have hw : oddGridWidths (fun _ : Fin d => R) = fun _ => (((2 * R + 1 : ℕ)) : ℤ) := by
    funext j
    simp only [oddGridWidths]
    push_cast
    try ring
  have h := annealedFull_odd_grid_centered (fun _ : Fin d => R) i p
  rw [hw, gridCell_const_zero] at h
  exact h.symm

/-- DISCHARGE of the convergence input: the actual full-Dirichlet cube means along
every triadic sequence converge to the same coefficient `fullCubeLimit d i p`. -/
theorem triadicDirichletLimitInput_fullCubeLimit (d : ℕ) (i : Fin d) :
    TriadicDirichletLimitInput d i (fullCubeLimit d i) := by
  intro p _ r
  have h3 : ∀ m : ℕ, m ≤ 3 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : 0 < 3 ^ m := by positivity
      rw [pow_succ]
      linarith
  have htend : Tendsto (fun m : ℕ => 3 ^ m * (2 * r + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun m => ?_) tendsto_id
    have := h3 m
    show m ≤ 3 ^ m * (2 * r + 1)
    nlinarith
  have heq : (fun m => annealedFull (centeredBox d (triadicCubeRadius r m)) i (p : ℝ)) =
      (fun M => annealedFull (zeroCube d M) i (p : ℝ)) ∘ (fun m : ℕ => 3 ^ m * (2 * r + 1)) := by
    funext m
    simp only [Function.comp, annealedFull_centeredBox_eq_zeroCube, triadicCubeRadius_side]
  rw [heq]
  exact (tendsto_annealedFull_zeroCube i p).comp htend

/-- Any coefficient satisfying the (former) convergence input IS the constructed
`fullCubeLimit` above criticality: conditional results about `κ` are results
about the actual homogenized coefficient. -/
theorem TriadicDirichletLimitInput.eq_fullCubeLimit {d : ℕ} {i : Fin d} {κ : ℝ → ℝ}
    (h : TriadicDirichletLimitInput d i κ) (p : unitInterval) (hp : criticalPoint d < p) :
    κ (p : ℝ) = fullCubeLimit d i (p : ℝ) :=
  tendsto_nhds_unique (h p hp 0) (triadicDirichletLimitInput_fullCubeLimit d i p hp 0)

end NearCritical
