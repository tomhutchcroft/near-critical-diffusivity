module

public import NearCritical.SlabPioneerFirstHit
public import NearCritical.AppendixErrBoundaryUniform

/-! The nearest-neighbour slab first-moment lower bound (source
lem.Nn_moments, second half) derived from the cited Panis half-space two-point
upper bound and the cited lower bound `c ≤ psi_{p_c}(H_n)` of source
eq.expansion_2.

A half-space path from the boundary to height `n` first reaches that height
through a path in the slab, so `psi(H_n) ≤ E[N_n] · M_n`, where `M_n` is the
largest total half-space connection mass from a vertex at height `n` to its own
layer (`halfSpacePioneerMass_le_slab_mul_plane`). The Panis kernel at two
points of height `n` is dominated by a decreasing radial kernel whose sum over
the layer telescopes to at most a constant times `n + 1`.

 -/
@[expose] public section
noncomputable section
namespace NearCritical
open AppendixVariance MeasureTheory Section8
open scoped Classical ENNReal

/-- Decreasing radial majorant of the Panis kernel between two points at
height `n` in dimension `k + 1`. -/
def planeKernel (k : ℕ) (n : ℝ) (j : ℕ) : ℝ :=
  4 * (n + 1) ^ 2 / (((j : ℝ) + 1) ^ (k - 1) * (((j : ℝ) + n + 1) * ((j : ℝ) + n + 2)))

theorem planeKernel_nonneg (k : ℕ) {n : ℝ} (hn : 0 ≤ n) (j : ℕ) : 0 ≤ planeKernel k n j := by
  unfold planeKernel
  positivity

theorem planeKernel_antitone (k : ℕ) {n : ℝ} (hn : 0 ≤ n) : Antitone (planeKernel k n) := by
  intro a b hab
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  unfold planeKernel
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _) _
    (by positivity) (by positivity)
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

theorem add_one_pow_le_two_pow (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
  rcases le_total x 1 with h | h
  · calc (x + 1) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + x ^ m) :=
        le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hx m])
  · calc (x + 1) ^ m ≤ (2 * x) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * x ^ m := mul_pow 2 x m
      _ ≤ 2 ^ m * (1 + x ^ m) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem min_sq_mul_le {n L : ℝ} (hn : 0 ≤ n) (hL : 0 ≤ L) :
    (1 + min n L) * (1 + min n L) * ((L + n + 1) * (L + n + 2)) ≤
      4 * (n + 1) ^ 2 * (L + 1) ^ 2 := by
  rcases le_total n L with h | h
  · rw [min_eq_left h]
    have hq : (L + n + 1) * (L + n + 2) ≤ (2 * (L + 1)) * (2 * (L + 1)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    calc (1 + n) * (1 + n) * ((L + n + 1) * (L + n + 2))
        ≤ (1 + n) * (1 + n) * ((2 * (L + 1)) * (2 * (L + 1))) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring
  · rw [min_eq_right h]
    have hq : (L + n + 1) * (L + n + 2) ≤ (2 * (n + 1)) * (2 * (n + 1)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    calc (1 + L) * (1 + L) * ((L + n + 1) * (L + n + 2))
        ≤ (1 + L) * (1 + L) * ((2 * (n + 1)) * (2 * (n + 1))) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring

/-- The Panis kernel at two points of depth `n` is at most the radial
majorant. -/
theorem panis_kernel_le_planeKernel {k : ℕ} (hk : 1 ≤ k) {C n : ℝ} (hC : 0 ≤ C)
    (hn : 0 ≤ n) (j : ℕ) :
    C * ((1 + min n (j : ℝ)) * (1 + min n (j : ℝ))) / (1 + (j : ℝ) ^ (k + 1)) ≤
      2 ^ (k + 1) * C * planeKernel k n j := by
  have hL : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hden : (0 : ℝ) < 1 + (j : ℝ) ^ (k + 1) := by positivity
  have hQ : (0 : ℝ) < ((j : ℝ) + 1) ^ (k - 1) * (((j : ℝ) + n + 1) * ((j : ℝ) + n + 2)) := by
    positivity
  have hpow : ((j : ℝ) + 1) ^ (k + 1) = ((j : ℝ) + 1) ^ (k - 1) * ((j : ℝ) + 1) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hmain : C * ((1 + min n (j : ℝ)) * (1 + min n (j : ℝ))) *
      (((j : ℝ) + 1) ^ (k - 1) * (((j : ℝ) + n + 1) * ((j : ℝ) + n + 2))) ≤
      2 ^ (k + 1) * C * (4 * (n + 1) ^ 2) * (1 + (j : ℝ) ^ (k + 1)) := by
    calc _ = C * ((j : ℝ) + 1) ^ (k - 1) * ((1 + min n (j : ℝ)) * (1 + min n (j : ℝ)) *
            (((j : ℝ) + n + 1) * ((j : ℝ) + n + 2))) := by ring
      _ ≤ C * ((j : ℝ) + 1) ^ (k - 1) * (4 * (n + 1) ^ 2 * ((j : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (min_sq_mul_le hn hL) (by positivity)
      _ = C * (4 * (n + 1) ^ 2) * ((j : ℝ) + 1) ^ (k + 1) := by rw [hpow]; ring
      _ ≤ C * (4 * (n + 1) ^ 2) * (2 ^ (k + 1) * (1 + (j : ℝ) ^ (k + 1))) :=
          mul_le_mul_of_nonneg_left (add_one_pow_le_two_pow (k + 1) hL) (by positivity)
      _ = _ := by ring
  unfold planeKernel
  rw [div_le_iff₀ hden, ← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ hQ]
  exact hmain

/-- The shell sum of the radial majorant telescopes. -/
theorem planeKernel_shell_sum_le {k : ℕ} {n : ℝ} (hn : 0 ≤ n) (m : ℕ) :
    ∑ j ∈ Finset.range m,
        2 * (k : ℝ) * 3 ^ (k - 1) * ((j + 1 : ℕ) : ℝ) ^ (k - 1) * planeKernel k n j ≤
      2 * (k : ℝ) * 3 ^ (k - 1) * (4 * (n + 1)) := by
  let t : ℕ → ℝ := fun j => 4 * (n + 1) ^ 2 / ((j : ℝ) + n + 1)
  have hterm : ∀ j : ℕ,
      2 * (k : ℝ) * 3 ^ (k - 1) * ((j + 1 : ℕ) : ℝ) ^ (k - 1) * planeKernel k n j =
        2 * (k : ℝ) * 3 ^ (k - 1) * (t j - t (j + 1)) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : ((j : ℝ) + 1) ^ (k - 1) ≠ 0 := by positivity
    have h2 : (j : ℝ) + n + 1 ≠ 0 := by positivity
    have h3 : (j : ℝ) + n + 2 ≠ 0 := by positivity
    have h4 : (j : ℝ) + 1 + n + 1 ≠ 0 := by positivity
    simp only [t, planeKernel]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, Finset.sum_range_sub']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have htm : 0 ≤ t m := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [t]
    positivity
  have ht0 : t 0 = 4 * (n + 1) := by
    have : n + 1 ≠ 0 := by positivity
    simp only [t, Nat.cast_zero, zero_add]
    field_simp
  linarith

/-- The constant in the same-height half-space mass bound. -/
def planeMassConst (k : ℕ) (C : ℝ) : ℝ :=
  2 ^ (k + 1) * C * (2 * (k : ℝ) * 3 ^ (k - 1) * 4)

theorem coordinateHalfSpace_zero_true {d : ℕ} (i : Fin d) :
    coordinateHalfSpace i (0 : ℤ) true = {z : Vertex d | 0 ≤ z i} := by
  ext z
  simp [coordinateHalfSpace, coordinateDepth]

/-- Finite form of the same-height half-space mass bound: from a vertex at
height `n`, the half-space connection probabilities to any finite set of
vertices at the same height sum to at most a constant times `n + 1`. -/
theorem sameHeight_halfSpace_sum_le {k : ℕ} (hk : 1 ≤ k) {C : ℝ} (hC : 0 ≤ C)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C) (i : Fin (k + 1)) (n : ℕ)
    (u : Vertex (k + 1)) (hu : u i = (n : ℤ)) (s : Finset (Vertex (k + 1))) :
    ∑ y ∈ s, (if y i = (n : ℤ) then (percolation (k + 1) (criticalPoint (k + 1))).real
        (connectionToSetEvent {z | 0 ≤ z i} u {y}) else 0) ≤
      planeMassConst k C * ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  let F := s.filter (fun y => y i = (n : ℤ))
  let R : ℕ := F.sup (linfDist u)
  have hpoint : ∀ y ∈ F, (percolation (k + 1) (criticalPoint (k + 1))).real
      (connectionToSetEvent {z | 0 ≤ z i} u {y}) ≤
      2 ^ (k + 1) * C * planeKernel k n (linfDist u y) := by
    intro y hy
    have hyi : y i = (n : ℤ) := (Finset.mem_filter.mp hy).2
    have huH : u ∈ coordinateHalfSpace i (0 : ℤ) true := by
      rw [coordinateHalfSpace_zero_true]
      change 0 ≤ u i
      rw [hu]
      exact Int.natCast_nonneg n
    have hyH : y ∈ coordinateHalfSpace i (0 : ℤ) true := by
      rw [coordinateHalfSpace_zero_true]
      change 0 ≤ y i
      rw [hyi]
      exact Int.natCast_nonneg n
    have hp := panis i 0 true u y huH hyH
    have hdu : coordinateDepth i 0 true u = (n : ℝ) := by simp [coordinateDepth, hu]
    have hdy : coordinateDepth i 0 true y = (n : ℝ) := by simp [coordinateDepth, hyi]
    rw [coordinateHalfSpace_zero_true, hdu, hdy, ← linfDist_cast_eq_latticeDistance] at hp
    exact hp.trans (panis_kernel_le_planeKernel hk hC hn _)
  rw [← Finset.sum_filter]
  calc ∑ y ∈ F, (percolation (k + 1) (criticalPoint (k + 1))).real
          (connectionToSetEvent {z | 0 ≤ z i} u {y})
      ≤ ∑ y ∈ F, 2 ^ (k + 1) * C * planeKernel k n (linfDist u y) :=
        Finset.sum_le_sum hpoint
    _ = 2 ^ (k + 1) * C * ∑ y ∈ F, planeKernel k n (linfDist u y) := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ (k + 1) * C * (2 * (k : ℝ) * 3 ^ (k - 1) * (4 * ((n : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (plane_radial_sum_le_projection F i u R
          (fun y hy => ((Finset.mem_filter.mp hy).2).trans hu.symm)
          (fun y hy => Finset.le_sup (f := linfDist u) hy)
          (planeKernel k n) (planeKernel_nonneg k hn) (planeKernel_antitone k hn)).trans ?_
        exact (radial_sum_shell_bound hk _ R (planeKernel k n)
          (planeKernel_nonneg k hn)).trans (planeKernel_shell_sum_le hn (R + 1))
    _ = _ := by unfold planeMassConst; ring

/-- Same-height half-space mass bound in the form consumed by
`halfSpacePioneerMass_le_slab_mul_plane`. -/
theorem sameHeight_halfSpace_mass_le {k : ℕ} (hk : 1 ≤ k) {C : ℝ} (hC : 0 ≤ C)
    (panis : PanisHalfSpaceTwoPointUpper (k + 1) C) (i : Fin (k + 1)) (n : ℕ)
    (u : Vertex (k + 1)) (hu : u i = (n : ℤ)) :
    (∑' y : Vertex (k + 1), if y i = (n : ℤ) then percolation (k + 1) (criticalPoint (k + 1))
        (connectionToSetEvent {z | 0 ≤ z i} u {y}) else 0) ≤
      ENNReal.ofReal (planeMassConst k C * ((n : ℝ) + 1)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hfin : ∀ y ∈ s, (if y i = (n : ℤ) then percolation (k + 1) (criticalPoint (k + 1))
      (connectionToSetEvent {z | 0 ≤ z i} u {y}) else 0) ≠ ⊤ := by
    intro y _
    split_ifs
    · exact measure_ne_top _ _
    · exact ENNReal.zero_ne_top
  have hB : 0 ≤ planeMassConst k C * ((n : ℝ) + 1) := by
    unfold planeMassConst
    positivity
  rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sum_ne_top.mpr hfin) hB,
    ENNReal.toReal_sum hfin]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun y _ => ?_)
    (sameHeight_halfSpace_sum_le hk hC panis i n u hu s)
  split_ifs
  · rfl
  · rfl

/-- One height: the slab first moment is at least `c / (2 (K + 1) n)`. -/
theorem slabPioneerMass_lower_of_halfSpace {k : ℕ} (hk : 1 ≤ k) {C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c) (panis : PanisHalfSpaceTwoPointUpper (k + 1) C) (i : Fin (k + 1))
    (n : ℕ) (hn : 1 ≤ n)
    (hlow : ENNReal.ofReal c ≤ halfSpacePioneerMass (criticalPoint (k + 1)) i (n : ℤ)) :
    ENNReal.ofReal (c / (2 * (planeMassConst k C + 1)) / (n : ℝ)) ≤
      slabPioneerMass (criticalPoint (k + 1)) i 0 (n : ℤ) 0 (n : ℤ) := by
  have hK : 0 ≤ planeMassConst k C := by
    unfold planeMassConst
    positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let M : ℝ := (planeMassConst k C + 1) * ((n : ℝ) + 1)
  have hM : 0 < M := by positivity
  have hfirst := halfSpacePioneerMass_le_slab_mul_plane (criticalPoint (k + 1)) i hn
    (ENNReal.ofReal M) (fun u hu =>
      (sameHeight_halfSpace_mass_le hk hC panis i n u hu).trans
        (ENNReal.ofReal_le_ofReal (by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith)))
  have hdiv : ENNReal.ofReal c / ENNReal.ofReal M ≤
      slabPioneerMass (criticalPoint (k + 1)) i 0 (n : ℤ) 0 (n : ℤ) :=
    ENNReal.div_le_of_le_mul (hlow.trans hfirst)
  rw [← ENNReal.ofReal_div_of_pos hM] at hdiv
  refine (ENNReal.ofReal_le_ofReal ?_).trans hdiv
  rw [div_div]
  apply div_le_div_of_nonneg_left hc.le hM
  have : (planeMassConst k C + 1) * ((n : ℝ) + 1) ≤ (planeMassConst k C + 1) * (2 * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc M ≤ (planeMassConst k C + 1) * (2 * (n : ℝ)) := this
    _ = _ := by ring

/-- **Slab first-moment lower bound** (`E[N_n] ≥ c / n`, source lem.Nn_moments)
from the Panis half-space two-point upper bound and the lower bound
`c ≤ psi_{p_c}(H_n)` of source eq.expansion_2. The conclusion is the `hslab`
premise of the main result wrappers. -/
theorem slab_first_moment_lower {d : ℕ} (hd : 2 ≤ d) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hlow : ∀ (i : Fin d) (n : ℕ), 1 ≤ n →
      ENNReal.ofReal c ≤ halfSpacePioneerMass (criticalPoint d) i (n : ℤ)) :
    ∃ cSlab : ℝ, 0 < cSlab ∧ ∀ (i : Fin d) (h : ℕ), 1 ≤ h →
      ENNReal.ofReal (cSlab / (h : ℝ)) ≤
        slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hK : 0 ≤ planeMassConst k C := by
    unfold planeMassConst
    positivity
  exact ⟨c / (2 * (planeMassConst k C + 1)), by positivity, fun i h hh =>
    slabPioneerMass_lower_of_halfSpace hk hC hc panis i h hh (hlow i h hh)⟩

end NearCritical
