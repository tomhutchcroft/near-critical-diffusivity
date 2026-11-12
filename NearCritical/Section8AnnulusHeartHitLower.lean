module

public import NearCritical.Section8CubeOneSided
public import NearCritical.Section8FiveDiagrams
public import NearCritical.Section8PxinfCLower
public import NearCritical.Section8YSecondMomentAtPc

/-! The heart-hit lower bound with the actual restricted connection kernels. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance MeasureTheory
open scoped Classical

private theorem boundary_root_connection_shell_le {d R : ℕ} (hd : 1 ≤ d)
    (C : ℝ) (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper d C)
    (x u : Vertex d) (hx : x ∈ centeredBox d R) (hu : u ∈ centeredBox d R)
    (hxR : linfDist 0 x = R) :
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (centeredBox d R : Set (Vertex d)) x {u}) ≤
      ((2 * C) * (2 : ℝ) ^ (d - 1)) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 1) := by
  let M := max 1 (latticeDistance x u)
  let S : ℝ := (linfDist x u + 1 : ℕ)
  have hx' : latticeDistance 0 x = R := by rw [← linfDist_cast_eq_latticeDistance, hxR]
  have h := cube_one_sided_connection_le (n := R) hd C hC panis
    (centeredBox d R : Set (Vertex d)) (fun _ hz => hz) x u hx hu
  rw [hx', sub_self, add_zero, mul_one] at h
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hS : 0 < S := by dsimp [S]; positivity
  have hSM : S ≤ 2 * M := by
    dsimp [S]
    rw [Nat.cast_add, Nat.cast_one, linfDist_cast_eq_latticeDistance]
    have h₁ : 1 ≤ M := le_max_left _ _
    have h₂ : latticeDistance x u ≤ M := le_max_right _ _
    linarith
  have hexp : (1 : ℝ) - (d : ℝ) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [hexp, Real.rpow_neg hM.le, Real.rpow_natCast] at h
  apply h.trans
  rw [inv_eq_one_div, ← mul_div_assoc, mul_one]
  apply (div_le_div_iff₀ (pow_pos hM _) (pow_pos hS _)).mpr
  calc
    _ ≤ (2 * C) * (2 * M) ^ (d - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS.le hSM _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- A uniform first-moment box lower bound implies the source lower rate
for the actual annulus hitting probability. The BK and upper two-point
inputs to the second moment are instantiated here. -/
theorem annulusG_lower_at_pc_of_box_lower (e : ℕ) (asymp : TwoPointAsymptotics (e + 7))
    (C : ℝ) (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (c : ℝ) (hc : 0 < c)
    (hbox : ∀ (i : Fin (e + 7)) (R : ℕ) (x : Vertex (e + 7)), 1 ≤ R →
      (x i = -(R : ℤ) ∨ x i = (R : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (R : ℝ) - (1 / 2 : ℝ) * (R : ℝ)) →
      ∀ y ∈ centeredBox (e + 7) R, R ≤ 2 * (R - linfDist 0 y) →
        c / (R : ℝ) ^ (e + 6) ≤ (percolation (e + 7) (criticalPoint (e + 7))).real
          (connectionToSetEvent (centeredBox (e + 7) R : Set (Vertex (e + 7))) x {y})) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (i : Fin (e + 7)) (R s : ℕ) (x : Vertex (e + 7)),
      1 ≤ s → 5 * s ≤ R → linfDist 0 x = R →
      (x i = -(R : ℤ) ∨ x i = (R : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (R : ℝ) - (1 / 2 : ℝ) * (R : ℝ)) →
      κ * ((s : ℝ) / (R : ℝ)) ^ (e + 3) / (R : ℝ) ^ 3 ≤
        annulusG (criticalPoint (e + 7)) (centeredBox (e + 7) R) (centeredBox (e + 7) s) x := by
  obtain ⟨C1, hC1, hTP⟩ := twoPointBound_of_asymptotics (d := e + 7) (by omega) asymp
  let C0 : ℝ := (2 * C) * (2 : ℝ) ^ (e + 6)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  obtain ⟨κ, hκ, hlow⟩ := PxinfC_lower_of_inputs e hc hC0 hC1.le
  refine ⟨κ, hκ, ?_⟩
  intro i R s x hs h5s hxR hface hmargin
  let Q := centeredBox (e + 7) R
  let H := centeredBox (e + 7) s
  let p := criticalPoint (e + 7)
  let P (a b : Vertex (e + 7)) := (percolation (e + 7) p).real
    (connectionToSetEvent (Q : Set (Vertex (e + 7))) a {b})
  have hR : 1 ≤ R := by omega
  have hxQ : x ∈ Q := by
    change x ∈ centeredBox (e + 7) R
    rw [← appendix_cube_eq_centeredBox, mem_cube_iff_dist_aux, hxR]
  have hxH : x ∉ H := by
    change x ∉ centeredBox (e + 7) s
    rw [← appendix_cube_eq_centeredBox, mem_cube_iff_dist_aux, hxR]
    omega
  have hxD : x ∈ heartAnnulus Q H := Finset.mem_sdiff.mpr ⟨hxQ, fun h => hxH (Finset.mem_sdiff.mp h).1⟩
  have hHQ : H ⊆ Q := by
    intro v hv
    apply mem_centeredBox.mpr
    intro j
    have hj := mem_centeredBox.mp hv j
    constructor <;> omega
  have hfirst (u : Vertex (e + 7)) (hu : u ∈ Q) : P x u ≤ C0 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6) := by
    simpa only [P, C0, show e + 7 - 1 = e + 6 by omega] using
      boundary_root_connection_shell_le (by omega : 1 ≤ e + 7) C hC panis x u hxQ hu hxR
  have hsecond := restricted_twoPointBound hTP (Q : Set (Vertex (e + 7)))
  have hevent : heartEvent Q H x = {ω | x ∈ heartClusterUnion ω Q H} := by
    ext ω
    exact heartEvent_iff_union_member _ _ hHQ x ω
  rw [annulusG, annulusHit, ← heart_probability_eq_annulus p Q H x hxD, hevent]
  refine hlow p R s x (P x) P hs h5s hxR
    (fun u _ => show 0 ≤ P x u from measureReal_nonneg)
    (fun u _ v => show 0 ≤ P u v from measureReal_nonneg) ?_ hfirst ?_ (hbox i R x hR hface hmargin)
  · intro y _ z _
    refine (restricted_tripod_connection_probability_le p Q x y z).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [P, connectionToSetEvent_singleton_symm (Q : Set (Vertex (e + 7))) z u]
  · intro u _ v _
    simpa only [P, show e + 7 - 2 = e + 5 by omega] using (hsecond u v).2

end NearCritical.Section8
