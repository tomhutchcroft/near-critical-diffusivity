module

public import NearCritical.SplitCrossDirectPunctured

/-! Lower bound for a tree edge in its punctured tube (item C of the direct
proof of `SplitCrossInput`).

`edge_lower_of_avoid`: let `S` be the tube, `Rm` the finite set of removed
vertices, `a, b` the two tips and `e' = a + ρ e_i`, `e'' = b + ρ e_j` the
points at distance `ρ` further out on the rays. If both ray segments lie in
`S \ Rm`, the unpunctured two-point function satisfies `c ≤ τ_S(e', e'')`, and
the BK avoidance sum `Σ_{w ∈ Rm} τ_S(e', w) τ_S(w, e'')` is at most `c / 2`,
then

  `p^(2ρ) · c / 2 ≤ τ_{S \ Rm}(a, b)`.

Harris joins the two open segments to the punctured connection.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ}

lemma conn_symm (S : Set (Vertex d)) (x y : Vertex d) :
    connectionToSetEvent S x {y} = connectionToSetEvent S y {x} := by
  ext ω
  constructor
  · rintro ⟨hx, z, hz, hzS, hreach⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hzS, x, rfl, hx, hreach.symm⟩
  · rintro ⟨hy, z, hz, hzS, hreach⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hzS, y, rfl, hy, hreach.symm⟩

theorem edge_lower_of_avoid (p : unitInterval) (S : Set (Vertex d)) (Rm : Finset (Vertex d))
    (a b : Vertex d) (i j : Fin d) (ρ : ℕ)
    (hrayA : ∀ k ≤ ρ, rayPt a i k ∈ S \ (Rm : Set (Vertex d)))
    (hrayB : ∀ k ≤ ρ, rayPt b j k ∈ S \ (Rm : Set (Vertex d)))
    {c : ℝ}
    (hlow : c ≤ (percolation d p).real
      (connectionToSetEvent S (rayPt a i ρ) {rayPt b j ρ}))
    (herr : ∑ w ∈ Rm, (percolation d p).real (connectionToSetEvent S (rayPt a i ρ) {w}) *
        (percolation d p).real (connectionToSetEvent S w {rayPt b j ρ}) ≤ c / 2) :
    (p : ℝ) ^ (2 * ρ) * (c / 2) ≤
      (percolation d p).real (connectionToSetEvent (S \ (Rm : Set (Vertex d))) a {b}) := by
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hmid : c / 2 ≤ (percolation d p).real
      (connectionToSetEvent (S \ (Rm : Set (Vertex d))) (rayPt a i ρ) {rayPt b j ρ}) := by
    have h := conn_avoid_lower p S Rm (rayPt a i ρ) (rayPt b j ρ)
    linarith
  have hA := conn_ray_ge p (S \ (Rm : Set (Vertex d))) a i ρ hrayA
  have hB := conn_ray_ge p (S \ (Rm : Set (Vertex d))) b j ρ hrayB
  rw [conn_symm] at hB
  have h1 := conn_harris_concat p (S \ (Rm : Set (Vertex d))) a (rayPt a i ρ) (rayPt b j ρ)
  have h2 := conn_harris_concat p (S \ (Rm : Set (Vertex d))) a (rayPt b j ρ) b
  have hpρ : (0 : ℝ) ≤ (p : ℝ) ^ ρ := pow_nonneg hp0 ρ
  rcases le_or_gt c 0 with hc | hc
  · have hnonpos : (p : ℝ) ^ (2 * ρ) * (c / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hp0 _) (by linarith)
    exact hnonpos.trans measureReal_nonneg
  · have hstep1 : (p : ℝ) ^ ρ * (c / 2) ≤ (percolation d p).real
        (connectionToSetEvent (S \ (Rm : Set (Vertex d))) a {rayPt b j ρ}) :=
      (mul_le_mul hA hmid (by linarith) measureReal_nonneg).trans h1
    have hstep2 : (p : ℝ) ^ ρ * (c / 2) * (p : ℝ) ^ ρ ≤ (percolation d p).real
        (connectionToSetEvent (S \ (Rm : Set (Vertex d))) a {b}) :=
      (mul_le_mul hstep1 hB hpρ measureReal_nonneg).trans h2
    calc (p : ℝ) ^ (2 * ρ) * (c / 2) = (p : ℝ) ^ ρ * (c / 2) * (p : ℝ) ^ ρ := by
          rw [two_mul, pow_add]
          ring
      _ ≤ _ := hstep2

end NearCritical.SplitCrossDirect
end
