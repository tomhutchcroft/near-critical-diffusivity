module

public import NearCritical.Section8PxinfCLower
public import NearCritical.AppendixBoxTwoPointLowerFaces

/-! Adapter: the verified `appendix_box_twopoint_lower` (lem.box_twopoint_lower,
both faces) feeds the first-moment input of `PxinfC_lower_of_inputs`, at `p = p_c` and `α = 1/2`.

`box_lower_hbox` converts the box theorem's real coordinatewise margin `|y_j| ≤ n - n/2` and
its `c·n^{1-d}` rpow form into the `hbox` shape used by `Y_firstmoment_of_box_lower`:
`y ∈ Q`, `R ≤ 2(R - |y|_∞)`, giving `c/R^{d-1}`.

`PxinfC_lower_at_pc` is the PxinfC lower bound at `p_c`. The box input is now supplied by
`appendix_box_twopoint_lower`, which itself rests on its own explicit inputs: (A)
(`TwoPointAsymptotics`), the cited `RestrictedRectangleLowerInput`, `hreg`
(lem.boundary_regularity) and `herr` (lem.err_cluster/err_boundary), all at `α = 1/2`. The
tree-graph and two-point inputs of the second moment also stay explicit. CONDITIONAL; not a
discharge of those inputs. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open AppendixVariance Section8

/-- The box lower bound at `α = 1/2`, in `hbox` shape. -/
theorem box_lower_hbox {d : ℕ} (hd : 7 ≤ d) (asymp : TwoPointAsymptotics d)
    (lower : RestrictedRectangleLowerInput d)
    (hreg : ∃ creg : ℝ, 0 < creg ∧ ∀ (i : Fin d) (n : ℕ) (x : Vertex d),
      1 ≤ n → 16 ≤ (1/2 : ℝ)*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-(1/2 : ℝ)*(n : ℝ)) →
      creg/(n : ℝ) ≤ appendixBoxClusterMean (criticalPoint d)
        (appendixBoxQ n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) x
        (fun C => ((C ∩ appendixBoxF n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x).card : ℝ)))
    (herr : ∃ Kerr : ℝ, 0 ≤ Kerr ∧ ∀ (i : Fin d) (n r : ℕ) (x : Vertex d),
      1 ≤ n → 1 ≤ r → 16 ≤ (1/2 : ℝ)*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-(1/2 : ℝ)*(n : ℝ)) →
      appendixBoxClusterMean (criticalPoint d)
          (appendixBoxQ n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) x
          (fun C => appendixBoxErrCluster C
            (appendixBoxF n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ) ∧
      appendixBoxClusterMean (criticalPoint d)
          (appendixBoxQ n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) x
          (fun C => appendixBoxErrBoundary C
            (appendixBoxF n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-(d : ℝ))/(n : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (R : ℕ) (x : Vertex d), 1 ≤ R →
      (x i = -(R : ℤ) ∨ x i = (R : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (R : ℝ) - (1/2 : ℝ) * (R : ℝ)) →
      ∀ y ∈ centeredBox d R, R ≤ 2 * (R - linfDist (0 : Vertex d) y) →
        c / (R : ℝ) ^ (d - 1) ≤ (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((centeredBox d R : Finset (Vertex d)) : Set (Vertex d)) x {y}) := by
  obtain ⟨c, hc, hbox⟩ := appendix_box_twopoint_lower hd asymp lower (α := (1/2 : ℝ))
    (by norm_num) (by norm_num) hreg herr
  refine ⟨c, hc, ?_⟩
  intro i R x hR hface hx y hyQ hmar
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hyR : linfDist (0 : Vertex d) y ≤ R := by
    rw [← appendix_cube_eq_centeredBox] at hyQ
    exact mem_cube_iff_dist_aux.mp hyQ
  have hy : ∀ j, |(y j : ℝ)| ≤ (R : ℝ) - (1/2 : ℝ) * (R : ℝ) := by
    intro j
    have hle : (y j).natAbs ≤ linfDist (0 : Vertex d) y := by
      rw [linfDist_zero]
      exact Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ j)
    have h2 : 2 * (y j).natAbs ≤ R := by omega
    have hcast : |(y j : ℝ)| = ((y j).natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have h2' : 2 * ((y j).natAbs : ℝ) ≤ R := by exact_mod_cast h2
    rw [hcast]; linarith
  have h := hbox i R x y hR hface hx hy
  have hd1 : 1 ≤ d := by omega
  have hpow : (R : ℝ) ^ ((1 : ℝ) - (d : ℝ)) = 1 / (R : ℝ) ^ (d - 1) := by
    rw [show (1 : ℝ) - (d : ℝ) = -((d - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub hd1, Nat.cast_one]; ring, Real.rpow_neg hRpos.le, Real.rpow_natCast,
      one_div]
  rw [hpow] at h
  calc c / (R : ℝ) ^ (d - 1) = c * (1 / (R : ℝ) ^ (d - 1)) := by ring
    _ ≤ _ := h

/-- PxinfC lower bound at `p_c`, with the box input supplied by `appendix_box_twopoint_lower`. -/
theorem PxinfC_lower_at_pc (e : ℕ) (asymp : TwoPointAsymptotics (e + 7))
    (lower : RestrictedRectangleLowerInput (e + 7))
    (hreg : ∃ creg : ℝ, 0 < creg ∧ ∀ (i : Fin (e + 7)) (n : ℕ) (x : Vertex (e + 7)),
      1 ≤ n → 16 ≤ (1/2 : ℝ)*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-(1/2 : ℝ)*(n : ℝ)) →
      creg/(n : ℝ) ≤ appendixBoxClusterMean (criticalPoint (e + 7))
        (appendixBoxQ n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) x
        (fun C => ((C ∩ appendixBoxF n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x).card : ℝ)))
    (herr : ∃ Kerr : ℝ, 0 ≤ Kerr ∧ ∀ (i : Fin (e + 7)) (n r : ℕ) (x : Vertex (e + 7)),
      1 ≤ n → 1 ≤ r → 16 ≤ (1/2 : ℝ)*(n : ℝ) → x i = -(n : ℤ) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ)-(1/2 : ℝ)*(n : ℝ)) →
      appendixBoxClusterMean (criticalPoint (e + 7))
          (appendixBoxQ n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) x
          (fun C => appendixBoxErrCluster C
            (appendixBoxF n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-((e + 7 : ℕ) : ℝ))/(n : ℝ) ∧
      appendixBoxClusterMean (criticalPoint (e + 7))
          (appendixBoxQ n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) x
          (fun C => appendixBoxErrBoundary C
            (appendixBoxF n (Nat.floor ((1/2 : ℝ)*(n : ℝ)/8)) i x) r) ≤
        Kerr*(r : ℝ)^((6 : ℝ)-((e + 7 : ℕ) : ℝ))/(n : ℝ))
    {C0 C1 : ℝ} (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (i : Fin (e + 7)) (R s : ℕ) (x : Vertex (e + 7))
      (tQ : Vertex (e + 7) → ℝ) (t : Vertex (e + 7) → Vertex (e + 7) → ℝ),
      1 ≤ s → 5 * s ≤ R → linfDist (0 : Vertex (e + 7)) x = R →
      (x i = -(R : ℤ) ∨ x i = (R : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (R : ℝ) - (1/2 : ℝ) * (R : ℝ)) →
      (∀ u ∈ centeredBox (e + 7) R, 0 ≤ tQ u) →
      (∀ u ∈ centeredBox (e + 7) R, ∀ v, 0 ≤ t u v) →
      (∀ y ∈ boundarySites (centeredBox (e + 7) s), ∀ z ∈ boundarySites (centeredBox (e + 7) s),
        (percolation (e + 7) (criticalPoint (e + 7))).real
          (connectionToSetEvent ((centeredBox (e + 7) R : Finset (Vertex (e + 7))) :
              Set (Vertex (e + 7))) x {y} ∩
            connectionToSetEvent ((centeredBox (e + 7) R : Finset (Vertex (e + 7))) :
              Set (Vertex (e + 7))) x {z}) ≤
          ∑ u ∈ centeredBox (e + 7) R, tQ u * t u y * t u z) →
      (∀ u ∈ centeredBox (e + 7) R, tQ u ≤ C0 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 6)) →
      (∀ u ∈ centeredBox (e + 7) R, ∀ v ∈ boundarySites (centeredBox (e + 7) s),
        t u v ≤ C1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (e + 5)) →
      κ * ((s : ℝ) / (R : ℝ)) ^ (e + 3) / (R : ℝ) ^ 3 ≤
        (percolation (e + 7) (criticalPoint (e + 7))).real
          {ω | x ∈ heartClusterUnion ω (centeredBox (e + 7) R) (centeredBox (e + 7) s)} := by
  obtain ⟨c, hc, hbox⟩ := box_lower_hbox (d := e + 7) (by omega) asymp lower hreg herr
  obtain ⟨κ, hκ, H⟩ := PxinfC_lower_of_inputs e hc hC0 hC1
  refine ⟨κ, hκ, ?_⟩
  intro i R s x tQ t hs h5s hxR hface hx htQ0 ht0 htree htQ ht
  have hR : 1 ≤ R := by omega
  refine H (criticalPoint (e + 7)) R s x tQ t hs h5s hxR htQ0 ht0 htree htQ ht ?_
  intro y hyQ hmar
  have h := hbox i R x hR hface hx y hyQ hmar
  rwa [show e + 7 - 1 = e + 6 by omega] at h

end NearCritical
