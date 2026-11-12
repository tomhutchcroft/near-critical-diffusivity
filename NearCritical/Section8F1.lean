module
public import NearCritical.Section8Convolution
public import NearCritical.Section8HeartAnnulus

/-! Source eq.F1_bound: the actual annulus two-point kernel, with the literal
integer ERE exponent. Only the source two-point asymptotics are supplied. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private lemma restricted_singleton_le_twoPoint {d : ℕ} (p : unitInterval)
    (D : Set (Vertex d)) (x y : Vertex d) :
    (percolation d p).real (connectionToSetEvent D x {y}) ≤ twoPoint d p x y := by
  have hs : connectionToSetEvent D x {y} ⊆ connectionEvent x y := by
    rintro ω ⟨_hx,z,hz,_hzD,hpath⟩
    have hzy : z = y := hz
    subst z
    have hle : restrictedGraph ω D ≤ openGraph ω := fun _ _ h => h.1
    exact hpath.mono hle
  exact measureReal_mono hs

/-- F1 for the actual critical restricted connection probabilities. The
global Green input is derived from the source asymptotics below. -/
theorem annulusF1_bound_of_green {d : ℕ} (hd : 5 ≤ d) (G : ℝ) (hG : 0 ≤ G)
    (green : CriticalSupGreenUpper d G) (r : ℕ) (hr : 1 ≤ r)
    (Q H excluded : Finset (Vertex d)) (x u : Vertex d) :
    ∑ y ∈ Q \ excluded, (max (r : ℝ) (latticeDistance x y))^((2 : ℤ)-(d : ℤ)) *
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) u {y}) ≤
      (G*((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))) *
        (max (r : ℝ) (latticeDistance x u))^((4 : ℤ)-(d : ℤ)) := by
  have ht (y : Vertex d) :
      (percolation d (criticalPoint d)).real
          (connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) u {y}) ≤
        G*(max 1 (latticeDistance u y))^((2 : ℝ)-(d : ℝ)) :=
    (restricted_singleton_le_twoPoint (criticalPoint d) (heartAnnulus Q H : Set (Vertex d)) u y).trans
      (green u y)
  have hreal :
      (∑ y ∈ Q \ excluded, (max (r : ℝ) (latticeDistance x y))^((2 : ℝ)-(d : ℝ)) *
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) u {y})) ≤
      (G*((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))) *
        (max (r : ℝ) (latticeDistance x u))^((4 : ℝ)-(d : ℝ)) := by
    calc
      _ ≤ ∑ y ∈ Q \ excluded, (max (r : ℝ) (latticeDistance x y))^((2 : ℝ)-(d : ℝ)) *
          (G*(max 1 (latticeDistance u y))^((2 : ℝ)-(d : ℝ))) := by
        apply Finset.sum_le_sum
        intro y _hy
        exact mul_le_mul_of_nonneg_left (ht y) (by positivity)
      _ = G*(∑ y ∈ Q \ excluded,
          (max (r : ℝ) (latticeDistance x y))^((2 : ℝ)-(d : ℝ)) *
            (max 1 (latticeDistance u y))^((2 : ℝ)-(d : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        ring
      _ ≤ G*(((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))) *
          (max (r : ℝ) (latticeDistance x u))^((4 : ℝ)-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left (truncated_green_convolution_le hd r hr (Q \ excluded) x u) hG
      _ = _ := by ring
  simpa only [← Real.rpow_intCast,Int.cast_sub,Int.cast_ofNat,Int.cast_natCast] using hreal

/-- Source F1 estimate, with a single positive constant independent of the
scale, cutoff, heart, excluded cube, and branch point. -/
theorem annulusF1_bound {d : ℕ} (hd : 5 ≤ d) (asymptotics : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (Q H excluded : Finset (Vertex d)) (x u : Vertex d),
      (∑ y ∈ Q \ excluded, (max (r : ℝ) (latticeDistance x y))^((2 : ℤ)-(d : ℤ)) *
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) u {y})) ≤
        C*(max (r : ℝ) (latticeDistance x u))^((4 : ℤ)-(d : ℤ)) := by
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  refine ⟨G*((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))),by positivity,?_⟩
  intro r hr Q H excluded x u
  exact annulusF1_bound_of_green hd G hG.le green r hr Q H excluded x u

end NearCritical.Section8
