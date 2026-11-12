module
public import NearCritical.Section8RectangleGrid
public import NearCritical.Section8ExtensionRectangleMargins
public import Mathlib.Data.Finset.Lattice.Fold

/-! The cited fixed-shape theorem implies the actual uniform source lower bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Finitely many fixed rectangle shapes give one lower constant for every
pair with the stated interior margins. Moving aspect ratios are not an input. -/
theorem section8_rectangle_interior_pair_lower {d : ℕ} (hd : 2 ≤ d)
    (lower : RestrictedRectangleLowerInput d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ (a z : Vertex d) (l u : Fin d → ℝ),
      (∀ j, u j-l j ≤ 1) →
      (∀ j, l j*(n : ℝ)+(n : ℝ)/16 ≤ (a j : ℝ) ∧
        (a j : ℝ) ≤ u j*(n : ℝ)-(n : ℝ)/16) →
      (∀ j, l j*(n : ℝ)+(n : ℝ)/16 ≤ (z j : ℝ) ∧
        (z j : ℝ) ≤ u j*(n : ℝ)-(n : ℝ)/16) →
      c*(n : ℝ)^((2 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent {v : Vertex d | ∀ j,
            l j*(n : ℝ) < (v j : ℝ) ∧ (v j : ℝ) < u j*(n : ℝ)} a {z}) := by
  let Shape := (Fin d → Fin 64) × (Fin d → Fin 64)
  have hex (κ : Shape) := section8_translated_rectangle_lower lower
    (section8RectangleGridWidth κ.1) (section8RectangleGridWidth κ.2)
    (fun j => (section8_rectangle_grid_width_bounds κ.1 j).1)
    (fun j => (section8_rectangle_grid_width_bounds κ.2 j).1)
    (65/64) (by norm_num)
  let C : Shape → ℝ := fun κ => Classical.choose (hex κ)
  have hC (κ : Shape) : 0 < C κ := (Classical.choose_spec (hex κ)).1
  have hbound (κ : Shape) := (Classical.choose_spec (hex κ)).2
  have hne : (Finset.univ : Finset Shape).Nonempty := Finset.univ_nonempty
  let c : ℝ := Finset.univ.inf' hne C
  have hc : 0 < c := (Finset.lt_inf'_iff hne).mpr (fun κ _ => hC κ)
  have hcC (κ : Shape) : c ≤ C κ := Finset.inf'_le C (Finset.mem_univ κ)
  refine ⟨c,hc,?_⟩
  intro n hn a z l u hwidth ha hz
  obtain ⟨κ,hinner,hcontain,hdist⟩ := section8_rectangle_grid_cover n hn a z l u hwidth ha hz
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hkpos : 0 < max 1 (latticeDistance 0 (z-a)) := zero_lt_one.trans_le (le_max_left _ _)
  have hkernel : (n : ℝ)^((2 : ℝ)-(d : ℝ)) ≤
      (max 1 (latticeDistance 0 (z-a)))^((2 : ℝ)-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hkpos hdist (by linarith)
  have hmono : connectionToSetEvent ((fun v : Vertex d => a+v) ''
        section8Rectangle (fun j => (65/64)*section8RectangleGridWidth κ.1 j)
          (fun j => (65/64)*section8RectangleGridWidth κ.2 j) n) a {z} ⊆
      connectionToSetEvent {v : Vertex d | ∀ j,
        l j*(n : ℝ) < (v j : ℝ) ∧ (v j : ℝ) < u j*(n : ℝ)} a {z} := by
    rintro ω ⟨haD,v,hvz,hvD,hav⟩
    refine ⟨hcontain haD,v,hvz,hcontain hvD,hav.mono ?_⟩
    exact fun _ _ h => ⟨h.1,hcontain h.2.1,hcontain h.2.2⟩
  calc
    _ ≤ C κ*(max 1 (latticeDistance 0 (z-a)))^((2 : ℝ)-(d : ℝ)) :=
      mul_le_mul (hcC κ) hkernel (Real.rpow_nonneg hn0.le _) (hC κ).le
    _ ≤ (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((fun v : Vertex d => a+v) ''
          section8Rectangle (fun j => (65/64)*section8RectangleGridWidth κ.1 j)
            (fun j => (65/64)*section8RectangleGridWidth κ.2 j) n) a {z}) :=
      hbound κ n hn a z hinner
    _ ≤ _ := measureReal_mono hmono (measure_ne_top _ _)

/-- The actual source shifted root and middle-core target have a uniform
restricted connection lower bound, deduced from the literal cited rectangle
input and the proved source margins/finite-grid containment. -/
theorem section8_extension_source_connection_lower {d : ℕ} (hd : 2 ≤ d)
    (lower : RestrictedRectangleLowerInput d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (n r : ℕ), 16*(r+1) ≤ n →
      ∀ x z : Vertex d, x ∈ section8ExtensionPositiveFaceCore i n →
      z ∈ section8ExtensionMiddleCore i n →
      c*(n : ℝ)^((2 : ℝ)-(d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) : Set (Vertex d))
            (Function.update x i (x i+(r : ℤ))) {z}) := by
  obtain ⟨c,hc,hbound⟩ := section8_rectangle_interior_pair_lower hd lower
  refine ⟨c,hc,?_⟩
  intro i n r hn x z hx hz
  let l : Fin d → ℝ := fun j => if j=i then 3/8 else -3/8
  let u : Fin d → ℝ := fun j => if j=i then 11/8 else 3/8
  let a := Function.update x i (x i+(r : ℤ))
  obtain ⟨hwidth,ha,hz',hdom⟩ := section8_extension_rectangle_margins i n r hn hx hz
  have hn1 : 1 ≤ n := by omega
  have hh := hbound n hn1 a z l u hwidth ha hz'
  rw [hdom] at hh
  exact hh

end NearCritical
