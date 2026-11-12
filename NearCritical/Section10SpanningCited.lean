module

public import NearCritical.Section10PreGoodCandidates
public import NearCritical.SpanningRoundedCuboid

/-! The spanning lower bound of `lem.arm.2dspanning` stated at the CITED level.

`SpanningCrossInput d c` is eq:2d_spanning_cross of the source: for every
`n >= 1` and every root `x` in `Lambda_{n/16}`, with probability at least
`c n^{-2}` at `p_c` the root is joined, inside each of the `2d` source cuboids,
to the far box `2 n e_i + [-n/8, n/8]^d`. The source derives it from the cited
super-Brownian scaling limit (blanc2026super); it is NOT proved here.

`spanning_lower_of_cross` derives from it the lower spanning bound for the
actual finite-box cluster, in the exact shape of the hypothesis `hspanlo` of
`hcand_of_raw` (origin cube, `N = (t-1)/2`, faces `typicalFace t 0`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
open MeasureTheory

/-- Source eq:2d_spanning_cross (cited-level input). -/
def SpanningCrossInput (d : ℕ) (c : ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ x ∈ centeredBox d (n / 32),
    c / (n : ℝ)^2 ≤ (percolation d (criticalPoint d)).real
      {ω : Configuration d | ∀ f : Fin d × Bool,
        ω ∈ connectionToSetEvent (roundedSourceSpanningCuboid n f) x
          (roundedSourceSpanningTarget n f)}

lemma centeredBox_mono {d r s : ℕ} (h : r ≤ s) : centeredBox d r ⊆ centeredBox d s := by
  intro x hx
  rw [mem_centeredBox] at hx ⊢
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have : (r : ℤ) ≤ (s : ℤ) := by exact_mod_cast h
  constructor <;> linarith

/-- Lower spanning bound for the actual origin cube from the cited crossing
estimate. -/
theorem spanning_lower_of_cross {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (hcross : SpanningCrossInput d c)
    (t N : ℕ) (ht : 3 ≤ t) (hN : (t - 1) / 2 = N) (x : Vertex d)
    (hx : x ∈ centeredBox d ((t - 1) / 32)) :
    (c / 4) / (N + 1 : ℝ)^2 ≤ (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) := by
  have hn : 1 ≤ t - 1 := by omega
  have ht1 : 1 ≤ t := by omega
  have hfaces : typicalFace t (0 : Vertex d) = signedCubeFace d N := by
    funext f
    rw [typicalFace_zero t ht1, hN]
  have hxN : x ∈ centeredBox d ((t - 1) / 2) :=
    centeredBox_mono (Nat.div_le_div_left (by norm_num) (by norm_num)) hx
  have hsub := all_roundedSourceSpanningCuboids_subset_spanning (d := d) hn x hxN
  have h1 := hcross (t - 1) hn x hx
  have h2 := measureReal_mono (μ := percolation d (criticalPoint d)) hsub
    (measure_ne_top (percolation d (criticalPoint d)) _)
  rw [hN] at h2
  rw [hfaces]
  refine le_trans ?_ (h1.trans h2)
  have hNpos : (0:ℝ) < (N + 1 : ℝ) := by positivity
  have hnpos : (0:ℝ) < ((t - 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hle : ((t - 1 : ℕ) : ℝ) ≤ 2 * (N + 1 : ℝ) := by
    have : t - 1 ≤ 2 * (N + 1) := by omega
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : ((t - 1 : ℕ) : ℝ)^2 ≤ 4 * (N + 1 : ℝ)^2 := by nlinarith
  nlinarith

end NearCritical.Section10
