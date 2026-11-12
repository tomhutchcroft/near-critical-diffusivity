module

public import NearCritical.Section10MarkedBounds

/-! Source `prop.nw.pair`, overlap bound `eq.nw.pair.overlap`, on the coupled law.

Two chains run synchronously (step `t` of both at joint time `t`); the pair is
a single chain on `X × X'` with kernel `pairKernel k k'`. `chainValue_pair`: its
weight is the product of the two chain weights.

`pair_entanglement_le`: let the pair kernel split as `K = a + b` (`a`: the two
bridges intersect; `b`: clean) and let `c` mark site entanglements produced by
clean steps, all local on pairwise disjoint fresh blocks and nonnegative. If the
MEAN kernels satisfy
* `E[sum_y K t x y] <= rho t` with `rho t >= 1`,
* a risk potential `phi t x >= 0` with
  `sum_y E[a t x y] phi (t+1) y <= theta * E[sum_y a t x y]`, `theta < 1`
  (persistence, `eq.nw.persist`, averaged over the producing step), and
  `sum_y E[b t x y] phi (t+1) y <= phi t x - E[sum_y a t x y] + delta t`
  (entering, `eq.nw.enter`; a stay carries the risk unchanged),
* `E[sum_y c t x y] <= delta t`,
then for every nonnegative `G` local on the explored bonds

  `E[G * (2 * #tube-entangled + #site-entangled, weighted)]`
  `  <= E[G] * prod rho * ((2 / (1 - theta)) * (a_t(x) + sum delta) + sum delta)`.

The one-step estimates are the content of `lem.nw.H`; they are hypotheses here.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- Synchronous kernel of two chains. -/
def pairKernel {d : ℕ} {X X' : Type*}
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → X' → X' → Configuration d × Configuration d → ℝ) :
    ℕ → X × X' → X × X' → Configuration d × Configuration d → ℝ :=
  fun t x y z => k t x.1 y.1 z * k' t x.2 y.2 z

/-- The pair weight is the product of the two chain weights. -/
theorem chainValue_pair {d : ℕ} {X X' : Type*} [Fintype X] [Fintype X']
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → X' → X' → Configuration d × Configuration d → ℝ) :
    ∀ (m t : ℕ) (x : X) (x' : X') (z : Configuration d × Configuration d),
      chainValue (pairKernel k k') m t (x, x') z =
        chainValue k m t x z * chainValue k' m t x' z := by
  intro m
  induction m with
  | zero =>
    intro t x x' z
    simp only [chainValue, mul_one]
  | succ m ih =>
    intro t x x' z
    simp only [chainValue, pairKernel, Fintype.sum_prod_type, ih]
    rw [Fintype.sum_mul_sum]
    exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun y' _ => by ring))

/-- **`eq.nw.pair.overlap`**, as an expectation bound for marked chains. -/
theorem pair_entanglement_le {d : ℕ} {S : Type*} [Fintype S] (p q : unitInterval)
    (B : ℕ → Finset (LBond d)) (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (K a b c : ℕ → S → S → Configuration d × Configuration d → ℝ)
    (hK : ∀ t x y, IsLocal (B t) (K t x y)) (ha : ∀ t x y, IsLocal (B t) (a t x y))
    (hb : ∀ t x y, IsLocal (B t) (b t x y)) (hc : ∀ t x y, IsLocal (B t) (c t x y))
    (ha0 : ∀ t x y z, 0 ≤ a t x y z) (hb0 : ∀ t x y z, 0 ≤ b t x y z)
    (hc0 : ∀ t x y z, 0 ≤ c t x y z) (hKab : ∀ t x y z, K t x y z = a t x y z + b t x y z)
    {ρ δ : ℕ → ℝ} (hρ : ∀ t, 1 ≤ ρ t) (hδ : ∀ t, 0 ≤ δ t) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hrow : ∀ t x, ∑ y, (∫ z, K t x y z ∂((percolation d p).prod (percolation d q))) ≤ ρ t)
    (φ : ℕ → S → ℝ) (hφ0 : ∀ t x, 0 ≤ φ t x)
    (hpersist : ∀ t x, ∑ y, (∫ z, a t x y z ∂((percolation d p).prod (percolation d q))) * φ (t+1) y ≤
      θ * ∑ y, ∫ z, a t x y z ∂((percolation d p).prod (percolation d q)))
    (henter : ∀ t x, ∑ y, (∫ z, b t x y z ∂((percolation d p).prod (percolation d q))) * φ (t+1) y ≤
      φ t x - (∑ y, ∫ z, a t x y z ∂((percolation d p).prod (percolation d q))) + δ t)
    (hsite : ∀ t x, ∑ y, (∫ z, c t x y z ∂((percolation d p).prod (percolation d q))) ≤ δ t)
    (m t : ℕ) (x : S) (R : Finset (LBond d)) (G : Configuration d × Configuration d → ℝ)
    (hG : IsLocal R G) (hG0 : ∀ z, 0 ≤ G z) (hR : ∀ j, j < m → Disjoint R (B (t+j))) :
    (∫ z, G z * (2 * markedValue K a m t x z + markedValue K c m t x z)
      ∂((percolation d p).prod (percolation d q))) ≤
      (∫ z, G z ∂((percolation d p).prod (percolation d q))) *
        (stepProd ρ m t * (2 * ((1 - θ)⁻¹ * φ t x +
          (1 - θ)⁻¹ * stepSum δ m t) + stepSum δ m t)) := by
  have hG0' : 0 ≤ ∫ z, G z ∂((percolation d p).prod (percolation d q)) := integral_nonneg hG0
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℕ → S → S → ℝ, Kb = fun t x y =>
      ∫ z, K t x y z ∂((percolation d p).prod (percolation d q)) := ⟨_, rfl⟩
  obtain ⟨Ab, hAb⟩ : ∃ Ab : ℕ → S → S → ℝ, Ab = fun t x y =>
      ∫ z, a t x y z ∂((percolation d p).prod (percolation d q)) := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ Bb : ℕ → S → S → ℝ, Bb = fun t x y =>
      ∫ z, b t x y z ∂((percolation d p).prod (percolation d q)) := ⟨_, rfl⟩
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℕ → S → S → ℝ, Cb = fun t x y =>
      ∫ z, c t x y z ∂((percolation d p).prod (percolation d q)) := ⟨_, rfl⟩
  have hA0 : ∀ t x y, 0 ≤ Ab t x y := fun t x y => by
    rw [hAb]
    exact integral_nonneg (ha0 t x y)
  have hB0 : ∀ t x y, 0 ≤ Bb t x y := fun t x y => by
    rw [hBb]
    exact integral_nonneg (hb0 t x y)
  have hC0 : ∀ t x y, 0 ≤ Cb t x y := fun t x y => by
    rw [hCb]
    exact integral_nonneg (hc0 t x y)
  have hKAB : ∀ t x y, Kb t x y = Ab t x y + Bb t x y := fun t x y => by
    rw [hKb, hAb, hBb]
    show (∫ z, K t x y z ∂((percolation d p).prod (percolation d q))) =
      (∫ z, a t x y z ∂((percolation d p).prod (percolation d q))) +
        ∫ z, b t x y z ∂((percolation d p).prod (percolation d q))
    rw [← integral_add ((ha t x y).integrable p q) ((hb t x y).integrable p q)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z => hKab t x y z))
  have hK0 : ∀ t x y, 0 ≤ Kb t x y := fun t x y => by
    rw [hKAB]
    exact add_nonneg (hA0 t x y) (hB0 t x y)
  have hrow' : ∀ t x, ∑ y, Kb t x y ≤ ρ t := fun t x => by rw [hKb]; exact hrow t x
  have htube := detMarked_tube_le_potential Kb Ab Bb hA0 hB0 hKAB hρ hrow' hθ0 hθ1 hδ φ hφ0
    (fun t x => by rw [hAb]; exact hpersist t x)
    (fun t x => by rw [hAb, hBb]; exact henter t x) m t x
  have hsiteb := detMarked_site_le Kb Cb hK0 hC0 hρ hrow' hδ
    (fun t x => by rw [hCb]; exact hsite t x) m t x
  have hintA := (IsLoc.mul ⟨R, hG⟩ (markedValue_isLoc B K a hK ha m t x)).integrable p q
  have hintC := (IsLoc.mul ⟨R, hG⟩ (markedValue_isLoc B K c hK hc m t x)).integrable p q
  have hsplit : (fun z => G z * (2 * markedValue K a m t x z + markedValue K c m t x z)) =
      fun z => 2 * (G z * markedValue K a m t x z) + G z * markedValue K c m t x z := by
    funext z
    ring
  rw [hsplit, integral_add (hintA.const_mul 2) hintC, integral_const_mul,
    markedValue_integral_eq p q B hB K a hK ha m t x R G hG hR,
    markedValue_integral_eq p q B hB K c hK hc m t x R G hG hR]
  rw [hKb, hAb] at htube
  rw [hKb, hCb] at hsiteb
  have h1 := mul_le_mul_of_nonneg_left htube hG0'
  have h2 := mul_le_mul_of_nonneg_left hsiteb hG0'
  beta_reduce at h1
  nlinarith [h1, h2]

end NearCritical.Section10
