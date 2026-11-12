module

public import NearCritical.Section9DiameterMoment
public import NearCritical.Section8Convolution
public import NearCritical.ThreePointDiagram

/-! `lem.sprinkling.AB.geo`: the `n^2` scale and the Markov tail.

With the regularised Green bound `CriticalSupGreenUpper d G` (a consequence of
assumption (A)) and `d >= 5`:

* `twoPoint_convolution_le`: `sum_z tau(x,z) tau(z,a) <= G^2 K_d n^{4-d}` when
  `x` and `a` are at distance at least `n`;
* `diameter_tail_le`: at `p_c`, with an independent `q`-sprinkle, if `A` and `B`
  are at distance at least `n` from the pivot box then

  `P[ rin >= K ] <= (1 + 2 q |E| |A| |B| G^3 K_d n^{4-d} n^{2-d}) / K`.

With `|E| <~ n^d`, `|A||B| <~ n^{d-2}`, `q <~ n^{-2}` the numerator is `O(n^2)`,
which is the statement of the lemma (unconditional product law, fixed revealed
sets).
-/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The dimensional constant of `truncated_green_convolution_le`. -/
def greenConvConst (d : ℕ) : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))

lemma greenConvConst_nonneg (d : ℕ) : 0 ≤ greenConvConst d := by
  unfold greenConvConst
  positivity

theorem twoPoint_convolution_le {d : ℕ} (hd : 5 ≤ d) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : CriticalSupGreenUpper d G) (s : Finset (Vertex d)) (x a : Vertex d) {n : ℝ}
    (hn : 0 < n) (hsep : n ≤ latticeDistance x a) :
    ∑ z ∈ s, twoPoint d (criticalPoint d) x z * twoPoint d (criticalPoint d) z a ≤
      G^2 * greenConvConst d * n^((4 : ℝ)-(d : ℝ)) := by
  have hterm : ∀ z ∈ s, twoPoint d (criticalPoint d) x z * twoPoint d (criticalPoint d) z a ≤
      G^2 * ((max ((1:ℕ) : ℝ) (latticeDistance x z))^((2 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance a z))^((2 : ℝ)-(d : ℝ))) := by
    intro z _
    have h1 := hG x z
    have h2 := hG z a
    rw [latticeDistance_comm z a] at h2
    rw [Nat.cast_one]
    calc twoPoint d (criticalPoint d) x z * twoPoint d (criticalPoint d) z a
        ≤ (G * (max 1 (latticeDistance x z))^((2 : ℝ)-(d : ℝ))) *
          (G * (max 1 (latticeDistance a z))^((2 : ℝ)-(d : ℝ))) :=
          mul_le_mul h1 h2 (twoPoint_nonneg _ _ _) (le_trans (twoPoint_nonneg _ _ _) h1)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hconv := Section8.truncated_green_convolution_le hd 1 (le_refl 1) s x a
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (max ((1:ℕ) : ℝ) (latticeDistance x a))^((4 : ℝ)-(d : ℝ)) ≤
      n^((4 : ℝ)-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hn (hsep.trans (le_max_right _ _)) (by linarith)
  calc G^2 * ∑ z ∈ s, (max ((1:ℕ) : ℝ) (latticeDistance x z))^((2 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance a z))^((2 : ℝ)-(d : ℝ))
      ≤ G^2 * (greenConvConst d * (max ((1:ℕ) : ℝ) (latticeDistance x a))^((4 : ℝ)-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left hconv (sq_nonneg G)
    _ ≤ G^2 * (greenConvConst d * n^((4 : ℝ)-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (greenConvConst_nonneg d)) (sq_nonneg G)
    _ = _ := by ring

lemma twoPoint_far_le {d : ℕ} (hd : 5 ≤ d) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : CriticalSupGreenUpper d G) (y b : Vertex d) {n : ℝ} (hn : 0 < n)
    (hsep : n ≤ latticeDistance y b) :
    twoPoint d (criticalPoint d) y b ≤ G * n^((2 : ℝ)-(d : ℝ)) := by
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  refine (hG y b).trans (mul_le_mul_of_nonneg_left ?_ hG0)
  exact Real.rpow_le_rpow_of_nonpos hn (hsep.trans (le_max_right _ _)) (by linarith)

/-- **Tail of the sprinkling intrinsic diameter** (lem.sprinkling.AB.geo). -/
theorem diameter_tail_le {d : ℕ} (hd : 5 ≤ d) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : CriticalSupGreenUpper d G) (q : unitInterval)
    (S L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hSL : S ⊆ L) (hsepQ : Disjoint (S : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    {n : ℝ} (hn : 0 < n)
    (hA : ∀ e ∈ orientedLatticePairs S, ∀ x ∈ A, n ≤ latticeDistance x e.1)
    (hB : ∀ e ∈ orientedLatticePairs S, ∀ y ∈ B, n ≤ latticeDistance y e.2)
    {K : ℝ} (hK : 0 < K) :
    ((percolation d (criticalPoint d)).prod (percolation d q)).real
      {z | K ≤ ((sprinklingIntrinsicDiameter (sprinklingUnexploredGraph z.1 L Q₁ F₁)
        (sprinklingUnexploredGraph z.1 R Q₃ F₃) A B
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs S)
          L R Q₁ F₁ Q₃ F₃ A B) : ℕ) : ℝ)} ≤
      (1 + ((orientedLatticePairs S).card : ℝ) * ((A.card : ℝ) * ((B.card : ℝ) *
        (2 * (G^2 * greenConvConst d * n^((4 : ℝ)-(d : ℝ)) *
          (G * n^((2 : ℝ)-(d : ℝ))) * (q : ℝ)))))) / K := by
  obtain ⟨g, hg, hle⟩ := diameter_dominated (criticalPoint d) q S L R Q₁ F₁ Q₃ F₃ A B hSL hsepQ
  set per : ℝ := G^2 * greenConvConst d * n^((4 : ℝ)-(d : ℝ)) *
    (G * n^((2 : ℝ)-(d : ℝ))) * (q : ℝ) with hper
  have hconv0 : 0 ≤ G^2 * greenConvConst d * n^((4 : ℝ)-(d : ℝ)) :=
    mul_nonneg (mul_nonneg (sq_nonneg G) (greenConvConst_nonneg d)) (Real.rpow_nonneg hn.le _)
  have hbound : (1 + ∑ e ∈ orientedLatticePairs S, ∑ x ∈ A, ∑ y ∈ B,
      ((∑ z ∈ insert x L, twoPoint d (criticalPoint d) x z * twoPoint d (criticalPoint d) z e.1 *
          twoPoint d (criticalPoint d) y e.2 * (q : ℝ)) +
        ∑ z ∈ insert y R, twoPoint d (criticalPoint d) y z * twoPoint d (criticalPoint d) z e.2 *
          twoPoint d (criticalPoint d) x e.1 * (q : ℝ))) ≤
      1 + ((orientedLatticePairs S).card : ℝ) * ((A.card : ℝ) * ((B.card : ℝ) * (2 * per))) := by
    refine add_le_add (le_refl _) ?_
    have hterm : ∀ e ∈ orientedLatticePairs S, ∀ x ∈ A, ∀ y ∈ B,
        ((∑ z ∈ insert x L, twoPoint d (criticalPoint d) x z *
            twoPoint d (criticalPoint d) z e.1 * twoPoint d (criticalPoint d) y e.2 * (q : ℝ)) +
          ∑ z ∈ insert y R, twoPoint d (criticalPoint d) y z *
            twoPoint d (criticalPoint d) z e.2 * twoPoint d (criticalPoint d) x e.1 * (q : ℝ)) ≤
          2 * per := by
      intro e he x hx y hy
      have h1 : (∑ z ∈ insert x L, twoPoint d (criticalPoint d) x z *
          twoPoint d (criticalPoint d) z e.1 * twoPoint d (criticalPoint d) y e.2 * (q : ℝ)) ≤
          per := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (twoPoint_convolution_le hd hG0 hG _ x e.1 hn (hA e he x hx))
            (twoPoint_far_le hd hG0 hG y e.2 hn (hB e he y hy)) (twoPoint_nonneg _ _ _) hconv0)
          q.2.1
      have h2 : (∑ z ∈ insert y R, twoPoint d (criticalPoint d) y z *
          twoPoint d (criticalPoint d) z e.2 * twoPoint d (criticalPoint d) x e.1 * (q : ℝ)) ≤
          per := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (twoPoint_convolution_le hd hG0 hG _ y e.2 hn (hB e he y hy))
            (twoPoint_far_le hd hG0 hG x e.1 hn (hA e he x hx)) (twoPoint_nonneg _ _ _) hconv0)
          q.2.1
      linarith
    calc _ ≤ ∑ e ∈ orientedLatticePairs S, ∑ x ∈ A, ∑ y ∈ B, 2 * per :=
          Finset.sum_le_sum (fun e he => Finset.sum_le_sum (fun x hx =>
            Finset.sum_le_sum (fun y hy => hterm e he x hx y hy)))
      _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
  have hg' : IntegralLe ((percolation d (criticalPoint d)).prod (percolation d q)) g
      (1 + ((orientedLatticePairs S).card : ℝ) * ((A.card : ℝ) * ((B.card : ℝ) * (2 * per)))) :=
    ⟨hg.1, hg.2.trans hbound⟩
  exact hg'.tail (fun z => Nat.cast_nonneg _) hle hK

end NearCritical
