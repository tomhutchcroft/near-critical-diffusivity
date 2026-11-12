module

public import NearCritical.Section10FirstGoodUsedHistory
public import NearCritical.Section10MarkedRouteProduct

/-! The exact sign change of variables for a mark of two actual route histories. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- A mark that couples both route histories has the same weighted sum
when each route draws its sign on the physical move that uses it. This
includes unequal prefix lengths and the source's fixed initial states. -/
theorem firstGood_pair_marked_sum_fixedStart
    (γ γ' : SourceRoute D M) (z : Configuration d × Configuration d) (hM : 1 ≤ M)
    (hbox : ∀ r ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ t, t < 2 * M →
      (routeLab M r.position t).site ∈ Λ.siteBox)
    (hpre : ∀ r ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ t, t < 2 * M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M r.position t).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (n n' : ℕ) (x x' : Λ.X) (b b' : Bool) (F : NestTrace Λ.X n → NestTrace Λ.X n' → ℝ) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let K (r : SourceRoute D M) :=
      (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel r G
    let L (r : SourceRoute D M) :=
      usedMaskedKernel (routeSignDraw r)
        (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb r G (routeSignDraw r))
    let U (r : SourceRoute D M) (m : ℕ) (a : Bool) (h : NestTrace Λ.X m) :=
      eraseInitialUsedSign m (usedMaskedTrace (routeSignDraw r) m 0 a h)
    (∑ l : NestTrace Λ.X n, ∑ r : NestTrace Λ.X n',
      F (U γ n x.2 l) (U γ' n' x'.2 r) *
        (routeTraceMass (K γ) z n 0 x l * routeTraceMass (K γ') z n' 0 x' r)) =
    ∑ l : NestTrace Λ.X n, ∑ r : NestTrace Λ.X n',
      F (eraseInitialUsedSign n l) (eraseInitialUsedSign n' r) *
        (routeTraceMass (L γ) z n 0 (x.1,b) l * routeTraceMass (L γ') z n' 0 (x'.1,b') r) := by
  intro G K L U
  have hγ : γ ∈ ({γ,γ'} : Finset (SourceRoute D M)) := by simp
  have hγ' : γ' ∈ ({γ,γ'} : Finset (SourceRoute D M)) := by simp
  let A := fun l => routeTraceMass (K γ) z n 0 x l
  let B := fun r => routeTraceMass (K γ') z n' 0 x' r
  let A' := fun l => routeTraceMass (L γ) z n 0 (x.1,b) l
  let B' := fun r => routeTraceMass (L γ') z n' 0 (x'.1,b') r
  have hL := Λ.firstGood_route_marked_sum_fixedStart p q ρ κ hκ hs hsiteProb
    γ z hM (hbox γ hγ) (hpre γ hγ) hcount n x.1 x.2 b
  have hR := Λ.firstGood_route_marked_sum_fixedStart p q ρ κ hκ hs hsiteProb
    γ' z hM (hbox γ' hγ') (hpre γ' hγ') hcount n' x'.1 x'.2 b'
  change (∑ l, ∑ r, F (U γ n x.2 l) (U γ' n' x'.2 r) * (A l * B r)) =
    ∑ l, ∑ r, F (eraseInitialUsedSign n l) (eraseInitialUsedSign n' r) * (A' l * B' r)
  calc
    _ = ∑ l, ∑ r, (F (U γ n x.2 l) (U γ' n' x'.2 r) * A l) * B r := by
      simp only [mul_assoc]
    _ = ∑ l, ∑ r, (F (U γ n x.2 l) (eraseInitialUsedSign n' r) * A l) * B' r := by
      apply Finset.sum_congr rfl
      intro l _
      exact hR (fun r => F (U γ n x.2 l) r * A l)
    _ = ∑ r, ∑ l, (F (U γ n x.2 l) (eraseInitialUsedSign n' r) * B' r) * A l := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro l _
      exact mul_right_comm _ _ _
    _ = ∑ r, ∑ l, (F (eraseInitialUsedSign n l) (eraseInitialUsedSign n' r) * B' r) * A' l := by
      apply Finset.sum_congr rfl
      intro r _
      exact hL (fun l => F l (eraseInitialUsedSign n' r) * B' r)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro r _
      rw [mul_right_comm, mul_assoc]

/-- Transport marks on the actual merged prefix between the pending-sign
and current-sign kernels. -/
theorem firstGood_merged_marked_sum_fixedStart
    (γ γ' : SourceRoute D M) (z : Configuration d × Configuration d) (hM : 1 ≤ M)
    (hbox : ∀ r ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ t, t < 2 * M →
      (routeLab M r.position t).site ∈ Λ.siteBox)
    (hpre : ∀ r ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ t, t < 2 * M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M r.position t).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (s : List PairMove) (x x' : Λ.X) (b b' : Bool)
    (F : NestTrace Λ.X (leftCount s) → NestTrace Λ.X (rightCount s) → ℝ) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let K (r : SourceRoute D M) :=
      (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel r G
    let L (r : SourceRoute D M) :=
      usedMaskedKernel (routeSignDraw r)
        (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb r G (routeSignDraw r))
    let U (r : SourceRoute D M) (m : ℕ) (a : Bool) (h : NestTrace Λ.X m) :=
      eraseInitialUsedSign m (usedMaskedTrace (routeSignDraw r) m 0 a h)
    (∑ h : NestTrace (Λ.X × Λ.X) s.length,
      F (U γ (leftCount s) x.2 (mergedRouteTraces s h).1)
        (U γ' (rightCount s) x'.2 (mergedRouteTraces s h).2) *
        mergedTraceMass (K γ) (K γ') z s 0 0 (x,x') h) =
    ∑ h : NestTrace (Λ.X × Λ.X) s.length,
      F (eraseInitialUsedSign (leftCount s) (mergedRouteTraces s h).1)
        (eraseInitialUsedSign (rightCount s) (mergedRouteTraces s h).2) *
        mergedTraceMass (L γ) (L γ') z s 0 0 ((x.1,b),(x'.1,b')) h := by
  intro G K L U
  let oldMark := fun r : NestTrace Λ.X (leftCount s) × NestTrace Λ.X (rightCount s) =>
    F (U γ (leftCount s) x.2 r.1) (U γ' (rightCount s) x'.2 r.2)
  let newMark := fun r : NestTrace Λ.X (leftCount s) × NestTrace Λ.X (rightCount s) =>
    F (eraseInitialUsedSign (leftCount s) r.1) (eraseInitialUsedSign (rightCount s) r.2)
  change (∑ h, oldMark (mergedRouteTraces s h) * mergedTraceMass (K γ) (K γ') z s 0 0 (x,x') h) =
    ∑ h, newMark (mergedRouteTraces s h) * mergedTraceMass (L γ) (L γ') z s 0 0 ((x.1,b),(x'.1,b')) h
  rw [mergedTraceMass_marked_sum_eq_routeProduct (K γ) (K γ') z s 0 0 (x,x') oldMark,
    mergedTraceMass_marked_sum_eq_routeProduct (L γ) (L γ') z s 0 0 ((x.1,b),(x'.1,b')) newMark,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  exact Λ.firstGood_pair_marked_sum_fixedStart p q ρ κ hκ hs hsiteProb γ γ' z hM
    hbox hpre hcount (leftCount s) (rightCount s) x x' b b' F

end NearCritical.Section10.NestLayout
