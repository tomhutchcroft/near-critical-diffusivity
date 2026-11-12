module

public import NearCritical.Section10SoloArrivalOccupation

/-! The product H1 bound for the two distinct chronological arrivals. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory
open scoped Classical

/-- A physical solo arrival and its one-child bound for every valid
incoming nest. -/
def SoloArrivalH1 {D d M : ℕ} (Λ : NestLayout D d) (p q : unitInterval)
    (G : Λ.Φ) (K : SourceRoute D M → ℕ → Λ.X → Λ.X → Configuration d × Configuration d → ℝ)
    (γ γ' : SourceRoute D M) (s : List PairMove) (m : PairMove) (c : Finset (Vertex d)) (A : ℝ) : Prop :=
  let μ := (percolation d p).prod (percolation d q)
  let H (δ : SourceRoute D M) (j : ℕ) :=
    let ℓ := routeLab M δ.position j
    (0 < j ∧ j+1 < 2*M ∧ ℓ.target ≠ ℓ.site) ∧
    ∀ u : Λ.X, Λ.moveCtx G ℓ u →
      (∫ z, ∑ y : Λ.X, if c ∈ y.1.val then K δ j u y z else 0 ∂μ) ≤ A
  (m = .left → H γ (leftCount s)) ∧ (m = .right → H γ' (rightCount s))

/-- The two solo arrivals are charged separately, even when shared rows
occur between them. The first occupation is read at its own arrival
before it is carried through the gap. -/
theorem firstGood_two_solo_arrival_mass_le
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      (routeLab M δ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (s gap : List PairMove) (m m' : PairMove) (hm : m ≠ .both) (hm' : m' ≠ .both)
    (x : Λ.X × Λ.X) (c c' : Finset (Vertex d)) {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let r := s ++ [m]
    let u := r ++ gap
    let v := u ++ [m']
    let left (h : NestTrace (Λ.X × Λ.X) u.length) :=
      ((mergedTraceAppend (Λ.X × Λ.X) r gap).symm h).1
    let before (h : NestTrace (Λ.X × Λ.X) v.length) :=
      ((mergedTraceAppend (Λ.X × Λ.X) u [m']).symm h).1
    PairFresh (B γ) (B γ') v 0 0 (Λ.S₀ G.1) →
    Λ.SoloArrivalH1 p q G K γ γ' s m c A →
    Λ.SoloArrivalH1 p q G K γ γ' u m' c' A' →
    markedPrefixMass p q (K γ) (K γ') v 0 0 x (fun h _ =>
      if (∃ y, soloArrivalState? s m (left (before h)) = some y ∧ c ∈ y.1.val) ∧
         (∃ y, soloArrivalState? u m' h = some y ∧ c' ∈ y.1.val)
      then 1 else 0) / ρ ^ sharedCount v ≤ A' * A := by
  intro G B K r u v left before hFresh hrow hrow'
  have hmem (c : Finset (Vertex d)) (N : Finset (Finset (Vertex d))) :
      (({c} : Finset (Finset (Vertex d))) ∩ N).Nonempty ↔ c ∈ N := by
    simp [Finset.Nonempty, Finset.mem_inter]
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let R := Λ.S₀ G.1
  let F (h : NestTrace (Λ.X × Λ.X) r.length) (_ : Configuration d × Configuration d) :=
    if ∃ y, soloArrivalState? s m h = some y ∧ c ∈ y.1.val then (1:ℝ) else 0
  let F' (h : NestTrace (Λ.X × Λ.X) u.length) z := F (left h) z
  have hFreshU := PairFresh.prefix_of_append (B γ) (B γ') u [m'] 0 0 R hFresh
  have hFreshR := PairFresh.prefix_of_append (B γ) (B γ') r gap 0 0 R hFreshU
  have hFreshS := PairFresh.prefix_of_append (B γ) (B γ') s [m] 0 0 R hFreshR
  have hloc (δ : SourceRoute D M) (i : ℕ) (x y : Λ.X) : IsLocal (B δ i) (K δ i x y) :=
    stepKernel_isLocal _ _ _ _ y
  have hn (δ : SourceRoute D M) (i : ℕ) (x y : Λ.X) (z : Configuration d × Configuration d) :
      0 ≤ K δ i x y z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs δ G i x)) y z
  have h₁ := Λ.firstGood_solo_arrival_mass_le p q ρ κ hκ hρ hs hsite γ γ' z₀
    hbox hpre hcount s m hm x (fun _ _ => 1) (fun _ => {c}) hA (b := 1) (by norm_num)
    hFreshR (fun he => (hrow.1 he).1) (fun he => (hrow.2 he).1)
    (fun _ => isLocal_const _ 1) (fun _ _ => zero_le_one) (fun _ _ _ => by simp)
    (fun _ he hu y hy => by
      have heq := Finset.mem_singleton.mp hy
      subst y
      exact (hrow.1 he).2 _ hu)
    (fun _ he hu y hy => by
      have heq := Finset.mem_singleton.mp hy
      subst y
      exact (hrow.2 he).2 _ hu)
  have hs₀ := Rule.unmarked_prefix_mass_le_one hρ γ γ' G s x hFreshS
  have hF : markedPrefixMass p q (K γ) (K γ') r 0 0 x F / ρ ^ sharedCount r ≤ A := by
    refine le_trans ?_ ((mul_le_mul_of_nonneg_left hs₀ hA).trans_eq (mul_one A))
    simpa only [F, hmem, one_mul] using h₁
  have hFloc (h : NestTrace (Λ.X × Λ.X) r.length) :
      IsLocal (R ∪ mergedTraceBlocks (B γ) (B γ') r 0 0) (F h) := isLocal_const _ _
  have hF₀ (h : NestTrace (Λ.X × Λ.X) r.length) (z : Configuration d × Configuration d) :
      0 ≤ F h z := by unfold F; split_ifs <;> norm_num
  have hg := markedPrefixMass_normalized_suffix_le p q (B γ) (B γ') (K γ) (K γ')
    (hloc γ) (hloc γ') (hn γ) (hn γ') hρ
    (fun i y => (Rule.kernel_row_integral_eq_one hρ γ G i y).le)
    (fun i y => (Rule.kernel_row_integral_eq_one hρ γ' G i y).le)
    (fun i i' y y' => Rule.kernel_pair_row_integral_le hρ γ γ' G i i' y y')
    r gap 0 0 x R hFreshU F hFloc hF₀
  have h₂ := Λ.firstGood_solo_arrival_mass_le p q ρ κ hκ hρ hs hsite γ γ' z₀
    hbox hpre hcount u m' hm' x F' (fun _ => {c'}) hA' (b := 1) (by norm_num)
    hFresh (fun he => (hrow'.1 he).1) (fun he => (hrow'.2 he).1)
    (fun _ => isLocal_const _ _) (fun h z => hF₀ (left h) z) (fun _ _ _ => by simp)
    (fun _ he hu y hy => by
      have heq := Finset.mem_singleton.mp hy
      subst y
      exact (hrow'.1 he).2 _ hu)
    (fun _ he hu y hy => by
      have heq := Finset.mem_singleton.mp hy
      subst y
      exact (hrow'.2 he).2 _ hu)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hg.trans hF) hA')
  let P (h : NestTrace (Λ.X × Λ.X) v.length) :=
    ∃ y, soloArrivalState? s m (left (before h)) = some y ∧ c ∈ y.1.val
  let Q (h : NestTrace (Λ.X × Λ.X) v.length) :=
    ∃ y, soloArrivalState? u m' h = some y ∧ c' ∈ y.1.val
  have h₂' : markedPrefixMass p q (K γ) (K γ') v 0 0 x
      (fun h _ => if Q h then (if P h then 1 else 0) else 0) / ρ ^ sharedCount v ≤
      A' * (markedPrefixMass p q (K γ) (K γ') u 0 0 x F' / ρ ^ sharedCount u) := by
    simpa only [P,Q,F',F,before,hmem,one_mul] using h₂
  refine (le_of_eq ?_).trans h₂'
  apply congrArg (fun F => markedPrefixMass p q (K γ) (K γ') v 0 0 x F / ρ ^ sharedCount v)
  funext h z
  by_cases hP : P h <;> by_cases hQ : Q h <;>
    simp only [P,Q] at hP hQ <;> simp only [P,Q,hP,hQ,true_and,false_and, and_false, ite_true,ite_false]

end NearCritical.Section10.NestLayout
