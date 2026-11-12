module

public import NearCritical.Section10PairedReveal
public import NearCritical.NestFreshTube

/-! Source `lem.nw.mean` on the ACTUAL coupled law: the martingale step.

The space is the project's coupled pair `(percolation d p).prod (percolation d q)`
(supercritical layer `z.1`, retention layer `z.2`, critical layer their thinning).
A function is *local on* a finite bond set `R` if it only reads both layers on `R`.

`chainValue B k m t x` is the remaining weight of a nest chain at step `t` in
state `x` with `m` steps to go: at each step the chain reads its own fresh block
`B t` and moves to `y` with weight `k t x y`. In the source,
`k t x y = P[choice] * 1_{A_t} / s_t * 1_{y in offspring}`; here `k` is ARBITRARY
subject to two actual properties: it is local on `B t`, and its total weight has
mean one under the actual coupled law.

`chainValue_integral`: for pairwise disjoint blocks and any `G` local on a set
disjoint from them (for instance the indicator of a revealed critical cluster
family, or the pre-good indicators of the cubes),
`E[G * chainValue] = E[G]`. No independence between successive successes and no
auxiliary chain law is assumed: the chain is a deterministic function of the
configuration, and the only probabilistic input is the block independence of
the actual product law (`coupled_past_fresh_pair_integral`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- A layered bond: `(false, e)` is the bond `e` in the first layer `z.1`,
`(true, e)` the bond `e` in the second layer `z.2`. -/
abbrev LBond (d : ℕ) : Type := Bool × Bond d

/-- The state of a layered bond in a configuration pair. -/
def layerVal {d : ℕ} (z : Configuration d × Configuration d) (e : LBond d) : Bool :=
  bif e.1 then z.2 e.2 else z.1 e.2

lemma measurable_layerVal {d : ℕ} :
    Measurable (layerVal : Configuration d × Configuration d → LBond d → Bool) := by
  apply measurable_pi_lambda
  rintro ⟨b, e⟩
  cases b
  · exact (measurable_pi_apply e).comp measurable_fst
  · exact (measurable_pi_apply e).comp measurable_snd

/-- `G` reads the configuration pair only on the finite set `R` of layered bonds. -/
def IsLocal {d : ℕ} (R : Finset (LBond d)) (G : Configuration d × Configuration d → ℝ) : Prop :=
  ∃ g : (R → Bool) → ℝ, ∀ z, G z = g (R.restrict (layerVal z))

lemma isLocal_const {d : ℕ} (R : Finset (LBond d)) (c : ℝ) :
    IsLocal R (fun _ : Configuration d × Configuration d => c) :=
  ⟨fun _ => c, fun _ => rfl⟩

lemma IsLocal.mono {d : ℕ} {R R' : Finset (LBond d)} (h : R ⊆ R')
    {G : Configuration d × Configuration d → ℝ} (hG : IsLocal R G) : IsLocal R' G := by
  obtain ⟨g, hg⟩ := hG
  exact ⟨fun b => g (fun e => b ⟨e.1, h e.2⟩), fun z => hg z⟩

lemma IsLocal.mul {d : ℕ} {R : Finset (LBond d)}
    {G K : Configuration d × Configuration d → ℝ} (hG : IsLocal R G) (hK : IsLocal R K) :
    IsLocal R (fun z => G z * K z) := by
  obtain ⟨g, hg⟩ := hG
  obtain ⟨k, hk⟩ := hK
  exact ⟨fun b => g b * k b, fun z => by
    show G z * K z = g _ * k _
    rw [hg z, hk z]⟩

lemma isLocal_sum {d : ℕ} {R : Finset (LBond d)} {Y : Type*} [Fintype Y]
    {F : Y → Configuration d × Configuration d → ℝ} (hF : ∀ y, IsLocal R (F y)) :
    IsLocal R (fun z => ∑ y, F y z) := by
  choose g hg using hF
  exact ⟨fun b => ∑ y, g y b, fun z => Finset.sum_congr rfl (fun y _ => hg y z)⟩

/-- A function factoring through a measurable map into a finite type is integrable. -/
lemma integrable_of_finite_factor {Ω β : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {m : Ω → β} (hm : Measurable m) (φ : β → ℝ) : Integrable (fun ω => φ (m ω)) μ := by
  refine Integrable.of_bound ((measurable_of_finite φ).comp hm).aestronglyMeasurable
    (∑ b, |φ b|) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun b => |φ b|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ _)

/-- Local functions are integrable under the actual coupled law. -/
lemma IsLocal.integrable {d : ℕ} (p q : unitInterval) {R : Finset (LBond d)}
    {G : Configuration d × Configuration d → ℝ} (hG : IsLocal R G) :
    Integrable G ((percolation d p).prod (percolation d q)) := by
  obtain ⟨g, hg⟩ := hG
  have hfun : G = fun z => g (R.restrict (layerVal z)) := funext hg
  rw [hfun]
  exact integrable_of_finite_factor _
    ((Finset.measurable_restrict R).comp measurable_layerVal) g

/-- Single-layer independence of disjoint finite blocks, in integral form. -/
lemma percolation_block_integral_mul {d : ℕ} (p : unitInterval) (S T : Finset (Bond d))
    (hd : Disjoint S T) (F : (S → Bool) → ℝ) (H : (T → Bool) → ℝ) :
    (∫ ω : Configuration d, F (S.restrict ω) * H (T.restrict ω) ∂percolation d p) =
      (∫ ω : Configuration d, F (S.restrict ω) ∂percolation d p) *
        ∫ ω : Configuration d, H (T.restrict ω) ∂percolation d p := by
  have hf := percolation_disjoint_block_integral p S T hd (fun ab => F ab.1 * H ab.2)
  simp_rw [integral_const_mul, integral_mul_const] at hf
  have hS := percolation_disjoint_block_integral p S T hd (fun ab => F ab.1)
  have hT := percolation_disjoint_block_integral p S T hd (fun ab => H ab.2)
  simp only [integral_const, probReal_univ, one_smul] at hS hT
  rwa [← hS, ← hT] at hf

/-- Two-layer independence: a function of the first layer on `R₁` and the second
on `R₂` is independent of one reading `T₁`, `T₂`, when `R₁ ∩ T₁ = ∅ = R₂ ∩ T₂`.
The first-layer set of one may meet the second-layer set of the other. -/
theorem two_layer_integral_mul {d : ℕ} (p q : unitInterval)
    (R₁ R₂ T₁ T₂ : Finset (Bond d)) (h1 : Disjoint R₁ T₁) (h2 : Disjoint R₂ T₂)
    (g : (R₁ → Bool) × (R₂ → Bool) → ℝ) (k : (T₁ → Bool) × (T₂ → Bool) → ℝ) :
    (∫ z : Configuration d × Configuration d,
      g (R₁.restrict z.1, R₂.restrict z.2) * k (T₁.restrict z.1, T₂.restrict z.2)
        ∂((percolation d p).prod (percolation d q))) =
      (∫ z : Configuration d × Configuration d, g (R₁.restrict z.1, R₂.restrict z.2)
        ∂((percolation d p).prod (percolation d q))) *
      ∫ z : Configuration d × Configuration d, k (T₁.restrict z.1, T₂.restrict z.2)
        ∂((percolation d p).prod (percolation d q)) := by
  have hmR : Measurable (fun z : Configuration d × Configuration d =>
      (R₁.restrict z.1, R₂.restrict z.2)) :=
    ((Finset.measurable_restrict R₁).comp measurable_fst).prodMk
      ((Finset.measurable_restrict R₂).comp measurable_snd)
  have hmT : Measurable (fun z : Configuration d × Configuration d =>
      (T₁.restrict z.1, T₂.restrict z.2)) :=
    ((Finset.measurable_restrict T₁).comp measurable_fst).prodMk
      ((Finset.measurable_restrict T₂).comp measurable_snd)
  have hiG := integrable_of_finite_factor ((percolation d p).prod (percolation d q)) hmR g
  have hiK := integrable_of_finite_factor ((percolation d p).prod (percolation d q)) hmT k
  have hiGK := integrable_of_finite_factor ((percolation d p).prod (percolation d q))
    (hmR.prodMk hmT) (fun b => g b.1 * k b.2)
  rw [integral_prod _ hiGK, integral_prod _ hiG, integral_prod _ hiK]
  have hinner : ∀ x : Configuration d,
      (∫ y : Configuration d, g (R₁.restrict x, R₂.restrict y) * k (T₁.restrict x, T₂.restrict y)
        ∂percolation d q) =
      (∫ y : Configuration d, g (R₁.restrict x, R₂.restrict y) ∂percolation d q) *
        ∫ y : Configuration d, k (T₁.restrict x, T₂.restrict y) ∂percolation d q :=
    fun x => percolation_block_integral_mul q R₂ T₂ h2
      (fun b => g (R₁.restrict x, b)) (fun b => k (T₁.restrict x, b))
  simp only [hinner]
  exact percolation_block_integral_mul p R₁ T₁ h1
    (fun a => ∫ y : Configuration d, g (a, R₂.restrict y) ∂percolation d q)
    (fun a => ∫ y : Configuration d, k (a, T₂.restrict y) ∂percolation d q)

/-- The bonds of layer `b` in a layered set. -/
def layerBonds {d : ℕ} (b : Bool) (R : Finset (LBond d)) : Finset (Bond d) :=
  (R.filter (fun e => e.1 = b)).image Prod.snd

lemma mem_layerBonds {d : ℕ} {b : Bool} {R : Finset (LBond d)} {e : LBond d}
    (he : e ∈ R) (hb : e.1 = b) : e.2 ∈ layerBonds b R :=
  Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hb⟩, rfl⟩

lemma layerBonds_disjoint {d : ℕ} (b : Bool) {R T : Finset (LBond d)} (h : Disjoint R T) :
    Disjoint (layerBonds b R) (layerBonds b T) := by
  rw [Finset.disjoint_left] at h ⊢
  intro e heR heT
  obtain ⟨e1, h1, rfl⟩ := Finset.mem_image.mp heR
  obtain ⟨e2, h2, h3⟩ := Finset.mem_image.mp heT
  rw [Finset.mem_filter] at h1 h2
  have : e2 = e1 := Prod.ext (h2.2.trans h1.2.symm) h3
  rw [this] at h2
  exact h h1.1 h2.1

/-- A local function, written through its two layers. -/
lemma IsLocal.exists_layers {d : ℕ} {R : Finset (LBond d)}
    {G : Configuration d × Configuration d → ℝ} (hG : IsLocal R G) :
    ∃ g' : (layerBonds false R → Bool) × (layerBonds true R → Bool) → ℝ,
      ∀ z, G z = g' ((layerBonds false R).restrict z.1, (layerBonds true R).restrict z.2) := by
  obtain ⟨g, hg⟩ := hG
  refine ⟨fun uv => g (fun i : R =>
    if h : i.1.1 = true then uv.2 ⟨i.1.2, mem_layerBonds i.2 h⟩
    else uv.1 ⟨i.1.2, mem_layerBonds i.2 (Bool.eq_false_iff.mpr h)⟩), fun z => ?_⟩
  rw [hg z]
  congr 1
  funext i
  obtain ⟨⟨b, e⟩, hi⟩ := i
  cases b
  · simp [layerVal]
  · simp [layerVal]

/-- Functions local on disjoint sets of layered bonds are independent under the
actual coupled law. -/
theorem IsLocal.integral_mul {d : ℕ} (p q : unitInterval) {R T : Finset (LBond d)}
    (hd : Disjoint R T) {G K : Configuration d × Configuration d → ℝ}
    (hG : IsLocal R G) (hK : IsLocal T K) :
    (∫ z, G z * K z ∂((percolation d p).prod (percolation d q))) =
      (∫ z, G z ∂((percolation d p).prod (percolation d q))) *
        (∫ z, K z ∂((percolation d p).prod (percolation d q))) := by
  obtain ⟨g, hg⟩ := hG.exists_layers
  obtain ⟨k, hk⟩ := hK.exists_layers
  have h := two_layer_integral_mul p q _ _ _ _ (layerBonds_disjoint false hd)
    (layerBonds_disjoint true hd) g k
  simp only [hg, hk]
  exact h

/-- Remaining chain weight at step `t`, state `x`, with `m` steps to go. -/
def chainValue {d : ℕ} {X : Type*} [Fintype X]
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ) :
    ℕ → ℕ → X → Configuration d × Configuration d → ℝ
  | 0, _, _, _ => 1
  | m+1, t, x, z => ∑ y, k t x y z * chainValue k m (t+1) y z

/-- The chain weight from step `t` reads only the blocks `B t, ..., B (t+m-1)`. -/
lemma chainValue_isLocal {d : ℕ} {X : Type*} [Fintype X] (B : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) :
    ∀ (m t : ℕ) (x : X),
      IsLocal ((Finset.range m).biUnion (fun j => B (t+j))) (chainValue k m t x) := by
  intro m
  induction m with
  | zero =>
    intro t x
    exact isLocal_const _ 1
  | succ m ih =>
    intro t x
    change IsLocal _ (fun z => ∑ y, k t x y z * chainValue k m (t+1) y z)
    apply isLocal_sum
    intro y
    apply IsLocal.mul
    · refine (hk t x y).mono ?_
      intro e he
      exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos m), by simpa using he⟩
    · refine (ih (t+1) y).mono ?_
      intro e he
      obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
      refine Finset.mem_biUnion.mpr ⟨j+1, Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hj
        omega), ?_⟩
      have hidx : t + (j+1) = t + 1 + j := by omega
      rw [hidx]
      exact hej

/-- **Source `lem.nw.mean`, martingale step on the actual coupled law.** If the
blocks are pairwise disjoint, every step kernel is local on its block and has
total weight of mean one, then the chain weight is conditionally mean one given
anything local on a bond set disjoint from the remaining blocks. -/
theorem chainValue_integral {d : ℕ} {X : Type*} [Fintype X] (p q : unitInterval)
    (B : ℕ → Finset (LBond d))
    (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y))
    (hnorm : ∀ t x, (∫ z, ∑ y, k t x y z ∂((percolation d p).prod (percolation d q))) = 1) :
    ∀ (m t : ℕ) (x : X) (R : Finset (LBond d)) (G : Configuration d × Configuration d → ℝ),
      IsLocal R G → (∀ j, j < m → Disjoint R (B (t+j))) →
      (∫ z, G z * chainValue k m t x z ∂((percolation d p).prod (percolation d q))) =
        ∫ z, G z ∂((percolation d p).prod (percolation d q)) := by
  intro m
  induction m with
  | zero =>
    intro t x R G _ _
    simp only [chainValue, mul_one]
  | succ m ih =>
    intro t x R G hG hR
    have hRt : Disjoint R (B t) := by
      have h := hR 0 (Nat.succ_pos m)
      simpa using h
    -- each summand: move `k` next to `G`, then apply the induction hypothesis
    have hterm : ∀ y, (∫ z, (G z * k t x y z) * chainValue k m (t+1) y z
        ∂((percolation d p).prod (percolation d q))) =
        ∫ z, G z * k t x y z ∂((percolation d p).prod (percolation d q)) := by
      intro y
      have hloc : IsLocal (R ∪ B t) (fun z => G z * k t x y z) :=
        (hG.mono Finset.subset_union_left).mul ((hk t x y).mono Finset.subset_union_right)
      refine ih (t+1) y (R ∪ B t) (fun z => G z * k t x y z) hloc ?_
      intro j hj
      have hidx : t + 1 + j = t + (j+1) := by omega
      rw [hidx, Finset.disjoint_union_left]
      exact ⟨hR (j+1) (by omega), hB t (t+(j+1)) (by omega)⟩
    have hint : ∀ y, Integrable (fun z => (G z * k t x y z) * chainValue k m (t+1) y z)
        ((percolation d p).prod (percolation d q)) := by
      intro y
      have hV := chainValue_isLocal B k hk m (t+1) y
      have hall : IsLocal (R ∪ B t ∪ (Finset.range m).biUnion (fun j => B (t+1+j)))
          (fun z => (G z * k t x y z) * chainValue k m (t+1) y z) :=
        (((hG.mono Finset.subset_union_left).mul
          ((hk t x y).mono Finset.subset_union_right)).mono Finset.subset_union_left).mul
          (hV.mono Finset.subset_union_right)
      exact hall.integrable p q
    have hint2 : ∀ y, Integrable (fun z => G z * k t x y z)
        ((percolation d p).prod (percolation d q)) := by
      intro y
      exact ((hG.mono (Finset.subset_union_left (s₂ := B t))).mul
        ((hk t x y).mono Finset.subset_union_right)).integrable p q
    have hsumloc : IsLocal (B t) (fun z => ∑ y, k t x y z) := isLocal_sum (hk t x)
    calc (∫ z, G z * chainValue k (m+1) t x z ∂((percolation d p).prod (percolation d q)))
        = ∫ z, ∑ y, (G z * k t x y z) * chainValue k m (t+1) y z
            ∂((percolation d p).prod (percolation d q)) := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall fun z => ?_
          change G z * (∑ y, k t x y z * chainValue k m (t+1) y z) = _
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => (mul_assoc _ _ _).symm)
      _ = ∑ y, ∫ z, (G z * k t x y z) * chainValue k m (t+1) y z
            ∂((percolation d p).prod (percolation d q)) :=
          integral_finset_sum _ (fun y _ => hint y)
      _ = ∑ y, ∫ z, G z * k t x y z ∂((percolation d p).prod (percolation d q)) :=
          Finset.sum_congr rfl (fun y _ => hterm y)
      _ = ∫ z, ∑ y, G z * k t x y z ∂((percolation d p).prod (percolation d q)) :=
          (integral_finset_sum _ (fun y _ => hint2 y)).symm
      _ = ∫ z, G z * ∑ y, k t x y z ∂((percolation d p).prod (percolation d q)) := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall fun z => ?_
          exact (Finset.mul_sum _ _ _).symm
      _ = (∫ z, G z ∂((percolation d p).prod (percolation d q))) *
            ∫ z, ∑ y, k t x y z ∂((percolation d p).prod (percolation d q)) :=
          IsLocal.integral_mul p q hRt hG hsumloc
      _ = ∫ z, G z ∂((percolation d p).prod (percolation d q)) := by
          rw [hnorm t x, mul_one]

/-! ### The source step kernel `iota_t * (uniform choice among offspring)` -/

/-- Conditional success probability of a step: the actual probability that the
fresh block `T` lands in the success set `a`. -/
def localSuccessProbability {d : ℕ} (p q : unitInterval) (T : Finset (LBond d))
    (a : Set ((T → Bool))) : ℝ :=
  ∫ z : Configuration d × Configuration d,
    (if (T.restrict (layerVal z)) ∈ a then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q))

/-- Source kernel of one step: on success (fresh bits in `a`) the chain moves to
a uniformly chosen element of the offspring `o bits`, with the normalised
indicator `1/s`; on failure it has weight zero. -/
def stepKernel {d : ℕ} {X : Type*} (T : Finset (LBond d))
    (a : Set ((T → Bool))) (o : (T → Bool) → Finset X)
    (s : ℝ) (y : X) (z : Configuration d × Configuration d) : ℝ :=
  if (T.restrict (layerVal z)) ∈ a ∧ y ∈ o (T.restrict (layerVal z)) then
    (s * ((o (T.restrict (layerVal z))).card : ℝ))⁻¹ else 0

lemma stepKernel_isLocal {d : ℕ} {X : Type*} (T : Finset (LBond d))
    (a : Set ((T → Bool))) (o : (T → Bool) → Finset X)
    (s : ℝ) (y : X) : IsLocal T (stepKernel T a o s y) :=
  ⟨fun b => if b ∈ a ∧ y ∈ o b then (s * ((o b).card : ℝ))⁻¹ else 0, fun _ => rfl⟩

/-- Summing the kernel over the next state leaves the normalised indicator. -/
lemma stepKernel_sum {d : ℕ} {X : Type*} [Fintype X] (T : Finset (LBond d))
    (a : Set ((T → Bool))) (o : (T → Bool) → Finset X)
    (ho : ∀ b ∈ a, (o b).Nonempty) (s : ℝ) (z : Configuration d × Configuration d) :
    (∑ y, stepKernel T a o s y z) =
      (if (T.restrict (layerVal z)) ∈ a then (1:ℝ) else 0) * s⁻¹ := by
  by_cases hz : (T.restrict (layerVal z)) ∈ a
  · have hc : ((o (T.restrict (layerVal z))).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (ho _ hz)).ne'
    have hterm : ∀ y, stepKernel T a o s y z =
        if y ∈ o (T.restrict (layerVal z)) then
          (s * ((o (T.restrict (layerVal z))).card : ℝ))⁻¹ else 0 := by
      intro y
      unfold stepKernel
      by_cases hy : y ∈ o (T.restrict (layerVal z))
      · have h1 : (T.restrict (layerVal z)) ∈ a ∧
            y ∈ o (T.restrict (layerVal z)) := ⟨hz, hy⟩
        rw [if_pos h1, if_pos hy]
      · have h1 : ¬ ((T.restrict (layerVal z)) ∈ a ∧
            y ∈ o (T.restrict (layerVal z))) := fun h => hy h.2
        rw [if_neg h1, if_neg hy]
    have h1 : (∑ y ∈ o (T.restrict (layerVal z)),
        (if y ∈ o (T.restrict (layerVal z)) then
          (s * ((o (T.restrict (layerVal z))).card : ℝ))⁻¹ else 0)) =
        ∑ y, (if y ∈ o (T.restrict (layerVal z)) then
          (s * ((o (T.restrict (layerVal z))).card : ℝ))⁻¹ else 0) :=
      Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => if_neg hy)
    have h2 : (∑ y ∈ o (T.restrict (layerVal z)),
        (if y ∈ o (T.restrict (layerVal z)) then
          (s * ((o (T.restrict (layerVal z))).card : ℝ))⁻¹ else 0)) =
        ∑ _y ∈ o (T.restrict (layerVal z)),
          (s * ((o (T.restrict (layerVal z))).card : ℝ))⁻¹ :=
      Finset.sum_congr rfl (fun y hy => if_pos hy)
    rw [Finset.sum_congr rfl (fun y _ => hterm y), ← h1, h2, Finset.sum_const, nsmul_eq_mul,
      if_pos hz, one_mul, mul_inv, mul_comm s⁻¹, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  · have hterm : ∀ y, stepKernel T a o s y z = 0 := by
      intro y
      unfold stepKernel
      have h1 : ¬ ((T.restrict (layerVal z)) ∈ a ∧
          y ∈ o (T.restrict (layerVal z))) := fun h => hz h.1
      rw [if_neg h1]
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_const_zero, if_neg hz, zero_mul]

/-- With `s` the actual success probability, the step kernel has total weight
of mean one: this is `E[iota_t | past] = 1`. -/
theorem stepKernel_integral_eq_one {d : ℕ} {X : Type*} [Fintype X] (p q : unitInterval)
    (T : Finset (LBond d)) (a : Set ((T → Bool)))
    (o : (T → Bool) → Finset X) (ho : ∀ b ∈ a, (o b).Nonempty)
    (hs : 0 < localSuccessProbability p q T a) :
    (∫ z, ∑ y, stepKernel T a o (localSuccessProbability p q T a) y z
      ∂((percolation d p).prod (percolation d q))) = 1 := by
  have hfun : (fun z : Configuration d × Configuration d =>
      ∑ y, stepKernel T a o (localSuccessProbability p q T a) y z) =
      fun z : Configuration d × Configuration d =>
        (if (T.restrict (layerVal z)) ∈ a then (1:ℝ) else 0) *
          (localSuccessProbability p q T a)⁻¹ :=
    funext fun z => stepKernel_sum T a o ho _ z
  rw [hfun, integral_mul_const]
  exact mul_inv_cancel₀ hs.ne'

/-! ### Conditioning on the revealed data -/

/-- **Source `lem.nw.mean` for one route, on the actual coupled law.** Let `ρ` be
any finite-valued reveal (in the source, the union `G` of the critical heart
clusters of the cubes), whose atoms `{ρ = F}` are local on bond sets `S F`. On
each atom the chain uses its own blocks `B F t`, disjoint from `S F` and from
each other, and its own step kernels, local on their blocks and of mean-one
total weight. Then the weighted chain value integrates like the weight alone:
`E[w(ρ) * zeta] = E[w(ρ)]`. -/
theorem revealed_chain_mean {d : ℕ} {X Φ : Type*} [Fintype X] [Fintype Φ]
    (p q : unitInterval) (ρ : Configuration d × Configuration d → Φ)
    (S : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (B : Φ → ℕ → Finset (LBond d))
    (hB : ∀ F i j, i ≠ j → Disjoint (B F i) (B F j))
    (hSB : ∀ F j, Disjoint (S F) (B F j))
    (k : Φ → ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ F t x y, IsLocal (B F t) (k F t x y))
    (hnorm : ∀ F t x,
      (∫ z, ∑ y, k F t x y z ∂((percolation d p).prod (percolation d q))) = 1)
    (w : Φ → ℝ) (n : Φ → ℕ) (x₀ : Φ → X) :
    (∫ z, w (ρ z) * chainValue (k (ρ z)) (n (ρ z)) 0 (x₀ (ρ z)) z
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z, w (ρ z) ∂((percolation d p).prod (percolation d q)) := by
  have hsplit : ∀ z, w (ρ z) * chainValue (k (ρ z)) (n (ρ z)) 0 (x₀ (ρ z)) z =
      ∑ F, ((if ρ z = F then (1:ℝ) else 0) * w F) * chainValue (k F) (n F) 0 (x₀ F) z := by
    intro z
    rw [Finset.sum_eq_single (ρ z)]
    · rw [if_pos rfl, one_mul]
    · intro F _ hF
      rw [if_neg (Ne.symm hF), zero_mul, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsplit2 : ∀ z, w (ρ z) = ∑ F, (if ρ z = F then (1:ℝ) else 0) * w F := by
    intro z
    rw [Finset.sum_eq_single (ρ z)]
    · rw [if_pos rfl, one_mul]
    · intro F _ hF
      rw [if_neg (Ne.symm hF), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hloc : ∀ F, IsLocal (S F) (fun z => (if ρ z = F then (1:ℝ) else 0) * w F) :=
    fun F => (hρ F).mul (isLocal_const (S F) (w F))
  have hterm : ∀ F, (∫ z, ((if ρ z = F then (1:ℝ) else 0) * w F) *
      chainValue (k F) (n F) 0 (x₀ F) z ∂((percolation d p).prod (percolation d q))) =
      ∫ z, (if ρ z = F then (1:ℝ) else 0) * w F
        ∂((percolation d p).prod (percolation d q)) := by
    intro F
    refine chainValue_integral p q (B F) (hB F) (k F) (hk F) (hnorm F) (n F) 0 (x₀ F) (S F)
      (fun z => (if ρ z = F then (1:ℝ) else 0) * w F) (hloc F) ?_
    intro j _
    rw [Nat.zero_add]
    exact hSB F j
  have hint : ∀ F, Integrable (fun z => ((if ρ z = F then (1:ℝ) else 0) * w F) *
      chainValue (k F) (n F) 0 (x₀ F) z) ((percolation d p).prod (percolation d q)) := by
    intro F
    have hV := chainValue_isLocal (B F) (k F) (hk F) (n F) 0 (x₀ F)
    exact (((hloc F).mono Finset.subset_union_left).mul
      (hV.mono Finset.subset_union_right)).integrable p q
  have hint2 : ∀ F, Integrable (fun z => (if ρ z = F then (1:ℝ) else 0) * w F)
      ((percolation d p).prod (percolation d q)) := fun F => (hloc F).integrable p q
  calc (∫ z, w (ρ z) * chainValue (k (ρ z)) (n (ρ z)) 0 (x₀ (ρ z)) z
        ∂((percolation d p).prod (percolation d q)))
      = ∫ z, ∑ F, ((if ρ z = F then (1:ℝ) else 0) * w F) * chainValue (k F) (n F) 0 (x₀ F) z
          ∂((percolation d p).prod (percolation d q)) :=
        integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = ∑ F, ∫ z, ((if ρ z = F then (1:ℝ) else 0) * w F) * chainValue (k F) (n F) 0 (x₀ F) z
          ∂((percolation d p).prod (percolation d q)) :=
        integral_finset_sum _ (fun F _ => hint F)
    _ = ∑ F, ∫ z, (if ρ z = F then (1:ℝ) else 0) * w F
          ∂((percolation d p).prod (percolation d q)) :=
        Finset.sum_congr rfl (fun F _ => hterm F)
    _ = ∫ z, ∑ F, (if ρ z = F then (1:ℝ) else 0) * w F
          ∂((percolation d p).prod (percolation d q)) :=
        (integral_finset_sum _ (fun F _ => hint2 F)).symm
    _ = ∫ z, w (ρ z) ∂((percolation d p).prod (percolation d q)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => (hsplit2 z).symm)

end NearCritical.Section10
