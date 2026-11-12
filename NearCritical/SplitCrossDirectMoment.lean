module

public import NearCritical.SplitCrossDirectTreeEvent

/-! Moment recursion (item B of the direct proof of `SplitCrossInput`,
summation over terminals).

For a finite domain `D`, a root `u`, and a finite terminal set `Y`, let
`P a b = P[a ↔ b inside D]`, a leaf mass `m ≥ sup_u Σ_{v ∈ Y} P u v` and a
branch mass `B ≥ sup_u Σ_{w ∈ D} P u w`.

* `sum_mul_sum_of_disjoint_coords`: for functions of tuples `y : ι → V` (`ι` a finite label type; decidable equality is classical
  throughout, as in `treeBound`)
  depending on disjoint coordinate sets, `(Σ_y f)(Σ_y g) = |Y|^N Σ_y f g`.
* `gN m B n k`: the recursion `g(n+1, k) = [k = 1] m + B Σ_{0<j<k} C(k,j) g(n,j) g(n,k-j)`.
* `sum_treeBound_le`: `Σ_{y ∈ Y^N} treeBound y n u S ≤ |Y|^(N - |S|) g(n, |S|)`.
* `sum_connections_le`: `Σ_{y ∈ Y^ι} P[u ↔ y_i inside D for all i] ≤ g(|ι|, |ι|)`.

The last sum is the `N`-th moment of the number of points of `Y` joined to `u`
inside `D`. Homogeneity `g(n,k) = γ(n,k) m^k B^(k-1)` and the moment identity
are in the next file.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory
open scoped Classical BigOperators

variable {d : ℕ}

/-- Functions of disjoint coordinate blocks decouple under the sum over tuples. -/
theorem sum_mul_sum_of_disjoint_coords {ι : Type*} [Fintype ι] {V : Type*} (Y : Finset V)
    (A B : Finset (ι)) (hAB : Disjoint A B) (f g : (ι → V) → ℝ)
    (hf : ∀ y y' : ι → V, (∀ i ∈ A, y i = y' i) → f y = f y')
    (hg : ∀ y y' : ι → V, (∀ i ∈ B, y i = y' i) → g y = g y') :
    (∑ y ∈ Fintype.piFinset (fun _ : ι => Y), f y) *
        (∑ y ∈ Fintype.piFinset (fun _ : ι => Y), g y) =
      (Y.card : ℝ) ^ Fintype.card ι * ∑ y ∈ Fintype.piFinset (fun _ : ι => Y), f y * g y := by
  have hcard : ((Fintype.piFinset (fun _ : ι => Y)).card : ℝ) = (Y.card : ℝ) ^ Fintype.card ι := by
    rw [Fintype.card_piFinset]
    simp
  have hR : (Y.card : ℝ) ^ Fintype.card ι * ∑ y ∈ Fintype.piFinset (fun _ : ι => Y), f y * g y =
      ∑ q ∈ Fintype.piFinset (fun _ : ι => Y) ×ˢ Fintype.piFinset (fun _ : ι => Y),
        f q.1 * g q.1 := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hconst : ∀ y1 ∈ Fintype.piFinset (fun _ : ι => Y),
        f (y, y1).1 * g (y, y1).1 = f y * g y := fun _ _ => rfl
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hcard]
  rw [hR, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun q => (fun k => if k ∈ B then q.2 k else q.1 k, fun k => if k ∈ B then q.1 k else q.2 k))
    (fun q => (fun k => if k ∈ B then q.2 k else q.1 k, fun k => if k ∈ B then q.1 k else q.2 k))
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    rw [Fintype.mem_piFinset] at h1 h2
    refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun k => ?_),
      Fintype.mem_piFinset.mpr (fun k => ?_)⟩
    · show (if k ∈ B then q.2 k else q.1 k) ∈ Y
      split_ifs
      · exact h2 k
      · exact h1 k
    · show (if k ∈ B then q.1 k else q.2 k) ∈ Y
      split_ifs
      · exact h1 k
      · exact h2 k
  · intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    rw [Fintype.mem_piFinset] at h1 h2
    refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun k => ?_),
      Fintype.mem_piFinset.mpr (fun k => ?_)⟩
    · show (if k ∈ B then q.2 k else q.1 k) ∈ Y
      split_ifs
      · exact h2 k
      · exact h1 k
    · show (if k ∈ B then q.1 k else q.2 k) ∈ Y
      split_ifs
      · exact h1 k
      · exact h2 k
  · intro q _
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show (if k ∈ B then (if k ∈ B then q.1 k else q.2 k) else (if k ∈ B then q.2 k else q.1 k))
        = q.1 k
      split_ifs <;> rfl
    · show (if k ∈ B then (if k ∈ B then q.2 k else q.1 k) else (if k ∈ B then q.1 k else q.2 k))
        = q.2 k
      split_ifs <;> rfl
  · intro q _
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show (if k ∈ B then (if k ∈ B then q.1 k else q.2 k) else (if k ∈ B then q.2 k else q.1 k))
        = q.1 k
      split_ifs <;> rfl
    · show (if k ∈ B then (if k ∈ B then q.2 k else q.1 k) else (if k ∈ B then q.1 k else q.2 k))
        = q.2 k
      split_ifs <;> rfl
  · intro q _
    show f q.1 * g q.2 = f (fun k => if k ∈ B then q.2 k else q.1 k) *
      g (fun k => if k ∈ B then q.2 k else q.1 k)
    rw [hf q.1 (fun k => if k ∈ B then q.2 k else q.1 k) (fun i hi => by
        rw [if_neg (Finset.disjoint_left.mp hAB hi)]),
      hg q.2 (fun k => if k ∈ B then q.2 k else q.1 k) (fun i hi => by rw [if_pos hi])]

/-- A sum over tuples of a function of one coordinate. -/
theorem sum_piFinset_apply {ι : Type*} [Fintype ι] {V : Type*} (Y : Finset V) (i : ι) (F : V → ℝ) :
    ∑ y ∈ Fintype.piFinset (fun _ : ι => Y), F (y i) =
      (∑ v ∈ Y, F v) * (Y.card : ℝ) ^ (Fintype.card ι - 1) := by
  have h := Finset.prod_univ_sum (fun _ : ι => Y)
    (fun (k : ι) (v : V) => if k = i then F v else (1 : ℝ))
  have hL : ∀ y : ι → V, (∏ k, (if k = i then F (y k) else (1 : ℝ))) = F (y i) := by
    intro y
    rw [Finset.prod_ite_eq' Finset.univ i (fun k => F (y k))]
    simp
  have hRk : ∀ k : ι, (∑ v ∈ Y, if k = i then F v else (1 : ℝ)) =
      if k = i then ∑ v ∈ Y, F v else (Y.card : ℝ) := by
    intro k
    split_ifs
    · rfl
    · simp
  simp_rw [hL, hRk] at h
  rw [← h, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk)),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

/-- `treeBound` reads the terminals only at the labels of `S`. -/
theorem treeBound_congr (P : Vertex d → Vertex d → ℝ) (Dfin : Finset (Vertex d)) {ι : Type*} :
    ∀ (n : ℕ) (u : Vertex d) (S : Finset ι) (y y' : ι → Vertex d), (∀ i ∈ S, y i = y' i) →
      treeBound P Dfin y n u S = treeBound P Dfin y' n u S
  | 0, _, _, _, _, _ => rfl
  | n+1, u, S, y, y', h => by
    show (∑ i ∈ S, if S = {i} then P u (y i) else 0) +
        ∑ w ∈ Dfin, ∑ A ∈ S.powerset,
          (if A.Nonempty ∧ (S \ A).Nonempty then
            P u w * treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) else 0) =
      (∑ i ∈ S, if S = {i} then P u (y' i) else 0) +
        ∑ w ∈ Dfin, ∑ A ∈ S.powerset,
          (if A.Nonempty ∧ (S \ A).Nonempty then
            P u w * treeBound P Dfin y' n w A * treeBound P Dfin y' n w (S \ A) else 0)
    congr 1
    · exact Finset.sum_congr rfl (fun i hi => by rw [h i hi])
    · refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun A hA => ?_))
      have hAS := Finset.mem_powerset.mp hA
      rw [treeBound_congr P Dfin n w A y y' (fun i hi => h i (hAS hi)),
        treeBound_congr P Dfin n w (S \ A) y y' (fun i hi => h i (Finset.sdiff_subset hi))]

theorem treeBound_nonneg (P : Vertex d → Vertex d → ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (Dfin : Finset (Vertex d)) {ι : Type*} (y : ι → Vertex d) :
    ∀ (n : ℕ) (u : Vertex d) (S : Finset ι), 0 ≤ treeBound P Dfin y n u S
  | 0, _, _ => le_rfl
  | n+1, u, S => by
    show 0 ≤ (∑ i ∈ S, if S = {i} then P u (y i) else 0) +
        ∑ w ∈ Dfin, ∑ A ∈ S.powerset,
          (if A.Nonempty ∧ (S \ A).Nonempty then
            P u w * treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) else 0)
    refine add_nonneg (Finset.sum_nonneg (fun i _ => ?_))
      (Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun A _ => ?_)))
    · split_ifs
      · exact hP _ _
      · exact le_rfl
    · split_ifs
      · exact mul_nonneg (mul_nonneg (hP _ _) (treeBound_nonneg P hP Dfin y n w A))
          (treeBound_nonneg P hP Dfin y n w (S \ A))
      · exact le_rfl

/-- The moment recursion. -/
def gN (m B : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n+1, k => (if k = 1 then m else 0) +
      B * ∑ j ∈ Finset.Ico 1 k, (k.choose j : ℝ) * gN m B n j * gN m B n (k - j)

theorem gN_nonneg {m B : ℝ} (hm : 0 ≤ m) (hB : 0 ≤ B) : ∀ n k : ℕ, 0 ≤ gN m B n k
  | 0, _ => le_rfl
  | n+1, k => by
    show 0 ≤ (if k = 1 then m else 0) +
      B * ∑ j ∈ Finset.Ico 1 k, (k.choose j : ℝ) * gN m B n j * gN m B n (k - j)
    refine add_nonneg (by split_ifs <;> [exact hm; exact le_rfl])
      (mul_nonneg hB (Finset.sum_nonneg (fun j _ => ?_)))
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (gN_nonneg hm hB n j))
      (gN_nonneg hm hB n (k - j))

theorem treeBound_succ (P : Vertex d → Vertex d → ℝ) (Dfin : Finset (Vertex d)) {ι : Type*}
    (y : ι → Vertex d) (n : ℕ) (u : Vertex d) (S : Finset ι) :
    treeBound P Dfin y (n + 1) u S =
      (∑ i ∈ S, if S = {i} then P u (y i) else 0) +
        ∑ w ∈ Dfin, ∑ A ∈ S.powerset,
          if A.Nonempty ∧ (S \ A).Nonempty then
            P u w * treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) else 0 := rfl

theorem gN_succ (m B : ℝ) (n k : ℕ) :
    gN m B (n + 1) k = (if k = 1 then m else 0) +
      B * ∑ j ∈ Finset.Ico 1 k, (k.choose j : ℝ) * gN m B n j * gN m B n (k - j) := rfl

set_option maxHeartbeats 800000 in
/-- **Summed tree-graph bound.** -/
theorem sum_treeBound_le {ι : Type*} [Fintype ι] (P : Vertex d → Vertex d → ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (Dfin Y : Finset (Vertex d)) (hY : 0 < Y.card) {m B : ℝ} (hm0 : 0 ≤ m) (hB0 : 0 ≤ B)
    (hm : ∀ u, ∑ v ∈ Y, P u v ≤ m) (hB : ∀ u, ∑ w ∈ Dfin, P u w ≤ B) :
    ∀ (n : ℕ) (u : Vertex d) (S : Finset (ι)),
      ∑ y ∈ Fintype.piFinset (fun _ : ι => Y), treeBound P Dfin y n u S ≤
        (Y.card : ℝ) ^ (Fintype.card ι - S.card) * gN m B n S.card
  | 0, u, S => by
    show ∑ y ∈ Fintype.piFinset (fun _ : ι => Y), (0 : ℝ) ≤
      (Y.card : ℝ) ^ (Fintype.card ι - S.card) * 0
    simp
  | n+1, u, S => by
    have ih := sum_treeBound_le (ι := ι) P hP Dfin Y hY hm0 hB0 hm hB n
    have hc0 : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY
    have hSN : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    rw [gN_succ]
    simp_rw [treeBound_succ]
    rw [Finset.sum_add_distrib, mul_add]
    refine add_le_add ?_ ?_
    · -- leaf part
      by_cases hS : ∃ i, S = {i}
      · obtain ⟨i, rfl⟩ := hS
        simp only [Finset.sum_singleton, ↓reduceIte]
        rw [sum_piFinset_apply Y i (fun v => P u v), Finset.card_singleton, if_pos rfl, mul_comm]
        exact mul_le_mul_of_nonneg_left (hm u) (pow_nonneg hc0.le _)
      · have hz : ∀ y : ι → Vertex d, (∑ i ∈ S, if S = {i} then P u (y i) else 0) = 0 :=
          fun y => Finset.sum_eq_zero (fun i _ => if_neg (fun h => hS ⟨i, h⟩))
        simp_rw [hz]
        rw [Finset.sum_const_zero]
        exact mul_nonneg (pow_nonneg hc0.le _) (by split_ifs <;> [exact hm0; exact le_rfl])
    · -- branch part
      have hpair : ∀ (w : Vertex d) (A : Finset (ι)), A ⊆ S → A.Nonempty →
          (S \ A).Nonempty →
          ∑ y ∈ Fintype.piFinset (fun _ : ι => Y),
              treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) ≤
            (Y.card : ℝ) ^ (Fintype.card ι - S.card) * (gN m B n A.card * gN m B n (S.card - A.card)) := by
        intro w A hAS hA hB'
        have hsw := sum_mul_sum_of_disjoint_coords Y A (S \ A) Finset.disjoint_sdiff
          (fun y => treeBound P Dfin y n w A) (fun y => treeBound P Dfin y n w (S \ A))
          (fun y y' h => treeBound_congr P Dfin n w A y y' h)
          (fun y y' h => treeBound_congr P Dfin n w (S \ A) y y' h)
        have h1 := ih w A
        have h2 := ih w (S \ A)
        have hcardB : (S \ A).card = S.card - A.card := Finset.card_sdiff_of_subset hAS
        have hAle : A.card ≤ S.card := Finset.card_le_card hAS
        rw [hcardB] at h2
        have hs1 : 0 ≤ ∑ y ∈ Fintype.piFinset (fun _ : ι => Y), treeBound P Dfin y n w A :=
          Finset.sum_nonneg (fun y _ => treeBound_nonneg P hP Dfin y n w A)
        have hg2 : 0 ≤ (Y.card : ℝ) ^ (Fintype.card ι - (S.card - A.card)) * gN m B n (S.card - A.card) :=
          mul_nonneg (pow_nonneg hc0.le _) (gN_nonneg hm0 hB0 _ _)
        have hprod := mul_le_mul h1 h2
          (Finset.sum_nonneg (fun y _ => treeBound_nonneg P hP Dfin y n w (S \ A)))
          (mul_nonneg (pow_nonneg hc0.le _) (gN_nonneg hm0 hB0 _ _))
        rw [hsw] at hprod
        have hexp : (Y.card : ℝ) ^ (Fintype.card ι - A.card) * (Y.card : ℝ) ^ (Fintype.card ι - (S.card - A.card)) =
            (Y.card : ℝ) ^ Fintype.card ι * (Y.card : ℝ) ^ (Fintype.card ι - S.card) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        have hcN : (0 : ℝ) < (Y.card : ℝ) ^ Fintype.card ι := pow_pos hc0 _
        have hfin : (Y.card : ℝ) ^ Fintype.card ι *
            ∑ y ∈ Fintype.piFinset (fun _ : ι => Y),
              treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) ≤
            (Y.card : ℝ) ^ Fintype.card ι * ((Y.card : ℝ) ^ (Fintype.card ι - S.card) *
              (gN m B n A.card * gN m B n (S.card - A.card))) := by
          calc _ ≤ _ := hprod
            _ = (Y.card : ℝ) ^ (Fintype.card ι - A.card) * (Y.card : ℝ) ^ (Fintype.card ι - (S.card - A.card)) *
                (gN m B n A.card * gN m B n (S.card - A.card)) := by ring
            _ = _ := by rw [hexp]; ring
        exact le_of_mul_le_mul_left hfin hcN
      -- exchange the sums
      have hswap : ∑ y ∈ Fintype.piFinset (fun _ : ι => Y),
          ∑ w ∈ Dfin, ∑ A ∈ S.powerset,
            (if A.Nonempty ∧ (S \ A).Nonempty then
              P u w * treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) else 0) =
          ∑ w ∈ Dfin, ∑ A ∈ S.powerset,
            (if A.Nonempty ∧ (S \ A).Nonempty then
              P u w * ∑ y ∈ Fintype.piFinset (fun _ : ι => Y),
                treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun A _ => ?_)
        split_ifs
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => by ring)
        · exact Finset.sum_const_zero
      rw [hswap]
      -- bound each term and count the subsets
      have hterm : ∀ w ∈ Dfin, ∑ A ∈ S.powerset,
            (if A.Nonempty ∧ (S \ A).Nonempty then
              P u w * ∑ y ∈ Fintype.piFinset (fun _ : ι => Y),
                treeBound P Dfin y n w A * treeBound P Dfin y n w (S \ A) else 0) ≤
          P u w * ((Y.card : ℝ) ^ (Fintype.card ι - S.card) * ∑ A ∈ S.powerset,
            (if 1 ≤ A.card ∧ A.card < S.card then
              gN m B n A.card * gN m B n (S.card - A.card) else 0)) := by
        intro w _
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum (fun A hA => ?_)
        have hAS := Finset.mem_powerset.mp hA
        by_cases hc : A.Nonempty ∧ (S \ A).Nonempty
        · have hcard : 1 ≤ A.card ∧ A.card < S.card := by
            refine ⟨hc.1.card_pos, ?_⟩
            have h := hc.2.card_pos
            rw [Finset.card_sdiff_of_subset hAS] at h
            omega
          rw [if_pos hc, if_pos hcard]
          have := mul_le_mul_of_nonneg_left (hpair w A hAS hc.1 hc.2) (hP u w)
          linarith
        · rw [if_neg hc]
          refine mul_nonneg (hP u w) (mul_nonneg (pow_nonneg hc0.le _) ?_)
          split_ifs
          · exact mul_nonneg (gN_nonneg hm0 hB0 _ _) (gN_nonneg hm0 hB0 _ _)
          · exact le_rfl
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hcount : ∑ A ∈ S.powerset,
            (if 1 ≤ A.card ∧ A.card < S.card then
              gN m B n A.card * gN m B n (S.card - A.card) else 0) =
          ∑ j ∈ Finset.Ico 1 S.card,
            (S.card.choose j : ℝ) * gN m B n j * gN m B n (S.card - j) := by
        rw [Finset.sum_powerset_apply_card
          (fun j => if 1 ≤ j ∧ j < S.card then gN m B n j * gN m B n (S.card - j) else 0)]
        have hsub : Finset.Ico 1 S.card ⊆ Finset.range (S.card + 1) := by
          intro j hj
          rw [Finset.mem_Ico] at hj
          exact Finset.mem_range.mpr (by omega)
        rw [← Finset.sum_subset hsub (fun j _ hj => by
          rw [Finset.mem_Ico] at hj
          rw [if_neg hj, smul_zero])]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_Ico] at hj
        rw [if_pos hj, nsmul_eq_mul]
        ring
      rw [hcount]
      have hsum_nonneg : 0 ≤ (Y.card : ℝ) ^ (Fintype.card ι - S.card) * ∑ j ∈ Finset.Ico 1 S.card,
          (S.card.choose j : ℝ) * gN m B n j * gN m B n (S.card - j) :=
        mul_nonneg (pow_nonneg hc0.le _) (Finset.sum_nonneg (fun j _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (gN_nonneg hm0 hB0 _ _))
            (gN_nonneg hm0 hB0 _ _)))
      calc _ ≤ B * ((Y.card : ℝ) ^ (Fintype.card ι - S.card) * ∑ j ∈ Finset.Ico 1 S.card,
            (S.card.choose j : ℝ) * gN m B n j * gN m B n (S.card - j)) :=
          mul_le_mul_of_nonneg_right (hB u) hsum_nonneg
        _ = _ := by ring

/-- **Summed `N`-point bound.** -/
theorem sum_connections_le {ι : Type*} [Fintype ι] [Nonempty ι] (p : unitInterval) (Dfin Y : Finset (Vertex d))
    (hY : 0 < Y.card) {m B : ℝ} (hm0 : 0 ≤ m) (hB0 : 0 ≤ B)
    (hm : ∀ u, ∑ v ∈ Y, (percolation d p).real
      (connectionToSetEvent (Dfin : Set (Vertex d)) u {v}) ≤ m)
    (hB : ∀ u, ∑ w ∈ Dfin, (percolation d p).real
      (connectionToSetEvent (Dfin : Set (Vertex d)) u {w}) ≤ B)
    {u : Vertex d} (hu : u ∈ Dfin) :
    ∑ y ∈ Fintype.piFinset (fun _ : ι => Y), (percolation d p).real {ω | ∀ i : ι,
        (restrictedGraph ω (Dfin : Set (Vertex d))).Reachable u (y i)} ≤
      gN m B (Fintype.card ι) (Fintype.card ι) := by
  have hne : (Finset.univ : Finset (ι)).Nonempty := Finset.univ_nonempty
  have h1 : ∀ y : ι → Vertex d, (percolation d p).real {ω | ∀ i : ι,
        (restrictedGraph ω (Dfin : Set (Vertex d))).Reachable u (y i)} ≤
      treeBound (fun a b => (percolation d p).real
        (connectionToSetEvent (Dfin : Set (Vertex d)) a {b})) Dfin y (Fintype.card ι) u Finset.univ := by
    intro y
    have h := connections_probability_le_treeBound p Dfin y hu hne
    simpa using h
  refine (Finset.sum_le_sum (fun y _ => h1 y)).trans ?_
  have h2 := sum_treeBound_le (ι := ι) (fun a b => (percolation d p).real
    (connectionToSetEvent (Dfin : Set (Vertex d)) a {b})) (fun _ _ => measureReal_nonneg)
    Dfin Y hY hm0 hB0 hm hB (Fintype.card ι) u Finset.univ
  simpa using h2

end NearCritical.SplitCrossDirect
end
