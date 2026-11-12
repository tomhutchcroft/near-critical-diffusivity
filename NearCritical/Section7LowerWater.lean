module

public import NearCritical.Section10FiniteLower
public import NearCritical.Section10IssuedPathSupport
public import NearCritical.Section10ConductivityMonotone
public import NearCritical.NestRegularBoundary
public import NearCritical.PreGoodUpperCount

/-! Source Section 7, `prop.lower_water` (main.tex 2712): the lower bound for the
RELAXED annealed conductivity of the paper's odd cube within the correlation
length, `a(Lambda_n, p_c) >~ n^(-6)`, and `a(Lambda_n, p) >~ (p - p_c)^3` for
`n <= l_*(p)`.

Everything is proved for the actual product law, the actual issued network of
`centeredBox d r` (bottom face / extra top layer), and actual components of the
cube. The only retained input is the conclusion of source `lem.spanning.diam`
(`SpanningDiamStatement`), plus `0 < p_c`.

Proof-route notes (recorded in the divergence report):
* the source's Chernoff step for the open exit edges is replaced by a
  first-moment (Markov) bound, giving `P[A'] >= (p_c/2) P[A]`;
* only the LOWER count `c_1 n^(d-6) <= |S|` and the diameter bound are used; the
  energy is bounded by `(D+1)/|S'|`, so the upper count and volume window of
  `lem.spanning.diam` are not needed;
* the result holds for `n >= N_0` (the range in which the source proves it).

 -/
@[expose] public section
noncomputable section
namespace NearCritical.Section7
open MeasureTheory
open scoped Classical BigOperators

/-! ### A. First-moment thinning for finite Bernoulli products -/

section Thinning
variable {E : Type*} [Fintype E]

lemma sum_indicator_const (T : Finset E) (c : ℝ) :
    (∑ e, if e ∈ T then c else 0) = (T.card : ℝ) * c := by
  have h1 : (∑ e ∈ T, (if e ∈ T then c else 0)) = ∑ e, (if e ∈ T then c else 0) :=
    Finset.sum_subset (Finset.subset_univ T) (fun e _ he => if_neg he)
  have h2 : (∑ e ∈ T, (if e ∈ T then c else 0)) = ∑ _e ∈ T, c :=
    Finset.sum_congr rfl (fun e he => if_pos he)
  rw [← h1, h2, Finset.sum_const, nsmul_eq_mul]

/-- A function insensitive to coordinate `e` is independent of that coordinate:
the closed-`e` part of its weighted sum is the fraction `1-p`. -/
lemma sum_weight_closed_of_flip_invariant (p : ℝ) (e : E) (g : (E → Bool) → ℝ)
    (hg : ∀ η, g (BernoulliCalculus.flip e η) = g η) :
    (∑ η, BernoulliCalculus.weight p η * (g η * (if η e then (0:ℝ) else 1))) =
      (1-p) * ∑ η, BernoulliCalculus.weight p η * g η := by
  have hD : ∀ η, BernoulliCalculus.deletedWeight p e (BernoulliCalculus.flip e η) *
      g (BernoulliCalculus.flip e η) = BernoulliCalculus.deletedWeight p e η * g η := by
    intro η
    rw [BernoulliCalculus.deletedWeight_flip, hg]
  have hswap : (∑ η, if η e then BernoulliCalculus.deletedWeight p e η * g η else 0) =
      ∑ η, if η e then 0 else BernoulliCalculus.deletedWeight p e η * g η := by
    have h := BernoulliCalculus.sum_flip e
      (fun η => if η e then 0 else BernoulliCalculus.deletedWeight p e η * g η)
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro η _
    rw [BernoulliCalculus.flip_apply_self, hD]
    by_cases hη : η e = true
    · have hn : ¬ ((!η e) = true) := by simp [hη]
      rw [if_pos hη, if_neg hn]
    · have hn : (!η e) = true := by simpa using hη
      rw [if_neg hη, if_pos hn]
  have hL : ∀ η, BernoulliCalculus.weight p η * (g η * (if η e then (0:ℝ) else 1)) =
      (1-p) * (if η e then 0 else BernoulliCalculus.deletedWeight p e η * g η) := by
    intro η
    rw [BernoulliCalculus.weight_split p e η]
    by_cases hη : η e = true
    · simp only [if_pos hη]
      ring
    · simp only [if_neg hη]
      ring
  have hR : ∀ η, BernoulliCalculus.weight p η * g η =
      p * (if η e then BernoulliCalculus.deletedWeight p e η * g η else 0) +
      (1-p) * (if η e then 0 else BernoulliCalculus.deletedWeight p e η * g η) := by
    intro η
    rw [BernoulliCalculus.weight_split p e η]
    by_cases hη : η e = true
    · simp only [if_pos hη]
      ring
    · simp only [if_neg hη]
      ring
  have h1 : (∑ η, BernoulliCalculus.weight p η * (g η * (if η e then (0:ℝ) else 1))) =
      ∑ η, (1-p) * (if η e then 0 else BernoulliCalculus.deletedWeight p e η * g η) :=
    Finset.sum_congr rfl (fun η _ => hL η)
  have h2 : (∑ η, BernoulliCalculus.weight p η * g η) =
      ∑ η, (p * (if η e then BernoulliCalculus.deletedWeight p e η * g η else 0) +
        (1-p) * (if η e then 0 else BernoulliCalculus.deletedWeight p e η * g η)) :=
    Finset.sum_congr rfl (fun η _ => hR η)
  have hLs : (∑ η, BernoulliCalculus.weight p η * (g η * (if η e then (0:ℝ) else 1))) =
      (1-p) * ∑ η, (if η e then 0 else BernoulliCalculus.deletedWeight p e η * g η) := by
    rw [h1, Finset.mul_sum]
  have hRs : (∑ η, BernoulliCalculus.weight p η * g η) =
      p * (∑ η, if η e then BernoulliCalculus.deletedWeight p e η * g η else 0) +
      (1-p) * ∑ η, (if η e then 0 else BernoulliCalculus.deletedWeight p e η * g η) := by
    rw [h2, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hLs, hRs, hswap]
  ring

/-- First-moment thinning. `J η` is a family of coordinates selected by the
configuration, and both `J` and the event `A` are insensitive to the selected
coordinates. Then, on a `p/2` fraction of `A`, at least a `p/2` proportion of
the selected coordinates is open. -/
theorem thinning_half_open (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A A' : Set (E → Bool)) (J : (E → Bool) → Finset E)
    (hJ : ∀ η e, e ∈ J η → J (BernoulliCalculus.flip e η) = J η)
    (hA : ∀ η e, e ∈ J η → (BernoulliCalculus.flip e η ∈ A ↔ η ∈ A))
    (hA' : ∀ η, η ∈ A' ↔ (η ∈ A ∧ p * ((J η).card:ℝ) ≤
      2 * (((J η).filter (fun e => η e = true)).card:ℝ))) :
    (p/2) * (∑ η, if η ∈ A then BernoulliCalculus.weight p η else 0) ≤
      ∑ η, if η ∈ A' then BernoulliCalculus.weight p η else 0 := by
  have hw0 : ∀ η : E → Bool, 0 ≤ BernoulliCalculus.weight p η := by
    intro η
    unfold BernoulliCalculus.weight
    apply Finset.prod_nonneg
    intro e _
    by_cases h : η e = true
    · rw [if_pos h]
      exact hp0
    · rw [if_neg h]
      linarith
  let g : E → (E → Bool) → ℝ := fun e η =>
    if η ∈ A ∧ e ∈ J η then 1/((J η).card:ℝ) else 0
  have hg0 : ∀ e η, 0 ≤ g e η := by
    intro e η
    dsimp only [g]
    by_cases h : η ∈ A ∧ e ∈ J η
    · simp only [if_pos h]
      positivity
    · simp only [if_neg h, le_refl]
  have hJ' : ∀ η e, e ∈ J (BernoulliCalculus.flip e η) → e ∈ J η := by
    intro η e h
    have h2 := hJ (BernoulliCalculus.flip e η) e h
    rw [BernoulliCalculus.flip_involutive e η] at h2
    rw [h2]
    exact h
  have hg : ∀ e η, g e (BernoulliCalculus.flip e η) = g e η := by
    intro e η
    dsimp only [g]
    by_cases he : e ∈ J η
    · rw [hJ η e he]
      by_cases hη : η ∈ A
      · have h1 : BernoulliCalculus.flip e η ∈ A ∧ e ∈ J η := ⟨(hA η e he).mpr hη, he⟩
        have h2 : η ∈ A ∧ e ∈ J η := ⟨hη, he⟩
        rw [if_pos h1, if_pos h2]
      · have h1 : ¬ (BernoulliCalculus.flip e η ∈ A ∧ e ∈ J η) :=
          fun h => hη ((hA η e he).mp h.1)
        have h2 : ¬ (η ∈ A ∧ e ∈ J η) := fun h => hη h.1
        rw [if_neg h1, if_neg h2]
    · have h1 : ¬ (BernoulliCalculus.flip e η ∈ A ∧
          e ∈ J (BernoulliCalculus.flip e η)) := fun h => he (hJ' η e h.2)
      have h2 : ¬ (η ∈ A ∧ e ∈ J η) := fun h => he h.2
      rw [if_neg h1, if_neg h2]
  have hsplit : ∀ η : E → Bool,
      (((J η).filter (fun e => η e = true)).card:ℝ) +
        (((J η).filter (fun e => ¬ η e = true)).card:ℝ) = ((J η).card:ℝ) := by
    intro η
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := J η) (fun e => η e = true)
  have hclosed : ∀ η : E → Bool, η ∈ A →
      (∑ e, g e η * (if η e then (0:ℝ) else 1)) =
        (((J η).filter (fun e => ¬ η e = true)).card:ℝ) * (1/((J η).card:ℝ)) := by
    intro η hη
    have hterm : ∀ e, g e η * (if η e then (0:ℝ) else 1) =
        if e ∈ (J η).filter (fun e => ¬ η e = true) then 1/((J η).card:ℝ) else 0 := by
      intro e
      dsimp only [g]
      by_cases he : e ∈ J η
      · by_cases h : η e = true
        · have hn : e ∉ (J η).filter (fun e => ¬ η e = true) :=
            fun hm => (Finset.mem_filter.mp hm).2 h
          rw [if_pos h, if_neg hn, mul_zero]
        · have hm : e ∈ (J η).filter (fun e => ¬ η e = true) :=
            Finset.mem_filter.mpr ⟨he, h⟩
          have hAJ : η ∈ A ∧ e ∈ J η := ⟨hη, he⟩
          rw [if_neg h, if_pos hm, if_pos hAJ, mul_one]
      · have hn : e ∉ (J η).filter (fun e => ¬ η e = true) :=
          fun hm => he (Finset.mem_filter.mp hm).1
        have hAJ : ¬ (η ∈ A ∧ e ∈ J η) := fun h => he h.2
        rw [if_neg hn, if_neg hAJ, zero_mul]
    have hsum : (∑ e, g e η * (if η e then (0:ℝ) else 1)) =
        ∑ e, if e ∈ (J η).filter (fun e => ¬ η e = true) then 1/((J η).card:ℝ) else 0 :=
      Finset.sum_congr rfl (fun e _ => hterm e)
    rw [hsum, sum_indicator_const]
  have htotal : ∀ η : E → Bool, (∑ e, g e η) ≤ if η ∈ A then (1:ℝ) else 0 := by
    intro η
    by_cases hη : η ∈ A
    · have hterm : ∀ e, g e η = if e ∈ J η then 1/((J η).card:ℝ) else 0 := by
        intro e
        dsimp only [g]
        by_cases he : e ∈ J η
        · have hAJ : η ∈ A ∧ e ∈ J η := ⟨hη, he⟩
          rw [if_pos hAJ, if_pos he]
        · have hAJ : ¬ (η ∈ A ∧ e ∈ J η) := fun h => he h.2
          rw [if_neg hAJ, if_neg he]
      have hsum : (∑ e, g e η) = ∑ e, if e ∈ J η then 1/((J η).card:ℝ) else 0 :=
        Finset.sum_congr rfl (fun e _ => hterm e)
      rw [if_pos hη, hsum, sum_indicator_const]
      by_cases hN : (J η).card = 0
      · simp [hN]
      · have hNpos : (0:ℝ) < ((J η).card:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
        exact (mul_one_div_cancel hNpos.ne').le
    · have hterm : ∀ e, g e η = 0 := by
        intro e
        dsimp only [g]
        have hAJ : ¬ (η ∈ A ∧ e ∈ J η) := fun h => hη h.1
        rw [if_neg hAJ]
      have hsum : (∑ e, g e η) = ∑ _e : E, (0:ℝ) :=
        Finset.sum_congr rfl (fun e _ => hterm e)
      simp only [if_neg hη, hsum, Finset.sum_const_zero, le_refl]
  have hbad : ∀ η : E → Bool, η ∈ A →
      ¬ (p * ((J η).card:ℝ) ≤ 2 * (((J η).filter (fun e => η e = true)).card:ℝ)) →
      1 - p/2 ≤ ∑ e, g e η * (if η e then (0:ℝ) else 1) := by
    intro η hη hb
    rw [hclosed η hη]
    have hs := hsplit η
    have hNpos : (0:ℝ) < ((J η).card:ℝ) := by
      by_contra hN
      have hN0 : ((J η).card:ℝ) = 0 := le_antisymm (not_lt.mp hN) (Nat.cast_nonneg _)
      apply hb
      rw [hN0, mul_zero]
      positivity
    have hb' := not_le.mp hb
    rw [mul_one_div, le_div_iff₀ hNpos]
    nlinarith
  have hsplitsum : (∑ η, if η ∈ A then BernoulliCalculus.weight p η else 0) =
      (∑ η, if η ∈ A' then BernoulliCalculus.weight p η else 0) +
      ∑ η, if η ∈ A ∧ η ∉ A' then BernoulliCalculus.weight p η else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro η _
    by_cases h1 : η ∈ A
    · by_cases h2 : η ∈ A'
      · have h12 : ¬ (η ∈ A ∧ η ∉ A') := fun h => h.2 h2
        simp only [if_pos h1, if_pos h2, if_neg h12, add_zero]
      · have h12 : η ∈ A ∧ η ∉ A' := ⟨h1, h2⟩
        simp only [if_pos h1, if_neg h2, if_pos h12, zero_add]
    · have h2 : η ∉ A' := fun h => h1 ((hA' η).mp h).1
      have h12 : ¬ (η ∈ A ∧ η ∉ A') := fun h => h1 h.1
      simp only [if_neg h1, if_neg h2, if_neg h12, add_zero]
  have hstep1 : (1 - p/2) *
      (∑ η, if η ∈ A ∧ η ∉ A' then BernoulliCalculus.weight p η else 0) ≤
      ∑ η, BernoulliCalculus.weight p η * ∑ e, g e η * (if η e then (0:ℝ) else 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro η _
    by_cases h : η ∈ A ∧ η ∉ A'
    · rw [if_pos h]
      have hb := hbad η h.1 (fun hc => h.2 ((hA' η).mpr ⟨h.1, hc⟩))
      calc (1 - p/2) * BernoulliCalculus.weight p η
          = BernoulliCalculus.weight p η * (1 - p/2) := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hb (hw0 η)
    · rw [if_neg h, mul_zero]
      apply mul_nonneg (hw0 η)
      apply Finset.sum_nonneg
      intro e _
      exact mul_nonneg (hg0 e η) (by split_ifs <;> norm_num)
  have hstep2 :
      (∑ η, BernoulliCalculus.weight p η * ∑ e, g e η * (if η e then (0:ℝ) else 1)) =
      (1-p) * ∑ η, BernoulliCalculus.weight p η * ∑ e, g e η := by
    calc (∑ η, BernoulliCalculus.weight p η * ∑ e, g e η * (if η e then (0:ℝ) else 1))
        = ∑ η, ∑ e, BernoulliCalculus.weight p η * (g e η * (if η e then (0:ℝ) else 1)) :=
          Finset.sum_congr rfl (fun η _ => Finset.mul_sum _ _ _)
      _ = ∑ e, ∑ η, BernoulliCalculus.weight p η * (g e η * (if η e then (0:ℝ) else 1)) :=
          Finset.sum_comm
      _ = ∑ e, (1-p) * ∑ η, BernoulliCalculus.weight p η * g e η :=
          Finset.sum_congr rfl
            (fun e _ => sum_weight_closed_of_flip_invariant p e (g e) (hg e))
      _ = (1-p) * ∑ e, ∑ η, BernoulliCalculus.weight p η * g e η :=
          (Finset.mul_sum _ _ _).symm
      _ = (1-p) * ∑ η, ∑ e, BernoulliCalculus.weight p η * g e η := by
          rw [Finset.sum_comm]
      _ = (1-p) * ∑ η, BernoulliCalculus.weight p η * ∑ e, g e η := by
          congr 1
          exact Finset.sum_congr rfl (fun η _ => (Finset.mul_sum _ _ _).symm)
  have hstep3 : (∑ η, BernoulliCalculus.weight p η * ∑ e, g e η) ≤
      ∑ η, if η ∈ A then BernoulliCalculus.weight p η else 0 := by
    apply Finset.sum_le_sum
    intro η _
    have ht := htotal η
    by_cases h : η ∈ A
    · rw [if_pos h] at ht
      rw [if_pos h]
      calc BernoulliCalculus.weight p η * ∑ e, g e η
          ≤ BernoulliCalculus.weight p η * 1 := mul_le_mul_of_nonneg_left ht (hw0 η)
        _ = BernoulliCalculus.weight p η := mul_one _
    · rw [if_neg h] at ht
      rw [if_neg h]
      have hs0 : (∑ e, g e η) = 0 :=
        le_antisymm ht (Finset.sum_nonneg (fun e _ => hg0 e η))
      simp only [hs0, mul_zero, le_refl]
  have hbadsum : (1 - p/2) *
      (∑ η, if η ∈ A ∧ η ∉ A' then BernoulliCalculus.weight p η else 0) ≤
      (1-p) * ∑ η, if η ∈ A then BernoulliCalculus.weight p η else 0 := by
    refine hstep1.trans ?_
    rw [hstep2]
    exact mul_le_mul_of_nonneg_left hstep3 (sub_nonneg.mpr hp1)
  have hPA'0 : 0 ≤ ∑ η, if η ∈ A' then BernoulliCalculus.weight p η else 0 := by
    apply Finset.sum_nonneg
    intro η _
    by_cases h : η ∈ A'
    · simp only [if_pos h, hw0 η]
    · simp only [if_neg h, le_refl]
  rw [hsplitsum] at hbadsum ⊢
  linarith [mul_nonneg hp0 hPA'0, hbadsum]

end Thinning

/-- Averaging unit path currents with pairwise disjoint supports of size at
most `B` gives energy at most `B` divided by the number of paths. -/
theorem average_disjoint_currents_energy {E I : Type*} [Fintype E] [Fintype I]
    (a : E → ℝ) (θ : I → E → ℝ) (P : I → Finset E) (B : ℝ)
    (hI : (0:ℝ) < (Fintype.card I : ℝ))
    (hθ : ∀ i e, |θ i e| ≤ if e ∈ P i then (1:ℝ) else 0)
    (hopen : ∀ i e, e ∈ P i → a e = 1)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcard : ∀ i, ((P i).card:ℝ) ≤ B) :
    Network.flowEnergy a (Network.weightedFlow (fun _ : I => 1/(Fintype.card I:ℝ)) θ) ≤
      B/(Fintype.card I:ℝ) := by
  have hc0 : (Fintype.card I : ℝ) ≠ 0 := hI.ne'
  have hα0 : ∀ _i : I, (0:ℝ) ≤ 1/(Fintype.card I:ℝ) := fun _ => by positivity
  have hE := Network.weighted_path_flow_energy_le_overlaps a
    (fun _ : I => 1/(Fintype.card I:ℝ)) θ P hα0 hθ hopen
  refine hE.trans ?_
  have hinner : ∀ i : I,
      (∑ j : I, 1/(Fintype.card I:ℝ)*(1/(Fintype.card I:ℝ))*((P i ∩ P j).card:ℝ)) ≤
        1/(Fintype.card I:ℝ)*(1/(Fintype.card I:ℝ))*B := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [Finset.inter_self]
      exact mul_le_mul_of_nonneg_left (hcard i) (by positivity)
    · intro j _ hji
      rw [Finset.disjoint_iff_inter_eq_empty.mp (hdisj i j (Ne.symm hji)),
        Finset.card_empty, Nat.cast_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  calc (∑ i : I, ∑ j : I,
        1/(Fintype.card I:ℝ)*(1/(Fintype.card I:ℝ))*((P i ∩ P j).card:ℝ))
      ≤ ∑ _i : I, 1/(Fintype.card I:ℝ)*(1/(Fintype.card I:ℝ))*B :=
        Finset.sum_le_sum (fun i _ => hinner i)
    _ = (Fintype.card I:ℝ)*(1/(Fintype.card I:ℝ)*(1/(Fintype.card I:ℝ))*B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((Fintype.card I:ℝ)*(1/(Fintype.card I:ℝ)))*((1/(Fintype.card I:ℝ))*B) := by ring
    _ = B/(Fintype.card I:ℝ) := by
        rw [mul_one_div_cancel hc0]
        ring

/-! ### B. Short crossings of the actual cube components -/

/-- A walk of the cube-restricted graph, read in the induced open graph. Its
length is unchanged and all its vertices are reachable from the start. -/
theorem exists_induce_walk {d : ℕ} (ω : Configuration d) (S : Set (Vertex d)) :
    ∀ {x y : Vertex d} (w : (restrictedGraph ω S).Walk x y) (hx : x ∈ S) (hy : y ∈ S),
      ∃ v : ((openGraph ω).induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩, v.length = w.length ∧
        ∀ z ∈ v.support, (restrictedGraph ω S).Reachable x z.val := by
  intro x y w
  induction w with
  | nil =>
    intro hx hy
    refine ⟨SimpleGraph.Walk.nil, rfl, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz
    exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj w ih =>
    intro hx hy
    obtain ⟨v, hv, hsupp⟩ := ih hadj.2.2 hy
    have hadj' : ((openGraph ω).induce S).Adj ⟨a, hx⟩ ⟨b, hadj.2.2⟩ := hadj.1
    refine ⟨SimpleGraph.Walk.cons hadj' v, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons, hv]
    · intro z hz
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with hz | hz
      · subst hz
        exact SimpleGraph.Reachable.refl _
      · exact hadj.reachable.trans (hsupp z hz)

/-- A component containing a bottom-face point and a top-face point (in
direction `i`) at graph distance at most `D`. -/
def IsShortCrossing {d : ℕ} (G : SimpleGraph (Vertex d)) (r : ℕ) (i : Fin d) (D : ℝ)
    (C : Finset (Vertex d)) : Prop :=
  ∃ x, x ∈ C ∧ ∃ y, y ∈ C ∧ x i = -(r:ℤ) ∧ y i = (r:ℤ) ∧ (G.dist x y : ℝ) ≤ D

def crossingBottom {d : ℕ} (G : SimpleGraph (Vertex d)) (r : ℕ) (i : Fin d) (D : ℝ)
    (C : Finset (Vertex d)) : Vertex d :=
  if h : IsShortCrossing G r i D C then h.choose else 0

def crossingTop {d : ℕ} (G : SimpleGraph (Vertex d)) (r : ℕ) (i : Fin d) (D : ℝ)
    (C : Finset (Vertex d)) : Vertex d :=
  if h : IsShortCrossing G r i D C then h.choose_spec.2.choose else 0

lemma crossing_spec {d : ℕ} {G : SimpleGraph (Vertex d)} {r : ℕ} {i : Fin d} {D : ℝ}
    {C : Finset (Vertex d)} (h : IsShortCrossing G r i D C) :
    crossingBottom G r i D C ∈ C ∧ crossingTop G r i D C ∈ C ∧
      crossingBottom G r i D C i = -(r:ℤ) ∧ crossingTop G r i D C i = (r:ℤ) ∧
      (G.dist (crossingBottom G r i D C) (crossingTop G r i D C) : ℝ) ≤ D := by
  have hb : crossingBottom G r i D C = h.choose := dif_pos h
  have ht : crossingTop G r i D C = h.choose_spec.2.choose := dif_pos h
  rw [hb, ht]
  exact ⟨h.choose_spec.1, h.choose_spec.2.choose_spec.1, h.choose_spec.2.choose_spec.2.1,
    h.choose_spec.2.choose_spec.2.2.1, h.choose_spec.2.choose_spec.2.2.2⟩

/-- Actual components of the odd cube that cross it in direction `i` within
graph distance `D`. -/
def crossingFamily {d : ℕ} (ω : Configuration d) (r : ℕ) (i : Fin d) (D : ℝ) :
    Finset (Finset (Vertex d)) :=
  (finiteClusterFamily ω (centeredBox d r)).filter
    (IsShortCrossing (restrictedGraph ω (centeredBox d r : Set (Vertex d))) r i D)

lemma mem_crossingFamily {d : ℕ} (ω : Configuration d) (r : ℕ) (i : Fin d) (D : ℝ)
    (C : Finset (Vertex d)) : C ∈ crossingFamily ω r i D ↔
      C ∈ finiteClusterFamily ω (centeredBox d r) ∧
        IsShortCrossing (restrictedGraph ω (centeredBox d r : Set (Vertex d))) r i D C := by
  simp only [crossingFamily, Finset.mem_filter]

/-- The chosen top-face point of a crossing component. -/
def exitPoint {d : ℕ} (ω : Configuration d) (r : ℕ) (i : Fin d) (D : ℝ)
    (C : Finset (Vertex d)) : Vertex d :=
  crossingTop (restrictedGraph ω (centeredBox d r : Set (Vertex d))) r i D C

theorem crossingFamily_eq_of_internal_agree {d : ℕ} (r : ℕ) (i : Fin d) (D : ℝ)
    (ω ω' : Configuration d)
    (hagree : ∀ e ∈ internalBondSet (centeredBox d r), ω e = ω' e) :
    crossingFamily ω r i D = crossingFamily ω' r i D ∧
      exitPoint ω r i D = exitPoint ω' r i D := by
  have hG := restrictedGraph_eq_of_internalBondSet_agree (centeredBox d r)
    (centeredBox d r : Set (Vertex d)) (fun x hx => hx) ω ω' hagree
  have hfun : finiteBoxCluster ω (centeredBox d r) = finiteBoxCluster ω' (centeredBox d r) := by
    funext root
    exact finiteBoxCluster_eq_of_internal_agree (centeredBox d r) (centeredBox d r)
      (fun x hx => hx) ω ω' hagree root
  constructor
  · simp only [crossingFamily, finiteClusterFamily, hfun, hG]
  · funext C
    simp only [exitPoint, hG]

lemma exitPoint_spec {d : ℕ} {ω : Configuration d} {r : ℕ} {i : Fin d} {D : ℝ}
    {C : Finset (Vertex d)} (hC : C ∈ crossingFamily ω r i D) :
    exitPoint ω r i D C ∈ C ∧ exitPoint ω r i D C i = (r:ℤ) ∧
      exitPoint ω r i D C ∈ centeredBox d r := by
  obtain ⟨hfam, hcross⟩ := (mem_crossingFamily ω r i D C).mp hC
  obtain ⟨_, hyC, _, hyi, _⟩ := crossing_spec hcross
  exact ⟨hyC, hyi, finiteClusterFamily_component_subset ω (centeredBox d r) hfam hyC⟩

/-! ### C. Faces of the issued network of the odd cube -/

lemma centeredBox_nonempty (d r : ℕ) : (centeredBox d r).Nonempty := by
  refine ⟨0, mem_centeredBox.mpr ?_⟩
  intro j
  change -(r:ℤ) ≤ 0 ∧ 0 ≤ (r:ℤ)
  omega

lemma faces_disjoint (d r : ℕ) (i : Fin d) :
    Disjoint (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact lt_irrefl _ (face_data_lt (centeredBox_nonempty d r) hx hx')

lemma internal_mem_negativeFace {d r : ℕ} (i : Fin d)
    (x : ↥((centeredBox d r : Finset (Vertex d)) : Set (Vertex d)))
    (hxi : x.val i = -(r:ℤ)) :
    Section10.internalIssuedVertex (centeredBox d r) x ∈ negativeFace (centeredBox d r) i := by
  have hbounds := sitesPlus_coordinate_bounds (centeredBox d r) i
    (fun y hy => (mem_centeredBox.mp hy) i)
  have hmin : ∀ y ∈ sitesPlus (centeredBox d r), x.val i ≤ y i := by
    intro y hy
    rw [hxi]
    exact (hbounds y hy).1
  exact ⟨mem_boundarySites_of_min i (base_mem_sitesPlus x.property) hmin, hmin⟩

lemma exit_mem_positiveFace {d r : ℕ} (i : Fin d)
    (y : ↥((centeredBox d r : Finset (Vertex d)) : Set (Vertex d)))
    (hyi : y.val i = (r:ℤ)) :
    Section10.issuedExitVertex (centeredBox d r) y i ∈ positiveFace (centeredBox d r) i := by
  have hbounds := sitesPlus_coordinate_bounds (centeredBox d r) i
    (fun z hz => (mem_centeredBox.mp hz) i)
  have htip : bondTip (y.val, i) i = (r:ℤ) + 1 := by
    simp only [bondTip, Function.update_self]
    omega
  have hmax : ∀ z ∈ sitesPlus (centeredBox d r), z i ≤ bondTip (y.val, i) i := by
    intro z hz
    rw [htip]
    exact (hbounds z hz).2
  exact ⟨mem_boundarySites_of_max i (tip_mem_sitesPlus y.property i) hmax, hmax⟩

/-! ### D. The unit path current of one crossing component -/

/-- Source flow `theta_gamma(C)`: a crossing component whose exit edge is open
carries a unit current from the bottom face to the extra top layer, supported
on at most `D+1` open issued bonds, all based in that component. -/
theorem cluster_exit_current {d r : ℕ} (i : Fin d) (ω : Configuration d) (D : ℝ)
    (C : Finset (Vertex d)) (hC : C ∈ crossingFamily ω r i D)
    (hexit : ω (exitPoint ω r i D C, i) = true) :
    ∃ (P : Finset (IssuedBond (centeredBox d r))) (θ : IssuedBond (centeredBox d r) → ℝ),
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) θ ∧
      Network.FlowSupported (domainWeights ω) θ ∧
      (∀ e, |θ e| ≤ if e ∈ P then (1:ℝ) else 0) ∧
      (∀ e ∈ P, (domainWeights ω : IssuedBond (centeredBox d r) → ℝ) e = 1) ∧
      (P.card : ℝ) ≤ D + 1 ∧ (∀ e ∈ P, e.val.1 ∈ C) := by
  obtain ⟨hfam, hcross⟩ := (mem_crossingFamily ω r i D C).mp hC
  obtain ⟨x, y, hxC, hyC, hxi, hyi, hdist, hyeq⟩ : ∃ x y : Vertex d, x ∈ C ∧ y ∈ C ∧
      x i = -(r:ℤ) ∧ y i = (r:ℤ) ∧
      ((restrictedGraph ω (centeredBox d r : Set (Vertex d))).dist x y : ℝ) ≤ D ∧
      y = exitPoint ω r i D C := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := crossing_spec hcross
    exact ⟨_, _, h1, h2, h3, h4, h5, rfl⟩
  rw [← hyeq] at hexit
  have hCU : C ⊆ centeredBox d r :=
    finiteClusterFamily_component_subset ω (centeredBox d r) hfam
  have hxU : x ∈ centeredBox d r := hCU hxC
  have hyU : y ∈ centeredBox d r := hCU hyC
  have hxS : x ∈ (centeredBox d r : Set (Vertex d)) := Finset.mem_coe.mpr hxU
  have hyS : y ∈ (centeredBox d r : Set (Vertex d)) := Finset.mem_coe.mpr hyU
  have hrec : finiteBoxCluster ω (centeredBox d r) x = C :=
    finiteClusterFamily_recover ω (centeredBox d r) hfam hxC
  have hmemC : ∀ z : Vertex d, z ∈ centeredBox d r →
      (restrictedGraph ω (centeredBox d r : Set (Vertex d))).Reachable x z → z ∈ C := by
    intro z hzU hz
    rw [← hrec]
    exact (mem_finiteBoxCluster ω (centeredBox d r) x z).mpr ⟨hzU, hz⟩
  have hreach : (restrictedGraph ω (centeredBox d r : Set (Vertex d))).Reachable x y := by
    have hy' : y ∈ finiteBoxCluster ω (centeredBox d r) x := by
      rw [hrec]
      exact hyC
    exact ((mem_finiteBoxCluster ω (centeredBox d r) x y).mp hy').2
  obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
  obtain ⟨v, hv, hvsupp⟩ :=
    exists_induce_walk ω (centeredBox d r : Set (Vertex d)) w hxS hyS
  obtain ⟨P, θ, hunit, hsupp, hmag, hopen, hcard, _, hsub⟩ :=
    Section10.issued_internal_walk_exit_current_support (centeredBox d r) ω
      (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i)
      (faces_disjoint d r i) ⟨x, hxS⟩ ⟨y, hyS⟩ i
      (internal_mem_negativeFace i ⟨x, hxS⟩ hxi)
      (exit_mem_positiveFace i ⟨y, hyS⟩ hyi) v hexit
  refine ⟨P, θ, hunit, hsupp, ?_, hopen, ?_, ?_⟩
  · intro e
    have h := hmag e
    by_cases hb : e ∈ P
    · rw [if_pos hb] at h ⊢
      exact h
    · rw [if_neg hb] at h ⊢
      exact h
  · have h1 : (P.card : ℝ) ≤ (v.length : ℝ) + 1 := by exact_mod_cast hcard
    rw [hv, hw] at h1
    linarith
  · intro e he
    have heU : e.val.1 ∈ centeredBox d r := (Finset.mem_product.mp e.property).1
    rcases hsub e he with h | h
    · have h1 := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ h
      rw [SimpleGraph.Walk.support_map] at h1
      obtain ⟨z, hz, hzeq⟩ := List.mem_map.mp h1
      have hval : z.val = e.val.1 := congrArg Subtype.val hzeq
      rw [← hval]
      exact hmemC z.val (Finset.mem_coe.mp z.property) (hvsupp z hz)
    · rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · have hval : e.val.1 = y := congrArg Subtype.val h1
        rw [hval]
        exact hyC
      · exfalso
        have hval : e.val.1 = bondTip (y, i) := congrArg Subtype.val h1
        have hb := ((mem_centeredBox.mp heU) i).2
        rw [hval] at hb
        simp only [bondTip, Function.update_self] at hb
        omega

/-! ### E. Thomson bound for the RELAXED conductivity -/

/-- Relaxed (two-face) analogue of `Section10.local_cube_flow_lower`. -/
theorem local_relaxed_flow_lower {d r : ℕ} (i : Fin d)
    (η : IssuedBond (centeredBox d r) → Bool) (θ : IssuedBond (centeredBox d r) → ℝ)
    (hsupport : Network.FlowSupported (Section10.cubeFlowWeights η) θ)
    (hθ : (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
      (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) θ) :
    0 < Network.flowEnergy (Section10.cubeFlowWeights η) θ ∧
      ((2*(r:ℝ)+1)^2/Network.flowEnergy (Section10.cubeFlowWeights η) θ)/
          ((centeredBox d r).card:ℝ) ≤
        localRelaxedConductivity (centeredBox d r) i η := by
  have hsource (x : DomainVertex (centeredBox d r))
      (hx : x ∈ negativeFace (centeredBox d r) i) : coordinateData i x = -(r:ℝ) := by
    have h := rectangularBox_negativeFace_coordinate (fun _ : Fin d => r) i hx
    change (x.val i:ℝ) = -(r:ℝ)
    exact_mod_cast h
  have htarget (x : DomainVertex (centeredBox d r))
      (hx : x ∈ positiveFace (centeredBox d r) i) :
      coordinateData i x = -(r:ℝ)+(2*(r:ℝ)+1) := by
    have h := rectangularBox_positiveFace_coordinate (fun _ : Fin d => r) i hx
    have hr : (x.val i:ℝ) = (r:ℝ)+1 := by exact_mod_cast h
    change (x.val i:ℝ) = _
    linarith
  have hS : negativeFace (centeredBox d r) i ⊆ twoFaceBoundary (centeredBox d r) i := by
    rw [twoFaceBoundary_eq_union]
    exact Set.subset_union_left
  have hT : positiveFace (centeredBox d r) i ⊆ twoFaceBoundary (centeredBox d r) i := by
    rw [twoFaceBoundary_eq_union]
    exact Set.subset_union_right
  have hnn : ∀ e, 0 ≤ Section10.cubeFlowWeights η e := by
    intro e
    dsimp only [Section10.cubeFlowWeights]
    split <;> norm_num
  have hb := (issuedNetwork (centeredBox d r)).conductance_ge_boundary_unit_flow
    (Section10.cubeFlowWeights η) θ hnn hsupport
    (twoFaceBoundary (centeredBox d r) i) (negativeFace (centeredBox d r) i)
    (positiveFace (centeredBox d r) i) (coordinateData i) hS hT hθ (-(r:ℝ)) (2*(r:ℝ)+1)
    (by positivity) hsource htarget
  refine ⟨hb.1, ?_⟩
  exact div_le_div_of_nonneg_right hb.2 (Nat.cast_nonneg _)

/-! ### F. Cube configurations, exit bonds and their locality -/

/-- The full-lattice configuration reading a cube assignment (closed outside). -/
def cubeConfig {d r : ℕ} (η : IssuedBond (centeredBox d r) → Bool) : Configuration d :=
  extendConfiguration (issuedBondSet (centeredBox d r)) (fun _ => false) η

lemma cubeConfig_apply {d r : ℕ} (η : IssuedBond (centeredBox d r) → Bool)
    (e : IssuedBond (centeredBox d r)) : cubeConfig η e.val = η e := by
  simp [cubeConfig, extendConfiguration, e.property]

lemma domainWeights_cubeConfig {d r : ℕ} (η : IssuedBond (centeredBox d r) → Bool) :
    (domainWeights (cubeConfig η) : IssuedBond (centeredBox d r) → ℝ) =
      Section10.cubeFlowWeights η := by
  funext e
  simp only [domainWeights, issuedBond, cubeConfig_apply, Section10.cubeFlowWeights]

/-- Exit bonds `{y_C, y_C + e_i}` of the crossing components, as issued bonds. -/
def exitBonds {d : ℕ} (r : ℕ) (i : Fin d) (D : ℝ)
    (η : IssuedBond (centeredBox d r) → Bool) : Finset (IssuedBond (centeredBox d r)) :=
  Finset.univ.filter (fun e => ∃ C ∈ crossingFamily (cubeConfig η) r i D,
    e.val = (exitPoint (cubeConfig η) r i D C, i))

lemma mem_exitBonds {d : ℕ} (r : ℕ) (i : Fin d) (D : ℝ)
    (η : IssuedBond (centeredBox d r) → Bool) (e : IssuedBond (centeredBox d r)) :
    e ∈ exitBonds r i D η ↔ ∃ C ∈ crossingFamily (cubeConfig η) r i D,
      e.val = (exitPoint (cubeConfig η) r i D C, i) := by
  simp only [exitBonds, Finset.mem_filter, Finset.mem_univ, true_and]

lemma exitBond_tip_notMem {d : ℕ} (r : ℕ) (i : Fin d) (D : ℝ)
    (η : IssuedBond (centeredBox d r) → Bool) (e : IssuedBond (centeredBox d r))
    (he : e ∈ exitBonds r i D η) : bondTip e.val ∉ centeredBox d r := by
  obtain ⟨C, hC, hval⟩ := (mem_exitBonds r i D η e).mp he
  have hyi := (exitPoint_spec hC).2.1
  intro hmem
  have hb := ((mem_centeredBox.mp hmem) i).2
  rw [hval] at hb
  simp only [bondTip, Function.update_self] at hb
  omega

lemma internal_agree_flip {d : ℕ} (r : ℕ) (i : Fin d) (D : ℝ)
    (η : IssuedBond (centeredBox d r) → Bool) (e : IssuedBond (centeredBox d r))
    (he : e ∈ exitBonds r i D η) :
    ∀ b ∈ internalBondSet (centeredBox d r),
      cubeConfig (BernoulliCalculus.flip e η) b = cubeConfig η b := by
  intro b hb
  obtain ⟨hb1, hb2⟩ := (mem_internalBondSet (centeredBox d r) b).mp hb
  have hbI : b ∈ issuedBondSet (centeredBox d r) :=
    Finset.mem_product.mpr ⟨hb1, Finset.mem_univ _⟩
  have h1 : cubeConfig (BernoulliCalculus.flip e η) b =
      BernoulliCalculus.flip e η ⟨b, hbI⟩ := cubeConfig_apply _ ⟨b, hbI⟩
  have h2 : cubeConfig η b = η ⟨b, hbI⟩ := cubeConfig_apply η ⟨b, hbI⟩
  have hne : (⟨b, hbI⟩ : IssuedBond (centeredBox d r)) ≠ e := by
    intro h
    apply exitBond_tip_notMem r i D η e he
    rw [← h]
    exact hb2
  rw [h1, h2]
  unfold BernoulliCalculus.flip
  first
    | exact @Function.update_of_ne _ _ _ _ _ hne _ _
    | (unfold Function.update; simp only [dif_neg hne])
    | simp [Function.update, hne]

lemma exitBonds_flip {d : ℕ} (r : ℕ) (i : Fin d) (D : ℝ)
    (η : IssuedBond (centeredBox d r) → Bool) (e : IssuedBond (centeredBox d r))
    (he : e ∈ exitBonds r i D η) :
    exitBonds r i D (BernoulliCalculus.flip e η) = exitBonds r i D η := by
  obtain ⟨h1, h2⟩ := crossingFamily_eq_of_internal_agree r i D
    (cubeConfig (BernoulliCalculus.flip e η)) (cubeConfig η) (internal_agree_flip r i D η e he)
  unfold exitBonds
  rw [h1, h2]

/-- The finite cube event `{m <= #crossing components}`. -/
def countEvent {d : ℕ} (r : ℕ) (i : Fin d) (D m : ℝ) :
    Set (IssuedBond (centeredBox d r) → Bool) :=
  {η | m ≤ ((crossingFamily (cubeConfig η) r i D).card : ℝ)}

/-- The thinned event: the count holds and at least a `p/2` proportion of the
exit bonds is open. -/
def thinnedEvent {d : ℕ} (r : ℕ) (i : Fin d) (D m p : ℝ) :
    Set (IssuedBond (centeredBox d r) → Bool) :=
  {η | η ∈ countEvent r i D m ∧ p * ((exitBonds r i D η).card:ℝ) ≤
    2 * (((exitBonds r i D η).filter (fun e => η e = true)).card:ℝ)}

lemma countEvent_flip {d : ℕ} (r : ℕ) (i : Fin d) (D m : ℝ)
    (η : IssuedBond (centeredBox d r) → Bool) (e : IssuedBond (centeredBox d r))
    (he : e ∈ exitBonds r i D η) :
    BernoulliCalculus.flip e η ∈ countEvent r i D m ↔ η ∈ countEvent r i D m := by
  have h1 := (crossingFamily_eq_of_internal_agree r i D
    (cubeConfig (BernoulliCalculus.flip e η)) (cubeConfig η)
    (internal_agree_flip r i D η e he)).1
  change m ≤ ((crossingFamily (cubeConfig (BernoulliCalculus.flip e η)) r i D).card : ℝ) ↔
    m ≤ ((crossingFamily (cubeConfig η) r i D).card : ℝ)
  rw [h1]

theorem exitBonds_card {d : ℕ} (r : ℕ) (i : Fin d) (D : ℝ)
    (η : IssuedBond (centeredBox d r) → Bool) :
    (exitBonds r i D η).card = (crossingFamily (cubeConfig η) r i D).card := by
  symm
  refine Finset.card_bij
    (fun C hC => (⟨(exitPoint (cubeConfig η) r i D C, i),
      Finset.mem_product.mpr ⟨(exitPoint_spec hC).2.2, Finset.mem_univ _⟩⟩ :
        IssuedBond (centeredBox d r))) ?_ ?_ ?_
  · intro C hC
    exact (mem_exitBonds r i D η _).mpr ⟨C, hC, rfl⟩
  · intro C1 h1 C2 h2 heq
    have htop : exitPoint (cubeConfig η) r i D C1 = exitPoint (cubeConfig η) r i D C2 :=
      congrArg (fun e : IssuedBond (centeredBox d r) => e.val.1) heq
    by_contra hne
    have hdis := finiteClusterFamily_disjoint (cubeConfig η) (centeredBox d r)
      ((mem_crossingFamily _ r i D C1).mp h1).1 ((mem_crossingFamily _ r i D C2).mp h2).1 hne
    have m1 := (exitPoint_spec h1).1
    have m2 := (exitPoint_spec h2).1
    rw [htop] at m1
    exact Finset.disjoint_left.mp hdis m1 m2
  · intro e he
    obtain ⟨C, hC, hval⟩ := (mem_exitBonds r i D η e).mp he
    exact ⟨C, hC, Subtype.ext hval.symm⟩

lemma crossingFamily_restrict {d : ℕ} (r : ℕ) (i : Fin d) (D : ℝ) (ω : Configuration d) :
    crossingFamily (cubeConfig ((issuedBondSet (centeredBox d r)).restrict ω)) r i D =
      crossingFamily ω r i D := by
  apply (crossingFamily_eq_of_internal_agree r i D _ _ ?_).1
  intro b hb
  obtain ⟨hb1, _⟩ := (mem_internalBondSet (centeredBox d r) b).mp hb
  have hbI : b ∈ issuedBondSet (centeredBox d r) :=
    Finset.mem_product.mpr ⟨hb1, Finset.mem_univ _⟩
  exact cubeConfig_apply ((issuedBondSet (centeredBox d r)).restrict ω) ⟨b, hbI⟩

/-! ### G. The averaged flow on the thinned event -/

/-- Source `eq.lower_water_step3`: if at least `t > 0` exit bonds are open, the
average of the corresponding path currents is a supported unit flow of energy
at most `(D+1)/t`. Distinct components give edge-disjoint paths. -/
theorem exists_flow_of_open_exits {d : ℕ} (r : ℕ) (i : Fin d) {D : ℝ} (hD : 0 ≤ D)
    (η : IssuedBond (centeredBox d r) → Bool) {t : ℝ} (ht : 0 < t)
    (hopen : t ≤ (((exitBonds r i D η).filter (fun e => η e = true)).card : ℝ)) :
    ∃ θ : IssuedBond (centeredBox d r) → ℝ,
      Network.FlowSupported (Section10.cubeFlowWeights η) θ ∧
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) θ ∧
      Network.flowEnergy (Section10.cubeFlowWeights η) θ ≤ (D+1)/t := by
  obtain ⟨O, hOdef⟩ : ∃ O : Finset (IssuedBond (centeredBox d r)),
      O = (exitBonds r i D η).filter (fun e => η e = true) := ⟨_, rfl⟩
  rw [← hOdef] at hopen
  have hOpos : (0:ℝ) < (O.card : ℝ) := lt_of_lt_of_le ht hopen
  have hOsub : ∀ b ∈ O, b ∈ exitBonds r i D η ∧ η b = true := by
    intro b hb
    rw [hOdef] at hb
    exact Finset.mem_filter.mp hb
  have hOmem : ∀ e : ↥O, e.val ∈ exitBonds r i D η ∧ η e.val = true :=
    fun e => hOsub e.val e.property
  have hsel : ∀ e : ↥O, ∃ C, C ∈ crossingFamily (cubeConfig η) r i D ∧
      e.val.val = (exitPoint (cubeConfig η) r i D C, i) := by
    intro e
    obtain ⟨C, hC, hval⟩ := (mem_exitBonds r i D η e.val).mp (hOmem e).1
    exact ⟨C, hC, hval⟩
  choose Csel hCsel hval using hsel
  have hexit : ∀ e : ↥O,
      cubeConfig η (exitPoint (cubeConfig η) r i D (Csel e), i) = true := by
    intro e
    rw [← hval e, cubeConfig_apply]
    exact (hOmem e).2
  have hcur := fun e : ↥O =>
    cluster_exit_current i (cubeConfig η) D (Csel e) (hCsel e) (hexit e)
  choose P θ hunit hsupp hmag hopenP hcard hsub using hcur
  have hcO : (Fintype.card ↥O : ℝ) = (O.card : ℝ) := by
    rw [Fintype.card_coe]
  have hIpos : (0:ℝ) < (Fintype.card ↥O : ℝ) := by
    rw [hcO]
    exact hOpos
  have hαsum : (∑ _e : ↥O, 1/(Fintype.card ↥O:ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hIpos.ne'
  refine ⟨Network.weightedFlow (fun _ : ↥O => 1/(Fintype.card ↥O:ℝ)) θ, ?_, ?_, ?_⟩
  · rw [← domainWeights_cubeConfig η]
    exact Network.flowSupported_weighted _ _ θ hsupp
  · exact Network.isBoundaryUnitFlow_weighted _ _ _ _ θ hαsum hunit
  · rw [← domainWeights_cubeConfig η]
    have hdisj : ∀ e f : ↥O, e ≠ f → Disjoint (P e) (P f) := by
      intro e f hef
      rw [Finset.disjoint_left]
      intro b hbe hbf
      have hne : Csel e ≠ Csel f := by
        intro hCC
        apply hef
        apply Subtype.ext
        apply Subtype.ext
        rw [hval e, hval f, hCC]
      have hdis := finiteClusterFamily_disjoint (cubeConfig η) (centeredBox d r)
        ((mem_crossingFamily _ r i D _).mp (hCsel e)).1
        ((mem_crossingFamily _ r i D _).mp (hCsel f)).1 hne
      exact Finset.disjoint_left.mp hdis (hsub e b hbe) (hsub f b hbf)
    have hE := average_disjoint_currents_energy (domainWeights (cubeConfig η)) θ P (D+1)
      hIpos
      (fun e b => by
        have h := hmag e b
        by_cases hb : b ∈ P e
        · rw [if_pos hb] at h ⊢
          exact h
        · rw [if_neg hb] at h ⊢
          exact h)
      hopenP hdisj hcard
    refine hE.trans ?_
    rw [hcO]
    exact div_le_div_of_nonneg_left (by linarith) ht hopen

/-! ### H. The conductivity bound from a crossing count -/

lemma cubeBernoulliWeight_nonneg' {J : Type*} [Fintype J] (p : unitInterval) (η : J → Bool) :
    0 ≤ Section10.cubeBernoulliWeight p η := by
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact p.2.1
  · exact sub_nonneg.mpr p.2.2

lemma localRelaxedConductivity_nonneg' {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) : 0 ≤ localRelaxedConductivity U i η := by
  apply div_nonneg _ (Nat.cast_nonneg U.card)
  exact (issuedNetwork U).conductance_nonneg (fun e => by split <;> norm_num) _ _

lemma annealedRelaxed_eq_weighted_sum {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) :
    (∑ η : IssuedBond U → Bool,
      Section10.cubeBernoulliWeight p η * localRelaxedConductivity U i η) =
        annealedRelaxed U i (p:ℝ) := by
  unfold annealedRelaxed finiteExpectation Section10.cubeBernoulliWeight
  apply Finset.sum_congr
  · ext η
    simp only [Finset.mem_univ]
  · intro η _
    ring

lemma annealedRelaxed_nonneg' {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) : 0 ≤ annealedRelaxed U i (p:ℝ) := by
  rw [← annealedRelaxed_eq_weighted_sum]
  exact Finset.sum_nonneg (fun η _ => mul_nonneg (cubeBernoulliWeight_nonneg' p η)
    (localRelaxedConductivity_nonneg' U i η))

/-- Core of `prop.lower_water` at any parameter: if with probability at least
`a` the odd cube has at least `m` components crossing it in direction `i`
within graph distance `D`, then
`(n^2/|Lambda|) (p a/2) (p m/2) <= a_relaxed(Lambda, p) (D+1)`, `n = 2r+1`. -/
theorem annealedRelaxed_lower_of_crossing_count {d : ℕ} (r : ℕ) (i : Fin d)
    (p : unitInterval) {D m a : ℝ} (hD : 0 ≤ D) (hm : 0 < m) (ha : 0 < a)
    (hcount : a ≤ (percolation d p).real
      {ω | m ≤ ((crossingFamily ω r i D).card : ℝ)}) :
    Section10.cubeFlowNormalization d r * (((p:ℝ)/2)*a) * ((p:ℝ)*m/2) ≤
      annealedRelaxed (centeredBox d r) i (p:ℝ) * (D+1) := by
  have hD1 : 0 < D + 1 := by linarith
  have hR0 := annealedRelaxed_nonneg' (centeredBox d r) i p
  by_cases hp0 : (p:ℝ) = 0
  · have hL : Section10.cubeFlowNormalization d r * (((p:ℝ)/2)*a) * ((p:ℝ)*m/2) = 0 := by
      rw [hp0]
      ring
    rw [hL]
    exact mul_nonneg hR0 hD1.le
  have hppos : 0 < (p:ℝ) := lt_of_le_of_ne p.2.1 (Ne.symm hp0)
  have hs := Section10.cubeFlowNormalization_pos d r
  -- Step 1: the count event as a finite cube event.
  have hP : a ≤ (percolation d p).real
      (Section10.cubeFlowEvent (centeredBox d r) (countEvent r i D m)) := by
    have hev : {ω : Configuration d | m ≤ ((crossingFamily ω r i D).card : ℝ)} =
        Section10.cubeFlowEvent (centeredBox d r) (countEvent r i D m) := by
      ext ω
      have hfam := crossingFamily_restrict r i D ω
      change m ≤ ((crossingFamily ω r i D).card : ℝ) ↔
        m ≤ ((crossingFamily
          (cubeConfig ((issuedBondSet (centeredBox d r)).restrict ω)) r i D).card : ℝ)
      rw [hfam]
    rw [hev] at hcount
    exact hcount
  rw [Section10.cubeFlowEvent_probability] at hP
  -- Step 2: thinning of the exit bonds.
  have hthin := thinning_half_open (p:ℝ) p.2.1 p.2.2 (countEvent r i D m)
    (thinnedEvent r i D m (p:ℝ)) (exitBonds r i D)
    (fun η e he => exitBonds_flip r i D η e he)
    (fun η e he => countEvent_flip r i D m η e he) (fun η => Iff.rfl)
  have hp2 : 0 ≤ (p:ℝ)/2 := by linarith
  -- The generic thinning lemma and the cube statements may carry different
  -- (propositionally equal) `Fintype` instances on the configuration space.
  have hPA' : ((p:ℝ)/2)*a ≤ ∑ η, if η ∈ thinnedEvent r i D m (p:ℝ) then
      Section10.cubeBernoulliWeight p η else 0 := by
    refine le_trans ?_ (le_trans hthin (le_of_eq ?_))
    · apply mul_le_mul_of_nonneg_left _ hp2
      refine le_trans hP (le_of_eq ?_)
      apply Finset.sum_congr
      · ext η
        simp only [Finset.mem_univ]
      · intro η _
        rfl
    · apply Finset.sum_congr
      · ext η
        simp only [Finset.mem_univ]
      · intro η _
        rfl
  have hpa : 0 < ((p:ℝ)/2)*a := mul_pos (by linarith) ha
  have hPApos : 0 < ∑ η, if η ∈ thinnedEvent r i D m (p:ℝ) then
      Section10.cubeBernoulliWeight p η else 0 := lt_of_lt_of_le hpa hPA'
  -- Step 3: the flow on the thinned event.
  have ht : 0 < (p:ℝ)*m/2 := by
    have := mul_pos hppos hm
    linarith
  have hflow : ∀ η ∈ thinnedEvent r i D m (p:ℝ),
      ∃ θ : IssuedBond (centeredBox d r) → ℝ,
        Network.FlowSupported (Section10.cubeFlowWeights η) θ ∧
        (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
          (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) θ ∧
        Network.flowEnergy (Section10.cubeFlowWeights η) θ ≤ (D+1)/((p:ℝ)*m/2) := by
    intro η hη
    obtain ⟨hcountη, hopenη⟩ : η ∈ countEvent r i D m ∧
        (p:ℝ) * ((exitBonds r i D η).card:ℝ) ≤
          2 * (((exitBonds r i D η).filter (fun e => η e = true)).card:ℝ) := hη
    have hm' : m ≤ ((exitBonds r i D η).card : ℝ) := by
      rw [exitBonds_card]
      exact hcountη
    apply exists_flow_of_open_exits r i hD η ht
    nlinarith [mul_le_mul_of_nonneg_left hm' hppos.le]
  let θ : (IssuedBond (centeredBox d r) → Bool) → IssuedBond (centeredBox d r) → ℝ :=
    fun η => if h : η ∈ thinnedEvent r i D m (p:ℝ) then (hflow η h).choose else 0
  have hθ : ∀ η (h : η ∈ thinnedEvent r i D m (p:ℝ)), θ η = (hflow η h).choose := by
    intro η h
    dsimp only [θ]
    rw [dif_pos h]
  -- Step 4: the finite-law Cauchy--Schwarz reduction.
  have he : ∀ η, 0 ≤ Network.flowEnergy (Section10.cubeFlowWeights η) (θ η) := by
    intro η
    apply Finset.sum_nonneg
    intro e _
    apply div_nonneg (sq_nonneg _)
    dsimp only [Section10.cubeFlowWeights]
    split <;> norm_num
  have hpoint : ∀ η ∈ thinnedEvent r i D m (p:ℝ),
      Section10.cubeFlowNormalization d r ≤
        localRelaxedConductivity (centeredBox d r) i η *
          Network.flowEnergy (Section10.cubeFlowWeights η) (θ η) := by
    intro η hη
    obtain ⟨hsupp, hunit, _⟩ := (hflow η hη).choose_spec
    rw [← hθ η hη] at hsupp hunit
    obtain ⟨hEpos, hb⟩ := local_relaxed_flow_lower i η (θ η) hsupp hunit
    apply (div_le_iff₀ hEpos).mp
    have hrw : Section10.cubeFlowNormalization d r /
        Network.flowEnergy (Section10.cubeFlowWeights η) (θ η) =
        ((2*(r:ℝ)+1)^2/Network.flowEnergy (Section10.cubeFlowWeights η) (θ η))/
          ((centeredBox d r).card:ℝ) := by
      unfold Section10.cubeFlowNormalization
      rw [div_right_comm]
    rw [hrw]
    exact hb
  obtain ⟨hEApos, hmean⟩ := Section10.mean_conductivity_lower
    (Section10.cubeBernoulliWeight p) (localRelaxedConductivity (centeredBox d r) i)
    (fun η => Network.flowEnergy (Section10.cubeFlowWeights η) (θ η))
    (thinnedEvent r i D m (p:ℝ)) (cubeBernoulliWeight_nonneg' p)
    (localRelaxedConductivity_nonneg' _ i) he hs hpoint hPApos
  rw [annealedRelaxed_eq_weighted_sum] at hmean
  -- Step 5: the energy budget on the thinned event.
  have hEA : (∑ η, if η ∈ thinnedEvent r i D m (p:ℝ) then
      Section10.cubeBernoulliWeight p η *
        Network.flowEnergy (Section10.cubeFlowWeights η) (θ η) else 0) ≤
      ((D+1)/((p:ℝ)*m/2)) * ∑ η, if η ∈ thinnedEvent r i D m (p:ℝ) then
        Section10.cubeBernoulliWeight p η else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro η _
    by_cases h : η ∈ thinnedEvent r i D m (p:ℝ)
    · have hen := (hflow η h).choose_spec.2.2
      rw [← hθ η h] at hen
      rw [if_pos h, if_pos h]
      calc Section10.cubeBernoulliWeight p η *
            Network.flowEnergy (Section10.cubeFlowWeights η) (θ η)
          ≤ Section10.cubeBernoulliWeight p η * ((D+1)/((p:ℝ)*m/2)) :=
            mul_le_mul_of_nonneg_left hen (cubeBernoulliWeight_nonneg' p η)
        _ = _ := mul_comm _ _
    · simp only [if_neg h, mul_zero, le_refl]
  -- Step 6: assemble.
  obtain ⟨PA, hPAdef⟩ : ∃ PA : ℝ, PA = ∑ η, if η ∈ thinnedEvent r i D m (p:ℝ) then
      Section10.cubeBernoulliWeight p η else 0 := ⟨_, rfl⟩
  obtain ⟨EA, hEAdef⟩ : ∃ EA : ℝ, EA = ∑ η, if η ∈ thinnedEvent r i D m (p:ℝ) then
      Section10.cubeBernoulliWeight p η *
        Network.flowEnergy (Section10.cubeFlowWeights η) (θ η) else 0 := ⟨_, rfl⟩
  have hPA'2 : ((p:ℝ)/2)*a ≤ PA := by
    rw [hPAdef]
    exact hPA'
  have hPApos2 : 0 < PA := by
    rw [hPAdef]
    exact hPApos
  have hEApos2 : 0 < EA := by
    rw [hEAdef]
    exact hEApos
  have hmean2 : Section10.cubeFlowNormalization d r * PA^2 / EA ≤
      annealedRelaxed (centeredBox d r) i (p:ℝ) := by
    rw [hPAdef, hEAdef]
    exact hmean
  have hEA2 : EA ≤ ((D+1)/((p:ℝ)*m/2)) * PA := by
    rw [hPAdef, hEAdef]
    exact hEA
  have h1 : Section10.cubeFlowNormalization d r * PA^2 ≤
      annealedRelaxed (centeredBox d r) i (p:ℝ) * EA := (div_le_iff₀ hEApos2).mp hmean2
  have h2 : EA * ((p:ℝ)*m/2) ≤ (D+1) * PA := by
    have h := mul_le_mul_of_nonneg_right hEA2 ht.le
    have hcancel : (D+1)/((p:ℝ)*m/2) * PA * ((p:ℝ)*m/2) = (D+1) * PA := by
      calc (D+1)/((p:ℝ)*m/2) * PA * ((p:ℝ)*m/2)
          = (D+1) * PA * (((p:ℝ)*m/2)/((p:ℝ)*m/2)) := by ring
        _ = (D+1) * PA := by rw [div_self ht.ne', mul_one]
    linarith
  have h3 : Section10.cubeFlowNormalization d r * PA^2 * ((p:ℝ)*m/2) ≤
      annealedRelaxed (centeredBox d r) i (p:ℝ) * (D+1) * PA := by
    calc Section10.cubeFlowNormalization d r * PA^2 * ((p:ℝ)*m/2)
        ≤ annealedRelaxed (centeredBox d r) i (p:ℝ) * EA * ((p:ℝ)*m/2) :=
          mul_le_mul_of_nonneg_right h1 ht.le
      _ = annealedRelaxed (centeredBox d r) i (p:ℝ) * (EA * ((p:ℝ)*m/2)) := by ring
      _ ≤ annealedRelaxed (centeredBox d r) i (p:ℝ) * ((D+1) * PA) :=
          mul_le_mul_of_nonneg_left h2 hR0
      _ = _ := by ring
  have h4 : PA * (Section10.cubeFlowNormalization d r * PA * ((p:ℝ)*m/2)) ≤
      PA * (annealedRelaxed (centeredBox d r) i (p:ℝ) * (D+1)) := by
    calc PA * (Section10.cubeFlowNormalization d r * PA * ((p:ℝ)*m/2))
        = Section10.cubeFlowNormalization d r * PA^2 * ((p:ℝ)*m/2) := by ring
      _ ≤ annealedRelaxed (centeredBox d r) i (p:ℝ) * (D+1) * PA := h3
      _ = _ := by ring
  have h5 := le_of_mul_le_mul_left h4 hPApos2
  calc Section10.cubeFlowNormalization d r * (((p:ℝ)/2)*a) * ((p:ℝ)*m/2)
      ≤ Section10.cubeFlowNormalization d r * PA * ((p:ℝ)*m/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPA'2 hs.le) ht.le
    _ ≤ _ := h5

/-! ### I. Source form: `lem.spanning.diam` implies `prop.lower_water` -/

/-- Source set `S` of `eq.def.spanning.diam`: `2d`-spanning components of the
odd cube with face diameter at most `C2 n^2` and volume in `(c0 n^4, C0 n^4)`,
`n = 2r+1`. -/
def spanningDiamFamily {d : ℕ} (ω : Configuration d) (r : ℕ) (C2 c0 C0 : ℝ) :
    Finset (Finset (Vertex d)) :=
  (finiteClusterFamily ω (centeredBox d r)).filter (fun C =>
    (∀ f : Fin d × Bool, (C ∩ signedCubeFace d r f).Nonempty) ∧
    (spanningFaceDiameter (restrictedGraph ω (centeredBox d r : Set (Vertex d))) C
      (signedCubeFace d r) : ℝ) ≤ C2 * (2*(r:ℝ)+1)^2 ∧
    c0 * (2*(r:ℝ)+1)^4 < (C.card : ℝ) ∧ (C.card : ℝ) < C0 * (2*(r:ℝ)+1)^4)

/-- The literal statement of source `lem.spanning.diam` (main.tex 1500) at the
critical point, for the odd cubes `Lambda_n`, `n = 2r+1`. This is the retained
input of Section 7; it is a paper lemma, not a cited literature result. -/
def SpanningDiamStatement (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ (N0 : ℕ) (c0 C0 c1 C1 C2 : ℝ), 0 < c0 ∧ 0 < C0 ∧ 0 < c1 ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ r : ℕ, N0 ≤ r → 1 - ε < (percolation d (criticalPoint d)).real
        {ω | c1 * (2*(r:ℝ)+1)^(d-6) ≤ ((spanningDiamFamily ω r C2 c0 C0).card : ℝ) ∧
          ((spanningDiamFamily ω r C2 c0 C0).card : ℝ) ≤ C1 * (2*(r:ℝ)+1)^(d-6)}

lemma mem_signedCubeFace_coord {d r : ℕ} {x : Vertex d} {i : Fin d} {b : Bool}
    (hx : x ∈ signedCubeFace d r (i, b)) :
    x i = if b then (r:ℤ) else -(r:ℤ) := by
  unfold signedCubeFace at hx
  exact (Finset.mem_filter.mp hx).2

theorem spanningDiamFamily_subset_crossingFamily {d : ℕ} (ω : Configuration d) (r : ℕ)
    (i : Fin d) (C2 c0 C0 : ℝ) :
    spanningDiamFamily ω r C2 c0 C0 ⊆ crossingFamily ω r i (C2 * (2*(r:ℝ)+1)^2) := by
  intro C hC
  unfold spanningDiamFamily at hC
  obtain ⟨hfam, hspan, hdiam, _, _⟩ := Finset.mem_filter.mp hC
  obtain ⟨x, hx⟩ := hspan (i, false)
  obtain ⟨y, hy⟩ := hspan (i, true)
  have hxi : x i = -(r:ℤ) := by
    have h := mem_signedCubeFace_coord (Finset.mem_inter.mp hx).2
    simpa using h
  have hyi : y i = (r:ℤ) := by
    have h := mem_signedCubeFace_coord (Finset.mem_inter.mp hy).2
    simpa using h
  have hne : ((i, false) : Fin d × Bool) ≠ (i, true) := by simp
  have hdist := dist_le_spanningFaceDiameter
    (restrictedGraph ω (centeredBox d r : Set (Vertex d))) C (signedCubeFace d r) hne hx hy
  refine (mem_crossingFamily ω r i _ C).mpr ⟨hfam, x, (Finset.mem_inter.mp hx).1, y,
    (Finset.mem_inter.mp hy).1, hxi, hyi, le_trans ?_ hdiam⟩
  exact_mod_cast hdist

/-- Scale form of the core bound: if, for all `r >= N0`, with probability at
least `1/2` the odd cube has at least `c1 n^(d-6)` components crossing it within
graph distance `C2 n^2` (`n = 2r+1`), then
`(p_c^2 c1 / (8 (C2+1))) n^(-6) <= a(Lambda_n, p_c)`. -/
theorem lower_water_of_crossing_count {d : ℕ} (hd : 6 ≤ d) (i : Fin d)
    {c1 C2 : ℝ} (hc1 : 0 < c1) (hC2 : 0 < C2) (N0 : ℕ)
    (hcount : ∀ r : ℕ, N0 ≤ r → (1/2 : ℝ) ≤ (percolation d (criticalPoint d)).real
      {ω | c1 * (2*(r:ℝ)+1)^(d-6) ≤
        ((crossingFamily ω r i (C2 * (2*(r:ℝ)+1)^2)).card : ℝ)}) :
    ∀ r : ℕ, N0 ≤ r →
      ((criticalPoint d : ℝ)^2 * c1 / (8*(C2+1))) / (2*(r:ℝ)+1)^6 ≤
        annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := by
  have hC21 : 0 < 8*(C2+1) := by linarith
  intro r hr
  have hcount' := hcount r hr
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = 2*(r:ℝ)+1 := ⟨_, rfl⟩
  rw [← hNdef] at hcount' ⊢
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN1
  have hN2 : 1 ≤ N^2 := one_le_pow₀ hN1
  have hX : 0 < N^(d-6) := pow_pos hNpos _
  have hN6 : 0 < N^6 := pow_pos hNpos _
  have hDnn : 0 ≤ C2 * N^2 := mul_nonneg hC2.le (sq_nonneg N)
  have hcore := annealedRelaxed_lower_of_crossing_count r i (criticalPoint d)
    (D := C2 * N^2) (m := c1 * N^(d-6)) (a := 1/2) hDnn (mul_pos hc1 hX)
    (by norm_num) hcount'
  have hR0 := annealedRelaxed_nonneg' (centeredBox d r) i (criticalPoint d)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ,
      R = annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := ⟨_, rfl⟩
  rw [← hRdef] at hcore hR0 ⊢
  have hcard : ((centeredBox d r).card : ℝ) = N^(d-6) * N^6 := by
    rw [card_centeredBox_exact, ← pow_add, Nat.sub_add_cancel hd, hNdef]
    norm_num
  have hXN : N^(d-6) * N^6 ≠ 0 := (mul_pos hX hN6).ne'
  have hsX : Section10.cubeFlowNormalization d r * (N^(d-6) * N^6) = N^2 := by
    unfold Section10.cubeFlowNormalization
    rw [hcard, ← hNdef, div_mul_eq_mul_div, mul_div_assoc, div_self hXN, mul_one]
  have key : N^2 * ((criticalPoint d : ℝ)^2 * c1 / 8) ≤ R * (C2 * N^2 + 1) * N^6 := by
    calc N^2 * ((criticalPoint d : ℝ)^2 * c1 / 8)
        = (Section10.cubeFlowNormalization d r * (N^(d-6) * N^6)) *
            ((criticalPoint d : ℝ)^2 * c1 / 8) := by rw [hsX]
      _ = (Section10.cubeFlowNormalization d r *
            (((criticalPoint d : ℝ)/2)*(1/2)) * ((criticalPoint d : ℝ)*(c1 * N^(d-6))/2)) *
            N^6 := by ring
      _ ≤ (R * (C2 * N^2 + 1)) * N^6 := mul_le_mul_of_nonneg_right hcore hN6.le
      _ = _ := by ring
  have hle : C2 * N^2 + 1 ≤ (C2+1) * N^2 := by nlinarith
  have hRN : 0 ≤ R * N^6 := mul_nonneg hR0 hN6.le
  have h4 := mul_le_mul_of_nonneg_left hle hRN
  have h3 : N^2 * ((criticalPoint d : ℝ)^2 * c1) ≤ N^2 * (R * N^6 * (8*(C2+1))) := by
    nlinarith [key, h4]
  have h5 : (criticalPoint d : ℝ)^2 * c1 ≤ R * N^6 * (8*(C2+1)) :=
    le_of_mul_le_mul_left h3 (pow_pos hNpos 2)
  rw [div_le_iff₀ hN6, div_le_iff₀ hC21]
  exact h5

/-- **Source `prop.lower_water`, `eq.lower_water_general`** (main.tex 2714) for the
relaxed annealed conductivity of the odd cube `Lambda_n`, `n = 2r+1`, at the
critical point: `c n^(-6) <= a(Lambda_n, p_c)` for `r >= N_0`. Conditional only
on the source lemma `lem.spanning.diam` and `0 < p_c`. -/
theorem lower_water_general {d : ℕ} (hd : 6 ≤ d) (i : Fin d)
    (hpc : 0 < (criticalPoint d : ℝ)) (hS : SpanningDiamStatement d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ r : ℕ, N0 ≤ r →
      c / (2*(r:ℝ)+1)^6 ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := by
  obtain ⟨N0, c0, C0, c1, C1, C2, _, _, hc1, _, hC2, hprob⟩ :=
    hS (1/2) (by norm_num) (by norm_num)
  have hC21 : 0 < 8*(C2+1) := by linarith
  have hcpos : 0 < (criticalPoint d : ℝ)^2 * c1 / (8*(C2+1)) :=
    div_pos (mul_pos (pow_pos hpc 2) hc1) hC21
  refine ⟨(criticalPoint d : ℝ)^2 * c1 / (8*(C2+1)), hcpos, N0, ?_⟩
  apply lower_water_of_crossing_count hd i hc1 hC2 N0
  intro r hr
  have h := (hprob r hr).le
  have h12 : (1/2 : ℝ) ≤ 1 - 1/2 := by norm_num
  refine le_trans h12 (le_trans h (measureReal_mono ?_ (measure_ne_top _ _)))
  intro ω hω
  have hsub := Finset.card_le_card
    (spanningDiamFamily_subset_crossingFamily ω r i C2 c0 C0)
  have hsub' : ((spanningDiamFamily ω r C2 c0 C0).card : ℝ) ≤
      ((crossingFamily ω r i (C2 * (2*(r:ℝ)+1)^2)).card : ℝ) := by exact_mod_cast hsub
  exact le_trans hω.1 hsub'

/-! ### J. Monotonicity in the parameter and `eq.lower_water` -/

/-- Verbatim copy of the private thinning lemma of `Section10ConductivityMonotone`. -/
private theorem finite_expectation_parameter_le_copy {E : Type*} [Fintype E]
    (f : (E → Bool) → ℝ) (hmono : ∀ η ξ, BK.ConfigLE η ξ → f η ≤ f ξ)
    {p q : unitInterval} (hpq : p ≤ q) : finiteExpectation (p:ℝ) f ≤ finiteExpectation (q:ℝ) f := by
  by_cases hq : (q:ℝ) = 0
  · have heq : p = q := by
      apply Subtype.ext
      exact le_antisymm hpq (by simpa only [hq] using p.2.1)
    rw [heq]
  · have hqpos : 0 < (q:ℝ) := lt_of_le_of_ne q.2.1 (Ne.symm hq)
    let r : unitInterval := ⟨(p:ℝ)/(q:ℝ),div_nonneg p.2.1 q.2.1,(div_le_one hqpos).mpr hpq⟩
    have hr : (p:ℝ) = (q:ℝ)*(r:ℝ) := by dsimp [r]; field_simp
    have hmap := finite_thin_map (E := E) q r p hr
    calc
      _ = ∫ η, f η ∂(Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false p)) :=
        (integral_finite_bernoulli p f).symm
      _ = ∫ z : (E → Bool) × (E → Bool), f (thinConfiguration z)
          ∂((Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false q)).prod
            (Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false r))) := by
        rw [← hmap]
        exact integral_map measurable_thinConfiguration.aemeasurable
          (measurable_of_finite f).aestronglyMeasurable
      _ ≤ ∫ z : (E → Bool) × (E → Bool), f z.1
          ∂((Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false q)).prod
            (Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false r))) := by
        exact integral_mono Integrable.of_finite Integrable.of_finite
          (fun z => hmono _ _ (thinConfiguration_le_left z))
      _ = ∫ η, f η ∂(Measure.pi (fun _ : E => ProbabilityTheory.bernoulliMeasure true false q)) := by
        rw [integral_fun_fst]
        simp only [probReal_univ,one_smul]
      _ = _ := integral_finite_bernoulli q f

/-- The relaxed local conductivity is increasing in the issued-bond assignment
(relaxed analogue of `Section10.localFullConductivity_config_mono`). -/
theorem localRelaxedConductivity_config_mono {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {η ξ : IssuedBond U → Bool} (hηξ : BK.ConfigLE η ξ) :
    localRelaxedConductivity U i η ≤ localRelaxedConductivity U i ξ := by
  have hw (e : IssuedBond U) : (if η e then (1:ℝ) else 0) ≤ if ξ e then 1 else 0 := by
    cases he : η e
    · simp only [he,Bool.false_eq_true,ite_false]
      split <;> norm_num
    · have hf := hηξ e he
      simp [he,hf]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg U.card)
  exact (issuedNetwork U).conductance_mono
    (fun e => by split <;> norm_num) hw (twoFaceBoundary U i) (coordinateData i)

/-- The actual relaxed annealed conductivity is monotone in the parameter. -/
theorem annealedRelaxed_parameter_mono {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {p q : unitInterval} (hpq : p ≤ q) :
    annealedRelaxed U i (p:ℝ) ≤ annealedRelaxed U i (q:ℝ) := by
  exact finite_expectation_parameter_le_copy (localRelaxedConductivity U i)
    (fun η ξ h => localRelaxedConductivity_config_mono U i h) hpq

/-- **Source `prop.lower_water`, `eq.lower_water`** (main.tex 2718): for every
`p > p_c` and every odd cube of side `n = 2r+1` with `N_0 <= r` and
`n <= l_*(p) = floor((p-p_c)^(-1/2))`, `c (p - p_c)^3 <= a(Lambda_n, p)`. -/
theorem lower_water {d : ℕ} (hd : 6 ≤ d) (i : Fin d)
    (hpc : 0 < (criticalPoint d : ℝ)) (hS : SpanningDiamStatement d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ p : unitInterval, criticalPoint d < p →
      ∀ r : ℕ, N0 ≤ r → 2*r+1 ≤ chemicalCorrelationScale d p →
        c * ((p:ℝ) - (criticalPoint d : ℝ))^3 ≤
          annealedRelaxed (centeredBox d r) i (p:ℝ) := by
  obtain ⟨c, hc, N0, hgen⟩ := lower_water_general hd i hpc hS
  refine ⟨c, hc, N0, ?_⟩
  intro p hp r hr hscale
  have hNpos : (0:ℝ) < 2*(r:ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have hle : (2*(r:ℝ)+1) ≤ (chemicalCorrelationScale d p : ℝ) := by exact_mod_cast hscale
  have h6 : (2*(r:ℝ)+1)^6 ≤ (chemicalCorrelationScale d p : ℝ)^6 :=
    pow_le_pow_left₀ hNpos.le hle 6
  have hinv := Section10.chemicalCorrelationScale_inverse_six_lower p hp
  have hinv2 : 1/(chemicalCorrelationScale d p : ℝ)^6 ≤ 1/(2*(r:ℝ)+1)^6 :=
    one_div_le_one_div_of_le (pow_pos hNpos 6) h6
  calc c * ((p:ℝ) - (criticalPoint d : ℝ))^3
      ≤ c * (1/(2*(r:ℝ)+1)^6) := mul_le_mul_of_nonneg_left (hinv.trans hinv2) hc.le
    _ = c / (2*(r:ℝ)+1)^6 := mul_one_div _ _
    _ ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) := hgen r hr
    _ ≤ annealedRelaxed (centeredBox d r) i (p:ℝ) :=
        annealedRelaxed_parameter_mono _ i hp.le

/-- Full-Dirichlet corollary of `lower_water_general`. -/
theorem lower_water_general_full {d : ℕ} (hd : 6 ≤ d) (i : Fin d)
    (hpc : 0 < (criticalPoint d : ℝ)) (hS : SpanningDiamStatement d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ r : ℕ, N0 ≤ r →
      c / (2*(r:ℝ)+1)^6 ≤ annealedFull (centeredBox d r) i (criticalPoint d : ℝ) := by
  obtain ⟨c, hc, N0, hgen⟩ := lower_water_general hd i hpc hS
  refine ⟨c, hc, N0, ?_⟩
  intro r hr
  exact (hgen r hr).trans
    (annealedRelaxed_le_full _ i (criticalPoint d).2.1 (criticalPoint d).2.2)

end NearCritical.Section7
