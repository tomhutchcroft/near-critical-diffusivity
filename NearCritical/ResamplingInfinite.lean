module

public import NearCritical.ResamplingLaw
public import Mathlib.Probability.ProductMeasure

/-! Resampling inside an infinite product law.

`resample_infinite_law`: let `ω, ω'` be two independent samples of an infinite
product law on `ι → Bool`, `J` a finite set of indices and `E ω ⊆ J` a stopping
set. The configuration equal to `ω'` on `J \ E ω` and to `ω` elsewhere has the
same infinite product law.

Proof: by uniqueness of the infinite product measure on finite boxes, reduce to
the finite set `s ∪ J` and apply `resample_law` with the stopping set enlarged
by the fixed set `(s ∪ J) \ J`.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Set
open scoped Classical

variable {ι : Type*}

/-- Use the second sample on `J \ E ω`, the first elsewhere. -/
def resampleOn (J : Finset ι) (E : (ι → Bool) → Finset ι)
    (q : (ι → Bool) × (ι → Bool)) : ι → Bool :=
  fun i => if i ∈ J ∧ i ∉ E q.1 then q.2 i else q.1 i

theorem resample_infinite_law (μ : ι → Measure Bool) [∀ i, IsProbabilityMeasure (μ i)]
    (J : Finset ι) (E : (ι → Bool) → Finset ι) (hsub : ∀ ω, E ω ⊆ J)
    (hstop : ∀ ω ω' : ι → Bool, (∀ i ∈ E ω, ω' i = ω i) → E ω' = E ω) :
    Measurable (resampleOn J E) ∧
    Measure.map (resampleOn J E) ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) =
      Measure.infinitePi μ := by
  have hEJ : ∀ ω ω' : ι → Bool, (∀ i ∈ J, ω' i = ω i) → E ω' = E ω :=
    fun ω ω' h => hstop ω ω' (fun i hi => h i (hsub ω hi))
  have hEmeas : ∀ i, MeasurableSet {ω : ι → Bool | i ∈ E ω} := by
    intro i
    have hrw : {ω : ι → Bool | i ∈ E ω} = J.restrict ⁻¹'
        {ξ : J → Bool | i ∈ E (fun k => if h : k ∈ J then ξ ⟨k, h⟩ else false)} := by
      ext ω
      simp only [mem_setOf_eq, mem_preimage]
      rw [hEJ ω (fun k => if h : k ∈ J then J.restrict ω ⟨k, h⟩ else false)
        (fun k hk => by simp [hk, Finset.restrict])]
    rw [hrw]
    exact (Finset.measurable_restrict J) MeasurableSet.of_discrete
  have hT : Measurable (resampleOn J E) := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i ∈ J
    · have hset : MeasurableSet {q : (ι → Bool) × (ι → Bool) | i ∈ J ∧ i ∉ E q.1} := by
        have hrw : {q : (ι → Bool) × (ι → Bool) | i ∈ J ∧ i ∉ E q.1} =
            Prod.fst ⁻¹' {ω : ι → Bool | i ∈ E ω}ᶜ := by
          ext q
          simp [hi]
        rw [hrw]
        exact measurable_fst (hEmeas i).compl
      exact Measurable.ite hset ((measurable_pi_apply i).comp measurable_snd)
        ((measurable_pi_apply i).comp measurable_fst)
    · have hrw : (fun q : (ι → Bool) × (ι → Bool) => resampleOn J E q i) = fun q => q.1 i := by
        funext q
        simp [resampleOn, hi]
      rw [hrw]
      exact (measurable_pi_apply i).comp measurable_fst
  refine ⟨hT, ?_⟩
  refine Measure.eq_infinitePi μ fun s t ht => ?_
  rw [Measure.map_apply hT (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  obtain ⟨s', hs'⟩ : ∃ s' : Finset ι, s' = s ∪ J := ⟨_, rfl⟩
  have hss' : s ⊆ s' := by rw [hs']; exact Finset.subset_union_left
  have hJs' : J ⊆ s' := by rw [hs']; exact Finset.subset_union_right
  obtain ⟨ext', hext'⟩ : ∃ ext' : (s' → Bool) → ι → Bool,
      ext' = fun ζ i => if h : i ∈ s' then ζ ⟨i, h⟩ else false := ⟨_, rfl⟩
  obtain ⟨E'', hE''def⟩ : ∃ E'' : (s' → Bool) → Finset s',
      E'' = fun ζ => (Finset.univ.filter fun i : s' => (i : ι) ∈ E (ext' ζ)) ∪
        (Finset.univ.filter fun i : s' => (i : ι) ∉ J) := ⟨_, rfl⟩
  have hext : ∀ ω : ι → Bool, E (ext' (s'.restrict ω)) = E ω := fun ω =>
    hEJ ω _ (fun i hi => by simp [hext', hJs' hi, Finset.restrict])
  have hE'' : ∀ ζ ζ' : s' → Bool, (∀ j ∈ E'' ζ, ζ' j = ζ j) → E'' ζ' = E'' ζ := by
    intro ζ ζ' h
    have hEq : E (ext' ζ') = E (ext' ζ) := hstop _ _ (fun i hi => by
      have his := hJs' (hsub _ hi)
      have hmem : (⟨i, his⟩ : s') ∈ E'' ζ := by
        rw [hE''def]
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have := h ⟨i, his⟩ hmem
      simp only [hext', dif_pos his]
      exact this)
    rw [hE''def]
    simp only [hEq]
  obtain ⟨t', ht'⟩ : ∃ t' : ι → Set Bool, t' = fun i => if i ∈ s then t i else univ := ⟨_, rfl⟩
  have hres : ∀ (q : (ι → Bool) × (ι → Bool)) (i : s'),
      resample E'' (Prod.map s'.restrict s'.restrict q) i = resampleOn J E q i := by
    intro q i
    have hmem : i ∈ E'' (s'.restrict q.1) ↔ ¬ ((i : ι) ∈ J ∧ (i : ι) ∉ E q.1) := by
      rw [hE''def]
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hext q.1]
      tauto
    change (if i ∈ E'' (s'.restrict q.1) then s'.restrict q.1 i else s'.restrict q.2 i) =
      if (i : ι) ∈ J ∧ (i : ι) ∉ E q.1 then q.2 i else q.1 i
    by_cases hc : (i : ι) ∈ J ∧ (i : ι) ∉ E q.1
    · rw [if_neg (fun hm => (hmem.mp hm) hc), if_pos hc]
      rfl
    · rw [if_pos (hmem.mpr hc), if_neg hc]
      rfl
  have hpre : resampleOn J E ⁻¹' (Set.pi s t) = (Prod.map s'.restrict s'.restrict) ⁻¹'
      (resample E'' ⁻¹' (Set.pi univ fun i : s' => t' i)) := by
    ext q
    simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_univ, true_imp_iff]
    constructor
    · intro h i
      rw [hres q i, ht']
      by_cases his : (i : ι) ∈ s
      · simp only [if_pos his]
        exact h i his
      · simp only [if_neg his]
        exact mem_univ _
    · intro h i his
      have := h ⟨i, hss' his⟩
      rw [hres q, ht'] at this
      simpa [his] using this
  have hmap : Measure.map (Prod.map s'.restrict s'.restrict)
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) =
      (Measure.pi fun i : s' => μ i).prod (Measure.pi fun i : s' => μ i) := by
    rw [← Measure.map_prod_map _ _ (Finset.measurable_restrict s')
      (Finset.measurable_restrict s'), Measure.infinitePi_map_restrict]
  rw [hpre, ← Measure.map_apply ((Finset.measurable_restrict s').prodMap
    (Finset.measurable_restrict s')) MeasurableSet.of_discrete, hmap,
    ← Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    resample_law (fun i : s' => μ i) E'' hE'', Measure.pi_pi,
    Finset.prod_coe_sort s' (fun i => μ i (t' i)),
    ← Finset.prod_subset hss' (fun i _ hi => by
      rw [ht']
      simp only [if_neg hi]
      exact measure_univ)]
  exact Finset.prod_congr rfl (fun i hi => by
    rw [ht']
    simp only [if_pos hi])

end NearCritical
