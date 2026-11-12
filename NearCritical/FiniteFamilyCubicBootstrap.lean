module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Semicontinuity.Basic

/-! NEW analytic bootstrap underlying source eq.M.diff -> eq.M.upper.
The actual finite maximum is used only continuously; it is never differentiated. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- The actual maximum of a finite nonempty family at a given parameter. -/
def finiteFamilyMaximum {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) (t : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ f i t)

lemma le_finiteFamilyMaximum {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) (i : I) (t : ℝ) : f i t ≤ finiteFamilyMaximum f t :=
  Finset.le_sup' (fun j ↦ f j t) (Finset.mem_univ i)

lemma finiteFamilyMaximum_le {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) (t r : ℝ) (h : ∀ i, f i t ≤ r) : finiteFamilyMaximum f t ≤ r :=
  Finset.sup'_le _ _ (fun i _ ↦ h i)

/-- Finite-family cubic bootstrap by a FIRST CROSSING, without assuming that
the finite maximum is differentiable. Continuity and interior differentiability
of each coordinate suffice; the quantitative C1 version follows below. -/
theorem finite_family_cubic_bootstrap {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b C L : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hcont : ∀ i, ContinuousOn (f i) (Icc a b))
    (hdiff : ∀ i, DifferentiableOn ℝ (f i) (Ioo a b))
    (hnonneg : ∀ i t, t ∈ Icc a b → 0 ≤ f i t)
    (hstart : ∀ i, f i a ≤ C)
    (hderiv : ∀ i t, t ∈ Ioo a b → deriv (f i) t ≤ L * (finiteFamilyMaximum f t) ^ 3)
    (hsmall : 16 * L * C ^ 2 * (b - a) ≤ 1) :
    ∀ t ∈ Icc a b, ∀ i, f i t ≤ 2 * C := by
  let M := finiteFamilyMaximum f
  have hMcont : ContinuousOn M (Icc a b) :=
    ContinuousOn.finset_sup'_apply Finset.univ_nonempty (fun i _ ↦ hcont i)
  have hMa : M a ≤ C := finiteFamilyMaximum_le f a C hstart
  let T := Icc a b ∩ M ⁻¹' Ici (2 * C)
  have hcompact : IsCompact T :=
    hMcont.upperSemicontinuousOn.isCompact_inter_preimage_Ici isCompact_Icc (2 * C)
  intro t ht i
  by_contra hbad
  have hbad' : 2 * C < f i t := lt_of_not_ge hbad
  have hTne : T.Nonempty := ⟨t, ht, hbad'.le.trans (le_finiteFamilyMaximum f i t)⟩
  obtain ⟨c, hc, hmin⟩ : ∃ c ∈ T, ∀ s ∈ T, c ≤ s :=
    hcompact.exists_isMinOn hTne continuous_id.continuousOn
  have hcIcc : c ∈ Icc a b := hc.1
  have hcM : 2 * C ≤ M c := hc.2
  have hac : a < c := by
    by_contra h
    have hca : c = a := le_antisymm (le_of_not_gt h) hcIcc.1
    rw [hca] at hcM
    linarith
  have hpre : ∀ s ∈ Ioo a c, M s < 2 * C := by
    intro s hs
    by_contra h
    have hsT : s ∈ T := ⟨⟨hs.1.le, hs.2.le.trans hcIcc.2⟩, le_of_not_gt h⟩
    exact (not_le_of_gt hs.2) (hmin s hsT)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j ↦ f j c)
  change M c = f j c at hj
  have hcontac : ContinuousOn (f j) (Icc a c) :=
    (hcont j).mono (fun s hs ↦ ⟨hs.1, hs.2.trans hcIcc.2⟩)
  have hdiffac : DifferentiableOn ℝ (f j) (interior (Icc a c)) := by
    rw [interior_Icc]
    exact (hdiff j).mono (fun s hs ↦ ⟨hs.1, lt_of_lt_of_le hs.2 hcIcc.2⟩)
  have hderivac : ∀ s ∈ interior (Icc a c), deriv (f j) s ≤ 8 * L * C ^ 3 := by
    intro s hs
    rw [interior_Icc] at hs
    have hsAB : s ∈ Ioo a b := ⟨hs.1, lt_of_lt_of_le hs.2 hcIcc.2⟩
    have hM0 : 0 ≤ M s := (hnonneg j s ⟨hsAB.1.le, hsAB.2.le⟩).trans
      (le_finiteFamilyMaximum f j s)
    calc
      _ ≤ L * (M s) ^ 3 := hderiv j s hsAB
      _ ≤ L * (2 * C) ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hM0 (hpre s hs).le 3) hL
      _ = _ := by ring
  have hinc := (convex_Icc a c).image_sub_le_mul_sub_of_deriv_le hcontac hdiffac
    hderivac a (left_mem_Icc.mpr hac.le) c (right_mem_Icc.mpr hac.le) hac.le
  have hgrowth : 8 * L * C ^ 3 * (c - a) ≤ 8 * L * C ^ 3 * (b - a) :=
    mul_le_mul_of_nonneg_left (by linarith [hcIcc.2]) (by positivity)
  have hsmallC := mul_le_mul_of_nonneg_right hsmall hC.le
  have hsmall' : 8 * L * C ^ 3 * (b - a) ≤ C / 2 := by nlinarith
  have hjc : 2 * C ≤ f j c := by simpa only [hj] using hcM
  linarith [hstart j]

/-- C1-on-the-closed-interval interface. No regularity of the maximum is a premise. -/
theorem finite_family_cubic_bootstrap_of_contDiffOn {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b C L : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hC1 : ∀ i, ContDiffOn ℝ 1 (f i) (Icc a b))
    (hnonneg : ∀ i t, t ∈ Icc a b → 0 ≤ f i t)
    (hstart : ∀ i, f i a ≤ C)
    (hderiv : ∀ i t, t ∈ Ioo a b → deriv (f i) t ≤ L * (finiteFamilyMaximum f t) ^ 3)
    (hsmall : 16 * L * C ^ 2 * (b - a) ≤ 1) :
    ∀ t ∈ Icc a b, ∀ i, f i t ≤ 2 * C :=
  finite_family_cubic_bootstrap f hC hL (fun i ↦ (hC1 i).continuousOn)
    (fun i ↦ (hC1 i).differentiableOn_one.mono Ioo_subset_Icc_self)
    hnonneg hstart hderiv hsmall

/-- Explicit source-style short interval: b-a<=1/(16LC²). The case L=0
is already covered by the product-form theorem above without division. -/
theorem finite_family_cubic_bootstrap_short_interval {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b C L : ℝ} (hC : 0 < C) (hL : 0 < L)
    (hC1 : ∀ i, ContDiffOn ℝ 1 (f i) (Icc a b))
    (hnonneg : ∀ i t, t ∈ Icc a b → 0 ≤ f i t)
    (hstart : ∀ i, f i a ≤ C)
    (hderiv : ∀ i t, t ∈ Ioo a b → deriv (f i) t ≤ L * (finiteFamilyMaximum f t) ^ 3)
    (hsmall : b - a ≤ 1 / (16 * L * C ^ 2)) :
    ∀ t ∈ Icc a b, ∀ i, f i t ≤ 2 * C := by
  apply finite_family_cubic_bootstrap_of_contDiffOn f hC hL.le hC1 hnonneg hstart hderiv
  have h := (le_div_iff₀ (show 0 < 16 * L * C ^ 2 by positivity)).mp hsmall
  nlinarith

end NearCritical
