module

public import NearCritical.DisjointOccurrence
public import NearCritical.FiniteExpectation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Finite Bernoulli BK inequality. Disjoint occurrence is the existing universal
finite-coordinate forcing definition. The initial probability theorem covers
0 <= p <= 1/2; extension to all p remains a separate stage. -/
@[expose] public section
noncomputable section
namespace NearCritical
namespace BK
open Set Finset
open scoped Classical

/-- Coordinatewise inclusion of the open coordinates. -/
def ConfigLE {E : Type*} (η θ : E → Bool) : Prop := ∀ e, η e = true → θ e = true

def Increasing {E : Type*} (A : Set (E → Bool)) : Prop :=
  ∀ ⦃η θ⦄, ConfigLE η θ → η ∈ A → θ ∈ A

/-- The configuration opening exactly F. -/
def openMask {E : Type*} (F : Set E) (e : E) : Bool := by
  classical
  exact if e ∈ F then true else false

@[simp] lemma openMask_eq_true {E : Type*} (F : Set E) (e : E) :
    openMask F e = true ↔ e ∈ F := by
  classical
  simp [openMask]

/-- Increasing-event certificates consisting entirely of open coordinates. -/
def OpenDisjointOccurrence {E : Type*} (A B : Set (E → Bool)) (η : E → Bool) : Prop :=
  ∃ F H : Set E, F.Finite ∧ H.Finite ∧ Disjoint F H ∧
    (∀ e ∈ F, η e = true) ∧ (∀ e ∈ H, η e = true) ∧ openMask F ∈ A ∧ openMask H ∈ B

lemma openMask_openCertificate {E : Type*} (η : E → Bool) (F : Set E) :
    openMask (Network.openCertificate η F) = Network.certificateConfiguration η F := by
  classical
  funext e
  by_cases he : e ∈ F <;> cases hη : η e <;>
    simp [openMask, Network.openCertificate, Network.certificateConfiguration, he, hη]

lemma openDisjointOccurrence_of_disjointOccurrence {E : Type*} {A B : Set (E → Bool)}
    {η : E → Bool} (h : DisjointOccurrence A B η) : OpenDisjointOccurrence A B η := by
  classical
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH⟩ := h
  refine ⟨Network.openCertificate η F, Network.openCertificate η H,
    hFinF.subset (fun e he ↦ he.1), hFinH.subset (fun e he ↦ he.1), ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun e heF heH ↦ Set.disjoint_left.mp hdisj heF.1 heH.1)
  · exact fun e he ↦ he.2
  · exact fun e he ↦ he.2
  · rw [openMask_openCertificate]
    exact hF _ (fun e he ↦ by simp [Network.certificateConfiguration, he])
  · rw [openMask_openCertificate]
    exact hH _ (fun e he ↦ by simp [Network.certificateConfiguration, he])

lemma OpenDisjointOccurrence.to_disjointOccurrence {E : Type*} {A B : Set (E → Bool)}
    {η : E → Bool} (h : OpenDisjointOccurrence A B η) (hA : Increasing A) (hB : Increasing B) :
    DisjointOccurrence A B η := by
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hAF, hBH⟩ := h
  refine ⟨F, H, hFinF, hFinH, hdisj, ?_, ?_⟩
  · intro θ hagree
    apply hA _ hAF
    intro e he
    have heF := (openMask_eq_true F e).mp he
    exact (hagree e heF).trans (hF e heF)
  · intro θ hagree
    apply hB _ hBH
    intro e he
    have heH := (openMask_eq_true H e).mp he
    exact (hagree e heH).trans (hH e heH)

lemma disjointOccurrence_iff_open {E : Type*} {A B : Set (E → Bool)}
    (hA : Increasing A) (hB : Increasing B) (η : E → Bool) :
    DisjointOccurrence A B η ↔ OpenDisjointOccurrence A B η :=
  ⟨openDisjointOccurrence_of_disjointOccurrence, fun h ↦ h.to_disjointOccurrence hA hB⟩

lemma disjointOccurrence_mono {E : Type*} {A B C D : Set (E → Bool)}
    (hAC : A ⊆ C) (hBD : B ⊆ D) {η : E → Bool} (h : DisjointOccurrence A B η) :
    DisjointOccurrence C D η := by
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH⟩ := h
  exact ⟨F, H, hFinF, hFinH, hdisj,
    fun θ hagree ↦ hAC (hF θ hagree), fun θ hagree ↦ hBD (hH θ hagree)⟩

/-- Split off one Bernoulli coordinate. -/
def extend {E : Type*} (b : Bool) (η : E → Bool) : Option E → Bool
  | none => b
  | some e => η e

def sectionEvent {E : Type*} (A : Set (Option E → Bool)) (b : Bool) : Set (E → Bool) :=
  {η | extend b η ∈ A}

lemma increasing_section {E : Type*} {A : Set (Option E → Bool)} (hA : Increasing A) (b : Bool) :
    Increasing (sectionEvent A b) := by
  intro η θ hηθ hη
  apply hA _ hη
  intro e he
  cases e with
  | none => exact he
  | some e => exact hηθ e he

lemma section_false_subset_true {E : Type*} {A : Set (Option E → Bool)} (hA : Increasing A) :
    sectionEvent A false ⊆ sectionEvent A true := by
  intro η hη
  apply hA _ hη
  intro e he
  cases e with
  | none => rfl
  | some e => exact he

lemma section_subset_true {E : Type*} {A : Set (Option E → Bool)} (hA : Increasing A) (b : Bool) :
    sectionEvent A b ⊆ sectionEvent A true := by
  cases b
  · exact section_false_subset_true hA
  · exact Set.Subset.rfl

def tailSet {E : Type*} (F : Set (Option E)) : Set E := Option.some ⁻¹' F

lemma tailSet_finite {E : Type*} {F : Set (Option E)} (hF : F.Finite) : (tailSet F).Finite :=
  Set.Finite.preimage (Option.some_injective E).injOn hF

lemma openMask_decompose {E : Type*} (F : Set (Option E)) :
    openMask F = extend (openMask F none) (openMask (tailSet F)) := by
  classical
  funext e
  cases e <;> rfl

lemma openDisjointOccurrence_sections {E : Type*} {A B : Set (Option E → Bool)}
    {b : Bool} {η : E → Bool} {F H : Set (Option E)}
    (hFinF : F.Finite) (hFinH : H.Finite) (hdisj : Disjoint F H)
    (hF : ∀ e ∈ F, extend b η e = true) (hH : ∀ e ∈ H, extend b η e = true)
    (hAF : openMask F ∈ A) (hBH : openMask H ∈ B) :
    OpenDisjointOccurrence (sectionEvent A (openMask F none))
      (sectionEvent B (openMask H none)) η := by
  refine ⟨tailSet F, tailSet H, tailSet_finite hFinF, tailSet_finite hFinH, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun e heF heH ↦ Set.disjoint_left.mp hdisj heF heH)
  · exact fun e he ↦ hF (some e) he
  · exact fun e he ↦ hH (some e) he
  · change extend _ _ ∈ A
    rw [← openMask_decompose]
    exact hAF
  · change extend _ _ ∈ B
    rw [← openMask_decompose]
    exact hBH

lemma openMask_some_image {E : Type*} (F : Set E) :
    openMask (Option.some '' F) = extend false (openMask F) := by
  classical
  funext e
  cases e <;> simp [openMask, extend]

lemma disjointOccurrence_section_false_iff {E : Type*} {A B : Set (Option E → Bool)}
    (hA : Increasing A) (hB : Increasing B) (η : E → Bool) :
    DisjointOccurrence A B (extend false η) ↔
      DisjointOccurrence (sectionEvent A false) (sectionEvent B false) η := by
  classical
  constructor
  · intro h
    obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hAF, hBH⟩ := openDisjointOccurrence_of_disjointOccurrence h
    have hnF : none ∉ F := by intro he; simpa [extend] using hF none he
    have hnH : none ∉ H := by intro he; simpa [extend] using hH none he
    have hsec := openDisjointOccurrence_sections hFinF hFinH hdisj hF hH hAF hBH
    have hbF : openMask F none = false := by simp [openMask, hnF]
    have hbH : openMask H none = false := by simp [openMask, hnH]
    rw [hbF, hbH] at hsec
    exact hsec.to_disjointOccurrence (increasing_section hA false) (increasing_section hB false)
  · intro h
    obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hAF, hBH⟩ := openDisjointOccurrence_of_disjointOccurrence h
    have hopen : OpenDisjointOccurrence A B (extend false η) := by
      refine ⟨Option.some '' F, Option.some '' H, hFinF.image _, hFinH.image _, ?_, ?_, ?_, ?_, ?_⟩
      · apply Set.disjoint_left.mpr
        rintro e ⟨f, hf, rfl⟩ ⟨g, hg, heq⟩
        have hfg : g = f := Option.some_injective E heq
        exact Set.disjoint_left.mp hdisj hf (hfg ▸ hg)
      · rintro e ⟨f, hf, rfl⟩
        exact hF f hf
      · rintro e ⟨f, hf, rfl⟩
        exact hH f hf
      · rw [openMask_some_image]
        exact hAF
      · rw [openMask_some_image]
        exact hBH
    exact hopen.to_disjointOccurrence hA hB

lemma disjointOccurrence_section_true_subset {E : Type*} {A B : Set (Option E → Bool)}
    (hA : Increasing A) (hB : Increasing B) {η : E → Bool}
    (h : DisjointOccurrence A B (extend true η)) :
    DisjointOccurrence (sectionEvent A true) (sectionEvent B false) η ∨
      DisjointOccurrence (sectionEvent A false) (sectionEvent B true) η := by
  classical
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hAF, hBH⟩ := openDisjointOccurrence_of_disjointOccurrence h
  have hsec := (openDisjointOccurrence_sections hFinF hFinH hdisj hF hH hAF hBH).to_disjointOccurrence
    (increasing_section hA _) (increasing_section hB _)
  by_cases hnF : none ∈ F
  · have hnH : none ∉ H := fun hnH ↦ Set.disjoint_left.mp hdisj hnF hnH
    have hbF : openMask F none = true := by simp [openMask, hnF]
    have hbH : openMask H none = false := by simp [openMask, hnH]
    rw [hbF, hbH] at hsec
    exact Or.inl hsec
  · have hbF : openMask F none = false := by simp [openMask, hnF]
    rw [hbF] at hsec
    exact Or.inr (disjointOccurrence_mono Set.Subset.rfl (section_subset_true hB _) hsec)

/-- Probability of a finite-coordinate event, using the explicit Bernoulli sum. -/
def eventProbability {E : Type*} [Fintype E] (p : ℝ) (A : Set (E → Bool)) : ℝ := by
  classical
  exact finiteExpectation p (fun η ↦ if η ∈ A then 1 else 0)

def occurrenceEvent {E : Type*} (A B : Set (E → Bool)) : Set (E → Bool) :=
  {η | DisjointOccurrence A B η}

lemma eventProbability_mono {E : Type*} [Fintype E] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {A B : Set (E → Bool)} (hAB : A ⊆ B) :
    eventProbability p A ≤ eventProbability p B := by
  classical
  apply Finset.sum_le_sum
  intro η _
  apply mul_le_mul_of_nonneg_right
  · by_cases hη : η ∈ A
    · simp [hη, hAB hη]
    · simp only [ite_eq_right hη]
      split <;> norm_num
  · apply Finset.prod_nonneg
    intro e _
    split <;> linarith

def optionConfigEquiv (E : Type*) : (Option E → Bool) ≃ Bool × (E → Bool) where
  toFun η := (η none, fun e ↦ η (some e))
  invFun η := extend η.1 η.2
  left_inv η := by funext e; cases e <;> rfl
  right_inv η := by cases η; rfl

lemma sum_configs_option {E : Type*} [Fintype E] (f : (Option E → Bool) → ℝ) :
    (∑ η : Option E → Bool, f η) = ∑ b : Bool, ∑ η : E → Bool, f (extend b η) := by
  classical
  have h := ((optionConfigEquiv E).symm.sum_comp f).symm
  simp only [Fintype.sum_prod_type] at h
  convert! h using 1

lemma weight_extend {E : Type*} [Fintype E] (p : ℝ) (b : Bool) (η : E → Bool) :
    (∏ e : Option E, if extend b η e then p else 1 - p) =
      (if b then p else 1 - p) * ∏ e : E, if η e then p else 1 - p := by
  classical
  rw [univ_option, Finset.prod_insertNone]
  rfl

lemma finiteExpectation_option {E : Type*} [Fintype E] (p : ℝ)
    (f : (Option E → Bool) → ℝ) :
    finiteExpectation p f =
      (1 - p) * finiteExpectation p (fun η ↦ f (extend false η)) +
        p * finiteExpectation p (fun η ↦ f (extend true η)) := by
  classical
  calc
    _ = ∑ b : Bool, ∑ η : E → Bool,
        f (extend b η) * ∏ e : Option E, if extend b η e then p else 1 - p := by
      unfold finiteExpectation
      convert! sum_configs_option (E := E)
        (fun ω ↦ f ω * ∏ e : Option E, if ω e then p else 1 - p) using 1
      apply Finset.sum_congr (by ext η; simp)
      intro η _
      apply congrArg (fun z : ℝ ↦ f η * z)
      apply Finset.prod_congr (by ext e; simp)
      intro e _
      rfl
    _ = ∑ b : Bool, (if b then p else 1 - p) *
        finiteExpectation p (fun η : E → Bool ↦ f (extend b η)) := by
      apply Finset.sum_congr rfl
      intro b _
      unfold finiteExpectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      rw [weight_extend]
      ring
    _ = _ := by
      simp [Fintype.univ_bool]
      ring

lemma eventProbability_option {E : Type*} [Fintype E] (p : ℝ) (A : Set (Option E → Bool)) :
    eventProbability p A = (1 - p) * eventProbability p (sectionEvent A false) +
      p * eventProbability p (sectionEvent A true) := by
  classical
  exact finiteExpectation_option p (fun η ↦ if η ∈ A then 1 else 0)

lemma occurrence_section_indicator_bound {E : Type*} {A B : Set (Option E → Bool)}
    (hA : Increasing A) (hB : Increasing B) (η : E → Bool) :
    (if DisjointOccurrence A B (extend true η) then (1 : ℝ) else 0) ≤
      (if DisjointOccurrence (sectionEvent A true) (sectionEvent B false) η then 1 else 0) +
      (if DisjointOccurrence (sectionEvent A false) (sectionEvent B true) η then 1 else 0) -
      (if DisjointOccurrence (sectionEvent A false) (sectionEvent B false) η then 1 else 0) := by
  classical
  by_cases h0 : DisjointOccurrence (sectionEvent A false) (sectionEvent B false) η
  · have h10 := disjointOccurrence_mono (section_false_subset_true hA) Set.Subset.rfl h0
    have h01 := disjointOccurrence_mono Set.Subset.rfl (section_false_subset_true hB) h0
    simp only [ite_eq_left h0, ite_eq_left h10, ite_eq_left h01]
    split <;> norm_num
  · simp only [ite_eq_right h0, sub_zero]
    by_cases h1 : DisjointOccurrence A B (extend true η)
    · have hcases := disjointOccurrence_section_true_subset hA hB h1
      rcases hcases with h10 | h01
      · simp only [ite_eq_left h1, ite_eq_left h10]
        split <;> norm_num
      · simp only [ite_eq_left h1, ite_eq_left h01]
        split <;> norm_num
    · simp only [ite_eq_right h1]
      split <;> split <;> norm_num

lemma occurrence_section_probability_bound {E : Type*} [Fintype E] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {A B : Set (Option E → Bool)}
    (hA : Increasing A) (hB : Increasing B) :
    eventProbability p (sectionEvent (occurrenceEvent A B) true) ≤
      eventProbability p (occurrenceEvent (sectionEvent A true) (sectionEvent B false)) +
      eventProbability p (occurrenceEvent (sectionEvent A false) (sectionEvent B true)) -
      eventProbability p (occurrenceEvent (sectionEvent A false) (sectionEvent B false)) := by
  classical
  calc
    _ ≤ ∑ η : E → Bool,
        ((if DisjointOccurrence (sectionEvent A true) (sectionEvent B false) η then 1 else 0) +
        (if DisjointOccurrence (sectionEvent A false) (sectionEvent B true) η then 1 else 0) -
        (if DisjointOccurrence (sectionEvent A false) (sectionEvent B false) η then 1 else 0)) *
        ∏ e, if η e then p else 1 - p := by
      apply Finset.sum_le_sum
      intro η _
      apply mul_le_mul_of_nonneg_right (occurrence_section_indicator_bound hA hB η)
      apply Finset.prod_nonneg
      intro e _
      split <;> linarith
    _ = _ := by
      simp only [eventProbability, finiteExpectation, occurrenceEvent, mem_ofPred_eq,
        add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      convert! rfl

lemma eventProbability_occurrence_option {E : Type*} [Fintype E] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {A B : Set (Option E → Bool)}
    (hA : Increasing A) (hB : Increasing B) :
    eventProbability p (occurrenceEvent A B) ≤
      (1 - 2 * p) * eventProbability p (occurrenceEvent (sectionEvent A false) (sectionEvent B false)) +
        p * (eventProbability p (occurrenceEvent (sectionEvent A true) (sectionEvent B false)) +
          eventProbability p (occurrenceEvent (sectionEvent A false) (sectionEvent B true))) := by
  have h0 : sectionEvent (occurrenceEvent A B) false =
      occurrenceEvent (sectionEvent A false) (sectionEvent B false) := by
    ext η
    exact disjointOccurrence_section_false_iff hA hB η
  rw [eventProbability_option, h0]
  have hbound := mul_le_mul_of_nonneg_left (occurrence_section_probability_bound hp hp1 hA hB) hp
  calc
    _ ≤ (1 - p) * eventProbability p (occurrenceEvent (sectionEvent A false) (sectionEvent B false)) +
        p * (eventProbability p (occurrenceEvent (sectionEvent A true) (sectionEvent B false)) +
        eventProbability p (occurrenceEvent (sectionEvent A false) (sectionEvent B true)) -
        eventProbability p (occurrenceEvent (sectionEvent A false) (sectionEvent B false))) :=
      by linarith [hbound]
    _ = _ := by ring

lemma bk_step_arithmetic {p a0 a1 b0 b1 : ℝ} (ha : a0 ≤ a1) (hb : b0 ≤ b1) :
    (1 - 2 * p) * (a0 * b0) + p * (a1 * b0 + a0 * b1) ≤
      ((1 - p) * a0 + p * a1) * ((1 - p) * b0 + p * b1) := by
  have h := mul_nonneg (sq_nonneg p) (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb))
  nlinarith

/-- The low-density BK assertion. The p<=1/2 restriction is explicit. -/
def LowDensityBK (E : Type*) [Fintype E] : Prop :=
  ∀ p : ℝ, 0 ≤ p → p ≤ 1 / 2 → ∀ A B : Set (E → Bool), Increasing A → Increasing B →
    eventProbability p (occurrenceEvent A B) ≤ eventProbability p A * eventProbability p B

lemma lowDensityBK_option {E : Type*} [Fintype E] (hBK : LowDensityBK E) : LowDensityBK (Option E) := by
  intro p hp hpHalf A B hA hB
  have hp1 : p ≤ 1 := by linarith
  have h00 := hBK p hp hpHalf (sectionEvent A false) (sectionEvent B false)
    (increasing_section hA false) (increasing_section hB false)
  have h10 := hBK p hp hpHalf (sectionEvent A true) (sectionEvent B false)
    (increasing_section hA true) (increasing_section hB false)
  have h01 := hBK p hp hpHalf (sectionEvent A false) (sectionEvent B true)
    (increasing_section hA false) (increasing_section hB true)
  have hc : 0 ≤ 1 - 2 * p := by linarith
  have hrec := eventProbability_occurrence_option hp hp1 hA hB
  have hfirst : eventProbability p (occurrenceEvent A B) ≤
      (1 - 2 * p) * (eventProbability p (sectionEvent A false) * eventProbability p (sectionEvent B false)) +
      p * (eventProbability p (sectionEvent A true) * eventProbability p (sectionEvent B false) +
        eventProbability p (sectionEvent A false) * eventProbability p (sectionEvent B true)) := by
    apply hrec.trans
    have hm00 := mul_le_mul_of_nonneg_left h00 hc
    have hm10 := mul_le_mul_of_nonneg_left h10 hp
    have hm01 := mul_le_mul_of_nonneg_left h01 hp
    nlinarith
  have ha := eventProbability_mono hp hp1 (section_false_subset_true hA)
  have hb := eventProbability_mono hp hp1 (section_false_subset_true hB)
  rw [eventProbability_option p A, eventProbability_option p B]
  exact hfirst.trans (bk_step_arithmetic ha hb)

/-- Reindex configurations along a bijection of coordinate types. -/
def coordinateEquiv {E F : Type*} (e : E ≃ F) : (E → Bool) ≃ (F → Bool) where
  toFun η := fun f ↦ η (e.symm f)
  invFun θ := fun a ↦ θ (e a)
  left_inv η := by funext a; simp
  right_inv θ := by funext f; simp

def pullEvent {E F : Type*} (e : E ≃ F) (A : Set (F → Bool)) : Set (E → Bool) :=
  {η | coordinateEquiv e η ∈ A}

lemma increasing_pullEvent {E F : Type*} (e : E ≃ F) {A : Set (F → Bool)}
    (hA : Increasing A) : Increasing (pullEvent e A) := by
  intro η θ hηθ hη
  apply hA _ hη
  intro f hf
  exact hηθ (e.symm f) hf

lemma disjointOccurrence_pullEvent_iff {E F : Type*} (e : E ≃ F)
    (A B : Set (F → Bool)) (η : E → Bool) :
    DisjointOccurrence (pullEvent e A) (pullEvent e B) η ↔
      DisjointOccurrence A B (coordinateEquiv e η) := by
  constructor
  · rintro ⟨K, L, hFinK, hFinL, hdisj, hK, hL⟩
    refine ⟨e '' K, e '' L, hFinK.image _, hFinL.image _, ?_, ?_, ?_⟩
    · apply Set.disjoint_left.mpr
      rintro f ⟨k, hk, rfl⟩ ⟨l, hl, hel⟩
      exact Set.disjoint_left.mp hdisj hk (e.injective hel ▸ hl)
    · intro θ hagree
      have hθ := hK ((coordinateEquiv e).symm θ) (by
        intro a ha
        have h := hagree (e a) ⟨a, ha, rfl⟩
        simpa [coordinateEquiv] using h)
      change coordinateEquiv e ((coordinateEquiv e).symm θ) ∈ A at hθ
      simpa only [Equiv.apply_symm_apply] using hθ
    · intro θ hagree
      have hθ := hL ((coordinateEquiv e).symm θ) (by
        intro a ha
        have h := hagree (e a) ⟨a, ha, rfl⟩
        simpa [coordinateEquiv] using h)
      change coordinateEquiv e ((coordinateEquiv e).symm θ) ∈ B at hθ
      simpa only [Equiv.apply_symm_apply] using hθ
  · rintro ⟨K, L, hFinK, hFinL, hdisj, hK, hL⟩
    refine ⟨e ⁻¹' K, e ⁻¹' L,
      Set.Finite.preimage e.injective.injOn hFinK,
      Set.Finite.preimage e.injective.injOn hFinL, ?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr (fun a haK haL ↦ Set.disjoint_left.mp hdisj haK haL)
    · intro θ hagree
      apply hK (coordinateEquiv e θ)
      intro f hf
      change θ (e.symm f) = η (e.symm f)
      apply hagree
      change e (e.symm f) ∈ K
      simpa only [Equiv.apply_symm_apply] using hf
    · intro θ hagree
      apply hL (coordinateEquiv e θ)
      intro f hf
      change θ (e.symm f) = η (e.symm f)
      apply hagree
      change e (e.symm f) ∈ L
      simpa only [Equiv.apply_symm_apply] using hf

lemma eventProbability_pullEvent {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (p : ℝ) (A : Set (F → Bool)) :
    eventProbability p (pullEvent e A) = eventProbability p A := by
  classical
  change (∑ η : E → Bool, (if coordinateEquiv e η ∈ A then 1 else 0) *
    ∏ a : E, if η a then p else 1 - p) =
    ∑ θ : F → Bool, (if θ ∈ A then 1 else 0) * ∏ f : F, if θ f then p else 1 - p
  apply Fintype.sum_equiv (coordinateEquiv e)
  intro η
  congr 1
  exact Fintype.prod_equiv e _ _ (fun a ↦ by simp [coordinateEquiv])

lemma eventProbability_occurrence_pullEvent {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (p : ℝ) (A B : Set (F → Bool)) :
    eventProbability p (occurrenceEvent (pullEvent e A) (pullEvent e B)) =
      eventProbability p (occurrenceEvent A B) := by
  have heq : occurrenceEvent (pullEvent e A) (pullEvent e B) = pullEvent e (occurrenceEvent A B) := by
    ext η
    exact disjointOccurrence_pullEvent_iff e A B η
  rw [heq]
  exact eventProbability_pullEvent e p _

lemma lowDensityBK_equiv {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (hBK : LowDensityBK E) : LowDensityBK F := by
  intro p hp hpHalf A B hA hB
  have h := hBK p hp hpHalf (pullEvent e A) (pullEvent e B)
    (increasing_pullEvent e hA) (increasing_pullEvent e hB)
  rw [eventProbability_occurrence_pullEvent, eventProbability_pullEvent, eventProbability_pullEvent] at h
  exact h

lemma disjointOccurrence_mem {E : Type*} {A B : Set (E → Bool)} {η : E → Bool}
    (h : DisjointOccurrence A B η) : η ∈ A ∧ η ∈ B := by
  obtain ⟨F, H, _, _, _, hF, hH⟩ := h
  exact ⟨hF η (fun _ _ ↦ rfl), hH η (fun _ _ ↦ rfl)⟩

lemma lowDensityBK_empty : LowDensityBK PEmpty := by
  intro p hp hpHalf A B hA hB
  classical
  let η : PEmpty → Bool := fun e ↦ nomatch e
  have hprob (C : Set (PEmpty → Bool)) : eventProbability p C = if η ∈ C then 1 else 0 := by
    unfold eventProbability finiteExpectation
    rw [Finset.sum_eq_single η]
    · simp
    · intro θ _ hθη
      exact False.elim (hθη (by funext e; exact PEmpty.elim e))
    · intro hn
      exact False.elim (hn (by
        apply Finset.mem_singleton.mpr
        funext e
        exact PEmpty.elim e))
  rw [hprob, hprob, hprob]
  by_cases hD : DisjointOccurrence A B η
  · have hm := disjointOccurrence_mem hD
    simp [occurrenceEvent, hD, hm.1, hm.2]
  · by_cases hA' : η ∈ A <;> by_cases hB' : η ∈ B <;>
      simp [occurrenceEvent, hD, hA', hB']

/-- BK for increasing events on any finite Boolean coordinate space, in the
explicit low-density range 0 <= p <= 1/2. The all-p extension is not claimed. -/
theorem lowDensity_bk {E : Type*} [Fintype E] : LowDensityBK E := by
  refine Fintype.induction_empty_option (P := fun α [h : Fintype α] ↦ @LowDensityBK α h)
    ?_ lowDensityBK_empty ?_ E
  · intro α β hβ e hBK
    let : Fintype α := Fintype.ofEquiv β e.symm
    exact lowDensityBK_equiv e hBK
  · intro α hα hBK
    exact lowDensityBK_option hBK

/-- The explicit event sum equals probability under the actual finite Bernoulli
product measure. All events here are measurable because the coordinate space
is finite. -/
theorem eventProbability_eq_measureReal {E : Type*} [Fintype E]
    (p : unitInterval) (A : Set (E → Bool)) :
    eventProbability (p : ℝ) A =
      (MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p)).real A := by
  classical
  have hI := integral_finite_bernoulli p (fun η : E → Bool ↦ if η ∈ A then (1 : ℝ) else 0)
  have hmeas : MeasurableSet A := (Set.toFinite A).measurableSet
  have hμ : (∫ η : E → Bool, (if η ∈ A then (1 : ℝ) else 0)
      ∂(MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p))) =
      (MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p)).real A := by
    convert! MeasureTheory.integral_indicator_one hmeas using 1
  exact hI.symm.trans hμ

/-- BK for the true finite Bernoulli product law in the proved low-density range.
The probability restriction p<=1/2 remains explicit. -/
theorem finite_bernoulli_bk_le_half {E : Type*} [Fintype E]
    (p : unitInterval) (hpHalf : (p : ℝ) ≤ 1 / 2)
    (A B : Set (E → Bool)) (hA : Increasing A) (hB : Increasing B) :
    (MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p)).real
        (occurrenceEvent A B) ≤
      (MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p)).real A *
      (MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p)).real B := by
  have h := lowDensity_bk (E := E) (p : ℝ) p.property.1 hpHalf A B hA hB
  rw [eventProbability_eq_measureReal p, eventProbability_eq_measureReal p,
    eventProbability_eq_measureReal p] at h
  exact h

end BK

namespace Network
open Set
variable {V E : Type*} (G : NearCritical.Network V E)

/-- Ordinary Bernoulli boundary connections are increasing events. -/
lemma boundaryConnectionEvent_increasing (x : V) (A : Set V) :
    BK.Increasing (G.boundaryConnectionEvent x A) := by
  intro η θ hηθ hη
  obtain ⟨z, hz, hpath⟩ := hη
  refine ⟨z, hz, SimpleGraph.Reachable.mono ?_ hpath⟩
  rintro v w ⟨hne, hv, hw, e, he, hends⟩
  have hηe : η e = true := by
    cases h : η e
    · simp [binaryWeights, h] at he
    · rfl
  have hθe := hηθ e hηe
  exact ⟨hne, hv, hw, e, by simp [binaryWeights, hθe], hends⟩

/-- Low-density BK directly for the finite positive-edge connection certificates
used by the geometric two-arm lemmas. -/
theorem disjointBoundaryConnections_probability_le_half [Fintype E]
    (p : unitInterval) (hpHalf : (p : ℝ) ≤ 1 / 2) (x y : V) (A B : Set V) :
    (MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p)).real
        {η | G.DisjointBoundaryConnections (binaryWeights η) x A y B} ≤
      (MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p)).real
        (G.boundaryConnectionEvent x A) *
      (MeasureTheory.Measure.pi (fun _ : E ↦ ProbabilityTheory.bernoulliMeasure true false p)).real
        (G.boundaryConnectionEvent y B) := by
  have heq : {η | G.DisjointBoundaryConnections (binaryWeights η) x A y B} =
      BK.occurrenceEvent (G.boundaryConnectionEvent x A) (G.boundaryConnectionEvent y B) := by
    ext η
    exact G.disjointBoundaryConnections_iff_disjointOccurrence η x y A B
  rw [heq]
  exact BK.finite_bernoulli_bk_le_half p hpHalf _ _
    (G.boundaryConnectionEvent_increasing x A) (G.boundaryConnectionEvent_increasing y B)

end Network
end NearCritical
