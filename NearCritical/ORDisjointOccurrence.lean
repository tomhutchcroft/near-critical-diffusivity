module

public import NearCritical.BK
public import NearCritical.ORProjection

/-! Transport of disjoint finite forcing certificates through an OR refinement.
Each old open coordinate contributes one currently open refined coordinate.
Only the forward inclusion is claimed: expanded disjoint witnesses can use
different bits from a single old group, so a converse is not generally valid. -/
@[expose] public section
noncomputable section
namespace NearCritical.BK
open Set
open scoped Classical

lemma orProject_configLE {E : Type*} (m : ℕ) {ω θ : E × Fin m → Bool}
    (h : ConfigLE ω θ) : ConfigLE (orProject m ω) (orProject m θ) := by
  intro e he
  obtain ⟨j, hj⟩ := (orProject_eq_true m ω e).mp he
  exact (orProject_eq_true m θ e).mpr ⟨j, h (e, j) hj⟩

lemma increasing_preimage_orProject {E : Type*} (m : ℕ) {A : Set (E → Bool)}
    (hA : Increasing A) : Increasing ((orProject m) ⁻¹' A) := by
  intro ω θ hωθ hω
  exact hA (orProject_configLE m hωθ) hω

/-- Disjoint occurrence in the old coordinates supplies disjoint certificates
in the refined coordinates. No nonemptiness assumption on Fin m is needed:
whenever an old witness coordinate exists, its projected bit is open and hence
provides an open refined bit. -/
theorem disjointOccurrence_orProject {E : Type*} (m : ℕ) (ω : E × Fin m → Bool)
    {A B : Set (E → Bool)} (hA : Increasing A) (hB : Increasing B)
    (hD : DisjointOccurrence A B (orProject m ω)) :
    DisjointOccurrence ((orProject m) ⁻¹' A) ((orProject m) ⁻¹' B) ω := by
  classical
  obtain ⟨F, H, hFinF, hFinH, hdisj, hF, hH, hAF, hBH⟩ :=
    openDisjointOccurrence_of_disjointOccurrence hD
  let : Fintype F := hFinF.fintype
  let : Fintype H := hFinH.fintype
  have hexF (e : F) : ∃ j : Fin m, ω (e.val, j) = true :=
    (orProject_eq_true m ω e.val).mp (hF e.val e.property)
  have hexH (e : H) : ∃ j : Fin m, ω (e.val, j) = true :=
    (orProject_eq_true m ω e.val).mp (hH e.val e.property)
  let jF : F → Fin m := fun e ↦ Classical.choose (hexF e)
  let jH : H → Fin m := fun e ↦ Classical.choose (hexH e)
  let FF : Set (E × Fin m) := Set.range (fun e : F ↦ (e.val, jF e))
  let HH : Set (E × Fin m) := Set.range (fun e : H ↦ (e.val, jH e))
  refine ⟨FF, HH, Set.finite_range _, Set.finite_range _, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro z ⟨e, rfl⟩ ⟨f, hef⟩
    have hval : f.val = e.val := congrArg Prod.fst hef
    exact Set.disjoint_left.mp hdisj e.property (hval ▸ f.property)
  · intro θ hagree
    apply hA _ hAF
    intro e he
    have heF : e ∈ F := (openMask_eq_true F e).mp he
    let eF : F := ⟨e, heF⟩
    have hmem : (e, jF eF) ∈ FF := ⟨eF, rfl⟩
    have hopen : θ (e, jF eF) = true :=
      (hagree (e, jF eF) hmem).trans (Classical.choose_spec (hexF eF))
    exact (orProject_eq_true m θ e).mpr ⟨jF eF, hopen⟩
  · intro θ hagree
    apply hB _ hBH
    intro e he
    have heH : e ∈ H := (openMask_eq_true H e).mp he
    let eH : H := ⟨e, heH⟩
    have hmem : (e, jH eH) ∈ HH := ⟨eH, rfl⟩
    have hopen : θ (e, jH eH) = true :=
      (hagree (e, jH eH) hmem).trans (Classical.choose_spec (hexH eH))
    exact (orProject_eq_true m θ e).mpr ⟨jH eH, hopen⟩

/-- The inclusion required for transferring low-density BK to an arbitrary
Bernoulli parameter by an OR block refinement. -/
theorem orProject_preimage_occurrence_subset {E : Type*} (m : ℕ)
    {A B : Set (E → Bool)} (hA : Increasing A) (hB : Increasing B) :
    (orProject m) ⁻¹' occurrenceEvent A B ⊆
      occurrenceEvent ((orProject m) ⁻¹' A) ((orProject m) ⁻¹' B) := by
  intro ω hω
  exact disjointOccurrence_orProject m ω hA hB hω

end NearCritical.BK
