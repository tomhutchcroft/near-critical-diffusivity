module
public import NearCritical.CountableBK

/-! Concrete BK bounds for four and five events in the Section 8 diagrams, with
finite-forcing occurrence at every nesting level. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

def diagramOccurrence4 {E : Type*} (A B C D : Set (E → Bool)) : Set (E → Bool) :=
  {ω | DisjointOccurrence A {θ | DisjointOccurrence B {η | DisjointOccurrence C D η} θ} ω}

def diagramOccurrence5 {E : Type*} (A B C D F : Set (E → Bool)) : Set (E → Bool) :=
  {ω | DisjointOccurrence A (diagramOccurrence4 B C D F) ω}

/-- Fixing the union forces disjoint occurrence regardless of all outside
coordinates. This permits recursive grouping of concrete path certificates. -/
theorem forcesOn_disjointOccurrence_union {E : Type*} {A B : Set (E → Bool)}
    {ω : E → Bool} {F G : Set E} (hFfin : F.Finite) (hGfin : G.Finite)
    (hFG : Disjoint F G) (hF : ForcesOn A ω F) (hG : ForcesOn B ω G) :
    ForcesOn {η | DisjointOccurrence A B η} ω (F ∪ G) := by
  intro θ hθ
  refine ⟨F,G,hFfin,hGfin,hFG,?_,?_⟩
  · intro η hη
    exact hF η (fun e he => (hη e he).trans (hθ e (Or.inl he)))
  · intro η hη
    exact hG η (fun e he => (hη e he).trans (hθ e (Or.inr he)))

private lemma increasing_DO {E : Type*} {A B : Set (E → Bool)}
    (hA : BK.Increasing A) (hB : BK.Increasing B) :
    BK.Increasing {ω | DisjointOccurrence A B ω} := by
  intro ω η h hω
  obtain ⟨F,G,hFfin,hGfin,hdis,hF,hG,hAF,hBG⟩ :=
    BK.openDisjointOccurrence_of_disjointOccurrence hω
  exact BK.OpenDisjointOccurrence.to_disjointOccurrence
    ⟨F,G,hFfin,hGfin,hdis,(fun e he => h e (hF e he)),
      (fun e he => h e (hG e he)),hAF,hBG⟩ hA hB

private lemma increasing_four {E : Type*} {A B C D : Set (E → Bool)}
    (hA : BK.Increasing A) (hB : BK.Increasing B)
    (hC : BK.Increasing C) (hD : BK.Increasing D) :
    BK.Increasing (diagramOccurrence4 A B C D) :=
  increasing_DO hA (increasing_DO hB (increasing_DO hC hD))

/-- Repeated proved BK under the actual percolation law; no product-bound
or independence premise is supplied. -/
theorem diagramOccurrence4_probability_le {d : ℕ} (p : unitInterval)
    (A B C D : Set (Configuration d)) (hA : BK.Increasing A) (hB : BK.Increasing B)
    (hC : BK.Increasing C) (hD : BK.Increasing D) :
    (percolation d p).real (diagramOccurrence4 A B C D) ≤
      (percolation d p).real A * (percolation d p).real B *
        (percolation d p).real C * (percolation d p).real D := by
  let CD := {ω : Configuration d | DisjointOccurrence C D ω}
  let BCD := {ω : Configuration d | DisjointOccurrence B CD ω}
  have hCD : BK.Increasing CD := increasing_DO hC hD
  have hBCD : BK.Increasing BCD := increasing_DO hB hCD
  calc
    _ ≤ (percolation d p).real A * (percolation d p).real BCD :=
      percolation_bk d p A BCD hA hBCD
    _ ≤ (percolation d p).real A *
        ((percolation d p).real B * (percolation d p).real CD) :=
      mul_le_mul_of_nonneg_left (percolation_bk d p B CD hB hCD) measureReal_nonneg
    _ ≤ (percolation d p).real A *
        ((percolation d p).real B * ((percolation d p).real C * (percolation d p).real D)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (percolation_bk d p C D hC hD) measureReal_nonneg) measureReal_nonneg
    _ = _ := by ring

theorem diagramOccurrence5_probability_le {d : ℕ} (p : unitInterval)
    (A B C D F : Set (Configuration d)) (hA : BK.Increasing A) (hB : BK.Increasing B)
    (hC : BK.Increasing C) (hD : BK.Increasing D) (hF : BK.Increasing F) :
    (percolation d p).real (diagramOccurrence5 A B C D F) ≤
      (percolation d p).real A * (percolation d p).real B *
        (percolation d p).real C * (percolation d p).real D * (percolation d p).real F := by
  calc
    _ ≤ (percolation d p).real A * (percolation d p).real (diagramOccurrence4 B C D F) :=
      percolation_bk d p A (diagramOccurrence4 B C D F) hA (increasing_four hB hC hD hF)
    _ ≤ (percolation d p).real A * ((percolation d p).real B * (percolation d p).real C *
        (percolation d p).real D * (percolation d p).real F) :=
      mul_le_mul_of_nonneg_left (diagramOccurrence4_probability_le p B C D F hB hC hD hF) measureReal_nonneg
    _ = _ := by ring

end NearCritical.Section8
