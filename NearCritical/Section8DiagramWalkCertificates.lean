module
public import NearCritical.Section8DiagramBK
public import NearCritical.HalfSpaceArmGeometry

/-! Actual finite open-walk certificates for the nested occurrences appearing
in the Section 8 diagrams. All outside assignments remain unrestricted. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set
open scoped Classical

private lemma walk_forcing_certificate {d : ℕ} {ω : Configuration d}
    {x y : Vertex d} (w : (openGraph ω).Walk x y) (S A : Set (Vertex d))
    (hS : ∀ v ∈ w.support, v ∈ S) (hy : y ∈ A) :
    ∃ F : Finset (Bond d), (∀ e ∈ F, s(e.1,bondTip e) ∈ w.edges) ∧
      ForcesOn (connectionToSetEvent S x A) ω (F : Set (Bond d)) := by
  obtain ⟨F,hopen,hedge,hforce⟩ := openWalk_certificate w S hS
  refine ⟨F,hedge,?_⟩
  intro θ hθ
  obtain ⟨hxS,v,hv,hyS,hxy⟩ := hforce θ (fun e he => (hθ e he).trans (hopen e he))
  have hvy : v = y := hv
  subst v
  exact ⟨hxS,y,hy,hyS,hxy⟩

private lemma certificate_disjoint_of_edges {d : ℕ} {ω : Configuration d}
    {x y z t : Vertex d} (w : (openGraph ω).Walk x y) (q : (openGraph ω).Walk z t)
    (F G : Finset (Bond d)) (hF : ∀ e ∈ F, s(e.1,bondTip e) ∈ w.edges)
    (hG : ∀ e ∈ G, s(e.1,bondTip e) ∈ q.edges) (hdis : w.edges.Disjoint q.edges) :
    Disjoint (F : Set (Bond d)) (G : Set (Bond d)) :=
  Set.disjoint_left.mpr (fun e heF heG => List.disjoint_left.mp hdis (hF e heF) (hG e heG))

private lemma disjoint_union_of {E : Type*} {F G H : Set E}
    (hFG : Disjoint F G) (hFH : Disjoint F H) : Disjoint F (G ∪ H) := by
  apply Set.disjoint_left.mpr
  intro e heF he
  rcases he with heG | heH
  · exact Set.disjoint_left.mp hFG heF heG
  · exact Set.disjoint_left.mp hFH heF heH

/-- Four concrete cross-edge-disjoint walks give the actual nested
finite-forcing occurrence to which repeated BK applies. -/
theorem fourOpenWalks_diagramOccurrence {d : ℕ} {ω : Configuration d}
    {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : Vertex d}
    (w₁ : (openGraph ω).Walk x₁ y₁) (w₂ : (openGraph ω).Walk x₂ y₂)
    (w₃ : (openGraph ω).Walk x₃ y₃) (w₄ : (openGraph ω).Walk x₄ y₄)
    (S A₁ A₂ A₃ A₄ : Set (Vertex d))
    (hS₁ : ∀ v ∈ w₁.support, v ∈ S) (hS₂ : ∀ v ∈ w₂.support, v ∈ S)
    (hS₃ : ∀ v ∈ w₃.support, v ∈ S) (hS₄ : ∀ v ∈ w₄.support, v ∈ S)
    (hy₁ : y₁ ∈ A₁) (hy₂ : y₂ ∈ A₂) (hy₃ : y₃ ∈ A₃) (hy₄ : y₄ ∈ A₄)
    (h₁₂ : w₁.edges.Disjoint w₂.edges) (h₁₃ : w₁.edges.Disjoint w₃.edges)
    (h₁₄ : w₁.edges.Disjoint w₄.edges) (h₂₃ : w₂.edges.Disjoint w₃.edges)
    (h₂₄ : w₂.edges.Disjoint w₄.edges) (h₃₄ : w₃.edges.Disjoint w₄.edges) :
    ω ∈ diagramOccurrence4 (connectionToSetEvent S x₁ A₁) (connectionToSetEvent S x₂ A₂)
      (connectionToSetEvent S x₃ A₃) (connectionToSetEvent S x₄ A₄) := by
  obtain ⟨F₁,he₁,hF₁⟩ := walk_forcing_certificate w₁ S A₁ hS₁ hy₁
  obtain ⟨F₂,he₂,hF₂⟩ := walk_forcing_certificate w₂ S A₂ hS₂ hy₂
  obtain ⟨F₃,he₃,hF₃⟩ := walk_forcing_certificate w₃ S A₃ hS₃ hy₃
  obtain ⟨F₄,he₄,hF₄⟩ := walk_forcing_certificate w₄ S A₄ hS₄ hy₄
  have hF₁₂ := certificate_disjoint_of_edges w₁ w₂ F₁ F₂ he₁ he₂ h₁₂
  have hF₁₃ := certificate_disjoint_of_edges w₁ w₃ F₁ F₃ he₁ he₃ h₁₃
  have hF₁₄ := certificate_disjoint_of_edges w₁ w₄ F₁ F₄ he₁ he₄ h₁₄
  have hF₂₃ := certificate_disjoint_of_edges w₂ w₃ F₂ F₃ he₂ he₃ h₂₃
  have hF₂₄ := certificate_disjoint_of_edges w₂ w₄ F₂ F₄ he₂ he₄ h₂₄
  have hF₃₄ := certificate_disjoint_of_edges w₃ w₄ F₃ F₄ he₃ he₄ h₃₄
  have hF₃₄force := forcesOn_disjointOccurrence_union F₃.finite_toSet F₄.finite_toSet hF₃₄ hF₃ hF₄
  have hF₂₃₄force := forcesOn_disjointOccurrence_union F₂.finite_toSet
    (F₃.finite_toSet.union F₄.finite_toSet) (disjoint_union_of hF₂₃ hF₂₄) hF₂ hF₃₄force
  exact ⟨(F₁ : Set (Bond d)),(F₂ : Set (Bond d)) ∪ ((F₃ : Set (Bond d)) ∪ (F₄ : Set (Bond d))),
    F₁.finite_toSet,F₂.finite_toSet.union (F₃.finite_toSet.union F₄.finite_toSet),
    disjoint_union_of hF₁₂ (disjoint_union_of hF₁₃ hF₁₄),hF₁,hF₂₃₄force⟩

/-- Five actual cross-edge-disjoint walks yield the five-event nested
occurrence, using recursively grouped finite certificates. -/
theorem fiveOpenWalks_diagramOccurrence {d : ℕ} {ω : Configuration d}
    {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ : Vertex d}
    (w₁ : (openGraph ω).Walk x₁ y₁)
    (w₂ : (openGraph ω).Walk x₂ y₂)
    (w₃ : (openGraph ω).Walk x₃ y₃)
    (w₄ : (openGraph ω).Walk x₄ y₄)
    (w₅ : (openGraph ω).Walk x₅ y₅)
    (S A₁ A₂ A₃ A₄ A₅ : Set (Vertex d))
    (hS₁ : ∀ v ∈ w₁.support, v ∈ S) (hy₁ : y₁ ∈ A₁)
    (hS₂ : ∀ v ∈ w₂.support, v ∈ S) (hy₂ : y₂ ∈ A₂)
    (hS₃ : ∀ v ∈ w₃.support, v ∈ S) (hy₃ : y₃ ∈ A₃)
    (hS₄ : ∀ v ∈ w₄.support, v ∈ S) (hy₄ : y₄ ∈ A₄)
    (hS₅ : ∀ v ∈ w₅.support, v ∈ S) (hy₅ : y₅ ∈ A₅)
    (h₁₂ : w₁.edges.Disjoint w₂.edges)
    (h₁₃ : w₁.edges.Disjoint w₃.edges)
    (h₁₄ : w₁.edges.Disjoint w₄.edges)
    (h₁₅ : w₁.edges.Disjoint w₅.edges)
    (h₂₃ : w₂.edges.Disjoint w₃.edges)
    (h₂₄ : w₂.edges.Disjoint w₄.edges)
    (h₂₅ : w₂.edges.Disjoint w₅.edges)
    (h₃₄ : w₃.edges.Disjoint w₄.edges)
    (h₃₅ : w₃.edges.Disjoint w₅.edges)
    (h₄₅ : w₄.edges.Disjoint w₅.edges) :
    ω ∈ diagramOccurrence5 (connectionToSetEvent S x₁ A₁) (connectionToSetEvent S x₂ A₂) (connectionToSetEvent S x₃ A₃) (connectionToSetEvent S x₄ A₄) (connectionToSetEvent S x₅ A₅) := by
  obtain ⟨F₁,he₁,hF₁⟩ := walk_forcing_certificate w₁ S A₁ hS₁ hy₁
  obtain ⟨F₂,he₂,hF₂⟩ := walk_forcing_certificate w₂ S A₂ hS₂ hy₂
  obtain ⟨F₃,he₃,hF₃⟩ := walk_forcing_certificate w₃ S A₃ hS₃ hy₃
  obtain ⟨F₄,he₄,hF₄⟩ := walk_forcing_certificate w₄ S A₄ hS₄ hy₄
  obtain ⟨F₅,he₅,hF₅⟩ := walk_forcing_certificate w₅ S A₅ hS₅ hy₅
  have hF₁₂ := certificate_disjoint_of_edges w₁ w₂ F₁ F₂ he₁ he₂ h₁₂
  have hF₁₃ := certificate_disjoint_of_edges w₁ w₃ F₁ F₃ he₁ he₃ h₁₃
  have hF₁₄ := certificate_disjoint_of_edges w₁ w₄ F₁ F₄ he₁ he₄ h₁₄
  have hF₁₅ := certificate_disjoint_of_edges w₁ w₅ F₁ F₅ he₁ he₅ h₁₅
  have hF₂₃ := certificate_disjoint_of_edges w₂ w₃ F₂ F₃ he₂ he₃ h₂₃
  have hF₂₄ := certificate_disjoint_of_edges w₂ w₄ F₂ F₄ he₂ he₄ h₂₄
  have hF₂₅ := certificate_disjoint_of_edges w₂ w₅ F₂ F₅ he₂ he₅ h₂₅
  have hF₃₄ := certificate_disjoint_of_edges w₃ w₄ F₃ F₄ he₃ he₄ h₃₄
  have hF₃₅ := certificate_disjoint_of_edges w₃ w₅ F₃ F₅ he₃ he₅ h₃₅
  have hF₄₅ := certificate_disjoint_of_edges w₄ w₅ F₄ F₅ he₄ he₅ h₄₅
  have h₄₅force := forcesOn_disjointOccurrence_union F₄.finite_toSet F₅.finite_toSet hF₄₅ hF₄ hF₅
  have h₃₄₅force := forcesOn_disjointOccurrence_union F₃.finite_toSet
    (F₄.finite_toSet.union F₅.finite_toSet) (disjoint_union_of hF₃₄ hF₃₅) hF₃ h₄₅force
  have h₂₃₄₅force := forcesOn_disjointOccurrence_union F₂.finite_toSet
    (F₃.finite_toSet.union (F₄.finite_toSet.union F₅.finite_toSet))
    (disjoint_union_of hF₂₃ (disjoint_union_of hF₂₄ hF₂₅)) hF₂ h₃₄₅force
  exact ⟨(F₁ : Set (Bond d)),(F₂ : Set (Bond d)) ∪ ((F₃ : Set (Bond d)) ∪
    ((F₄ : Set (Bond d)) ∪ (F₅ : Set (Bond d)))),F₁.finite_toSet,
    F₂.finite_toSet.union (F₃.finite_toSet.union (F₄.finite_toSet.union F₅.finite_toSet)),
    disjoint_union_of hF₁₂ (disjoint_union_of hF₁₃ (disjoint_union_of hF₁₄ hF₁₅)),hF₁,h₂₃₄₅force⟩

end NearCritical.Section8
