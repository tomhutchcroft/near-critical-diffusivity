module

public import NearCritical.ExternalExposureCompleteness
public import NearCritical.RectangleBoundary

/-!
Incident-union counting adapted from openai/math4eaee875,
CriticalPercolation/Exploration/IncidenceDegree.lean, incident_card_le;
Apache-2.0 license retained in third_party/openai-math. The adapted argument
uses actual bond indices and finite unions instead of the modular graph API.
Combined with imported ExactExposure.compile_reads_incident and reads_nodup.
 This is a deterministic cost bound, not an expectation
or stopped-KL theorem.
-/
@[expose] public section
noncomputable section
namespace NearCritical.External
open OAI.CriticalPercolation Finset
open scoped Classical

/-- The positive and negative bonds incident to one lattice vertex. -/
def vertexIncidentBonds {d : ℕ} (x : Vertex d) : Finset (Bond d) :=
  (univ.image (fun i : Fin d => (x, i))) ∪
    (univ.image (fun i : Fin d => (bondPredecessor x i, i)))

lemma mem_vertexIncidentBonds {d : ℕ} (x : Vertex d) (e : Bond d) :
    e ∈ vertexIncidentBonds x ↔ e.1 = x ∨ bondTip e = x := by
  constructor
  · intro he
    rcases mem_union.mp he with he | he
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      exact Or.inl rfl
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      exact Or.inr (bondTip_predecessor x i)
  · rintro (hbase | htip)
    · apply mem_union.mpr
      exact Or.inl (mem_image.mpr ⟨e.2, mem_univ _, by cases e; simpa using hbase.symm⟩)
    · apply mem_union.mpr
      refine Or.inr (mem_image.mpr ⟨e.2, mem_univ _, ?_⟩)
      have hpred := predecessor_bondTip e
      rw [htip] at hpred
      exact Prod.ext hpred rfl

lemma card_vertexIncidentBonds_le {d : ℕ} (x : Vertex d) :
    (vertexIncidentBonds x).card ≤ 2 * d := by
  calc
    _ ≤ (univ.image (fun i : Fin d => (x, i))).card +
        (univ.image (fun i : Fin d => (bondPredecessor x i, i))).card := card_union_le _ _
    _ ≤ (univ : Finset (Fin d)).card + (univ : Finset (Fin d)).card :=
      Nat.add_le_add card_image_le card_image_le
    _ = 2 * d := by simp [two_mul]

/-- A nonrepeating list of actual bond queries incident to C costs at most
2d times the number of vertices in C. -/
theorem bond_queries_length_le {d : ℕ} (D : Finset (Bond d))
    (queries : List D) (C : Finset (Vertex d)) (hn : queries.Nodup)
    (hi : ∀ e ∈ queries, e.val.1 ∈ C ∨ bondTip e.val ∈ C) :
    queries.length ≤ C.card * (2 * d) := by
  have hsub : queries.toFinset.image Subtype.val ⊆ C.biUnion vertexIncidentBonds := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    rcases hi q (List.mem_toFinset.mp hq) with hb | ht
    · exact mem_biUnion.mpr ⟨q.val.1, hb, (mem_vertexIncidentBonds _ _).mpr (Or.inl rfl)⟩
    · exact mem_biUnion.mpr ⟨bondTip q.val, ht,
        (mem_vertexIncidentBonds _ _).mpr (Or.inr rfl)⟩
  calc
    queries.length = (queries.toFinset.image Subtype.val).card := by
      rw [card_image_of_injective _ Subtype.val_injective, List.toFinset_card_of_nodup hn]
    _ ≤ (C.biUnion vertexIncidentBonds).card := card_le_card hsub
    _ ≤ ∑ v ∈ C, (vertexIncidentBonds v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ C, 2 * d := sum_le_sum (fun v _ => card_vertexIncidentBonds_le v)
    _ = C.card * (2 * d) := by simp

/-- Imported exact exposure costs at most 2d queries per reached vertex, for
any finite bond domain and fuel. -/
theorem finite_exposure_query_cost {d : ℕ} (D : Finset (Bond d))
    (x : Vertex d) (n : ℕ) (ω : Configuration d) :
    let tree := ExactExposure.compile (finiteBondSearchGraph D) n (rootExposureState D x)
    (tree.reads (fun e => ω e.val)).length ≤
      (tree.run (fun e => ω e.val)).reached.card * (2 * d) := by
  apply bond_queries_length_le
  · exact finite_exposure_no_repeats D x n ω
  · intro e he
    have hc : ExactExposure.Consistent (finiteBondSearchGraph D)
        (rootExposureState D x) (fun e => ω e.val) := by
      simp [ExactExposure.Consistent, rootExposureState]
    have hs : ExactExposure.Sound (finiteBondSearchGraph D) Set.univ
        (rootExposureState D x) (fun e => ω e.val) := by
      intro v _
      exact ⟨v, Set.mem_univ v, .refl v⟩
    obtain ⟨v, hv, hve⟩ := ExactExposure.compile_reads_incident
      (finiteBondSearchGraph D) n (rootExposureState D x) (fun e => ω e.val) hc hs e he
    have hends : v = e.val.1 ∨ v = bondTip e.val := Sym2.mem_iff.mp hve
    rcases hends with hb | ht
    · exact Or.inl (hb ▸ hv)
    · exact Or.inr (ht ▸ hv)

end NearCritical.External
