module

public import NearCritical.ExternalFiniteSearch
public import OAI.Probability.CriticalPercolation.Exploration.QueryTree

/-!
Finite leaf-transcript route to the imported query-tree entropy identity.
Source openai/math4eaee875, Apache-2.0; exact hashes in third_party/openai-math.
The conversion preserves finite search queries, output decoding and validity.
 No actual law/KL identification is asserted yet.
-/
@[expose] public section
namespace NearCritical.External
open OAI.CriticalPercolation

/-- Retain every branch decision of the imported search as a finite leaf transcript. -/
def searchTranscriptTree {E R : Type*} : SearchTree E R → QueryTree E
  | .done _ => .stop
  | .ask e left right => .ask e (searchTranscriptTree left) (searchTranscriptTree right)

/-- Decode the final search result from its full finite leaf transcript. -/
def decodeSearchTranscript {E R : Type*} :
    (t : SearchTree E R) → (searchTranscriptTree t).Leaf → R
  | .done r, _ => r
  | .ask _ left _, .inl leaf => decodeSearchTranscript left leaf
  | .ask _ _ right, .inr leaf => decodeSearchTranscript right leaf

/-- The leaf transcript determines the original search output exactly. -/
theorem decode_search_transcript_run {E R : Type*} (t : SearchTree E R) (ω : E → Bool) :
    decodeSearchTranscript t ((searchTranscriptTree t).run ω) = t.run ω := by
  induction t with
  | done r => rfl
  | ask e left right hl hr =>
    by_cases he : ω e = true
    · simpa [searchTranscriptTree, QueryTree.run, SearchTree.run, he,
        decodeSearchTranscript] using hr
    · simpa [searchTranscriptTree, QueryTree.run, SearchTree.run, he,
        decodeSearchTranscript] using hl

/-- Full finite transcripts retain exactly the queried-bond list. -/
theorem search_transcript_reads {E R : Type*} (t : SearchTree E R) (ω : E → Bool) :
    (searchTranscriptTree t).reads ω = t.reads ω := by
  induction t with
  | done r => rfl
  | ask e left right hl hr =>
    by_cases he : ω e = true
    · simp [searchTranscriptTree, QueryTree.reads, SearchTree.reads, he, hr]
    · simp [searchTranscriptTree, QueryTree.reads, SearchTree.reads, he, hl]

/-- A valid nonrepeating search gives a valid nonrepeating transcript tree. -/
theorem search_transcript_valid {E R : Type*} [DecidableEq E]
    (t : SearchTree E R) (used : Finset E) (ht : t.Valid used) :
    (searchTranscriptTree t).Valid used := by
  induction t generalizing used with
  | done r => trivial
  | ask e left right hl hr => exact ⟨ht.1, hl _ ht.2.1, hr _ ht.2.2⟩

end NearCritical.External
