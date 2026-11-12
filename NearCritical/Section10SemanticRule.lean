module

public import NearCritical.Section10RevealRefine

/-! From configuration-level step predicates to bit-level success sets.

A `NestRule` wants the success set of a step as a set of bit patterns on the
fresh block `T`, for each value `⟨F, η⟩` of the refined reveal. The source
defines success through the configuration. `gluePair` rebuilds a configuration
pair from the revealed bits `η` on `S F` and the fresh bits `b` on `T`
(everything else closed), and `gluePair_agree` says it agrees with any actual
`z` in the reveal atom on `S F ∪ T`.

So for a predicate `P` that only reads `S F ∪ T` (`ReadsOnly`), the bit set
`{b | P (gluePair η b)}` satisfies: for `z` in the atom,
`T.restrict (layerVal z) ∈ bitSet ↔ P z` (`bitSet_iff`). The same holds for
functions (`glue_fun_eq`), used for offspring.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- `P` only reads the layered bonds in `U`. -/
def ReadsOnly {d : ℕ} {β : Type*} (U : Finset (LBond d))
    (P : Configuration d × Configuration d → β) : Prop :=
  ∀ z z' : Configuration d × Configuration d,
    (∀ e ∈ U, layerVal z e = layerVal z' e) → P z = P z'

/-- Configuration pair with prescribed bits on `S` and on `T`, closed elsewhere. -/
def gluePair {d : ℕ} {S T : Finset (LBond d)} (η : S → Bool) (b : T → Bool) :
    Configuration d × Configuration d :=
  (fun e => if h : ((false, e) : LBond d) ∈ S then η ⟨_, h⟩
      else if h' : ((false, e) : LBond d) ∈ T then b ⟨_, h'⟩ else false,
   fun e => if h : ((true, e) : LBond d) ∈ S then η ⟨_, h⟩
      else if h' : ((true, e) : LBond d) ∈ T then b ⟨_, h'⟩ else false)

lemma layerVal_gluePair {d : ℕ} {S T : Finset (LBond d)} (η : S → Bool) (b : T → Bool)
    (e : LBond d) :
    layerVal (gluePair η b) e =
      if h : e ∈ S then η ⟨e, h⟩ else if h' : e ∈ T then b ⟨e, h'⟩ else false := by
  obtain ⟨l, e⟩ := e
  cases l <;> rfl

/-- The glued pair agrees with an actual configuration pair on `S ∪ T`. -/
lemma gluePair_agree {d : ℕ} {S T : Finset (LBond d)}
    (z : Configuration d × Configuration d) :
    ∀ e ∈ S ∪ T, layerVal (gluePair (S.restrict (layerVal z)) (T.restrict (layerVal z))) e =
      layerVal z e := by
  intro e he
  rw [layerVal_gluePair]
  by_cases h : e ∈ S
  · rw [dif_pos h]
    rfl
  · rw [dif_neg h]
    have h' : e ∈ T := by
      rcases Finset.mem_union.mp he with h1 | h1
      · exact absurd h1 h
      · exact h1
    rw [dif_pos h']
    rfl

/-- Value of a local function, read off the revealed and fresh bits. -/
theorem glue_fun_eq {d : ℕ} {β : Type*} {S T : Finset (LBond d)}
    (P : Configuration d × Configuration d → β) (hP : ReadsOnly (S ∪ T) P)
    (z : Configuration d × Configuration d) :
    P (gluePair (S.restrict (layerVal z)) (T.restrict (layerVal z))) = P z :=
  hP _ _ (gluePair_agree z)

/-- Bit-level success set of a configuration-level predicate. -/
def bitSet {d : ℕ} {S T : Finset (LBond d)} (η : S → Bool)
    (P : Configuration d × Configuration d → Prop) : Set (T → Bool) :=
  {b | P (gluePair η b)}

theorem bitSet_iff {d : ℕ} {S T : Finset (LBond d)}
    (P : Configuration d × Configuration d → Prop) (hP : ReadsOnly (S ∪ T) P)
    (z : Configuration d × Configuration d) :
    T.restrict (layerVal z) ∈ (bitSet (S.restrict (layerVal z)) P : Set (T → Bool)) ↔ P z := by
  have h := glue_fun_eq (S := S) (T := T) P hP z
  constructor
  · intro hb
    have hb' : P (gluePair (S.restrict (layerVal z)) (T.restrict (layerVal z))) := hb
    rwa [h] at hb'
  · intro hz
    show P (gluePair (S.restrict (layerVal z)) (T.restrict (layerVal z)))
    rw [h]
    exact hz

lemma ReadsOnly.mono {d : ℕ} {β : Type*} {U U' : Finset (LBond d)} (h : U ⊆ U')
    {P : Configuration d × Configuration d → β} (hP : ReadsOnly U P) : ReadsOnly U' P :=
  fun z z' hz => hP z z' (fun e he => hz e (h he))

lemma ReadsOnly.comp {d : ℕ} {β γ : Type*} {U : Finset (LBond d)}
    {P : Configuration d × Configuration d → β} (hP : ReadsOnly U P) (f : β → γ) :
    ReadsOnly U (fun z => f (P z)) :=
  fun z z' hz => congrArg f (hP z z' hz)

lemma ReadsOnly.pair {d : ℕ} {β γ : Type*} {U : Finset (LBond d)}
    {P : Configuration d × Configuration d → β} {Q : Configuration d × Configuration d → γ}
    (hP : ReadsOnly U P) (hQ : ReadsOnly U Q) : ReadsOnly U (fun z => (P z, Q z)) :=
  fun z z' hz => Prod.ext (hP z z' hz) (hQ z z' hz)

end NearCritical.Section10
