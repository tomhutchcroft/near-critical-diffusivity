module

public import NearCritical.Section10NestTransitionLaw
public import NearCritical.NestRepresentative

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Compute the offspring set of the first good representative on success.
The empty fallback is used only on outcomes where the chain dies. -/
def selectedRepresentativeOffspring {ι α Ξ : Type*} [LinearOrder ι]
    (nest : Finset ι) (offspring : Ξ → ι → Finset α) (k : ℕ)
    (success : Ξ → Prop)
    (hgood : ∀ ξ, success ξ →
      (goodNestRepresentatives nest (offspring ξ) k).Nonempty) (ξ : Ξ) : Finset α :=
  if h : success ξ then
    offspring ξ (nestRepresentative nest (offspring ξ) k (hgood ξ h))
  else ∅

/-- Successful first-good selection supplies enough offspring for the sampler. -/
theorem selectedRepresentativeOffspring_enough {ι α Ξ : Type*} [LinearOrder ι]
    (nest : Finset ι) (offspring : Ξ → ι → Finset α) {k : ℕ} (hk : 0 < k)
    (success : Ξ → Prop)
    (hgood : ∀ ξ, success ξ →
      (goodNestRepresentatives nest (offspring ξ) k).Nonempty)
    (ξ : Ξ) (hξ : success ξ) :
    k ≤ (selectedRepresentativeOffspring nest offspring k success hgood ξ).card := by
  obtain ⟨next, hsub, hcard⟩ :=
    nestRepresentative_next_nest nest (offspring ξ) hk (hgood ξ hξ)
  simpa only [selectedRepresentativeOffspring, dif_pos hξ, hcard] using
    Finset.card_le_card hsub

/-- The actual tube sampler with the first-good representative has exactly
the mass of the successful tube event. Representative choice adds no loss. -/
theorem firstGoodNestTubeTransition_mass {d : ℕ} {ι α : Type*}
    [LinearOrder ι] [Fintype α] [MeasurableSpace (Finset α)]
    [MeasurableSingletonClass (Finset α)]
    (p : unitInterval) (T : Finset (Bond d)) (nest : Finset ι)
    (offspring : (T → Bool) → ι → Finset α) {k : ℕ} (hk : 0 < k)
    (hcard : nest.card = k) (success : (T → Bool) → Prop)
    (htotal : ∀ ξ, success ξ → 2*k^4 ≤ (nest.biUnion (offspring ξ)).card) :
    let hgood := fun ξ hξ =>
      goodNestRepresentatives_nonempty nest (offspring ξ) hk hcard (htotal ξ hξ)
    nestTubeTransition p T success
      (selectedRepresentativeOffspring nest offspring k success hgood) k Set.univ =
        (Measure.pi (fun _ : T => bernoulliMeasure true false p)) {ξ | success ξ} := by
  intro hgood
  exact nestTubeTransition_mass p T success _ k
    (selectedRepresentativeOffspring_enough nest offspring hk success hgood)

end NearCritical.Section10
