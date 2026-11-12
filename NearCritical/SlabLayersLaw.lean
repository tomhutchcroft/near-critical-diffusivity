module

public import NearCritical.SlabSiteProbability

/-! Joint law of the two layers.

`layers_law`: under the two-layer law `infinitePi (sprinkleLaw a s)`, the pair
(critical layer, sprinkle layer) has law `P_a ⊗ P_s`. This is the product law
under which the Section 10 offspring estimate is stated
(`Section10.origin_offspring_failure_le`).
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set ProbabilityTheory
open scoped Classical

variable {d : ℕ}

/-- The sprinkle layer of a two-layer sample. -/
def sprinkleLayer (ω : Bond d × Bool → Bool) : Configuration d := fun e => ω (e, false)

lemma measurable_sprinkleLayer : Measurable (sprinkleLayer (d := d)) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem pi_bool_map_pair {X : Type*} [MeasurableSpace X] (ν : Bool → Measure X)
    [∀ b, IsProbabilityMeasure (ν b)] :
    Measure.map (fun g : Bool → X => (g true, g false)) (Measure.pi ν) =
      (ν true).prod (ν false) := by
  have hm : Measurable (fun g : Bool → X => (g true, g false)) :=
    (measurable_pi_apply true).prodMk (measurable_pi_apply false)
  symm
  refine Measure.prod_eq fun S T hS hT => ?_
  rw [Measure.map_apply hm (hS.prod hT)]
  have hpre : (fun g : Bool → X => (g true, g false)) ⁻¹' (S ×ˢ T) =
      Set.pi univ (fun b : Bool => if b then S else T) := by
    ext g
    simp only [mem_preimage, mem_prod, Set.mem_pi, mem_univ, true_imp_iff]
    constructor
    · rintro ⟨h1, h2⟩ b
      cases b
      · simpa using h2
      · simpa using h1
    · intro h
      exact ⟨by simpa using h true, by simpa using h false⟩
  rw [hpre, Measure.pi_pi, Fintype.prod_bool]
  simp

theorem layers_law (a s : I) :
    Measure.map (fun ω : Bond d × Bool → Bool => (criticalLayer ω, sprinkleLayer ω))
        (Measure.infinitePi (sprinkleLaw (d := d) a s)) =
      (percolation d a).prod (percolation d s) := by
  have hf : Function.Injective (fun x : Bool × Bond d => ((x.2, x.1) : Bond d × Bool)) := by
    rintro ⟨b, e⟩ ⟨b', e'⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have h1 := Measure.map_infinitePi_infinitePi_of_inj (P := sprinkleLaw (d := d) a s) hf
  have h2 := Measure.infinitePi_map_curry
    (fun (b : Bool) (e : Bond d) => sprinkleLaw (d := d) a s (e, b))
  have hν1 : Measure.infinitePi (fun e : Bond d => sprinkleLaw (d := d) a s (e, true)) =
      percolation d a := by
    unfold percolation
    congr 1
  have hν0 : Measure.infinitePi (fun e : Bond d => sprinkleLaw (d := d) a s (e, false)) =
      percolation d s := by
    unfold percolation
    congr 1
  have hm1 : Measurable (fun (ω : Bond d × Bool → Bool) (x : Bool × Bond d) => ω (x.2, x.1)) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hm3 : Measurable (fun g : Bool → Configuration d => (g true, g false)) :=
    (measurable_pi_apply true).prodMk (measurable_pi_apply false)
  have hcomp : (fun ω : Bond d × Bool → Bool => (criticalLayer ω, sprinkleLayer ω)) =
      ((fun g : Bool → Configuration d => (g true, g false)) ∘
        (MeasurableEquiv.curry Bool (Bond d) Bool)) ∘
        (fun (ω : Bond d × Bool → Bool) (x : Bool × Bond d) => ω (x.2, x.1)) := rfl
  rw [hcomp, ← Measure.map_map (hm3.comp (MeasurableEquiv.measurable _)) hm1, h1,
    ← Measure.map_map hm3 (MeasurableEquiv.measurable _), h2, Measure.infinitePi_eq_pi,
    pi_bool_map_pair, hν1, hν0]

end NearCritical
