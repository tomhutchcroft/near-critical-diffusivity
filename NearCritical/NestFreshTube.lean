module

public import NearCritical.NestCubeWeights
public import Mathlib.MeasureTheory.Integral.Prod

/-! Actual finite fresh-tube integral identity for the new chain-weight argument.
Source exploration must still supply the revealed/fresh coordinate blocks. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Full joint product-law/Fubini identity for arbitrary observables of disjoint
past and fresh restrictions. No observable independence is assumed. -/
theorem percolation_disjoint_block_integral {d : ℕ} (p : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T)
    (f : (S → Bool) × (T → Bool) → ℝ) :
    (∫ ω : Configuration d, f (S.restrict ω,T.restrict ω) ∂percolation d p) =
      ∫ η, ∫ ξ, f (η,ξ) ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p))
        ∂(Measure.pi (fun _ : S => bernoulliMeasure true false p)) := by
  have hi : IndepFun (S.restrict : Configuration d → (S → Bool))
      (T.restrict : Configuration d → (T → Bool)) (percolation d p) :=
    iIndepFun.indepFun_finset S T hd
      (iIndepFun_infinitePi (fun _ : Bond d => (measurable_id : Measurable (id : Bool → Bool))))
      (fun e => measurable_pi_apply e)
  have hmap := hi.map_prod_eq_prod_map_map (Finset.measurable_restrict S).aemeasurable
    (Finset.measurable_restrict T).aemeasurable
  have hS : (percolation d p).map S.restrict = Measure.pi (fun _ : S => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  have hT : (percolation d p).map T.restrict = Measure.pi (fun _ : T => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  rw [hS,hT] at hmap
  have hm : Measurable (fun ω : Configuration d => (S.restrict ω,T.restrict ω)) :=
    (Finset.measurable_restrict S).prodMk (Finset.measurable_restrict T)
  calc
    _ = ∫ z, f z ∂((percolation d p).map (fun ω => (S.restrict ω,T.restrict ω))) :=
      (integral_map hm.aemeasurable (Integrable.of_finite : Integrable f _).aestronglyMeasurable).symm
    _ = _ := by rw [hmap]; exact integral_prod f Integrable.of_finite

def freshTubeSuccessProbability {d : ℕ} (p : unitInterval) (S T : Finset (Bond d))
    (success : (S → Bool) → (T → Bool) → Prop) (η : S → Bool) : ℝ :=
  (Measure.pi (fun _ : T => bernoulliMeasure true false p)).real {ξ | success η ξ}

def freshTubeSuccessWeight {d : ℕ} (p : unitInterval) (S T : Finset (Bond d))
    (success : (S → Bool) → (T → Bool) → Prop) (η : S → Bool) (ξ : T → Bool) : ℝ :=
  if success η ξ then (freshTubeSuccessProbability p S T success η)⁻¹ else 0

lemma freshTubeSuccessWeight_integral {d : ℕ} (p : unitInterval) (S T : Finset (Bond d))
    (success : (S → Bool) → (T → Bool) → Prop) (η : S → Bool)
    (hq : 0<freshTubeSuccessProbability p S T success η) :
    (∫ ξ, freshTubeSuccessWeight p S T success η ξ
      ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p)))=1 := by
  have hm : MeasurableSet {ξ : T → Bool | success η ξ} := (Set.toFinite _).measurableSet
  have he : freshTubeSuccessWeight p S T success η =
      ({ξ : T → Bool | success η ξ} : Set (T → Bool)).indicator
        (fun _ => (freshTubeSuccessProbability p S T success η)⁻¹) := by
    funext ξ
    simp [freshTubeSuccessWeight,Set.indicator]
  rw [he,integral_indicator_const _ hm]
  exact mul_inv_cancel₀ hq.ne'

/-- The actual normalized fresh-tube indicator has mean one against every
past observable. This is the finite-coordinate conditional-mean identity used
in the paper's martingale argument, with the normalizer computed from the law. -/
theorem percolation_freshTube_weighted_mean_on_support {d : ℕ} (p : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T)
    (success : (S → Bool) → (T → Bool) → Prop)
    (H : (S → Bool) → ℝ)
    (hq : ∀ η, H η≠0 → 0<freshTubeSuccessProbability p S T success η) :
    (∫ ω : Configuration d, H (S.restrict ω) *
      freshTubeSuccessWeight p S T success (S.restrict ω) (T.restrict ω) ∂percolation d p) =
      ∫ ω : Configuration d, H (S.restrict ω) ∂percolation d p := by
  rw [percolation_disjoint_block_integral p S T hd
    (fun z => H z.1 * freshTubeSuccessWeight p S T success z.1 z.2)]
  have he (η : S → Bool) :
      (∫ ξ, H η * freshTubeSuccessWeight p S T success η ξ
        ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p)))=H η := by
    rw [integral_const_mul]
    by_cases hH : H η=0
    · simp [hH]
    · rw [freshTubeSuccessWeight_integral p S T success η (hq η hH),mul_one]
  simp_rw [he]
  have hm : (percolation d p).map S.restrict = Measure.pi (fun _ : S => bernoulliMeasure true false p) :=
    Measure.infinitePi_map_restrict _
  rw [← hm]
  exact integral_map (Finset.measurable_restrict S).aemeasurable
    (Integrable.of_finite : Integrable H _).aestronglyMeasurable

/-- Convenient everywhere-positive version of the supported-history identity. -/
theorem percolation_freshTube_weighted_mean {d : ℕ} (p : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T)
    (success : (S → Bool) → (T → Bool) → Prop)
    (hq : ∀ η, 0<freshTubeSuccessProbability p S T success η) (H : (S → Bool) → ℝ) :
    (∫ ω : Configuration d, H (S.restrict ω) *
      freshTubeSuccessWeight p S T success (S.restrict ω) (T.restrict ω) ∂percolation d p) =
      ∫ ω : Configuration d, H (S.restrict ω) ∂percolation d p :=
  percolation_freshTube_weighted_mean_on_support p S T hd success H (fun η _ => hq η)

end NearCritical
