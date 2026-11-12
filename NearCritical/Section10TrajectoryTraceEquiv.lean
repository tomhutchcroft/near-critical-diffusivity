module

public import NearCritical.Section10Trajectories
public import NearCritical.Section10MarkedRouteProduct
public import NearCritical.Section10RouteArrival

/-! The flow's finite trajectories and the weighted pair proof's histories
record the same states in the same order. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

open scoped Classical

/-- Convert the trajectory of a path to the successive states used by the
merged pair calculation. -/
def trajectoryTraceEquiv (X : Type*) : (n : ℕ) → (Fin n → X) ≃ NestTrace X n
  | 0 =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ i => Fin.elim0 i
      left_inv := fun _ => funext fun i => Fin.elim0 i
      right_inv := fun x => by cases x; rfl }
  | n+1 => (consEquiv' X n).symm.trans ((Equiv.refl X).prodCongr (trajectoryTraceEquiv X n))

theorem routeTraceGet?_trajectory {X : Type*} (n : ℕ) (f : Fin n → X) (j : ℕ) (hj : j < n) :
    routeTraceGet? n (trajectoryTraceEquiv X n f) j = some (f ⟨j,hj⟩) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j =>
      change routeTraceGet? n (trajectoryTraceEquiv X n (Fin.tail f)) j = _
      exact ih (Fin.tail f) j (by omega)

theorem routeTraceMass_trajectory {d : ℕ} {X : Type*}
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (z : Configuration d × Configuration d) (n t : ℕ) (x : X) (f : Fin n → X) :
    routeTraceMass k z n t x (trajectoryTraceEquiv X n f) = trajWeight k n t x f z := by
  induction n generalizing t x with
  | zero => rfl
  | succ n ih =>
    change k t x (f 0) z * routeTraceMass k z n (t+1) (f 0)
      (trajectoryTraceEquiv X n (Fin.tail f)) = k t x (f 0) z * trajWeight k n (t+1) (f 0) (Fin.tail f) z
    rw [ih]

theorem mergedTraceMass_marked_sum_eq_trajProduct {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (z : Configuration d × Configuration d) (s : List PairMove) (t t' : ℕ) (x : X × Y)
    (F : NestTrace X (leftCount s) × NestTrace Y (rightCount s) → ℝ) :
    (∑ h : NestTrace (X × Y) s.length,
      F (mergedRouteTraces s h) * mergedTraceMass k k' z s t t' x h) =
    ∑ f : (Fin (leftCount s) → X) × (Fin (rightCount s) → Y),
      F (trajectoryTraceEquiv X (leftCount s) f.1, trajectoryTraceEquiv Y (rightCount s) f.2) *
        (trajWeight k (leftCount s) t x.1 f.1 z * trajWeight k' (rightCount s) t' x.2 f.2 z) := by
  rw [mergedTraceMass_marked_sum_eq_routeProduct]
  let e := (trajectoryTraceEquiv X (leftCount s)).prodCongr (trajectoryTraceEquiv Y (rightCount s))
  symm
  apply Fintype.sum_equiv e
  intro f
  simp only [e, Equiv.prodCongr_apply, Prod.map, routeTraceMass_trajectory]

end NearCritical.Section10
