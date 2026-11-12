module

public import NearCritical.Section10MergedRouteTraces

/-! Reindex the exact signed history so that the sign used on a move is
sampled with that move. The unused terminal sign is summed out. -/
@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- Exchange the incoming sign with the sign stored by the next state. -/
def exchangeTraceSign (X T : Type*) : Bool × ((X × Bool) × T) ≃ (X × Bool) × (Bool × T) where
  toFun x := ((x.2.1.1, x.1), (x.2.1.2, x.2.2))
  invFun x := (x.1.2, ((x.1.1, x.2.1), x.2.2))
  left_inv := by rintro ⟨a,⟨⟨y,b⟩,z⟩⟩; rfl
  right_inv := by rintro ⟨⟨y,a⟩,⟨b,z⟩⟩; rfl

/-- Convert the signs stored at the start and at each arrival to the signs
used during each move, together with the unused terminal sign. -/
def usedSignTrace (X : Type*) : (n : ℕ) →
    Bool × NestTrace (X × Bool) n ≃ NestTrace (X × Bool) n × Bool
  | 0 => Equiv.prodComm _ _
  | n+1 => (exchangeTraceSign X (NestTrace (X × Bool) n)).trans
      ((Equiv.prodCongr (Equiv.refl (X × Bool)) (usedSignTrace X n)).trans
        (Equiv.prodAssoc (X × Bool) (NestTrace (X × Bool) n) Bool).symm)

/-- The source kernel stores a freshly drawn sign for the next move. -/
def nextSignKernel {X : Type*} (K : ℕ → X → Bool → X → ℝ)
    (n : ℕ) (x y : X × Bool) : ℝ :=
  K n x.1 x.2 y.1 / 2

/-- The reindexed kernel samples the sign used during the current move. -/
def usedSignKernel {X : Type*} (K : ℕ → X → Bool → X → ℝ)
    (n : ℕ) (x y : X × Bool) : ℝ :=
  K n x.1 y.2 y.1 / 2

theorem nestTraceMass_usedSignTrace {X : Type*} (K : ℕ → X → Bool → X → ℝ)
    (n : ℕ) (x : X) (a b : Bool) (h : NestTrace (X × Bool) n) :
    nestTraceMass (nextSignKernel K) n (x,a) h =
      nestTraceMass (usedSignKernel K) n (x,b) ((usedSignTrace X n) (a,h)).1 := by
  induction n generalizing x a b with
  | zero => rfl
  | succ n ih =>
    change (K n x a h.1.1 / 2) * nestTraceMass (nextSignKernel K) n h.1 h.2 =
      (K n x a h.1.1 / 2) * nestTraceMass (usedSignKernel K) n (h.1.1,a)
        ((usedSignTrace X n) (h.1.2,h.2)).1
    rw [ih h.1.1 h.1.2 a h.2]

/-- The two descriptions have the same mass for every mark of the nests
and signs used on moves. -/
theorem markedTraceMass_sum_usedSigns {X : Type*} [Fintype X] (K : ℕ → X → Bool → X → ℝ)
    (n : ℕ) (x : X) (b : Bool) (F : NestTrace (X × Bool) n → ℝ) :
    (∑ h : Bool × NestTrace (X × Bool) n,
      F ((usedSignTrace X n) h).1 * nestTraceMass (nextSignKernel K) n (x,h.1) h.2 / 2) =
    ∑ h : NestTrace (X × Bool) n, F h * nestTraceMass (usedSignKernel K) n (x,b) h := by
  simp_rw [nestTraceMass_usedSignTrace K n x _ b _]
  let e := usedSignTrace X n
  calc
    _ = ∑ z : NestTrace (X × Bool) n × Bool,
        F z.1 * nestTraceMass (usedSignKernel K) n (x,b) z.1 / 2 :=
      e.sum_comp (fun z => F z.1 * nestTraceMass (usedSignKernel K) n (x,b) z.1 / 2)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h _
      simp [Finset.sum_const, nsmul_eq_mul] <;> ring

/-- The same sign reindexing for the increasing clocks of the merged
route histories. -/
theorem routeTraceMass_usedSignTrace {Ω X : Type*} (K : ℕ → X → Bool → X → Ω → ℝ)
    (z : Ω) (n t : ℕ) (x : X) (a b : Bool) (h : NestTrace (X × Bool) n) :
    routeTraceMass (fun j x y z => nextSignKernel (fun i v s w => K i v s w z) j x y) z n t (x,a) h =
      routeTraceMass (fun j x y z => usedSignKernel (fun i v s w => K i v s w z) j x y) z n t
        (x,b) ((usedSignTrace X n) (a,h)).1 := by
  induction n generalizing t x a b with
  | zero => rfl
  | succ n ih =>
    change (K t x a h.1.1 z / 2) *
        routeTraceMass (fun j x y z => nextSignKernel (fun i v s w => K i v s w z) j x y)
          z n (t+1) h.1 h.2 =
      (K t x a h.1.1 z / 2) *
        routeTraceMass (fun j x y z => usedSignKernel (fun i v s w => K i v s w z) j x y)
          z n (t+1) (h.1.1,a) ((usedSignTrace X n) (h.1.2,h.2)).1
    rw [ih (t+1) h.1.1 h.1.2 a h.2]

end NearCritical.Section10
