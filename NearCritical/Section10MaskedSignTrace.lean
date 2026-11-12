module

public import NearCritical.Section10UsedSignTrace

/-! Reindex the fair signs on physical moves, with arbitrary intervening rows
that preserve the pending sign. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- An inactive row uses a sign-independent nest kernel and retains the
pending sign. -/
def pendingMaskedKernel {Ω X : Type*} (active : ℕ → Bool)
    (K : ℕ → X → Bool → X → Ω → ℝ) (t : ℕ) (x y : X × Bool) (z : Ω) : ℝ :=
  if active t = true then K t x.1 x.2 y.1 z / 2
  else if y.2 = x.2 then K t x.1 false y.1 z else 0

/-- An active row stores the sign it used. An inactive row stores a fixed
placeholder, since it does not use a sign. -/
def usedMaskedKernel {Ω X : Type*} (active : ℕ → Bool)
    (K : ℕ → X → Bool → X → Ω → ℝ) (t : ℕ) (x y : X × Bool) (z : Ω) : ℝ :=
  if active t = true then K t x.1 y.2 y.1 z / 2
  else if y.2 = false then K t x.1 false y.1 z else 0

def usedMaskedTrace {X : Type*} (active : ℕ → Bool) :
    (n : ℕ) → ℕ → Bool → NestTrace (X × Bool) n → NestTrace (X × Bool) n
  | 0, _, _, _ => PUnit.unit
  | n+1, t, a, h =>
    ((h.1.1, if active t = true then a else false),
      usedMaskedTrace active n (t+1) h.1.2 h.2)

private theorem sum_routeTrace_succ {X : Type*} [Fintype X] (n : ℕ)
    (f : (X × Bool) → NestTrace (X × Bool) n → ℝ) :
    (∑ h : NestTrace (X × Bool) (n+1), f h.1 h.2) =
      ∑ x : X, ∑ a : Bool, ∑ h : NestTrace (X × Bool) n, f (x,a) h := by
  change (∑ h : (X × Bool) × NestTrace (X × Bool) n, f h.1 h.2) = _
  simp only [Fintype.sum_prod_type]

private theorem sum_signedRouteTrace {X : Type*} [Fintype X] (n : ℕ)
    (f : Bool → NestTrace (X × Bool) n → ℝ) :
    (∑ h : Bool × NestTrace (X × Bool) n, f h.1 h.2) =
      ∑ a : Bool, ∑ h : NestTrace (X × Bool) n, f a h :=
  Fintype.sum_prod_type _

/-- Moving the fair draw from the previous active move to the move that uses
it preserves every marked chronological sum, including when stays intervene. -/
theorem routeTraceMass_marked_sum_usedMasked {Ω X : Type*} [Fintype X]
    (active : ℕ → Bool) (K : ℕ → X → Bool → X → Ω → ℝ) (z : Ω)
    (n t : ℕ) (x : X) (b : Bool) (F : NestTrace (X × Bool) n → ℝ) :
    (∑ h : Bool × NestTrace (X × Bool) n,
      F (usedMaskedTrace active n t h.1 h.2) *
        routeTraceMass (pendingMaskedKernel active K) z n t (x,h.1) h.2 / 2) =
    ∑ h : NestTrace (X × Bool) n, F h *
      routeTraceMass (usedMaskedKernel active K) z n t (x,b) h := by
  induction n generalizing t x b with
  | zero =>
    simp only [usedMaskedTrace, routeTraceMass, mul_one]
    rw [sum_signedRouteTrace (X := X) 0 (fun _ _ => F PUnit.unit / 2)]
    have hunit (h : NestTrace (X × Bool) 0) : h = PUnit.unit := by
      cases h
      rfl
    simp only [hunit]
    change (∑ _ : Bool, ∑ _ : PUnit, F PUnit.unit / 2) = ∑ _ : PUnit, F PUnit.unit
    simp [Finset.sum_const, nsmul_eq_mul] <;> ring
  | succ n ih =>
    let old := fun a y h => routeTraceMass (pendingMaskedKernel active K) z n (t+1) (y,a) h
    let new := fun a y h => routeTraceMass (usedMaskedKernel active K) z n (t+1) (y,a) h
    let use := fun (a : Bool) (h : NestTrace (X × Bool) n) => usedMaskedTrace active n (t+1) a h
    rw [sum_signedRouteTrace (X := X) (n+1) (fun a h =>
      F (usedMaskedTrace active (n+1) t a h) *
        routeTraceMass (pendingMaskedKernel active K) z (n+1) t (x,a) h / 2)]
    have hleft (a : Bool) := sum_routeTrace_succ (X := X) n (fun v h =>
      F (usedMaskedTrace active (n+1) t a (v,h)) *
        routeTraceMass (pendingMaskedKernel active K) z (n+1) t (x,a) (v,h) / 2)
    refine (Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset Bool)) =>
      hleft a)).trans ?_
    refine Eq.trans ?_ (sum_routeTrace_succ (X := X) n (fun v h => F (v,h) *
      routeTraceMass (usedMaskedKernel active K) z (n+1) t (x,b) (v,h))).symm
    by_cases ht : active t = true
    · simp only [routeTraceMass, pendingMaskedKernel, usedMaskedKernel, usedMaskedTrace, if_pos ht]
      change (∑ a : Bool, ∑ y : X, ∑ c : Bool, ∑ h,
        F ((y,a), use c h) * ((K t x a y z / 2) * old c y h) / 2) =
          ∑ y : X, ∑ a : Bool, ∑ h, F ((y,a),h) * ((K t x a y z / 2) * new a y h)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = ∑ c : Bool, ∑ h, (F ((y,a), use c h) * (K t x a y z / 2)) * old c y h / 2 := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro h _
          ring
        _ = ∑ h, (F ((y,a),h) * (K t x a y z / 2)) * new a y h := by
          exact (sum_signedRouteTrace (X := X) n (fun c h =>
            (F ((y,a), use c h) * (K t x a y z / 2)) * old c y h / 2)).symm.trans
              (ih (t+1) y a (fun h => F ((y,a),h) * (K t x a y z / 2)))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro h _
          ring
    · simp only [routeTraceMass, pendingMaskedKernel, usedMaskedKernel, usedMaskedTrace, if_neg ht]
      change (∑ a : Bool, ∑ y : X, ∑ c : Bool, ∑ h,
        F ((y,false), use c h) * ((if c = a then K t x false y z else 0) * old c y h) / 2) =
          ∑ y : X, ∑ c : Bool, ∑ h,
            F ((y,c),h) * ((if c = false then K t x false y z else 0) * new c y h)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      calc
        _ = ∑ a : Bool, ∑ h,
            (F ((y,false), use a h) * K t x false y z) * old a y h / 2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_eq_single a]
          · apply Finset.sum_congr rfl
            intro h _
            simp only [if_true]
            ring
          · intro c _ hc
            simp [hc]
          · simp
        _ = ∑ h, (F ((y,false),h) * K t x false y z) * new false y h := by
          exact (sum_signedRouteTrace (X := X) n (fun a h =>
            (F ((y,false), use a h) * K t x false y z) * old a y h / 2)).symm.trans
              (ih (t+1) y false (fun h => F ((y,false),h) * K t x false y z))
        _ = _ := by
          rw [Finset.sum_eq_single false]
          · apply Finset.sum_congr rfl
            intro h _
            simp only [if_true]
            ring
          · intro c _ hc
            simp [hc]
          · simp

end NearCritical.Section10
