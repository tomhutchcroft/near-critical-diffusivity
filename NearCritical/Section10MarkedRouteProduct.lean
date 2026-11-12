module

public import NearCritical.Section10UsedSignTrace

/-! Exact finite sums for weighted pairs of chronological route histories. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- A mark of the two projected histories has exactly the same weighted sum
under the merged trace and under the product of the two route trace masses. -/
theorem mergedTraceMass_marked_sum_eq_routeProduct {Ω X Y : Type*} [Fintype X] [Fintype Y]
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ)
    (z : Ω) (s : List PairMove) (t t' : ℕ) (x : X × Y)
    (F : NestTrace X (leftCount s) × NestTrace Y (rightCount s) → ℝ) :
    (∑ h : NestTrace (X × Y) s.length,
      F (mergedRouteTraces s h) * mergedTraceMass k k' z s t t' x h) =
    ∑ r : NestTrace X (leftCount s) × NestTrace Y (rightCount s),
      F r * (routeTraceMass k z (leftCount s) t x.1 r.1 *
        routeTraceMass k' z (rightCount s) t' x.2 r.2) := by
  classical
  let replay := fun r : NestTrace X (leftCount s) × NestTrace Y (rightCount s) =>
    interleaveRouteTraces s x r.1 r.2
  let f := fun h => F (mergedRouteTraces s h) * mergedTraceMass k k' z s t t' x h
  have hreplay : Function.LeftInverse (mergedRouteTraces s) replay := by
    rintro ⟨l,r⟩
    exact mergedRouteTraces_interleave s x l r
  calc
    ∑ h, f h = ∑ h ∈ Finset.univ.image replay, f h := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro h _ hnot
      have hz : mergedTraceMass k k' z s t t' x h = 0 := by
        by_contra hne
        exact hnot (Finset.mem_image.mpr
          ⟨mergedRouteTraces s h, Finset.mem_univ _,
            interleave_mergedRouteTraces_of_nonzero k k' z s t t' x h hne⟩)
      simp [f, hz]
    _ = ∑ r, f (replay r) :=
      Finset.sum_image fun a _ b _ h => hreplay.injective h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [f, replay, mergedRouteTraces_interleave, Prod.eta, mergedTraceMass_interleave]

/-- After summing the initial uniform sign, the chronological trace has
the mass of a kernel drawing the sign on the move where it is used. -/
theorem routeTraceMass_marked_sum_usedSigns {Ω X : Type*} [Fintype X]
    (K : ℕ → X → Bool → X → Ω → ℝ) (z : Ω)
    (n t : ℕ) (x : X) (b : Bool) (F : NestTrace (X × Bool) n → ℝ) :
    (∑ h : Bool × NestTrace (X × Bool) n,
      F ((usedSignTrace X n) h).1 *
        routeTraceMass (fun j x y z => nextSignKernel (fun i v s w => K i v s w z) j x y)
          z n t (x,h.1) h.2 / 2) =
    ∑ h : NestTrace (X × Bool) n, F h *
      routeTraceMass (fun j x y z => usedSignKernel (fun i v s w => K i v s w z) j x y)
        z n t (x,b) h := by
  simp_rw [routeTraceMass_usedSignTrace K z n t x _ b _]
  let f := fun h => F h *
    routeTraceMass (fun j x y z => usedSignKernel (fun i v s w => K i v s w z) j x y)
      z n t (x,b) h
  calc
    _ = ∑ h : NestTrace (X × Bool) n × Bool, f h.1 / 2 :=
      (usedSignTrace X n).sum_comp (fun h => f h.1 / 2)
    _ = ∑ h, f h := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h _
      simp [Finset.sum_const, nsmul_eq_mul] <;> ring

/-- The two independent initial signs can be summed out simultaneously,
even when the mark couples the two histories. -/
theorem routeTraceMass_marked_pair_sum_usedSigns {Ω X Y : Type*} [Fintype X] [Fintype Y]
    (K : ℕ → X → Bool → X → Ω → ℝ) (K' : ℕ → Y → Bool → Y → Ω → ℝ)
    (z : Ω) (n n' t t' : ℕ) (x : X) (y : Y) (b b' : Bool)
    (F : NestTrace (X × Bool) n → NestTrace (Y × Bool) n' → ℝ) :
    (∑ l : Bool × NestTrace (X × Bool) n, ∑ r : Bool × NestTrace (Y × Bool) n',
      (F ((usedSignTrace X n) l).1 ((usedSignTrace Y n') r).1 *
        routeTraceMass (fun j x y z => nextSignKernel (fun i v s w => K i v s w z) j x y)
          z n t (x,l.1) l.2 *
        routeTraceMass (fun j x y z => nextSignKernel (fun i v s w => K' i v s w z) j x y)
          z n' t' (y,r.1) r.2) / 4) =
    ∑ l : NestTrace (X × Bool) n, ∑ r : NestTrace (Y × Bool) n',
      F l r *
        routeTraceMass (fun j x y z => usedSignKernel (fun i v s w => K i v s w z) j x y)
          z n t (x,b) l *
        routeTraceMass (fun j x y z => usedSignKernel (fun i v s w => K' i v s w z) j x y)
          z n' t' (y,b') r := by
  let A := fun l : Bool × NestTrace (X × Bool) n =>
    routeTraceMass (fun j x y z => nextSignKernel (fun i v s w => K i v s w z) j x y)
      z n t (x,l.1) l.2
  let B := fun r : Bool × NestTrace (Y × Bool) n' =>
    routeTraceMass (fun j x y z => nextSignKernel (fun i v s w => K' i v s w z) j x y)
      z n' t' (y,r.1) r.2
  let U := fun l => routeTraceMass
    (fun j x y z => usedSignKernel (fun i v s w => K i v s w z) j x y) z n t (x,b) l
  let V := fun r => routeTraceMass
    (fun j x y z => usedSignKernel (fun i v s w => K' i v s w z) j x y) z n' t' (y,b') r
  let L := fun l : Bool × NestTrace (X × Bool) n => ((usedSignTrace X n) l).1
  let R := fun r : Bool × NestTrace (Y × Bool) n' => ((usedSignTrace Y n') r).1
  change (∑ l, ∑ r, (F (L l) (R r) * A l * B r) / 4) = ∑ l, ∑ r, F l r * U l * V r
  calc
    _ = ∑ l, ∑ r, (F (L l) r * A l / 2) * V r := by
      apply Finset.sum_congr rfl
      intro l _
      calc
        _ = ∑ r, (F (L l) (R r) * A l / 2) * B r / 2 := by
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ = _ := routeTraceMass_marked_sum_usedSigns K' z n' t' y b'
          (fun r => F (L l) r * A l / 2)
    _ = ∑ r, ∑ l, (F (L l) r * V r) * A l / 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ r, ∑ l, (F l r * V r) * U l := by
      apply Finset.sum_congr rfl
      intro r _
      exact routeTraceMass_marked_sum_usedSigns K z n t x b (fun l => F l r * V r)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro r _
      ring

end NearCritical.Section10
