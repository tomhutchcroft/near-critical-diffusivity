module

public import NearCritical.Section10FirstGoodPersistence
public import NearCritical.Section10FirstGoodUsedHistory
public import NearCritical.Section10RouteArrival

/-! A tube mark reads the incoming sign in the pending history and the
sign on the move itself in the used-sign history. Both histories record
the same nests. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open NestLayout (eraseInitialUsedSign)

theorem routeTraceGet?_usedMaskedTrace_nest {X : Type*}
    (active : ℕ → Bool) (n t : ℕ) (a : Bool) (h : NestTrace (X × Bool) n) (j : ℕ) :
    (routeTraceGet? n (usedMaskedTrace active n t a h) j).map Prod.fst =
      (routeTraceGet? n h j).map Prod.fst := by
  induction n generalizing t a j with
  | zero => rfl
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih (t+1) h.1.2 h.2 j

theorem routeTraceGet?_eraseInitialUsedSign_nest {X : Type*}
    (n : ℕ) (h : NestTrace (X × Bool) n) (j : ℕ) :
    (routeTraceGet? n (eraseInitialUsedSign n h) j).map Prod.fst =
      (routeTraceGet? n h j).map Prod.fst := by
  cases n <;> cases j <;> rfl

theorem routeTraceGet?_eraseInitialUsedSign_succ {X : Type*}
    (n : ℕ) (h : NestTrace (X × Bool) n) (j : ℕ) :
    routeTraceGet? n (eraseInitialUsedSign n h) (j+1) =
      routeTraceGet? n h (j+1) := by
  cases n <;> rfl

/-- The sign recorded at the next active row is the sign stored at the
end of the previous pending row. -/
theorem routeTraceGet?_usedMaskedTrace_succ {X : Type*}
    (active : ℕ → Bool) (n t : ℕ) (a : Bool) (h : NestTrace (X × Bool) n)
    (j : ℕ) (u v : X × Bool)
    (hu : routeTraceGet? n h j = some u)
    (hv : routeTraceGet? n h (j+1) = some v) :
    routeTraceGet? n (usedMaskedTrace active n t a h) (j+1) =
      some (v.1, if active (t+(j+1)) = true then u.2 else false) := by
  induction n generalizing t a j with
  | zero => simp [routeTraceGet?] at hu
  | succ n ih =>
    cases j with
    | zero =>
      have he : h.1 = u := Option.some.inj hu
      change routeTraceGet? n h.2 0 = some v at hv
      cases n with
      | zero => simp [routeTraceGet?] at hv
      | succ n =>
        have he' : h.2.1 = v := Option.some.inj hv
        change some (h.2.1.1, if active (t+1) = true then h.1.2 else false) = _
        rw [he, he']
    | succ j =>
      change routeTraceGet? n h.2 j = some u at hu
      change routeTraceGet? n h.2 (j+1) = some v at hv
      change routeTraceGet? n (usedMaskedTrace active n (t+1) h.1.2 h.2) (j+1) = _
      rw [ih (t+1) h.1.2 h.2 j hu hv, show t+1+(j+1) = t+(j+1+1) by omega]

/-- At a physical tube, erasing the dummy start sign leaves the sign
used there equal to the incoming pending sign. -/
theorem routeTraceGet?_usedPhysicalSign {X : Type*}
    (active : ℕ → Bool) (n j : ℕ) (a : Bool) (h : NestTrace (X × Bool) n)
    (u v : X × Bool)
    (hu : routeTraceGet? n h j = some u)
    (hv : routeTraceGet? n h (j+1) = some v) (ha : active (j+1) = true) :
    routeTraceGet? n (eraseInitialUsedSign n (usedMaskedTrace active n 0 a h)) (j+1) =
      some (v.1,u.2) := by
  rw [routeTraceGet?_eraseInitialUsedSign_succ]
  simpa only [Nat.zero_add, if_pos ha] using routeTraceGet?_usedMaskedTrace_succ active n 0 a h j u v hu hv

/-- Last recorded route state, or the initial state for an empty trace. -/
def routeTraceLast {X : Type*} : (n : ℕ) → X → NestTrace X n → X
  | 0, x, _ => x
  | n+1, _, h => routeTraceLast n h.1 h.2

theorem routeTraceGet?_last {X : Type*} (n : ℕ) (x : X) (h : NestTrace X n) (hn : 0 < n) :
    routeTraceGet? n h (n-1) = some (routeTraceLast n x h) := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change routeTraceGet? (n+1) h.2 n = some (routeTraceLast (n+1) h.1 h.2)
      exact ih h.1 h.2 (by omega)

/-- Interleaving the route traces leaves the final state of each route
at its own local clock. -/
theorem mergedTraceLast_interleave {X Y : Type*} (s : List PairMove) (x : X × Y)
    (l : NestTrace X (leftCount s)) (r : NestTrace Y (rightCount s)) :
    mergedTraceLast s x (interleaveRouteTraces s x l r) =
      (routeTraceLast (leftCount s) x.1 l, routeTraceLast (rightCount s) x.2 r) := by
  induction s generalizing x with
  | nil => rfl
  | cons m s ih =>
    cases m
    · exact ih (l.1,x.2) l.2 r
    · exact ih (x.1,r.1) l r.2
    · exact ih (l.1,r.1) l.2 r.2

/-- In a nonzero history the two incoming states of the next row are
exactly the last states recorded on the separate route traces. -/
theorem mergedTraceLast_eq_routeTraceLast {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ) (z : Ω)
    (s : List PairMove) (t t' : ℕ) (x : X × Y) (h : NestTrace (X × Y) s.length)
    (hh : mergedTraceMass k k' z s t t' x h ≠ 0) :
    mergedTraceLast s x h =
      (routeTraceLast (leftCount s) x.1 (mergedRouteTraces s h).1,
        routeTraceLast (rightCount s) x.2 (mergedRouteTraces s h).2) := by
  have he := interleave_mergedRouteTraces_of_nonzero k k' z s t t' x h hh
  exact (congrArg (mergedTraceLast s x) he.symm).trans
    (mergedTraceLast_interleave s x (mergedRouteTraces s h).1 (mergedRouteTraces s h).2)

/-- Read a tube event only when all four entries are recorded. -/
def optionTubeMark {X Ω : Type*} (F : X → X → Bool → Bool → Ω → Prop)
    (p q : Option X) (a b : Option Bool) (z : Ω) : Prop :=
  match p, q, a, b with
  | some u, some v, some c, some c' => F u v c c' z
  | _, _, _, _ => False

namespace NestLayout

/-- A shared tube always reads the two incoming nests. In a used-sign
history the sign for each nest is read one row later, on the move. -/
def historyTubeMark {D d : ℕ} (Λ : NestLayout D d) (G : Λ.Φ) (ℓ : RouteLabel D)
    (used : Bool) (n n' j j' : ℕ) (h : NestTrace Λ.X n) (h' : NestTrace Λ.X n')
    (z : Configuration d × Configuration d) : Prop :=
  optionTubeMark (fun (u v : ↥Λ.P) a b => Λ.firstGoodSharedTubeMark G ℓ u.val v.val a b)
    ((routeTraceGet? n h j).map Prod.fst) ((routeTraceGet? n' h' j').map Prod.fst)
    ((routeTraceGet? n h (if used then j+1 else j)).map Prod.snd)
    ((routeTraceGet? n' h' (if used then j'+1 else j')).map Prod.snd) z

/-- The physical tube event is preserved by the transformation that
moves the sign draw to the row that uses it. -/
theorem historyTubeMark_used_iff_pending {D d : ℕ} (Λ : NestLayout D d)
    (G : Λ.Φ) (ℓ : RouteLabel D) (active active' : ℕ → Bool)
    (n n' j j' : ℕ) (a b : Bool) (h : NestTrace Λ.X n) (h' : NestTrace Λ.X n')
    (u v u' v' : Λ.X)
    (hu : routeTraceGet? n h j = some u) (hv : routeTraceGet? n h (j+1) = some v)
    (hu' : routeTraceGet? n' h' j' = some u') (hv' : routeTraceGet? n' h' (j'+1) = some v')
    (ha : active (j+1) = true) (hb : active' (j'+1) = true)
    (z : Configuration d × Configuration d) :
    Λ.historyTubeMark G ℓ true n n' j j'
      (eraseInitialUsedSign n (usedMaskedTrace active n 0 a h))
      (eraseInitialUsedSign n' (usedMaskedTrace active' n' 0 b h')) z ↔
    Λ.historyTubeMark G ℓ false n n' j j' h h' z := by
  have hleft := routeTraceGet?_usedPhysicalSign active n j a h u v hu hv ha
  have hright := routeTraceGet?_usedPhysicalSign active' n' j' b h' u' v' hu' hv' hb
  simp only [historyTubeMark, optionTubeMark, Bool.false_eq_true, if_false, if_true,
    routeTraceGet?_eraseInitialUsedSign_nest, routeTraceGet?_usedMaskedTrace_nest,
    hleft, hright, hu, hu', Option.map_some]

end NestLayout

end NearCritical.Section10
