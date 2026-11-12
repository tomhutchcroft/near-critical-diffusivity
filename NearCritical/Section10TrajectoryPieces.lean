module

public import NearCritical.Section10Trajectories

/-! Backward selection of a microscopic walk with separate finite edge sets
for the cluster piece and the bridge piece at each trajectory time. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

open scoped Classical

/-- State before the transition at a zero-based trajectory offset. -/
def trajInput {X : Type*} : (n : ℕ) → X → (Fin n → X) → ℕ → X
  | 0, x, _, _ => x
  | _+1, x, _, 0 => x
  | n+1, _, f, j+1 => trajInput n (f 0) (Fin.tail f) j

theorem trajInput_eq_output {X : Type*} (n : ℕ) (x : X) (f : Fin n → X)
    (j : ℕ) (hj : j < n) : trajInput n x f (j+1) = f ⟨j,hj⟩ := by
  induction n generalizing x j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => cases n <;> rfl
    | succ j =>
      change trajInput n (f 0) (Fin.tail f) (j+1) = f ⟨j+1,hj⟩
      exact ih (f 0) (Fin.tail f) j (by omega)

/-- The selected local pieces cover the concatenation. The terminal
predicate retains the exit edge's provenance in the last incoming state. -/
theorem trajectory_walk_pieces {d : ℕ} {X ι V : Type*} (G Gexit : SimpleGraph V)
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk0 : ∀ t x y z, 0 ≤ k t x y z) (z : Configuration d × Configuration d)
    (cl : X → Set ι) (bd : ℕ → ι → Set V) (Inv : ℕ → X → Prop)
    (clusterPiece bridgePiece : ℕ → X → Finset (Sym2 V) → Prop)
    (exit : X → V → V → Prop) (T : ℕ)
    (hexit : ∀ x y, Inv T x → 0 < k T x y z →
      ∃ c ∈ cl x, ∀ pt ∈ bd T c, ∃ v w, exit x v w ∧ Gexit.Adj v w ∧
        ∃ (W : G.Walk pt v) (C : Finset (Sym2 V)), clusterPiece T x C ∧
          ∀ e ∈ W.edges, e ∈ C)
    (hstep : ∀ t, t < T → ∀ x y, Inv t x → 0 < k t x y z →
      Inv (t+1) y ∧ ∀ c' ∈ cl y, ∃ c ∈ cl x, ∀ pt ∈ bd t c, ∃ v ∈ bd (t+1) c',
        ∃ (W : G.Walk pt v) (C B : Finset (Sym2 V)),
          clusterPiece t x C ∧ bridgePiece t x B ∧ ∀ e ∈ W.edges, e ∈ C ∨ e ∈ B) :
    ∀ (m t : ℕ) (x : X) (f : Fin (m+1) → X), t + m = T → Inv t x →
      0 < trajWeight k (m+1) t x f z →
      ∃ c ∈ cl x, ∀ pt ∈ bd t c, ∃ v w,
        exit (trajInput (m+1) x f m) v w ∧ Gexit.Adj v w ∧
        ∃ (W : G.Walk pt v) (C B : ℕ → Finset (Sym2 V)),
          (∀ j ≤ m, clusterPiece (t+j) (trajInput (m+1) x f j) (C j)) ∧
          (∀ j < m, bridgePiece (t+j) (trajInput (m+1) x f j) (B j)) ∧
          ∀ e ∈ W.edges, (∃ j ≤ m, e ∈ C j) ∨ ∃ j < m, e ∈ B j := by
  intro m
  induction m with
  | zero =>
    intro t x f ht hInv hw
    have htT : t = T := by omega
    subst htT
    have hk : 0 < k t x (f 0) z := by simpa only [trajWeight, mul_one] using hw
    obtain ⟨c, hc, hwalk⟩ := hexit x (f 0) hInv hk
    refine ⟨c, hc, fun pt hpt => ?_⟩
    obtain ⟨v,w,he,ha,W,C,hC,hcover⟩ := hwalk pt hpt
    refine ⟨v,w,he,ha,W,fun _ => C,fun _ => ∅, ?_, ?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa only [Nat.add_zero, trajInput] using hC
    · omega
    · exact fun e h => Or.inl ⟨0, le_rfl, hcover e h⟩
  | succ m ih =>
    intro t x f ht hInv hw
    have hprod : 0 < k t x (f 0) z * trajWeight k (m+1) (t+1) (f 0) (Fin.tail f) z := hw
    have htail0 := trajWeight_nonneg k hk0 (m+1) (t+1) (f 0) (Fin.tail f) z
    have hkt := pos_of_mul_pos_left hprod htail0
    have htail := pos_of_mul_pos_right hprod (hk0 t x (f 0) z)
    obtain ⟨hInv',hconn⟩ := hstep t (by omega) x (f 0) hInv hkt
    obtain ⟨c',hc',hwalk'⟩ := ih (t+1) (f 0) (Fin.tail f) (by omega) hInv' htail
    obtain ⟨c,hc,hfirst⟩ := hconn c' hc'
    refine ⟨c,hc,fun pt hpt => ?_⟩
    obtain ⟨u,hu,U,C₀,B₀,hC₀,hB₀,hU⟩ := hfirst pt hpt
    obtain ⟨v,w,he,ha,W,C,B,hC,hB,hW⟩ := hwalk' u hu
    let C' : ℕ → Finset (Sym2 V) := fun j => Nat.casesOn j C₀ C
    let B' : ℕ → Finset (Sym2 V) := fun j => Nat.casesOn j B₀ B
    refine ⟨v,w,he,ha,U.append W,C',B', ?_, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero =>
        change clusterPiece (t+0) x C₀
        simpa only [Nat.add_zero] using hC₀
      | succ j =>
        have htime : t + (j+1) = t+1+j := by omega
        rw [htime]
        exact hC j (by omega)
    · intro j hj
      cases j with
      | zero =>
        change bridgePiece (t+0) x B₀
        simpa only [Nat.add_zero] using hB₀
      | succ j =>
        have htime : t + (j+1) = t+1+j := by omega
        rw [htime]
        exact hB j (by omega)
    · intro e he'
      rw [SimpleGraph.Walk.edges_append, List.mem_append] at he'
      rcases he' with hu' | hw'
      · rcases hU e hu' with hc₀ | hb₀
        · exact Or.inl ⟨0, Nat.zero_le _, hc₀⟩
        · exact Or.inr ⟨0, Nat.zero_lt_succ _, hb₀⟩
      · rcases hW e hw' with ⟨j,hj,hcj⟩ | ⟨j,hj,hbj⟩
        · exact Or.inl ⟨j+1, by omega, hcj⟩
        · exact Or.inr ⟨j+1, by omega, hbj⟩

end NearCritical.Section10
