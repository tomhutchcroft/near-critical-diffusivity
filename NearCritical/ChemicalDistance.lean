module

public import NearCritical.ChemicalThinning
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Extended chemical distance: infinity on disconnected configurations. -/
@[expose] public section
noncomputable section
namespace NearCritical

lemma graphNStep_iff_exists_walk {V : Type*} (G : SimpleGraph V) (n : ℕ) (x y : V) :
    graphNStep G n x y ↔ ∃ w : G.Walk x y, w.length = n := by
  constructor
  · intro h
    induction n generalizing y with
    | zero =>
      change x = y at h
      subst y
      exact ⟨.nil, rfl⟩
    | succ n ih =>
      obtain ⟨z, hz, hzy⟩ := h
      obtain ⟨w, hw⟩ := ih z hz
      exact ⟨w.concat hzy, by simp [hw]⟩
  · rintro ⟨w, rfl⟩
    induction w using SimpleGraph.Walk.concatRec with
    | Hnil => rfl
    | Hconcat p h ih =>
      simp only [SimpleGraph.Walk.length_concat]
      exact ⟨_, ih, h⟩

/-- The intrinsic graph distance, taking value infinity if no open path exists. -/
def chemicalDistance {d : ℕ} (ω : Configuration d) (x y : Vertex d) : ℕ∞ :=
  (openGraph ω).edist x y

lemma chemicalConnectionEvent_eq_distance {d : ℕ} (x y : Vertex d) (m : ℕ) :
    chemicalConnectionEvent x y m = {ω | chemicalDistance ω x y ≤ (m : ℕ∞)} := by
  ext ω
  constructor
  · rintro ⟨n, hn, hw⟩
    obtain ⟨w, hw⟩ := (graphNStep_iff_exists_walk (openGraph ω) n x y).mp hw
    change (openGraph ω).edist x y ≤ (m : ℕ∞)
    exact w.edist_le.trans (by simpa [hw] using (ENat.natCast_le_natCast.mpr hn))
  · intro h
    change (openGraph ω).edist x y ≤ (m : ℕ∞) at h
    have hfin : (openGraph ω).edist x y ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt h (ENat.natCast_lt_top m))
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfin
    rw [← hw] at h
    exact ⟨w.length, ENat.natCast_le_natCast.mp h,
      (graphNStep_iff_exists_walk (openGraph ω) w.length x y).mpr ⟨w, rfl⟩⟩

/-- Literal source lem.chem.monotone, with extended intrinsic-distance events. -/
theorem chemicalDistance_probability_comparison (d : ℕ) (p p' : unitInterval)
    (hp' : 0 < (p' : ℝ)) (hpp : (p' : ℝ) ≤ (p : ℝ))
    (x y : Vertex d) (m : ℕ) :
    (percolation d p).real {ω | chemicalDistance ω x y ≤ (m : ℕ∞)} ≤
      ((p : ℝ) / (p' : ℝ)) ^ m *
        (percolation d p').real {ω | chemicalDistance ω x y ≤ (m : ℕ∞)} := by
  simpa only [chemicalConnectionEvent_eq_distance] using
    chemicalConnection_probability_comparison d p p' hp' hpp x y m

end NearCritical
