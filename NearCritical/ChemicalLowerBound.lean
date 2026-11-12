module

public import NearCritical.ChemicalConverse
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! New source prop.chem.lower deduction. Standard subcritical exponential
connection bounds and the named uniqueness/shape inputs remain explicit. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Filter
open scoped Topology

/-- The cited HMS input along a ray, source lem.chem.HMS (Hutchcroft 2023,
Theorem 1.1), with constants made explicit. This is not assumed as an axiom. -/
def RayExponentialConnectionBound (d : ℕ) (p : unitInterval) (u : Vertex d)
    (C b : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → twoPoint d p 0 (n • u) ≤ C * Real.exp (-b * (n : ℝ))

lemma chemicalShort_probability_exponential {d : ℕ} (p q : unitInterval)
    (hq : 0 < (q : ℝ)) (hqp : (q : ℝ) ≤ (p : ℝ)) (u : Vertex d)
    {a k C b : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hratio : (p : ℝ) / (q : ℝ) ≤ Real.exp k)
    (hHMS : RayExponentialConnectionBound d q u C b) {n : ℕ} (hn : 1 ≤ n) :
    (percolation d p).real (chemicalShortEvent 0 (n • u) (a * (n : ℝ))) ≤
      C * Real.exp ((k*a-b) * (n : ℝ)) := by
  have ht : 0 ≤ a * (n : ℝ) := mul_nonneg ha (Nat.cast_nonneg n)
  rw [chemicalShortEvent_eq_floor _ _ ht]
  have hcomp := chemicalConnection_probability_comparison d p q hq hqp 0 (n • u) ⌊a*(n:ℝ)⌋₊
  have hsub : chemicalConnectionEvent (0 : Vertex d) (n • u) ⌊a*(n:ℝ)⌋₊ ⊆
      connectionEvent 0 (n • u) := by
    rintro ω ⟨m,hm,hw⟩
    exact (graph_reachable_iff_exists_nStep _ _ _).mpr ⟨m,hw⟩
  have hprob : (percolation d q).real
      (chemicalConnectionEvent 0 (n • u) ⌊a*(n:ℝ)⌋₊) ≤
      C * Real.exp (-b*(n:ℝ)) :=
    (measureReal_mono hsub).trans (hHMS n hn)
  have hpow : ((p : ℝ)/(q : ℝ)) ^ ⌊a*(n:ℝ)⌋₊ ≤ Real.exp (k*a*(n:ℝ)) := by
    calc
      _ ≤ (Real.exp k) ^ ⌊a*(n:ℝ)⌋₊ :=
        pow_le_pow_left₀ (div_nonneg p.2.1 q.2.1) hratio _
      _ = Real.exp (k * (⌊a*(n:ℝ)⌋₊ : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hf := mul_le_mul_of_nonneg_left (Nat.floor_le ht) hk
        nlinarith)
  calc
    _ ≤ ((p : ℝ)/(q : ℝ)) ^ ⌊a*(n:ℝ)⌋₊ *
        (percolation d q).real (chemicalConnectionEvent 0 (n • u) ⌊a*(n:ℝ)⌋₊) := hcomp
    _ ≤ Real.exp (k*a*(n:ℝ)) * (C * Real.exp (-b*(n:ℝ))) :=
      mul_le_mul hpow hprob measureReal_nonneg (Real.exp_nonneg _)
    _ = _ := by rw [← mul_assoc, mul_comm (Real.exp _) C, mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Strictly negative exponent forces the actual short-event probabilities to zero. -/
theorem chemicalShort_probability_tendsto_zero {d : ℕ} (p q : unitInterval)
    (hq : 0 < (q : ℝ)) (hqp : (q : ℝ) ≤ (p : ℝ)) (u : Vertex d)
    {a k C b : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hratio : (p : ℝ)/(q : ℝ) ≤ Real.exp k)
    (hHMS : RayExponentialConnectionBound d q u C b) (hdecay : k*a < b) :
    Tendsto (fun n : ℕ => (percolation d p).real
      (chemicalShortEvent 0 (n • u) (a*(n:ℝ)))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => C * Real.exp ((k*a-b)*(n:ℝ))) atTop (𝓝 0) := by
    have hs : Summable (fun n : ℕ => Real.exp ((n:ℝ)*(k*a-b))) :=
      Real.summable_exp_nat_mul_iff.mpr (sub_neg.mpr hdecay)
    simpa [mul_comm] using hs.tendsto_atTop_zero.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact chemicalShort_probability_exponential p q hq hqp u ha hk hratio hHMS hn

/-- Core new lower-bound deduction: no speed below b/(2k) is compatible with
thinning, HMS exponential decay, and the positive chemical-converse liminf. -/
theorem chemical_timeConstant_lower {d : ℕ} (p q : unitInterval)
    (hp : criticalPoint d < p) (hq : 0 < (q : ℝ)) (hqp : (q : ℝ) ≤ (p : ℝ))
    (u : Vertex d) {μ k C b : ℝ} (hk : 0 < k) (hb : 0 < b)
    (hratio : (p : ℝ)/(q : ℝ) ≤ Real.exp k)
    (hHMS : RayExponentialConnectionBound d q u C b)
    (huniq : AEInfiniteClusterUniqueness d p) (hlimit : AEConnectedChemicalLimit d p u μ) :
    b/(2*k) ≤ μ := by
  by_contra h
  have ha : μ < b/(2*k) := lt_of_not_ge h
  have hzero := chemicalShort_probability_tendsto_zero p q hq hqp u
    (le_of_lt (div_pos hb (mul_pos (by norm_num) hk))) hk.le hratio hHMS
    (show k*(b/(2*k)) < b by field_simp; nlinarith)
  have hpos := chemical_converse_liminf_pos hp huniq hlimit ha
  rw [hzero.liminf_eq] at hpos
  exact lt_irrefl 0 hpos

/-- The elementary parameter comparison in source prop.chem.lower. -/
lemma chemical_lower_parameter_ratio {pc δ P Q : ℝ} (hδ : 0 < δ)
    (hw : δ < pc/2) (hP : P = pc+δ) (hQ : Q = pc-δ) :
    P/Q ≤ Real.exp (4*δ/pc) := by
  have hpc : 0 < pc := by linarith
  have hq : 0 < pc-δ := by linarith
  have he : (pc+δ)/(pc-δ) ≤ (pc+4*δ)/pc := by
    apply (div_le_div_iff₀ hq hpc).2
    nlinarith
  have hid : (pc+4*δ)/pc = 1+4*δ/pc := by field_simp
  rw [hP,hQ]
  exact he.trans (hid ▸ (by simpa [add_comm] using Real.add_one_le_exp (4*δ/pc)))

/-- The near-critical part of source prop.chem.lower with explicit constant.
The HMS estimate at q=pc-delta is a named standard input; uniqueness and the
Garet–Marchand connected-subsequence limit are the same named inputs as in
lem.chem.converse. No time-constant lower bound is assumed. -/
theorem chemical_timeConstant_nearCritical_lower {d : ℕ} (p q : unitInterval)
    (hp : criticalPoint d < p) (u : Vertex d) {μ δ c C : ℝ}
    (hδ : 0 < δ) (hw : δ < (criticalPoint d : ℝ)/2)
    (hpδ : (p : ℝ) = (criticalPoint d : ℝ)+δ)
    (hqδ : (q : ℝ) = (criticalPoint d : ℝ)-δ) (hc : 0 < c)
    (hHMS : RayExponentialConnectionBound d q u C (c*Real.sqrt δ))
    (huniq : AEInfiniteClusterUniqueness d p) (hlimit : AEConnectedChemicalLimit d p u μ) :
    (c*(criticalPoint d : ℝ)/8)/Real.sqrt δ ≤ μ := by
  have hpc : 0 < (criticalPoint d : ℝ) := by linarith
  have hq : 0 < (q : ℝ) := by rw [hqδ]; linarith
  have hqp : (q : ℝ) ≤ (p : ℝ) := by rw [hpδ,hqδ]; linarith
  have hk : 0 < 4*δ/(criticalPoint d : ℝ) := div_pos (by positivity) hpc
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hb : 0 < c*Real.sqrt δ := mul_pos hc hs
  have h := chemical_timeConstant_lower p q hp hq hqp u hk hb
    (chemical_lower_parameter_ratio hδ hw hpδ hqδ) hHMS huniq hlimit
  have hid : (c*Real.sqrt δ)/(2*(4*δ/(criticalPoint d : ℝ))) =
      (c*(criticalPoint d : ℝ)/8)/Real.sqrt δ := by
    have hs2 := Real.sq_sqrt hδ.le
    field_simp
    nlinarith
  rwa [hid] at h

lemma open_adj_coordinate_displacement {d : ℕ} {ω : Configuration d}
    {x y : Vertex d} (h : (openGraph ω).Adj x y) (i : Fin d) : y i-x i ≤ 1 := by
  obtain ⟨e,he,h | h⟩ := h
  · rcases h with ⟨rfl,rfl⟩
    by_cases hi : i=e.2
    · subst i; simp [bondTip]
    · simp [bondTip,Function.update_of_ne hi]
  · rcases h with ⟨rfl,rfl⟩
    by_cases hi : i=e.2
    · subst i; simp [bondTip]
    · simp [bondTip,Function.update_of_ne hi]

lemma graphNStep_coordinate_displacement {d : ℕ} {ω : Configuration d}
    {x y : Vertex d} {n : ℕ} (h : graphNStep (openGraph ω) n x y) (i : Fin d) :
    y i-x i ≤ (n : ℤ) := by
  induction n generalizing y with
  | zero => change x=y at h; subst y; simp
  | succ n ih =>
    obtain ⟨z,hz,hzy⟩ := h
    have h1 := ih hz
    have h2 := open_adj_coordinate_displacement hzy i
    omega

lemma axis_chemicalShortEvent_empty {d : ℕ} (i : Fin d) {a : ℝ} (ha : a<1)
    {n : ℕ} (hn : 1 ≤ n) :
    chemicalShortEvent 0 (n • Pi.single i (1 : ℤ)) (a*(n:ℝ)) = ∅ := by
  ext ω
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨m,hm,k,hkm,hw⟩
  have hd := graphNStep_coordinate_displacement hw i
  have hnat : n ≤ m := by
    simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one,
      Pi.zero_apply, sub_zero] at hd
    omega
  have hreal : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnat
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  nlinarith

lemma chemical_timeConstant_ge_one {d : ℕ} (p : unitInterval) (hp : criticalPoint d < p)
    (i : Fin d) {μ : ℝ} (huniq : AEInfiniteClusterUniqueness d p)
    (hlimit : AEConnectedChemicalLimit d p (Pi.single i 1) μ) : 1 ≤ μ := by
  by_contra h
  have ha : μ < (μ+1)/2 := by linarith
  have hb : (μ+1)/2 < 1 := by linarith
  have hz : Tendsto (fun n : ℕ => (percolation d p).real
      (chemicalShortEvent 0 (n • Pi.single i 1) (((μ+1)/2)*(n:ℝ)))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [axis_chemicalShortEvent_empty i hb hn, measureReal_empty]
  have hpos := chemical_converse_liminf_pos hp huniq hlimit ha
  rw [hz.liminf_eq] at hpos
  exact lt_irrefl 0 hpos

lemma chemical_lower_constant_pos {pc c : ℝ} (hpc : 0<pc) (hc : 0<c) :
    0 < min (Real.sqrt (pc/2)) (c*pc/8) := by
  apply lt_min
  · exact Real.sqrt_pos.mpr (div_pos hpc (by norm_num))
  · exact div_pos (mul_pos hc hpc) (by norm_num)

/-- Full source prop.chem.lower deduction with an explicit uniform constant.
Standard pc>0, uniform HMS ray decay and the named uniqueness/shape inputs are
exposed. The near-critical exponent and the macroscopic parameter case are proved. -/
theorem chemical_timeConstant_lower_uniform {d : ℕ} (i : Fin d)
    (_hpc : 0 < (criticalPoint d : ℝ)) {c C : ℝ} (hc : 0<c)
    (hHMS : ∀ q : unitInterval, 0 < (q:ℝ) → (q:ℝ) ≤ (criticalPoint d : ℝ) →
      RayExponentialConnectionBound d q (Pi.single i 1) C
        (c*Real.sqrt ((criticalPoint d : ℝ)-(q:ℝ))))
    (p : unitInterval) (hp : criticalPoint d < p) {μ : ℝ}
    (huniq : AEInfiniteClusterUniqueness d p)
    (hlimit : AEConnectedChemicalLimit d p (Pi.single i 1) μ) :
    min (Real.sqrt ((criticalPoint d : ℝ)/2)) (c*(criticalPoint d : ℝ)/8) /
      Real.sqrt ((p:ℝ)-(criticalPoint d : ℝ)) ≤ μ := by
  let δ := (p:ℝ)-(criticalPoint d : ℝ)
  have hδ : 0<δ := sub_pos.mpr hp
  have hs : 0<Real.sqrt δ := Real.sqrt_pos.mpr hδ
  by_cases hw : δ < (criticalPoint d : ℝ)/2
  · let q : unitInterval := ⟨(criticalPoint d : ℝ)-δ, by
      constructor
      · linarith
      · have := (criticalPoint d).2.2; linarith⟩
    have hq : 0<(q:ℝ) := by dsimp [q]; linarith
    have hH := hHMS q hq (by dsimp [q]; linarith)
    have hid : (criticalPoint d : ℝ)-(q:ℝ)=δ := by dsimp [q]; ring
    rw [hid] at hH
    have h := chemical_timeConstant_nearCritical_lower p q hp (Pi.single i 1)
      hδ hw (by dsimp [δ]; ring) rfl hc hH huniq hlimit
    exact (div_le_div_of_nonneg_right (min_le_right _ _) hs.le).trans h
  · have hmin : min (Real.sqrt ((criticalPoint d : ℝ)/2))
        (c*(criticalPoint d : ℝ)/8) ≤ Real.sqrt δ :=
      (min_le_left _ _).trans (Real.sqrt_le_sqrt (le_of_not_gt hw))
    exact ((div_le_one hs).2 hmin).trans (chemical_timeConstant_ge_one p hp i huniq hlimit)

end NearCritical
