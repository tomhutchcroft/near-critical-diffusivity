module

public import NearCritical.ChemicalUpperFromLayouts
public import NearCritical.Section10ActualRoute

/-! Source `prop.chem.upper` for the actual Section 10 construction.

`chemical_timeConstant_upper_actual`: in dimension `D + 1` (`D >= 3`), with the
actual layout `actualLayout` (cubes of mesh `l0 = 2t`, `t >= 9`, translated
Section 9 half tubes, exit bonds at the top level), the time constant satisfies
`mu <= 2 (4 (A_sp + A_sk) n0 + 1) l_*` provided

* `hs`: for all large `M`, every step of the lattice nest rule has conditional
  success probability at least `1/rho` (`prop.proba.k-nest`);
* `hsite`: for all large `M`, `P[pre-good] >= 1/kappa` (`prop.proba.pregood`);
* parameter relations (`(rho kappa)^2 q0 < 1`, `k <= c l0^(d-6)`, the length
  scales, `l0 = n0 l_*`);
* `hGM`: the cited lower tail of the chemical distance.

All geometric hypotheses of `chemical_timeConstant_upper_of_layouts` are proved
here. The two probability bounds are the remaining paper-internal inputs of the
upper bound in `thm.time_constant`.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter
open NearCritical.Section10

theorem chemical_timeConstant_upper_actual {D : ℕ} (hD : 3 ≤ D) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧
    ∀ (pc q : unitInterval) (N : Seminorm ℝ (Fin (D + 1) → ℝ))
      (_hunit : ∀ j, N (Pi.single j 1) = 1)
      (_hreflect : ∀ j x, N (coordinateReflection j x) = N x)
      {μ Asp Ask : ℝ} (_hμ : 0 ≤ μ) (_hAsp : 0 ≤ Asp) (_hAsk : 0 ≤ Ask)
      {ϱ κ : ℝ} (_hϱ : 1 ≤ ϱ) (_hκ : 1 ≤ κ) (_hΛq : (ϱ * κ) ^ 2 * q0 < 1)
      (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
      (MOff Mcoal Kdiam : ℕ) {n0 ellStar : ℕ} (_hscale : 2 * t = n0 * ellStar)
      (_hstar : 1 ≤ ellStar)
      (_hA : 2 * (typ.diameterUpper * (2 * (t : ℝ)) ^ 2) = Asp * ((2 * t : ℕ) : ℝ) ^ 2)
      (_hB : (Kdiam : ℝ) = Ask * ((2 * t : ℕ) : ℝ) ^ 2)
      (_hcount : (k : ℝ) ≤ typ.countLower * (2 * (t : ℝ)) ^ (D + 1 - 6))
      (_hs : ∀ᶠ M in atTop, ∀ (γ : SourceRoute D M)
        (G : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Φ) (t' : ℕ)
        (x : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).X), ϱ⁻¹ ≤
        localSuccessProbability pc q
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Bl₀ G.1
            (routeLab M γ.position t'))
          (bitSet G.2 (fun z => (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).succσ G
            (routeLab M γ.position t') x
            ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).view G.1
              (routeLab M γ.position t') z))))
      (_hsite : ∀ᶠ M in atTop, ∀ st, κ⁻¹ ≤
        coupledProb pc q ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).siteEvent st))
      (_hGM : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ,
        UniformChemicalLowerTail (D + 1) (orParameter pc q) N μ ε B R),
      μ ≤ 2 * ((4 * (Asp + Ask) * (n0 : ℝ) + 1) * (ellStar : ℝ)) := by
  obtain ⟨q0, hq0, hq1, hmain⟩ :=
    chemical_timeConstant_upper_of_layouts (d := D + 1) (by omega)
  refine ⟨q0, hq0, hq1, ?_⟩
  intro pc q N hunit hreflect μ Asp Ask hμ hAsp hAsk ϱ κ hϱ hκ hΛq typ t ht k hk MOff Mcoal
    Kdiam n0 ellStar hscale hstar hA hB hcount hs hsite hGM
  have ht0 : 0 < t := by omega
  refine hmain pc q (0 : Fin (D + 1)) N hunit hreflect hμ hAsp hAsk hϱ hκ hΛq hscale hstar
    (fun M => boxCenter (D + 1) t M) (fun M => boxRadius t M)
    (fun _ => 2 * ((t - 1) / 2) + 1) ?_ (fun _ => by omega) ?_ ?_ hGM
  · refine tendsto_atTop_atTop.mpr (fun b => ⟨b + 1, fun M hM => ?_⟩)
    unfold boxRadius
    have h1 : M - 1 ≤ (M - 1) * t := Nat.le_mul_of_pos_right _ ht0
    omega
  · intro M
    unfold boxRadius
    ring
  · filter_upwards [hs, hsite, eventually_ge_atTop 1] with M hsM hsiteM hM1
    refine ⟨actualLayout D typ t ht k hk MOff Mcoal Kdiam M, rfl, rfl, hA, hB, hcount, hsM,
      hsiteM, ?_, ?_, ?_, ?_, ?_⟩
    · intro γ hroute t' ht'
      exact routeLab_site_mem_box γ hroute ht'
    · intro st hst
      exact Finset.coe_subset.mpr (cube_subset_support ht0 0 _
        (fun kk => siteCenter_bounds t hst kk))
    · intro γ hroute t' ht' ℓ hℓ hstep hmove
      subst hℓ
      have htube : HasTube M (routeLab M γ.position t') :=
        routeLab_hasTube γ.1.1 γ.2 hstep hmove
      have hsitebox := routeLab_site_mem_box γ hroute ht'
      have hLdef : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).L
          (routeLab M γ.position t') =
          stepL t (siteCenter t (routeLab M γ.position t').site)
            (dirOf (routeLab M γ.position t')) := by
        show LOf t M _ = _
        unfold LOf
        rw [if_pos htube]
      have hRdef : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).R
          (routeLab M γ.position t') =
          stepR t (siteCenter t (routeLab M γ.position t').site)
            (dirOf (routeLab M γ.position t')) := by
        show ROf t M _ = _
        unfold ROf
        rw [if_pos htube]
      have hfar := siteCenter_target t htube
      have htgtbox : (routeLab M γ.position t').target ∈ siteBoxOf D M := by
        have hlt : t' + 1 < 2 * M := by
          by_contra hcon
          have ht'eq : t' = 2 * M - 1 := by omega
          have hl := routeLab_last hM1 γ.position
          rw [← ht'eq] at hl
          rw [hl] at hstep
          exact hstep
        rw [← routeLab_next_site γ.position hlt]
        exact routeLab_site_mem_box γ hroute (by omega)
      have hci : siteCenter t (routeLab M γ.position t').site (dirOf (routeLab M γ.position t'))
          + 2 * (t : ℤ) ≤ 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ) := by
        have h := (siteCenter_bounds t htgtbox (dirOf (routeLab M γ.position t'))).2
        rw [hfar, farCenter_apply_self] at h
        exact h
      have hsupp := stepLR_subset_support (M := M) ht (0 : Fin (D + 1))
        (dirOf (routeLab M γ.position t')) (siteCenter t (routeLab M γ.position t').site)
        (fun kk => siteCenter_bounds t hsitebox kk) hci
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hLdef]
        exact Finset.coe_subset.mpr (Finset.subset_union_left.trans hsupp)
      · rw [hRdef]
        exact Finset.coe_subset.mpr (Finset.subset_union_right.trans hsupp)
      · rw [hLdef]
        show Disjoint _ ((typicalCube t (siteCenter t (routeLab M γ.position t').target) :
          Finset (Vertex (D + 1))) : Set (Vertex (D + 1)))
        rw [hfar]
        exact Finset.disjoint_coe.mpr (stepL_disjoint_far_cube t _ _)
      · rw [hRdef]
        exact Finset.disjoint_coe.mpr (stepR_disjoint_near_cube t _ _)
      · intro pl
        rw [hLdef]
        exact splitFace_subset_stepL ht _ _ pl
    · intro st hst hlev pt hpt
      refine bottomFace_mem ht0 0 _ (fun kk => siteCenter_bounds t hst kk) ?_ hpt
      show siteCenter t st 0 = 0
      rw [siteCenter_zero, hlev]
      simp
    · intro st hst hlev y hy
      refine exitFace_mem ht0 0 _ (fun kk => siteCenter_bounds t hst kk) ?_ hy
      show siteCenter t st 0 = 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ)
      rw [siteCenter_zero, hlev]

end NearCritical
