module

public import NearCritical.MicroscopicChainPath
public import NearCritical.ChemicalCoarseBox

/-! Exact terminal exit-edge absorption in source lem.chem.crossing.
The +1 in lem.nw.path is retained and absorbed into the explicit constant. -/
@[expose] public section
namespace NearCritical
open Set

lemma chemical_crossing_coarse_length_bound_with_exit {M ell0 s n0 ellStar : ℕ}
    (hM : 2≤M) (hscale : ell0=n0*ellStar) (hstar : 1≤ellStar) (hs : 1≤s)
    {A : ℝ} (hA : 0≤A) :
    2*(M:ℝ)*A*(ell0:ℝ)^2+1 ≤
      (4*A*(n0:ℝ)+1)*(ellStar:ℝ)*(((M-1)*ell0+s:ℕ):ℝ) := by
  have h := chemical_crossing_coarse_length_bound (s := s) hM hscale hA
  have hL : 1≤(M-1)*ell0+s := by omega
  have hprod : (1:ℝ)≤(ellStar:ℝ)*(((M-1)*ell0+s:ℕ):ℝ) := by
    exact_mod_cast (show 1≤ellStar*((M-1)*ell0+s) from Nat.mul_pos (by omega) (by omega))
  nlinarith

/-- Local chain geometry plus the source route/scale identities implies the
actual confined crossing with a corrected explicit chemical length constant. -/
theorem microscopicChain_crossing_with_source_length {d R : ℕ} (a : Vertex d) (i : Fin d)
    {ω : Configuration d} {Asp Ask : ℝ} {n M ell0 s n0 ellStar : ℕ}
    {x y z : Vertex d} (hAsp : 0≤Asp) (hAsk : 0≤Ask)
    (hx : x ∈ chemicalBottomFace d R i) (hz : z ∈ chemicalExitFace d R i)
    (h : MicroscopicChainGeometry
      (restrictedGraph ω (translateSites a (chemicalCrossingSupport d R i) : Set (Vertex d)))
      (Asp*(ell0:ℝ)^2) (Ask*(ell0:ℝ)^2) n (a+x) y)
    (hexit : (restrictedGraph ω (translateSites a (chemicalCrossingSupport d R i) :
      Set (Vertex d))).Adj y (a+z))
    (hn : n+1≤2*M) (hM : 2≤M) (hscale : ell0=n0*ellStar)
    (hstar : 1≤ellStar) (hs : 1≤s) (hside : (M-1)*ell0+s=2*R+1) :
    ω ∈ chemicalBoxCrossingEvent a R i ((4*(Asp+Ask)*(n0:ℝ)+1)*(ellStar:ℝ)) := by
  apply microscopicChain_crossing a i hx hz h hexit
  have hroute := microscopicChain_route_length_bound hn
    (mul_nonneg hAsp (sq_nonneg (ell0:ℝ))) (mul_nonneg hAsk (sq_nonneg (ell0:ℝ)))
  have hbound := chemical_crossing_coarse_length_bound_with_exit hM hscale hstar hs
    (add_nonneg hAsp hAsk)
  rw [hside] at hbound
  nlinarith

end NearCritical
