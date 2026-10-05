/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVNormalizedRootCompanionEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Actual crossing data for a degree-minimal pair of small degree gcd -/
namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 1000000

structure GGVSmallDegreeCrossingData (P Q : A1 ℂ) where
  left : A1 ℂ
  right : A1 ℂ
  minimal : IsDegreeMinimalCounterexamplePair left right
  leftDegree : totalDeg left.1 = totalDeg P.1
  rightDegree : totalDeg right.1 = totalDeg Q.1
  rho : ℕ
  s : ℕ
  d : ℕ
  n : ℕ
  u : ℕ
  v : ℕ
  r : ℕ
  t : ℕ
  h : ℕ
  root : MvPolynomial (Fin 2) ℂ
  companion : MvPolynomial (Fin 2) ℂ
  nu : ℂ
  mu : ℂ
  weight : ℤ
  rhoPos : 0 < rho
  sPos : 0 < s
  direction : IsDirection (rho : ℤ) (-(s : ℤ))
  leftDirection : InDir (rho : ℤ) (-(s : ℤ)) left.1
  rightDirection : InDir (rho : ℤ) (-(s : ℤ)) right.1
  dProper : 1 < d
  nProper : 1 < n
  coprime : Nat.Coprime d n
  rootNonzero : root ≠ 0
  nuNonzero : nu ≠ 0
  muNonzero : mu ≠ 0
  rootHomogeneous : root.IsWeightedHomogeneous (wt (rho : ℤ) (-(s : ℤ))) weight
  leftFace : leadingForm (rho : ℤ) (-(s : ℤ)) left.1 = C nu * root^d
  rightFace : leadingForm (rho : ℤ) (-(s : ℤ)) right.1 = C mu * root^n
  leftWeight : vDeg (rho : ℤ) (-(s : ℤ)) left.1 = (d : ℤ)*weight
  endOccupied : expo u v ∈ root.support
  startOccupied : expo r t ∈ root.support
  endMax : ∀ x ∈ root.support, x 0 ≤ u
  startMin : ∀ x ∈ root.support, r ≤ x 0
  startCrossing : t < r
  endCrossing : u < v
  distinctEndpoints : r < u
  endpointBound : u+v ≤ 15
  companionHomogeneous : companion.IsWeightedHomogeneous
    (wt (rho : ℤ) (-(s : ℤ))) ((rho : ℤ)-s)
  companionBracket : poisson root companion = root
  companionBase : expo 1 1 ∈ companion.support
  f1 : ℕ
  f2 : ℕ
  companionEnd : expo f1 f2 ∈ companion.support
  companionMax : ∀ x ∈ companion.support, x 0 ≤ f1
  companionEndProper : 2 ≤ f1
  companionProportion : f1*v=f2*u
  companionStepPrimitive : Nat.gcd (f1-1) (f2-1)=1
  hProper : 2 ≤ h
  tBound : t ≤ h
  endHeight : v=t+rho*h
  cornerEquation : rho*r+(h-t)*s=rho*h-1

theorem degreeMinimal_small_degree_crossing_data
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (hsmall : Nat.gcd (totalDeg P.1) (totalDeg Q.1) ≤ 15) :
    Nonempty (GGVSmallDegreeCrossingData P Q) := by
  obtain ⟨A,B,a,b,c,e,j,hj,ρ,s,E,G,hminAB,hAdeg,hBdeg,ha,_,_,_,hrectA,
    hrectB,hprop,_,hρ,hs,hdir,hentry,hfaceA,hfaceB,hE,hG,hEmin,hGmax,hEpos,hGneg⟩ :=
    degreeMinimal_strict_crossing_pair P Q hmin
  obtain ⟨d,n,R,ν,μ,w,hd,hn,hcop,hAd,hBd,hR,hν,hμ,hhom,hweight,hAf,hBf⟩ :=
    degreeMinimal_subrectangular_negative_common_root A B hminAB ρ s hρ hdir
      j hj hentry a b c e ha hrectA hrectB hprop
  obtain ⟨u,v,r,t,hu,hr,hmax,hminRoot,htr,huv,hru,hbound,_,_⟩ :=
    negative_face_root_crossing_and_gcd_bound A B R ν ρ s d w hρ hs
      (by omega) hR hν hhom hAf hAd E G hE hG hEmin hGmax hEpos hGneg
  have hsmallRoot : u+v ≤ 15 := by
    have hg : Nat.gcd (totalDeg A.1) (totalDeg B.1) ≤ 15 := by
      simpa only [hAdeg,hBdeg] using hsmall
    omega
  obtain ⟨F,f₁,f₂,h,hFhom,hbr,hbase,hFend,hFmax,hf₁,hFprop,hprimitive,
      hh,hth,hv,heq⟩ := counterexample_crossing_root_small_degree_coordinates
    A B hminAB.1 R ν ρ s d u v r t w hs (by omega) hdir hR hν hhom
      hAf hu hr hmax htr huv hru hsmallRoot
  exact ⟨{
    left := A, right := B, minimal := hminAB
    leftDegree := hAdeg, rightDegree := hBdeg
    rho := ρ, s := s, d := d, n := n, u := u, v := v, r := r, t := t, h := h
    root := R, companion := F, nu := ν, mu := μ, weight := w
    rhoPos := hρ, sPos := hs, direction := hdir
    leftDirection := hfaceA, rightDirection := hfaceB
    dProper := hd, nProper := hn, coprime := hcop
    rootNonzero := hR, nuNonzero := hν, muNonzero := hμ
    rootHomogeneous := hhom, leftFace := hAf, rightFace := hBf, leftWeight := hweight
    endOccupied := hu, startOccupied := hr, endMax := hmax, startMin := hminRoot
    startCrossing := htr, endCrossing := huv, distinctEndpoints := hru
    endpointBound := hsmallRoot, companionHomogeneous := hFhom
    companionBracket := hbr, companionBase := hbase
    f1 := f₁, f2 := f₂, companionEnd := hFend, companionMax := hFmax
    companionEndProper := hf₁, companionProportion := hFprop
    companionStepPrimitive := hprimitive, hProper := hh, tBound := hth
    endHeight := hv, cornerEquation := heq
  }⟩

end Dixmier.Weyl
